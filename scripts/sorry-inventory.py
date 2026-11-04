#!/usr/bin/env python3
"""Report compiled sorry owners and their ancestors; never a certification gate.

Ledger contract: one fenced `toml sorry-inventory` block with modules and roots
arrays (qualified Lean names). Empty roots explicitly mean missing assembly.
Only tables headed `Declaration | ... | Paper argument/status` are compiled rows;
each declaration cell is one backtick-quoted qualified name. Other tables are
reported as excluded, not coverage. Paper text is recorded, not verified.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tomllib


def ledger(text):
    blocks = re.findall(r"^```toml sorry-inventory\s*\n(.*?)^```\s*$", text, re.M | re.S)
    if len(blocks) != 1:
        raise ValueError("expected one toml sorry-inventory block")
    config = tomllib.loads(blocks[0])
    for key in ("modules", "roots"):
        if not isinstance(config.get(key), list) or any(
                not isinstance(n, str) or not n or n.startswith("--") for n in config[key]):
            raise ValueError(f"{key} must be an array of Lean names")
    rows, excluded, issues = {}, [], []
    header = None
    for number, line in enumerate(text.splitlines(), 1):
        if not line.startswith("|"):
            header = None
            continue
        cells = [s.strip() for s in line.strip().strip("|").split("|")]
        if header is None:
            header = cells
            if not (header[0] == "Declaration" and "Paper argument/status" in header):
                excluded.append({"line": number, "header": header})
            continue
        if all(re.fullmatch(r":?-+:?", c) for c in cells):
            continue
        if header[0] != "Declaration" or "Paper argument/status" not in header:
            continue
        if len(cells) != len(header) or not re.fullmatch(r"`[^`]+\.[^`]+`", cells[0]):
            issues.append(f"malformed compiled row at line {number}")
            continue
        name = cells[0][1:-1]
        argument = cells[header.index("Paper argument/status")]
        if name in rows:
            issues.append(f"duplicate row: {name}")
        if not argument:
            issues.append(f"missing paper argument or OPEN: {name}")
        rows[name] = {"line": number, "argument": argument}
    return config, rows, excluded, issues


def reachable(seeds, edges):
    seen, todo = set(), list(seeds)
    while todo:
        name = todo.pop()
        if name not in seen:
            seen.add(name)
            todo.extend(edges.get(name, ()))
    return seen


def inventory(config, rows, records):
    nodes = {r["declaration"]: r for r in records if "declaration" in r}
    edges = {n: r["dependencies"] for n, r in nodes.items()}
    issues = []
    if not config["roots"]:
        issues.append("missing concrete obligations root: assembly unresolved (NOT MET)")
    for name in sorted(set(config["roots"]) | rows.keys()):
        if name not in nodes:
            issues.append(f"unknown declaration: {name}")
    closure = reachable(config["roots"], edges)
    reverse = {}
    for name in closure:
        for dep in edges.get(name, ()):
            reverse.setdefault(dep, []).append(name)
    owners = []
    for name in sorted(closure & nodes.keys()):
        if "sorryAx" not in edges[name]:
            continue
        if name not in rows:
            issues.append(f"unmapped sorry owner: {name}")
        def location(n):
            module = nodes[n]["module"]
            # Logical source path, relative to the owning package's source root.
            return {"declaration": n, "module": module,
                    "file": module.replace(".", "/") + ".lean" if module else None}
        owners.append({**location(name), "mapping": rows.get(name),
                       "ancestors": [location(n) for n in sorted(
                           reachable([name], reverse) - {name})]})
    for name in sorted(closure - nodes.keys()):
        issues.append(f"missing dependency: {name}")
    return owners, issues


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ledger", type=Path, default=Path("docs/obligations-dependencies.md"))
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()
    result = {"schema_version": 1, "mode": "report-only", "status": "incomplete",
              "ledger": str(args.ledger), "roots": [], "modules": [], "sorries": [],
              "rows": {}, "excluded_tables": [], "issues": []}
    try:
        config, rows, excluded, issues = ledger(args.ledger.read_text())
        result.update({"modules": config["modules"], "roots": config["roots"],
                       "rows": rows, "excluded_tables": excluded, "issues": issues})
        if not config["roots"]:
            result["issues"].append("missing concrete obligations root: assembly unresolved (NOT MET)")
        seeds = sorted(set(config["roots"]) | rows.keys())
        records = []
        if seeds:
            if not config["modules"]:
                raise ValueError("modules required to validate roots and rows")
            # Refuse stale module artifacts. All builds, including this freshness
            # check, run inside the caller's job on the shared box.
            subprocess.run(["lake", "build", "--no-build", "spec-surface", *config["modules"]],
                           check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            proc = subprocess.run(["lake", "exe", "spec-surface", "dependencies", "--from",
                                   *seeds, "--modules", *config["modules"]],
                                  check=True, capture_output=True, text=True)
            records = [json.loads(line) for line in proc.stdout.splitlines()]
        result["sorries"], findings = inventory(config, rows, records)
        result["issues"].extend(i for i in findings if i not in result["issues"])
        result["status"] = "incomplete" if result["issues"] else "mapped"
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        result["status"] = "incomplete"
        result["issues"].append(str(exc))
        if isinstance(exc, subprocess.CalledProcessError):
            result["issues"].append((exc.stderr or "")[-4000:])
    if not result["roots"] and not any("missing concrete obligations root" in i for i in result["issues"]):
        result["issues"].append("missing concrete obligations root: assembly unresolved (NOT MET)")
    args.json_out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"REPORT sorry inventory: {result['status']}; {len(result['sorries'])} direct owners; "
          f"{len(result['excluded_tables'])} noncompiled tables excluded; JSON: {args.json_out}")
    for issue in result["issues"]:
        print(f"  REPORT {issue}")
    for owner in result["sorries"]:
        print(f"  sorry {owner['declaration']} ({owner['file']})")
        for ancestor in owner["ancestors"]:
            print(f"    ancestor {ancestor['declaration']} ({ancestor['file']})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
