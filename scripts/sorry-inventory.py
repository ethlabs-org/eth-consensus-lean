#!/usr/bin/env python3
"""Report compiled sorry owners and their ancestors; never a certification gate.

Config contract (scripts/sorry-inventory.toml): `modules` and `roots`, arrays of qualified Lean
names; empty roots explicitly mean missing assembly. The optional table `mapped` maps a sorry owner
(a qualified name) to its paper argument or OPEN; an unmapped owner in the closure of the roots
reports incomplete. Argument text is recorded, not verified.
"""
import argparse
import json
from pathlib import Path
import subprocess
import tomllib


def read_config(text):
    config = tomllib.loads(text)
    for key in ("modules", "roots"):
        if not isinstance(config.get(key), list) or any(
                not isinstance(n, str) or not n or n.startswith("--") for n in config[key]):
            raise ValueError(f"{key} must be an array of Lean names")
    mapped = config.get("mapped", {})
    if not isinstance(mapped, dict):
        raise ValueError("mapped must be a table of qualified names")
    rows, issues = {}, []
    for name, argument in mapped.items():
        if "." not in name or name.startswith(".") or name.endswith("."):
            issues.append(f"malformed mapped entry: {name}")
            continue
        if not isinstance(argument, str) or not argument.strip():
            issues.append(f"missing paper argument or OPEN: {name}")
        rows[name] = {"argument": argument if isinstance(argument, str) else ""}
    return config, rows, issues


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
    parser.add_argument("--config", type=Path, default=Path("scripts/sorry-inventory.toml"))
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()
    result = {"schema_version": 2, "mode": "report-only", "status": "incomplete",
              "config": str(args.config), "roots": [], "modules": [], "sorries": [],
              "rows": {}, "issues": []}
    try:
        config, rows, issues = read_config(args.config.read_text())
        result.update({"modules": config["modules"], "roots": config["roots"],
                       "rows": rows, "issues": issues})
        if not config["roots"]:
            result["issues"].append("missing concrete obligations root: assembly unresolved (NOT MET)")
        seeds = sorted(set(config["roots"]) | rows.keys())
        records = []
        if seeds:
            if not config["modules"]:
                raise ValueError("modules required to validate roots and rows")
            # Refuse stale module artifacts.
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
          f"JSON: {args.json_out}")
    for issue in result["issues"]:
        print(f"  REPORT {issue}")
    for owner in result["sorries"]:
        print(f"  sorry {owner['declaration']} ({owner['file']})")
        for ancestor in owner["ancestors"]:
            print(f"    ancestor {ancestor['declaration']} ({ancestor['file']})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
