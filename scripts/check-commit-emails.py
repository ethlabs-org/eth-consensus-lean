#!/usr/bin/env python3
"""Check that every new commit names only allowed email addresses (owner, 2026-11-04; docs/decisions.md).

  scripts/check-commit-emails.py [--allowlist FILE] [<base> [<head>]]

Checks the commits reachable from <head> (default HEAD) and not from <base>: the author's and the committer's
address, and the address of every `Co-authored-by:` trailer. With no <base>, or one that is not a commit here
(a first push, a dispatch, a force push), it checks every commit reachable from <head>. An address passes if it
ends with one of `suffixes` or equals one of `addresses` in scripts/commit-emails.toml (case-insensitive); a
co-author trailer without an `<address>` fails. A failure names the commit and the field, never the address:
CI logs are public, and the allowlist is public by design, so nothing private is written anywhere. This is a
detector after upload (CI) and a guard before it (scripts/push-main.sh runs it on what it is about to push).
"""
import argparse
from pathlib import Path
import re
import subprocess
import sys
import tomllib

SEP = "\x1f"


def git(*args):
    return subprocess.run(["git", *args], check=True, capture_output=True, text=True).stdout


def allowed(address, suffixes, addresses):
    address = address.strip().lower()
    return bool(address) and (address in addresses or any(address.endswith(s) for s in suffixes))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--allowlist", type=Path, default=Path(__file__).with_name("commit-emails.toml"))
    parser.add_argument("base", nargs="?", default="")
    parser.add_argument("head", nargs="?", default="HEAD")
    args = parser.parse_args()
    config = tomllib.loads(args.allowlist.read_text())
    suffixes = [s.lower() for s in config.get("suffixes", [])]
    addresses = {a.lower() for a in config.get("addresses", [])}
    if not suffixes and not addresses:
        print(f"FAIL[emails] {args.allowlist} allows no address")
        return 1
    revs = [args.head]
    base = args.base
    if base and not re.fullmatch(r"0+", base):
        if subprocess.run(["git", "cat-file", "-e", f"{base}^{{commit}}"], capture_output=True).returncode == 0:
            revs.append(f"^{base}")
        else:
            print(f"check-commit-emails: base {base[:12]} is not a commit here: checking all of {args.head}")
    fmt = SEP.join(["%H", "%ae", "%ce", "%(trailers:key=Co-authored-by,valueonly,separator=%x1e)"]) + "%x00"
    out = git("log", "--no-show-signature", f"--format={fmt}", *revs, "--")
    failures, commits, checked = [], 0, 0
    for record in out.split("\x00"):
        record = record.strip("\n")
        if not record:
            continue
        sha, author, committer, coauthors = (record.split(SEP) + [""] * 4)[:4]
        commits += 1
        fields = [("author", author), ("committer", committer)]
        for i, value in enumerate(v for v in coauthors.split("\x1e") if v.strip()):
            m = re.search(r"<([^<>]*)>\s*$", value.strip())
            fields.append((f"Co-authored-by #{i + 1}", m.group(1) if m else ""))
        for field, address in fields:
            checked += 1
            if not allowed(address, suffixes, addresses):
                failures.append(f"FAIL[emails] {sha[:12]} {field}: address not on the allowlist ({args.allowlist.name})")
    for line in failures:
        print(line)
    if failures:
        print(f"check-commit-emails: {len(failures)} of {checked} addresses in {commits} commits are not allowed; "
              "rewrite the commits with an allowed address (a GitHub users.noreply.github.com address)")
        return 1
    print(f"check-commit-emails: {checked} addresses in {commits} commits, all on the allowlist: pass")
    return 0


if __name__ == "__main__":
    sys.exit(main())
