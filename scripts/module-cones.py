#!/usr/bin/env python3
"""Module import cones of consensus-lean, for build-structure work (report only, no gate).

Run from a consensus-lean checkout. Reads every non-archive `.lean` file at a Git revision
(default HEAD), so the tree need not be built or checked out at that revision.

  module-cones.py [--rev R] top [N]                  largest reverse-import cones
  module-cones.py [--rev R] cone MODULE              cone size and members
  module-cones.py [--rev R] adds [--since DATE] [N]  commits adding a public decl x cone ("score")
  module-cones.py [--rev R] usage MODULE             each public decl of MODULE: users in its cone
  module-cones.py [--rev R] passthrough MODULE...    importers that name nothing of MODULE, and
                                                     the cone after rewiring them to MODULE's imports
  module-cones.py [--rev R] passthrough-all [N]      the same over the N largest Lemmas cones
  module-cones.py [--rev R] split MODULE Part:lo-hi... [--flat]
                                                     model moving the public decls in each line
                                                     range to a new module Part

Definitions (card build_structure_plan.md, appendix):
- cone(M): modules importing M transitively, minus the generated roots ConsensusLean and
  ConsensusLeanTest. The static upper bound of a rebuild after a change to M's public interface.
- usage: a module "names" a declaration when its source contains the last name component as a
  whole word (optionally dotted). Textual: instances, notation, open-scoped names and simp sets are
  invisible, so the build is the check for any rewiring.
- split: decls in a range move to Part, which imports M (or M's imports with --flat); every module
  of cone(M) naming a moved decl imports Part; a direct importer naming nothing left in M drops M
  (taking M's imports if no part supplies them). Dependencies between parts are not modelled.
"""
import argparse, collections, re, subprocess, sys

ROOTS = ('ConsensusLean', 'ConsensusLeanTest')
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*((?:private|protected|noncomputable|public|nonrec|partial)\s+)*'
                  r'(?:def|theorem|lemma|abbrev|structure|class|inductive|instance|opaque)\s+([^\s:({\[]+)', re.M)
IMPORT = re.compile(r'^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)', re.M)


def git(*a, inp=None):
    return subprocess.run(['git', *a], input=inp, capture_output=True, check=True,
                          text=inp is None or isinstance(inp, str)).stdout


class Graph:
    def __init__(self, rev):
        self.rev = rev
        files = [f for f in git('ls-tree', '-r', '--name-only', rev).split()
                 if f.endswith('.lean') and f != 'lakefile.lean'
                 and not f.startswith(('archive/', '.lake/', 'scripts/', 'fixtures/'))]
        out = subprocess.run(['git', 'cat-file', '--batch'], input=''.join(f'{rev}:{f}\n' for f in files).encode(),
                             capture_output=True, check=True).stdout
        self.src, i = {}, 0
        self.file = {}
        for f in files:
            e = out.index(b'\n', i)
            size = int(out[i:e].split()[2])
            m = f[:-5].replace('/', '.')
            self.src[m] = out[e + 1:e + 1 + size].decode()
            self.file[m] = f
            i = e + 1 + size + 1
        mods = set(self.src)
        self.imp = {m: {d for d in IMPORT.findall(s) if d in mods} for m, s in self.src.items()}
        self.rev_ = self.invert(self.imp)

    @staticmethod
    def invert(imp):
        r = collections.defaultdict(set)
        for a, ds in imp.items():
            for d in ds:
                r[d].add(a)
        return r

    @staticmethod
    def cone(m, rev):
        seen, st = set(), [m]
        while st:
            for y in rev.get(st.pop(), ()):
                if y not in seen:
                    seen.add(y)
                    st.append(y)
        return {x for x in seen if x not in ROOTS}

    def decls(self, m, private=False):
        s = self.src[m]
        out = []
        for mm in DECL.finditer(s):
            priv = bool(mm.group(1) and 'private' in mm.group(1))
            if priv and not private:
                continue
            out.append((mm.group(2), s[:mm.start()].count('\n') + 1, priv))
        return out

    _pat = {}

    def names(self, x, name):
        last = name.split('.')[-1]
        p = self._pat.get(last)
        if p is None:
            p = self._pat[last] = re.compile(r'(?<![\w.])(?:[\w.]*\.)?' + re.escape(last) + r"(?![\w'])")
        return p.search(self.src[x]) is not None

    def resolve(self, m):
        if m in self.src:
            return m
        hits = [x for x in self.src if x.endswith('.' + m)]
        if len(hits) != 1:
            sys.exit(f'module {m!r}: {len(hits)} matches {hits[:5]}')
        return hits[0]


def short(m):
    return m.split('Goldilocks.')[-1]


def passthrough(G, m):
    ds = G.decls(m)
    direct = [x for x in G.rev_[m] if x not in ROOTS]
    pt = [x for x in direct if not any(G.names(x, n) for n, _, _ in ds)]
    rev2 = collections.defaultdict(set, {k: set(v) for k, v in G.rev_.items()})
    for x in pt:
        rev2[m].discard(x)
        for d in G.imp[m]:
            rev2[d].add(x)
    return direct, pt, len(G.cone(m, G.rev_)), len(G.cone(m, rev2))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--rev', default='HEAD')
    ap.add_argument('--since', default='2026-10-30')
    ap.add_argument('--flat', action='store_true')
    ap.add_argument('cmd')
    ap.add_argument('args', nargs='*')
    a = ap.parse_args()
    G = Graph(a.rev)
    n_of = lambda d: int(a.args[0]) if a.args else d
    if a.cmd == 'top':
        cs = sorted(((len(G.cone(m, G.rev_)), m) for m in G.imp if m not in ROOTS), reverse=True)
        for c, m in cs[:n_of(30)]:
            print(c, G.src[m].count('\n'), m)
    elif a.cmd == 'cone':
        m = G.resolve(a.args[0])
        c = G.cone(m, G.rev_)
        print(len(c), m)
        for x in sorted(c):
            print('  ', x)
    elif a.cmd == 'adds':
        log = git('log', '--first-parent', f'--since={a.since}', '-p', '--format=@@C %h', a.rev, '--', 'ConsensusLean')
        pub = re.compile(r'^\+\s*(?:@\[[^\]]*\]\s*)*(?:(?:protected|noncomputable|public|nonrec)\s+)*'
                         r'(?:def|theorem|lemma|abbrev|structure|class|inductive|instance)\s')
        adds, seen, c, f = collections.Counter(), set(), None, None
        for line in log.split('\n'):
            if line.startswith('@@C '):
                c = line[4:]
            elif line.startswith('+++ b/'):
                f = line[6:]
            elif f and f.endswith('.lean') and pub.match(line) and (c, f) not in seen:
                seen.add((c, f))
                adds[f] += 1
        f2m = {v: k for k, v in G.file.items()}
        rows = sorted(((n * len(G.cone(f2m[f], G.rev_)), n, len(G.cone(f2m[f], G.rev_)),
                        G.src[f2m[f]].count('\n'), f2m[f]) for f, n in adds.items() if f in f2m), reverse=True)
        print('score adds cone lines module')
        for r in rows[:n_of(40)]:
            print(*r[:4], short(r[4]))
    elif a.cmd == 'usage':
        m = G.resolve(a.args[0])
        c = G.cone(m, G.rev_)
        print(short(m), 'lines', G.src[m].count('\n'), 'cone', len(c))
        for name, ln, _ in G.decls(m):
            us = sorted(x for x in c if G.names(x, name))
            print(f'{ln:5d} {len(us):3d} {name}  ' + ' '.join(short(u) for u in us[:8]) + (' …' if len(us) > 8 else ''))
    elif a.cmd in ('passthrough', 'passthrough-all'):
        if a.cmd == 'passthrough':
            ms = [G.resolve(x) for x in a.args]
        else:
            cand = [m for m in G.imp if '.Lemmas.' in m]
            ms = sorted(cand, key=lambda m: -len(G.cone(m, G.rev_)))[:n_of(120)]
        res = []
        for m in ms:
            direct, pt, c0, c1 = passthrough(G, m)
            if pt or a.cmd == 'passthrough':
                res.append((c0 - c1, c0, c1, m, pt, len(direct)))
        res.sort(reverse=True)
        for d, c0, c1, m, pt, nd in res:
            print(f'{short(m)}: cone {c0} -> {c1} (direct {nd}, pass-through {len(pt)}): ' + ', '.join(short(p) for p in sorted(pt)))
    elif a.cmd == 'split':
        m = G.resolve(a.args[0])
        parts = []
        for p in a.args[1:]:
            nm, r = p.split(':')
            lo, hi = map(int, r.split('-'))
            parts.append((nm, lo, hi))
        ds = G.decls(m)
        where = {n: next((nm for nm, lo, hi in parts if lo <= ln <= hi), m) for n, ln, _ in ds}
        cone = G.cone(m, G.rev_)
        imp2 = {k: set(v) for k, v in G.imp.items()}
        for nm, _, _ in parts:
            imp2[nm] = set(G.imp[m]) | (set() if a.flat else {m})
        for x in cone:
            used = {where[n] for n, _, _ in ds if G.names(x, n)}
            for nm, _, _ in parts:
                if nm in used:
                    imp2[x].add(nm)
            if m in imp2[x] and m not in used:
                imp2[x].discard(m)
                if not any(p in imp2[x] for p, _, _ in parts):
                    imp2[x] |= set(G.imp[m])
        rev2 = G.invert(imp2)
        print(f'{short(m)}: cone {len(cone)}')
        print(f'  remaining {sum(1 for n in where if where[n] == m)} public decls: cone {len(G.cone(m, rev2))}')
        for nm, lo, hi in parts:
            c = G.cone(nm, rev2)
            print(f'  part {nm} ({lo}-{hi}, {sum(1 for n in where if where[n] == nm)} public decls): cone {len(c)}')
    else:
        ap.error(f'unknown command {a.cmd}')


if __name__ == '__main__':
    main()
