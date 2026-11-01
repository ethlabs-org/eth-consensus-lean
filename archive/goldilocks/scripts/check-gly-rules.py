#!/usr/bin/env python3
"""Check (i), BUILD §7.3: the GLY §F rules checked by source scans or compiled
declaration bodies (GLY r3.13 §F; step-2 rulings D08 as corrected, D13;
GEN-FIRST lead ruling, 2026-09-30).
The driver is scripts/check-gly-rules.sh.

Each source rule has a baseline scripts/baselines/check-gly-rules-<rule>.txt.
A FAIL rule fails on a finding in a new library (scripts/new-libraries.txt)
and on a legacy finding that its baseline does not list. A REVIEW rule
("review list" / "review the output" in GLY §F) lists its findings;
its baseline separates the reviewed ones. Stale F-1, F-13, F-18 or F-31 allow entries
always fail. F-13 (duplicate short names) is baselined in new libraries too
(step-2 ruling D07).
scripts/gly-rules-allow.txt: `<rule> <declaration>` lines that a rule
skips (the F-3 E-13 wrapper allow list; empty now).
scripts/gly-f1-allow.txt: complete F-1 group keys with a nonempty reason
after `#`. F-1 skips only an exact match of the field set and all names.
scripts/gly-f13-allow.txt: exact `F-13 dup <name> <Lib> <Lib> [...]` keys
with a nonempty reason after `#`. F-13 skips only an exact match of the
short name and all libraries.
scripts/gly-f18-allow.txt: exact F-18 declaration-and-file keys with a
nonempty reason after `#`.
scripts/gly-genfirst-allow.txt: exact `GEN-FIRST <constant> <module> -> <Gen>`
keys with a nonempty reason after `#`. All four allow files fail on unused
entries. F-31 runs scripts/CheckGenFirst.lean on the built tree; it has no
baseline exemption and runs compiled negative and positive controls.

Baseline rewrites (lead ruling, 2026-09-29): `--write-baseline` for F-13, or
for any rule, is allowed only in a commit whose message names the rule and
the reason. The reviewer reads the baseline diff. `--write-baseline` prints
a WARNING line with every key that the rewrite ADDS, because a rewrite also
accepts a real new finding (for example a new duplicate short name).

Rules (GLY §F row → what this script checks):
  F-1  REVIEW  structures (and classes) whose field-name sets coincide.
  F-3  FAIL    a premise of a theorem in Generic, KitFG or an FGSA library
               names RootInjectiveBelow, ViewRootInj, RootInjectiveOn or
               ContentAgree.
  F-4  FAIL    the import closure of a Generic Pure module
               (Statements.Pure.*, Proofs.Pure.*) holds only Model.Objects.*,
               Generic Pure modules and GridCO.Model.Walk (plus non-project
               modules: Mathlib, …).
  F-5  REVIEW  Block.genesis (or `.genesis`) in the statement of a theorem
               in a Walk, Votes or Lease module.
  F-6  FAIL    `slowLeasePolicy` in Generic.
  F-12 FAIL    the closure of Generic Statements.Pure (not Walk) holds only
               Model.Objects.* and Statements.Pure (not Walk); the closure of
               Statements.V2 also holds Statements.V2 and the closures of
               EngineV2.{Engine,Conditions,Laws}.* and KitV2.{ClockLaws,
               DutyClockLaws} (DutyClockLaws: no-round migration 02).
  F-13 FAIL    a theorem short name in more than one library (exact allow
               keys or legacy baseline); a `private theorem` in Generic.
  F-14 REVIEW  a theorem outside Generic with a PartialSynchrony or
               HealthyPrefixDelivery premise and a handles/processed
               conclusion.
  F-15 FAIL    `…` in a Generic Statements module (outside comments).
  F-18 REVIEW  a window definition (name contains "window") outside the
               Schedule and Recurrence modules.
  F-20 FAIL    a declaration name with suffix _of_pins, _closed or _landed
               in Generic or an FGSA library.
  F-21 FAIL    plan vocabulary in a declaration name: a component token
               T<n>, I<n>, W<n>, V<3-9>, GF<n>, G_F<n> or F<n><letter>.
  F-23 FAIL    a premise of a theorem in Generic, KitFG or
               FGSAProofs …Shared… names CleanCut₂, Outage₂, Recovery₂,
               HealthyPrefix₂, HealingInput, a …Set or a …Contract type.
  F-24         retired name rule; F-24 is now the compiled proof-route check
               (scripts/CheckFaultXRoute.lean, run by check-gly-rules.sh).
  F-25 REVIEW  a Keep/Frame theorem with `∩` in its conclusion.
  F-26 FAIL    HealingInput in FGSAClaims Statements/Phases (PhasesInternal
               exempt).
  F-28 FAIL    a theorem in a Statements module (a `.Statements.` module or a
               KitFG definition module) whose name does not end in `_def`.
  F-30 FAIL    a Generic declaration in namespace AvailableChain.Generic; a
               GridCO.Proofs module in the closure of a Generic module.
  F-31 FAIL    GEN-FIRST: an FGSA*, Shared, Claims or KitFG declaration body
               is a Gen constant, bare or applied only to its own binders,
               after leading lambdas and mdata are removed. The scope comes
               from lakefile.toml; GridCO is excluded. See CheckGenFirst.lean
               for the exact auxiliary and deriving skip rule.

Usage: python3 scripts/check-gly-rules.py [--rule F-n]... [--list-legacy]
[--write-baseline]. Exit 0: no failing finding; 1: a failing finding;
2: an input error (for example, the base commit cannot be read)."""
import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from collections import defaultdict

sys.dont_write_bytecode = True
import check_common as C
from source_layout import Layout  # noqa: E402

GEN = {'AvailableChainGeneric'}
FGSA_ALL = {'AvailableChainFGSA', 'AvailableChainFGSARun', 'AvailableChainFGSAClaims',
            'AvailableChainFGSAProofs', 'AvailableChainFGSAInhabit', 'AvailableChainPCSAProofs'}
COMPOSE = {'AvailableChainFGCompose'}
KITFG = {'AvailableChainKitFG'}
ALLOW = os.path.join(C.SCRIPTS, 'gly-rules-allow.txt')
F1_ALLOW = os.path.join(C.SCRIPTS, 'gly-f1-allow.txt')
F13_ALLOW = os.path.join(C.SCRIPTS, 'gly-f13-allow.txt')
F18_ALLOW = os.path.join(C.SCRIPTS, 'gly-f18-allow.txt')
GENFIRST_ALLOW = os.path.join(C.SCRIPTS, 'gly-genfirst-allow.txt')
GENFIRST_KEY = re.compile(r'GEN-FIRST (\S+) (\S+) -> (AvailableChain\.Gen\.\S+)')
GENFIRST_LINK = 'AvailableChain.FGSA.Run.fgsa_accepted_by_deadline_of_parentStored'
KITFG_DEF = os.path.join(C.BASELINES, 'kitfg-def-modules.txt')
THM = ('theorem', 'lemma')


def tok(names):
    """A regex for these identifiers as a whole name or a last component."""
    return re.compile(r'(?<![\w.₀-₉])(?:[\w₀-₉]+\.)*(' + '|'.join(names) + r')(?![\w₀-₉])')


def has_prefix(module, prefixes):
    return any(module == p or module.startswith(p + '.') for p in prefixes)


def read_allow():
    out = set()
    if os.path.exists(ALLOW):
        for line in open(ALLOW, encoding='utf-8'):
            line = line.split('#', 1)[0].split()
            if len(line) == 2:
                out.add(tuple(line))
    return out


def read_exact_allow(path, rule):
    out = []
    if os.path.exists(path):
        with open(path, encoding='utf-8') as f:
            for n, line in enumerate(f, 1):
                key, sep, reason = line.partition('#')
                key = key.strip()
                if not key:
                    continue
                where = f'{os.path.relpath(path, C.ROOT)}:{n}'
                if not sep or not reason.strip():
                    raise RuntimeError(f'{where}: {rule} allow entry needs a nonempty reason')
                if rule == 'F-1' and (not key.startswith('F-1 ') or ' :: ' not in key):
                    raise RuntimeError(f'{where}: expected a complete F-1 group key')
                if rule == 'F-13' and not re.fullmatch(
                        r"F-13 dup [\w'!?]+(?: [\w']+){2,}", key):
                    raise RuntimeError(f'{where}: expected an exact F-13 duplicate-name key')
                if rule == 'F-18' and not re.fullmatch(
                        r"F-18 [\w']+(?:\.[\w']+)+ (?:[\w'-]+/)+[\w'-]+\.lean", key):
                    raise RuntimeError(f'{where}: expected an exact F-18 declaration-and-file key')
                if rule == 'F-31' and not GENFIRST_KEY.fullmatch(key):
                    raise RuntimeError(f'{where}: expected an exact GEN-FIRST key')
                out.append((key, where))
    return out


def apply_exact_allow(findings, entries):
    current = {f.key for f in findings}
    allowed = {key for key, _ in entries}
    out = [f for f in findings if f.key not in allowed]
    for key, where in entries:
        if key not in current:
            msg = f'STALE ALLOW {where}: {key}'
            # A stale allow entry must fail even if a baseline lists its key.
            out.append(C.Finding(msg, msg, new=True))
    return out


def kitfg_def_modules():
    mods = set()
    if os.path.exists(KITFG_DEF):
        for line in open(KITFG_DEF, encoding='utf-8'):
            x = line.split('#', 1)[0].strip()
            if x:
                x = Layout(C.ROOT).module_of_source(x) if x.endswith('.lean') else x
                mods.add(x if x.startswith('AvailableChainKitFG') else 'AvailableChainKitFG.' + x)
    return mods


class Ctx:
    def __init__(self):
        self.scope = C.Scope()
        self.files = C.library_files()
        self.decls = {lf.path: C.declarations(lf) for lf in self.files}
        self.graph = C.import_graph(self.files)
        self.allow = read_allow()

    def new(self, lf):
        return self.scope.is_new_file(lf)

    def all_decls(self, libs=None):
        for lf in self.files:
            if libs is None or lf.lib in libs:
                for d in self.decls[lf.path]:
                    yield lf, d


def F(rule, key, msg, lf=None, new=None, review=False, **kw):
    return C.Finding(f'{rule} {key}', f'{rule}: {msg}', new=bool(new), review=review, **kw)


# ---------------------------------------------------------------------------
# Rules. Each returns a list of findings.

FIELD = re.compile(r'^\(?\s*([^\s:({\[⦃]+(?:\s+[^\s:({\[⦃]+)*)\s*(?::|\(|\{|\[|⦃)')


def struct_fields(d):
    t = d.text()
    m = re.search(r'\bwhere\b', t)
    if not m:
        return None
    lines = t[m.end():].split('\n')[1:]
    indent, fields = None, []
    for line in lines:
        if not line.strip():
            continue
        ind = len(line) - len(line.lstrip())
        if ind == 0:
            break
        if indent is None:
            indent = ind
        if ind != indent:
            continue
        s = line.strip()
        if re.match(r'^[\w₀-₉\']+\s*::', s):      # constructor name
            continue
        fm = FIELD.match(s)
        if fm:
            fields.extend(fm.group(1).split())
    return frozenset(fields) if fields else None


def rule_f1(x):
    allow = read_exact_allow(F1_ALLOW, 'F-1')
    groups = defaultdict(list)
    for lf, d in x.all_decls():
        if d.kind in ('structure', 'class'):
            fs = struct_fields(d)
            if fs:
                groups[fs].append((lf, d))
    out = []
    for fs, members in groups.items():
        if len(members) > 1:
            names = sorted(d.full for _, d in members)
            key = f'{",".join(sorted(fs))} :: {" ".join(names)}'
            out.append(F('F-1', key,
                         f'structures with the field set {{{", ".join(sorted(fs))}}}: {", ".join(names)}',
                         new=any(x.new(lf) for lf, _ in members), review=True))
    return apply_exact_allow(out, allow)


ROOT_PREMISES = tok(['RootInjectiveBelow', 'ViewRootInj', 'RootInjectiveOn', 'ContentAgree'])


def rule_f3(x):
    out = []
    for lf, d in x.all_decls(GEN | KITFG | FGSA_ALL | COMPOSE):
        if d.kind not in THM or ('F-3', d.full) in x.allow:
            continue
        prem, _ = d.premises_and_conclusion()
        for name in sorted({m.group(1) for m in ROOT_PREMISES.finditer(prem)}):
            out.append(F('F-3', f'{lf.module} {d.full} {name}',
                         f'{lf.path}:{d.line}: {d.full} takes a {name} premise', new=x.new(lf)))
    return out


def closure_rule(x, rule, starts, allowed):
    """Findings for each local module in the closure of each start module
    that `allowed(module)` rejects."""
    out = []
    by_mod = {lf.module: lf for lf in x.files}
    for m in sorted(starts):
        lf = by_mod[m]
        for bad in sorted(t for t in C.closure(x.graph, m) if t in by_mod and not allowed(t)):
            out.append(F(rule, f'{m} {bad}', f'{lf.path}: the import closure holds {bad}', new=x.new(lf)))
    return out


GEN_S_PURE = 'AvailableChainGeneric.Statements.Pure'
GEN_P_PURE = 'AvailableChainGeneric.Proofs.Pure'
GEN_S_V2 = 'AvailableChainGeneric.Statements.V2'
GEN_S_WALK = GEN_S_PURE + '.Walk'


def rule_f4(x):
    starts = [lf.module for lf in x.files if has_prefix(lf.module, [GEN_S_PURE, GEN_P_PURE])]
    ok = lambda t: has_prefix(t, ['AvailableChainModel.Objects', GEN_S_PURE, GEN_P_PURE,
                                  'AvailableChainGridCO.Model.Walk'])
    return closure_rule(x, 'F-4', starts, ok)


def rule_f5(x):
    out = []
    pat = re.compile(r'(?<![\w₀-₉])(?:Block)?\.genesis(?![\w₀-₉])')
    for lf, d in x.all_decls():
        if d.kind in THM and re.search(r'(Walk|Votes|Lease)', lf.module.rsplit('.', 1)[-1]):
            if pat.search(d.signature()):
                out.append(F('F-5', f'{lf.module} {d.full}',
                             f'{lf.path}:{d.line}: {d.full}: Block.genesis in the statement',
                             new=x.new(lf), review=True))
    return out


def grep_rule(x, rule, libs, pattern, what, module_filter=lambda m: True):
    out = []
    for lf in x.files:
        if lf.lib in libs and module_filter(lf.module):
            for m in pattern.finditer(lf.stripped):
                out.append(F(rule, f'{lf.module}', f'{lf.path}:{C.line_of(lf.stripped, m.start())}: {what}',
                             new=x.new(lf)))
    return out


def rule_f6(x):
    return grep_rule(x, 'F-6', GEN, tok(['slowLeasePolicy']), 'slowLeasePolicy in Generic')


def rule_f12(x):
    by_mod = {lf.module for lf in x.files}
    pure = [m for m in by_mod if has_prefix(m, [GEN_S_PURE]) and not has_prefix(m, [GEN_S_WALK])]
    v2 = [m for m in by_mod if has_prefix(m, [GEN_S_V2])]
    pure_ok = lambda t: has_prefix(t, ['AvailableChainModel.Objects', GEN_S_PURE]) and not has_prefix(t, [GEN_S_WALK])
    roots = [m for m in by_mod if has_prefix(m, ['AvailableChainEngineV2.Engine', 'AvailableChainEngineV2.Conditions',
                                                 'AvailableChainEngineV2.Laws', 'AvailableChainKitV2.ClockLaws',
                                                 'AvailableChainKitV2.DutyClockLaws'])]
    v2_allowed = set(roots)
    for r in roots:
        v2_allowed |= C.closure(x.graph, r)
    v2_ok = lambda t: pure_ok(t) or has_prefix(t, [GEN_S_V2]) or t in v2_allowed
    return closure_rule(x, 'F-12', pure, pure_ok) + closure_rule(x, 'F-12', v2, v2_ok)


def rule_f13(x):
    allow = read_exact_allow(F13_ALLOW, 'F-13')
    libs_of = defaultdict(set)
    where = defaultdict(list)
    for lf, d in x.all_decls():
        if d.kind in THM and d.name:
            libs_of[d.short].add(lf.lib)
            where[d.short].append((lf, d))
    out = []
    for short, libs in sorted(libs_of.items()):
        if len(libs) > 1:
            locs = ', '.join(f'{lf.path}:{d.line}' for lf, d in where[short])
            out.append(F('F-13', f'dup {short} {" ".join(sorted(libs))}',
                         f'theorem short name {short} in {len(libs)} libraries: {locs}',
                         new=any(x.new(lf) for lf, _ in where[short]), baselinable_in_new=True))
    for lf, d in x.all_decls(GEN):
        if d.kind in THM and d.private:
            out.append(F('F-13', f'private {lf.module} {d.full}',
                         f'{lf.path}:{d.line}: private theorem {d.full} in Generic', new=x.new(lf)))
    return apply_exact_allow(out, allow)


def rule_f14(x):
    out = []
    p = tok(['PartialSynchrony', 'HealthyPrefixDelivery'])
    c = tok(['handles', 'processed'])
    for lf, d in x.all_decls():
        if lf.lib in GEN or d.kind not in THM:
            continue
        prem, concl = d.premises_and_conclusion()
        if p.search(prem) and c.search(concl):
            out.append(F('F-14', f'{lf.module} {d.full}',
                         f'{lf.path}:{d.line}: {d.full}: PartialSynchrony/HealthyPrefixDelivery premise, '
                         f'handles/processed conclusion', new=x.new(lf), review=True))
    return out


def rule_f15(x):
    return grep_rule(x, 'F-15', GEN, re.compile('…'), '`…` in a Generic Statements module',
                     lambda m: '.Statements.' in m + '.')


def rule_f18(x):
    allow = read_exact_allow(F18_ALLOW, 'F-18')
    out = []
    for lf, d in x.all_decls():
        if d.kind in ('def', 'abbrev', 'structure', 'inductive') and 'window' in d.short.lower() \
                and not re.search(r'Schedule|Recurrence', lf.module):
            out.append(F('F-18', f'{d.full} {lf.path}', f'{lf.path}:{d.line}: window definition {d.full}',
                         new=x.new(lf), review=True))
    return apply_exact_allow(out, allow)


def rule_f20(x):
    out = []
    for lf, d in x.all_decls(GEN | FGSA_ALL):
        if re.search(r'_(of_pins|closed|landed)$', d.short):
            out.append(F('F-20', f'{lf.module} {d.full}', f'{lf.path}:{d.line}: staged name {d.full}',
                         new=x.new(lf)))
    return out


PLAN = re.compile(r'(?:^|(?<=[_.])|(?<=[a-z]))(T\d+|I\d+|W\d+|V[3-9]\d*|G_?F\d+[a-z]?|F\d+[a-z])(?=$|[_.A-Z])')


def rule_f21(x):
    out = []
    for lf, d in x.all_decls():
        if not d.name:
            continue
        toks = [m.group(1) for comp in d.name.split('.') for m in PLAN.finditer(comp)]
        if toks:
            out.append(F('F-21', f'{lf.module} {d.full}',
                         f'{lf.path}:{d.line}: plan vocabulary {",".join(toks)} in {d.full}', new=x.new(lf)))
    return out


REGIME = re.compile(r'(?<![\w.₀-₉])(?:[\w₀-₉]+\.)*(CleanCut₂|Outage₂|Recovery₂|HealthyPrefix₂|HealingInput|'
                    r'[\w₀-₉]+Set|[\w₀-₉]*Contract)(?![\w₀-₉])')


# L47 (lead ruling 2026-09-30): the regime-record producer module (P3 §3.1,
# §4.4). Its theorems may take ONE regime premise (they turn a regime into
# the small records); a theorem with two or more regime premises fails.
SHARED_REGIMES = 'AvailableChainFGSAProofs.Proofs.Shared.Regimes'
TYPE_HEAD = re.compile(r'[\w₀-₉.]+')


def _top_groups(text):
    """The top-level bracket groups of a binder text, without the brackets."""
    out, depth, start = [], 0, 0
    for i, c in enumerate(text):
        if c in '([{⦃⟨':
            if depth == 0:
                start = i + 1
            depth += 1
        elif c in ')]}⦄⟩':
            depth -= 1
            if depth == 0:
                out.append(text[start:i])
    return out


def _split_top(text, sep):
    parts, depth, last = [], 0, 0
    for i, c in enumerate(text):
        if c in '([{⦃⟨':
            depth += 1
        elif c in ')]}⦄⟩':
            depth -= 1
        elif depth == 0 and text.startswith(sep, i):
            parts.append(text[last:i])
            last = i + len(sep)
    return parts + [text[last:]]


def _is_regime_type(ty):
    m = TYPE_HEAD.match(ty.strip().lstrip('('))
    return bool(m and REGIME.fullmatch(m.group(0)))


def regime_premises(d):
    """The number of premises of d whose type head is a regime record, Set or
    Contract: binder names in bracket groups (named or anonymous) and
    top-level `→` premises of the type."""
    binders, ty = d.binders_and_type()
    n = 0
    for g in _top_groups(binders):
        names, colon, gty = g.partition(':')
        if not colon:
            names, gty = '', g
        if _is_regime_type(gty):
            n += max(1, len(names.split()))
    for part in _split_top(ty, '→')[:-1]:
        part = part.strip()
        if part.startswith(('(', '{', '[', '⦃')) and ':' in part:
            n += regime_premises_groups(part)
        elif _is_regime_type(part):
            n += 1
    return n


def regime_premises_groups(text):
    n = 0
    for g in _top_groups(text):
        names, colon, gty = g.partition(':')
        if colon and _is_regime_type(gty):
            n += max(1, len(names.split()))
    return n


def f23_findings(lf, decls, new=None):
    out = []
    shared = lf.lib in {'AvailableChainFGSAProofs', 'AvailableChainPCSAProofs'} and '.Shared.' in lf.module + '.'
    if not (lf.lib in GEN | KITFG | COMPOSE or shared):
        return out
    for d in decls:
        if d.kind not in THM:
            continue
        if lf.module == SHARED_REGIMES:
            n = regime_premises(d)
            if n > 1:
                out.append(F('F-23', f'{lf.module} {d.full} MULTI',
                             f'{lf.path}:{d.line}: {d.full} takes {n} regime premises '
                             f'(L47: at most one in {SHARED_REGIMES})', new=new))
            continue
        prem, _ = d.premises_and_conclusion()
        for name in sorted({m.group(1) for m in REGIME.finditer(prem)}):
            out.append(F('F-23', f'{lf.module} {d.full} {name}',
                         f'{lf.path}:{d.line}: {d.full} takes a {name} premise (a regime bundle)', new=new))
    return out


F23_CONTROLS = [
    # (module, source, expected keys)
    (SHARED_REGIMES, 'theorem A.one (h : Outage₂ p c E rho b) (hp : 0 < b) : FaultQ n a := rfl\n', set()),
    (SHARED_REGIMES, 'theorem A.two (h : Outage₂ p c E rho b) (h\' : Recovery₂ p c E rho G) : FaultQ n a := rfl\n',
     {f'F-23 {SHARED_REGIMES} A.two MULTI'}),
    (SHARED_REGIMES, 'theorem A.pair (h h\' : HealthyPrefix₂ p c E rho b) : Batch n a := rfl\n',
     {f'F-23 {SHARED_REGIMES} A.pair MULTI'}),
    (SHARED_REGIMES, 'theorem A.arrow (h : CleanCut₂ p c E rho b) : Outage₂ p c E rho b → FaultQ n a := rfl\n',
     {f'F-23 {SHARED_REGIMES} A.arrow MULTI'}),
    ('AvailableChainFGSAProofs.Proofs.Shared.Other',
     'theorem A.one (h : Outage₂ p c E rho b) : FaultQ n a := rfl\n',
     {'F-23 AvailableChainFGSAProofs.Proofs.Shared.Other A.one Outage₂'}),
]


def f23_controls():
    for module, src, expected in F23_CONTROLS:
        lf = C.LeanFile('AvailableChainFGSAProofs', module.replace('.', '/') + '.lean', module)
        lf._raw = src
        got = {f.key for f in f23_findings(lf, C.declarations(lf))}
        if got != expected:
            raise RuntimeError(f'F-23 control failed for {module}: expected {sorted(expected)}, got {sorted(got)}')
    print(f'F-23: {len(F23_CONTROLS)} L47 controls PASS')


def rule_f23(x):
    if os.environ.get('NEG', '1') == '1':
        f23_controls()
    out = []
    for lf in x.files:
        out += f23_findings(lf, x.decls[lf.path], new=x.new(lf))
    return out


def rule_f25(x):
    out = []
    for lf, d in x.all_decls():
        if d.kind in THM and re.search(r'keep|frame', d.short, re.I):
            if '∩' in d.premises_and_conclusion()[1]:
                out.append(F('F-25', f'{lf.module} {d.full}', f'{lf.path}:{d.line}: {d.full}: `∩` in the conclusion',
                             new=x.new(lf), review=True))
    return out


def rule_f26(x):
    return grep_rule(x, 'F-26', {'AvailableChainFGSAClaims'}, tok(['HealingInput']),
                     'HealingInput in Statements/Phases',
                     lambda m: has_prefix(m, ['AvailableChainFGSAClaims.Statements.Phases']))


def rule_f28(x):
    defs = kitfg_def_modules()
    out = []
    for lf, d in x.all_decls():
        if d.kind in THM and ('.Statements.' in lf.module + '.' or lf.module in defs) \
                and not d.short.endswith('_def') and not (
                    # DECISION P23-A / 04e0a138: exact old-safety projection, as in
                    # check-fgsa-claims.sh (user approval 2026-10-11).
                    lf.module == 'AvailableChainFGSAClaims.Statements.Regimes'
                    and d.full == 'AvailableChain.FGSA.Run.Base₂.idealization'):
            out.append(F('F-28', f'{lf.module} {d.full}', f'{lf.path}:{d.line}: theorem {d.full} in a Statements module',
                         new=x.new(lf)))
    return out


def rule_f30(x):
    out = []
    ns = re.compile(r'^\s*namespace\s+AvailableChain\.Generic(\.|\s|$)', re.M)
    for lf in x.files:
        if lf.lib in GEN:
            for m in ns.finditer(lf.stripped):
                out.append(F('F-30', f'namespace {lf.module}',
                             f'{lf.path}:{C.line_of(lf.stripped, m.start())}: namespace AvailableChain.Generic',
                             new=True))
    for lf, d in x.all_decls(GEN):
        if d.full.startswith('AvailableChain.Generic.'):
            out.append(F('F-30', f'decl {lf.module} {d.full}', f'{lf.path}:{d.line}: {d.full} in AvailableChain.Generic',
                         new=True))
    starts = [lf.module for lf in x.files if lf.lib in GEN]
    out += closure_rule(x, 'F-30', starts, lambda t: not has_prefix(t, ['AvailableChainGridCO.Proofs']))
    return out


def genfirst_run(command):
    try:
        result = subprocess.run(command, cwd=C.ROOT, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    except OSError as e:
        raise RuntimeError(f'GEN-FIRST could not run: {e}') from e
    if result.returncode:
        raise RuntimeError(f'GEN-FIRST command failed (rc {result.returncode}):\n{result.stdout}')
    return result.stdout


def genfirst_keys(output):
    keys = set()
    for line in output.splitlines():
        if line.startswith('GEN-FIRST '):
            if not GENFIRST_KEY.fullmatch(line):
                raise RuntimeError(f'malformed GEN-FIRST key: {line}')
            keys.add(line)
        elif not line.startswith('CheckGenFirst: '):
            raise RuntimeError(f'unexpected GEN-FIRST output: {line}')
    if not any(line.startswith('CheckGenFirst: scope ') for line in output.splitlines()):
        raise RuntimeError('GEN-FIRST helper did not report its scope')
    return keys


# ---------------------------------------------------------------------------
# GEN-FIRST controls. Compile a scratch module in scope; leave library sources intact.

def genfirst_controls(output):
    positive = GENFIRST_LINK
    if any(GENFIRST_KEY.fullmatch(key).group(1) == positive for key in genfirst_keys(output)):
        raise RuntimeError(f'POSITIVE CONTROL flagged: {positive}')
    print(f'F-31: POSITIVE CONTROL PASS: {positive} is not flagged')
    module = 'AvailableChainFGSARun.Tests.GenFirstControl'
    expected = {
        f'GEN-FIRST AvailableChain.FGSA.Run.fgsa_alias {module} -> AvailableChain.Gen.Pure.qF',
        f'GEN-FIRST AvailableChain.FGSA.Run.fgsa_alias_theorem {module} -> AvailableChain.Gen.Pure.qF_def',
    }
    with tempfile.TemporaryDirectory(prefix='genfirst-neg.', dir=os.path.join(C.ROOT, '.lake')) as scratch:
        # Lean selects one search directory per library. Keep its built data
        # with the extra module so the scratch directory does not hide it.
        built = os.path.join(C.ROOT, '.lake', 'build', 'lib', 'lean')
        shutil.copytree(os.path.join(built, 'AvailableChainFGSARun'),
                        os.path.join(scratch, 'AvailableChainFGSARun'))
        for name in os.listdir(built):
            if name.startswith('AvailableChainFGSARun.'):
                shutil.copy2(os.path.join(built, name), scratch)
        source = os.path.join(scratch, *module.split('.')) + '.lean'
        os.makedirs(os.path.dirname(source), exist_ok=True)
        with open(source, 'w', encoding='utf-8') as f:
            f.write('''module
public import AvailableChainGeneric.Statements.Pure.Quorum
public section
namespace AvailableChain.FGSA.Run
def fgsa_alias := @AvailableChain.Gen.Pure.qF
theorem fgsa_alias_theorem (n : Nat) :
    AvailableChain.Gen.Pure.qF n = (2 * n + 2) / 3 :=
  AvailableChain.Gen.Pure.qF_def n
end AvailableChain.FGSA.Run
end
''')
        genfirst_run(['lake', 'env', 'lean', '--root=' + scratch, '-o', source[:-5] + '.olean', source])
        # Set the scratch search path after lake env sets the built library paths.
        control = genfirst_run(['lake', 'env', 'bash', '-c',
                               'LEAN_PATH="$1:$LEAN_PATH" lean --run scripts/CheckGenFirst.lean "$2"',
                               'genfirst-control', scratch, module])
        actual = {key for key in genfirst_keys(control) if GENFIRST_KEY.fullmatch(key).group(2) == module}
        if actual != expected:
            raise RuntimeError(f'NEGATIVE CONTROL mismatch: expected {sorted(expected)}, got {sorted(actual)}')
        for key in sorted(actual):
            print(f'F-31: NEGATIVE CONTROL PASS: {key}')


def rule_f31(x):
    allow = read_exact_allow(GENFIRST_ALLOW, 'F-31')
    output = genfirst_run(['lake', 'env', 'lean', '--run', 'scripts/CheckGenFirst.lean',
                          '--expect', GENFIRST_LINK])
    keys = genfirst_keys(output)
    for line in output.splitlines():
        if line.startswith('CheckGenFirst: '):
            print(line)
    if os.environ.get('NEG', '1') == '1':
        genfirst_controls(output)
    # new=True prevents any baseline from accepting a GEN-FIRST finding.
    return apply_exact_allow([C.Finding(key, key, new=True) for key in sorted(keys)], allow)


RULES = {'F-1': rule_f1, 'F-3': rule_f3, 'F-4': rule_f4, 'F-5': rule_f5, 'F-6': rule_f6,
         'F-12': rule_f12, 'F-13': rule_f13, 'F-14': rule_f14,
         'F-15': rule_f15, 'F-18': rule_f18, 'F-20': rule_f20, 'F-21': rule_f21, 'F-23': rule_f23,
         'F-25': rule_f25, 'F-26': rule_f26, 'F-28': rule_f28, 'F-30': rule_f30,
         'F-31': rule_f31}


def main():
    ap = C.standard_args(argparse.ArgumentParser(description=__doc__.split('\n')[0]))
    for act in ap._actions:
        if act.dest == 'write_baseline':
            act.help = ('rewrite the baseline of each selected rule; allowed only in a commit whose '
                        'message names the rule and the reason; the reviewer reads the baseline diff; '
                        'the ADDED keys are printed as a WARNING')
    ap.add_argument('--rule', action='append', choices=list(RULES), help='run only this rule')
    a = ap.parse_args()
    x = Ctx()
    fails, errors = 0, 0
    for rule in a.rule or RULES:
        name = f'check-gly-rules-{rule}'
        try:
            findings = RULES[rule](x)
        except RuntimeError as e:
            print(f'{rule}: ERROR: {e}')
            errors += 1
            continue
        stale_allow = sum(f.msg.startswith('STALE ALLOW ') for f in findings)

        def report(line):
            if line.startswith('FAIL NEW-LIBRARY: STALE ALLOW '):
                line = line.removeprefix('FAIL NEW-LIBRARY: ')
            if rule in ('F-1', 'F-13', 'F-18', 'F-31') and line.startswith(f'{rule}: '):
                line += f', {stale_allow} stale allow entries'
            print(line)

        if a.write_baseline and rule == 'F-31':
            print('F-31: ERROR: GEN-FIRST has no baseline exemption; use an exact allow key')
            errors += 1
        elif a.write_baseline and not stale_allow:
            before = C.read_baseline(name)
            n = C.write_baseline(name, findings, [
                f'check (i) check-gly-rules, GLY §F rule {rule}: legacy findings.',
                f'Generated by: python3 scripts/check-gly-rules.py --rule {rule} --write-baseline'])
            added = sorted((C.read_baseline(name) - before).elements())
            print(f'{rule}: wrote {n} baseline entries')
            if added:
                print(f'WARNING {rule}: the rewrite ADDS {len(added)} key(s); name {rule} and the reason '
                      f'in the commit message: ' + ' | '.join(added))
            continue
        fails += C.evaluate(name, findings, a.list_legacy, title=rule, out=report)
    if a.write_baseline:
        return 2 if errors else (1 if fails else 0)
    print(f'check-gly-rules: {"FAIL" if fails or errors else "PASS"}: {fails} failing findings, '
          f'{errors} rule errors, {len(a.rule or RULES)} rules')
    return 2 if errors else (1 if fails else 0)


if __name__ == '__main__':
    sys.exit(main())
