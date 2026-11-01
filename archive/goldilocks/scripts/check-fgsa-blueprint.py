#!/usr/bin/env python3
"""D10: check the FG-SA blueprint → Lean claim map.

Inputs:
- docs/internal/blueprint/fgsa/: an exact snapshot of the current blueprint chapters.
  SOURCE.json records the source path, the source repository head and the
  SHA-256 of each file.
- docs/internal/FGSA-BLUEPRINT-LEAN.json: the reviewed claim map.
- docs/internal/FGSA-BLUEPRINT-OPEN.md: the OPEN items, generated from the map.

The checker extracts the claim entries of outline §3 independently of the
map: every line that starts with a bold id (`**bp.…`, `**fj.…`, …), and every
inline `field (<id>)` inside an entry. A statement is the paragraph from the
entry line (or the inline id) to the first blank line, the next entry or the
next heading. The map must name each extracted id once, with its line,
section, paper status and statement SHA-256. It must also have the required
facets below. A facet statement is its parent statement, plus the paragraph at
its anchor when it has one.

Each Lean clause names a theorem, its owning module and its expected type
fingerprint. scripts/CheckBlueprintClaims.lean reads the compiled constants.
A clause passes only if the constant exists, is a theorem in that module, has
that fingerprint, and uses only propext, Classical.choice and Quot.sound. A
clause marked `aggregate` must also have no proposition binder and the
recorded binder count, so that a closed package cannot gain a law or proof
parameter. The fingerprint covers the field types of a structure that the
statement reaches.

The checker enforces the reviewed map. It cannot establish that a Lean type
means the same as the prose clause. A pass means: every blueprint item is
accounted for, and every active proof map passes. It does not mean that all
blueprint claims are proved while OPEN items remain; --require-proved checks
that stronger condition.

Modes: --check (default), --require-proved, --write (refresh the derived
fields and the OPEN document; review the diff), --selftest.
Exit codes: 0 pass; 1 a map, statement or Lean mismatch; 2 an input error.
"""
import argparse
import unported as U
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
from source_layout import Layout
import re
import shutil
import subprocess
import tempfile
import textwrap

REPO = Path(__file__).resolve().parents[1]
MAP = 'docs/internal/FGSA-BLUEPRINT-LEAN.json'
OPEN_DOC = 'docs/internal/FGSA-BLUEPRINT-OPEN.md'
SNAPSHOT = 'docs/internal/blueprint/fgsa'
ORACLE = 'scripts/CheckBlueprintClaims.lean'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
STATUSES = ('PROVED', 'PARTIAL', 'OPEN', 'HISTORICAL')
REQUIRED_FACETS = {
    'bp.firstFinality.v2': ('Rec_FE_W', 'Rec_F4_W', 'strong alternatives',
                            'qualified search B_best^F'),
    'bp.finalityLiveness.v2': ('FF5 Rec_FE_W', 'FF5 Rec_F4_W', 'FF6 Rec_FE_W', 'FF6 Rec_F4_W',
                               'FF7 Rec_FE_W', 'FF7 Rec_F4_W', 'strong alternatives', 'HP',
                               'FL-W/RF/D/T7'),
}
SAFETY_FIELDS = ('accountable', 'agreement', 'runAccountable', 'runAgreement',
                 'eventPrefixAgreement', 'finalizedMonotone', 'faultCountSlashableBound',
                 'honestNeverSlashed', 'assembled package')
PROTOCOLS = ('FG-SA', 'PC-SA')
# Every field of these structures needs a supplier map (fgsa_fields).
CLAIMS_SOURCE = 'AvailableChainFGSAClaims/FGSAClaims.lean'
CLAIMS_STRUCTURES = ('FGSASafetyClaims', 'FGSAClaims')
ID = r'[a-z][A-Za-z0-9]*(?:\.[A-Za-z0-9\-]+)+'
ENTRY = re.compile(r'^\*\*(' + ID + r')(?=[ *.])')
INLINE = re.compile(r'\bfield \((' + ID + r')\)')
HEADER = re.compile(r'^\*\*(.*?)\*\*')
PLACEHOLDER = re.compile(r'^(?:tbd|todo|open|n/?a|none|-+|\?+|unknown)\.?$', re.I)


class InputError(Exception):
    pass


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


def strict_json(path):
    def pairs(items):
        keys = [k for k, _ in items]
        dup = sorted({k for k in keys if keys.count(k) > 1})
        if dup:
            raise InputError(f'DUPLICATE JSON KEY in {path.name}: {", ".join(dup)}')
        return dict(items)
    if not path.is_file():
        raise InputError(f'MISSING INPUT: {path}')
    return json.loads(path.read_text(), object_pairs_hook=pairs)


# ---------------------------------------------------------------------------
# Snapshot and outline extraction

def load_snapshot(root):
    base = root / SNAPSHOT
    source = strict_json(base / 'SOURCE.json')
    files = source.get('files')
    if not isinstance(files, dict) or not files or source.get('outline') not in files:
        raise InputError('INVALID SNAPSHOT RECORD: files or outline')
    for key in ('source_path', 'source_repository_head'):
        if not source.get(key):
            raise InputError(f'INVALID SNAPSHOT RECORD: {key}')
    errors = []
    present = {p.name for p in base.iterdir() if p.name != 'SOURCE.json'}
    for name in sorted(present - set(files)):
        errors.append(f'UNLISTED SNAPSHOT FILE: {name}')
    for name, digest in sorted(files.items()):
        path = base / name
        if not path.is_file():
            raise InputError(f'MISSING SNAPSHOT FILE: {name}')
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            errors.append(f'SNAPSHOT HASH: {name}')
    return (base / source['outline']).read_text(), errors


def paragraph(lines, start, col=0):
    """The text from (start, col) to the first blank line, entry or heading."""
    out = [lines[start][col:]]
    for line in lines[start + 1:]:
        if not line.strip() or line.startswith('**') or line.startswith('#'):
            break
        out.append(line)
    return '\n'.join(out).rstrip()


def extract(outline):
    """Ordered {id: record} of outline §3 entries and inline ids."""
    lines = outline.split('\n')
    try:
        first = next(i for i, l in enumerate(lines) if l.startswith('## 3.'))
    except StopIteration:
        raise InputError('MISSING OUTLINE SECTION 3') from None
    last = next((i for i in range(first + 1, len(lines)) if lines[i].startswith('## ')), len(lines))
    found, section = {}, lines[first][3:].strip()
    for i in range(first, last):
        line = lines[i]
        if line.startswith('### '):
            section = line[4:].strip()
        m = ENTRY.match(line)
        if not m:
            continue
        cid = m.group(1)
        if cid in found:
            raise InputError(f'DUPLICATE OUTLINE ENTRY: {cid}')
        text = paragraph(lines, i)
        header = HEADER.match(line).group(1) if HEADER.match(line) else line
        found[cid] = {'kind': 'claim', 'line': i + 1, 'section': section,
                      'paper_status': header[len(cid):].strip(' —.'), 'statement': text}
        k = i
        for k in range(i, i + text.count('\n') + 1):
            for im in INLINE.finditer(lines[k]):
                iid = im.group(1)
                if iid in found:
                    raise InputError(f'DUPLICATE OUTLINE ENTRY: {iid}')
                found[iid] = {'kind': 'inline', 'parent': cid, 'line': k + 1, 'section': section,
                              'paper_status': 'inline in ' + cid,
                              'statement': paragraph(lines, k, im.start()) if k == i else
                              '\n'.join([lines[k][im.start():]] +
                                        text.split('\n')[k - i + 1:]).rstrip()}
    return found, lines[first:last]


def anchor_paragraph(section_lines, anchor):
    hits = [i for i, l in enumerate(section_lines) if l.startswith(anchor)]
    if len(hits) != 1:
        raise InputError(f'ANCHOR NOT UNIQUE: {anchor} ({len(hits)} matches)')
    return paragraph(section_lines, hits[0])


def claim_fields(root):
    """The fields of the FGSAClaims structures, read from the source."""
    path = root / Layout(root).physical_path(CLAIMS_SOURCE)
    if not path.is_file():
        raise InputError(f'MISSING SOURCE: {CLAIMS_SOURCE}')
    lines = path.read_text().split('\n')
    fields = []
    for name in CLAIMS_STRUCTURES:
        start = [i for i, l in enumerate(lines) if re.match(rf'^structure {name}\b', l)]
        if len(start) != 1:
            raise InputError(f'MISSING STRUCTURE: {name} in {CLAIMS_SOURCE}')
        found = []
        for line in lines[start[0] + 1:]:
            if line and not line.startswith(' '):
                break
            m = re.match(r'^  ([A-Za-z_][A-Za-z0-9_]*) :', line)
            if m:
                found.append(m.group(1))
        if not found:
            raise InputError(f'NO FIELDS: {name} in {CLAIMS_SOURCE}')
        fields += found
    return fields


# ---------------------------------------------------------------------------
# The Lean oracle

def module_source(root, module):
    return root / Layout(root).source_path(module)


def module_olean(root, module):
    return root / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')


def compiled_clauses(data):
    """Defer only the PC-SA safety section, regardless of a row's module field."""
    return list(all_clauses(data, compiled=True))


def run_oracle(root, clauses):
    """Read active constants only. Deferred source/map rows are checked in run."""
    groups = {}
    for c in clauses:
        groups.setdefault('active', set()).add((c['module'], c['theorem']))
    results = {}
    with tempfile.TemporaryDirectory(prefix='fgsa-blueprint.', dir=root / '.lake') as tmp:
        for group, pairs in sorted(groups.items()):
            request = Path(tmp) / f'{group}.txt'
            request.write_text(''.join(f'import {m}\n' for m in sorted({m for m, _ in pairs})) +
                               ''.join(f'const {t}\n' for t in sorted({t for _, t in pairs})))
            proc = subprocess.run(['lake', 'env', 'lean', '--run', str(REPO / ORACLE), str(request)],
                                  cwd=root, text=True, capture_output=True)
            if proc.returncode != 0:
                raise InputError('ORACLE INPUT ERROR: ' + (proc.stderr + proc.stdout).strip()[-2000:])
            results.update(parse_oracle(proc.stdout))
    return results


def parse_oracle(text):
    out = {}
    for line in text.splitlines():
        if line.startswith('MISSING '):
            out[line.split()[1]] = None
        elif line.startswith('CONST '):
            parts = line.split()
            fields = dict(p.split('=', 1) for p in parts[2:])
            fields['axioms'] = set() if fields['axioms'] == '-' else set(fields['axioms'].split(','))
            out[parts[1]] = fields
    return out


def compare_clause(c, got, where):
    name = c['theorem']
    if got is None:
        return [f'MISSING CONSTANT: {name} ({where})']
    errors = []
    if got['kind'] != 'theorem':
        errors.append(f'INVALID PROOF CONSTANT: {name} is a {got["kind"]} ({where})')
    bad = sorted(got['axioms'] - ALLOWED_AXIOMS)
    if bad:
        errors.append(f'INVALID PROOF CONSTANT: {name} uses axioms {",".join(bad)} ({where})')
    if got['module'] != c['module']:
        errors.append(f'OWNER MISMATCH: {name} is in {got["module"]}, map says {c["module"]} ({where})')
    if got['fingerprint'] != c.get('type_fingerprint'):
        errors.append(f'TYPE MISMATCH: {name} fingerprint {got["fingerprint"]}, '
                      f'map says {c.get("type_fingerprint")} ({where})')
    if c.get('aggregate') and (got['props'] != '0' or got['binders'] != str(c.get('binders'))):
        errors.append(f'AGGREGATE TYPE MISMATCH: {name} has {got["binders"]} binders, '
                      f'{got["props"]} propositions; map says {c.get("binders")} and 0 ({where})')
    return errors


# ---------------------------------------------------------------------------
# The map

def all_clauses(data, compiled=False):
    for e in data['entries']:
        for c in e.get('clauses', []):
            yield e['id'], c
    for proto, rows in data.get('safety_package', {}).items():
        for c in rows:
            if compiled and proto == 'PC-SA' and U.pcsa() and c.get('field') in SAFETY_FIELDS:
                continue
            yield f'safety {proto} {c.get("field")}', c
    for c in data.get('additional_results', []):
        yield f'additional {c.get("id")}', c
    for c in data.get('fgsa_fields', []):
        yield f'FGSAClaims field {c.get("field")}', c


def statement_of(entry, found, section_lines):
    if entry['kind'] == 'facet':
        parent = found.get(entry.get('parent'))
        if parent is None:
            return None
        text = parent['statement']
        if entry.get('anchor'):
            text += '\n\n' + anchor_paragraph(section_lines, entry['anchor'])
        return text
    rec = found.get(entry['id'])
    return rec['statement'] if rec else None


def open_document(data):
    lines = ['# FG-SA blueprint: OPEN items', '',
             'Generated from `docs/internal/FGSA-BLUEPRINT-LEAN.json` by',
             '`python3 scripts/check-fgsa-blueprint.py --write`. Do not edit by hand.', '',
             'An OPEN item names a blueprint clause that has no reviewed Lean proof map.',
             'The D10 check passes with these items open; `--require-proved` fails while',
             'any item remains.', '']
    for e in data['entries']:
        if not e.get('open'):
            continue
        lines.append(f'## {e["id"]} ({e["lean_status"]})')
        lines.append('')
        for o in e['open']:
            line = f'- `{o["id"]}`: {o["missing"]}'
            if e['id'].startswith('bp.finalityLiveness.v2#FF'):
                lines.extend(textwrap.wrap(line, width=100, subsequent_indent='  ',
                                           break_long_words=False, break_on_hyphens=False))
            else:
                lines.append(line)
        lines.append('')
    return '\n'.join(lines).rstrip('\n')


def check_map(data, found, section_lines, fields=()):
    errors = []
    entries = data.get('entries')
    if not isinstance(entries, list) or not entries:
        return ['EMPTY MAP']
    ids = [e.get('id') for e in entries]
    for cid in sorted({i for i in ids if ids.count(i) > 1}):
        errors.append(f'DUPLICATE CLAIM: {cid}')
    byid = {e['id']: e for e in entries}
    for cid in found:
        if cid not in byid:
            errors.append(f'MISSING CLAIM: {cid}')
    for parent, labels in REQUIRED_FACETS.items():
        for label in labels:
            if f'{parent}#{label}' not in byid:
                errors.append(f'MISSING FACET: {parent}#{label}')
    open_ids = []
    for e in entries:
        cid, kind, status = e['id'], e.get('kind'), e.get('lean_status')
        if kind in ('claim', 'inline'):
            rec = found.get(cid)
            if rec is None:
                errors.append(f'UNKNOWN CLAIM: {cid}')
                continue
            if rec['kind'] != kind or rec.get('parent') != e.get('parent'):
                errors.append(f'KIND MISMATCH: {cid}')
            for key in ('line', 'section', 'paper_status'):
                if e.get(key) != rec[key]:
                    errors.append(f'{key.upper()} MISMATCH: {cid}: {e.get(key)!r} != {rec[key]!r}')
        elif kind == 'facet':
            parent = e.get('parent')
            label = cid.split('#', 1)[1] if '#' in cid else ''
            if parent not in found or cid != f'{parent}#{label}':
                errors.append(f'UNKNOWN CLAIM: {cid}')
                continue
            if label not in REQUIRED_FACETS.get(parent, ()):
                errors.append(f'UNKNOWN FACET: {cid}')
        else:
            errors.append(f'INVALID KIND: {cid}')
            continue
        try:
            text = statement_of(e, found, section_lines)
        except InputError as err:
            errors.append(f'{err} ({cid})')
            continue
        if text is None or e.get('statement_sha256') != sha(text):
            errors.append(f'STATEMENT HASH: {cid}')
        clauses, opens = e.get('clauses', []), e.get('open', [])
        facets = [f for f in entries if f.get('kind') == 'facet' and f.get('parent') == cid]
        if status not in STATUSES:
            errors.append(f'INVALID STATUS: {cid}: {status}')
        elif facets:
            want = 'PROVED' if all(f.get('lean_status') == 'PROVED' for f in facets) else 'PARTIAL'
            if status != want or clauses or opens:
                errors.append(f'FACET STATUS: {cid} must be {want} with its clauses in facets')
        elif status == 'PROVED' and (not clauses or opens):
            errors.append(f'PROVED WITHOUT COMPLETE MAP: {cid}')
        elif status == 'PARTIAL' and (not clauses or not opens):
            errors.append(f'PARTIAL WITHOUT CLAUSES AND OPEN ITEMS: {cid}')
        elif status == 'OPEN' and not opens:
            errors.append(f'INCOMPLETE OPEN RECORD: {cid} has no OPEN item')
        elif status == 'HISTORICAL':
            header = found.get(cid, {}).get('paper_status', '')
            if clauses or opens or not e.get('note') or not re.search(r'WITHDRAWN|historical',
                                                                     header, re.I):
                errors.append(f'INVALID HISTORICAL ENTRY: {cid}')
        for k, o in enumerate(opens, 1):
            text = (o.get('missing') or '').strip()
            if o.get('id') != f'OPEN.{cid}.{k}' or len(text) < 20 or PLACEHOLDER.match(text):
                errors.append(f'INCOMPLETE OPEN RECORD: {cid} item {k}')
            open_ids.append(o.get('id'))
        for c in clauses:
            if not all(c.get(k) for k in ('clause', 'theorem', 'module')):
                errors.append(f'INCOMPLETE CLAUSE: {cid}')
    safety = data.get('safety_package', {})
    for proto in PROTOCOLS:
        present = [c.get('field') for c in safety.get(proto, [])]
        for field in SAFETY_FIELDS:
            if present.count(field) != 1:
                errors.append(f'MISSING SAFETY FIELD: {proto} {field}')
    mapped = [c.get('field') for c in data.get('fgsa_fields', [])]
    for field in fields:
        if field not in mapped:
            errors.append(f'MISSING FGSACLAIMS FIELD: {field}')
    for field in sorted(set(mapped) - set(fields)):
        errors.append(f'UNKNOWN FGSACLAIMS FIELD: {field}')
    return errors


def derive(data, found, section_lines, oracle):
    """Refresh the derived fields (--write). Review fields are unchanged."""
    for e in data['entries']:
        rec = found.get(e['id'])
        if rec:
            e['line'], e['section'], e['paper_status'] = rec['line'], rec['section'], rec['paper_status']
        text = statement_of(e, found, section_lines)
        if text is not None:
            e['statement_sha256'] = sha(text)
    for _, c in all_clauses(data):
        got = oracle.get(c['theorem'])
        if got:
            c['type_fingerprint'] = got['fingerprint']
            if c.get('aggregate'):
                c['binders'] = int(got['binders'])
    order = ('id', 'kind', 'parent', 'anchor', 'line', 'section', 'paper_status',
             'statement_sha256', 'lean_status', 'clauses', 'open', 'note')
    data['entries'] = [{k: e[k] for k in order if k in e} for e in data['entries']]


def summary(data, oracle_errors):
    entries = data['entries']
    count = {s: sum(e['lean_status'] == s for e in entries) for s in STATUSES}
    claims = sum(e['kind'] in ('claim', 'inline') for e in entries)
    facets = sum(e['kind'] == 'facet' for e in entries)
    opens = sum(len(e.get('open', [])) for e in entries)
    for e in entries:
        names = ', '.join(c['theorem'].rsplit('.', 1)[-1] for c in e.get('clauses', [])) or '-'
        print(f'{e["id"]:<48} {e["lean_status"]:<10} {len(e.get("open", []))} open  {names}')
    for proto in PROTOCOLS:
        bad = [x for x in oracle_errors if f'safety {proto} ' in x]
        rows = data['safety_package'][proto]
        status = 'FAIL' if bad else 'PASS'
        if rows and proto == 'PC-SA' and U.pcsa() and all(
                c.get('field') in SAFETY_FIELDS for c in rows):
            status = 'DEFERRED (source/map only)'
        print(f'safety package {proto}: {status} ({len(rows)} fields)')
    print(f'claims {claims}; facets {facets}; PROVED {count["PROVED"]}; PARTIAL {count["PARTIAL"]}; '
          f'OPEN {count["OPEN"]}; HISTORICAL {count["HISTORICAL"]}; OPEN items {opens}')
    return count


def run(root, mode='check', oracle=None, oleans=None):
    """mode: check, require-proved or write. `oracle` replaces the compiled oracle, and
    `oleans=False` skips the olean test (selftests)."""
    try:
        outline, errors = load_snapshot(root)
        found, section_lines = extract(outline)
        fields = claim_fields(root)
        data = strict_json(root / MAP)
        clauses = list(all_clauses(data))
        active = compiled_clauses(data)
        for _, c in clauses:
            if not module_source(root, c.get('module', '')).is_file():
                raise InputError(f'MISSING SOURCE: {c.get("module")} for {c.get("theorem")}')
        for _, c in active:
            if (oleans if oleans is not None else oracle is None) and \
                    not module_olean(root, c['module']).is_file():
                raise InputError(f'MISSING OLEAN: {c["module"]} for {c["theorem"]}')
        got = oracle(active) if oracle else run_oracle(root, [c for _, c in active])
    except (InputError, json.JSONDecodeError) as err:
        print(f'fgsa-blueprint: INPUT ERROR: {err}')
        return 2
    if mode == 'write':
        if errors:
            print('\n'.join(errors))
            return 1
        derive(data, found, section_lines, got)
        (root / MAP).write_text(json.dumps(data, indent=1, ensure_ascii=False) + '\n')
        (root / OPEN_DOC).write_text(open_document(data) + '\n')
        print(f'fgsa-blueprint: wrote {MAP} and {OPEN_DOC}; review the diff')
        mode = 'check'
    errors += check_map(data, found, section_lines, fields)
    oracle_errors = []
    for where, c in active:
        oracle_errors += compare_clause(c, got.get(c['theorem']), where)
    errors += oracle_errors
    doc = root / OPEN_DOC
    if not doc.is_file() or doc.read_text() != open_document(data) + '\n':
        errors.append(f'OPEN DOCUMENT OUT OF DATE: {OPEN_DOC}; run --write')
    if errors:
        print('\n'.join(errors))
        print(f'fgsa-blueprint: FAIL ({len(errors)} errors)')
        return 1
    count = summary(data, oracle_errors)
    if mode == 'require-proved':
        unproved = count['PARTIAL'] + count['OPEN']
        if unproved:
            print(f'fgsa-blueprint: FAIL: UNPROVED CLAIMS: {unproved} entries have OPEN items')
            return 1
    print('fgsa-blueprint: PASS (every blueprint item is accounted for; '
          'every active proof map passes)')
    return 0


# ---------------------------------------------------------------------------
# Selftest

OUTLINE = """# Fixture outline

## 3. Fixed statement list

### 3.1 Fixture

**bp.alpha.v1 — NEW — PROVED-paper.** Alpha holds.
Second line of alpha. Growth field (bp.alphaGrowth.v1): alpha grows.

**bp.beta.v1 — OPEN.** Beta is open.

**bp.old.v1 — historical; WITHDRAWN for current use.** Old form.

**bp.firstFinality.v2 — PROVED-paper.** First finality.

**bp.finalityLiveness.v2 — PROVED-paper.** Liveness.

**FF6 / FF7 window instances.** Use the window.

## 4. Next
"""

FIXTURE_FACETS = {**{('bp.firstFinality.v2', f): 'PROVED' for f in REQUIRED_FACETS['bp.firstFinality.v2']},
                  **{('bp.finalityLiveness.v2', f): 'PROVED'
                     for f in REQUIRED_FACETS['bp.finalityLiveness.v2']}}


def fixture_map():
    def clause(name, **kw):
        return dict({'clause': 'fixture clause', 'theorem': 'Fix.' + name,
                     'module': 'Fix.Proofs', 'type_fingerprint': 'f' * 16}, **kw)
    entries = [
        {'id': 'bp.alpha.v1', 'kind': 'claim', 'lean_status': 'PROVED', 'clauses': [clause('alpha')],
         'open': []},
        {'id': 'bp.alphaGrowth.v1', 'kind': 'inline', 'parent': 'bp.alpha.v1', 'lean_status': 'PROVED',
         'clauses': [clause('alpha')], 'open': []},
        {'id': 'bp.beta.v1', 'kind': 'claim', 'lean_status': 'OPEN', 'clauses': [],
         'open': [{'id': 'OPEN.bp.beta.v1.1', 'missing': 'Beta has no Lean statement in the fixture.'}]},
        {'id': 'bp.old.v1', 'kind': 'claim', 'lean_status': 'HISTORICAL', 'clauses': [], 'open': [],
         'note': 'Withdrawn.'},
        {'id': 'bp.firstFinality.v2', 'kind': 'claim', 'lean_status': 'PROVED', 'clauses': [], 'open': []},
        {'id': 'bp.finalityLiveness.v2', 'kind': 'claim', 'lean_status': 'PROVED', 'clauses': [],
         'open': []},
    ]
    for (parent, label), status in FIXTURE_FACETS.items():
        e = {'id': f'{parent}#{label}', 'kind': 'facet', 'parent': parent, 'lean_status': status,
             'clauses': [clause('alpha')], 'open': []}
        if label.startswith('FF6'):
            e['anchor'] = '**FF6 / FF7 window instances.**'
        entries.append(e)
    safety = {p: [clause('alpha', field=f) for f in SAFETY_FIELDS] for p in PROTOCOLS}
    safety['FG-SA'][-1].update(theorem='Fix.package', aggregate=True, binders=1)
    safety['PC-SA'][-1].update(theorem='Fix.package', aggregate=True, binders=1)
    fields = [clause('alpha', field=f) for f in ('base', 'extra')]
    return {'version': 1, 'entries': entries, 'safety_package': safety, 'additional_results': [],
            'fgsa_fields': fields}


def fixture_oracle(table):
    def oracle(clauses):
        return {c['theorem']: (dict(table[c['theorem']]) if table.get(c['theorem']) else None)
                for _, c in clauses}
    return oracle


GOOD = {'Fix.alpha': {'kind': 'theorem', 'module': 'Fix.Proofs', 'fingerprint': 'f' * 16,
                      'binders': '2', 'props': '1', 'axioms': {'propext'}},
        'Fix.package': {'kind': 'theorem', 'module': 'Fix.Proofs', 'fingerprint': 'f' * 16,
                        'binders': '1', 'props': '0', 'axioms': set()}}


def make_fixture(root, outline=OUTLINE, data=None, src="."):
    (root / 'lakefile.toml').write_text(
        'srcDir="' + src + '"\n'
        '[[lean_lib]]\nname="Fix"\n[[lean_lib]]\nname="AvailableChainFGSAClaims"\n')
    snap = root / SNAPSHOT
    snap.mkdir(parents=True)
    (snap / '00-outline.md').write_text(outline)
    (snap / 'SOURCE.json').write_text(json.dumps({
        'source_path': 'fixture', 'source_repository_head': '0' * 40, 'outline': '00-outline.md',
        'files': {'00-outline.md': hashlib.sha256(outline.encode()).hexdigest()}}))
    (root / src / 'Fix').mkdir(parents=True)
    (root / Layout(root).source_path('Fix.Proofs')).write_text('-- fixture\n')
    claims = root / Layout(root).physical_path(CLAIMS_SOURCE)
    claims.parent.mkdir(parents=True)
    claims.write_text('structure FGSASafetyClaims (p : Nat) : Prop where\n  base : True\n\n'
                      'structure FGSAClaims (p : Nat) : Prop extends FGSASafetyClaims p where\n'
                      '  extra : True\n')
    (root / 'docs').mkdir(exist_ok=True)
    (root / MAP).write_text(json.dumps(data or fixture_map()))
    # Derive the hashes and the OPEN document as --write does.
    with contextlib.redirect_stdout(io.StringIO()):
        assert run(root, 'write', fixture_oracle(GOOD)) == 0, 'fixture write'


def selftest():
    with tempfile.TemporaryDirectory(prefix='blueprint-nested-') as tmp:
        root = Path(tmp)
        make_fixture(root, src="src")
        with contextlib.redirect_stdout(io.StringIO()):
            assert run(root, oracle=fixture_oracle(GOOD), oleans=False) == 0
        assert module_source(root, "Fix.Proofs") == root / "src/Fix/Proofs.lean"
        print("SELFTEST fgsa-blueprint nested source/oracle fixture: PASS")
    def edit_map(root, fn):
        data = json.loads((root / MAP).read_text())
        fn(data)
        (root / MAP).write_text(json.dumps(data))

    def drop(cid):
        return lambda d: d.update(entries=[e for e in d['entries'] if e['id'] != cid])

    def oracle_change(name, **kw):
        table = {k: dict(v) for k, v in GOOD.items()}
        if kw.get('missing'):
            table[name] = None
        else:
            table[name].update(kw)
        return fixture_oracle(table)

    def entry(cid, **kw):
        def fn(d):
            for e in d['entries']:
                if e['id'] == cid:
                    e.update(kw)
        return fn

    cases = [
        ('valid theorem and explicit OPEN item', None, None, None, 'check', 0,
         'OPEN items 1'),
        ('blueprint id removed from map', drop('bp.beta.v1'), None, None, 'check', 1,
         'MISSING CLAIM: bp.beta.v1'),
        ('inline growth id omitted', drop('bp.alphaGrowth.v1'), None, None, 'check', 1,
         'MISSING CLAIM: bp.alphaGrowth.v1'),
        ('FF6 facet omitted', drop('bp.finalityLiveness.v2#FF6 Rec_FE_W'), None, None, 'check', 1,
         'MISSING FACET: bp.finalityLiveness.v2#FF6 Rec_FE_W'),
        ('duplicate claim id', lambda d: d['entries'].append(dict(d['entries'][0])), None, None,
         'check', 1, 'DUPLICATE CLAIM: bp.alpha.v1'),
        ('unknown claim id', lambda d: d['entries'].append(dict(d['entries'][0], id='bp.ghost.v1')),
         None, None, 'check', 1, 'UNKNOWN CLAIM: bp.ghost.v1'),
        ('blueprint clause changed', None, OUTLINE.replace('Alpha holds.', 'Alpha fails.'), None,
         'check', 1, 'STATEMENT HASH: bp.alpha.v1'),
        ('facet anchor changed', None, OUTLINE.replace('Use the window.', 'Use no window.'), None,
         'check', 1, 'STATEMENT HASH: bp.finalityLiveness.v2#FF6 Rec_FE_W'),
        ('missing theorem', None, None, oracle_change('Fix.alpha', missing=True), 'check', 1,
         'MISSING CONSTANT: Fix.alpha'),
        ('missing source', entry('bp.alpha.v1', clauses=[{
            'clause': 'c', 'theorem': 'Fix.alpha', 'module': 'Fix.Absent',
            'type_fingerprint': 'f' * 16}]), None, None, 'check', 2, 'MISSING SOURCE: Fix.Absent'),
        ('missing snapshot file', 'unlink-outline', None, None, 'check', 2,
         'MISSING SNAPSHOT FILE: 00-outline.md'),
        ('same theorem name, different type', None, None,
         oracle_change('Fix.alpha', fingerprint='0' * 16), 'check', 1, 'TYPE MISMATCH: Fix.alpha'),
        ('theorem assigned to wrong owner', None, None,
         oracle_change('Fix.alpha', module='Fix.Other'), 'check', 1, 'OWNER MISMATCH: Fix.alpha'),
        ('definition as proof', None, None, oracle_change('Fix.alpha', kind='definition'), 'check', 1,
         'INVALID PROOF CONSTANT: Fix.alpha is a definition'),
        ('project axiom as proof', None, None,
         oracle_change('Fix.alpha', axioms={'propext', 'Fix.bad'}), 'check', 1,
         'INVALID PROOF CONSTANT: Fix.alpha uses axioms Fix.bad'),
        ('OPEN item with no reason', entry('bp.beta.v1', open=[{'id': 'OPEN.bp.beta.v1.1',
                                                                'missing': 'TBD'}]),
         None, None, 'check', 1, 'INCOMPLETE OPEN RECORD: bp.beta.v1 item 1'),
        ('OPEN entry with no item', entry('bp.beta.v1', open=[]), None, None, 'check', 1,
         'INCOMPLETE OPEN RECORD: bp.beta.v1 has no OPEN item'),
        ('PROVED with an OPEN item', entry('bp.alpha.v1', open=[{
            'id': 'OPEN.bp.alpha.v1.1', 'missing': 'A clause that the fixture leaves open.'}]),
         None, None, 'check', 1, 'PROVED WITHOUT COMPLETE MAP: bp.alpha.v1'),
        ('added law parameter in an aggregate', None, None,
         oracle_change('Fix.package', binders='2', props='1'), 'check', 1,
         'AGGREGATE TYPE MISMATCH: Fix.package'),
        ('missing FGSAClaims field map', lambda d: d['fgsa_fields'].pop(), None, None, 'check', 1,
         'MISSING FGSACLAIMS FIELD: extra'),
        ('missing safety field', lambda d: d['safety_package']['PC-SA'].pop(), None, None, 'check', 1,
         'MISSING SAFETY FIELD: PC-SA assembled package'),
        ('OPEN document out of date', 'stale-open', None, None, 'check', 1,
         'OPEN DOCUMENT OUT OF DATE'),
        ('empty map', lambda d: d.update(entries=[]), None, None, 'check', 1, 'EMPTY MAP'),
        ('OPEN map with --require-proved', None, None, None, 'require-proved', 1,
         'UNPROVED CLAIMS: 1'),
    ]
    cases.append(('missing olean', 'check-oleans', None, None, 'check', 2,
                  'MISSING OLEAN: Fix.Proofs for Fix.alpha'))
    for label, change, outline, oracle, mode, code, reason in cases:
        with tempfile.TemporaryDirectory(prefix='fgsa-blueprint-selftest.') as tmp:
            root = Path(tmp)
            make_fixture(root)
            if outline is not None:
                snap = root / SNAPSHOT
                (snap / '00-outline.md').write_text(outline)
                source = json.loads((snap / 'SOURCE.json').read_text())
                source['files']['00-outline.md'] = hashlib.sha256(outline.encode()).hexdigest()
                (snap / 'SOURCE.json').write_text(json.dumps(source))
            if change == 'unlink-outline':
                (root / SNAPSHOT / '00-outline.md').unlink()
            elif change == 'check-oleans':
                pass
            elif change == 'stale-open':
                (root / OPEN_DOC).write_text('stale\n')
            elif change is not None:
                edit_map(root, change)
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                rc = run(root, mode, oracle or fixture_oracle(GOOD),
                         oleans=True if change == 'check-oleans' else None)
            text = out.getvalue()
            assert rc == code and reason in text, (label, rc, text)
            print(f'SELFTEST fgsa-blueprint {label}: PASS (rc {code}; {reason})', flush=True)
    # The compiled oracle on built constants: a theorem passes; a definition does not.
    module = 'AvailableChainFGCompose.Tests.SafetyControls'
    if module_olean(REPO, module).is_file():
        ns = 'AvailableChain.FGCompose.Tests.SafetyControls.'
        got = run_oracle(REPO, [{'module': module, 'theorem': ns + 'unordered_read'},
                                {'module': module, 'theorem': ns + 'deliveredScope'},
                                {'module': module, 'theorem': ns + 'absentControl'}])
        thm, dfn = got[ns + 'unordered_read'], got[ns + 'deliveredScope']
        assert thm['kind'] == 'theorem' and thm['module'] == module, thm
        assert not compare_clause({'theorem': ns + 'unordered_read', 'module': module,
                                   'type_fingerprint': thm['fingerprint']}, thm, 'compiled')
        errors = compare_clause({'theorem': ns + 'deliveredScope', 'module': module,
                                 'type_fingerprint': dfn['fingerprint']}, dfn, 'compiled')
        assert errors == [f'INVALID PROOF CONSTANT: {ns}deliveredScope is a definition (compiled)'], errors
        assert got[ns + 'absentControl'] is None
        print('SELFTEST fgsa-blueprint compiled oracle: PASS (theorem accepted; definition and '
              'missing constant rejected)', flush=True)
    else:
        print(f'SELFTEST fgsa-blueprint compiled oracle: FAIL (missing olean for {module})')
        return 2
    print('fgsa-blueprint selftest: PASS')
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--check', action='store_true')
    group.add_argument('--require-proved', action='store_true')
    group.add_argument('--write', action='store_true')
    group.add_argument('--selftest', action='store_true')
    args = parser.parse_args()
    if args.selftest:
        return selftest()
    mode = 'write' if args.write else 'require-proved' if args.require_proved else 'check'
    return run(REPO, mode)


if __name__ == '__main__':
    raise SystemExit(main())
