#!/usr/bin/env python3
"""Check the complete current compose source inventory and global extensions."""
from pathlib import Path
from source_layout import Layout
from importlib import import_module
import re
import sys
sys.path.insert(0, 'scripts')
import check_common as C
from check_inventory import read_names

# Lean v4.34.1 declModifiers keywords, which may precede a constructor identifier.
MODIFIERS = {'private', 'public', 'protected', 'meta', 'noncomputable', 'unsafe',
             'partial', 'nonrec'}


def constructors(raw, d):
    """Collect simple inductive syntax; reject ambiguous terms and command layouts."""
    def reject(reason):
        raise SystemExit(f'UNSUPPORTED INDUCTIVE {d.full}: {reason}')

    lines = raw.splitlines()[d.line - 1:]
    header = C.DECL.match(lines[0])
    indent = len(header[1])
    body = [lines[0][header.end():]]
    for line in lines[1:]:
        if not line.strip():
            continue
        if len(line) - len(line.lstrip()) <= indent:
            if (C.DECL.match(line) or C.END.match(line) or C.NAMESPACE.match(line)
                    or C.SECTION.match(line) or re.match(r'\s*(?:#|variable\b|open\b)', line)):
                break
            reject('continuation must be indented below the header')
        body.append(line)
    derived = []
    # A final own-line `deriving DecidableEq` adds one instance with Lean's derived name.
    if len(body) > 1 and re.fullmatch(r'\s+deriving\s+DecidableEq\s*', body[-1]):
        # Lean capitalizes the type name; accept only names it leaves unchanged.
        if not re.fullmatch(r"[A-Z][\w']*", d.name):
            reject('derived instance name needs a simple capitalized type identifier')
        body.pop()
        derived.append(d.full[:-len(d.name)] + 'instDecidableEq' + d.name)
    text = '\n'.join(body)
    # Such terms can contain bars which are not constructor separators. Fail closed.
    commands = '|'.join(C.DECL_KW + ('match', 'by', 'let', 'do', 'if', 'fun', 'deriving',
                                    'namespace', 'section', 'end', 'variable', 'open', 'with',
                                    'private', 'protected', 'public', 'noncomputable', 'unsafe'))
    if re.search(r'\b(?:' + commands + r')\b|[#«»`]|:=|=>', text):
        reject('term syntax or command boundary needs a full Lean parser')
    names, stack, i = [], [], 0
    pairs = {'(': ')', '[': ']', '{': '}', '⦃': '⦄', '⟨': '⟩'}
    while i < len(text):
        char = text[i]
        if char in pairs:
            stack.append(pairs[char])
        elif char in pairs.values():
            if not stack or stack.pop() != char:
                reject('unbalanced delimiters')
        elif char == '|':
            if stack:
                reject('nested bar is not supported')
            ctor = re.match(r'\s*([^\s:({\[⦃]+)', text[i + 1:])
            if not ctor or not re.fullmatch(r"[^\W\d][\w'!?]*", ctor[1]):
                reject('unsupported constructor identifier after |')
            if ctor[1] in MODIFIERS:
                reject('constructor modifier is not supported')
            names.append(d.full + '.' + ctor[1])
            i += ctor.end()
        i += 1
    if stack:
        reject('unbalanced delimiters')
    return names, derived


expected = set(read_names('scripts/fg-compose-expected.txt'))
found = set()
derived = []
texts = []
files = [lf for lf in C.library_files() if lf.lib == 'AvailableChainFGCompose']
if not files or not Path(Layout(C.ROOT).source_path('AvailableChainFGCompose')).is_file():
    raise SystemExit('MISSING COMPOSE SOURCE SCOPE')
found.update(import_module('current-inventory').source_names('compose'))
for lf in files:
    raw = C.strip(Path(lf.path).read_text())
    texts.append(raw)
    # Statements expose their definitions. No other extension is permitted.
    if '.Statements.' in lf.module:
        raw = raw.replace('@[expose] public section', '')
    if re.search(r'@\[|\b(instance|notation|infix[lr]?|prefix|postfix|macro|syntax|attribute|'
                 r'initialize|register_option|elab|builtin_initialize|declare_syntax_cat|export|alias|'
                 r'register_simp_attr|declare_aesop_rule_sets)\b', raw):
        raise SystemExit('FORBIDDEN GLOBAL EXTENSION: ' + lf.module)
    if '.Statements.' in lf.module or '.Proofs.' in lf.module:
        for d in C.declarations(lf):
            if d.kind in ('def', 'abbrev', 'theorem', 'lemma', 'structure', 'inductive', 'opaque', 'irreducible_def'):
                if not d.private:
                    found.add(d.full)
                    if d.kind == 'inductive':
                        ctors, instances = constructors(raw, d)
                        found.update(ctors + instances)
                        derived.extend(instances)
        for name, body in re.findall(r'^structure (\w+).*?where\n(.*?)(?=^(?:variable|structure|def|theorem)|\Z)',
                                     raw, re.M | re.S):
            found.add('AvailableChain.FGCompose.' + name + '.mk')
            for field in re.findall(r'^  (\w+) :', body, re.M):
                found.add('AvailableChain.FGCompose.' + name + '.' + field)
layout = Layout(C.ROOT)
for logical in ('AvailableChainFGSAProofs/Proofs/Shared/FGCompose.lean',
                'AvailableChainPCSAProofs/Proofs/Shared/FGCompose.lean'):
    path = Path(C.ROOT) / layout.physical_path(logical)
    if path.exists():
        raw = C.strip(path.read_text())
        texts.append(raw)
        if re.search(r'@\[|\b(instance|notation|infix[lr]?|prefix|postfix|macro|syntax|attribute|'
                     r'initialize|register_option|elab|builtin_initialize|declare_syntax_cat|export|alias|'
                 r'register_simp_attr|declare_aesop_rule_sets)\b', raw):
            raise SystemExit('FORBIDDEN GLOBAL EXTENSION: ' + str(path))
# Lean renames a derived instance whose name is taken. Fail closed: every deriving clause
# must be a supported public one, derived names must be distinct, and no source text may
# mention a derived name (or a suffixed form of it) at all.
if sum(len(re.findall(r'\bderiving\b', t)) for t in texts) != len(derived):
    raise SystemExit('UNSUPPORTED INDUCTIVE deriving: a clause outside a supported public inductive')
for name in sorted(derived):
    short = name.rsplit('.', 1)[-1]
    if derived.count(name) > 1 or any(re.search(r'\b' + short, t) for t in texts):
        raise SystemExit(f'UNSUPPORTED INDUCTIVE {name}: derived instance name may be taken')
if found != expected:
    print('COMPOSE INVENTORY MISSING:', sorted(expected - found))
    print('COMPOSE INVENTORY UNLISTED:', sorted(found - expected))
    raise SystemExit(2)
print(f'Compose source coverage: {len(files)} modules; {len(expected)} public declarations/projections')
