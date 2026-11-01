"""Shared code of the text checks (BUILD §7.3, step-2 ruling D13).

Python 3 standard library only. The check scripts import this module from
their own directory (`python3 scripts/check-….py` puts `scripts/` on the
path).

- `ROOT` is the repository root (the parent of `scripts/`). Every path that
  a check prints is relative to it.
- Library files: every `.lean` file (extension in any case, symbolic links
  followed) of every `[[lean_lib]]` in lakefile.toml: the root file and the
  files under the library directory, under `srcDir` when the library sets
  one.
- Scope (BUILD §7.3): `scripts/new-libraries.txt` is the one list of the new
  libraries. On a new library (or a new module of a partly new library) a
  finding always fails. On a legacy library a finding that the baseline
  lists is a legacy finding; a finding that the baseline does not list
  fails.
- Baselines: `scripts/baselines/<name>.txt`, one finding key per line, as a
  multiset (a key that occurs twice is two findings). Keys carry no line
  numbers, so an edit elsewhere in a file does not change them.
- `strip(src)` replaces comments, strings and character literals with
  spaces and keeps every newline, so line numbers stay correct.
"""
import os
import re
import sys
import tomllib
from source_layout import Layout
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCRIPTS = os.path.join(ROOT, 'scripts')
BASELINES = os.path.join(SCRIPTS, 'baselines')
SCOPE_FILE = os.path.join(SCRIPTS, 'new-libraries.txt')


# ---------------------------------------------------------------------------
# Library files and modules

class LeanFile:
    def __init__(self, lib, path, module):
        self.lib = lib          # library name, e.g. AvailableChainGridCO
        self.path = path        # path relative to ROOT
        self.module = module    # module name, e.g. AvailableChainGridCO.Proofs.Map
        self._raw = None
        self._stripped = None

    @property
    def raw(self):
        if self._raw is None:
            with open(os.path.join(ROOT, self.path), encoding='utf-8') as f:
                self._raw = f.read()
        return self._raw

    @property
    def stripped(self):
        if self._stripped is None:
            self._stripped = strip(self.raw)
        return self._stripped

    @property
    def is_test(self):
        return '/Tests/' in '/' + self.path

    @property
    def is_facade(self):
        return self.module == self.lib


def libraries():
    """[(name, srcDir)] of every [[lean_lib]] in lakefile.toml."""
    return [(lib['name'], lib.get('srcDir', '.'))
            for lib in Layout(ROOT).declarations()]


def _is_lean(name):
    return name.lower().endswith('.lean')


def library_files():
    """Every library file, sorted by path."""
    layout = Layout(ROOT)
    return [LeanFile(layout.module_of_source(p).split('.')[0], p,
                     layout.module_of_source(p)) for p in layout.source_files()]


_layout_cache = {}


def source_layout():
    path = os.path.join(ROOT, 'lakefile.toml')
    stamp = (ROOT, os.stat(path).st_mtime_ns)
    if stamp not in _layout_cache:
        _layout_cache.clear()
        _layout_cache[stamp] = Layout(ROOT)
    return _layout_cache[stamp]


def logical_path(path):
    return source_layout().logical_path(path)


def canonical_key(key):
    """Normalize only the documented path token in stable finding keys."""
    tokens = key.split(' ')
    if tokens[0] in ('not-module', 'expose-attribute', 'expose-section', 'expose-decl',
                     'remove', 'add') and len(tokens) > 1:
        tokens[1] = logical_path(tokens[1])
    elif tokens[0] in ('F-18',) and len(tokens) > 2:
        tokens[2] = logical_path(tokens[2])
    elif tokens[0] in ('import-all', 'meta-import', 'plain-import', 'other-import',
                       'script-module') and len(tokens) > 1:
        # Header findings have <kind> <path> <token> keys.
        tokens[1] = logical_path(tokens[1])
    return ' '.join(tokens)


def module_path(module):
    """Path (relative to ROOT) of a local module, or None."""
    for lf in library_files():
        if lf.module == module:
            return lf.path
    return None


# ---------------------------------------------------------------------------
# Scope: the new libraries

class Scope:
    """Reads scripts/new-libraries.txt.

    `lib <Lib>`             every module of <Lib> is new.
    `partial <Lib>`         a module of <Lib> is new unless a `legacy` line
                            names it.
    `legacy <Module>`       a legacy module of a partial library.
    """

    def __init__(self, path=SCOPE_FILE):
        self.new_libs, self.partial_libs, self.legacy_modules = set(), set(), set()
        with open(path, encoding='utf-8') as f:
            for n, line in enumerate(f, 1):
                line = line.split('#', 1)[0].strip()
                if not line:
                    continue
                parts = line.split()
                if len(parts) != 2 or parts[0] not in ('lib', 'partial', 'legacy'):
                    sys.exit(f'{os.path.relpath(path, ROOT)}:{n}: bad line: {line}')
                {'lib': self.new_libs, 'partial': self.partial_libs,
                 'legacy': self.legacy_modules}[parts[0]].add(parts[1])

    def is_new(self, lib, module):
        if lib in self.new_libs:
            return True
        if lib in self.partial_libs:
            return module not in self.legacy_modules
        return False

    def is_new_file(self, lf):
        return self.is_new(lf.lib, lf.module)


def lib_of_module(module, libs=None):
    names = [n for n, _ in libraries()] if libs is None else libs
    best = None
    for n in names:
        if module == n or module.startswith(n + '.'):
            if best is None or len(n) > len(best):
                best = n
    return best


# ---------------------------------------------------------------------------
# Lexer: remove comments, strings and character literals

_IDENT_CHAR = re.compile(r"[\w'!?.₀-₉ₐ-ₜ]")


def strip(src):
    """Replace comments, string and char literals by spaces; keep newlines."""
    out = []
    i, n = 0, len(src)

    def blank(s):
        return ''.join(c if c == '\n' else ' ' for c in s)

    while i < n:
        c = src[i]
        if src.startswith('--', i):
            j = src.find('\n', i)
            j = n if j < 0 else j
            out.append(blank(src[i:j]))
            i = j
        elif src.startswith('/-', i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith('/-', j):
                    depth, j = depth + 1, j + 2
                elif src.startswith('-/', j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append(blank(src[i:j]))
            i = j
        elif c == '"' or (c == 'r' and re.match(r'r#*"', src[i:i + 16])
                          and (i == 0 or not _IDENT_CHAR.match(src[i - 1]))):
            if c == 'r':
                m = re.match(r'r(#*)"', src[i:])
                close = '"' + m.group(1)
                j = src.find(close, i + len(m.group(0)))
                j = n if j < 0 else j + len(close)
            else:
                j = i + 1
                while j < n and src[j] != '"':
                    j += 2 if src[j] == '\\' else 1
                j = min(j + 1, n)
            out.append(blank(src[i:j]))
            i = j
        elif c == "'" and (i == 0 or not _IDENT_CHAR.match(src[i - 1])):
            m = re.match(r"'(\\[^']{1,8}|[^\\'\n])'", src[i:])
            if m:
                out.append(blank(m.group(0)))
                i += len(m.group(0))
            else:
                out.append(c)
                i += 1
        else:
            out.append(c)
            i += 1
    return ''.join(out)


# ---------------------------------------------------------------------------
# Headers and imports

IMPORT = re.compile(r'^\s*((?:public|private)\s+)?(meta\s+)?import\s+(all\s+)?(.*)$')


def header(lf):
    """(is_module, [(line, public, meta, all, target)]) of a library file.

    The header is the `module` command and the import commands after it,
    read from the comment-free text. It ends at the first other command."""
    lines = lf.stripped.split('\n')
    k = 0
    while k < len(lines) and not lines[k].strip():
        k += 1
    is_module = k < len(lines) and re.match(r'^\s*module\b', lines[k]) is not None
    if is_module:
        k += 1
    imps = []
    while k < len(lines):
        s = lines[k].strip()
        if not s:
            k += 1
            continue
        m = IMPORT.match(lines[k])
        if not m:
            break
        for t in m.group(4).split():
            imps.append((k + 1, (m.group(1) or '').strip(), bool(m.group(2)),
                         bool(m.group(3)), t))
        k += 1
    return is_module, imps


def import_graph(files=None):
    """{module: [imported module]} over the library files (all targets,
    local or not)."""
    files = library_files() if files is None else files
    return {lf.module: [t for (_, _, _, _, t) in header(lf)[1]] for lf in files}


def closure(graph, start):
    """Local modules reachable from `start` through imports (not `start`)."""
    seen, stack = set(), list(graph.get(start, []))
    while stack:
        m = stack.pop()
        if m in seen or m not in graph:
            continue
        seen.add(m)
        stack.extend(graph[m])
    return seen


# ---------------------------------------------------------------------------
# Declarations

DECL_KW = ('theorem', 'lemma', 'def', 'abbrev', 'structure', 'class', 'inductive',
           'instance', 'opaque', 'axiom', 'example', 'irreducible_def')
DECL = re.compile(
    r'^(\s*)(?:@\[[^\]]*\]\s*)*'
    r'((?:(?:private|protected|public|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*)'
    r'(?:class\s+(?=inductive\b))?'
    r'(' + '|'.join(DECL_KW) + r')\b[ \t]*'
    r'(?:\([^)]*:=[^)]*\)\s*)?'            # instance (priority := …)
    r'([^\s:({\[⦃]*)')
NAMESPACE = re.compile(r'^\s*namespace\s+(\S+)')
SECTION = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:public|private|noncomputable)\s+)*section\b\s*(\S*)')
MUTUAL = re.compile(r'^\s*mutual\b')
END = re.compile(r'^\s*end\b\s*(\S*)')


class Decl:
    def __init__(self, lf, line, kind, name, full, mods, start, stop):
        self.lf = lf
        self.line = line        # 1-based line of the keyword
        self.kind = kind        # theorem, def, …
        self.name = name        # as written ('' for an anonymous instance)
        self.full = full        # with the namespace
        self.private = 'private' in mods
        self.start = start      # offset of the keyword line in lf.stripped
        self.stop = stop        # offset of the next declaration (or EOF)

    @property
    def short(self):
        return self.full.rsplit('.', 1)[-1]

    def text(self):
        return self.lf.stripped[self.start:self.stop]

    def signature(self):
        """The text from the keyword to the top-level `:=`, `|` or `where`."""
        t = self.text()
        m = re.search(r'\b' + re.escape(self.kind) + r'\b', t)
        t = t[m.start():] if m else t
        depth, i = 0, 0
        while i < len(t):
            c = t[i]
            if c in '([{⦃⟨':
                depth += 1
            elif c in ')]}⦄⟩':
                depth -= 1
            elif depth <= 0:
                if t.startswith(':=', i):
                    return t[:i]
                if c == '|' and not t[t.rfind('\n', 0, i) + 1:i].strip():
                    return t[:i]     # a pattern-matching `|` that starts a line
                if re.match(r'where\b', t[i:]) and (i == 0 or not _IDENT_CHAR.match(t[i - 1])):
                    return t[:i]
            i += 1
        return t

    def binders_and_type(self):
        """(binder text, type text) of the signature: split at the first
        top-level `:` after the name."""
        sig = self.signature()
        m = re.match(r'\s*\S+\s*' + (re.escape(self.name) if self.name else ''), sig)
        i = m.end() if m else 0
        depth = 0
        while i < len(sig):
            c = sig[i]
            if c in '([{⦃⟨':
                depth += 1
            elif c in ')]}⦄⟩':
                depth -= 1
            elif depth == 0 and c == ':' and not sig.startswith(':=', i):
                return sig[:i], sig[i + 1:]
            i += 1
        return sig, ''

    def premises_and_conclusion(self):
        """(premise text, conclusion text): the binders plus every
        top-level `→` premise of the type; the conclusion is the part after
        the last top-level `→` (a leading `∀ …,` is a premise)."""
        binders, ty = self.binders_and_type()
        parts, depth, last = [], 0, 0
        for i, c in enumerate(ty):
            if c in '([{⦃⟨':
                depth += 1
            elif c in ')]}⦄⟩':
                depth -= 1
            elif depth == 0 and c == '→':
                parts.append(ty[last:i])
                last = i + 1
        concl = ty[last:]
        prem = binders + ' ' + ' '.join(parts)
        # A leading `∀ binders,` of the conclusion is a premise.
        while True:
            m = re.match(r'\s*∀', concl)
            if not m:
                break
            depth, k = 0, m.end()
            while k < len(concl):
                c = concl[k]
                if c in '([{⦃⟨':
                    depth += 1
                elif c in ')]}⦄⟩':
                    depth -= 1
                elif depth == 0 and c == ',':
                    break
                k += 1
            prem += ' ' + concl[:k]
            concl = concl[k + 1:]
        return prem, concl


def declarations(lf):
    """Every declaration of a library file, with its full name."""
    text = lf.stripped
    lines = text.split('\n')
    offsets, off = [], 0
    for line in lines:
        offsets.append(off)
        off += len(line) + 1
    stack = []   # entries: ('ns', [components]) | ('sec', name) | ('mutual', '')
    found = []
    for k, line in enumerate(lines):
        m = NAMESPACE.match(line)
        if m:
            stack.append(('ns', m.group(1).split('.')))
            continue
        m = END.match(line)
        if m and not DECL.match(line):
            name = m.group(1)
            if stack:
                kind, val = stack[-1]
                if kind == 'ns' and name and name == '.'.join(val):
                    stack.pop()
                elif kind in ('sec', 'mutual') and (name == val or not name):
                    stack.pop()
                elif name and kind == 'ns':
                    # `end A.B` for `namespace A` + `namespace B`
                    comps = name.split('.')
                    while comps and stack and stack[-1][0] == 'ns' and stack[-1][1] == [comps[-1]]:
                        stack.pop()
                        comps.pop()
            continue
        m = SECTION.match(line)
        if m and not DECL.match(line):
            stack.append(('sec', m.group(1)))
            continue
        if MUTUAL.match(line):
            stack.append(('mutual', ''))
            continue
        m = DECL.match(line)
        if m:
            kind, name = m.group(3), m.group(4)
            if kind == 'example':
                name = ''
            ns = [c for kind_, val in stack if kind_ == 'ns' for c in val]
            if name.startswith('_root_.'):
                full = name[len('_root_.'):]
            elif name:
                full = '.'.join(ns + [name])
            else:
                full = '.'.join(ns + [f'<{kind}@{k + 1}>'])
            found.append(Decl(lf, k + 1, kind, name, full, m.group(2).split(),
                              offsets[k], None))
    for a, b in zip(found, found[1:] + [None]):
        a.stop = b.start if b else len(text)
    return found


def line_of(text, offset):
    return text.count('\n', 0, offset) + 1


# ---------------------------------------------------------------------------
# Findings, baselines and the report

class Finding:
    """key: stable baseline key; msg: text with the location; new: the file
    is in a new library (the finding always fails); review: the rule is a
    review list (listed, never fails)."""

    def __init__(self, key, msg, new=False, review=False, baselinable_in_new=False):
        self.key, self.msg, self.new, self.review = canonical_key(key), msg, new, review
        self.baselinable_in_new = baselinable_in_new


def baseline_path(name):
    return os.path.join(BASELINES, name + '.txt')


def read_baseline(name):
    p = baseline_path(name)
    if not os.path.exists(p):
        return Counter()
    with open(p, encoding='utf-8') as f:
        return Counter(l.rstrip('\n') for l in f if l.strip() and not l.startswith('#'))


def write_baseline(name, findings, header):
    keys = sorted(f.key for f in findings
                  if not f.new or f.baselinable_in_new)
    os.makedirs(BASELINES, exist_ok=True)
    with open(baseline_path(name), 'w', encoding='utf-8') as f:
        for h in header:
            f.write('# ' + h + '\n')
        for k in keys:
            f.write(k + '\n')
    return len(keys)


def evaluate(name, findings, list_legacy=False, title=None, out=print):
    """Compare findings with the baseline `name`. Print the result; return
    the number of failing findings."""
    title = title or name
    base = read_baseline(name)
    left = Counter(base)
    fails, legacy, review = [], [], []
    for f in findings:
        if f.new and not f.baselinable_in_new:
            (review if f.review else fails).append(('NEW-LIBRARY', f))
        elif left[f.key] > 0:
            left[f.key] -= 1
            legacy.append(f)
        else:
            (review if f.review else fails).append(('NEW', f))
    stale = sorted((+left).elements())
    for tag, f in fails:
        out(f'FAIL {tag}: {f.msg}')
    for tag, f in review:
        out(f'REVIEW {tag}: {f.msg}')
    if list_legacy:
        for f in legacy:
            out(f'legacy: {f.msg}')
    status = 'FAIL' if fails else 'PASS'
    out(f'{title}: {status}: {len(fails)} failing, {len(review)} to review, '
        f'{len(legacy)} legacy (baseline {sum(base.values())}), {len(stale)} stale baseline entries')
    for s in stale:
        out(f'  stale (no longer found; remove from scripts/baselines/{name}.txt): {s}')
    return len(fails)


def standard_args(ap):
    ap.add_argument('--list-legacy', action='store_true',
                    help='also list the legacy findings that the baseline covers')
    ap.add_argument('--write-baseline', action='store_true',
                    help='write the current legacy findings to the baseline and exit 0')
    return ap
