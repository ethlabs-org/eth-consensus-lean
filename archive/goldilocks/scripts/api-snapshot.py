#!/usr/bin/env python3
"""Generate/check full compiled current graphs with the shared kernel extractor."""
import argparse
import importlib.util
import json
from pathlib import Path
from source_layout import Layout
import subprocess
import sys
import tempfile
from check_inventory import parse_names
import unported as U

spec = importlib.util.spec_from_file_location('deep', 'scripts/fgsa-deep.py')
deep = importlib.util.module_from_spec(spec)
spec.loader.exec_module(deep)
SCOPES = {
    'v2': ('AvailableChainEngineV2', 'AvailableChainKitV2'),
    'gen': ('AvailableChainGeneric',),
    'legacy': ('AvailableChainGridCO', 'AvailableChainSimplexFG',
               'AvailableChainKitFG', 'AvailableChainKit'),
    'compose': ('AvailableChainFGCompose',),
    'semantic': ('AvailableChainFramework', 'AvailableChainEngineV2',
                 'AvailableChainKitV2', 'AvailableChainGeneric', 'AvailableChainFGCompose',
                 'AvailableChainFGSA', 'AvailableChainFGSARun', 'AvailableChainFGSAClaims',
                 'AvailableChainFGSAProofs', 'AvailableChainFGSAInhabit'),
    'fg': ('AvailableChainSimplexFG', 'AvailableChainKitFG'),
    'fgsa': ('AvailableChainFGSA',),
    'fgsa-run': ('AvailableChainFGSARun',),
    'fgsa-claims': ('AvailableChainFGSAClaims', 'AvailableChainFGSAProofs',
                    'AvailableChainFGSAInhabit'),
}


def source_modules(libraries):
    modules = []
    layout = Layout(Path.cwd())
    for lib in libraries:
        try:
            facade = Path(layout.source_path(lib))
        except ValueError:
            raise ValueError('MISSING SOURCE SCOPE: ' + lib) from None
        if not facade.is_file() or not Path(layout.source_dir(lib)).is_dir():
            raise ValueError('MISSING SOURCE SCOPE: ' + lib)
        modules.append(lib)
        modules.extend(layout.module_of_source(p) for p in layout.source_files([lib]))
    return sorted(set(modules))


def checkpoint_modules(path):
    modules = [row['name'] for row in deep.root_list(path)]
    layout = Layout(Path.cwd())
    for module in modules:
        try:
            source = Path(layout.source_path(module))
        except ValueError:
            raise ValueError('MISSING CHECKPOINT MODULE: ' + module) from None
        if not source.is_file():
            raise ValueError('MISSING CHECKPOINT MODULE: ' + module)
    return modules


def extract(scope, inventory=False, roots=None,
            blueprint=Path('docs/internal/FGSA-BLUEPRINT-LEAN.json'),
            checkpoint='baseline', imports=None):
    libraries = SCOPES[scope]
    extra = ('AvailableChainPCSAProofs',) if (
        scope == 'fgsa-claims' and not inventory and not U.pcsa()) else ()
    if checkpoint == 'g-s1':
        if scope != 'semantic' or roots is None or imports is None or inventory:
            raise ValueError('G-S1 requires semantic roots and an explicit REQUIRED module list')
        modules = checkpoint_modules(imports)
    else:
        if imports is not None:
            raise ValueError('--imports is only valid at G-S1')
        modules = source_modules(libraries + extra)
    # Modules come from the source tree, independently of facades and inventories.
    imports = ', '.join('{ module := `' + m + ' }' for m in modules)
    lib_names = ', '.join('`' + lib for lib in libraries)
    helpers = Path('scripts/V2Manifest.lean').read_text().split('def main (args : List String)')[0]
    probe = f'''
def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{imports}] {{}}
  let _libs : Array Name := #[{lib_names}]
  let mut roots : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let some m := moduleOf? env n | continue
    unless _libs.any (·.isPrefixOf m) do continue
    if ← runCore env (generated n) then
      unless fgsaExplicit env n ci do continue
    roots := roots.push n
  if roots.isEmpty then throw (IO.userError "EMPTY COMPILED INVENTORY")
  IO.println (← deepSnapshot env roots).compress
  return 0
'''
    if scope in ('v2', 'gen'):
        first = probe.index('  let mut roots : Array Name')
        last = probe.index('  if roots.isEmpty', first)
        probe = probe[:first] + f'''  let decls ← runCore env (scan .{scope})
  let roots := decls.toArray.flatMap fun (_, xs) => xs.map (·.1)
''' + probe[last:]
    if scope == 'fgsa-claims' and not inventory:
        mapped = deep.strict_json(blueprint)
        # Only the PC-SA section is excluded. Every FG-SA mapped root stays required.
        mapped = {**mapped, 'safety_package': list(U.blueprint_clauses(mapped))}
        def theorem_names(value):
            if isinstance(value, dict):
                for key, row in value.items():
                    if key == 'theorem' and isinstance(row, str):
                        yield row
                    else:
                        yield from theorem_names(row)
            elif isinstance(value, list):
                for row in value:
                    yield from theorem_names(row)
        names = tuple(sorted(set(theorem_names(mapped))))
        parse_names(repr(names), 'blueprint theorem names')
        mapped_names = ', '.join('`' + n for n in names)
        at = probe.index('  if roots.isEmpty')
        probe = probe[:at] + f'''  let statements ← runCore env (scan .fgsa)
  let mapped : Array Name := #[{mapped_names}]
  for n in mapped do
    unless (env.find? n).isSome do
      throw (IO.userError s!"MISSING MAPPED ROOT {{n}}")
  let exports := roots.filter fun n => match moduleOf? env n with
    | some m => (`AvailableChainFGSAProofs.Proofs.Assembly).isPrefixOf m ||
        m.toString.endsWith ".Export" || mapped.contains n
    | none => false
  roots := (({{}} : Std.HashSet Name).insertMany
    ((statements.toArray.flatMap fun (_, xs) => xs.map (·.1)) ++ exports ++ mapped)).toArray
''' + probe[at:]
    if roots is not None:
        subjects = deep.root_list(roots)
        if checkpoint == 'g-s1':
            if any(not r.get('module') for r in subjects):
                raise ValueError('G-S1 subjects require exact module identities')
            subjects = [r for r in subjects if r['module'] in modules]
        subjects = ', '.join('`' + r['name'] for r in subjects)
        first = probe.index('  let mut roots : Array Name')
        last = probe.index('  if roots.isEmpty', first)
        probe = probe[:first] + f'''  let subjects : Array Name := #[{subjects}]
  let roots := subjects.filter fun n => (env.find? n).isSome
''' + probe[last:]
    if inventory:
        probe = probe.replace('  IO.println (← deepSnapshot env roots).compress',
                              '  IO.println (toJson (roots.qsort Name.lt |>.map '
                              'Name.toString)).compress')
    with tempfile.TemporaryDirectory(prefix='api-snapshot-') as scratch:
        path = Path(scratch) / 'Snapshot.lean'
        path.write_text(helpers + probe)
        result = subprocess.run(['lake', 'env', 'lean', '--run', str(path)],
                                capture_output=True, text=True)
        if result.returncode:
            raise ValueError(result.stdout + result.stderr)
        try:
            data = json.loads(result.stdout)
        except ValueError as exc:
            raise ValueError('INVALID COMPILED JSON: ' + result.stdout[:1200] +
                             result.stderr[-1200:]) from exc
    if not inventory:
        deep.validate_graph(data)
        data['pins'] = deep.pins()
        if checkpoint == 'g-s1':
            data['checkpoint'] = dict(name=checkpoint, modules=modules)
        if roots is not None:
            diagnostics = deep.root_diagnostics(None, data, deep.root_list(roots), checkpoint)
            deep.require_roots(dict(unresolved=diagnostics))
            data['pending'] = diagnostics
    return data


def check_snapshot(expected, actual):
    failures = deep.check_deep(expected, actual)
    if failures:
        raise ValueError('\n'.join(failures))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--scope', choices=SCOPES, required=True)
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    ap.add_argument('--output', type=Path)
    ap.add_argument('--roots', type=Path)
    ap.add_argument('--checkpoint', choices=('baseline', 'g-s1', 'g-s2', 'g-s3'),
                    default='baseline')
    ap.add_argument('--imports', type=Path, help='G-S1 REQUIRED modules, one exact name per line')
    args = ap.parse_args()
    path = args.output or Path('docs/internal/api') / (args.scope + '-api.json')
    data = extract(args.scope, roots=args.roots, checkpoint=args.checkpoint, imports=args.imports)
    if args.write:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(deep.render(data))
    else:
        check_snapshot(deep.read_baseline(path), data)
    print(f'{path}: PASS ({len(data["entries"])} roots; {len(data["nodes"])} nodes)')
    for row in data.get('pending', []):
        print('PENDING ROOT: ' + row['name'] + ': ' + row['reason'])


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError) as exc:
        print(f'API SNAPSHOT FAIL: {exc}', file=sys.stderr)
        sys.exit(1)
