#!/usr/bin/env python3
"""Use isolated source and compiled fixtures with the real Compose checks."""
import os
from pathlib import Path
from source_layout import Layout
import shutil
import subprocess
import tempfile

REPO = Path(__file__).resolve().parents[1]
LAYOUT = Layout(REPO)


def run(args, cwd=REPO, env=None):
    return subprocess.run(args, cwd=cwd, env=env, text=True, capture_output=True)


SAFETY_CONTROLS = 'AvailableChainFGCompose/Tests/SafetyControls.lean'


def require_safety_controls(base):
    """The P13 behavior controls are required; a missing file fails."""
    if not (Path(base) / Layout(base).physical_path(SAFETY_CONTROLS)).is_file():
        raise SystemExit(f'MISSING SAFETY CONTROLS: {SAFETY_CONTROLS}')


def require(label, result, code, reason):
    output = result.stdout + result.stderr
    assert result.returncode == code and reason in output, (label, result.returncode, output)
    print(f'CONTROL Compose {label}: PASS (rc {code}; {reason})', flush=True)


with tempfile.TemporaryDirectory(prefix='compose-controls.', dir=REPO / '.lake') as tmp:
    root = Path(tmp)
    base = run(['lake', 'env', 'printenv', 'LEAN_PATH'])
    assert base.returncode == 0, base.stderr

    def fixture(label):
        tree = root / label
        tree.mkdir()
        shutil.copytree(REPO / 'scripts', tree / 'scripts', ignore=shutil.ignore_patterns('__pycache__'))
        (tree / 'lakefile.toml').write_text(
            'name = "fixture"\ndefaultTargets = ["AvailableChainFGCompose"]\n'
            '[[lean_lib]]\nname = "AvailableChainFGCompose"\n'
            'globs = ["AvailableChainFGCompose.*"]\n')
        (tree / 'AvailableChainFGCompose').mkdir()
        # The pure audit scans its source scope before the Compose audit.
        built = REPO / '.lake/build/lib/lean'
        for lib in ('AvailableChainSimplexFG', 'AvailableChainKitFG'):
            shutil.copytree(REPO / LAYOUT.source_dir(lib), tree / lib)
            shutil.copy2(REPO / LAYOUT.source_path(lib), tree / (lib + ".lean"))
            with (tree / "lakefile.toml").open("a") as config:
                config.write('[[lean_lib]]\nname = "' + lib + '"\n')
            shutil.copytree(built / lib, tree / lib, dirs_exist_ok=True)
            for part in built.glob(lib + '.olean*'):
                shutil.copy2(part, tree / part.name)
        env = dict(os.environ, LEAN_PATH=str(tree) + os.pathsep + base.stdout.strip())
        return tree, env

    def compile_module(tree, env, module, body):
        source = tree / (module.replace('.', '/') + '.lean')
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(body)
        result = run(['lake', 'env', 'env', 'LEAN_PATH=' + env['LEAN_PATH'], 'lean',
                      '-o', str(source.with_suffix('.olean')), str(source)], env=env)
        assert result.returncode == 0, (module, result.stdout, result.stderr)
        return source

    def audit(tree, env, *args):
        return run(['lake', 'env', 'env', 'LEAN_PATH=' + env['LEAN_PATH'], 'lean', '--run',
                    str(REPO / 'scripts/CheckFGAxioms.lean'), '--compose', *args], tree, env)

    tree, env = fixture('empty-source-scope')
    compile_module(tree, env, 'AvailableChainFGCompose', 'module\n')
    require('empty source scope', audit(tree, env), 2, 'EMPTY COMPOSE SOURCE SCOPE')

    module = 'AvailableChainFGCompose.Proofs.Orphan'
    for label, body, code, reason in [
        ('positive', 'public section\ntheorem present : True := True.intro\n', 0, 'Compose checked'),
        ('sorry orphan', 'public section\ntheorem present : True := by sorry\n', 1, 'sorryAx'),
        ('private project axiom', 'private axiom bad : False\nprivate theorem present : False := bad\n',
         1, 'BAD AXIOMS'),
        ('native orphan', 'public section\ntheorem present : (1 : Nat) = 1 := by native_decide\n',
         1, 'BAD AXIOMS'),
        ('compiled forbidden import', 'public import AvailableChainFGSA.Model.Store\n'
         'public section\ntheorem present : True := True.intro\n', 1, 'COMPILED IMPORT NOT ALLOWED'),
    ]:
        tree, env = fixture(label.replace(' ', '-'))
        compile_module(tree, env, 'AvailableChainFGCompose', 'module\n')
        compile_module(tree, env, module, 'module\npublic import Lean.Elab.Tactic.Decide\n' + body)
        require(label, audit(tree, env), code, reason)
        if label == 'positive':
            require('missing expected beside present', audit(tree, env, '--expect', 'present', 'absent'),
                    2, 'NOT CHECKED: absent')
            require('bad arguments', audit(tree, env, '--typo'), 2, 'USAGE:')
            missing = tree / 'AvailableChainFGCompose/Proofs/Missing.lean'
            missing.write_text('module\n')
            require('missing olean', audit(tree, env), 2, 'COMPOSE INPUT ERROR:')
            missing.rename(tree / 'missing-source.saved')
            (tree / 'AvailableChainFGCompose.lean').rename(tree / 'root.saved')
            require('missing source root', audit(tree, env), 2, 'MISSING COMPOSE ROOT')

    # Keep lower libraries available, but exclude the real Compose output.
    fallback = root / 'lower-oleans'
    fallback.mkdir()
    for entry in (REPO / '.lake/build/lib/lean').iterdir():
        if not entry.name.startswith('AvailableChainFGCompose'):
            (fallback / entry.name).symlink_to(entry, target_is_directory=entry.is_dir())
    # Exercise the introduced safety paths, without fallback to real oleans.
    for name in ('Statements.SafetyReads', 'Statements.SafetyStore', 'Statements.SafetyClient',
                 'Statements.SafetyClaims', 'Proofs.SafetyStore', 'Proofs.SafetyAccountable',
                 'Proofs.SafetyClient', 'Proofs.SafetyCount', 'Proofs.SafetyMonotone',
                 'Proofs.SafetySlashing'):
        tree, env = fixture('safety-' + name)
        env['LEAN_PATH'] = os.pathsep.join([str(fallback), *[part for part in
            env['LEAN_PATH'].split(os.pathsep) if part != str(REPO / '.lake/build/lib/lean')]])
        compile_module(tree, env, 'AvailableChainFGCompose', 'module\n')
        target = 'AvailableChainFGCompose.' + name
        source = compile_module(tree, env, target,
                                'module\npublic section\n'
                                'namespace SafetyControl\n'
                                'def present : Prop := True\nend SafetyControl\n')
        require('safety ' + name + ' coverage', audit(tree, env, '--expect', 'SafetyControl.present'),
                0, 'Compose checked')
        require('safety ' + name + ' missing name', audit(tree, env, '--expect', 'SafetyControl.absent'),
                2, 'NOT CHECKED: SafetyControl.absent')
        source.with_suffix('.olean').rename(tree / 'saved.olean')
        require('safety ' + name + ' missing olean', audit(tree, env), 2, 'COMPOSE INPUT ERROR:')
        compile_module(tree, env, target,
                       'module\nprivate axiom bad : False\nprivate theorem present : False := bad\n')
        require('safety ' + name + ' forbidden axiom', audit(tree, env), 1, 'BAD AXIOMS')

    # A forbidden extra root is exempt only for itself, never for its imports.
    for dep in ('AvailableChainEngineV2.Engine.Duty.Run', 'AvailableChainFGCompose.Statements.EventReads'):
        tree, env = fixture('pure-' + dep.split('.')[0])
        # Lean resolves a library prefix in the first search directory.
        # Preserve the built pure library when adding its orphan control.
        built = REPO / '.lake/build/lib/lean'
        shutil.copytree(built / 'AvailableChainKitFG', tree / 'AvailableChainKitFG',
                        dirs_exist_ok=True)
        for part in built.glob('AvailableChainKitFG.olean*'):
            shutil.copy2(part, tree / part.name)
        shutil.copytree(built / 'AvailableChainFGCompose', tree / 'AvailableChainFGCompose',
                        dirs_exist_ok=True)
        for part in built.glob('AvailableChainFGCompose.olean*'):
            shutil.copy2(part, tree / part.name)
        compile_module(tree, env, 'AvailableChainKitFG.Control', f'module\npublic import {dep}\n')
        require('pure closure ' + dep, audit(tree, env, '--root', 'AvailableChainKitFG.Control'),
                1, 'FORBIDDEN LIBRARY IN THE FG IMPORT CLOSURE:')

    for label, dep in [('fgsa', 'AvailableChainFGSA.Model.Store'), ('unknown', 'UnknownComposeLibrary')]:
        tree, env = fixture('closure-' + label)
        if label == 'unknown':
            compile_module(tree, env, dep, 'module\npublic section\ndef unknownValue := 0\n')
        compile_module(tree, env, 'AvailableChainFGCompose', 'module\n')
        compile_module(tree, env, module, f'module\npublic import {dep}\npublic section\ndef value := 0\n')
        require('closure ' + label, audit(tree, env), 1,
                'FORBIDDEN LIBRARY IN THE COMPOSE IMPORT CLOSURE:')

    # Source controls use checker copies so removing each scope can be tested.
    tree, env = fixture('source-scopes')
    source = tree / 'AvailableChainFGCompose/Proofs/Control.lean'
    source.parent.mkdir(parents=True, exist_ok=True)
    positive = 'module\npublic section\nnamespace Control\ntheorem good : True := True.intro\n'
    for rule, premise in [('F-3', 'RootInjectiveBelow'), ('F-23', 'Outage₂')]:
        source.write_text(positive + 'end Control\n')
        args = ['python3', '-B', 'scripts/check-gly-rules.py', '--rule', rule]
        require(rule + ' positive', run(args, tree), 0, 'check-gly-rules: PASS')
        source.write_text(positive + f'theorem bad (h : {premise}) : True := True.intro\nend Control\n')
        require(rule + ' scope', run(args + ['--list-legacy'], tree), 1, premise + ' premise')
        keys = ['python3', '-B', '-c',
                "import sys, runpy; sys.path.insert(0, 'scripts'); a=runpy.run_path('scripts/check-gly-rules.py'); "
                "print('\\n'.join(f.key for f in a['RULES'][" + repr(rule) + "](a['Ctx']())))"]
        exact_key = f'{rule} AvailableChainFGCompose.Proofs.Control Control.bad {premise}'
        require(rule + ' exact key', run(keys, tree), 0, exact_key)

        checker = tree / 'scripts/check-gly-rules.py'
        original = checker.read_text()
        checker.write_text(original.replace("COMPOSE = {'AvailableChainFGCompose'}", 'COMPOSE = set()'))
        result = run(args, tree)
        assert result.returncode == 0 and 'Control.bad takes' not in result.stdout, result.stdout
        try:
            require(rule + ' removed-scope runner', run(keys, tree), 0, exact_key)
        except AssertionError:
            pass
        else:
            raise AssertionError('scope mutation escaped the control runner')

        print(f'CONTROL Compose {rule} removed scope: expected diagnostic is absent', flush=True)
        checker.write_text(original)

    # Run the syntax scan itself. An axiom-audit refusal cannot replace it.
    for lib in ('AvailableChainSimplexFG', 'AvailableChainKitFG'):
        (tree / lib).mkdir(exist_ok=True)
        (tree / (lib + '.lean')).write_text('module\n')
    (tree / 'AvailableChainFGCompose.lean').write_text('module\n')
    source.write_text(positive + 'end Control\n')
    syntax = ['bash', 'scripts/check-fg-syntax.sh']
    require('syntax positive', run(syntax, tree), 0, '')
    source.write_text('module\nexample : True := by native_decide\n')
    require('syntax scope', run(syntax, tree), 1,
            'native evaluation in AvailableChainFGCompose/Proofs/Control.lean')
    checker = tree / 'scripts/check-fg-syntax.sh'
    original = checker.read_text()
    checker.write_text(original.replace(' AvailableChainFGCompose;', ';')
                       .replace('AvailableChainSimplexFG AvailableChainKitFG '
                                'AvailableChainFGCompose)',
                                'AvailableChainSimplexFG AvailableChainKitFG)'))
    result = run(syntax, tree)
    assert result.returncode == 0
    try:
        require('syntax removed-scope runner', result, 1, 'native evaluation in')
    except AssertionError:
        pass
    else:
        raise AssertionError('syntax scope mutation escaped the control runner')
    print('CONTROL Compose syntax removed scope: expected diagnostic is absent', flush=True)

    tree, env = fixture('f13-exact')
    with (tree / 'lakefile.toml').open('a') as out:
        out.write('[[lean_lib]]\nname = "AvailableChainFGSAClaims"\n')
    allow = tree / 'scripts/gly-f13-allow.txt'
    allow.write_text('F-13 dup preTick_def AvailableChainFGCompose AvailableChainFGSAClaims # exact\n'
                     'F-13 dup postClock_def AvailableChainFGCompose AvailableChainFGSAClaims # exact\n')
    paths = []
    for lib, ns in [('AvailableChainFGCompose', 'ComposeControl'),
                    ('AvailableChainFGSAClaims', 'ClaimsControl')]:
        path = tree / lib / 'Statements/Control.lean'
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f'module\npublic section\nnamespace {ns}\n'
                        'theorem preTick_def : True := True.intro\n'
                        'theorem postClock_def : True := True.intro\nend ' + ns + '\n')
        paths.append(path)
    args = ['python3', '-B', 'scripts/check-gly-rules.py', '--rule', 'F-13']
    require('F-13 exact positive', run(args, tree), 0, '0 stale allow entries')
    for path in paths:
        with path.open('a') as out:
            out.write('theorem unrelatedDup : True := True.intro\n')
    require('F-13 unrelated duplicate', run(args, tree), 1, 'unrelatedDup')
    with allow.open('a') as out:
        out.write('F-13 dup stale AvailableChainFGCompose AvailableChainFGSAClaims # stale\n')
    require('F-13 stale exact allow', run(args, tree), 1, 'STALE ALLOW')

    # The compiled GEN-FIRST checker must see the new library by lakefile scope.
    tree, env = fixture('gen-first')
    compile_module(tree, env, 'AvailableChainKitFG',
                   'module\npublic section\ndef retainedScope (n : Nat) : Nat := n + 1\n')
    compile_module(tree, env, 'AvailableChainFGCompose', 'module\n')
    compile_module(tree, env, module,
                   'module\npublic import AvailableChainGeneric.Statements.Pure.Quorum\n'
                   'public section\nnamespace Control\n'
                   'def good (n : Nat) : Nat := n + 1\n'
                   'def bad (n : Nat) : Nat := AvailableChain.Gen.Pure.qF n\nend Control\n')
    key = f'GEN-FIRST Control.bad {module} -> AvailableChain.Gen.Pure.qF'
    args = ['lake', 'env', 'env', 'LEAN_PATH=' + env['LEAN_PATH'], 'lean', '--run',
            str(tree / 'scripts/CheckGenFirst.lean')]
    result = run(args, tree, env)
    require('GEN-FIRST scope', result, 0, key)
    assert 'GEN-FIRST Control.good ' not in result.stdout
    checker = tree / 'scripts/CheckGenFirst.lean'
    checker.write_text(checker.read_text().replace('  library == "AvailableChainFGCompose" ||\n', ''))
    result = run(args, tree, env)
    assert result.returncode == 0 and key not in result.stdout, result.stdout + result.stderr
    try:
        require('GEN-FIRST removed-scope runner', result, 0, key)
    except AssertionError:
        pass
    else:
        raise AssertionError('GEN-FIRST scope mutation escaped the control runner')
    print('CONTROL Compose GEN-FIRST removed scope: expected diagnostic is absent', flush=True)

    # The source extension guard must reject an orphan, including Tests.
    tree, env = fixture('global-extension')
    shutil.copytree(REPO / LAYOUT.source_dir('AvailableChainFGCompose'),
                    tree / 'AvailableChainFGCompose',
                    dirs_exist_ok=True)
    shutil.copy2(REPO / LAYOUT.source_path('AvailableChainFGCompose'),
                 tree / 'AvailableChainFGCompose.lean')
    for rel in ('AvailableChainFGCompose/Tests/Orphan.lean',):
        path = tree / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text('module\n@[simp] theorem bad : True := True.intro\n')
    require('global extension', run(['bash', 'scripts/check-fg-compose.sh'], tree, env),
            1, 'FORBIDDEN GLOBAL EXTENSION:')

    tree, env = fixture('source-inventory')
    shutil.copytree(REPO / LAYOUT.source_dir('AvailableChainFGCompose'),
                    tree / 'AvailableChainFGCompose',
                    dirs_exist_ok=True)
    shutil.copy2(REPO / LAYOUT.source_path('AvailableChainFGCompose'),
                 tree / 'AvailableChainFGCompose.lean')
    orphan = tree / 'AvailableChainFGCompose/Statements/Unlisted.lean'
    orphan.write_text('module\npublic section\nnamespace Extra\n'
                      'opaque unlisted : Nat := 1\nend Extra\n')
    require('unlisted public declaration', run(['bash', 'scripts/check-fg-compose.sh'], tree, env),
            2, 'COMPOSE INVENTORY UNLISTED:')
    orphan.rename(tree / 'unlisted.saved')
    inventory = tree / 'scripts/fg-compose-expected.txt'
    inventory.write_text(inventory.read_text().replace("    'AvailableChain.FGCompose.cutPred',\n", ''))
    require('inventory omission', run(['bash', 'scripts/check-fg-compose.sh'], tree, env),
            2, 'AvailableChain.FGCompose.cutPred')

    inventory.write_text((REPO / 'scripts/fg-compose-expected.txt').read_text())
    for name in ('Statements/SafetyReads', 'Statements/SafetyStore', 'Statements/SafetyClient',
                 'Statements/SafetyClaims', 'Proofs/SafetyStore', 'Proofs/SafetyAccountable',
                 'Proofs/SafetyClient', 'Proofs/SafetyCount', 'Proofs/SafetyMonotone',
                 'Proofs/SafetySlashing'):
        source = tree / ('AvailableChainFGCompose/' + name + '.lean')
        if not source.exists():
            continue
        saved = source.read_bytes()
        source.rename(tree / (name.replace('/', '-') + '.saved'))
        require('safety ' + name + ' missing source',
                run(['bash', 'scripts/check-fg-compose.sh'], tree, env),
                2, 'COMPOSE INVENTORY MISSING:')
        source.write_bytes(saved)

    if (REPO / LAYOUT.source_path('AvailableChainFGCompose.Proofs.SourceHead')).exists():
        # These attempts fail at the exact omitted contract premise.
        context = ("import AvailableChainFGCompose.Proofs.SourceHead\n"
                   "namespace AvailableChain.FGCompose.ContractControl\n"
                   "open AvailableChain.SimplexFG AvailableChain.KitFG\n"
                   "variable {V In : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]\n"
                   "variable {n : Nat} {Base Proposal RowWire : Type}\n"
                   "variable (R : FGCoreReads P n Base Proposal RowWire)\n"
                   "variable (E : Generic.Env V) (rho : V2.D.Run V P)\n")
        for label, body, reason in [
            ('NoRestart required',
             "example (L : FGCoreLaws R) {i j : Nat} (hij : i ≤ j) (x : V) :\n"
             "    TFAt R E rho i x ⊆ TFAt R E rho j x := by\n"
             "  exact tf_cumulative R E rho L hij x\n", 'V2.D.NoRestart rho'),
            ('ancestry required',
             "example (Ef : Electorate (Fin n)) (H : FGHeightView (Fin n))\n"
             "    (laws : FGHeightLaws Ef H) {D C : FGBlock (Fin n)} {y : Nat}\n"
             "    (hD : (H D).h = y + 1) (hC : (H C).h ≤ y + 1) : (H C).h = y + 1 := by\n"
             "  exact (source_height_entry Ef H laws hD hC).1\n", 'FGBlock.Preceq'),
        ]:
            source = root / (label.replace(' ', '-') + '.lean')
            source.write_text(context + body + 'end AvailableChain.FGCompose.ContractControl\n')
            result = run(['lake', 'env', 'lean', str(source)])
            require(label, result, 1, reason)
            assert 'Application type mismatch' in result.stdout, result.stdout + result.stderr

    # Negative control: a tree without the controls file fails.
    (root / "lakefile.toml").write_text('[[lean_lib]]\nname="AvailableChainFGCompose"\n')
    try:
        require_safety_controls(root)
    except SystemExit as exc:
        assert str(exc) == f'MISSING SAFETY CONTROLS: {SAFETY_CONTROLS}', exc
        print('CONTROL Compose safety controls file missing: PASS (MISSING SAFETY CONTROLS)',
              flush=True)
    else:
        raise AssertionError('a missing SafetyControls.lean was not detected')
    require_safety_controls(REPO)
    # Each behavior control: the positive form compiles, and the negative
    # form fails with its exact diagnostic.
    context = ("import AvailableChainFGCompose.Tests.SafetyControls\n"
               "import AvailableChainFGCompose.Proofs.SafetyMonotone\n"
               "namespace AvailableChain.FGCompose.Tests.SafetyControls.NegativeControl\n"
               "open AvailableChain.SimplexFG AvailableChain.KitFG "
               "AvailableChain.FGCompose.Tests.SafetyControls\n")
    monotone = ("variable {In V : Type} {P : V2.ProtocolSpecD In} {n : Nat} "
                "{Base Proposal Wire : Type}\n"
                "variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)\n"
                "variable [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V P)\n"
                "example (C : FGCoreLaws R) (O : FGSafetyOrderLaws R S)SORTED\n"
                "    (hnr : V2.D.NoRestart rho) :\n"
                "    ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →\n"
                "      Block.Preceq (S.finalizedOut (V2.D.Run.readAt E rho t x))\n"
                "        (S.finalizedOut (V2.D.Run.readAt E rho t' x)) := by\n"
                "  exact safety_finalized_monotone R S E rho C O HS hnr\n")
    scope = ("example (N : FGSafetyScopeLaws emitReads emitSafety envU emitRun deliveredScope)\n"
             "    (hne : tip.parent ≠ FGBlock.genesis) :\n"
             "    deliveredScope (emitReads.erase BLOCK) :=\n"
             "  N.parent_scope tip tip_runBlock hne\n")
    row = '(⟨0, .empty, none⟩ : Row (Fin 1))'
    controls = []
    for label, good, bad, reason in [
        ('unordered inclusive read',
         "example : V2.D.Run.readAt envU unordered 1 () = 2 := by decide\n",
         "example : V2.D.Run.readAt envU unordered 1 () =\n"
         "    V2.D.Run.stateBefore envU unordered 1 () := by decide\n",
         'V2.D.Run.stateBefore envU unordered 1 ()\nis false'),
        ('monotone needs sorted events',
         monotone.replace('SORTED', '\n    (hs : rho.events.Pairwise (fun a b => a.key ≤ b.key))')
         .replace(' HS', ' hs'),
         monotone.replace('SORTED', '').replace(' HS', ''),
         'List.Pairwise (fun a b => a.key ≤ b.key) rho.events'),
        ('repeated row one signer',
         f"example : ([{row}, {row}].map Row.signer).toFinset.card = 1 := by decide\n",
         f"example : ([{row}, {row}].map Row.signer).toFinset.card = 2 := by decide\n",
         '    2\nis false'),
        ('seat permutation holder',
         "example : safetyHolder swapReads seatRun 0 = 1 := by decide\n",
         "example : safetyHolder swapReads seatRun 0 = 0 := by decide\n",
         'safetyHolder swapReads seatRun 0 = 0\nis false'),
        ('lost durable record',
         "example : ∀ nd t, keptReads.record (kept.restore (kept.durable nd) t) =\n"
         "    keptReads.record nd := fun _ _ => rfl\n",
         "example : ∀ nd t, lossyReads.record (lossy.restore (lossy.durable nd) t) =\n"
         "    lossyReads.record nd := fun _ _ => rfl\n",
         'lossyReads.record (lossy.restore (lossy.durable'),
        ('emitted-only tip scope',
         scope.replace('BLOCK', 'tip.parent'), scope.replace('BLOCK', 'tip'),
         'deliveredScope (emitReads.erase tip.parent)'),
    ]:
        controls.append((label, good, bad, reason))
    # All positive forms compile in one file; each negative form alone.
    end = 'end AvailableChain.FGCompose.Tests.SafetyControls.NegativeControl\n'
    source = root / 'safety-positive.lean'
    source.write_text(context + ''.join(
        f'section\n{good}end\n' for _, good, _, _ in controls) + end)
    result = run(['lake', 'env', 'lean', str(source)])
    assert result.returncode == 0 and 'error' not in result.stdout, result.stdout + result.stderr
    print(f'CONTROL Compose safety positive forms ({len(controls)}): PASS (rc 0)', flush=True)
    for label, _, bad, reason in controls:
        source = root / ('safety-' + label.replace(' ', '-') + '-negative.lean')
        source.write_text(context + bad + end)
        result = run(['lake', 'env', 'lean', str(source)])
        require('safety ' + label, result, 1, reason)
        assert result.stdout.count('error:') == 1, (label, result.stdout)

print('Compose controls: PASS', flush=True)
