#!/usr/bin/env python3
"""Compile isolated fixtures; run the real checker and check each refusal reason."""

import os
from pathlib import Path
import signal
import subprocess
import tempfile

from audit_pool import AuditPool


REPO = Path(__file__).resolve().parents[1]
os.chdir(REPO)


SIGNALS = {signal.SIGTERM, signal.SIGINT}


def interrupt(signum, _frame):
    for sig in SIGNALS:
        signal.signal(sig, signal.SIG_IGN)
    raise SystemExit(128 + signum)


for sig in SIGNALS:
    signal.signal(sig, interrupt)


def command(args, *, check=False, **kwargs):
    # Defer signals until the child is stored; restore its mask before exec.
    mask = signal.pthread_sigmask(signal.SIG_BLOCK, SIGNALS)
    try:
        proc = subprocess.Popen(args, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, start_new_session=True,
                                preexec_fn=lambda: signal.pthread_sigmask(signal.SIG_SETMASK, mask),
                                **kwargs)
    except BaseException:
        signal.pthread_sigmask(signal.SIG_SETMASK, mask)
        raise
    try:
        signal.pthread_sigmask(signal.SIG_SETMASK, mask)
        stdout, stderr = proc.communicate()
    except BaseException:
        # Stop and reap the child group before the source copy is removed.
        AuditPool.terminate(proc)
        raise
    result = subprocess.CompletedProcess(args, proc.returncode, stdout, stderr)
    if check:
        result.check_returncode()
    return result


mask = signal.pthread_sigmask(signal.SIG_BLOCK, SIGNALS)
with tempfile.TemporaryDirectory(prefix="proof-eqns-neg.", dir=REPO / ".lake") as scratch:
    signal.pthread_sigmask(signal.SIG_SETMASK, mask)
    root = Path(scratch)
    source = root / "tree"
    source.mkdir()
    env_result = command(["lake", "env", "printenv", "LEAN_PATH"])
    assert env_result.returncode == 0, env_result.stderr
    lean_path = str(source) + os.pathsep + env_result.stdout.strip()
    lean = ["lake", "env", "env", f"LEAN_PATH={lean_path}", "lean"]
    # Keep the full default-root/source scope, but publish fixture links only
    # in a private source copy. Lake supplies the real built imports before cd.
    private_repo = root / 'repo'
    private_repo.mkdir()
    command(['rsync', '-a', '--exclude=/.lake', '--exclude=/.git',
                    '--exclude=/AGENTS.md', '--exclude=/state.md', '--exclude=/log.md',
                    '--exclude=/claude-files', str(REPO) + '/', str(private_repo) + '/'],
                   check=True)
    check_lean = lean[:-1] + ['bash', '-c', 'cd "$1" || exit; shift; exec lean "$@"',
                             'proof-eqns-control', str(private_repo)]
    prefix = "AvailableChainCoverageControl"
    with (private_repo / 'lakefile.toml').open('a') as config:
        for library in (prefix, 'OtherCoverageControl'):
            config.write('[[lean_lib]]\nname="' + library + '"\nroots=[]\n'
                         'globs=["' + library + '.+"]\n')

    def compile_module(module, body):
        file = source / (module.replace(".", "/") + ".lean")
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text(body)
        result = command(lean + ["-o", str(file.with_suffix(".olean")), str(file)])
        assert result.returncode == 0, (module, result.stdout, result.stderr)

    for case, equation in (
        ("Valid", "theorem P_def : P = True := by simp [P]"),
        ("Missing", ""),
        ("Private", "private theorem P_def : P = True := rfl"),
        ("WrongType", "theorem P_def : True := True.intro"),
        ("Reflexive", "theorem P_def : P = P := rfl"),
    ):
        module = f"{prefix}.Statements.{case}"
        compile_module(module, "module\npublic import Init\npublic section\n"
                       f"namespace {case}\ndef P : Prop := True\n{equation}\nend {case}\n")
    compile_module(f"{prefix}.Statements.Exposed",
                   "module\npublic import Init\n@[expose] public section\n"
                   "namespace Exposed\ndef P : Prop := True\nend Exposed\n")
    compile_module(f"{prefix}.Statements.Binders",
                   "module\npublic import Init\npublic section\nnamespace Binders\n"
                   "def P {α : Type u} (x : α) := x = x\n"
                   "theorem P_def {α : Type u} (x : α) : P x ↔ x = x := by simp [P]\n"
                   "end Binders\n")
    compile_module(f"{prefix}.Statements.Alias",
                   "module\npublic import Init\npublic section\nnamespace Alias\n"
                   "def SortAlias := Prop\ndef P : SortAlias := True\nend Alias\n")
    compile_module(f"{prefix}.Statements.Other",
                   f"module\npublic import {prefix}.Statements.Missing\n"
                   f"import all {prefix}.Statements.Missing\npublic section\n"
                   "theorem Missing.P_def : Missing.P = True := by simp [Missing.P]\n")
    compile_module(f"{prefix}.Proofs.Leak",
                   "module\npublic import Init\n@[expose] public section\n"
                   "def Leak.f (n : Nat) : Nat := n + 1\n"
                   "theorem Leak.test (n : Nat) : Leak.f n = n + 1 := Leak.f.eq_def n\n")
    for case, line in (
        ("Valid", "#print axioms Valid.P"),
        ("Commented", "-- #print axioms Valid.P\n/- #print axioms Valid.P -/"),
        ("Short", "open Valid\n#print axioms P"),
    ):
        compile_module(f"{prefix}.Tests.{case}",
                       f"module\npublic import {prefix}.Statements.Valid\n{line}\n")
    for case, line in (("PrivateSyntax", "#print axioms Valid.P"),
                       ("PrivateSyntaxMissing", "-- #print axioms Valid.P")):
        compile_module(f"{prefix}.Tests.{case}",
                       f"module\npublic import {prefix}.Statements.Valid\n"
                       "import Lean.Elab.Tactic.RCases\n"
                       "example : True := by\n"
                       "  obtain ⟨h, _⟩ := And.intro True.intro True.intro\n"
                       "  exact h\n" + line + "\n")
    compile_module("OtherCoverageControl.Tests.Axioms",
                   f"module\npublic import {prefix}.Statements.Valid\n#print axioms Valid.P\n")
    special = ("B'_resetF", "B'_resetF_def", "clock_eq_saClockFrom_gate'", 'block?_proposal')
    owner = f'{prefix}.Model.Special'
    compile_module(owner, 'module\npublic import Init\npublic section\nnamespace Special\n'
                   + '\n'.join(f'theorem {name} : True := True.intro' for name in special)
                   + '\nend Special\n')
    special_audit = f'{prefix}.Tests.Special'
    special_body = (f'module\npublic import {owner}\nnamespace Special\n'
                    + '\n'.join(f'#print axioms {name}' for name in special)
                    + '\nend Special\n#print axioms True.intro\n')
    compile_module(special_audit, special_body)

    def check(label, module, rc, reason, audit=None):
        args = check_lean + ["--run", "scripts/CheckProofEqns.lean", "--baseline",
                       "scripts/baselines/check-proof-eqns.txt", module]
        if audit:
            data = root / "coverage.txt"
            data.write_text(f"{prefix}.Statements.Valid Valid.P {audit}\n")
            args += ["--coverage", str(data)]
        result = command(args)
        output = result.stdout + result.stderr
        assert result.returncode == rc and reason in output, (label, result.returncode, output)
        print(f"CONTROL {label}: PASS (rc {rc}; {reason})", flush=True)

    # The audit parser reads its private source tree; no real-tree link is needed.
    link = private_repo / prefix
    assert not link.exists()
    link.symlink_to(source / prefix, target_is_directory=True)
    other_link = private_repo / 'OtherCoverageControl'
    other_link.symlink_to(source / 'OtherCoverageControl', target_is_directory=True)
    try:
        check("home equation", f"{prefix}.Statements.Valid", 0, "0 unaccepted")
        check("exposed predicate", f"{prefix}.Statements.Exposed", 0, "0 unaccepted")
        check("inferred Prop / binders / iff", f"{prefix}.Statements.Binders", 0, "0 unaccepted")
        for case in ("Missing", "Private"):
            check(case, f"{prefix}.Statements.{case}", 1, "STATEMENT DEF MISSING")
        check("unrelated theorem", f"{prefix}.Statements.WrongType", 1, "STATEMENT DEF WRONG TYPE")
        check("reflexive theorem", f"{prefix}.Statements.Reflexive", 1, "STATEMENT DEF WRONG TYPE")
        check("hidden Prop alias", f"{prefix}.Statements.Alias", 1, "STATEMENT DEF MISSING")
        check("wrong home", f"{prefix}.Statements.Other", 1, "STATEMENT DEF WRONG MODULE")
        check("equation export", f"{prefix}.Proofs.Leak", 1, "EQ EXPORT")
        for case, rc, reason in (("Valid", 0, "0 unaccepted"),
                                 ("Commented", 1, "AUDIT LINE MISSING"),
                                 ("Short", 1, "AUDIT LINE MISSING"),
                                 ("PrivateSyntax", 0, "0 unaccepted"),
                                 ("PrivateSyntaxMissing", 1, "AUDIT LINE MISSING")):
            audit = f"{prefix}.Tests.{case}"
            check(f"audit {case}", audit, rc, reason, audit)
        audit = "OtherCoverageControl.Tests.Axioms"
        check("audit wrong library", audit, 1, "AUDIT MODULE NOT COVERED", audit)
        # Generate from all commands, including local names and an imported owner.
        data = root / 'complete-coverage.txt'
        args = check_lean + ['--run', 'scripts/CheckProofEqns.lean', '--baseline',
                       'scripts/baselines/check-proof-eqns.txt', special_audit]
        result = command(args + ['--write-coverage', str(data)])
        assert result.returncode == 0, (result.stdout, result.stderr)
        original = data.read_text()
        assert len(original.splitlines()) == 5, original
        for name in special:
            assert f'{owner} Special.{name} {special_audit}\n' in original, original
        check_args = args + ['--coverage', str(data), '--complete-coverage']

        def complete_check(label, rc, reason):
            result = command(check_args)
            output = result.stdout + result.stderr
            assert result.returncode == rc and reason in output, (label, output)
            print(f'CONTROL complete coverage {label}: PASS (rc {rc}; {reason})', flush=True)

        complete_check('all commands and owners', 0, '0 unaccepted')
        audit_path = source / (special_audit.replace('.', '/') + '.lean')
        for name in special:
            audit_path.write_text(special_body.replace(f'#print axioms {name}\n', ''))
            complete_check('removed ' + name, 1, f'AUDIT LINE MISSING name=Special.{name} ')
            audit_path.write_text(special_body)
        data.write_text('\n'.join(line for line in original.splitlines()
                                  if " Special.B'_resetF " not in line) + '\n')
        complete_check('inventory omission', 1, "AUDIT INVENTORY MISSING name=Special.B'_resetF ")
    finally:
        link.unlink()
        other_link.unlink()

    # Compose has its own proof leak and audit-owner controls.
    compose_owner = 'AvailableChainFGCompose.Statements.Control'
    compose_audit = 'AvailableChainFGCompose.Tests.Control'
    compose_proof = 'AvailableChainFGCompose.Proofs.Control'
    compile_module(compose_owner,
                   'module\npublic import Init\n@[expose] public section\n'
                   'namespace ComposeControl\ndef P : Prop := True\nend ComposeControl\n')
    compile_module(compose_audit, f'module\npublic import {compose_owner}\n'
                   '#print axioms ComposeControl.P\n')
    compile_module(compose_proof,
                   'module\npublic import Init\n@[expose] public section\n'
                   'namespace ComposeLeak\ndef f (n : Nat) : Nat := n + 1\n'
                   'theorem test (n : Nat) : f n = n + 1 := f.eq_def n\nend ComposeLeak\n')
    (source / 'scripts/baselines').mkdir(parents=True, exist_ok=True)
    (source / 'scripts/source_layout.py').write_bytes(
        (REPO / 'scripts/source_layout.py').read_bytes())
    for name in ('kitfg-def-modules.txt', 'check-proof-eqns.txt'):
        (source / 'scripts/baselines' / name).write_bytes((REPO / 'scripts/baselines' / name).read_bytes())
    compile_module('AvailableChainCoverageControlRoot', 'module\n')
    (source / 'lakefile.toml').write_text(
        'name = "compose-proof-control"\n'
        'defaultTargets = ["AvailableChainCoverageControlRoot"]\n'
        '[[lean_lib]]\nname = "AvailableChainCoverageControlRoot"\n'
        '[[lean_lib]]\nname = "AvailableChainFGCompose"\n'
        'globs = ["AvailableChainFGCompose.*"]\n')
    args = lean + ['--run', str(REPO / 'scripts/CheckProofEqns.lean'), '--baseline',
                   str(REPO / 'scripts/baselines/check-proof-eqns.txt')]
    result = command(args + [compose_proof], cwd=source)
    assert result.returncode == 1 and f'EQ EXPORT {compose_proof}' in result.stdout, (result.returncode, result.stdout, result.stderr)
    print('CONTROL Compose proof equation leak: PASS', flush=True)
    data = root / 'compose-coverage.txt'
    row = f'{compose_owner} ComposeControl.P {compose_audit}\n'
    data.write_text(row)
    args += [compose_audit, '--coverage', str(data), '--complete-coverage']
    for label, body, owner, rc, reason in (
        ('positive', '#print axioms ComposeControl.P\n', compose_owner, 0, '0 unaccepted'),
        ('missing', '', compose_owner, 1, 'AUDIT LINE MISSING'),
        ('commented', '-- #print axioms ComposeControl.P\n', compose_owner, 1, 'AUDIT LINE MISSING'),
        ('wrong owner', '#print axioms ComposeControl.P\n', compose_proof, 1, 'AUDIT DECLARATION MISSING'),
    ):
        (source / (compose_audit.replace('.', '/') + '.lean')).write_text(
            f'module\npublic import {compose_owner}\n' + body)
        data.write_text(f'{owner} ComposeControl.P {compose_audit}\n')
        result = command(args, cwd=source)
        assert result.returncode == rc and reason in result.stdout, (label, result.stdout, result.stderr)
        print(f'CONTROL Compose audit {label}: PASS', flush=True)
