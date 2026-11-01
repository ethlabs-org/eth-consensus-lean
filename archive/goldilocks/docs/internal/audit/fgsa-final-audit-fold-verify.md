# G13 fold verification (Opus): FG-SA store, commit 8f61f06

Branch `fgsa-composition`, worktree `~/worktrees/available-chain-fgsa`, HEAD
`8f61f06`. I did not edit or commit in that worktree. I built in a detached
scratch worktree at `8f61f06` and removed it at the end. My control files are
in `codex/scratch/g13-fold-scripts/`.

## Verdict

**CLOSED WITH FIXES.** No BLOCKING or MAJOR finding. Two MINOR findings.

The fold closes every case that the two G13 audits named. Astra M1, M2, N1,
N2, N3 and Opus m1–m5 are folded. No theorem, statement or model rule changed.
The new tests are correct, and the `stL` test kills the mutation that it is
for. The rewritten guards are strict inside FGSA modules: all my FGSA-module
controls fail as expected. But the guards are not closed against adversarial
input at two edges:

- The lease check does not fully inspect imported definitions (MINOR-1).
- The import check fails open on some valid Lean header forms and on some
  file names (MINOR-2).

Neither gap is a present defect. Independent checks show that the current
tree obeys both rules. Apply the fixes before you use the guards as
adversarial enforcement.

## 1. Scope of 8f61f06

`git diff 8e8b61e 8f61f06 --stat -- AvailableChainFGSA/Model
AvailableChainFGSA/Statements AvailableChainFGSA/Proofs AvailableChain/` is
empty. The changed files are:

```text
┌─────────────────────────────────────────────┬──────────────────────────────┐
│ File                                        │ Change                       │
├─────────────────────────────────────────────┼──────────────────────────────┤
│ AvailableChainFGSA.lean                     │ +1 import (Tests)            │
│ AvailableChainFGSA/Tests/RootCollision.lean │ new (84 lines)               │
│ AvailableChainFGSA/Tests/Smoke.lean         │ +21, no deletions (stL)      │
│ scripts/CheckFGSALease.lean                 │ rewritten                    │
│ scripts/CheckFGSAAxioms.lean                │ coverage and closure added   │
│ scripts/check-fgsa.sh                       │ rewritten                    │
│ docs/ (report, MAP, plan, two audits)       │ text                         │
└─────────────────────────────────────────────┴──────────────────────────────┘
```

No file of another library changed.

## 2. Baseline

`bash scripts/check-fgsa.sh` in the scratch worktree: exit 0, 3 min 15 s.
The build replayed the copied artifacts (3377 jobs). The axiom script checked
805 constants, 442 theorems and 5503 modules. The lease script checked 788
constants (17 generated equation lemmas skipped), inspected 332 imported
definitions and found 116 lease arguments. All six negative controls were
rejected.

## 3. Lease guard (`scripts/CheckFGSALease.lean`)

### 3.1 Controls in an FGSA-scanned module: all rejected

File `AdvA.lean`, a scanned root, run with
`lean --run scripts/CheckFGSALease.lean AdvA`. Result: exit 1.

```text
┌─────┬──────────────────────────────────────────────┬────────────────────────┐
│ ID  │ Control                                      │ Result                 │
├─────┼──────────────────────────────────────────────┼────────────────────────┤
│ A1  │ policy in a structure field: Box.mk          │ rejected (Box.mk has a │
│     │ gridLeasePolicy, then gate at box.pol        │ policy parameter; gate │
│     │                                              │ at Box.pol box)        │
│ A2  │ let pol := gridLeasePolicy; @gate pol …      │ rejected (gate at #0)  │
│ A3  │ abbrev MyPol := LeasePolicy; def f [MyPol]   │ rejected (policy       │
│     │                                              │ parameter; gate at #3) │
│ A4  │ @[reducible] def slowish := gridLeasePolicy  │ rejected (gate at      │
│     │                                              │ slowish)               │
│ A5  │ instance (priority := high) fgsaPol :=       │ rejected (gate at      │
│     │ gridLeasePolicy; gate elaborated with it     │ fgsaPol)               │
│ A6  │ theorem about slowLeasePolicy whose proof    │ rejected (gate at      │
│     │ uses gridLeasePolicy (a `have`)              │ gridLeasePolicy)       │
│ E1  │ def GridCO.gate.eq_9 / .eq_def / .eq_01 /    │ Lean rejects: "is a    │
│     │ .eq_0 in a user file (skip-rule spoof)       │ reserved name"         │
│ E2  │ non-exposed def in a `module` library        │ body visible; rejected │
└─────┴──────────────────────────────────────────────┴────────────────────────┘
```

E1 shows that a user cannot declare a name that the skip rule skips. E2 shows
that the script, a non-module importer, reads private module data.

**A6 (the question in the task).** The check rejects a theorem whose proof
uses `gridLeasePolicy` but whose statement mentions only `slowLeasePolicy`.
The check scans theorem values. This rejection is stricter than soundness
requires, because a proof term cannot change what its statement means. I
recommend that you keep it. FGSA does not need such a proof. A bridge lemma
between the two policies would need an explicit, reviewed exception. The
script header says "the types and values of these constants". Add one line
that says that theorem proofs are scanned too.

### 3.2 Controls in an imported library: not rejected (MINOR-1)

`AdvLib.lean` (not scanned, as `FGSALeaseLib` in the implementer's control)
and `AdvUse.lean` (scanned, in `AvailableChain.FGSA`). Run:
`lean --run scripts/CheckFGSALease.lean AdvUse`. Result: **exit 0, no
report.**

```text
┌─────┬───────────────────────────────────────────────────┬──────────────────┐
│ ID  │ Imported definition that FGSA calls               │ Why it passes    │
├─────┼───────────────────────────────────────────────────┼──────────────────┤
│ B1  │ fixedLet: let pol := gridLeasePolicy;             │ any bound        │
│     │ @gate pol …                                       │ variable passes  │
│ B2  │ fixedBeta: (fun pol => @gate pol …)               │ same; the closed │
│     │ gridLeasePolicy                                   │ arg is at no     │
│     │                                                   │ policy position  │
│ B3  │ fixedViaPriv calls private fixedPriv, which uses  │ `_private.…` has │
│     │ @gate gridLeasePolicy                             │ no `AvailableCh- │
│     │                                                   │ ain` prefix      │
│ B4  │ genI (pol : PolI), PolI := LeasePolicy, then      │ whnf at default  │
│     │ attribute [irreducible] PolI; FGSA passes         │ transparency     │
│     │ cast polI_eq gridLeasePolicy                      │ hides the policy │
│     │                                                   │ position         │
│ B5  │ Evil.fixedGate (namespace outside AvailableChain) │ trusted, as the  │
│     │                                                   │ header states    │
└─────┴───────────────────────────────────────────────────┴──────────────────┘
```

B1 and B2 contradict the script header (lines 26–30): "every closed policy
argument must be `GridCO.slowLeasePolicy`. So an imported wrapper that fixes
`gridLeasePolicy` inside and that FGSA reaches fails." They also do not meet
the letter of Astra M1: "inspect generic bodies while allowing only their own
bound policy parameter". The check accepts every bound variable, also one
that a `let` or a `fun` inside the body binds. My G13 m2 asked for the same
restriction. B3 is outside the stated scope only because of the private-name
prefix; the header does not state this exception.

**Present state.** `Reach.lean` computes the transitive closure of constants
from all FGSA constants. It follows the types and values of every reached
constant in every namespace, private names included. It does not follow the
proofs of imported theorems. Result: 4203 constants reached, 38 of them
imported private constants. **No reached imported constant mentions
`gridLeasePolicy`.** No reached constant outside `AvailableChain.*` mentions an
`AvailableChain.GridCO.*` constant. On `AdvUse`, the same script finds B1, B2,
B3 and B5, so the script can detect them. There is no present defect. An
attack needs a change in an imported library. The plan does not permit such a
change.

**Fix (any one closes B1–B4; (d) also closes B5):**

- (a) In generic mode, open the lambda telescope of the definition. Accept
  only the free variables of the definition's own policy parameters. Reject
  every other bound variable.
- (b) Test the namespace on `privateToUserName? c` (or on the module of `c`)
  and not on the raw name.
- (c) Classify binder types with `withTransparency .all` (or `whnfD` after
  `unfoldDefinition?`), so that an irreducible alias does not hide a policy
  position.
- (d) The simplest backstop: add a reachability rule, as in `Reach.lean`. No
  constant in the transitive closure from FGSA (all namespaces, private
  included, imported theorem proofs excluded) may use `gridLeasePolicy`.
  `LeasePolicy.mk` may occur only in the value of `slowLeasePolicy`.

Add B1 and B3 as negative controls.

## 4. Import guard (`scripts/check-fgsa.sh`)

### 4.1 Forms that the guard handles correctly

`imports_of` returns the correct list for these headers: a nested comment that
contains an import (`/- /- -/ public import X.Y -/`), `public meta import`, a
line comment before the import, and CRLF line ends. Lean rejects a UTF-8 BOM
before `module`, so a BOM is not a bypass. The layer rules reject a file
directly under `AvailableChainFGSA/` or in a new directory (fail closed). The
script aborts when one of the two Lean scripts is missing (Astra N1).

### 4.2 Bypasses (MINOR-2)

I put four modules in `Model/` of the scratch tree. Each module imports
`AvailableChainLStar.Model.Protocol`, which the allowlist does not permit. The
root imports all four:

```text
┌──────────────────────────────┬────────────────────────────────────────────┐
│ Module                       │ Form                                       │
├──────────────────────────────┼────────────────────────────────────────────┤
│ Model/AdvG.lean              │ public import «AvailableChainLStar».Model. │
│                              │ Protocol  (guillemets: parser stops, 0     │
│                              │ imports)                                   │
│ Model/AdvP.lean              │ module / prelude / public import …         │
│                              │ (parser stops at `prelude`, 0 imports)     │
│ Model/AdvCase.LEAN           │ upper-case extension; Lake on macOS (case- │
│                              │ insensitive APFS) builds it; `find -name   │
│                              │ '*.lean'` does not list it                 │
│ Model/Sub/X.lean             │ Model/Sub is a symlink to a directory;     │
│                              │ Lake builds through it; `find` does not    │
│                              │ descend into it                            │
└──────────────────────────────┴────────────────────────────────────────────┘
```

All four compile. **The full `bash scripts/check-fgsa.sh` exits 0** (log:
`g13-fold-scripts/check-fgsa-bypass.log`; 5508 modules in the closure). The
compiled closure check does not help, because it rejects only the four
forbidden roots. `AvailableChainLStar` is not one of them. Also, a
non-identifier character at the start of a module name (for example `«`)
stops the parser. Then the parser also misses every later import of that
file.

The same file enumeration feeds the Q1/Q5 grep and the native grep. In
`AdvCase.LEAN` and `Sub/X.lean`, a name with `Interface` was not reported;
the same name in `AdvG.lean` and `AdvP.lean` was reported. The axiom check
still catches native evaluation, so only the Q1/Q5 grep has no compiled
backstop.

Coverage (`CheckFGSAAxioms`, `sourceModules`): `walkDir` follows the
symlinked directory, so an orphan `Sub/Orphan.lean` with `sorry` is reported
as `NOT IN THE BUILD`. An orphan `OrphanC.LEAN` is not reported by this check
or by the root check. It is not compiled, and no module uses it. It is only a
risk if a report cites it.

**Present state.** `Imports.lean` applies the plan allowlist and its layer
rules to the COMPILED direct imports (`env.header.moduleData[i].imports`).
Clean tree: 21 FGSA modules, 0 bad imports. Bypass tree: it reports exactly
the four modules above. The current imports obey the allowlist.

**Fix.** Check the direct allowlist on the compiled data in
`CheckFGSAAxioms.lean` (prototype: `g13-fold-scripts/Imports.lean`; allow
`Init`). This removes the dependence on header syntax, case and symlinks.
Keep the source parser as a first check, but make it fail closed: after it
reads the header, reject the file if the remaining text still contains the
token `import` or `prelude`, or if a module name contains `«`. Enumerate the
files with `find -L … -iname '*.lean'`, or take the file list from the
compiled module list. Add a negative control for the guillemet form.

## 5. Axiom and coverage guard (`scripts/CheckFGSAAxioms.lean`)

The coverage rule works for the orphan control of the implementer and for an
orphan in a symlinked directory. The closure rule rejects the four roots
(implementer control: `AvailableChainSAPC`). The only gap is the `.LEAN`
orphan in 4.2. The rule compares the extension with `"lean"` and so is case
sensitive. I do not rate it separately.

## 6. New tests

**`Tests/RootCollision.lean`: correct.** The root formula in the test matches
`GridCO.propose` (`AvailableChainGridCO/Model/Protocol.lean:292`:
`s * (parent.root.value + 1)`), and the `example` checks both roots with
`decide`. The claims are as follows:
(1) `Reachable` for both stores, from `init`, `tick 20` and deliveries. The
invariants come from the library theorems, and the membership facts are
checked by `decide +kernel`.
(2) `not_contentAgree` uses `ContentAgree` at `(4, ba)` and `(2, bb)`, which
have the same root, and derives `ba = bb`, which is false. The negated
conclusion of `rootInjectiveOn_across` is correct: the premise is necessary.
(3) The DQ2 refusal of `bb` at a store that holds `ba` is checked by
`decide +kernel`.
"Honest" here means "made with the root formula of the honest proposer". The
test does not build an honest-proposer run. The docstring does not claim that
it does.

**`stL` tests (Astra N3): correct, and they discriminate.** `StLMut.lean`
replaces `fullTree` by the active FG tree (`TF` filtered by `actView`) in
copies of `liveRoot` and `fgSource`. With `decide +kernel`, the mutated rule
gives `liveRoot = eraseFG X` and `fgSource = some X`, and
`liveRoot pT stL ≠ liveRootM pT stL`. So the committed test fails under the
wrong rule, as the docstring says. `stL` is a hand-set state and is not
reachable, and the docstring says so.

## 7. Other G13 items

- Opus m3/m4 and Astra N2: the wording is fixed in `docs/FGSA-STORE-REPORT.md`
  (lines 11, 34, 51, 79–91, 199–221) and in `docs/MAP.md` (653–683).
- Opus m5: the Q1/Q5 grep now runs on comment-free text and includes `Run`,
  `Env`, `Interface` and `Claims`.
- Astra N1: the script requires both Lean scripts.

## 8. Findings

### BLOCKING

None.

### MAJOR

None.

### MINOR

**MINOR-1. Imported-definition inspection of the lease check is incomplete.**
`scripts/CheckFGSALease.lean:119` (`generic && a.isBVar`), `:171` (raw-name
prefix), `:79` (`whnf` at default transparency). A let- or beta-bound default
policy, a private imported wrapper and an irreducible type alias pass (B1–B4,
compiled, exit 0). This contradicts the header claim at lines 26–30 and the
letter of Astra M1. There is no present defect: `gridLeasePolicy` is not
reachable from FGSA. Fix: 3.2 (a)–(d). Add B1 and B3 as controls.

**MINOR-2. The import allowlist fails open on valid header forms and file
names.** `scripts/check-fgsa.sh:39–45` (`header_imports`), `:48–56` and
`:67` (`find -name '*.lean'`). A guillemet module name, a `prelude` header, a
`.LEAN` file (macOS) and a symlinked directory each let a `Model/` module
import `AvailableChainLStar`. The full `check-fgsa.sh` then exits 0. The last
two forms also skip the Q1/Q5 grep. There is no present defect: the compiled
imports obey the allowlist. Fix: section 4.2, with the check on compiled
`moduleData.imports` as the main fix.

## 9. Validation

```text
┌─────────────────────────────────────────────────┬───────────────────────────┐
│ Command (scratch worktree at 8f61f06)           │ Result                    │
├─────────────────────────────────────────────────┼───────────────────────────┤
│ git diff 8e8b61e 8f61f06 -- Model Statements    │ empty                     │
│ Proofs AvailableChain/                          │                           │
│ bash scripts/check-fgsa.sh (clean)              │ exit 0, 3:15              │
│ CheckFGSALease.lean AdvA                        │ exit 1, A1–A6 reported    │
│ lean AdvEqn / AdvEqn3                           │ "reserved name" errors    │
│ CheckFGSALease.lean AdvModUse                   │ exit 1 (non-exposed body  │
│                                                 │ read)                     │
│ CheckFGSALease.lean AdvUse                      │ exit 0 (B1–B5 missed)     │
│ Reach.lean (clean) / Reach.lean AdvUse          │ 0 hits / 4 hits           │
│ bash scripts/check-fgsa.sh (bypass tree)        │ exit 0, 3:52              │
│ CheckFGSAAxioms.lean (+ orphans)                │ Sub/Orphan caught;        │
│                                                 │ OrphanC.LEAN missed       │
│ Imports.lean (bypass tree / clean tree)         │ 4 bad / 0 bad (21 mods)   │
│ lean StLMut.lean                                │ exit 0 (mutation killed)  │
│ git worktree remove (scratch)                   │ done; branch HEAD 8f61f06 │
│                                                 │ unchanged                 │
└─────────────────────────────────────────────────┴───────────────────────────┘
```

I did not rebuild the non-FGSA libraries. I copied `.lake/build` from the
branch worktree, and Lake replayed the build. The lease, reachability and
import prototypes run on those artifacts.
