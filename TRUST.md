# What you must trust

A proof checked by Lean is only as good as what it is checked against. This file says what you must trust to
believe the certified statements, which files state them, what the automatic checks guarantee, where those checks
stop, and what the model assumes about the world. [`docs/checks.md`](docs/checks.md) has the detail of every check.

## 1. What you trust

- **Lean v4.35.0's kernel**, which checks proofs under exactly the axioms `propext`, `Classical.choice` and
  `Quot.sound`.
- **Mathlib and its dependencies** at the exact revisions of `scripts/pins.toml`. Step 0 checks the toolchain, the
  manifest, clean checkouts and Lake's actual resolution. Approved revisions:

  | Package | Revision |
  |---|---|
  | mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
  | plausible | `dfa4f38190d07c37e315953e08b90fe2d95b3c24` |
  | LeanSearchClient | `d6b4c7be5be75ec4917c873ac50c756dc1436372` |
  | importGraph | `a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93` |
  | proofwidgets | `df72b022e558978a1c50264cfc4d7fec86fa8e04` |
  | aesop | `4a174c490d8707121c4a9290800489f105d85e07` |
  | Qq | `dce0ad79c486cb1fb504af04f953c3466b0c6db8` |
  | batteries | `66e469188fe07963e5cf666c7d4433f45b8131c5` |
  | Cli | `c24fe6078c630e89b489bffe59b3e20ac30d12c8` |

- **The build.** The lakefile's `leanOptions` are part of the Spec snapshot header. Tactics and elaborators run
  during compilation; kernel replay checks the terms they produce. Mathlib's prebuilt `.olean` files are not
  rebuilt, but `lake check` replays what the project uses of them. A dependency's own lakefile, in its pinned and
  clean checkout, is trusted as upstream content.
- **The trusted files** of §2, read by a person: they state what is claimed.

The check suite itself (`scripts/**`, `.github/**`, the lakefile) is not trusted surface. A change to what a check
checks comes with fixtures that show the new verdicts; a speedup comes with evidence that every fixture verdict is
unchanged.

## 2. The trusted surface

| Part | Paths | Rule |
|---|---|---|
| Trusted layers | `ConsensusLean/{Init,Core,Spec,Statements,ToMathlib}`, each as `X.lean` and `X/**` | They import only trusted layers, so their closure holds only trusted modules and the pinned base set; it cannot reach proofs, instances, the solution, tests or fixtures. The files, in reading order: [`docs/definition.md`](docs/definition.md#reading-order-the-trusted-files). |
| Protected layers | `ConsensusLean/Instances/<P>/{Spec,Statements}` (as `X.lean` and `X/**`) and `Instances/<P>/AsChainShape.lean`, for every protocol instance `P` (today Goldilocks) | Not trusted layers, but on the surface: they import only trusted and protected layers, so the closure of the instance endpoint stays inside the surface. |
| Files | `Challenge.lean`, `comparator.json`, `lean-toolchain`, `lake-manifest.json`, `ConsensusLeanTest/ReviewAxioms.lean`, `ConsensusLeanTest/ReviewGuard.lean` | The certified statements, how they are compared, the toolchain and dependency pins, and the statement and axiom pins. |

The list lives in `scripts/boundaries.toml` (`[checks] trusted_paths`); `check-boundaries.py` requires it to cover
every file of a trusted or protected layer. Outside it: the Shape examples (`ConsensusLean/Examples/Shape/`), which no
Challenge statement reaches; the Goldilocks milestone statements other than the endpoint, and the instance Spec only
they reach (`ConsensusLean/Instances/Goldilocks/Milestones/`), which are proved lemmas, not certified statements;
and `Lemmas/Problem/Derived.lean`, which no trusted statement reads (by a compiled type-closure walk).

`ConsensusLean/Statements/Review.lean` holds statements only: `ReviewGuard.checkComplete` requires every
non-proof constant (generated matchers exempt) to have a review pair, and `ConsensusLeanTest/ReviewAxioms.lean`
compiles alpha-equality, binder-kind and axiom pins. Primary statement: `Consensus.Review.ObligationsSufficient`, and
its form on a class of runs `ObligationsSufficientOn` (at constant faults, the static adversary at full strength);
secondaries: `RegimesRealizable`, `LogFaithful`, `HeldIffServed`. Challenge adds the Goldilocks endpoint and headline,
`MeetsObligations` and `Consensus.Goldilocks.GoldilocksCorrect` (Goldilocks is a `CorrectProtocol` under the growing
adversary), from `Instances/Goldilocks/Statements/Obligations.lean`.

**Changes are recorded, not gated.** Every non-merge commit that touches a trusted path carries a line
`Trusted-surface: <what changes and why>`; `scripts/review-boundary.sh` (self-tested on throwaway repositories)
fails a change without it, reading the lists at HEAD and at the base as literal paths, united. So
`git log --grep='^Trusted-surface:'` lists every change. In CI the review boundary also writes each such
commit's trusted paths and its Trusted-surface line to the summary of the `check` run, so the check run of every
push and pull request records them. The record covers the listed files' text, not everything
they import, and it records changes; it does not approve them. Reading the snapshot diff is part of making a Spec
change; the comparator cannot replace that reading.

## 3. What the checks guarantee

| Risk | Check (step of `scripts/check.sh`) | What it guarantees |
|---|---|---|
| Spec drift | Spec snapshot diff (4) | Every Spec-owned constant (readable text and structural hashes) equals `scripts/spec-snapshot.txt`; a change fails until the snapshot is regenerated and its diff committed. |
| Protected-surface drift | protected snapshot diff (4) | The same for every protected module, against `scripts/instance-spec-snapshot.txt` (`check-boundaries.py --inventory-out` lists the modules). |
| Dependency drift | pins (0) | Exact toolchain, manifest and revisions, clean checkouts, Lake's resolution. The v4.35.0 upgrade was also audited constant by constant (`docs/checks.md`). |
| Unfinished proofs, extra axioms | check-decls (3), axiom audit (3b), grep (7) | `sorry` only in the `sorry = true` layers (`Lemmas`, `Proofs.<M>`), never an axiom; every declaration in the closure of `Solution`, of each `proved_milestone_modules` entry and of every test uses only the three standard axioms; no proof `example`s. |
| Invalid proofs | leanchecker (5), `lake check` (10), comparator (11) | Kernel replay of every leaf module; the default targets exported and replayed with what they use of the dependencies; `Solution` against `Challenge` replayed by Lean's kernel and, with `--paranoid`, by every external kernel bundled with Lean. |
| Wrong statements proved | review pins (6), comparator config (9), comparator (11) | The review statements are alpha-equal to their source theorems with exact axiom lists; `Solution` proves exactly the statements of `Challenge`, built from Spec alone, with identical reachable constants in both exports. |
| Layering | `check-boundaries.py` (2) | The import matrix of `scripts/boundaries.toml`; the trusted closure contains only trusted modules. |
| Cited names | docs (12) | Every `Consensus.…` name in `docs/roadmap.md` and `docs/goldilocks-mapping.md` exists; the trusted-file list of `docs/definition.md` is complete. |
| Unrecorded trusted change | `review-boundary.sh` | Every non-merge commit touching a trusted path carries its `Trusted-surface:` line. |

CI is GitHub Actions: `check` runs the fast mode on every pull request and every push to `main`; `full` runs
everything (kernel replay, `lake check`, the paranoid comparator) nightly, on milestone and release tags and on
demand. A pull request runs on the `pull_request` event with a read-only token and no secrets, so the scripts of a
head can change nothing but its own check result. Full CI rejects any skipped step and a dirty tree. "Certified"
means a passing `full` run of a named main commit. `check` also checks commit email addresses against a public
allowlist: a privacy check, not a trust check.

## 4. Known limits

- A proof-only edit that adds a non-`Prop` auxiliary (a `match_N` definition) inside a theorem's proof still changes
  the snapshot.
- The protected snapshot does not cover the trusted files outside the default library (`ReviewAxioms`,
  `ReviewGuard`: step 6), `Challenge.lean` (step 9), the extension and theorem policies (trusted layers only) or the
  non-Lean trusted files.
- The comparator is not a Spec-drift check: both sides read the same source tree.
- `lake check` covers the default targets only while the sorry layers hold no `sorry`; otherwise only the comparator
  replays what the solution uses of the dependencies.
- Without bubblewrap, `lake check` and the comparator are skipped and listed as CI-only; that is not a passing
  full result. A proof change merged after a green fast run is replayed by the kernel at the latest the next night.
- axiom-audit's shared memo can under-count inside an inductive cycle when the declaration that uses the axiom
  directly is not audited; check-decls still fails a direct `sorry` outside the sorry layers.
- check-decls and axiom-audit load `.olean` files at `trustLevel := 1024` and check-decls runs imported modules'
  initializers: a defence against mistakes, not an adversarial checker. Kernel replay and the grep for `debug.`
  options cover what they trust.
- `SpecSurface`'s extension check is a persisted-extension policy, not a source audit: local commands are visible
  only through their effect in the snapshot.
- Step 3c (the sorry inventory) is a report, not a gate: "mapped" means a paper argument is recorded, not that it
  is valid or the proof finished.

## 5. Assumed, not proved

Model adequacy assumes one-key-per-validator PKI, sound membership credentials, unforgeable
key/role-binding signatures, persistent client slashing protection, the stated delivery service
(including forwarded adversarial objects and persistent transaction inboxes), known Δ and unit ticks,
restart/tick/delivery event order and restarts at wakes, and hash collision resistance.
All-knowing adversary whose set of compromised validators grows (`EnvPoint.faultyAt`, monotone): a compromise is
immediate and permanent, with the ordinary signing key (no forward-secure keys, no corruption delay); it takes
effect before every event of its time; an honest release keeps its provenance after its signer is compromised.
Every lawful trace is quantified, so adaptive scheduling and corruption are covered; no probabilistic or
computational adversary is modelled. The Goldilocks claims are certified for constant faults only while its proofs
migrate (§2). Per instance the reviewer binds outputs to user reads,
`conflicts` to the enforced slashing rule, and numbers to the intended values.

## 6. Out of scope

Streamlet/Tendermint are Shape examples (values, not protocol
proofs, and not on the trusted surface), and Tendermint's pointwise `notReadyAtMost` is a placeholder. Arbitrary L0
`CorrectProtocol` systems trust their abstraction; only `sysOf` binds the distributed model. See
[`docs/definition.md`](docs/definition.md#scope): one GST/outage, full-participation healthy runs, equal weights,
fixed Δ, bounded latency, no adaptive/probabilistic/PoW model, non-validator readers, responsiveness, transaction
validity/fees/capacity/chain quality, public schedules or partitioned-committee premise; run-wide collision escape
and same-run accountability. Sleepy liveness is mandatory for stable, final accountability is mandatory, and no
separate network knowledge-of-equivocation service is modelled. No concrete protocol correctness follows from values
alone.
