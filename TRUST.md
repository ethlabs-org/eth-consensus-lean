# Trust and review boundary

## Trusted code and dependencies

Lean **v4.35.0's kernel** checks proofs under exactly `propext`, `Classical.choice` and `Quot.sound`.
Mathlib and its dependencies' definitions are trusted at `scripts/pins.toml`'s exact revs;
step 0 checks toolchain, manifest, clean checkouts and Lake's actual resolution. Approved revisions:

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

The snapshot header includes lakefile `leanOptions` (printing, implicit binders, linters, synthesis depth),
toolchain and dependency revs. Tactics/elaborators run during compilation; replay checks the terms.

The v4.34.1 → v4.35.0 upgrade was audited in `reorg2/dep-audit.md` and `expected-diffs.md`
(in the reorganization run folder): 2,535 project constants and their dependency closure were compared.
All 43 changed project and 24 changed dependency constants have kernel-checked equivalence probes,
including the `Decidable` representation change, generated eliminators and `protects`.
A cut-graph traversal covered all 109 one-sided dependencies through proved changed constants; no unresolved differences remained.

## Roles of the checks

- **Spec drift:** snapshot every Spec-owned constant (readable text plus structural hashes), diff
  against `scripts/spec-snapshot.txt`, then owner review of every change (`spec-approved`).
  Proof values are omitted by proof irrelevance; non-proof auxiliary constants are included.
- **Dependency drift:** exact pins; the upgrade above additionally used the dependency audit.
- **Unfinished proofs** (foundation plan §5, the FLT/Carleson model): `sorry` may stay only in the
  `sorry = true` layers of `scripts/boundaries.toml` (`Lemmas`, `Proofs.<M>`; check-boundaries.py refuses
  the flag on a trusted layer, outside Lemmas/Proofs or outside the default library); no declaration of Spec,
  Statements, Main, the instances, the tests or the solution contains one (check-decls `--sorry-ok`, grep step 7),
  and it is never an axiom. **Certified = the import closure of
  `Solution`**: axiom-audit (step 3b, every PR) fails any declaration of `ConsensusLean` or `Solution` in that
  closure that depends on an axiom other than the three standard ones (`sorryAx`, `native_decide`'s axioms, a
  declared axiom, also through imports), and so it does for every test declaration (a test built on an unfinished
  lemma proves nothing; grep step 7 refuses proof `example`s, which never enter the environment). `Solution` imports
  `Main` and every milestone today, so all of them must be finished; a new milestone may stay unfinished while
  neither imports it (step 3b's report lists what is unfinished). The instances reach the generic library only
  through `Main`, inside the closure, so everything they use is finished today. The review
  pins and the comparator check the review theorems' axioms too. axiom-audit's shared memo can under-count inside
  an inductive/constructor cycle when the declaration that uses the axiom directly is not audited (the tests gate,
  whose roots exclude the library): check-decls still fails a direct `sorry` outside the sorry layers. `lake build --wfail` runs with `warn.sorry = false`, so every other warning fails the build.
- **Proofs:** leanchecker, one process per leaf module of the checked libraries (parents own no
  constants); `lake check` (of the default targets while the sorry layers' files hold no `sorry`/`admit` outside
  comments and strings: it rejects `sorryAx`; otherwise only the comparator replays what the solution uses of the
  dependencies); check-decls; axiom-audit; and the comparator: statement matching, axiom limits,
  identical reachable constants across exports (tamper resistance) and sandboxed replay, by Lean's
  kernel and, with `--paranoid`, by every external kernel bundled with Lean.
  The comparator is **not a Spec-drift check**: both sides read the same source tree.

`scripts/check.sh` wires checks and fixtures. CI runs its fast mode (no replay, `lake check` or
comparator; check-decls, axiom audit, snapshot diff and review pins included) on every pull request and push to main,
and its full mode nightly, on demand and on milestone/release tags: a proof change merged after a green
fast run is replayed by the kernel at the latest the next night. `lake check` and `lake comparator` run
inside a bubblewrap sandbox wherever `bwrap` exists (CI full mode always; the shared box since
2026-10-29); without it check.sh skips them and lists them as CI-only.

## Checking tools and open trust notes

EthLib check-decls is CC0-1.0 and SHA-256-pinned by `scripts/vendor.sha256`. Every vendored file was copied
from the reuse-study clone (2026-10, no git metadata) and is byte-identical to
[ethereum/EthLib](https://github.com/ethereum/EthLib) at `6390c73ef040311e807b9047d99dca6b1be1c42f` (checked 2026-10-29),
except two local patches to `scripts/CheckDecls.lean`. The first (#13) computes the in-scope module indices once instead of
rebuilding `EnvironmentHeader.moduleNames` (an array of every imported module) for each of ~450k constants. Same
findings, counts and exit codes on every library and on `test_check_decls.sh`; step 3 about 25× faster.
A second local patch (#5) fixes the reaches-opaque frontier: a definition that check-decls does not check
(one in a module with a `Proofs` or `Exports` component, a `Repr`/`ToString` formatting definition, an `initialize`
function) no longer counts as having reported the opaque constants it reaches; they are reported at the checked
definition that unfolds it. Without it, the single `ConsensusLean` scope let a definition in `Main` or an instance
reach an opaque unreported through such a definition (self-test fixture `CheckFixtures.HiddenOpaque`).
A third local patch (#7) adds `--sorry-ok PREFIX` (repeatable): a `sorry` finding at a declaration of a module
under such a prefix is listed (`allowed sorry ...`) instead of failing; every other finding kind is unchanged.
check.sh passes the prefixes of the `sorry = true` layers; without the option the tool behaves as before.
Upstream copy: `0032a6629a73ac37f49ca52b9bd665f2c6755b6014d629f8775c6f850f273bb2`; with the #13 patch: `69b9fe48f5d913031348aa33895155e96236819ba7d86c9e36675a793c1241d6`; with #13 and #5: `03ed87d6cecae9a145ed47e56788978ffbe67a70055c3326f933a6d397edb10a`; with all three: `b941e9baa619e80d954e2cdaf32ba7d5f48a8b29e4c888d3b97a91cee42aa367`.
`scripts/test_check_decls.sh`: `591a1d993df5dc1a01a9cf645f71cbeffdb7da9fdff9e3ca8f5179f60ead9f25`.
`vendor.sha256` also pins fixtures/licence. check-decls runs imported modules' initializers:
a defence against mistakes, not an adversarial checker.
[leanprover-community/axiom-audit](https://github.com/leanprover-community/axiom-audit) v0.1.2
(`46024e005996495c65ef609368e11ab39c4222e3`, Apache-2.0; the tool the foundation plan and lean-action's
`axiom-audit` input name) is vendored verbatim as `scripts/AxiomAudit.lean` and `scripts/AxiomAuditMain.lean`
(its `Main.lean`), SHA-256-pinned likewise. Like check-decls it loads `.olean` files with `trustLevel := 1024`:
it reads which axioms each declaration uses, not whether the proofs check, so kernel replay (steps 5, 10, 11) and
the grep for `debug.` options (step 7) cover what it trusts.

`scripts/check-boundaries.py` checks the layer matrix of `scripts/boundaries.toml` on parsed imports
(`lean --deps-json`; the inventory part started as a CC0 port of verified-consensus `check-review-boundary.rb`). `scripts/check-pins.py` checks provenance. Our `scripts/SpecSurface.lean` loads no extension state and runs no checked code.
Its extension check is a persisted-extension policy, not a source audit: local/non-persisted commands
are visible only through their effect in the snapshot. A grep backstop adds hygiene.

Mathlib `.olean` files fetched by `lake exe cache get` in CI or taken from the shared Lake
artifact cache on the box are not rebuilt locally. leanchecker replays the project's modules only;
`lake check` exports the default targets with the constants they use and replays that export, which
re-checks what the project uses of them. A dependency's own lakefile in its pinned, clean checkout is trusted
as upstream content. The check scripts/configuration (`scripts/**`, `.github/**`, the lakefile) are trust
infrastructure reviewed by agents, not by the owner: Code Owner review (`.github/CODEOWNERS`) is not enforced (#21).
A change to what a trust check checks needs two independent agent reviews linked in its PR; a speedup that keeps
every check's verdict needs one review and evidence that the fixtures' verdicts are unchanged.

## Trusted statements

The trusted layers (`ConsensusLean.{Init,Core,Spec,Statements,ToMathlib}`) are the claim
(file list in `README.md`); they allow only trusted layers, so their closure holds only trusted modules and the pinned base set.
It cannot reach proofs, instances, the solution, tests or fixtures. Pins/snapshot fix dependencies/meaning.
The trusted surface is `ConsensusLean/{Init,Core,Spec,Statements,ToMathlib}` (each as `X.lean` and
`X/**`), `Challenge.lean`, `comparator.json`, `lean-toolchain`, `lake-manifest.json`,
`ConsensusLeanTest/ReviewAxioms.lean` and `ConsensusLeanTest/ReviewGuard.lean`, and, since #38, the instance semantics and statements (`ConsensusLean/Instances/<P>/{Spec,Statements}`
as `X.lean` and `X/**`, and `Instances/<P>/Refinement/Defs.lean`, for every instance `P`). The instance paths are
tag-protected but are not trusted layers: their imports are not restricted to trusted layers (the Goldilocks
`Baseline` modules and the Bft, Streamlet and Tendermint Specs import the generic `Main` through a reviewed
exception). The definitions the Goldilocks sheet reads from there, `Lemmas/Problem/Derived.lean`, are in the list
too; the tag freezes their text, not everything they import. `scripts/boundaries.toml`
(`[checks] trusted_paths`) lists it, and check-boundaries.py requires it to cover every file of a trusted or
`protected` layer;
CI's `review-boundary` compares those paths (literal, at the PR head and at the tag) with `spec-approved`.
`ConsensusLean/Statements/Review.lean` must hold statements only: every non-proof constant needs a
review pair (`ConsensusLeanTest/ReviewGuard.lean`, `ReviewGuard.checkComplete`; generated matchers
are exempt). `ConsensusLeanTest/ReviewAxioms.lean` compiles alpha-equality/binder-kind and axiom pins.
Primary: `Consensus.Review.AcceptedGood`; secondaries: `RegimesRealizable`, `LogFaithful`, `HeldIffServed`.
Only the owner, or an agent he explicitly authorizes (never the PR's author on its own), sets or moves
`spec-approved`, after reviewing the protected changes.

## Assumed, not proved; per-instance bindings

Model adequacy assumes one-key-per-validator PKI, sound membership credentials, unforgeable
key/role-binding signatures, persistent client slashing protection, the stated delivery service
(including forwarded adversarial objects and persistent transaction inboxes), known Δ and unit ticks,
restart/tick/delivery event order and restarts at wakes, and hash collision resistance.
Static, all-knowing adversary; no adaptive corruption. Per instance the reviewer binds outputs to user reads,
`conflicts` to the enforced slashing rule, and numbers to the intended values.

## Not proved / out of scope

There is no FG-SA bridge proving `GoldilocksTarget`; Streamlet/Tendermint are values, not protocol
proofs, and Tendermint's pointwise `notReadyAtMost` is a placeholder. Arbitrary L0 `Good` systems
trust their abstraction; only `sysOf` binds the distributed model. See `README.md` Scope: one GST/outage,
full-participation healthy runs, equal weights, fixed Δ, bounded latency, no adaptive/probabilistic/PoW
model, non-validator readers, responsiveness, transaction validity/fees/capacity/chain quality, public
schedules or partitioned-committee premise; run-wide collision escape and same-run accountability.
Sleepy liveness is mandatory for stable, final accountability is mandatory, and no separate network
knowledge-of-equivocation service is modelled. No concrete protocol correctness follows from values alone.
