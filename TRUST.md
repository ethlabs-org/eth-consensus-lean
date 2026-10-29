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
- **Proofs:** leanchecker, one process per default-library leaf module (parents own no
  constants); `lake check`; check-decls; and the comparator: statement matching, axiom limits,
  identical reachable constants across exports (tamper resistance) and sandboxed replay, by Lean's
  kernel and, with `--paranoid`, by every external kernel bundled with Lean.
  The comparator is **not a Spec-drift check**: both sides read the same source tree.

`scripts/check.sh` wires checks and fixtures. CI runs its fast mode (no replay, `lake check` or
comparator; check-decls, snapshot diff and review pins included) on every pull request and push to main,
and its full mode nightly, on demand and on milestone/release tags: a proof change merged after a green
fast run is replayed by the kernel at the latest the next night. `lake check` and `lake comparator` run
inside a bubblewrap sandbox wherever `bwrap` exists (CI full mode always; the shared box since
2026-10-29); without it check.sh skips them and lists them as CI-only.

## Checking tools and open trust notes

EthLib check-decls is CC0-1.0 and SHA-256-pinned by `scripts/vendor.sha256`. Every vendored file was copied
from the reuse-study clone (2026-10, no git metadata) and is byte-identical to
[ethereum/EthLib](https://github.com/ethereum/EthLib) at `6390c73ef040311e807b9047d99dca6b1be1c42f` (checked 2026-10-29),
except one local patch to `scripts/CheckDecls.lean` (#13): it computes the in-scope module indices once instead of
rebuilding `EnvironmentHeader.moduleNames` (an array of every imported module) for each of ~450k constants. Same
findings, counts and exit codes on every library and on `test_check_decls.sh`; step 3 about 25× faster.
Upstream copy: `0032a6629a73ac37f49ca52b9bd665f2c6755b6014d629f8775c6f850f273bb2`; patched: `69b9fe48f5d913031348aa33895155e96236819ba7d86c9e36675a793c1241d6`.
`scripts/test_check_decls.sh`: `591a1d993df5dc1a01a9cf645f71cbeffdb7da9fdff9e3ca8f5179f60ead9f25`.
`vendor.sha256` also pins fixtures/licence. check-decls runs imported modules' initializers:
a defence against mistakes, not an adversarial checker.

`scripts/check-imports.py` is a CC0 port of verified-consensus `check-review-boundary.rb` using parsed
imports for R1–R3. `scripts/check-pins.py` checks provenance. Our `scripts/SpecSurface.lean` loads no extension state and runs no checked code.
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

All of `ConsensusSpec/` is the claim (file list in `README.md`); R1 excludes Proofs/Instances/Tests from its imports. Pins/snapshot fix dependencies/meaning.
`ConsensusSpec/Statements.lean` must hold statements only: every non-proof constant needs a
review pair (`ConsensusTests/ReviewGuard.lean`, `ReviewGuard.checkComplete`; generated matchers
are exempt). `ConsensusTests/ReviewAxioms.lean` compiles alpha-equality/binder-kind and axiom pins.
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
