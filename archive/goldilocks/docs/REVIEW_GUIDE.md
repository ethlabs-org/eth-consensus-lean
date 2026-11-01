# Review guide

Read the public contract before treating an aggregate theorem as an unconditional guarantee.
A useful path through FG-SA is:

1. [The run binding](../fgsa/AvailableChainFGSARun/Model/Protocol.lean), then the engine's duty
   run and sleep/delivery conditions.
2. [FGSAClaims](../fgsa/AvailableChainFGSAClaims/FGSAClaims.lean) and its imported Statements:
   identify the regime and output premises of the field being reviewed.
3. [Assembly.Root](../fgsa/AvailableChainFGSAProofs/Proofs/Assembly/Root.lean), then the matching
   lane's Export, adapters and producers. Shared FG results live in `generic/FGCompose` under
   the full library name `AvailableChainFGCompose`.
4. [Inhabit witnesses](../fgsa/AvailableChainFGSAInhabit/) and the owning `Tests/` audit.
   Check that a positive witness satisfies its premises on exactly its declared run/data.
5. [The blueprint map](internal/FGSA-BLUEPRINT-LEAN.json) and
   [OPEN records](internal/FGSA-BLUEPRINT-OPEN.md) for unclosed prose obligations.

For a premise ledger, record the exact statement and producer of every assumption:

| Premise family | What to inspect |
| --- | --- |
| Authentication, roots, codecs | The exact model/reads and named-body obligations |
| Sleep, delivery, finite horizon | Receiver readiness and strict bounds in the run conditions |
| Recovery and continuation | The field's regime and the assembly that supplies it |
| Geometry and law bundles | Whether supplied by a proof or retained as a premise |
| Non-vacuity | A witness and its `_premises_sat` proof, with its exact conditional statement |

Use the pinned [toolchain](../lean-toolchain), then:

```sh
lake build --wfail
lake build --wfail @ AvailableChainFGSAClaimsTests AvailableChainFGSAProofsTests \
  AvailableChainFGSAInhabitTests
python3 -B scripts/source_layout.py --check
python3 -B scripts/source_layout.py --selftest
bash scripts/gate.sh --tier full --base <accepted-base> --neg
```

The FULL gate runs under the project's existing platform memory/concurrency workflow; the
lead runs the NUC gate for this reorganization. Individual checks are mapped in the
[root README](../README.md). Axiom audits inspect compiled kernel dependencies. Import,
header and GLY checks enforce source boundaries; proof-equation and coverage checks enforce
exports and owning audits. API checks compare compiled declaration graphs and snapshots.
Shake rejects new import-removal suggestions, subject to its explicit keep rules.

These checks have distinct scopes. None proves that prose and formal statements mean the
same thing, or that an implementation meets all contractual premises. PC-SA remains unported
and excluded from compiled default targets; its sources remain scanned. Compare revisions
using their own Lake layout, and use [PATHS](internal/PATHS.md) when following old coordinates.
