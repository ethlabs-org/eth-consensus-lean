# Modeling choices and premises

The [contract draft](internal/CONTRACT.md) records the earlier v1 design. Current source types
and claim premises determine the FG-SA result. In particular, the draft's receiving and
processing during sleep predates the current full-sleep engine.

| Choice | Scope and review obligation |
| --- | --- |
| Committees | Unit-weight seats, assigned by a run's per-label seat mapping; no sampling theorem |
| Corruption | A fixed honest/faulty partition for the run; no adaptive-corruption result |
| Signatures | Abstract authentication and unforgeability conditions, not a cryptographic proof |
| Root identity | Explicit named-body, codec and root premises; inspect the exact claim's scope |
| Sleep | Valid runs have no tick, delivery or restart while asleep |
| Delivery | Checked handler/readiness premises and strict bounds, subject to stated horizons |
| Recovery | Claim-specific regimes and output-contract premises; no automatic network guarantee |
| Runs | Finite event traces and horizons; liveness is quantified within the stated run conditions |

Start with [model objects](../engine/AvailableChainModel/Objects/) and
[the duty run](../engine/AvailableChainEngineV2/Engine/Duty/Run.lean). The duty protocol model
allows label-specific seat counts and scheduled actions; the FG-SA binding distinguishes
committee actions from single-seat proposal duties. Its self-visible FG duty is explicit.
Do not carry the v1 draft's all-label committee or no-self-observation wording into v2 without
checking the binding in [Protocol.lean](../fgsa/AvailableChainFGSARun/Model/Protocol.lean).

An assumption in a statement is contractual unless its producer is supplied by a proved
assembly or witness on the same data. A theorem that derives a claim from a law bundle does
not prove that an arbitrary implementation satisfies the bundle. The recovery, receipt,
geometry and continuation statements in
[FGSAClaims/Statements](../fgsa/AvailableChainFGSAClaims/Statements/) expose those obligations.
The [assembled claim types](../fgsa/AvailableChainFGSAClaims/FGSAClaims.lean) remain the precise
reference for each public field.

[FGSAInhabit](../fgsa/AvailableChainFGSAInhabit/) supplies concrete non-vacuity witnesses.
They show satisfiable premises for their exact runs and data; they do not establish every
regime for every environment. Positive controls retain their `_premises_sat` proofs and
negative controls isolate the stated failed condition.

Historical ledgers and freeze records are preserved under `internal/`; they describe their
recorded revision. The current API is a compiled snapshot, with exact comparison checks.
This layout change grants no additional assumptions, import permissions or baseline exceptions.
