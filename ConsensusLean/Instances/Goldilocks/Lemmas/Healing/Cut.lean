module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset

/-! # Goldilocks Healing: HR.1, cut and reset

HR.1 over a Goldilocks run under `Healthy(g)` and `NoColl` (claims HR.1, status S; healing-simple
`t1-proof.md` §7 (F1), `producer-reset-continuation.md` §4 (R0) and §10). The theorem
`cut_and_reset` and one lemma per conjunct are in `Cut/Reset`; the facts of one reachable FG store
(G0.2 (f), the signed height pair, one state per block) in `Cut/Store`; the FG states of the
honest nodes of a run and the tick order at an `fg_attest` cut in `Cut/Run`. -/
