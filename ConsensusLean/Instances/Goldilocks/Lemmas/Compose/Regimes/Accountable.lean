module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Outputs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts

public section

/-! # Goldilocks Regimes: non-framing over a fixed honest set (R.7)

`goldilocksRun_nonFraming` (G0.5; no `NoColl`): the FG projection executes the FG at the honest
nodes (`fg_exec`), so an honest validator's signings are the outputs of one client run
(`Store.signed_run_of_exec`), which signs no slashable pair (`FG.client_safety`). The growing row
`Regimes.Growing.non_framing` applies it on a retained prefix; the static R.7 rows are retired
(owner decision), and the growing accountability and safety rows are proved over the growing FG
projection (`Lemmas/Growing/Compose/Outputs`). -/

namespace Consensus.Goldilocks.Regimes

open AC (ACParams Payload)
open Compose

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n}

/-- **R.7, `nonFraming`** of a Goldilocks run from any AC starts `ini`: the FG projection
executes the FG at the honest nodes, whose clients sign no slashable pair. -/
theorem goldilocksRun_nonFraming {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : GoldilocksRun proposer dg H tr ini) {v : Fin sp.n} (hv : v ∈ H)
    {k k' : Nat} {a b : FG.Att sp.n} (ha : tr.SignAt v k a) (hb : tr.SignAt v k' b) :
    ¬ FG.slashable a b := by
  obtain ⟨inputs, hin, hsign⟩ := Store.signed_run_of_exec (fg_exec hrun.toLocalRun) hv
    (max k k' + 1)
  have conv : ∀ m c, tr.SignAt v m c → tr.projFG.SignAt v m c := fun m c ⟨src, hs⟩ =>
    ⟨src, projFG_callAt.2 hs⟩
  exact FG.client_safety sp.toParams.fg v inputs hin a
    (hsign k (by omega) a (conv k a ha)) b (hsign k' (by omega) b (conv k' b hb))

end Consensus.Goldilocks.Regimes

end
