module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Reach
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run

public section

/-! # Shadow P-U: proposal and attestation interfaces

These three named interfaces are unresolved. Their stock proofs await the shadow
handler-chain and own-block suppliers. This module stays downstream of Run and
Coherence; neither supplier module imports it.
-/

namespace Consensus.Goldilocks.Coherence

open AC (ACParams ReplayOrder Payload)

section Proposals

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}

/-- Unresolved: an honest proposal is accepted at its cut, from arbitrary run starts. -/
theorem accept_of_proposesAt' {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : GoldilocksRun' proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat} {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hW : tr.ProposesAt p k W) :
    tr.AcceptAt p k W ∧ W ∈ (tr.state p (k + 1)).fg.tree ∧ tr.post k = tr.state p (k + 1) := by
  sorry

/-- Unresolved: extraction of the AC proposal run from the proposal cut. -/
theorem honestProposalRun_of_proposesAt' {ini} (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} {kP s : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hp : p ∈ H) (hpp : p = proposer s) (hP : tr.ProposesAt p kP P)
    (hPs : P.slot = s) : Healing.HonestProposalRun tr H proposer s P := by
  sorry

end Proposals

section Attestations

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- Unresolved: an attestation is sourced by the immediately preceding AC toFG call. -/
theorem attest_source' (h : Node.LocalRun' proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    {j : Nat} {C : A.Blk} {a : FG.Att P.n} (hc : tr.CallAt y j (.fg (.attest C (some a)))) :
    ∃ j', j = j' + 1 ∧ ∃ ℓ : ACLabel A, tr.CallAt y j' (.ac ℓ) ∧ ℓ.call = .toFG ∧
      tr.time j' = tr.time j ∧ (A.toFG (tr.state y j').ac ℓ.frame (tr.time j')).2 = some C ∧
      (tr.state y j).fg = (tr.state y j').fg := by
  sorry

end Attestations

end Consensus.Goldilocks.Coherence
