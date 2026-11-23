module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Groups

public section

/-! # The votes of an own proposal are pooled before its block cut

In any Goldilocks run, the votes in the payload of an honest node's own proposal were in its pool
before its AC block cut: `own_proposal_payload_pooled_run`. It reads the node's tick, proposal
and block cuts and their cut laws only. Growing faults use it on the prefix through the
proposal. -/

namespace Consensus.Goldilocks.Obligations.Growing

variable {sp : AC.ACParams} {ro : AC.ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

section Generic

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A}

/-- A pooled proposal member remains pooled at the AC block cut if proposing preserves it. -/
theorem _root_.Consensus.Goldilocks.Compose.own_proposal_payload_pooled_run
    {ini} (hr : Node.LocalRun proposer dg H sg tr ini)
    {M : Type} {pooled : A.State → M → Prop}
    (hpres : ∀ a φ τ m, pooled a m → pooled (A.proposal a φ τ).1 m)
    {y : Fin P.n} (hy : y ∈ H) {j : Nat} {t : Time} {x : Nat}
    (hg : tr.GroupAt proposer dg y j t (.tick x))
    {ℓp : ACLabel A} (hcp : tr.CallAt y (j + 1) (.ac ℓp)) (hpc : ℓp.call = .proposal)
    {B : A.Blk} (hcb : tr.CallAt y (j + 2) (.fg (.block B true))) {m : M}
    (hm : pooled (Node.tickStep proposer dg y (tr.state y j) t x .acTick).1.ac m) :
    pooled (tr.state y (j + 3)).ac m := by
  have htick := hg.2.1 0 (by simp [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps,
    Node.tickStep, Node.acCall])
  have hct : tr.CallAt y j (Node.acCall y (tr.state y j) t .tick).2 := by
    exact ⟨by simpa using htick.1, by
      simpa [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps, Node.tickStep,
        Node.acCall] using htick.2.2.2.2⟩
  have ht : tr.time j = t := by simpa using htick.2.1
  have hl := hr.cutLaw y hy j _ hct
  rw [ht] at hl
  have hstate : (tr.state y (j + 1)).ac =
      (Node.tickStep proposer dg y (tr.state y j) t x .acTick).1.ac := by
    rw [tr.state_succ_of_call hct]
    exact (congrArg Prod.fst hl.2.1).symm
  have hp := (hr.cutLaw y hy (j + 1) _ hcp).2.1
  rw [hpc] at hp
  have he : (A.proposal (tr.state y (j + 1)).ac ℓp.frame (tr.time (j + 1))).1 =
      (tr.post (j + 1)).ac := congrArg Prod.fst hp
  rw [show j + 3 = (j + 2) + 1 by omega, tr.state_succ_of_call hcb,
    (hr.cutLaw y hy (j + 2) _ hcb).2.2.1,
    show j + 2 = (j + 1) + 1 by omega, tr.state_succ_of_call hcp, ← he]
  exact hpres _ _ _ _ (hstate ▸ hm)

end Generic

/-- Goldilocks proposal members come from a pool. -/
theorem proposal_pool {a : AC.ACState sp.n} {φ : (goldilocksNode sp ro).Frm} {t : Time}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (AC.Payload sp.n)} {p : AC.Payload sp.n}
    (hd : (AC.acProposal sp a φ t).2 = some (d, p)) {m : AC.Vote sp.n} (hm : m ∈ p.1) :
    ∃ σ, m ∈ a.pool σ := by
  obtain ⟨-, hpay, -⟩ := AC.proposal_payload hd
  rw [hpay] at hm
  exact ⟨_, (AC.ACState.mem_poolAt.mp (List.mem_filter.mp hm).1).2⟩

/-- The Goldilocks proposal changes locks without removing pooled votes. -/
theorem proposal_preserves_pool (y : Fin sp.n) (a : AC.ACState sp.n)
    (φ : (goldilocksNode sp ro).Frm) (t : Time) (m : AC.Vote sp.n) (hm : ∃ σ, m ∈ a.pool σ) :
    ∃ σ, m ∈ (AC.acProposal sp a φ t).1.pool σ := by
  obtain ⟨σ, hm⟩ := hm
  have hg : AC.Grows a (AC.acProposal sp a φ t).1 :=
    (AC.voteClosed_grows a).step ro y φ t (c := .proposal) (by simp) (AC.Grows.refl a)
  exact ⟨σ, hg.mem hm⟩

/-- Votes in an actual own-proposal payload were already pooled before its AC block cut. -/
theorem own_proposal_payload_pooled_run {ini} (hr : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {t : Time} {x : Nat}
    (hg : tr.GroupAt proposer dg y j t (.tick x))
    {d : DutyHead sp.n (List (FG.Att sp.n)) (AC.Payload sp.n)} {p : AC.Payload sp.n}
    (hd : (Node.acProposal
      (Node.tickStep proposer dg y (tr.state y j) t x .acTick).1 t).2.2 = some (d, p))
    (hprop : ∃ ℓp, tr.CallAt y (j + 1) (.ac ℓp) ∧ ℓp.call = .proposal)
    (hfg : ∃ B, tr.CallAt y (j + 2) (.fg (.block B true)))
    {m : AC.Vote sp.n} (hm : m ∈ p.1) :
    m ∈ (tr.state y (j + 3)).ac.pool m.slot := by
  obtain ⟨ℓp, hcp, hpc⟩ := hprop
  obtain ⟨B, hcb⟩ := hfg
  obtain ⟨σ, hmem⟩ := Compose.own_proposal_payload_pooled_run hr.toLocalRun
    (pooled := fun a m => ∃ σ, m ∈ a.pool σ) (proposal_preserves_pool (ro := ro) y)
    hy hg hcp hpc hcb (proposal_pool (ro := ro) hd hm)
  have hslot := (Compose.state_pool_cap hr hy (j + 3) σ).1 m
    (by simpa only [Compose.projAC_state hr.toLocalRun hy] using hmem)
  rwa [hslot]

end Consensus.Goldilocks.Obligations.Growing

end
