module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Settle
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Agree
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing, HS.3: the setting of frozen-tree agreement

HS.3 (a), with its settled premise: the facts
that do not compare walks:

* **The ready proposal is an honest proposal** of the AC projection (`honestProposalRun_of_ready`:
  the own block is the tick's proposal, accepted at once, C0.3), so HS.2's proposal clause
  applies to it.
* **The setting** `AgreeSetting`: HS.3 (a)'s premises with the proposal's `ac_proposal` call
  (`Compose.proposal_data`), its duty head `d` (`P.parent = d.head`) and payload `pay`. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload gbar)

/-! ### Block stamps -/

section Stamps

variable {FGP : Type} {sp : ACParams} {H : Set (Fin sp.n)}
  {U : Set (AC.Blk sp.n FGP)} {tr : AC.GTrace sp FGP}

end Stamps

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n}
  {ini : Fin sp.n → (goldilocksNode sp).State} {g ΔF w : Time}
  {i₀ i m : Nat}
  {c : PhaseCase (AC.Blk sp.n (List (FG.Att sp.n)))}

/-! ### The phase-interval sandwich -/

/-! ### The ready proposal is an honest proposal -/

/-- An actual honest proposal is made by the tick's `ac_proposal` call and accepted at once.
No global support-heldness or healing premise is needed. -/
theorem honestProposalRun_of_proposesAt {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} {kP s : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hp : p ∈ H) (hpp : p = proposer s) (hP : tr.ProposesAt p kP P)
    (hPs : P.slot = s) : HonestProposalRun tr H proposer s P := by
  have h := hrun.toLocalRun
  subst p
  obtain ⟨⟨⟨acc, hc⟩, hpos⟩, -, htk⟩ := hP
  refine ⟨hp, ?_⟩
  rcases Compose.blockCall_cases h hp hc with hg |
    ⟨j, x, fgDue, rfl, hg, hpr, d, pay, hdp, hB, -, -, -, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  have hreq : ({ goldilocksNode sp with initial := ini (proposer s) } :
      NodeAC sp.toParams).Requirements :=
    Compose.requirements_from sp (hrun.vstart (proposer s))
  obtain ⟨hc1, ht1, hst1⟩ := tick_proposal_call h hp hg hpr
  obtain ⟨hacc, ht2⟩ := own_block_accepted h hreq hrun.genesis_root_ok hnc hp hg hpr hdp
  obtain ⟨hacc3, ht3, -⟩ := ac_block_after h hp hacc
  have hts : tr.time (j + 2) = sp.ts s := by
    rw [htk, sp.slotTime_eq, hPs]; rfl
  subst hB
  refine ⟨j + 1, ⟨.proposal, Node.frame
    (Node.tickStep proposer dg _ (tr.state _ j) (tr.time (j + 2)) x .acTick).1, []⟩,
    d, pay, Compose.projAC_callAt.2 hc1, rfl, ?_, ht1.trans hts, rfl, hPs, rfl,
    rfl, j + 3, by omega, hacc3, ht3.trans (ht2.trans hts)⟩
  have ht1' : tr.projAC.time (j + 1) = tr.time (j + 2) := ht1
  rw [Compose.projAC_state h hp, hst1, ht1']
  exact hdp

/-- **A ready proposal is an honest proposal** of the AC projection. The support and joined
conjuncts are unnecessary for this operational extraction. -/
theorem honestProposalRun_of_ready (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} {kP s : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p kP s P) : HonestProposalRun tr H proposer s P :=
  honestProposalRun_of_proposesAt hrun hnc hP.1 hP.2.1 hP.2.2.2.1 hP.2.2.2.2.1

/-! ### The setting -/

section Setting

variable {p : Fin sp.n} {kP s : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}

/-- **The setting of HS.3 (a)**: its premises (with the settled premise), and the
proposal's `ac_proposal` call at cut `iP`, at `t_s`, with duty head `d` (`P.parent = d.head`)
and payload `pay`. -/
structure AgreeSetting (K : AC.CommitteeDict sp.n) (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp) (g ΔF w : Time) (i₀ i m : Nat)
    (c : PhaseCase (AC.Blk sp.n (List (FG.Att sp.n)))) (p : Fin sp.n) (kP s : Nat)
    (P : AC.Blk sp.n (List (FG.Att sp.n))) (iP : Nat) (ℓp : ACLabel (goldilocksNode sp))
    (d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)) (pay : Payload sp.n) : Prop where
  run : GoldilocksRun proposer dg H tr (AC.committeeStart sp.genesisRoot K)
  shared : HSShared tr H K dg g ΔF
  catchUp : CatchRun tr H g (2 * sp.Δ)
  settled : SettledIn tr H g w i₀ m c
  settled_le : i₀ ≤ i
  ready : ReadyProposal tr H proposer p kP s P
  start_le : i ≤ kP
  start_time : tr.time i ≤ sp.ts ((s : Int) - 1) + 3 * sp.Δ
  gbar_le : gbar g ≤ sp.ts ((s : Int) - 1) + 3 * sp.Δ
  phase : ∀ y ∈ H, ∀ k ℓ e, AC.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
    PhaseOn tr.projFG H i k m c
  call : tr.projAC.CallAt p iP ℓp
  call_proposal : ℓp.call = .proposal
  payload : (AC.acProposal sp (tr.projAC.state p iP) ℓp.frame (tr.time iP)).2 = some (d, pay)
  time : tr.time iP = sp.ts s
  parent : P.parent = some d.head.root

end Setting

end Consensus.Goldilocks.Healing

end
