module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.DrainCommon
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Carry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ResultAnc
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing, HS.2: the proposal boundary

Under the settled context `Γ` of `DrainCommon`:

* The proposal's cut precedes the vote's cut (`proposal_cut_lt`): a late vote is after `t_s`,
  and an early one holds a slot-`s` block of the honest proposer, which it accepted after the
  proposer's own block call (`block_unforgeable`). So the proposer reads in the phase, and every
  honest vote it reads is before the vote.

The proposal boundary itself (the honest proposal follows a clean origin) is removed with HS.4 and
HR.3 (retired, owner decision). -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n} {g ΔF w : Time}
  {i₀ m : Nat}
  {ini : Fin sp.n → (goldilocksNode sp).State}
  {c : PhaseCase (AC.Blk sp.n (List (FG.Att sp.n)))}

/-! ### The proposal precedes the votes of its slot -/

/-- **The proposal's cut precedes every honest holder of a slot-`s` block of its proposer**: the
holder accepted the block after its proposer's own block call (unforgeable blocks), which is the
cut after the `ac_proposal` cut (one tick per node and time). -/
private theorem proposal_before_holder (hrun : GoldilocksRun proposer dg H tr ini) {p : Fin sp.n}
    (hpH : p ∈ H) {kP s : Nat} {ℓp : ACLabel (goldilocksNode sp)}
    (hcP : tr.projAC.CallAt p kP ℓp) (hcall : ℓp.call = .proposal)
    (htP : tr.time kP = sp.ts s) (hs1 : 1 ≤ s) {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPs : P.slot = s) (hPprop : P.proposer = p) {z : Fin sp.n} (hz : z ∈ H) {k : Nat}
    (hPz : P ∈ (tr.state z k).fg.tree) : kP < k := by
  have hl := hrun.toLocalRun
  rcases Compose.tree_cases hl hz hPz with hg | ⟨a, hak, ha⟩
  · have := congrArg (·.slot) hg
    simp only [Params.genesisBlock] at this
    omega
  obtain ⟨j', hj'a, hown⟩ := hl.block_unforgeable z hz a P ⟨true, ha⟩ (hPprop ▸ hpH)
  rw [hPprop] at hown
  obtain ⟨⟨acc, hc⟩, hpos⟩ := hown
  rcases Compose.blockCall_cases hl hpH hc with hg |
    ⟨j'', x, fgDue, rfl, hg, hpr, d', pay', -, hB, -, -, -, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  obtain ⟨j₀, rfl, h₀⟩ := proposal_call_tick hl hpH (Compose.projAC_callAt.1 hcP) hcall
  have hslot : P.slot = sp.toParams.slotOf (tr.time (j'' + 2)) := by rw [hB]; rfl
  have ht : tr.time (j'' + 2) = tr.time (j₀ + 1) := by
    rw [htP, hpr.2.1, ← hslot, hPs, sp.slotTime_eq]; rfl
  have := hl.tick_unique p hpH j₀ j'' _ h₀ (by rw [← ht]; exact ⟨x, fgDue, hg⟩)
  omega

/-- **The proposal's cut precedes every honest vote of its slot**: a vote after `t_s` is at a
later cut; an early vote holds a slot-`s` block (`cast_readyU`), of the slot's proposer
(`HonestObjects.proposer`), so it is after the proposal (`proposal_before_holder`). -/
theorem proposal_cut_lt (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {kP s : Nat} {ℓp : ACLabel (goldilocksNode sp)}
    (hpH : proposer s ∈ H) (hcP : tr.projAC.CallAt (proposer s) kP ℓp)
    (hcall : ℓp.call = .proposal) (htP : tr.time kP = sp.ts s) (hs1 : 1 ≤ s) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hv : AC.CastAt tr.projAC y k ℓ e)
    (he : e.msg.slot = s) : kP < k := by
  have hl := hrun.toLocalRun
  have hac := Compose.goldilocks_ac_projection_from hrun hnc
  have hr := hac.localRun
  have hU := Compose.honest_blocks_coherent hl hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  by_cases hearly : tr.time k < sp.ts s + sp.Δ
  · obtain ⟨⟨P', hP', hP's, -⟩, -⟩ := AC.cast_readyU hr.toU hy hv (by rw [he]; exact hearly)
    rw [he] at hP's
    have hfU := (AC.frameIn_of_callAt hr hy hv.1).2
    have hroot : P'.root ≠ sp.genesisRoot := by
      intro hg
      have hG := Store.genesis_mem (Compose.fg_reachable hl hy k)
      obtain rfl := hU.1 (hfU hP') ⟨y, hy, k, hG⟩ hg
      simp [Params.genesisBlock] at hP's
      omega
    have hprop := hac.honest.proposer P' ⟨y, hy, k, ℓ, hv.1, hP'⟩ hroot
    exact proposal_before_holder hrun hpH hcP hcall htP hs1 hP's (by rw [hprop, hP's]) hy
      (mem_tree_of_frame hrun hy hv.1 hP')
  · by_contra hn
    have := hl.time_mono (not_lt.1 hn)
    linarith only [htP, hΔ, hearly, this]

end Consensus.Goldilocks.Healing

end
