module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.DrainCommon
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing, HS.2: the proposal boundary

Under the settled context `Γ` of `DrainCommon`:

* The proposal's cut precedes the vote's cut (`proposal_cut_lt`): a late vote is after `t_s`,
  and an early one holds a slot-`s` block of the honest proposer, which it accepted after the
  proposer's own block call (`block_unforgeable`). So the proposer reads in the phase, and every
  honest vote it reads is before the vote.
* A1.4 (a) at the proposal duty, for an ancestor of the optimistic selection
  (`optimistic_first_proposal_anc`).

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

/-! ### The first proposal after an optimistic origin, for an ancestor (general frames) -/

section General

open AC

variable {FGP : Type} {U : Set (Blk sp.n FGP)}
  {T : GTrace sp FGP}

/-- **A1.4 (a) at the proposal duty, for an ancestor `B ⪯ D` of the optimistic selection**
(A1.4 (a) at the proposal with its hypotheses and conclusion about `B`, as
`result_transfer_anc` is for A1.8): for an honest optimistic lock of slot `σ` on `D` and
`B ⪯ D`, under (V) and (L-high) for `B`, (P) for the counted votes, and for the slot committees
`K` (P, their size, CS2 at `σ`), the head of an honest proposal of slot `σ + 1` extends `B`: the
optimistic voters of `D`, three quarters of the committee, reach the proposer, each as a
supporter of `D`, hence of `B`, or an equivocator; the proposal's voters are members. -/
theorem optimistic_first_proposal_anc {ini} (hrun : ACRun proposer T H U ini)
    (K : CommitteeDict sp.n) (hPK : CommitteeP K T H)
    (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize) {X : Fin sp.n} (hX : X ∈ H)
    {i₀ σ : Nat} {D B : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hopt : OptimisticLockAt T X i₀ σ D CV) (hBD : Anc U B D) {x : Fin sp.n} (hx : x ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksAC sp FGP)} (hc : T.CallAt x i ℓ)
    (hslot : sp.slot (T.time i) = σ + 1) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    (hprop : (acProposal sp (T.state x i) ℓ.frame (T.time i)).2 = some (d, pay))
    (hV : B ∈ ℓ.frame.tree ∧
      (B ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc B ℓ.frame.fcRoot))
    (hP : ∀ v ∈ CV, HeldAtProposal (T.state x i) ℓ.frame σ v)
    (hhigh : HighLocksCompatible U (T.state x i) (T.time i) σ B)
    (hf : 2 * (K.committee σ ∩ Hᶜ).ncard < sp.committeeSize) :
    Anc U B d.head := by
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc
  obtain ⟨ℓX, A, hpt, hslX, hsel, rfl⟩ := id hopt
  obtain ⟨-, hΦXU⟩ := frameIn_of_callAt hr hX hpt.1
  have hsel' := hsel
  unfold optimisticSelect at hsel'
  dsimp only at hsel'
  split_ifs at hsel' with hcond
  obtain ⟨-, h34, -⟩ := (deepest_mem hsel').1
  rw [hslX] at h34
  set V := View.ofLists (voteViewList (T.state x i) ℓ.frame σ ⊤) with hV'
  set SX := optimisticVoters sp A ℓX.frame σ D
  -- every optimistic voter of `D` supports `B` at the proposal, or equivocates there
  have hcover : SX ⊆ supporters ℓ.frame V σ B ∪ equivocators V.votes := by
    rintro w ⟨v, hv, rfl, R', hR', hR'r, hDR'⟩
    have hvs := optimisticPoint_pool_slotU hr.toU hrun.vstart hX hpt hv
    by_cases heq : v.val ∈ equivocators V.votes
    · exact Or.inr heq
    left
    obtain ⟨hheld, R, hR, hRr, hbs⟩ := heldAtProposal_iff.1 (hP v ⟨hv, R', hR', hR'r, hDR'⟩)
    obtain rfl : R = R' := hU.1 (hΦU hR) (hΦXU hR') (hRr.trans hR'r.symm)
    have hheld : v ∈ (T.state x i).pool σ := hheld.resolve_right fun h =>
      heq (equivocators_mono (fun u hu => (mem_proposalView_votesU hr.toU
        hrun.vstart hx i σ ℓ.frame u).2 hu) h)
    have hRs : R.slot ≤ σ := by
      have := frame_slot_leU sp hr.toU hX hpt.1 R hR'
      omega
    exact proposal_supporterU hr.toU hrun.vstart hx hc hvs hheld hR hRr hRs
      (anc_tree_of_anc_U hU hΦ hΦU hV.1 (hBD.trans (Anc.mono hΦXU hDR')) hR) hbs heq
  -- counting: the equivocators are faulty, the other voters are outside `SX`
  have hSXK : SX ⊆ K.committee σ := by
    rintro _ ⟨v, hv, rfl, -⟩
    exact hPK.2 X hX i₀ ℓX A hpt σ v hv
  have hVK : voters V.votes ⊆ K.committee σ := by
    rintro _ ⟨v, hv, rfl⟩
    exact hPK.1 x hx i σ v ((mem_proposalView_votesU hr.toU hrun.vstart hx i σ ℓ.frame v).1 hv)
  have hE : (equivocators V.votes).ncard ≤ (K.committee σ ∩ Hᶜ).ncard := by
    refine Set.ncard_le_ncard fun w hw => ⟨?_, fun hwH =>
      honest_not_equivocator_proposalU hrun.toU hx i σ ℓ.frame hwH hw⟩
    obtain ⟨a, ha, -, -, -, haw, -⟩ := hw
    exact hVK ⟨a, ha, haw⟩
  have hO : (voters V.votes \ SX).ncard + SX.ncard ≤ sp.committeeSize := by
    have := Set.ncard_le_ncard
      (Set.union_subset ((Set.sdiff_subset (t := SX)).trans hVK) hSXK)
    rwa [Set.ncard_union_eq Set.disjoint_sdiff_left, hsize σ] at this
  have h3 : (equivocators V.votes).ncard + (voters V.votes \ SX).ncard < SX.ncard := by omega
  refine proposal_walk hr hx hc hslot hprop hV.2
    (unlocked_compatible hU hΦ hΦU hV.1 (Or.inl ⟨SX, fun w hw => ?_, by omega⟩)
      (fun l hl hlive hlσ X hX hXr =>
        highLocksCompatible_iff.1 hhigh l hl hlive (by exact_mod_cast hlσ) X hX hXr)
      (locksWF_state hr hrun.vstart hx i))
    fun X' Cx hCx hp hCxB => isBest_of_cover hΦ (ofLists_support_subset _ _ _ _)
      (fun _ h => h.1) hcover (cover_sdiff_lt h3) hCx hp hCxB
  rcases hcover hw with ⟨-, v, hv, hvw, hvs, hva⟩ | h
  · exact Or.inr ⟨v, hv, hvw, hvs, hva⟩
  · exact Or.inl h

end General

/-! ### The proposal after a clean origin -/

/-! ### HS.2 (3) at the proposal boundary -/

end Consensus.Goldilocks.Healing

end
