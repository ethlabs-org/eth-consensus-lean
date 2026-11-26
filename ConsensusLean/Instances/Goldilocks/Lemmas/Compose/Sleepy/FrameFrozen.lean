module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Deadline
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: the frozen witness

An honest head relayed before the freeze lies in the voter block tree. `Frame` supplies the
honest-store geometry; `FrameLabels` uses this witness for viability at votes. -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Vote Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-! ### The frozen witness: an honest head relayed before the freeze -/

private theorem add_mul_delta_lt {x a b : Time} (h : a < b) : x + a * sp.Δ < x + b * sp.Δ :=
  add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_right h sp.toParams.hΔ)

private theorem optimistic_stamp (A : AC.ACState sp.n) (Φ : AC.Frm sp.n (List (FG.Att sp.n)))
    (t : Time) : (AC.optimisticConfirmation sp A Φ t).blockStamp = A.blockStamp := by
  unfold AC.optimisticConfirmation AC.updateLatestConfirmed
  split
  · rfl
  · split_ifs <;> rfl

/-- At an honest slot-`(s+1)` vote, the voter's restarts up to the vote were at or before `t_s`,
and the vote is cast from `t_{s+1} = t_s + 4Δ` on. -/
theorem honest_vote_restarts {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {s : Nat}
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) :
    (∀ c ≤ i, tr.projAC.RestartAt y c → tr.time c ≤ sp.ts s) ∧ sp.ts s + 4 * sp.Δ ≤ tr.time i := by
  have hr := (goldilocks_ac_projection_from hrun hnc).localRun
  obtain ⟨-, hslot, hjoin, -⟩ := AC.castAt_spec hr hy hc
  have hti : sp.slot (tr.projAC.time i) = s + 1 := hslot ▸ hs
  have hjp : AC.joined sp (tr.projAC.post i) (tr.projAC.time i) := by
    unfold AC.joined; rw [AC.restartTime_of_castAt hr hy hc]; exact hjoin
  refine ⟨fun c hc' hrc => ?_, ?_⟩
  · have h := (AC.joined_awakeU sp _ ro H _ tr.projAC hr.toU y hy i ℓ hc.1 hjp).2 c hc' hrc
    rw [hti, show (((s + 1 : Nat) : Int) - 1) = (s : Int) by push_cast; ring] at h
    exact h
  · have h := (AC.ts_le_iff_le_slot sp (hr.time_nonneg i) ((s : Int) + 1)).2
      (by rw [hti]; push_cast; rfl)
    have e4 : sp.ts ((s : Int) + 1) = sp.ts s + 4 * sp.Δ := by simp only [ACParams.ts]; ring
    rw [e4] at h
    exact h

/-- The emissions of `ac_on_tick` are made at `t_σ + Δ` only. -/
private theorem acOnTick_emits {self : Fin sp.n} {A : AC.ACState sp.n}
    {Φ : AC.Frm sp.n (List (FG.Att sp.n))} {t : Time} {e : AC.Em sp (List (FG.Att sp.n))}
    (he : e ∈ (AC.acOnTick sp self A Φ t).2) : t = sp.ts (sp.slot t) + sp.Δ := by
  unfold AC.acOnTick at he
  dsimp only at he
  split_ifs at he <;> first | assumption | simp at he

/-- **The calls that cast an honest vote**: a tick at `t_σ + Δ`, a block or a message; never a
restart, `ac_proposal` or `ac_to_fg`. -/
theorem honest_vote_call {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ℓ e) :
    (ℓ.call = .tick → tr.time i = sp.ts (sp.slot (tr.time i)) + sp.Δ) ∧ ℓ.call ≠ .proposal ∧
      ℓ.call ≠ .toFG ∧ ℓ.call ≠ .restart := by
  have hr := (goldilocks_ac_projection_from hrun hnc).localRun
  obtain ⟨hΦ, -⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  have hx := hr.exec i ℓ hc.1.2 (hc.1.1 ▸ hy)
  rw [hc.1.1] at hx
  have he' : e ∈ ((AC.goldilocksAC sp _ ro).step y (tr.projAC.state y i) ℓ.frame
      (tr.projAC.time i) ℓ.call).2 := by rw [hx]; exact hc.2
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [h] at he'
  · exact acOnTick_emits (self := y) (A := tr.projAC.state y i) (Φ := ℓ.frame) he'
  · simp [ACInterface.step] at he'
  · simp [ACInterface.step] at he'
  · change e ∈ (AC.acRestart sp ro y _ ℓ.frame _).2 at he'
    rw [((AC.restart_state sp) _ ro y _ ℓ.frame _ hΦ (hr.time_nonneg i)).1] at he'
    simp at he'

/-- **A block accepted before the freeze is in the voter block tree** of an honest
slot-`(s+1)` vote whose `Σ.F` it extends: it is in the voter's frame, and its stamp at the read
point is below `t_s + 3Δ` (the voter's restarts were before, and this call does not receive
it). -/
theorem accepted_voter_tree {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {s : Nat} {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) {X : AC.Blk sp.n (List (FG.Att sp.n))}
    (hXU : X ∈ tr.HonestBlocks H) (hacc : AC.AcceptedBefore tr.projAC y X (sp.ts s + 3 * sp.Δ))
    (hFX : Anc (tr.HonestBlocks H) ℓ.frame.F X) :
    X ∈ AC.voterBlockTree sp e.readPoint ℓ.frame (s + 1) := by
  have hr := (goldilocks_ac_projection_from hrun hnc).localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hΦ, -⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  obtain ⟨hrs, hti⟩ := honest_vote_restarts hrun hnc hy hc hs
  have hT : sp.ts s + 3 * sp.Δ < tr.projAC.time i := by
    change sp.ts s + 3 * sp.Δ < tr.time i
    exact (add_mul_delta_lt (by norm_num)).trans_le hti
  -- in the voter's frame
  obtain ⟨G, hGU, hGr, hGp⟩ := AC.genesis_mem_of_call sp hr hy _ _ hc.1
  have hXt : X ∈ ℓ.frame.tree := by
    rcases hacc with hg | ⟨k, hk, hkt⟩
    · obtain rfl : X = G := hU.1 hXU hGU (hg.trans hGr.symm)
      obtain h | ⟨c, -, hcp⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hFX
      · exact h ▸ hΦ.rooted.1
      · exact absurd (hcp.2.2.symm.trans hGp) (Option.some_ne_none _)
    · have hki : k ≤ i := by
        by_contra h
        have := hr.time_mono (le_of_not_ge h)
        exact lt_irrefl _ (hT.trans (this.trans_lt hkt))
      exact AC.mem_tree_of_acceptAt sp hr hy hk hki hc.1 hFX
  -- its stamp before the call is below the freeze
  have hbs := AC.blockStamp_lt_of_acceptedBefore sp hr hrun.vstart hy hc.1 hXt hacc
    (fun k hk hrk => lt_of_le_of_lt (hrs k hk hrk)
      (lt_add_of_pos_right _ (mul_pos (by norm_num) hΔ))) (Or.inl hT.le)
  -- the call does not receive `X`, so the read point keeps that stamp
  have hne : ∀ B, ℓ.call = .block B → X.root ≠ B.root := by
    intro B hcall hXB
    have hai : tr.projAC.AcceptAt y i B := ⟨ℓ, hc.1, hcall⟩
    obtain rfl : B = X := hΦ.coherent.1 ((AC.accept_new sp hr hy hai).1 ℓ hc.1) hXt hXB.symm
    rcases hacc with hg | ⟨k, hk, hkT⟩
    · exact AC.accept_ne_genesis sp hr hy hai hg
    · obtain rfl := AC.accept_unique sp hr hy hk hai
      exact absurd hkT (not_lt.2 hT.le)
  have hx := hr.exec i ℓ hc.1.2 (hc.1.1 ▸ hy)
  rw [hc.1.1] at hx
  have hnr := (honest_vote_call hrun hnc hy hc).2.2.2
  have hrp : e.readPoint.blockStamp X.root = (tr.projAC.state y i).blockStamp X.root := by
    have h1 : (tr.projAC.post i).blockStamp = e.readPoint.blockStamp := by
      rw [AC.post_of_castAtU hr.toU hy hc, optimistic_stamp, AC.admitVote_blockStamp]
    have hp : tr.projAC.post i = ((AC.goldilocksAC sp _ ro).step y (tr.projAC.state y i)
        ℓ.frame (tr.projAC.time i) ℓ.call).1 := by rw [hx]
    obtain ⟨hblk, -, hoth⟩ :=
      AC.step_blockStamp_eq ro y (tr.projAC.state y i) hΦ (hr.time_nonneg i) ℓ.call
    rw [← h1, hp]
    by_cases hb : ∃ B, ℓ.call = .block B
    · obtain ⟨B, hB⟩ := hb
      rw [hblk B hB, Function.update_of_ne (hne B hB)]
    · rw [hoth (fun B h => hb ⟨B, h⟩) hnr]
  have hfz : AC.freeze sp (s + 1) = sp.ts s + 3 * sp.Δ := by simp [AC.freeze]
  exact ⟨hXt, Or.inl (by rw [hrp, hfz]; exact hbs)⟩

end Consensus.Goldilocks.Compose

end
