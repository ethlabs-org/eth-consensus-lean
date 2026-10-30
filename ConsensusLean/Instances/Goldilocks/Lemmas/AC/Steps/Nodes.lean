module
public import ConsensusLean.Instances.Goldilocks.Statements.AC.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Count
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry

public section

/-! # Goldilocks SA: the step lemmas (A1.1–A1.5, A1.8, A1.9)

The per-vote transfer lemmas over SA traces. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- **A1.1.** -/
theorem proposer_voters_agree : ProposerVotersAgree sp := by
  sorry

/-- **A1.2.** -/
theorem first_transfer : FirstTransfer sp := by
  sorry

/-- **A1.3.** -/
theorem next_transfer : NextTransfer sp := by
  sorry

/-- **A1.4 (a).** -/
theorem optimistic_transfer : OptimisticTransfer sp := by
  sorry

/-- **A1.4 (b).** -/
theorem optimistic_next_update : OptimisticNextUpdate sp := by
  sorry

/-- A block that `ac_to_fg` returns is a candidate. -/
private theorem mem_toFGCandidates {FGP : Type} {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {C : Blk sp.n FGP} (h : (acToFG sp A Φ t).2.1 = some C) : C ∈ toFGCandidates sp A Φ t := by
  unfold acToFG at h
  dsimp only at h
  split_ifs at h
  split at h
  · cases h
  · rename_i C' hC'
    split_ifs at h
    cases h
    exact (deepest_mem hC').1

/-- **A1.5.** -/
theorem source_age : SourceAge sp := by
  intro FGP ro H U tr hrun τ x i ℓ C hx hto hslot
  obtain ⟨hc, -, hC⟩ := hto
  obtain ⟨hCv, l, hl, hlb, hlf, hls⟩ := mem_toFGCandidates sp hC
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := hl
  obtain ⟨j, hj, B', CV', hfl, L, hL, hLr, hLB'⟩ :=
    fast_lock_provenance hrun.localRun hx i l₀ hl₀ hlf
  have hU := hrun.localRun.coherent
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
    rcases hrun.localRun.frameLaw x hx i ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
      exact h.1
  refine ⟨j, hj.le, l₀.slot, B', CV', hfl, ?_, hls, ?_⟩
  · -- the lock was written in a slot after `τ`'s
    have h1 : sp.slot τ + 1 ≤ l₀.slot := by simp only at hls; omega
    have hτ : τ < sp.ts (l₀.slot : Int) := by
      rcases le_or_gt 0 τ with h0 | h0
      · refine lt_of_lt_of_le (not_le.1 fun h => ?_)
          ((ts_le_iff sp (a := (sp.slot τ : Int) + 1) (b := l₀.slot)).2 (by omega))
        have := ((ts_le_iff_le_slot sp h0) _).1 h
        omega
      · refine lt_of_lt_of_le h0 ?_
        simp only [SAParams.ts]
        have := sp.toParams.hΔ
        positivity
    rcases hfl with ⟨ℓ', C', ⟨-, -, ht, -⟩, -⟩ | ⟨ℓ', A', -, hs, -⟩
    · rw [ht]
      have := sp.toParams.hΔ
      linarith
    · refine lt_of_lt_of_le hτ ?_
      rw [← hs]
      exact ((ts_le_iff_le_slot sp (hrun.localRun.time_nonneg j)) _).2 le_rfl
  · -- `C` is the viable ancestor of the lock's block, which is `L`
    have hCt : C ∈ ℓ.frame.tree := hCv.1
    have hva : Anc ℓ.frame.tree (ℓ.frame.viableAncestor B₀) B₀ := by
      unfold Frame.viableAncestor
      split
      · rename_i h
        exact h.choose_spec.1
      · exact Relation.ReflTransGen.refl
    have hvat : ℓ.frame.viableAncestor B₀ ∈ ℓ.frame.tree := by
      by_cases he : ℓ.frame.viableAncestor B₀ = B₀
      · rw [he]; exact hB₀
      · exact (Anc.mem hva he).1
    have hCe : C = ℓ.frame.viableAncestor B₀ := hU.1 (hΦU hCt) (hΦU hvat) hlb.symm
    have hLe : L = B₀ := hU.1 hL (hΦU hB₀) (hLr.trans hB₀r.symm)
    subst hCe hLe
    exact (Anc.mono hΦU hva).trans hLB'

/-- **A1.8.** -/
theorem result_transfer : ResultTransfer sp := by
  intro FGP ro H U tr hrun s X y i₀ i C CV ℓ e hX hres hy hc hs hcarry hviab hlocks hd
  obtain ⟨-, -, -, hhead⟩ := castAt_spec hrun.localRun hy hc
  have hU := hrun.localRun.coherent
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
    rcases hrun.localRun.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
      exact h.1
  have hσ : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  rw [hs, hσ] at hhead
  have hdomA := voterBlockTree_anc hrun.localRun hy hc
  rw [hs] at hdomA
  have hCt : C ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact mem_of_anc h hΦ.fcRoot_mem
  have hcore := anc_getHead hU hΦ hΦU e.readPoint (tr.time i)
    (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int) (fun B hB => hB.1) hdomA hviab
    (fun L hL => hlocks L hL) fun X' Cx hCx hp hCxC =>
      isBest_of_majority hΦ (merged_support_subset hrun.localRun hy hc (s + 1))
        (fun B hB => hB.1.1)
        (result_supporters hrun hX hy hres hc hs hcarry hviab hd)
        (merged_voters_subset hrun.localRun hy hc hd)
        (result_majority hres) hCx hp hCxC
  refine ⟨_, hΦU ?_, hhead.symm, Anc.mono hΦU hcore⟩
  by_cases he : C = getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame (s + 1)))
      (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int)
  · exact he ▸ hCt
  · exact (Anc.mem hcore he).2

/-- **A1.9.** -/
theorem source_compatible : SourceCompatible sp := by
  sorry

end Consensus.Goldilocks.SA

end
