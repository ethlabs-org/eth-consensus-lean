module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Node
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Key
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameWindowCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.RiseWindow

public section

/-! # Shadow P-U windows

The maximum height and top status are fixed at every honest cut. Justification is fixed
only in top windows. The sequential pigeonhole is the existing frame-independent theorem;
the key-to-frame-data step uses the shadow key instead of the merged stock key.
-/

namespace Consensus.Goldilocks.Healing

variable {P : Params} {A : NodeAC P}

/-- F-independent P-U frame data at the honest cuts of a finite interval.
For a constant honest set use `H := fun _ => H₀`. -/
structure FrameWindow' (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (lo hi : Time) (M : Nat) (isTop : Prop) (J : A.Blk) : Prop where
  M_eq : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i ≤ hi →
    (tr.state y i).fg.hmax = M
  top_iff : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i ≤ hi →
    ((tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ↔ isTop)
  root_eq : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i ≤ hi → isTop →
    (tr.state y i).fg.J = J

/-- Restricting the interval changes none of the pinned data. -/
theorem FrameWindow'.mono {tr : RunTrace A} {H : Time → Set (Fin P.n)}
    {lo hi lo' hi' : Time} {M : Nat} {isTop : Prop} {J : A.Blk}
    (h : FrameWindow' tr H lo hi M isTop J) (hl : lo ≤ lo') (hh : hi' ≤ hi) :
    FrameWindow' tr H lo' hi' M isTop J :=
  ⟨fun y i hy hi₁ hi₂ => h.M_eq y i hy (hl.trans hi₁) (hi₂.trans hh),
    fun y i hy hi₁ hi₂ => h.top_iff y i hy (hl.trans hi₁) (hi₂.trans hh),
    fun y i hy hi₁ hi₂ => h.root_eq y i hy (hl.trans hi₁) (hi₂.trans hh)⟩

open Classical in
/-- The two numerical window fields determine the shadow key. -/
theorem FrameWindow'.key_eq {tr : RunTrace A} {H : Time → Set (Fin P.n)}
    {lo hi : Time} {M : Nat} {isTop : Prop} {J : A.Blk}
    (h : FrameWindow' tr H lo hi M isTop J) {y : Fin P.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) (hl : lo ≤ tr.time i) (hh : tr.time i ≤ hi) :
    frameKey'' (tr.state y i).fg = 2 * M + if isTop then 1 else 0 := by
  classical
  rw [frameKey''_def, h.M_eq y i hy hl hh]
  have ht := h.top_iff y i hy hl hh
  rw [h.M_eq y i hy hl hh] at ht
  simp only [ht]

/-- Constant shadow keys give constant `(M, isTop)`; top justification agreement supplies J.
This is the P-U replacement of `frameData_of_frameKey'_eq`. -/
theorem frameData_of_frameKey''_eq {α : Type*} (mem : α → Nat → Prop)
    (time : Nat → Time) (st : α → Nat → Store P A.Payload) (dflt : A.Blk)
    {lo hi : Time}
    (hK : ∀ y z i m, mem y i → mem z m → lo ≤ time i → time i ≤ hi → lo ≤ time m →
      time m ≤ hi → frameKey'' (st y i) = frameKey'' (st z m))
    (hJ : ∀ y z i m, mem y i → mem z m → lo ≤ time i → time i ≤ hi → lo ≤ time m →
      time m ≤ hi → (st y i).hj = (st z m).hj → (st y i).J = (st z m).J) :
    ∃ M isTop J,
      (∀ y i, mem y i → lo ≤ time i → time i ≤ hi → (st y i).hmax = M) ∧
      (∀ y i, mem y i → lo ≤ time i → time i ≤ hi →
        ((st y i).hmax = (st y i).hj + 1 ↔ isTop)) ∧
      (∀ y i, mem y i → lo ≤ time i → time i ≤ hi → isTop → (st y i).J = J) := by
  classical
  by_cases hex : ∃ y i, mem y i ∧ lo ≤ time i ∧ time i ≤ hi
  · obtain ⟨y₀, i₀, hy₀, h₁, h₂⟩ := hex
    have heq := fun y i hy hl hh =>
      frameKey''_eq_iff.mp (hK y y₀ i i₀ hy hy₀ hl hh h₁ h₂)
    refine ⟨_, _, (st y₀ i₀).J, fun y i hy hl hh => (heq y i hy hl hh).1,
      fun y i hy hl hh => (heq y i hy hl hh).2, fun y i hy hl hh ht => ?_⟩
    have h := heq y i hy hl hh
    have ht' := h.2.mpr ht
    apply hJ y y₀ i i₀ hy hy₀ hl hh h₁ h₂
    omega
  · push Not at hex
    exact ⟨0, True, dflt, fun y i hy hl hh => absurd hh (not_le.mpr (hex y i hy hl)),
      fun y i hy hl hh => absurd hh (not_le.mpr (hex y i hy hl)),
      fun y i hy hl hh => absurd hh (not_le.mpr (hex y i hy hl))⟩

/-- Four attempts suffice once the run supplies height range, shadow-key lag and J agreement.
The run-level service supplier must discharge these premises on shadow executions. -/
theorem exists_frameWindow'_seq_of_mem {tr : RunTrace A} {H : Time → Set (Fin P.n)}
    {lo lam T : Time} {hz : Nat} (len : Nat → Time)
    (hlen : ∀ v, 0 ≤ len v) (hlam : 0 ≤ lam)
    (hrange : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i < T →
      hz ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ hz + 1)
    (hlag : ∀ x z i k, x ∈ H (tr.time i) → z ∈ H (tr.time k) →
      lo ≤ tr.time i → tr.time i < T → tr.time i + lam ≤ tr.time k → tr.time k < T →
      frameKey'' (tr.state x i).fg ≤ frameKey'' (tr.state z k).fg)
    (hJ : ∀ y z i m, y ∈ H (tr.time i) → z ∈ H (tr.time m) → lo ≤ tr.time i →
      tr.time i < T → lo ≤ tr.time m → tr.time m < T →
      (tr.state y i).fg.hj = (tr.state z m).fg.hj →
      (tr.state y i).fg.J = (tr.state z m).fg.J)
    (hT : lo + ∑ j ∈ Finset.range 4, (len (2 * hz + j) + lam) < T) :
    ∃ v, 2 * hz ≤ v ∧ v ≤ 2 * hz + 3 ∧ ∃ a, lo + lam ≤ a ∧
      a + len v ≤ lo + ∑ j ∈ Finset.range (v - 2 * hz + 1), (len (2 * hz + j) + lam) ∧
      (∀ y i, y ∈ H (tr.time i) → a ≤ tr.time i → tr.time i ≤ a + len v →
        frameKey'' (tr.state y i).fg = v) ∧
      ∃ M isTop J, FrameWindow' tr H a (a + len v) M isTop J := by
  obtain ⟨v, hv₁, hv₂, a, ha, hb, hK⟩ := exists_const_window_seq_of_mem
    (fun y i => y ∈ H (tr.time i)) tr.time (fun y i => frameKey'' (tr.state y i).fg)
    (2 * hz) 3 len hlen hlam
    (fun y i hy hl hh => frameKey''_bounds (hrange y i hy hl hh).1
      (hrange y i hy hl hh).2) hlag hT
  have hpart : (∑ j ∈ Finset.range (v - 2 * hz + 1), (len (2 * hz + j) + lam)) ≤
      ∑ j ∈ Finset.range 4, (len (2 * hz + j) + lam) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun j _ _ => add_nonneg (hlen _) hlam)
  have hend : a + len v < T := lt_of_le_of_lt (hb.trans (add_le_add_right hpart lo)) hT
  obtain ⟨M, isTop, J, hM, ht, hj⟩ := frameData_of_frameKey''_eq
    (fun y i => y ∈ H (tr.time i)) tr.time (fun y i => (tr.state y i).fg)
    (P.genesisBlock A.genesisPayload)
    (fun y z i m hy hz hi₁ hi₂ hm₁ hm₂ =>
      (hK y i hy hi₁ hi₂).trans (hK z m hz hm₁ hm₂).symm)
    (fun y z i m hy hz hi₁ hi₂ hm₁ hm₂ => hJ y z i m hy hz
      ((le_add_of_nonneg_right hlam).trans (ha.trans hi₁)) (hi₂.trans_lt hend)
      ((le_add_of_nonneg_right hlam).trans (ha.trans hm₁)) (hm₂.trans_lt hend))
  exact ⟨v, hv₁, hv₂, a, ha, hb, hK, M, isTop, J, hM, ht, hj⟩

/-- The P-U floor, unlike the stock contest floor, is always `hmax - 1`. -/
theorem le_pred_add_riseRounds (st : Store P A.Payload) {hz : Nat}
    (hpos : 1 ≤ st.hmax) (hv : 2 * hz ≤ frameKey'' st) :
    hz + 1 ≤ st.hmax - 1 + riseRounds hz (frameKey'' st) := by
  classical
  rw [riseRounds_eq, frameKey''_def] at *
  split_ifs at * <;> omega

end Consensus.Goldilocks.Healing

end
