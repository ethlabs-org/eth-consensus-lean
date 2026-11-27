module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Node
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Key
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Cache
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

/-- A P-U viable held block is above finality. In the predecessor-height top case use
`F ⪯ J ⪯ Q`; all other cases are strictly above `hj` and use the existing G1.2 proof. -/
theorem finalized_below_viable' {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hR : st.Reachable' acp₀) {U : Set (NodeBlock P ACP)} (hU : Coherent U)
    (hsub : st.tree ⊆ U) {V : Set (Fin P.n)}
    (hV : Vᶜ.ncard < 2 * P.fg.q - P.n)
    (hsafe : ∀ a b, (∃ Y ∈ st.tree, a ∈ Y.fgPayload) →
      (∃ Y ∈ st.tree, b ∈ Y.fgPayload) → a.val ∈ V → ¬ FG.slashable a b)
    {Q : NodeBlock P ACP} (hQ : Q ∈ st.tree) (hv : st.IsViable' Q) : st.Anc st.F Q := by
  have hj := Store.hj_lt_hmax_of_reachable_with Store.finalitySpec_updateFinality'
    hR.reachableWith
  rcases (Store.isViable'_iff st Q).mp hv with hh | ⟨hh, hgap | hJ⟩
  · exact Store.F_anc_of_hj_lt_of_safe_with Store.finalitySpec_updateFinality'
      hR.reachableWith hR.reachableWith hU hsub hsub hV hsafe hQ (by omega)
  · exact Store.F_anc_of_hj_lt_of_safe_with Store.finalitySpec_updateFinality'
      hR.reachableWith hR.reachableWith hU hsub hsub hV hsafe hQ (by omega)
  · exact (Store.cache_invariants' hR).2.2.1.trans hJ

/-- Viability transport within fixed numerical frame data. The caller separately supplies
finalized ancestry at the receiving cut, using `finalized_below_viable'`. -/
theorem isViable'_of_window_data {ACP : Type} {a b : Store P ACP} {Q : NodeBlock P ACP}
    (hm : a.hmax = b.hmax) (ht : (a.hmax = a.hj + 1) ↔ (b.hmax = b.hj + 1))
    (hJ : a.hmax = a.hj + 1 → a.J = b.J) (hb : b.hj < b.hmax)
    (hσ : a.σ Q.root = b.σ Q.root)
    (hanc : a.Anc a.J Q → b.Anc a.J Q) (hv : a.IsViable' Q) : b.IsViable' Q := by
  rw [Store.isViable'_iff] at hv ⊢
  rcases hv with hh | ⟨hh, hgap | hAQ⟩
  · exact Or.inl (by rw [← hm, ← hσ]; exact hh)
  · refine Or.inr ⟨by rw [← hm, ← hσ]; exact hh, Or.inl ?_⟩
    have hnot : ¬ b.hmax = b.hj + 1 := fun h => by
      have := ht.mpr h
      omega
    omega
  · refine Or.inr ⟨by rw [← hm, ← hσ]; exact hh, ?_⟩
    by_cases htop : a.hmax = a.hj + 1
    · exact Or.inr (hJ htop ▸ hanc hAQ)
    · exact Or.inl (by have := ht.not.mp htop; omega)

/-- The shadow key lag needs only the maximum-height and J carriers. The stock contest
witness is unnecessary: contest and clean top frames have the same shadow key. -/
theorem frameKey''_le_of_relay {ACP : Type} {acp₀ : ACP} {stx stz : Store P ACP}
    (hRx : stx.Reachable' acp₀) (hRz : stz.Reachable' acp₀)
    {U : Set (NodeBlock P ACP)} (hU : Coherent U)
    (hsubx : stx.tree ⊆ U) (hsubz : stz.tree ⊆ U) {V : Set (Fin P.n)}
    (hV : Vᶜ.ncard < 2 * P.fg.q - P.n)
    (hsafe : ∀ a b, (∃ Y ∈ stz.tree, a ∈ Y.fgPayload) →
      (∃ Y ∈ stx.tree, b ∈ Y.fgPayload) → a.val ∈ V → ¬ FG.slashable a b)
    (hjmax : ∀ B ∈ stz.tree, ∀ X ∈ stz.tree, (stz.σ B.root).J = X.root →
      stz.Anc stz.F X → (stz.σ B.root).hj ≤ stz.hj)
    (hancz : ∀ A C, Anc U A C → C ∈ stz.tree → stz.Anc A C)
    (hheld : ∀ B ∈ stx.tree, stz.hmax ≤ (stx.σ B.root).h → B ∈ stz.tree) :
    frameKey'' stx ≤ frameKey'' stz := by
  classical
  have hu := Store.finalitySpec_updateFinality' (P := P) (ACP := ACP)
  have hrx := hRx.reachableWith
  have hrz := hRz.reachableWith
  obtain ⟨-, hJx, -, ⟨Bj, hBj, hBjJ, hBjhj⟩, -, ⟨Bh, hBh, hBhh⟩, -⟩ :=
    Store.cache_invariants' hRx
  obtain ⟨-, -, -, -, hgez, -, -⟩ := Store.cache_invariants' hRz
  by_cases hlt : stx.hmax < stz.hmax
  · rw [frameKey''_def, frameKey''_def]
    split_ifs <;> omega
  have hle : stz.hmax ≤ stx.hmax := not_lt.mp hlt
  have hheld' : ∀ {B : NodeBlock P ACP}, B ∈ stx.tree → stx.hmax ≤ (stx.σ B.root).h →
      B ∈ stz.tree := fun hB hh => hheld _ hB (hle.trans hh)
  have hσ : ∀ {B : NodeBlock P ACP}, B ∈ stz.tree → B ∈ stx.tree →
      stz.σ B.root = stx.σ B.root :=
    fun hBz hBx => Store.σ_eq_of_mem_with hrz hu hrx hU.1 hsubz hsubx hBz hBx
  have hBhz := hheld' hBh hBhh.ge
  have heq : stz.hmax = stx.hmax := by
    have := hgez Bh hBhz
    rw [hσ hBhz hBh] at this
    omega
  have hjz := Store.hj_lt_hmax_of_reachable_with hu hrz
  have htop : stx.hmax = stx.hj + 1 → stz.hmax = stz.hj + 1 := by
    intro htx
    have hBjh := Store.hj_lt_h_with hu hrx hBj
    have hBjz := hheld' hBj (by omega)
    obtain ⟨E, hE, hEr, hEB, -⟩ := Store.J_entry_with hu hrx hBj
    obtain rfl : E = stx.J := hU.1 (hsubx hE) (hsubx hJx) (hEr.trans hBjJ)
    have hJz : stx.J ∈ stz.tree := mem_of_anc (hancz _ _ (hEB.mono hsubx) hBjz) hBjz
    have hJh := Store.J_height_le_with hu hrx hBj hJx hBjJ.symm
    by_contra hn
    have hzlt : stz.hj < stx.hj := by omega
    have hFJ := hancz _ _ ((Store.F_anc_of_hj_lt_of_safe_with hu hrz hrx hU hsubz hsubx
      hV hsafe hJx (by rw [hBjhj] at hJh; omega)).mono hsubx) hJz
    have hσj := hσ hBjz hBj
    have := hjmax Bj hBjz _ hJz (by rw [hσj, hBjJ]) hFJ
    rw [hσj] at this
    omega
  rw [frameKey''_def, frameKey''_def]
  split_ifs <;> omega

end Consensus.Goldilocks.Healing

end
