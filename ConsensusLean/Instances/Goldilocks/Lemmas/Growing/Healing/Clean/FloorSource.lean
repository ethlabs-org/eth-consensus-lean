module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LeftEntry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot

public section

/-! # A high floor has a signed source below a bounded row label, under growing faults

The growing form of `high_floor_signed_source_of_row_bound` (`Healing/Retention/Boot`): the
reader is honest at an observation `t ≤ b` after its state's cuts, and every origin is honest at
its own write. Pairwise comparison of the earlier origins rules out a high contest at the reader:
the two entries that a contest leaves at `h_j` are each below an earlier origin
(`left_entry_origin_at`), the two origins are below a block held by one of their writers, and two
entries of one height below a held block are one. So the floor is `h_max − 1`; the entry at the
floor below the reader's highest block is left by a signer honest at `t`, from an earlier origin
`O` (`left_entry_origin_at`), and comparison with `B` orients `B ⪯ O`, since `O ⪯ B` would put the
floor entry below `B`, at a height `≤ h(B)` below the floor. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- **A high floor has a signed source below a bounded row label**: for a reader honest at
`t ≤ b`, a high origin under the reader's head-height floor yields a high origin, of a label
below `u`, above an entry at or past the floor, signed by the origin's writer after the write. -/
theorem high_floor_signed_source_of_row_bound_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {i j k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {u : Nat}
    (hrow : ∀ W ∈ (tr.state y k).fg.tree, ∀ att ∈ W.fgPayload,
      ∀ v d, v ∈ H (tr.time d) → tr.SignAt v d att → d < k → ∀ r l O,
        r < d → HighOrigin tr H g v r l O → l < u)
    (hpair : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      ∀ v' r' l' O', r' < k → HighOrigin tr H g v' r' l' O' →
      Compatible (tr.HonestBlocksAt H) O O')
    (hcomp : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocksAt H) B O)
    (hfloor : ((tr.state x i).fg.σ B.root).h < (tr.state y k).fg.headHeightFloor) :
    ∃ v r l O E, r < k ∧ HighOrigin tr H g v r l O ∧ l < u ∧
      E ∈ (tr.state y k).fg.tree ∧ Anc (tr.HonestBlocksAt H) E O ∧
      Anc (tr.HonestBlocksAt H) B O ∧
      (tr.state y k).fg.headHeightFloor ≤ ((tr.state y k).fg.σ E.root).h ∧
      ∃ d att, r < d ∧ d < k ∧ v ∈ H (tr.time d) ∧ tr.SignAt v d att ∧ att.T = E.root := by
  have hrun := hp.run
  have hnc0 := hp.noColl
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc0
  have hreach := fg_reachable_at hrun ht hle hy
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun X hX => ⟨y, k, t, ht, hle, hy, hX⟩
  have hBx := Outcome.high_origin_mem_at hrun hnc0 ho
  have hcut : ∀ q, ∀ p < q, tr.time p ≤ tr.time q := fun _ _ hp' => hrun.time_mono hp'.le
  -- two earlier origins are below a block held by one of their writers, at its write
  have hupper : ∀ {v₁ v₂ : Fin sp.n} {r₁ l₁ r₂ l₂ : Nat}
      {O₁ O₂ : SA.Blk sp.n (List (FG.Att sp.n))}, HighOrigin tr H g v₁ r₁ l₁ O₁ → r₁ < k →
      HighOrigin tr H g v₂ r₂ l₂ O₂ → r₂ < k → ∃ z m C, z ∈ H (tr.time m) ∧
        C ∈ (tr.state z m).fg.tree ∧
        Anc (tr.HonestBlocksAt H) O₁ C ∧ Anc (tr.HonestBlocksAt H) O₂ C := by
    intro v₁ v₂ r₁ l₁ r₂ l₂ O₁ O₂ ho₁ hr₁ ho₂ hr₂
    have hO₁ := Outcome.high_origin_mem_at hrun hnc0 ho₁
    have hO₂ := Outcome.high_origin_mem_at hrun hnc0 ho₂
    rcases hpair v₁ r₁ l₁ O₁ hr₁ ho₁ v₂ r₂ l₂ O₂ hr₂ ho₂ with h | h
    · exact ⟨v₂, r₂, O₂, ho₂.1, hO₂, h, .refl⟩
    · exact ⟨v₁, r₁, O₁, ho₁.1, hO₁, .refl, h⟩
  have hnc : ¬ ((tr.state y k).fg.Contest ∧ HZ tr H g + 2 ≤ (tr.state y k).fg.hmax) := by
    rintro ⟨⟨hmj, C, hC, -, hCh, hJC⟩, hmax⟩
    obtain ⟨-, hJm, -, ⟨Bj, hBj, hBjJ, hBjhj⟩, -⟩ :=
      Goldilocks.Store.cache_invariants _ _ _ _ hreach
    obtain ⟨EJ, hEJ, hEJr, hEJB, hcase⟩ := Store.J_entry_of_reachable hreach hBj
    obtain rfl : EJ = (tr.state y k).fg.J := hU.1 (hsub hEJ) (hsub hJm) (hEJr.trans hBjJ)
    rcases hcase with hg | ⟨hJh, hJT⟩
    · exact hJC (hg ▸ (Goldilocks.Store.accepted_tree _ _ _ _ hreach).2.2.2 C hC)
    have hJlt := Store.hj_lt_h hreach hBj
    obtain ⟨W₂, -, att₂, -, v₂, d₂, -, hd₂, -, -, r₂, hr₂, l₂, O₂, ho₂, hJO⟩ :=
      hp.left_entry_origin_at ht hle hy htb hJm hJT
        (by clear * - hmax hmj hBjhj hJh; omega) hEJB (by clear * - hJh hJlt; omega)
    obtain ⟨EC, hEC, hECC, hECh, hECT⟩ :=
      entry_at_height hreach hC (h := (tr.state y k).fg.hj) (by clear * - hmax hmj; omega) (by
          clear * - hmj hCh; omega)
    obtain ⟨W₁, -, att₁, -, v₁, d₁, -, hd₁, -, -, r₁, hr₁, l₁, O₁, ho₁, hECO⟩ :=
      hp.left_entry_origin_at ht hle hy htb hEC hECT (by clear * - hmax hmj hECh; omega) hECC
        (by clear * - hmj hCh hECh; omega)
    obtain ⟨z, m', C', hz, hC', hO₁C, hO₂C⟩ := hupper ho₁ (by clear * - hd₁ hr₁; omega) ho₂ (by
        clear * - hd₂ hr₂; omega)
    have hm0 := hrun.time_nonneg m'
    have h₁ := hECO.trans hO₁C
    have h₂ := hJO.trans hO₂C
    have hEC' := mem_of_honest_anc_at hrun hnc0 hm0 (hcut m') hz h₁ hC'
    have hJ' := mem_of_honest_anc_at hrun hnc0 hm0 (hcut m') hz h₂ hC'
    have hσ₁ := σ_eq_honest_at hrun hnc0 ht hle hy hm0 (hcut m') hz hEC hEC'
    have hσ₂ := σ_eq_honest_at hrun hnc0 ht hle hy hm0 (hcut m') hz hJm hJ'
    have hrz := fg_reachable_at hrun hm0 (hcut m') hz
    -- two entries of one height below a held block are one
    have he : EC.root = (tr.state y k).fg.J.root := by
      have hh : ((tr.state z m').fg.σ EC.root).h =
          ((tr.state z m').fg.σ (tr.state y k).fg.J.root).h := by
        rw [← hσ₁, ← hσ₂, hECh, hJh, hBjhj]
      have hT₁ : ((tr.state z m').fg.σ EC.root).Th = EC.root := by rw [← hσ₁]; exact hECT
      have hT₂ : ((tr.state z m').fg.σ (tr.state y k).fg.J.root).Th =
          (tr.state y k).fg.J.root := by rw [← hσ₂]; exact hJT
      rcases SA.anc_total hU h₁ h₂ with h | h
      · have := Th_eq_of_anc hrz (store_anc_of_honest_anc_at hrun hnc0 hm0 (hcut m') hz h hJ')
          hh.symm
        rw [← hT₁, ← hT₂, this]
      · have := Th_eq_of_anc hrz (store_anc_of_honest_anc_at hrun hnc0 hm0 (hcut m') hz h hEC')
          hh
        rw [← hT₁, ← hT₂, this]
    obtain rfl : EC = (tr.state y k).fg.J := hU.1 (hsub hEC) (hsub hJm) he
    exact hJC hECC
  have hcon : ¬ (tr.state y k).fg.Contest := fun hcon => by
    unfold Store.headHeightFloor at hfloor
    simp only [hcon, ↓reduceIte] at hfloor
    exact hnc ⟨hcon, by have := ho.2.2.2; omega⟩
  have hfl : (tr.state y k).fg.headHeightFloor = (tr.state y k).fg.hmax - 1 := by
    unfold Store.headHeightFloor
    simp only [hcon, ↓reduceIte]
  rw [hfl] at hfloor
  have hBh := ho.2.2.2
  obtain ⟨-, -, -, -, -, ⟨C, hC, hCh⟩, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hreach
  obtain ⟨E, hE, hEC, hEh, hET⟩ :=
    entry_at_height hreach hC (h := (tr.state y k).fg.hmax - 1) (by clear * - hfloor; omega) (by
        clear * - hCh; omega)
  obtain ⟨W, hW, att, ha, v, d₁, hv, hd₁, hsd, haT, r, hrd, l, O, hoO, hEO⟩ :=
    hp.left_entry_origin_at ht hle hy htb hE hET (by omega) hEC
      (by clear * - hfloor hCh hEh; omega)
  have hvd : v ∈ H (tr.time d₁) := hrun.antitone (hle d₁ hd₁) hv
  have hi0 := hrun.time_nonneg i
  have hBO : Anc (tr.HonestBlocksAt H) B O := by
    rcases hcomp v r l O (by clear * - hd₁ hrd; omega) hoO with h | h
    · exact h
    · exfalso
      have hEB := hEO.trans h
      have hEx := mem_of_honest_anc_at hrun hnc0 hi0 (hcut i) ho.1 hEB hBx
      have hle' := σ_h_le_of_anc (fg_reachable_at hrun hi0 (hcut i) ho.1)
        (store_anc_of_honest_anc_at hrun hnc0 hi0 (hcut i) ho.1 hEB hBx)
      rw [σ_eq_honest_at hrun hnc0 hi0 (hcut i) ho.1 ht hle hy hEx hE] at hle'
      clear * - hfloor hEh hle'; omega
  exact ⟨v, r, l, O, E, by clear * - hd₁ hrd; omega, hoO,
    hrow W hW att ha v d₁ hvd hsd hd₁ r l O hrd hoO, hE, hEO, hBO,
    by clear * - hfl hEh; omega, d₁, att, hrd, hd₁, hvd, hsd, haT⟩

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
