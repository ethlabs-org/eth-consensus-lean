module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SourceCover
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LeftEntry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot

public section

/-! # Signed sources at the predecessor of the maximum held height -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams Payload)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {hold : Time}

/-- A high origin below `hmax − 1` has a signed source or covered entry at that height. -/
theorem high_pred_signed_source_or_covered_before_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i j k : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {u : Nat}
    (hrow : ∀ W ∈ (tr.state y k).fg.tree, ∀ att ∈ W.fgPayload,
      ∀ v d, v ∈ H (tr.time d) → tr.SignAt v d att → d < k → ∀ r l O,
        r < d → HighOrigin tr H g v r l O → l < u)
    (hcomp : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocksAt H) B O)
    (hfloor : ((tr.state x i).fg.σ B.root).h < (tr.state y k).fg.hmax - 1) :
    (∃ v r l O E, r < k ∧ HighOrigin tr H g v r l O ∧ l < u ∧
      E ∈ (tr.state y k).fg.tree ∧ Anc (tr.HonestBlocksAt H) E O ∧
      Anc (tr.HonestBlocksAt H) B O ∧
      (tr.state y k).fg.hmax - 1 ≤ ((tr.state y k).fg.σ E.root).h ∧
      ∃ d att, r < d ∧ d < k ∧ v ∈ H (tr.time d) ∧ tr.SignAt v d att ∧ att.T = E.root) ∨
    (∃ E ∈ (tr.state y k).fg.tree, CoveredBefore tr H g a b (sp.slot t) k E ∧
      (tr.state y k).fg.hmax - 1 ≤ ((tr.state y k).fg.σ E.root).h ∧
      ∃ v d att, d < k ∧ v ∈ H (max (cutZ sp.toParams g) t) ∧ tr.SignAt v d att ∧
        att.T = E.root) := by
  have hrun := hp.run
  have hnc0 := hp.noColl
  have hreach := fg_reachable_at hrun ht hle hy
  have hBx := Outcome.high_origin_mem_at hrun hnc0 ho
  have hcut : ∀ q, ∀ p < q, tr.time p ≤ tr.time q := fun _ _ hp' => hrun.time_mono hp'.le
  have hBh := ho.2.2.2
  obtain ⟨-, -, -, -, -, ⟨C, hC, hCh⟩, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hreach
  obtain ⟨E, hE, hEC, hEh, hET⟩ :=
    entry_at_height hreach hC (h := (tr.state y k).fg.hmax - 1) (by clear * - hfloor; omega) (by
        clear * - hCh; omega)
  obtain ⟨W, hW, att, ha, v, d₁, hv, hd₁, hsd, haT, hor⟩ :=
    hp.left_entry_origin_or_covered_before_at ht hle hy htb hE hET (by omega) hEC
      (by clear * - hfloor hCh hEh; omega)
  rcases hor with ⟨r, hrd, l, O, hoO, hEO⟩ | ⟨hvz, hcov⟩
  swap
  · exact Or.inr ⟨E, hE, hcov, by omega, v, d₁, att, hd₁, hvz, hsd, haT⟩
  have hvd : v ∈ H (tr.time d₁) := hrun.antitone (hle d₁ hd₁) hv
  have hi0 := hrun.time_nonneg i
  have hx := hrun.antitone (le_max_right _ _) ho.1
  have hBO : Anc (tr.HonestBlocksAt H) B O := by
    rcases hcomp v r l O (by clear * - hd₁ hrd; omega) hoO with h | h
    · exact h
    · exfalso
      have hEB := hEO.trans h
      have hEx := mem_of_honest_anc_at hrun hnc0 hi0 (hcut i) hx hEB hBx
      have hle' := h_le_of_store_anc (fg_reachable_at hrun hi0 (hcut i) hx)
        (store_anc_of_honest_anc_at hrun hnc0 hi0 (hcut i) hx hEB hBx)
      rw [σ_eq_honest_at hrun hnc0 hi0 (hcut i) hx ht hle hy hEx hE] at hle'
      clear * - hfloor hEh hle'; omega
  exact Or.inl ⟨v, r, l, O, E, by clear * - hd₁ hrd; omega, hoO,
    hrow W hW att ha v d₁ hvd hsd hd₁ r l O hrd hoO, hE, hEO, hBO,
    by omega, d₁, att, hrd, hd₁, hvd, hsd, haT⟩

theorem high_pred_signed_source_or_covered_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i j k : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {u : Nat}
    (hrow : ∀ W ∈ (tr.state y k).fg.tree, ∀ att ∈ W.fgPayload,
      ∀ v d, v ∈ H (tr.time d) → tr.SignAt v d att → d < k → ∀ r l O,
        r < d → HighOrigin tr H g v r l O → l < u)
    (hcomp : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocksAt H) B O)
    (hfloor : ((tr.state x i).fg.σ B.root).h < (tr.state y k).fg.hmax - 1) :
    (∃ v r l O E, r < k ∧ HighOrigin tr H g v r l O ∧ l < u ∧
      E ∈ (tr.state y k).fg.tree ∧ Anc (tr.HonestBlocksAt H) E O ∧
      Anc (tr.HonestBlocksAt H) B O ∧
      (tr.state y k).fg.hmax - 1 ≤ ((tr.state y k).fg.σ E.root).h ∧
      ∃ d att, r < d ∧ d < k ∧ v ∈ H (tr.time d) ∧ tr.SignAt v d att ∧ att.T = E.root) ∨
    (∃ E ∈ (tr.state y k).fg.tree, CoveredUpTo tr H g a b (sp.slot t) E ∧
      (tr.state y k).fg.hmax - 1 ≤ ((tr.state y k).fg.σ E.root).h ∧
      ∃ v d att, d < k ∧ v ∈ H (max (cutZ sp.toParams g) t) ∧ tr.SignAt v d att ∧
        att.T = E.root) :=
  (hp.high_pred_signed_source_or_covered_before_at ho ht hle hy htb hrow hcomp hfloor).imp
    id fun ⟨E, hE, hcov, h⟩ => ⟨E, hE, hcov.coveredUpTo, h⟩

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
