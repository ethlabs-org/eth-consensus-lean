module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.VoteRoots
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.RowLabel
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.CoreStock
import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.View
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LeftEntry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LowFinalized
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.High

public section

/-! # Finite vote-domain assembly at independently honest cuts

The row-parametric assembly is closed by the proved causal vote-row exclusion,
yielding the exact frozen endpoint without a writer-survival premise.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams ReplayOrder Payload)
open Consensus.Goldilocks.Store

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
variable {hold : Time}

/-- The finite domain reduction once the vote-row labels are strictly earlier. -/
private theorem held_target_vote_domain_of_row_bound_before_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y v : Fin sp.n} {r i q m : Nat} {B S : AC.Blk sp.n (List (FG.Att sp.n))}
    (_hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time i))
    (_hBx : B ∈ (tr.state x r).fg.tree) (_hrb : tr.time r ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hcast : AC.CastAt tr.projAC y i ell e) (hib : tr.time i ≤ b)
    (hheld : Anc (tr.HonestBlocksAt H) ell.frame.F B →
      B ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot)
    (hS : HighOrigin tr H g v q m S) (hqb : tr.time q ≤ b) (hm : m < e.msg.slot)
    (hBS : Compatible (tr.HonestBlocksAt H) B S)
    (hcompare : ∀ z d n O, d < i → HighOrigin tr H g z d n O →
      Compatible (tr.HonestBlocksAt H) B O)
    (_hseedCompare : ∀ z d n O, d < i → HighOrigin tr H g z d n O →
      Compatible (tr.HonestBlocksAt H) S O)
    (_hpair : ∀ z d n O, d < i → HighOrigin tr H g z d n O →
      ∀ z' d' n' O', d' < i → HighOrigin tr H g z' d' n' O' →
      Compatible (tr.HonestBlocksAt H) O O')
    (hrow : ∀ W ∈ (tr.state y i).fg.tree, ∀ att ∈ W.fgPayload,
      ∀ z d, z ∈ H (tr.time d) → tr.SignAt z d att → d < i → ∀ c l O,
        c < d → HighOrigin tr H g z c l O → l < e.msg.slot)
    (hpre : ∀ D, sp.deepDepth = some D → b ≤ cutZ sp.toParams g + 4 * D * sp.Δ) :
    Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
      B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  have ht := hp.run.time_nonneg i
  have hle : ∀ c < i, tr.time c ≤ tr.time i := fun _ hc => hp.run.time_mono hc.le
  have hR := fg_reachable_at hp.run ht hle hy
  have hr := hR.reachableWith
  have hu := finalitySpec_updateFinality (P := sp.toParams) (ACP := Payload sp.n)
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hsub : (tr.state y i).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨y, i, tr.time i, ht, hle, hy, h⟩
  have hanc : ∀ {X Y : AC.Blk sp.n (List (FG.Att sp.n))}, Anc (tr.HonestBlocksAt H) X Y →
      Y ∈ (tr.state y i).fg.tree → (tr.state y i).fg.Anc X Y :=
    fun h hY => store_anc_of_honest_anc_at hp.run hp.noColl ht hle hy h hY
  have hfr := Outcome.frame_of_call hp.run hy hcast.1
  have hFe : ell.frame.F = (tr.state y i).fg.F := by rw [hfr]; rfl
  have hroot : ell.frame.fcRoot = (tr.state y i).fg.F := by rw [hfr]; rfl
  have hvt : ∀ {W : AC.Blk sp.n (List (FG.Att sp.n))},
      W ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot →
      W ∈ (tr.state y i).fg.tree := fun hW =>
    (frame_tree_subset_at hp.run hp.noColl hy hcast.1).2 hW.1
  have frozen : ∀ {x' : Fin sp.n} {r' l' : Nat} {O : AC.Blk sp.n (List (FG.Att sp.n))},
      HighOrigin tr H g x' r' l' O → tr.time r' ≤ b → l' < e.msg.slot →
      Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F O →
      ∃ W ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
        Anc (tr.HonestBlocksAt H) O W := fun ho hrb' hl hFO =>
    high_origin_frozen_head_at hp ho hrb' hy hcast hl (hFe ▸ hFO)
  suffices key : Anc (tr.HonestBlocksAt H) B (tr.state y i).fg.F ∨
      (Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F B ∧
        ∃ D ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
          Anc (tr.HonestBlocksAt H) B D ∧ (tr.state y i).fg.IsViable D) by
    rcases key with h | ⟨hFB, D, hD, hBD, hvD⟩
    · exact Or.inl (hroot ▸ h)
    · exact (vote_viable_of_root_at hp.run hp.noColl hy hcast (Or.inl (hroot ▸ hFB))
        (Or.inl ⟨D, hD, hBD, hvD⟩)).symm
  have hjm := hj_lt_hmax_of_reachable_with hu hr
  have leftOrigin : ∀ {E C : AC.Blk sp.n (List (FG.Att sp.n))},
      E ∈ (tr.state y i).fg.tree → ((tr.state y i).fg.σ E.root).Th = E.root →
      HZ tr H g + 1 ≤ ((tr.state y i).fg.σ E.root).h → (tr.state y i).fg.Anc E C →
      ((tr.state y i).fg.σ E.root).h < ((tr.state y i).fg.σ C.root).h →
      ∃ v' r' l' O, HighOrigin tr H g v' r' l' O ∧ r' < i ∧ tr.time r' ≤ b ∧
        l' < e.msg.slot ∧ Anc (tr.HonestBlocksAt H) E O := by
    intro E C hE hET hEh hEC hlt
    obtain ⟨W, hW, att, ha, v', d, hv', hd, hs', -, r', hrd, l', O, ho, hEO⟩ :=
      hp.left_entry_origin_of_quarantine_at ht hle hy hib hE hET hEh hEC hlt hpre
    have hl := hrow W hW att ha v' d
      (hp.run.antitone (hp.run.time_mono hd.le) hv') hs' hd r' l' O hrd ho
    exact ⟨v', r', l', O, ho, by omega, (hp.run.time_mono (show r' ≤ i by omega)).trans hib,
      hl, hEO⟩
  have gapW : (tr.state y i).fg.hj + 1 < (tr.state y i).fg.hmax →
      HZ tr H g + 1 ≤ (tr.state y i).fg.hmax - 1 → B ∈ (tr.state y i).fg.tree →
      Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F B →
      ∃ D ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
        Anc (tr.HonestBlocksAt H) B D ∧ (tr.state y i).fg.IsViable D := by
    intro hgap hHZ hBt hFB
    have viab : ∀ {W : AC.Blk sp.n (List (FG.Att sp.n))}, W ∈ (tr.state y i).fg.tree →
        (tr.state y i).fg.hmax - 1 ≤ ((tr.state y i).fg.σ W.root).h →
        (tr.state y i).fg.IsViable W := fun {W} _ hh => by
      change _ ∨ (_ ∧ _)
      by_cases hm' : (tr.state y i).fg.hmax ≤ ((tr.state y i).fg.σ W.root).h
      · exact Or.inl hm'
      · exact Or.inr ⟨by omega, Or.inl hgap⟩
    by_cases hBh : (tr.state y i).fg.hmax - 1 ≤ ((tr.state y i).fg.σ B.root).h
    · exact ⟨B, hheld (hFe ▸ hFB), .refl, viab hBt hBh⟩
    obtain ⟨_, _, _, _, _, ⟨C, hC, hCh⟩, _⟩ := cache_invariants_with hu hr
    obtain ⟨E, hE, hEC, hEh, hET⟩ :=
      entry_at_height_with hu hr hC (h := (tr.state y i).fg.hmax - 1) (by omega) (by omega)
    obtain ⟨_, r', _, O, ho, hri, hrb', hl, hEO⟩ :=
      leftOrigin hE hET (by omega) hEC (by omega)
    have hBO : Anc (tr.HonestBlocksAt H) B O := by
      rcases hcompare _ r' _ O hri ho with h | h
      · exact h
      · exfalso
        have := h_le_of_store_anc_with hu hr (hanc (hEO.trans h) hBt)
        omega
    obtain ⟨W, hW, hOW⟩ := frozen ho hrb' hl (hFB.trans hBO)
    have hEW := h_le_of_store_anc_with hu hr (hanc (hEO.trans hOW) (hvt hW))
    exact ⟨W, hW, hBO.trans hOW, viab (hvt hW) (by omega)⟩
  by_cases hhigh : HZ tr H g + 1 ≤ (tr.state y i).fg.hj
  · obtain ⟨_, hJm, hFJ, ⟨Bj, hBj, hBjJ, hBjhj⟩, _⟩ := cache_invariants_with hu hr
    obtain ⟨EJ, hEJ, hEJr, hEJB, hcase⟩ := J_entry_hj_with hu hr hBj
    obtain rfl : EJ = (tr.state y i).fg.J := hU.1 (hsub hEJ) (hsub hJm) (hEJr.trans hBjJ)
    rcases hcase with ⟨-, h0⟩ | ⟨hJh, hJT⟩
    · omega
    have hJlt : ((tr.state y i).fg.σ (tr.state y i).fg.J.root).h <
        ((tr.state y i).fg.σ Bj.root).h := by have := hj_lt_h_with hu hr hBj; omega
    obtain ⟨_, r', _, O, ho, hri, hrb', hl, hJO⟩ := leftOrigin hJm hJT (by omega) hEJB hJlt
    have hJB : Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.J B := by
      rcases hcompare _ r' _ O hri ho with h | h
      · exact Anc.total hU hJO h
      · exact Or.inl (hJO.trans h)
    have hFJU := hFJ.mono hsub
    have hFB : Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.F B := by
      rcases hJB with h | h
      · exact Or.inl (hFJU.trans h)
      · exact Anc.total hU hFJU h
    rcases hFB with hFB | hBF
    swap
    · exact Or.inl hBF
    right
    refine ⟨hFB, ?_⟩
    have hBv := hheld (hFe ▸ hFB)
    have hBt := hvt hBv
    by_cases hgap : (tr.state y i).fg.hj + 1 < (tr.state y i).fg.hmax
    · exact gapW hgap (by omega) hBt hFB
    have viabJ : ∀ {W : AC.Blk sp.n (List (FG.Att sp.n))}, W ∈ (tr.state y i).fg.tree →
        (tr.state y i).fg.Anc (tr.state y i).fg.J W → (tr.state y i).fg.IsViable W := by
      intro W hW hJW
      have := h_le_of_store_anc_with hu hr hJW
      change _ ∨ (_ ∧ _)
      by_cases hm' : (tr.state y i).fg.hmax ≤ ((tr.state y i).fg.σ W.root).h
      · exact Or.inl hm'
      · exact Or.inr ⟨by omega, Or.inr hJW⟩
    rcases hJB with hJB | hBJ
    · exact ⟨B, hBv, .refl, viabJ hBt (hanc hJB hBt)⟩
    · obtain ⟨W, hW, hOW⟩ := frozen ho hrb' hl (hFJU.trans hJO)
      exact ⟨W, hW, hBJ.trans (hJO.trans hOW), viabJ (hvt hW) (hanc (hJO.trans hOW) (hvt hW))⟩
  · have hFS := hp.low_finalized_below_origin_at ht hle hy hib (by omega) hS hqb
    have hFB : Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.F B := by
      rcases hBS with h | h
      · exact Anc.total hU hFS h
      · exact Or.inl (hFS.trans h)
    rcases hFB with hFB | hBF
    swap
    · exact Or.inl hBF
    right
    refine ⟨hFB, ?_⟩
    have hBv := hheld (hFe ▸ hFB)
    have hBt := hvt hBv
    obtain ⟨W, hWv, hBW, hWh⟩ : ∃ W ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
        Anc (tr.HonestBlocksAt H) B W ∧ HZ tr H g + 1 ≤ ((tr.state y i).fg.σ W.root).h := by
      rcases hBS with hBS | hSB
      · obtain ⟨W, hW, hSW⟩ := frozen hS hqb hm (hFB.trans hBS)
        exact ⟨W, hW, hBS.trans hSW,
          Outcome.high_of_anc_at hp.run hp.noColl hS ht hle hy (hvt hW) hSW⟩
      · exact ⟨B, hBv, .refl, Outcome.high_of_anc_at hp.run hp.noColl hS ht hle hy hBt hSB⟩
    by_cases hHm : (tr.state y i).fg.hmax ≤ HZ tr H g + 1
    · exact ⟨W, hWv, hBW, Or.inl (by omega)⟩
    · exact gapW (by omega) (by omega) hBt hFB

/-- Finite domain reduction with exactly the frozen earlier-comparison inputs, inside the deep
quarantine (`hpre`). -/
theorem held_target_vote_domain_before_of_quarantine_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y v : Fin sp.n} {r i q m : Nat} {B S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time i))
    (hBx : B ∈ (tr.state x r).fg.tree) (hrb : tr.time r ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hcast : AC.CastAt tr.projAC y i ell e) (hib : tr.time i ≤ b)
    (hheld : Anc (tr.HonestBlocksAt H) ell.frame.F B →
      B ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot)
    (hS : HighOrigin tr H g v q m S) (hqb : tr.time q ≤ b) (hm : m < e.msg.slot)
    (hBS : Compatible (tr.HonestBlocksAt H) B S)
    (hcompare : ∀ z d n O, d < i → HighOrigin tr H g z d n O →
      Compatible (tr.HonestBlocksAt H) B O)
    (hseedCompare : ∀ z d n O, d < i → HighOrigin tr H g z d n O →
      Compatible (tr.HonestBlocksAt H) S O)
    (hpair : ∀ z d n O, d < i → HighOrigin tr H g z d n O →
      ∀ z' d' n' O', d' < i → HighOrigin tr H g z' d' n' O' →
      Compatible (tr.HonestBlocksAt H) O O')
    (hpre : ∀ D, sp.deepDepth = some D → b ≤ cutZ sp.toParams g + 4 * D * sp.Δ) :
    Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
      B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  apply held_target_vote_domain_of_row_bound_before_at hp hx hy hBx hrb hcast hib hheld
    hS hqb hm hBS hcompare hseedCompare hpair
  · intro W hW att ha z d hz hs hdi c l O hcd ho
    exact row_origin_label_lt_at hp hy hcast hW ha hz hs hdi hcd ho
  · exact hpre

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
