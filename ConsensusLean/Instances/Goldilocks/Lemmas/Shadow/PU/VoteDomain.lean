module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.LowFinalized
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.VoteReceipt
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.RowLabel

public section

/-! # P-U shadow kernel: the vote domain of a held high target (S1's vote-domain step)

`KernelProof.held_target_vote_domain_before_of_quarantine_at'` is the stock
`Kernel/VoteDomain` lemma over the shadow run, with the **stock conclusion verbatim**:
`B ⪯ fc_root ∨ B ∈ viableTree (voterBlockTree)`, where the shadow frame's `fc_root` is `Σ.F`.
So `HighInduction`, `HighVote` and the AC transfer lemmas consume it unchanged.

The proof is the P-U one (the stock proof reads `headHeightFloor`, `Contest` and `fc_root = Σ.J`):

* **High `h_j`** (`HZ + 1 ≤ h_j`). `Σ.J` is a high left entry (not genesis: `J_entry_hj_with`).
  Its left-entry origin `O_J ⪰ Σ.J` is written before the vote with a label below the vote's
  slot (`row_origin_label_lt_at'`), so `B` is compatible with it (`hcompare`), hence with `Σ.J`
  and `Σ.F`. In a top frame, `Σ.J ⪯ B` makes `B` itself P-U viable; `B ≺ Σ.J` uses the frozen
  head of `O_J` (`high_origin_frozen_head_at'`), which is in the voter block tree above `Σ.J`,
  hence P-U viable. This is the case where the stock proof exited through `fc_root = Σ.J`.
* **Low `h_j`**. `Σ.F` is below the seed (`low_finalized_below_origin_at'`); a witness above `B`
  of height `≥ HZ + 1` is `B` or the seed's frozen head.
* **Gap frames** with `HZ + 1 ≤ h_max − 1`: the entry at `h_max − 1` below a block at `h_max` has a
  left-entry origin above `B` (or `B` reaches `h_max − 1` itself), whose frozen head is viable.

The row label bound is the shared `KernelProof.row_origin_label_lt_at'` (`Shadow/PU/RowLabel`). -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)
open Consensus.Goldilocks.Store

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
  {hold : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

/-- **A viable frozen descendant puts the target in the vote's viable tree** over the shadow
frame (`KernelProof.vote_viable_of_root_at`; the shadow root is `Σ.F`). -/
theorem KernelProof.vote_viable_of_root_at' {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) {B D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B)
    (hD : D ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot)
    (hBD : Anc (tr.HonestBlocksAt H) B D) (hvD : (tr.state y k).fg.IsViable D) :
    B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  have hd := hrun.time_nonneg k
  have hle : ∀ q < k, tr.time q ≤ tr.time k := fun _ hq => hrun.time_mono hq.le
  have hr := (Compose.goldilocks_ac_projection_from (hrun.upTo hd) (hnc.upTo _)).localRun
  have hc' : AC.CastAt (tr.upTo (tr.time k)).projAC y k ell e := by
    rw [RunTrace.upTo_projAC]
    exact AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hfr := Shadow.PU.Growing.frame_of_projAC_at hrun hy hc.1
  have hFe : ell.frame.F = (tr.state y k).fg.F := by rw [hfr, Node.frame_eq, toFrame_F]
  have hDs : D ∈ (tr.state y k).fg.tree ∧ (tr.state y k).fg.Anc (tr.state y k).fg.F D := by
    have h := hfr ▸ hD.1
    rwa [Node.frame_eq, toFrame_tree] at h
  have hBDs := Coherence.held_anc_at hrun hnc hd hy hle hBD hDs.1
  have hBs := Compose.FrameGeometry.anc_mem hBDs hDs.1
  have hFBs := Coherence.held_anc_at hrun hnc hd hy hle (hFe ▸ hFB) hBs
  have hΦBD : ell.frame.Anc B D := by
    rw [hfr, Node.frame_eq]
    simp only [Frame.Anc, toFrame_tree]
    exact Anc.restrict hFBs hBDs
  have hΦFB : ell.frame.Anc ell.frame.fcRoot B := by
    rw [hfr, Node.frame_eq]
    simp only [Frame.Anc, toFrame_tree, toFrame_fcRoot]
    exact Anc.restrict .refl hFBs
  refine ⟨AC.voterBlockTree_ancU hr.toU (hrun.upTo hd).vstart hy hc' D hD B hΦBD,
    hΦFB, D, hD, ?_, hΦBD⟩
  rw [hfr, Node.frame_eq, toFrame_viableHeads]
  exact ⟨hDs.1, hDs.2, hvD⟩

/-- **The finite vote-domain reduction inside the deep quarantine**, over the shadow run
(`KernelProof.held_target_vote_domain_before_of_quarantine_at`), with the stock conclusion. -/
theorem KernelProof.held_target_vote_domain_before_of_quarantine_at'
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
    (hpre : ∀ D, sp.deepDepth = some D → b ≤ cutZ sp.toParams g + 4 * D * sp.Δ) :
    Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
      B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  have ht := hp.run.time_nonneg i
  have hle : ∀ c < i, tr.time c ≤ tr.time i := fun _ hc => hp.run.time_mono hc.le
  have hR := Compose.Growing.reachable_at hp.run ht hy hle
  have hs := hR.puSnapshot
  have hr := hR.reachableWith
  have hu := finalitySpec_updateFinality (P := sp.toParams) (ACP := Payload sp.n)
  have hU := Coherence.honestBlocksAt_coherent hp.run hp.noColl
  have hsub : (tr.state y i).fg.tree ⊆ tr.HonestBlocksAt H :=
    Compose.Growing.tree_held_at ht hy hle
  have hanc : ∀ {X Y : AC.Blk sp.n (List (FG.Att sp.n))}, Anc (tr.HonestBlocksAt H) X Y →
      Y ∈ (tr.state y i).fg.tree → (tr.state y i).fg.Anc X Y :=
    fun h hY => Coherence.held_anc_at hp.run hp.noColl ht hy hle h hY
  have hfr := Shadow.PU.Growing.frame_of_projAC_at hp.run hy hcast.1
  have hFe : ell.frame.F = (tr.state y i).fg.F := by rw [hfr, Node.frame_eq, toFrame_F]
  have hroot : ell.frame.fcRoot = (tr.state y i).fg.F := by
    rw [hfr, Node.frame_eq, toFrame_fcRoot]
  have hvt : ∀ {W : AC.Blk sp.n (List (FG.Att sp.n))},
      W ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot →
      W ∈ (tr.state y i).fg.tree := fun hW =>
    (Shadow.PU.Growing.frame_tree_subset_at hp.run hp.noColl hy hcast.1).2 hW.1
  have frozen : ∀ {x' : Fin sp.n} {r' l' : Nat} {O : AC.Blk sp.n (List (FG.Att sp.n))},
      HighOrigin tr H g x' r' l' O → tr.time r' ≤ b → l' < e.msg.slot →
      Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F O →
      ∃ W ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
        Anc (tr.HonestBlocksAt H) O W := fun ho hrb' hl hFO =>
    KernelProof.high_origin_frozen_head_at hp ho hrb' hy hcast hl (hFe ▸ hFO)
  -- the reduction: `B ⪯ Σ.F`, or `Σ.F ⪯ B` with a P-U viable frozen block above `B`
  suffices key : Anc (tr.HonestBlocksAt H) B (tr.state y i).fg.F ∨
      (Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F B ∧
        ∃ D ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
          Anc (tr.HonestBlocksAt H) B D ∧ (tr.state y i).fg.IsViable D) by
    rcases key with h | ⟨hFB, D, hD, hBD, hvD⟩
    · exact Or.inl (hroot ▸ h)
    · exact Or.inr (KernelProof.vote_viable_of_root_at' hp.run hp.noColl hy hcast
        (hFe ▸ hFB) hD hBD hvD)
  have hjm := hs.hj_lt_hmax
  -- a left-entry origin, written before the vote, has a label below the vote's slot
  have leftOrigin : ∀ {E C : AC.Blk sp.n (List (FG.Att sp.n))},
      E ∈ (tr.state y i).fg.tree → ((tr.state y i).fg.σ E.root).Th = E.root →
      HZ tr H g + 1 ≤ ((tr.state y i).fg.σ E.root).h → (tr.state y i).fg.Anc E C →
      ((tr.state y i).fg.σ E.root).h < ((tr.state y i).fg.σ C.root).h →
      ∃ v' r' l' O, HighOrigin tr H g v' r' l' O ∧ r' < i ∧ tr.time r' ≤ b ∧
        l' < e.msg.slot ∧ Anc (tr.HonestBlocksAt H) E O := by
    intro E C hE hET hEh hEC hlt
    obtain ⟨W, hW, att, ha, v', d, hv', hd, hs', -, r', hrd, l', O, ho, hEO⟩ :=
      hp.left_entry_origin_of_quarantine_at ht hle hy hib hE hET hEh hEC hlt hpre
    have hl := KernelProof.row_origin_label_lt_at hp hy hcast hW ha
      (hp.run.antitone (hp.run.time_mono hd.le) hv') hs' hd hrd ho
    exact ⟨v', r', l', O, ho, by omega, (hp.run.time_mono (show r' ≤ i by omega)).trans hib,
      hl, hEO⟩
  -- gap frames with `HZ + 1 ≤ h_max − 1`: the entry at `h_max − 1` supplies the witness
  have gapW : (tr.state y i).fg.hj + 1 < (tr.state y i).fg.hmax →
      HZ tr H g + 1 ≤ (tr.state y i).fg.hmax - 1 → B ∈ (tr.state y i).fg.tree →
      Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F B →
      ∃ D ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
        Anc (tr.HonestBlocksAt H) B D ∧ (tr.state y i).fg.IsViable D := by
    intro hgap hHZ hBt hFB
    have viab : ∀ {W : AC.Blk sp.n (List (FG.Att sp.n))}, W ∈ (tr.state y i).fg.tree →
        (tr.state y i).fg.hmax - 1 ≤ ((tr.state y i).fg.σ W.root).h →
        (tr.state y i).fg.IsViable W := fun {W} _ hh => by
      rw [isViable_iff]
      by_cases hm' : (tr.state y i).fg.hmax ≤ ((tr.state y i).fg.σ W.root).h
      · exact Or.inl hm'
      · exact Or.inr ⟨by omega, Or.inl hgap⟩
    by_cases hBh : (tr.state y i).fg.hmax - 1 ≤ ((tr.state y i).fg.σ B.root).h
    · exact ⟨B, hheld (hFe ▸ hFB), .refl, viab hBt hBh⟩
    obtain ⟨C, hC, hCh⟩ := hs.max_attained
    obtain ⟨E, hE, hEC, hEh, hET⟩ :=
      hs.entry_at_height hC (h := (tr.state y i).fg.hmax - 1) (by omega) (by omega)
    obtain ⟨_, r', _, O, ho, hri, hrb', hl, hEO⟩ :=
      leftOrigin hE hET (by omega) hEC (by omega)
    have hBO : Anc (tr.HonestBlocksAt H) B O := by
      rcases hcompare _ r' _ O hri ho with h | h
      · exact h
      · exfalso
        have hEB := hEO.trans h
        have := hs.height_mono (hanc hEB hBt)
        omega
    obtain ⟨W, hW, hOW⟩ := frozen ho hrb' hl (hFB.trans hBO)
    have hEW := hs.height_mono (hanc (hEO.trans hOW) (hvt hW))
    exact ⟨W, hW, hBO.trans hOW, viab (hvt hW) (by omega)⟩
  by_cases hhigh : HZ tr H g + 1 ≤ (tr.state y i).fg.hj
  · -- high `h_j`: `Σ.J` is a high left entry with an origin `O_J` compatible with `B`
    obtain ⟨_, hJm, hFJ, ⟨Bj, hBj, hBjJ, hBjhj⟩, _⟩ := cache_invariants_with hu hr
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
    -- top frame: a block extending `Σ.J` at height `≥ h_j` is viable
    have viabJ : ∀ {W : AC.Blk sp.n (List (FG.Att sp.n))}, W ∈ (tr.state y i).fg.tree →
        (tr.state y i).fg.Anc (tr.state y i).fg.J W → (tr.state y i).fg.IsViable W := by
      intro W hW hJW
      have := hs.height_mono hJW
      rw [isViable_iff]
      by_cases hm' : (tr.state y i).fg.hmax ≤ ((tr.state y i).fg.σ W.root).h
      · exact Or.inl hm'
      · exact Or.inr ⟨by omega, Or.inr hJW⟩
    rcases hJB with hJB | hBJ
    · exact ⟨B, hBv, .refl, viabJ hBt (hanc hJB hBt)⟩
    · -- `B ≺ Σ.J`: the frozen head of `O_J` is in the voter block tree above `Σ.J`
      obtain ⟨W, hW, hOW⟩ := frozen ho hrb' hl (hFJU.trans hJO)
      exact ⟨W, hW, hBJ.trans (hJO.trans hOW), viabJ (hvt hW) (hanc (hJO.trans hOW) (hvt hW))⟩
  · -- low `h_j`: `Σ.F` is below the seed
    have hFS := hp.low_finalized_below_origin_at ht hle hy hib (by omega) hS hqb
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
    · exact ⟨W, hWv, hBW, isViable_of_hmax_le (by omega)⟩
    · exact gapW (by omega) (by omega) hBt hFB

end Consensus.Goldilocks.Healing.Growing

end
