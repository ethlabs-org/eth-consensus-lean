module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Geometry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Kernel
import ConsensusLean.Instances.Goldilocks.Lemmas.Frame.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RowLabel
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ResetSeeds

public section

/-! # P-U shadow, V-B9: the S1/S2 frontier inputs over the shadow run

`viable_of_frozen_witnesses'` is the stock `Compose/Run/FrameWitness` lemma over `Node.LocalRun'`
and `Node.frame'` (whose `fc_root` is `Σ.F`). The stock proof goes through unchanged except at one
place: a top frame (`h_max = h_j + 1`) and a block `B ⪯ Σ.J`. The stock frame roots fork choice at
`Σ.J` there and concludes `B ⪯ fc_root`; the shadow frame roots it at `Σ.F`, so the proof instead
puts `B` below `Σ.J`, which is a P-U viable head (`J_mem_viableHeads'`) with a witness in `T` (the
witness of `Σ.J`'s honest source). Everywhere else, a witness at height `≥ h_max − 1` is P-U viable:
by height, by the gap, or because it extends `Σ.J`.

The growing items (`no_high_contest_at'`, `reset_vote_floor_above_old_or_covered_at'`,
`held_high_origin_viable_at'`) are over `Growing.GoldilocksRun'` and `ResetPremisesUpTo'`. They read
the run-level origin family (left entries, high origins, healed covers) from `Shadow/PU/Origins`,
the row label bound from `Shadow/PU/RowLabel`, and the reset seed and the row entry member from
`Shadow/PU/ResetSeeds`.

* `no_high_contest_at'` is an FG-state fact. Its proof compares the two entries at `h_j` through
  their origins or covers directly (pairwise compatible above, so compatible), instead of through a
  common held block; it reads no viability.
* `reset_vote_floor_above_old_or_covered_at'` keeps the stock conclusion (`headHeightFloor`, an
  FG-state notion) and the stock proof.
* `held_high_origin_viable_at'` (Pivot/Viability): the shadow frame's root is `Σ.F`, so a block of
  the frame is above the root and the stock root comparison drops out. A block at height `h_max − 1`
  in a top frame is viable when it extends `Σ.J`, and otherwise lies below `Σ.J`, which is viable;
  the comparison with `Σ.J` comes from `Σ.J`'s left entry, as in the stock proof's lower case. -/

namespace Consensus.Goldilocks.Compose.FrameGeometry

open Consensus.Goldilocks.Store

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- **S3 over sources `G`, with frozen witnesses in `T`, over the shadow node**
(`viable_of_frozen_witnesses`): a block `B` of the honest blocks, compatible with every source of
the node's honest rows at heights `≥ h_j` (sources pairwise compatible), is in the viable tree of
`T` or at or below `fc_root` (`Σ.F` in the shadow frame), when `T` is a part of the node's frame
tree closed under ancestors and `B` and every source above `Σ.F` have witnesses in `T` above
them. -/
theorem viable_of_frozen_witnesses' (hr : Node.LocalRun' proposer dg H sg tr ini)
    (hfg : FGLocalRun' A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hf : 2 * Hᶜ.ncard < P.n) {y : Fin P.n} (hy : y ∈ H) {i : Nat} {G : A.Blk → Prop}
    (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (_hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    {T : Set A.Blk} (hTt : T ⊆ (Node.frame' (tr.state y i)).tree)
    (hTa : ∀ W ∈ T, ∀ X, (Node.frame' (tr.state y i)).Anc X W → X ∈ T)
    (hGW : ∀ D, G D → Anc (tr.HonestBlocks H) (Node.frame' (tr.state y i)).F D →
      ∃ W ∈ T, Anc (tr.HonestBlocks H) D W)
    {B : A.Blk} (hB : B ∈ tr.HonestBlocks H) (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hw : Anc (tr.HonestBlocks H) (Node.frame' (tr.state y i)).F B →
      ∃ W ∈ T, Anc (tr.HonestBlocks H) B W) :
    B ∈ (Node.frame' (tr.state y i)).viableTree T ∨
      Anc (tr.HonestBlocks H) B (Node.frame' (tr.state y i)).fcRoot := by
  set st := (tr.state y i).fg with hst
  have hΦe : Node.frame' (tr.state y i) = st.toFrame' := Node.frame'_eq _
  have hU := hfg.coherent
  have hR := Node.fg_reachable_at' hr hy i
  have hΦ : FrameOK (Node.frame' (tr.state y i)) := frameOK_state' hr hy i
  have hmemΦ : ∀ X, X ∈ (Node.frame' (tr.state y i)).tree ↔ X ∈ st.tree ∧ st.Anc st.F X := by
    intro X
    rw [hΦe, toFrame'_tree]
    rfl
  have hΦU : (Node.frame' (tr.state y i)).tree ⊆ tr.HonestBlocks H :=
    fun X hX => ⟨y, hy, i, ((hmemΦ X).1 hX).1⟩
  have hsU := fg_tree_subset_honest (tr := tr) hy i
  have hF0 : (Node.frame' (tr.state y i)).F = st.F := by rw [hΦe, toFrame'_F]
  have hfc0 : (Node.frame' (tr.state y i)).fcRoot = st.F := by rw [hΦe, toFrame'_fcRoot]
  have hs := hR.puSnapshot
  have hJt : st.J ∈ st.tree := hs.J_mem
  have hFJ : st.Anc st.F st.J := hs.F_J
  have hjm : st.hj < st.hmax := hs.hj_lt_hmax
  -- `Σ.J` and `Σ.F` are compatible with `B`
  have hJ := J_compatible' hr hfg hf hy hsrc hGB hB
  have hF : Compatible (tr.HonestBlocks H) st.F B := by
    rcases hJ with h | h
    · exact Or.inl ((hFJ.mono hsU).trans h)
    · exact Anc.total hU (hFJ.mono hsU) h
  rw [hfc0]
  rcases hF with hFB | hBf
  swap
  · exact Or.inr hBf
  left
  -- `B` lies between `Σ.F` and a witness, so it is in the frame
  obtain ⟨W, hW, hBW⟩ := hw (hF0 ▸ hFB)
  have hWt := (hmemΦ W).1 (hTt hW)
  have hBW' := honest_held_anc' hr hfg hy hBW hWt.1
  have hBt : B ∈ st.tree := anc_mem hBW' hWt.1
  have hBΦ : B ∈ (Node.frame' (tr.state y i)).tree :=
    (hmemΦ B).2 ⟨hBt, honest_held_anc' hr hfg hy hFB hBt⟩
  have hΦBW : (Node.frame' (tr.state y i)).Anc B W :=
    Frame.anc_tree_of_anc_U hU hΦ hΦU hBΦ hBW (hTt hW)
  have hΦfB : (Node.frame' (tr.state y i)).Anc (Node.frame' (tr.state y i)).fcRoot B :=
    Frame.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem (hfc0 ▸ hFB) hBΦ
  refine ⟨hTa W hW B hΦBW, hΦfB, ?_⟩
  have hΦs : ∀ X Y, (Node.frame' (tr.state y i)).Anc X Y → st.Anc X Y := fun X Y h =>
    Anc.mono (fun Z hZ => ((hmemΦ Z).1 hZ).1) h
  -- a viable witness above `B`
  have head : ∀ W' ∈ T, (Node.frame' (tr.state y i)).Anc B W' → st.IsViable' W' →
      ∃ W' ∈ T, W' ∈ (Node.frame' (tr.state y i)).viableHeads ∧
        (Node.frame' (tr.state y i)).Anc B W' := fun W' hW' hBW'' hv => by
    have hW't := (hmemΦ W').1 (hTt hW')
    refine ⟨W', hW', ?_, hBW''⟩
    rw [hΦe, toFrame'_viableHeads]
    exact ⟨hW't.1, hW't.2, hv⟩
  -- the top-frame case below `Σ.J`: `Σ.J` is a viable head with a witness in `T`
  by_cases hcase : st.hj + 1 < st.hmax ∨ Anc (tr.HonestBlocks H) st.J B
  swap
  · have htop : st.hmax = st.hj + 1 := by omega
    have hBJ : Anc (tr.HonestBlocks H) B st.J := hJ.resolve_left fun h => hcase (Or.inr h)
    have h1 : 1 ≤ st.hj := by
      by_contra h0
      have hJg := justified_genesis' hr (show st.hj = 0 by omega) hy
      exact hcase (Or.inr (hJg ▸ (honest_genesis_anc' hr hB).2))
    obtain ⟨-, -, D, hD, hDs⟩ := justified_honest_source_of' hr hfg hf hy hsrc h1
    obtain ⟨x, hx, k, -, -, hJD, -, -⟩ := honest_source_entry' hr hfg hDs ⟨y, hy, i, hJt⟩ rfl
    have hJDU : Anc (tr.HonestBlocks H) st.J D := hJD.mono (fg_tree_subset_honest hx k)
    obtain ⟨W', hW', hDW'⟩ := hGW D hD (hF0 ▸ (hFB.trans (hBJ.trans hJDU)))
    have hJΦ : st.J ∈ (Node.frame' (tr.state y i)).tree := (hmemΦ _).2 ⟨hJt, hFJ⟩
    have hJT : st.J ∈ T :=
      hTa W' hW' st.J (Frame.anc_tree_of_anc_U hU hΦ hΦU hJΦ (hJDU.trans hDW') (hTt hW'))
    refine ⟨st.J, hJT, ?_, Frame.anc_tree_of_anc_U hU hΦ hΦU hBΦ hBJ hJΦ⟩
    rw [hΦe]
    exact J_mem_viableHeads' hs htop
  -- otherwise every witness above `B` at height `≥ h_max − 1` is viable
  have viab : ∀ W', W' ∈ st.tree → st.Anc B W' → st.hmax - 1 ≤ (st.σ W'.root).h →
      st.IsViable' W' := by
    intro W' hW' hBW'' hh
    rw [isViable'_iff]
    by_cases hm : st.hmax ≤ (st.σ W'.root).h
    · exact Or.inl hm
    refine Or.inr ⟨by omega, hcase.imp id fun hJB => ?_⟩
    exact honest_held_anc' hr hfg hy (hJB.trans (hBW''.mono hsU)) hW'
  rcases floor_or_crossing_of' hr hfg hf hy hsrc hGB hBt with hle | ⟨D, E, -, hD, hDs, hE,
    hBE, hEh, -⟩
  · exact head W hW hΦBW (viab W hWt.1 (hΦs _ _ hΦBW)
      (hle.trans (honest_held_height' hr hy (hΦs _ _ hΦBW)).1))
  · -- the witness above the crossing source
    obtain ⟨x₀, hx₀, k₀, -, -, hED, -, -⟩ := honest_source_entry' hr hfg hDs ⟨y, hy, i, hE⟩ rfl
    have hEDU : Anc (tr.HonestBlocks H) E D := hED.mono (fg_tree_subset_honest hx₀ k₀)
    obtain ⟨W', hW', hDW'⟩ := hGW D hD (hF0 ▸ (hFB.trans ((hBE.mono hsU).trans hEDU)))
    have hW't := (hmemΦ W').1 (hTt hW')
    have hEW' := honest_held_anc' hr hfg hy (hEDU.trans hDW') hW't.1
    have hΦBW' := Frame.anc_tree_of_anc_U hU hΦ hΦU hBΦ
      ((hBE.mono hsU).trans (hEDU.trans hDW')) (hTt hW')
    refine head W' hW' hΦBW' (viab W' hW't.1 (hΦs _ _ hΦBW') ?_)
    rw [← hEh]
    exact (honest_held_height' hr hy hEW').1

end Consensus.Goldilocks.Compose.FrameGeometry

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)
open Consensus.Goldilocks.Store

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp} {g ΔF a b : Time}
  {hold : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

/-- Two blocks below two compatible blocks of a coherent set are compatible. -/
private theorem compatible_of_below {U : Set (AC.Blk sp.n (List (FG.Att sp.n)))}
    (hU : Coherent U) {X₁ X₂ Y₁ Y₂ : AC.Blk sp.n (List (FG.Att sp.n))}
    (h₁ : Anc U X₁ Y₁) (h₂ : Anc U X₂ Y₂) (h : Compatible U Y₁ Y₂) : Compatible U X₁ X₂ := by
  rcases h with h | h
  · exact Anc.total hU (h₁.trans h) h₂
  · exact Anc.total hU h₁ (h₂.trans h)

/-- An origin or a cover above each of two left entries makes them compatible. -/
private theorem entries_compatible
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {E₁ E₂ : AC.Blk sp.n (List (FG.Att sp.n))} {c d₁ d₂ : Nat} {v₁ v₂ : Fin sp.n}
    {m₁ m₂ : Nat} (hcb : tr.time c ≤ b) (hd₁ : d₁ < c) (hd₂ : d₂ < c)
    (h₁ : (∃ r < d₁, ∃ l O, HighOrigin tr H g v₁ r l O ∧ Anc (tr.HonestBlocksAt H) E₁ O) ∨
      CoveredUpTo tr H g a b m₁ E₁)
    (h₂ : (∃ r < d₂, ∃ l O, HighOrigin tr H g v₂ r l O ∧ Anc (tr.HonestBlocksAt H) E₂ O) ∨
      CoveredUpTo tr H g a b m₂ E₂) :
    Compatible (tr.HonestBlocksAt H) E₁ E₂ := by
  have hU := Coherence.honestBlocksAt_coherent' hp.run hp.noColl
  have hb : ∀ {r d}, r < d → d < c → tr.time r ≤ b := fun hr hd =>
    (hp.run.time_mono (show _ ≤ c by omega)).trans hcb
  rcases h₁ with ⟨r₁, hr₁, l₁, O₁, ho₁, hEO₁⟩ | hc₁
  · rcases h₂ with ⟨r₂, hr₂, l₂, O₂, ho₂, hEO₂⟩ | hc₂
    · exact compatible_of_below hU hEO₁ hEO₂
        (hp.origins_compatible_at' ho₁ (hb hr₁ hd₁) ho₂ (hb hr₂ hd₂))
    · exact compatible_of_below hU hEO₁ .refl
        (CoveredUpTo.compatible_highOrigin' hp.run hp.noColl hc₂ (hb hr₁ hd₁) ho₁).symm
  · rcases h₂ with ⟨r₂, hr₂, l₂, O₂, ho₂, hEO₂⟩ | hc₂
    · exact compatible_of_below hU .refl hEO₂
        (CoveredUpTo.compatible_highOrigin' hp.run hp.noColl hc₁ (hb hr₂ hd₂) ho₂)
    · obtain ⟨hc, C₁, s₁, hC₁, -, hEC₁⟩ := coveredUpTo_iff.1 hc₁
      obtain ⟨-, C₂, s₂, hC₂, -, hEC₂⟩ := coveredUpTo_iff.1 hc₂
      exact compatible_of_below hU hEC₁ hEC₂ (hc.s1 C₁ s₁ C₂ s₂ hC₁ hC₂)

/-- **No high contest at an honest reader's cut** over the shadow run (`no_high_contest_at`). -/
theorem Outcome.no_high_contest_at'
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {p : Fin sp.n} {i : Nat} (hpH : p ∈ H (tr.time i)) (hib : tr.time i ≤ b) :
    ¬ ((tr.state p i).fg.Contest ∧ HZ tr H g + 2 ≤ (tr.state p i).fg.hmax) := by
  have ht := hp.run.time_nonneg i
  have hi : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hp.run.time_mono hq.le
  have hU := Coherence.honestBlocksAt_coherent' hp.run hp.noColl
  have hr := (Compose.Growing.reachable_at' hp.run ht hpH hi).reachableWith
  have hu := finalitySpec_updateFinality' (P := sp.toParams) (ACP := Payload sp.n)
  have hsub : (tr.state p i).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨p, i, tr.time i, ht, hi, hpH, h⟩
  rintro ⟨⟨hmj, C, hC, _, hCh, hJC⟩, hmax⟩
  obtain ⟨_, hJm, _, ⟨Bj, hBj, hBjJ, hBjhj⟩, _⟩ := cache_invariants_with hu hr
  obtain ⟨EJ, hEJ, hEJr, hEJB, hcase⟩ := J_entry_with hu hr hBj
  obtain rfl : EJ = (tr.state p i).fg.J := hU.1 (hsub hEJ) (hsub hJm) (hEJr.trans hBjJ)
  rcases hcase with hg | ⟨hJh, hJT⟩
  · exact hJC (hg ▸ (accepted_tree_with hu hr).2.2.2 C hC)
  obtain ⟨EC, hEC, hECC, hECh, hECT⟩ := entry_at_height_with hu hr hC
    (h := (tr.state p i).fg.hj) (by omega) (by omega)
  have hJlt : ((tr.state p i).fg.σ (tr.state p i).fg.J.root).h <
      ((tr.state p i).fg.σ Bj.root).h := by have := hj_lt_h_with hu hr hBj; omega
  obtain ⟨-, -, -, -, v₁, d₁, -, hd₁, -, -, h₁⟩ :=
    hp.left_entry_origin_or_covered_at' ht hi hpH hib hEC hECT (by omega) hECC (by omega)
  obtain ⟨-, -, -, -, v₂, d₂, -, hd₂, -, -, h₂⟩ :=
    hp.left_entry_origin_or_covered_at' ht hi hpH hib hJm hJT (by omega) hEJB hJlt
  have hcmp := entries_compatible hp hib hd₁ hd₂ (h₁.imp_right And.right) (h₂.imp_right And.right)
  have hh : ((tr.state p i).fg.σ (tr.state p i).fg.J.root).h =
      ((tr.state p i).fg.σ EC.root).h := by rw [hJh, hBjhj, hECh]
  have he : EC.root = (tr.state p i).fg.J.root := by
    rcases hcmp with h | h
    · have := Th_eq_of_anc_with hu hr
        (Coherence.held_anc_at' hp.run hp.noColl ht hpH hi h hJm) hh
      rw [← hECT, ← hJT, this]
    · have := Th_eq_of_anc_with hu hr
        (Coherence.held_anc_at' hp.run hp.noColl ht hpH hi h hEC) hh.symm
      rw [← hECT, ← hJT, this]
  have heq : EC = (tr.state p i).fg.J := hU.1 (hsub hEC) (hsub hJm) he
  exact hJC (heq ▸ hECC)

/-- An older fast-lock label written by the late-vote deadline was written before the slot
(`Outcome.fastLock_time_lt_at`, the stock proof). -/
theorem Outcome.fastLock_time_lt_at' {ini : Fin sp.n → (goldilocksNode' sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    {x : Fin sp.n} {r m u : Nat} {D : AC.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (AC.Vote sp.n)} (hfl : AC.FastLockAt tr.projAC x r m D CV)
    (hmu : m < u) (htr : tr.time r ≤ sp.ts u + sp.Δ) : tr.time r < sp.ts u :=
  hrun.toCore.fastLock_time_lt_at hfl hmu htr

/-- **The voter's height floor** over the shadow run (`reset_vote_floor_above_old_or_covered_at`):
a pre-slot origin bound and a label-bounded cover bound reach the voter's height floor. -/
theorem ResetPremisesUpTo'.reset_vote_floor_above_old_or_covered_at'
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {j u : Nat} (hy : y ∈ H (tr.time j)) (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode' sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y j).fg.tree)
    (hBold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocksAt H) O B)
    (hcovered : HighSourceCover tr H g a b → ∀ C s,
      HealedMemberBefore tr H g a b C s j → s < u → Anc (tr.HonestBlocksAt H) C B) :
    (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ B.root).h := by
  have ht := hp.run.time_nonneg j
  have hj : ∀ q < j, tr.time q ≤ tr.time j := fun q hq => hp.run.time_mono hq.le
  have hreach := (Compose.Growing.reachable_at' hp.run ht hy hj).reachableWith
  have hu := finalitySpec_updateFinality' (P := sp.toParams) (ACP := Payload sp.n)
  obtain ⟨v₀, r₀, l₀, O₀, ho₀, hrb, _, hrt⟩ := hp.reset_seed_before_slot_at' hR
  have hBh := Outcome.high_of_anc_at' hp.run hp.noColl ho₀ ht hj hy hB
    (hBold v₀ r₀ l₀ O₀ ho₀ hrt hrb)
  have hnc := Outcome.no_high_contest_at' hp hy hjb
  by_contra hle
  have hfloor := lt_of_not_ge hle
  have hcon : ¬ (tr.state y j).fg.Contest := fun hcon => by
    unfold Store.headHeightFloor at hfloor
    simp only [hcon, ↓reduceIte] at hfloor
    exact hnc ⟨hcon, by omega⟩
  have hfl : (tr.state y j).fg.headHeightFloor = (tr.state y j).fg.hmax - 1 := by
    unfold Store.headHeightFloor
    simp only [hcon, ↓reduceIte]
  rw [hfl] at hfloor
  obtain ⟨_, _, _, _, _, ⟨C, hC, hCh⟩, _⟩ := cache_invariants_with hu hreach
  obtain ⟨E, hE, hEC, hEh, hET⟩ := entry_at_height_with hu hreach hC
    (h := (tr.state y j).fg.hmax - 1) (by omega) (by omega)
  obtain ⟨W, hW, att, ha, v, d, hv, hdj, hs, hT, hsource⟩ :=
    hp.left_entry_origin_or_covered_at' ht hj hy hjb hE hET (by omega) hEC (by omega)
  have hc' : (tr.upTo (tr.time j)).projAC.CallAt y j ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc.1⟩
  have hr := (Compose.goldilocks_ac_projection_from' (hp.run.upTo ht) (hp.noColl.upTo _)).localRun
  have htupper : tr.time j ≤ sp.ts u + sp.Δ :=
    hes ▸ (Compose.cast_head_fcRoot hr (hp.run.upTo ht).vstart hy ⟨hc', hc.2⟩).2
  have hEB : Anc (tr.HonestBlocksAt H) E B := by
    rcases hsource with ⟨r, hrd, l, O, ho, hEO⟩ | ⟨_, hcov⟩
    · have hlu : l < u := hes ▸ KernelProof.row_origin_label_lt_at' hp hy hc hW ha
        (hp.run.antitone (hp.run.time_mono hdj.le) hv) hs hdj hrd ho
      obtain ⟨CV, ellw, D, _, hf, _⟩ := ho.2.2.1
      have hrj := hp.run.time_mono (show r ≤ j by omega)
      have hrt := Outcome.fastLock_time_lt_at' hp.run hf hlu (hrj.trans htupper)
      exact hEO.trans (hBold v r l O ho hrt (hrj.trans hjb))
    · obtain ⟨hcov, _⟩ := coveredUpTo_iff.1 hcov
      obtain ⟨C, s, hC, hsu, hEC⟩ := Outcome.row_entry_member_before_cast_at' hp hy hjb hc hW ha
        ‹v ∈ H (max (cutZ sp.toParams g) (tr.time j))› hs hdj hE hT (by omega) hcov
      exact hEC.trans (hcovered hcov C s hC (hes ▸ hsu))
  have hh := h_le_of_store_anc_with hu hreach
    (Coherence.held_anc_at' hp.run hp.noColl ht hy hj hEB hB)
  omega

/-- **A held origin is viable at its independently honest reader** over the shadow run
(`ProposalImpl.held_high_origin_viable_at`, Pivot/Viability). -/
theorem ProposalImpl.held_high_origin_viable_at'
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {p : Fin sp.n} {c : Nat} (hpH : p ∈ H (tr.time c))
    {ell : ACLabel (goldilocksNode' sp)} (hc : tr.projAC.CallAt p c ell)
    (hcb : tr.time c ≤ b) {x : Fin sp.n} {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B)
    (hib : tr.time i ≤ b) (_ht : sp.ts (j + 1 : Nat) ≤ tr.time c)
    (hBt : B ∈ ell.frame.tree) :
    B ∈ ell.frame.viableTree ell.frame.tree ∨ ell.frame.Anc B ell.frame.fcRoot := by
  have ht := hp.run.time_nonneg c
  have hle : ∀ q < c, tr.time q ≤ tr.time c := fun _ hq => hp.run.time_mono hq.le
  have hR := Compose.Growing.reachable_at' hp.run ht hpH hle
  have hs := hR.puSnapshot
  have hU := Coherence.honestBlocksAt_coherent' hp.run hp.noColl
  have hanc : ∀ {X Y : AC.Blk sp.n (List (FG.Att sp.n))}, Anc (tr.HonestBlocksAt H) X Y →
      Y ∈ (tr.state p c).fg.tree → (tr.state p c).fg.Anc X Y :=
    fun h hY => Coherence.held_anc_at' hp.run hp.noColl ht hpH hle h hY
  rw [Shadow.PU.Growing.frame_of_projAC_at' hp.run hpH hc, Node.frame'_eq] at hBt ⊢
  rw [toFrame'_tree] at hBt
  obtain ⟨hBs, hFB⟩ := hBt
  left
  rw [mem_viableTree'_iff]
  refine ⟨hBs, hFB, ?_⟩
  set st := (tr.state p c).fg with hst
  have hBh : HZ tr H g + 1 ≤ (st.σ B.root).h :=
    Outcome.high_of_anc_at' hp.run hp.noColl ho ht hle hpH hBs .refl
  have hjm := hs.hj_lt_hmax
  -- the left entry of a held entry `E` above `B`'s height is compatible with `B`
  have hcmp : ∀ {E W : AC.Blk sp.n (List (FG.Att sp.n))}, E ∈ st.tree →
      (st.σ E.root).Th = E.root → HZ tr H g + 1 ≤ (st.σ E.root).h → st.Anc E W →
      (st.σ E.root).h < (st.σ W.root).h → Compatible (tr.HonestBlocksAt H) E B := by
    intro E W hE hET hEh hEW hlt
    obtain ⟨_, _, _, _, v, d, _, hdc, _, _, hor⟩ :=
      hp.left_entry_origin_or_covered_at' ht hle hpH hcb hE hET hEh hEW hlt
    rcases hor with ⟨r, hrd, l, O, hoO, hEO⟩ | ⟨-, hcov⟩
    · rcases hp.origins_compatible_at' hoO
          ((hp.run.time_mono (show r ≤ c by omega)).trans hcb) ho hib with h | h
      · exact Or.inl (hEO.trans h)
      · exact Anc.total hU hEO h
    · exact CoveredUpTo.compatible_highOrigin' hp.run hp.noColl hcov hib ho
  by_cases hm : st.hmax ≤ (st.σ B.root).h
  · exact ⟨B, hBs, hFB, isViable'_of_hmax_le hm, .refl⟩
  by_cases hlow : (st.σ B.root).h + 2 ≤ st.hmax
  · -- the stock lower case: `B` is below the entry at `h_max − 1` of a block at `h_max`
    obtain ⟨C, hC, hCh⟩ := hs.max_attained
    obtain ⟨E, hE, hEC, hEh, hET⟩ := hs.entry_at_height hC (h := st.hmax - 1) (by omega) (by omega)
    have hBE : Anc (tr.HonestBlocksAt H) B E := by
      rcases hcmp hE hET (by omega) hEC (by omega) with h | h
      · have := hs.height_mono (hanc h hBs)
        omega
      · exact h
    have hBC := (hanc hBE hE).trans hEC
    exact ⟨C, hC, hFB.trans hBC, isViable'_of_hmax_le (by omega), hBC⟩
  -- `B` at `h_max − 1`: viable in a gap frame, and in a top frame compared with `Σ.J`
  have hBm : (st.σ B.root).h + 1 = st.hmax := by omega
  by_cases hgap : st.hj + 1 < st.hmax
  · exact ⟨B, hBs, hFB, (st.isViable'_iff B).2 (Or.inr ⟨hBm, Or.inl hgap⟩), .refl⟩
  have hJB : Compatible (tr.HonestBlocksAt H) st.J B := by
    rcases hs.J_entry with hg | ⟨hJh, hJT, W, hW, hJW, hlt⟩
    · exact Or.inl ((hg ▸ hs.genesis_anc B hBs).mono fun X hX =>
        (⟨p, c, tr.time c, ht, hle, hpH, hX⟩ : X ∈ tr.HonestBlocksAt H))
    · exact hcmp hs.J_mem hJT (by omega) hJW (by omega)
  rcases hJB with h | h
  · exact ⟨B, hBs, hFB, (st.isViable'_iff B).2 (Or.inr ⟨hBm, Or.inr (hanc h hBs)⟩), .refl⟩
  · refine ⟨st.J, hs.J_mem, hs.F_J, ?_, hanc h hs.J_mem⟩
    exact J_mem_viableHeads' hs (by omega) |> fun h' => by
      rw [toFrame'_viableHeads] at h'
      exact h'.2.2

end Consensus.Goldilocks.Healing.Growing

end
