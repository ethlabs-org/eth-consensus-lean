module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Cut
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing, HR.4: the vote-step pieces

Pieces of C1.1's vote step for the reset `a_z`, at the height-scoped scope (`𝓔_B` the entries of
height `≥ H_z + 1` that conflict with `B`): a high origin's write is no earlier than its label's
slot (`le_ts_of_highOrigin`), C1.1 (i) from a compatible fork-choice root (`vote_viable_of_root`),
C1.1 (ii) (`high_vote_extends`, C1.1's `vote_extends` without the window `(s, m]` and without
`Clean`), and the compatibility of an earlier target with a later origin
(`ResetPremisesUpTo.target_compatible_later_origin_before`). -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n}
  {ini : Fin sp.n → (goldilocksNode sp).State} {H : Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-! ### The vote step -/

/-- The label of a high origin starts at or after `g` (`t_j ≥ c_z > ḡ ≥ g`). -/
theorem le_ts_of_highOrigin (hp : ResetPremises tr H K proposer dg g ΔF a) {x : Fin sp.n}
    {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) : g ≤ sp.ts j := by
  have h₁ := cutZ_le_ts_of_highOrigin hp ho
  have h₂ := lt_cutZ sp g
  have h₃ := le_gbar g
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  linarith

/-- **C1.1 (i) at a vote, from a compatible root** (as
`FrameGeometry.viable_of_frozen_witnesses`, with the compatibility of `fc_root` with `B` as the
premise instead of both caches): with (K2), `B` is in the viable voter block tree or at or below
`fc_root`. -/
theorem vote_viable_of_root (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y k ℓ e)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hcomp : Compatible (tr.HonestBlocks H) ℓ.frame.fcRoot B)
    (hK2 : (∃ D ∈ AC.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
        Anc (tr.HonestBlocks H) B D ∧ (tr.state y k).fg.IsViable D) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    B ∈ ℓ.frame.viableTree (AC.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  have hr := (Compose.goldilocks_ac_projection_from hrun hnc).localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hr.frameLaw y hy k ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  have hfr := Compose.frame_of_projAC hrun hy hc.1
  rcases hK2 with ⟨D, hD, hBD, hvD⟩ | h
  · rcases hcomp with hfB | hBf
    · have hDt : D ∈ ℓ.frame.tree := hD.1
      have hFB := (Anc.mono hΦU hΦ.F_anc_fcRoot).trans hfB
      have hBt := AC.frame_mem_of_between sp hU hΦ hΦU hDt hBD hFB
      have hΦBD := AC.anc_tree_of_anc_U hU hΦ hΦU hBt hBD hDt
      have hΦfB := AC.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfB hBt
      refine Or.inl ⟨AC.voterBlockTree_ancU hr.toU hrun.vstart hy hc D hD B hΦBD,
        hΦfB, D, hD, ?_, hΦBD⟩
      have hfD := hΦfB.trans hΦBD
      rw [hfr] at hDt hfD ⊢
      exact ⟨hDt.1, hDt.2, hvD⟩
    · exact Or.inr hBf
  · exact Or.inr h

/-- **C1.1 (ii) at a vote, height-scoped** (C1.1's `vote_extends` for a high origin, every slot
`> j` instead of the window `(j, m]`, and the premises one by one, without C1.1's `Clean`, which
need not hold): when (i) holds at an honest vote of a slot `σ > j` and every honest
vote of a slot `> j` at an earlier cut extends `B`, the vote extends `B`: below `fc_root` by
requirement 1, otherwise by A1.2 for `σ = j + 1` (its stored-block form) and by A1.3 after. -/
theorem high_vote_extends_of_syncAC
    (hrun : GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    {x : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (hx : x ∈ H) (hfl : Compose.StoredFastLockAt tr x i j B CV) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {ℓ : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ℓ e) (hs : j < e.msg.slot)
    (hsync0 : SyncAC (goldilocksNode sp) H (tr.HonestBlocks H)
      (sp.ts j) (tr.time k) tr.projAC)
    (hcarry : e.msg.slot = j + 1 → ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot →
      AC.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV)
    (hcarryLater : ∀ m', e.msg.slot = m' + 1 → j < m' →
      ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot →
      AC.CarryAt tr.projAC (tr.HonestBlocks H) y k e m' (Compose.honestVotes tr H m'))
    (hhalf : ∀ m', e.msg.slot = m' + 1 → j < m' →
      sp.committeeSize ≤
        2 * {x' | x' ∈ H ∧ ∃ j' e', AC.VoteAt tr.projAC x' j' e' ∧ e'.msg.slot = m'}.ncard)
    (hfault : ∀ m, j ≤ m → m < e.msg.slot → AC.FaultBoundK K m tr.projAC H (tr.time k))
    (hviab : B ∈ ℓ.frame.viableTree (AC.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot)
    (hprior : ∀ z ∈ H, ∀ j' < k, ∀ e', AC.VoteAt tr.projAC z j' e' → j < e'.msg.slot →
      AC.VoteExtends (tr.HonestBlocks H) e'.msg B)
    (hP : AC.CommitteeP K tr.projAC H) (hT : AC.CommitteeT K tr.projAC H)
    (hsize : ∀ s, (K.committee s).ncard = sp.committeeSize)
    (hcs2 : 2 * (K.committee e.msg.slot ∩ Hᶜ).ncard < sp.committeeSize) :
    AC.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hrun' := Compose.goldilocks_ac_projection_from hrun hnc
  have hr := hrun'.localRun
  obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, hle⟩ := Compose.cast_head_fcRoot hr
      hrun.vstart hy hc
  obtain ⟨-, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hr.frameLaw y hy k ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  by_cases hBf : Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot
  · exact ⟨Hd, hΦU hHd, hHdr, hBf.trans (Anc.mono hΦU hfHd)⟩
  have hv := hviab.resolve_right hBf
  have h0 := hr.time_nonneg k
  have hearlier : AC.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) k e.msg.slot B :=
    fun z hz j' hj' e' hv' hsl => hprior z hz j' hj' e' hv' (hsl ▸ hs)
  by_cases h1 : e.msg.slot = j + 1
  · obtain ⟨ℓw, D, hcw, hflD, hBD⟩ := hfl
    have hΦwU : ℓw.frame.tree ⊆ tr.HonestBlocks H := by
      rcases hr.frameLaw x hx i ℓw hcw with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1.2
    refine AC.first_transfer_storedU sp hrun'.toU K hP hT hsize hx hflD
      (hBD ▸ Anc.mono hΦwU (AC.anc_viableAncestor ℓw.frame D)) hy hc h1
      hsync0 (hcarry h1 hBf) (hfault j le_rfl hs) (h1 ▸ hcs2) ?_ ?_
    · rw [← h1]; exact Or.inl hv
    · rw [← h1]; exact hearlier
  · obtain ⟨m', hm'⟩ : ∃ m', e.msg.slot = m' + 1 := ⟨e.msg.slot - 1, by omega⟩
    have hsm' : j < m' := by omega
    refine AC.next_transfer_of_carry sp hrun' K hP hT hsize hy hc hm' ?_
      (hhalf m' hm' hsm') (hcarryLater m' hm' hsm' hBf) (hfault m' hsm'.le (by omega))
      (hm' ▸ hcs2) ?_ ?_
    · intro z hz j' e' hv' hsl
      have hjk : j' < k := by
        by_contra hjk
        obtain ⟨ℓ', hc', he'⟩ := hv'
        have h₁ := (AC.castAt_specU hr.toU hz ⟨hc', he'⟩).2.1
        have h₂ := AC.slot_mono sp h0 (hr.time_mono (not_lt.mp hjk))
        have h₃ := (AC.castAt_specU hr.toU hy hc).2.1
        omega
      exact hprior z hz j' hjk e' hv' (by omega)
    · rw [← hm']; exact Or.inl hv
    · rw [← hm']; exact hearlier

/-- Node synchrony specialization of high-origin vote transfer. -/
theorem high_vote_extends (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {x : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (hx : x ∈ H) (hfl : Compose.StoredFastLockAt tr x i j B CV) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {ℓ : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ℓ e) (hs : j < e.msg.slot)
    (hsync : tr.SyncRun H ΔF (sp.ts j) (sp.ts e.msg.slot + sp.Δ))
    (hcarry : e.msg.slot = j + 1 → ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot →
      AC.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV)
    (hcarryLater : ∀ m', e.msg.slot = m' + 1 → j < m' →
      ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot →
      AC.CarryAt tr.projAC (tr.HonestBlocks H) y k e m' (Compose.honestVotes tr H m'))
    (hhalf : ∀ m', e.msg.slot = m' + 1 → j < m' →
      sp.committeeSize ≤
        2 * {x' | x' ∈ H ∧ ∃ j' e', AC.VoteAt tr.projAC x' j' e' ∧ e'.msg.slot = m'}.ncard)
    (hfault : ∀ m, j ≤ m → m < e.msg.slot → AC.FaultBoundK K m tr.projAC H (tr.time k))
    (hviab : B ∈ ℓ.frame.viableTree (AC.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot)
    (hprior : ∀ z ∈ H, ∀ j' < k, ∀ e', AC.VoteAt tr.projAC z j' e' → j < e'.msg.slot →
      AC.VoteExtends (tr.HonestBlocks H) e'.msg B)
    (hP : AC.CommitteeP K tr.projAC H) (hT : AC.CommitteeT K tr.projAC H)
    (hsize : ∀ s, (K.committee s).ncard = sp.committeeSize)
    (hcs2 : 2 * (K.committee e.msg.slot ∩ Hᶜ).ncard < sp.committeeSize) :
    AC.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hr := (Compose.goldilocks_ac_projection_from hrun hnc).localRun
  have hsync0 := Compose.sync_projection sp.toParams (goldilocksNode sp) dg H (fun v => v.val) tr
    proposer ΔF (sp.ts j) (sp.ts e.msg.slot + sp.Δ) hrun.toLocalRun hsync
  exact high_vote_extends_of_syncAC hrun hnc hx hfl hy hc hs
    (Compose.syncAC_mono hsync0 le_rfl (Compose.cast_head_fcRoot hr
        hrun.vstart hy hc).2)
    hcarry hcarryLater hhalf hfault hviab hprior hP hT hsize hcs2

/-! ### The join and the assembly -/

/-- A later controlling high source compares with a prospective target from strictly
earlier head support. The target need not be a high origin or have been written yet. -/
theorem ResetPremisesUpTo.target_compatible_later_origin_before {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {x : Fin sp.n} {r m i l : Nat} {B O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r m O) (hri : r < i) (hlm : l < m)
    (hsupport : ∀ z ∈ H, ∀ q < i, ∀ e, AC.VoteAt tr.projAC z q e →
      l < e.msg.slot → AC.VoteExtends (tr.HonestBlocks H) e.msg B) :
    Compatible (tr.HonestBlocks H) B O := by
  have hrun := Compose.goldilocks_ac_projection_from hp.run hp.noColl
  obtain ⟨CV, hst⟩ := ho.2.2.1
  obtain ⟨_, D, hfl, hOD⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
  have hcomp := AC.fastLock_compatible_of_votes hrun _ hp.hP ho.1 hri hfl
    (hp.cs2 (slot_gbar_lt_of_cutZ_le (hp.cutZ_le_ts_of_highOrigin ho)))
    (fun z hz q hq e hv hs => hsupport z hz q hq e hv (by omega))
  rcases hcomp with hDB | hBD
  · exact Or.inr (hOD.trans hDB)
  · exact AC.anc_total hrun.localRun.coherent hBD hOD

end Consensus.Goldilocks.Healing

end
