module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames

public section

/-! # The reader-local part of operational update selection

The pool and live-lock hypotheses belong to one honest update. Only receiving-node
execution is retained; no reset, cache-origin or service invariant is made static.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The update handler's post-state conclusions follow from its selected confirmation.
This is local execution, independent of the historical source of the pool or locks. -/
theorem update_selection_of_confirmation_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {j u : Nat}
    (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hu : SA.UpdateAt tr.projAC y j u ell)
    (hconf : SA.getConfirmation sp (tr.projAC.state y j) ell.frame u = some P)
    (hnv : ¬ SA.conflictsWithLock sp (tr.projAC.state y j).locks ell.frame (tr.time j) P) :
    tr.projAC.post j = SA.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u ∧
      (tr.projAC.post j).latestConfirmed =
        (SA.updateLatestConfirmed sp (tr.projAC.state y j) ell.frame P).latestConfirmed := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time j))
    (tr.upTo (tr.time j)) proposer (hrun.upTo (hrun.time_nonneg j))
    (hnc.upTo (tr.time j))).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hu' : SA.UpdateAt (tr.projAC.upTo (tr.time j)) y j u ell := by
    refine ⟨(Trace.upTo_callAt _).mpr ⟨le_rfl, hu.1⟩, hu.2.1, hu.2.2.1, ?_⟩
    simpa only [Trace.upTo_state tr.projAC y (fun _ hk => hrun.time_mono hk.le),
      Trace.upTo_time] using hu.2.2.2
  have he := hr.exec j ell hu'.1.2 (hu'.1.1 ▸ hy)
  rw [hu'.1.1, hu.2.1] at he
  rw [Trace.upTo_state tr.projAC y (fun _ hk => hrun.time_mono hk.le)] at he
  rw [Trace.upTo_post, Trace.upTo_time] at he
  have h1 : tr.projAC.post j =
      (SA.acOnTick sp y (tr.projAC.state y j) ell.frame (tr.time j)).1 :=
    (congrArg Prod.fst he).symm
  have ht : tr.time j = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hslot : sp.slot (tr.time j) = u + 1 := by
    rw [ht]
    exact SA.slot_of_mem sp (u + 1)
      (by simp only [SAParams.ts]; push_cast; linarith only [sp.toParams.hΔ])
      (by simp only [SAParams.ts]; push_cast; linarith only [sp.toParams.hΔ])
  have hpost : tr.projAC.post j =
      SA.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u := by
    rw [h1]
    unfold SA.acOnTick
    dsimp only
    have hn1 : ¬ tr.time j = sp.ts (u + 1 : Nat) + sp.Δ := by
      rw [ht]; simp only [SAParams.ts]; push_cast; linarith only [sp.toParams.hΔ]
    have h2 : tr.time j = sp.ts (u + 1 : Nat) + 2 * sp.Δ := by
      rw [ht]; simp only [SAParams.ts]; push_cast; ring
    have hj : SA.joined sp (tr.projAC.state y j) (tr.time j) := hu.2.2.2
    have hc2 : (tr.time j = sp.ts (u + 1 : Nat) + 2 * sp.Δ ∧ 0 < u + 1) = True :=
      eq_true ⟨h2, Nat.succ_pos u⟩
    rw [hslot]
    simp only [hj, not_true_eq_false, hn1, hc2, ↓reduceIte, Nat.add_sub_cancel]
  refine ⟨hpost, ?_⟩
  rw [hpost]
  unfold SA.updateConfirmation
  simp only [hconf, hnv, ↓reduceIte]
  unfold SA.updateLatestConfirmed
  split <;> rfl

/-- Early-resolved unanimous votes and compatible live locks determine the honest update.
Only the pool's voters at the reading cut are counted. -/
theorem ready_update_selection_of_pool_core_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {j u : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time j)) (hfault : 3 * (H (tr.time j))ᶜ.ncard ≤ sp.n - 1)
    (hu : SA.UpdateAt tr.projAC y j u ell) (hPt : P ∈ ell.frame.tree)
    (hPg : P.root ≠ sp.genesisRoot)
    (hpool : ∀ v, v ∈ H (tr.time j) → ∃ vote ∈ (tr.projAC.state y j).pool u,
      vote.val = v ∧ vote.head = P.root ∧
      SA.resolutionTime (tr.projAC.state y j) ell.frame vote < SA.ETime.of (sp.ts u + 2 * sp.Δ) ∧
      ∀ vote' ∈ (tr.projAC.state y j).pool u, vote'.val = v → vote' = vote)
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp (tr.projAC.state y j).locks ell.frame (tr.time j),
      Compatible (tr.HonestBlocksAt H) L P) (hstock : sp.committeeSize = sp.n) :
    SA.getConfirmation sp (tr.projAC.state y j) ell.frame u = some P ∧
      ¬ SA.conflictsWithLock sp (tr.projAC.state y j).locks ell.frame (tr.time j) P ∧
      SA.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P ∧
      tr.projAC.post j = SA.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u ∧
      (tr.projAC.post j).latestConfirmed =
        (SA.updateLatestConfirmed sp (tr.projAC.state y j) ell.frame P).latestConfirmed := by
  have hd0 := hrun.time_nonneg j
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time j))
    (tr.upTo (tr.time j)) proposer (hrun.upTo hd0) (hnc.upTo (tr.time j))).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hc : (tr.projAC.upTo (tr.time j)).CallAt y j ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hu.1⟩
  obtain ⟨hPhi, hPhiU₀⟩ := SA.frameIn_of_callAt hr hy hc
  have hPhiU : ell.frame.tree ⊆ tr.HonestBlocksAt H := fun X hX =>
    RunTrace.honestBlocks_upTo_subset hrun.time_mono hd0 (hPhiU₀ hX)
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  let A := tr.projAC.state y j
  let Hv := H (tr.time j)
  have hHvot : Hv ⊆ SA.voters {v | v ∈ A.pool u} := fun v hv => by
    obtain ⟨vote, hm, he, -⟩ := hpool v hv
    exact ⟨vote, hm, he⟩
  have hvle : (SA.voters {v | v ∈ A.pool u}).ncard ≤ sp.n := by
    have := Set.ncard_le_ncard (Set.subset_univ (SA.voters {v | v ∈ A.pool u}))
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have hHn : Hv.ncard + Hvᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hHle := Set.ncard_le_ncard hHvot
  have hf : 3 * Hvᶜ.ncard ≤ sp.n - 1 := hfault
  have hn : 0 < sp.n := sp.toParams.hn
  have hscore : Hv.ncard ≤ SA.confirmationScore sp A ell.frame u P := by
    unfold SA.confirmationScore
    apply Set.ncard_le_ncard (ht := Set.toFinite _)
    intro v hv
    obtain ⟨vote, hm, he, hh, hres, huniq⟩ := hpool v hv
    refine ⟨?_, vote, ⟨hm, hres⟩, he, ?_, P, hPt, hh.symm, .refl⟩
    · rintro ⟨x, hx, z, hz, hne, hxv, hzv⟩
      exact hne ((huniq x hx hxv).trans (huniq z hz hzv).symm)
    · have hm' : vote ∈ ((tr.projAC.upTo (tr.time j)).state y j).pool u := by
        simpa only [Trace.upTo_state tr.projAC y (fun _ hk => hrun.time_mono hk.le)] using hm
      exact_mod_cast SA.state_pool_slot sp hr hy j u vote hm'
  have hconf : SA.getConfirmation sp A ell.frame u = some P := by
    unfold SA.getConfirmation
    have hPS : P ∈ {B | B ∈ ell.frame.tree ∧ ell.frame.Anc ell.frame.F B ∧
        (SA.voters {v | v ∈ A.pool u}).ncard < 2 * SA.confirmationScore sp A ell.frame u B} :=
      ⟨hPt, hPhi.rooted.2 P hPt, by omega⟩
    have hall : ∀ B ∈ {B | B ∈ ell.frame.tree ∧ ell.frame.Anc ell.frame.F B ∧
        (SA.voters {v | v ∈ A.pool u}).ncard < 2 * SA.confirmationScore sp A ell.frame u B},
        ell.frame.Anc B P := by
      rintro B ⟨hBt, -, hmaj⟩
      by_contra hBP
      unfold SA.confirmationScore at hmaj
      dsimp only at hmaj
      refine absurd hmaj (not_lt.2 (le_trans (Nat.mul_le_mul_left 2
        (Set.ncard_le_ncard (t := Hvᶜ) ?_)) (by omega)))
      rintro v ⟨-, x, ⟨hx, -⟩, rfl, -, R, hR, hRr, hBR⟩ hv
      obtain ⟨vote, -, -, hh, -, huniq⟩ := hpool _ hv
      obtain rfl := huniq x hx rfl
      obtain rfl : R = P := hPhi.coherent.1 hR hPt (hRr.trans hh)
      exact hBP hBR
    obtain ⟨D, hD⟩ := SA.exists_deepest hPhi (fun B hB => hB.1) ⟨P, hPS⟩
    have hDP := hall D (SA.deepest_mem hD).1
    have hPD := SA.anc_deepest hPhi (fun B hB => hB.1)
      (fun B hB C hC => SA.anc_total hPhi.coherent (hall B hB) (hall C hC)) hD P hPS
    rw [hD, Anc.antisymm hPhi.coherent hDP hPD]
  have hnv : ¬ SA.conflictsWithLock sp A.locks ell.frame (tr.time j) P := by
    rintro ⟨L, hL, hnc⟩
    apply hnc
    rcases hlocks L hL with h | h
    · exact Or.inr (SA.anc_tree_of_anc_U hU hPhi hPhiU hL.1 h hPt)
    · exact Or.inl (SA.anc_tree_of_anc_U hU hPhi hPhiU hPt h hL.1)
  have hfast : SA.fastSelect sp A ell.frame u P = some P :=
    SA.fastSelect_eq_result hPhi hPt hPg (by unfold SA.FastTest; rw [hstock]; omega)
  exact ⟨hconf, hnv, hfast, update_selection_of_confirmation_at hrun hnc hy hu hconf hnv⟩

/-- The finite-reset wrapper supplies only execution, no collisions and the cut fault bound. -/
theorem ResetPremisesUpTo.ready_update_selection_of_pool_at {g ΔF a b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {j u : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time j)) (hjb : tr.time j ≤ b)
    (hu : SA.UpdateAt tr.projAC y j u ell) (hPt : P ∈ ell.frame.tree)
    (hPg : P.root ≠ sp.genesisRoot)
    (hpool : ∀ v, v ∈ H (tr.time j) → ∃ vote ∈ (tr.projAC.state y j).pool u,
      vote.val = v ∧ vote.head = P.root ∧
      SA.resolutionTime (tr.projAC.state y j) ell.frame vote < SA.ETime.of (sp.ts u + 2 * sp.Δ) ∧
      ∀ vote' ∈ (tr.projAC.state y j).pool u, vote'.val = v → vote' = vote)
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp (tr.projAC.state y j).locks ell.frame (tr.time j),
      Compatible (tr.HonestBlocksAt H) L P) :
    SA.getConfirmation sp (tr.projAC.state y j) ell.frame u = some P ∧
      ¬ SA.conflictsWithLock sp (tr.projAC.state y j).locks ell.frame (tr.time j) P ∧
      SA.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P ∧
      tr.projAC.post j = SA.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u ∧
      (tr.projAC.post j).latestConfirmed =
        (SA.updateLatestConfirmed sp (tr.projAC.state y j) ell.frame P).latestConfirmed :=
  ready_update_selection_of_pool_core_at hp.run hp.noColl hy
    (hp.faults _ (hp.run.time_nonneg j) hjb) hu hPt hPg hpool hlocks hp.stock

end Consensus.Goldilocks.Healing.Growing

end
