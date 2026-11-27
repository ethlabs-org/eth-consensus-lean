module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The reader-local part of operational update selection

The pool and live-lock hypotheses belong to one honest update. Only receiving-node
execution is retained; no reset, cache-origin or service invariant is made static.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
variable {hold : Time}

/-- The update handler's post-state conclusions follow from its selected confirmation.
This is local execution, independent of the historical source of the pool or locks. -/
theorem update_selection_of_confirmation_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {j u : Nat}
    (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hu : AC.UpdateAt tr.projAC y j u ell)
    (hconf : AC.getConfirmation sp (tr.projAC.state y j) ell.frame u = some P)
    (hnv : ¬ AC.conflictsWithLock sp (tr.projAC.state y j).locks ell.frame (tr.time j) P) :
    tr.projAC.post j = AC.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u ∧
      (tr.projAC.post j).latestConfirmed =
        (AC.updateLatestConfirmed sp (tr.projAC.state y j) ell.frame P).latestConfirmed := by
  have hr := (Compose.goldilocks_ac_projection_from (hrun.upTo (hrun.time_nonneg j))
    (hnc.upTo (tr.time j))).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hu' : AC.UpdateAt (tr.projAC.upTo (tr.time j)) y j u ell := by
    refine ⟨(Trace.upTo_callAt _).mpr ⟨le_rfl, hu.1⟩, hu.2.1, hu.2.2.1, ?_⟩
    simpa only [Trace.upTo_state tr.projAC y (fun _ hk => hrun.time_mono hk.le),
      Trace.upTo_time] using hu.2.2.2
  have he := hr.exec j ell hu'.1.2 (hu'.1.1 ▸ hy)
  rw [hu'.1.1, hu.2.1] at he
  rw [Trace.upTo_state tr.projAC y (fun _ hk => hrun.time_mono hk.le)] at he
  rw [Trace.upTo_post, Trace.upTo_time] at he
  have h1 : tr.projAC.post j =
      (AC.acOnTick sp y (tr.projAC.state y j) ell.frame (tr.time j)).1 :=
    (congrArg Prod.fst he).symm
  have ht : tr.time j = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hslot : sp.slot (tr.time j) = u + 1 := by
    rw [ht]
    exact AC.slot_of_mem sp (u + 1)
      (by simp only [ACParams.ts]; push_cast; linarith only [sp.toParams.hΔ])
      (by simp only [ACParams.ts]; push_cast; linarith only [sp.toParams.hΔ])
  have hpost : tr.projAC.post j =
      AC.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u := by
    rw [h1]
    unfold AC.acOnTick
    dsimp only
    have hn1 : ¬ tr.time j = sp.ts (u + 1 : Nat) + sp.Δ := by
      rw [ht]; simp only [ACParams.ts]; push_cast; linarith only [sp.toParams.hΔ]
    have h2 : tr.time j = sp.ts (u + 1 : Nat) + 2 * sp.Δ := by
      rw [ht]; simp only [ACParams.ts]; push_cast; ring
    have hj : AC.joined sp (tr.projAC.state y j) (tr.time j) := hu.2.2.2
    have hc2 : (tr.time j = sp.ts (u + 1 : Nat) + 2 * sp.Δ ∧ 0 < u + 1) = True :=
      eq_true ⟨h2, Nat.succ_pos u⟩
    rw [hslot]
    simp only [hj, not_true_eq_false, hn1, hc2, ↓reduceIte, Nat.add_sub_cancel]
  refine ⟨hpost, ?_⟩
  rw [hpost]
  unfold AC.updateConfirmation
  simp only [hconf, hnv, ↓reduceIte]
  unfold AC.updateLatestConfirmed
  split <;> rfl

/-- Early-resolved unanimous votes of the honest slot-`u` committee members and compatible live
locks determine the honest update. Only the pool's voters at the reading cut are counted: they are
committee members, fewer than half of the committee is faulty, and the members honest at the cut
all support `P`. -/
theorem ready_update_selection_of_pool_core_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {K : AC.CommitteeDict sp.n}
    {y : Fin sp.n} {j u : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time j))
    (hP : ∀ v ∈ (tr.projAC.state y j).pool u, v.val ∈ K.committee u)
    (hsize : (K.committee u).ncard = sp.committeeSize)
    (hcs2 : 2 * (K.committee u ∩ (H (tr.time j))ᶜ).ncard < sp.committeeSize)
    (hu : AC.UpdateAt tr.projAC y j u ell) (hPt : P ∈ ell.frame.tree)
    (hPg : P.root ≠ sp.genesisRoot)
    (hpool : ∀ v, v ∈ H (tr.time j) → v ∈ K.committee u →
      ∃ vote ∈ (tr.projAC.state y j).pool u,
      vote.val = v ∧ vote.head = P.root ∧
      AC.resolutionTime (tr.projAC.state y j) ell.frame vote < AC.ETime.of (sp.ts u + 2 * sp.Δ) ∧
      ∀ vote' ∈ (tr.projAC.state y j).pool u, vote'.val = v → vote' = vote)
    (hlocks : ∀ L ∈ AC.liveLockBlocks sp (tr.projAC.state y j).locks ell.frame (tr.time j),
      Compatible (tr.HonestBlocksAt H) L P) :
    AC.getConfirmation sp (tr.projAC.state y j) ell.frame u = some P ∧
      ¬ AC.conflictsWithLock sp (tr.projAC.state y j).locks ell.frame (tr.time j) P ∧
      AC.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P ∧
      tr.projAC.post j = AC.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u ∧
      (tr.projAC.post j).latestConfirmed =
        (AC.updateLatestConfirmed sp (tr.projAC.state y j) ell.frame P).latestConfirmed := by
  have hd0 := hrun.time_nonneg j
  have hr := (Compose.goldilocks_ac_projection_from (hrun.upTo hd0)
    (hnc.upTo (tr.time j))).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hc : (tr.projAC.upTo (tr.time j)).CallAt y j ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hu.1⟩
  obtain ⟨hPhi, hPhiU₀⟩ := AC.frameIn_of_callAt hr hy hc
  have hPhiU : ell.frame.tree ⊆ tr.HonestBlocksAt H := fun X hX =>
    RunTrace.honestBlocks_upTo_subset hrun.time_mono hd0 (hPhiU₀ hX)
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  let A := tr.projAC.state y j
  let Hv := H (tr.time j)
  have hKvot : (K.committee u ∩ Hv) ⊆ (AC.voters {v | v ∈ A.pool u}) ∩ Hv := fun v hv => by
    obtain ⟨vote, hm, he, -⟩ := hpool v hv.2 hv.1
    exact ⟨⟨vote, hm, he⟩, hv.2⟩
  have hVK : (AC.voters {v | v ∈ A.pool u}) ⊆ K.committee u := by
    rintro w ⟨v, hv, rfl⟩
    exact hP v hv
  have hFV : Hvᶜ ∩ (AC.voters {v | v ∈ A.pool u}) ⊆ K.committee u ∩ Hvᶜ := fun w hw =>
    ⟨hVK hw.2, hw.1⟩
  have hsplitK : (K.committee u ∩ Hv).ncard + (K.committee u ∩ Hvᶜ).ncard = sp.committeeSize := by
    rw [← hsize, Set.inter_comm (K.committee u) Hvᶜ, ← Set.sdiff_eq_compl_inter]
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)
  have hsplitV : ((AC.voters {v | v ∈ A.pool u}) ∩ Hv).ncard +
      (Hvᶜ ∩ (AC.voters {v | v ∈ A.pool u})).ncard = (AC.voters {v | v ∈ A.pool u}).ncard := by
    rw [← Set.sdiff_eq_compl_inter]
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)
  have hKle := Set.ncard_le_ncard hKvot
  have hcs2' : 2 * (K.committee u ∩ Hvᶜ).ncard < sp.committeeSize := hcs2
  have hFle := Set.ncard_le_ncard hFV
  have hVHle : ((AC.voters {v | v ∈ A.pool u}) ∩ Hv).ncard ≤ (K.committee u ∩ Hv).ncard :=
    Set.ncard_le_ncard (fun w hw => ⟨hVK hw.1, hw.2⟩)
  have hscore : (K.committee u ∩ Hv).ncard ≤ AC.confirmationScore sp A ell.frame u P := by
    unfold AC.confirmationScore
    apply Set.ncard_le_ncard (ht := Set.toFinite _)
    intro v hv
    obtain ⟨vote, hm, he, hh, hres, huniq⟩ := hpool v hv.2 hv.1
    refine ⟨?_, vote, ⟨hm, hres⟩, he, ?_, P, hPt, hh.symm, .refl⟩
    · rintro ⟨x, hx, z, hz, hne, hxv, hzv⟩
      exact hne ((huniq x hx hxv).trans (huniq z hz hzv).symm)
    · have hm' : vote ∈ ((tr.projAC.upTo (tr.time j)).state y j).pool u := by
        simpa only [Trace.upTo_state tr.projAC y (fun _ hk => hrun.time_mono hk.le)] using hm
      exact_mod_cast AC.state_pool_slotU sp hr.toU (fun _ => (hrun.upTo hd0).vstart _) hy j u
        vote hm'
  have hconf : AC.getConfirmation sp A ell.frame u = some P := by
    unfold AC.getConfirmation
    have hPS : P ∈ {B | B ∈ ell.frame.tree ∧ ell.frame.Anc ell.frame.F B ∧
        (AC.voters {v | v ∈ A.pool u}).ncard < 2 * AC.confirmationScore sp A ell.frame u B} :=
      ⟨hPt, hPhi.rooted.2 P hPt, by omega⟩
    have hall : ∀ B ∈ {B | B ∈ ell.frame.tree ∧ ell.frame.Anc ell.frame.F B ∧
        (AC.voters {v | v ∈ A.pool u}).ncard < 2 * AC.confirmationScore sp A ell.frame u B},
        ell.frame.Anc B P := by
      rintro B ⟨hBt, -, hmaj⟩
      by_contra hBP
      unfold AC.confirmationScore at hmaj
      dsimp only at hmaj
      refine absurd hmaj (not_lt.2 (le_trans (Nat.mul_le_mul_left 2
        (Set.ncard_le_ncard (t := Hvᶜ ∩ (AC.voters {v | v ∈ A.pool u})) ?_)) (by omega)))
      rintro v ⟨-, x, ⟨hx, -⟩, rfl, -, R, hR, hRr, hBR⟩
      refine ⟨fun hv => ?_, x, hx, rfl⟩
      obtain ⟨vote, -, -, hh, -, huniq⟩ := hpool _ hv (hP x hx)
      obtain rfl := huniq x hx rfl
      obtain rfl : R = P := hPhi.coherent.1 hR hPt (hRr.trans hh)
      exact hBP hBR
    obtain ⟨D, hD⟩ := AC.exists_deepest hPhi (fun B hB => hB.1) ⟨P, hPS⟩
    have hDP := hall D (AC.deepest_mem hD).1
    have hPD := AC.anc_deepest hPhi (fun B hB => hB.1)
      (fun B hB C hC => AC.anc_total hPhi.coherent (hall B hB) (hall C hC)) hD P hPS
    rw [hD, Anc.antisymm hPhi.coherent hDP hPD]
  have hnv : ¬ AC.conflictsWithLock sp A.locks ell.frame (tr.time j) P := by
    apply AC.not_conflictsWithLock_of_forall
    intro L hL
    rcases hlocks L hL with h | h
    · exact Or.inr (AC.anc_tree_of_anc_U hU hPhi hPhiU hL.1 h hPt)
    · exact Or.inl (AC.anc_tree_of_anc_U hU hPhi hPhiU hPt h hL.1)
  have hfast : AC.fastSelect sp A ell.frame u P = some P :=
    AC.fastSelect_eq_result hPhi hPt hPg (by unfold AC.FastTest; omega)
  exact ⟨hconf, hnv, hfast, update_selection_of_confirmation_at hrun hnc hy hu hconf hnv⟩

/-- The finite-reset wrapper supplies execution, no collisions, and at the slot-`u` committee
its pool membership (P), size and CS2 at the reading cut (`committee_cs2_at`). -/
theorem ResetPremisesUpTo.ready_update_selection_of_pool_at {g ΔF a b : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {j u : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time j)) (hjb : tr.time j ≤ b) (hgu : AC.gbar g ≤ sp.ts u)
    (hu : AC.UpdateAt tr.projAC y j u ell) (hPt : P ∈ ell.frame.tree)
    (hPg : P.root ≠ sp.genesisRoot)
    (hpool : ∀ v, v ∈ H (tr.time j) → v ∈ (Generic.dictOfTime sp cm).committee u →
      ∃ vote ∈ (tr.projAC.state y j).pool u,
      vote.val = v ∧ vote.head = P.root ∧
      AC.resolutionTime (tr.projAC.state y j) ell.frame vote < AC.ETime.of (sp.ts u + 2 * sp.Δ) ∧
      ∀ vote' ∈ (tr.projAC.state y j).pool u, vote'.val = v → vote' = vote)
    (hlocks : ∀ L ∈ AC.liveLockBlocks sp (tr.projAC.state y j).locks ell.frame (tr.time j),
      Compatible (tr.HonestBlocksAt H) L P) :
    AC.getConfirmation sp (tr.projAC.state y j) ell.frame u = some P ∧
      ¬ AC.conflictsWithLock sp (tr.projAC.state y j).locks ell.frame (tr.time j) P ∧
      AC.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P ∧
      tr.projAC.post j = AC.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u ∧
      (tr.projAC.post j).latestConfirmed =
        (AC.updateLatestConfirmed sp (tr.projAC.state y j) ell.frame P).latestConfirmed :=
  ready_update_selection_of_pool_core_at hp.run hp.noColl hy
    (fun v hv => hp.committeeFacts.hP.1 _ y hy j (fun _ hk => hp.run.time_mono hk.le) u v hv)
    (hp.committeeFacts.hsize u)
    (hp.committee_cs2_at hgu (by
      have ht : tr.time j = sp.ts u + 6 * sp.Δ := hu.2.2.1
      linarith [sp.toParams.hΔ])
      (hp.run.time_nonneg j) hjb) hu hPt hPg hpool hlocks

end Consensus.Goldilocks.Healing.Growing

end
