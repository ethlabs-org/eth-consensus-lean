module
import all AvailableChainFGCompose.Tests.P0d5db
import AvailableChainFGCompose.Proofs.Population.FrontierSearchFull
import AvailableChainFGCompose.Proofs.Population.FrontierSearchBridges

-- Standalone all-holder control on the accepted ladder event fold.
noncomputable section
namespace AvailableChain.FGCompose.Tests.POP6bFrozen
open AvailableChain.SimplexFG AvailableChain.KitFG
open P0d5db

private theorem frozen_premises_sat :
    (FGTimingLaws v5T) ∧
    (1 ≤ 1) ∧
    (RXing ladR v5env ladrho ladO) ∧
    (V2.D.ScheduleWellFormed v5env ladrho) ∧
    (FGRunOrderLaws v5env ladrho ladR) ∧
    (∀ y ∈ ladrho.honest, ∀ t, v5env.t_GST ≤ t → t ≤ ladrho.horizon → v5env.awake y t = true) ∧
    (∀ iy y t, y ∈ ladrho.honest → ladrho.events[iy]? = some (.tick y t) → t ≤ ladrho.horizon →
      v5env.t_GST ≤ slotStartZ v5T (((slotAt v5T t : Slot) : Int) - 1) → (fun _ => true)
      (ladP.clock (ladrho.stateBefore v5env iy y) t) = true) ∧
    (∀ t, 12 ≤ t → v5env.t_GST ≤ slotStartZ v5T (((slotAt v5T t : Slot) : Int) - 1)) ∧
    (∀ i (ev : V2.Event Unit ladP.Object) m, ladrho.events[i]? = some ev → 12 ≤ ev.time → 1 ≤ m →
      frontierAtIdx ladR v5env ladrho (i + 1) = m → ev.time + v5T.delta ≤ ladrho.horizon →
      PhaseWitnessReceiptScope ladR v5env ladrho ladO (fun _ => true) ladreceipt (i + 1) m
      (ev.time + v5T.delta)) ∧
    (∀ W d y, y ∈ ladrho.honest → ladreceipt (ladR.erase W) d y → W ∈ (ladR.core
      (ladrho.stateBeforeTime v5env d y)).fg.TF) ∧
    (v5E.weightOf (historyFaulty ladS ladrho) < v5E.q) ∧
    (v5env.Δ ≤ 1) ∧
    (v5env.Δ = v5T.delta) ∧
    (∀ t, v5env.t_GST ≤ t → t + 4 ≤ ladrho.horizon → ∃ s, t < v5T.proposal s ∧ v5T.proposal s ≤ t
      + 4 ∧ Gen.V2.Duty.HonestSlot ladrho ladI s) ∧
    (v5env.t_GST ≤ 12) ∧
    (4 * v5T.delta ≤ 4) ∧
    (PromotionSlotProposal ladR v5env ladrho v5T ladI) ∧
    (PromotionProposalRead ladR ladS v5env ladrho ladO ladI laddecode id (fun _ => [])
      ladparentFG ladparentHeight ladvalidFor ladfold) ∧
    (PromotionRowOrder ladR v5env ladrho ladO ladI) ∧
    (PromotionRowSigner ladS v5env ladrho v5T ladD) ∧
    (PromotionSourceParent ladR v5env ladrho ladO v5T ladI 12) ∧
    (TRowsReceipt ladR ladS v5env ladrho v5T (fun _ => []) 1) ∧
    (∀ (r height : Nat) (U X : FGBlock (Fin 1)), BatchPrem ladR ladS ladO v5T v5env ladrho ladI
      ladD v5E laddecode id (fun _ => []) (fun _ => []) ladparentFG ladparentHeight ladvalidFor 1
      .progress r height U X → (ladO.height X.parent).h = height → ProgressCoveredByChild v5E
      ladO.height X U height) ∧
    (ProgressFoldAdvance v5E ladO.height 4) ∧
    (∃ Q : Finset (Fin 1), (∀ i ∈ Q, safetyHolder ladS ladrho i ∈ ladrho.honest) ∧ v5E.q ≤
      v5E.weightOf Q) ∧
    (∀ r x y K L, x ∈ ladrho.honest → y ∈ ladrho.honest → actionSourceFG ladR v5env ladrho v5T x
      r = some (some K) → actionSourceFG ladR v5env ladrho v5T y r = some (some L) → (ladO.height
      K).T_h.root = (ladO.height L).T_h.root → (ladO.height K).T_h = (ladO.height L).T_h) ∧
    (∀ r x K, x ∈ ladrho.honest → actionSourceFG ladR v5env ladrho v5T x r = some (some K) →
      K.slot ≤ r * v5T.roundSlots) ∧
    (∀ r x K A, x ∈ ladrho.honest → actionSourceFG ladR v5env ladrho v5T x r = some (some K) →
      FGBlock.Preceq A K → A.slot ≤ K.slot) ∧
    (∀ A B : FGBlock (Fin 1), Block.Preceq (ladR.erase A) (ladR.erase B) → FGBlock.Preceq A B) ∧
    (AttemptProposalFloor ladR v5env ladrho ladO v5T ladI 12) ∧
    (∀ u v m J contested q Q, 12 ≤ u → PhaseInterval ladR v5env ladrho ladO u v m J contested →
      FrontierSeedQualification v5T 1 v5env.t_GST u q → v5T.gate q ≤ v → HonestProposal v5env
      ladrho ladI q Q → ∃ i x Qfg, V2.D.Run.idxBefore ladrho u ≤ i ∧ i ≤ timeIdx ladrho v ∧ x ∈
      ladrho.honest ∧ Qfg ∈ (ladR.core (ladrho.stateBefore v5env i x)).fg.TF ∧ ladR.erase Qfg =
      Q) ∧
    (∀ u v m J contested q Q Qfg, 12 ≤ u → HonestProposal v5env ladrho ladI q Q → ladR.erase Qfg
      = Q → (ladO.height Qfg).h = m → FrontierProposalService ladR v5env ladrho v5T q Q →
      FrontierSeedQualification v5T 1 v5env.t_GST u q → u ≤ v5T.proposal q → PhaseInterval ladR
      v5env ladrho ladO u (v5T.gate q) m J contested → v5T.gate q ≤ v → v ≤ ladrho.horizon → (∀ i
      x, timeIdx ladrho u ≤ i → i ≤ timeIdx ladrho v → x ∈ ladrho.honest → (ladR.core
      (ladrho.stateBefore v5env i x)).fg.h_max ≤ m) → FrontierLocalServiceFG ladR ladS v5env ladrho
      ladO v5T ladI ladD.heightPair q Q Qfg m v) ∧
    (∀ u m J contested q Q Qfg r, 12 ≤ u → HonestProposal v5env ladrho ladI q Q → ladR.erase Qfg
      = Q → FrontierProposalService ladR v5env ladrho v5T q Q → FrontierSeedQualification v5T 1
      v5env.t_GST u q → u ≤ v5T.proposal q → q ≤ r * v5T.roundSlots → (∀ r', q ≤ r' *
      v5T.roundSlots → r ≤ r') → PhaseInterval ladR v5env ladrho ladO u (v5T.action r) m J
      contested → OpeningCoveredFG ladR ladS v5env ladrho ladO.height v5T ladD.heightPair
      (FGHonestSeats ladS ladrho) r Q ∧
      ((ladO.height Qfg).h = m - 1 → OpeningEntry ladR v5env ladrho ladO.height v5T r (m - 1) ∨ ∃
      x K, x ∈ ladrho.honest ∧ actionSourceFG ladR v5env ladrho v5T x r = some (some K) ∧
      (ladO.height K).h = m)) ∧
    (∀ i x A K, K ∈ (ladR.core (ladrho.stateBefore v5env i x)).fg.TF → FGBlock.Preceq A K →
      A.slot ≤ K.slot) ∧
    (∀ q Q K, HonestProposal v5env ladrho ladI q Q → ladR.erase K = Q → K.slot = q) ∧
    (∀ i x, x ∈ ladrho.honest → (ladR.core (ladrho.stateBefore v5env i x)).fg.h_j ≠ 0 → ∃ j y r a
      K, j < i ∧ HonestRowAt ladS v5env ladrho v5T j y r a ∧ actionSourceFG ladR v5env ladrho v5T
      y r = some (some K) ∧ (ladO.height K).T_h = (ladR.core (ladrho.stateBefore v5env i
      x)).fg.J) ∧
    (∀ q Q, HonestProposal v5env ladrho ladI q Q → ∃ j, ladrho.events[j]? = some (.tick
      (V2.D.proposerOf ladrho ladI q) (v5T.proposal q)) ∧ ∀ Qfg, ladR.erase Qfg = Q →
      FGBlock.Preceq (ladO.controls (ladrho.stateBefore v5env j (V2.D.proposerOf ladrho ladI
      q))).Z Qfg.parent) ∧
    (∀ X : FGBlock (Fin 1), (ladR.erase X).parent = ladR.erase X.parent) ∧
    (PromotionCapReceipt ladR v5env ladrho ladO v5T ladI) ∧
    (RCap ladR ladS v5env ladrho ladO v5T (fun a => namedEntry (ladD.heightPair a)) (fun _ _ =>
      ladAllRows)) ∧
    (ladrho.honest.Nonempty) ∧
    (∀ rG ρbar, 12 ≤ v5T.action rG → (∀ r, 12 ≤ v5T.action r → rG ≤ r) → FrontierRepairAllowance
      ladR v5env ladrho ladO v5T ladI 12 1 4 ρbar (v5T.action (rG + 2)) → ∀ i ev m kind,
      FrontierSearchStart ladR v5env ladrho ladO v5T 12 i ev m kind → 12 + 2 * FGCompose.P v5T ≤
      ev.time → FrontierRepairAllowance ladR v5env ladrho ladO v5T ladI 12 1 4 ρbar (ev.time + 3
      * v5T.delta)) := by
  have service := fun u v m J c q Q Qfg hu hp he hh hsvc hseed htime hphase hg hhor hcap =>
    (frontierLocalServiceFG_frozen_iff ladR ladS v5env ladrho ladO v5T ladI ladD.heightPair
      (Equiv.ofUnique (Fin 1) Unit) (fun _ => Subsingleton.elim _ _) q Q Qfg m v).2
      (ladserviceLeaf u v m J c q Q Qfg hu hp he hh hsvc hseed htime hphase hg hhor hcap)
  have common := fun u m J c q Q Qfg r hu hp he hsvc hseed htime hqr hfirst hphase => by
    obtain ⟨hc, rest⟩ := ladcommon u m J c q Q Qfg r hu hp he hsvc hseed htime hqr hfirst hphase
    exact And.intro ((openingCoveredFG_frozen_iff ladR ladS v5env ladrho ladO.height v5T
      ladD.heightPair (Equiv.ofUnique (Fin 1) Unit) (fun _ => Subsingleton.elim _ _) r Q).2 hc) rest
  exact ⟨v5TLaws, le_rfl, ladcrossing, ladschedule, ladmono, ladawake, ladjoinedTick, ladready,
    ladservices, ladreceiptHeld, ladfault, le_rfl, rfl, ladgap, ladJst, ladG, ladslot, ladread,
    ladorder, ladsigner, ladsourceParent, ladrowsReceipt, ladprogressCoverage, v9foldAdvance,
    ladquorum, ladentryAgreement, ladsourceSlot, ladancestorSlot, v9erase_reflect, ladfloor,
    ladgateCopy, service, common, ladheldSlot, ladproposalSlot, ladjustified,
    ladparentFrame, v9erase_parent, ladcapReceipt, ladcap, ladne, ladtransfer⟩

#print axioms frozen_premises_sat

private theorem frozen_full_bridge :
    FrontierSearchStatement ladR ladS v5env ladrho ladO v5T ladI ladD.heightPair 12 1 4 4 1 := by
  obtain ⟨hT, hk, crossing, schedule, mono, awake, joinedTick, readyCut, hServices,
    receiptHeld, faultWeight, deltaF, hdelta, gap, hJst, hG, slotProposal, read, order,
    signer, sourceParent, rowsReceipt, progressCoverage, hfold, honestQuorum, entryAgreement,
    sourceSlot, ancestorSlot, eraseReflect, floor, gateCopy, service, common, heldSlot,
    proposalSlot, justifiedSource, parentFrame, eraseParent, capReceipt, cap, hne, transfer⟩ :=
    frozen_premises_sat
  exact frontierSearch_holder (R := ladR) (S := ladS) (O := ladO) (T := v5T)
    (E := v5env) (rho := ladrho)
    (I := ladI) (D := ladD) (Ef := v5E) (decodeProposal := laddecode) (bodyErase := id)
    (bodyRows := fun _ => []) (blockWireRows := fun _ => []) (parentFG := ladparentFG)
    (parentHeight := ladparentHeight) (validFor := ladvalidFor) (fold := ladfold) (Jst := 12)
    (leaseSlots := 1) (obs := ladobs) (cert := v5cert) (inv := ladinv) (justif := v5justif)
    (keep := ladkeep) (positive := by decide) (coreLaws := ladcore)
    (erasePreceq := fun h => v5erase_mono h) (joined := fun _ => true) (receipt := ladreceipt)
    (chainRows := fun _ _ => ladAllRows) (G := 4) (ΔF := 1) (deltaT := 4)
    hT hk crossing schedule mono awake joinedTick readyCut hServices receiptHeld faultWeight
    deltaF hdelta gap hJst hG slotProposal read order signer sourceParent rowsReceipt
    progressCoverage hfold honestQuorum entryAgreement sourceSlot ancestorSlot eraseReflect
    floor gateCopy service common heldSlot proposalSlot justifiedSource parentFrame eraseParent
    capReceipt cap hne transfer

#print axioms frozen_full_bridge

private theorem frozen_selected_witness :
    (∃ j ev, timeIdx ladrho 30 ≤ j ∧ ladrho.events[j]? = some ev ∧
      ev.time ≤ 30 + frontierSearchRiseBudget v5T 4 1 7 ∧
      j = 44 ∧ ev = ladDel (ladp 4) 37) ∧
    ∃ rStar, ladHR rStar 5 ∧
      (∀ r, ladHR r 5 → rStar ≤ r) ∧ rStar = 4 ∧
      ∀ ρ : Time, ρ = 7 ∨ ρ = 8 → ∃ j ev, ladrho.events[j]? = some ev ∧
        j = 44 ∧ ev.time = 37 ∧
        v5T.action rStar ≤ ev.time + frontierSearchRowBudget v5T 4 1 ρ := by
  obtain ⟨h1, h2, h3, h4, h5, ha7, ha8, _, hd7, hd8, hH, _⟩ := ladSearch_premises_sat
  obtain ⟨hrise, hrow⟩ := (FrontierSearchStatement_def ladR ladS v5env ladrho ladO v5T ladI
    ladD.heightPair 12 1 4 4 1).mp frozen_full_bridge rfl ⟨by decide⟩ 1 30 4
      h1 h2 h3 h4 h5 ladrowCap
  refine ⟨?_, ?_⟩
  · obtain ⟨j, ev, hj, hev, ht, hh, hcap⟩ := hrise 7 ha7 (by decide +kernel)
    obtain ⟨rfl, rfl⟩ := ladriseWitness hj hev hh hcap
    exact ⟨_, _, hj, hev, ht, rfl, rfl⟩
  · obtain ⟨rStar, hr, hfirst, hall⟩ := hrow ⟨7, ha7, by decide +kernel⟩
    have hr4 : rStar = 4 := (ladrow5 rStar).mp hr
    refine ⟨rStar, hr, hfirst, hr4, ?_⟩
    rintro ρ (rfl | rfl)
    · obtain ⟨j, ev, hj, hev, _, hh, hcap, hrowt⟩ := hall 7 ha7 (by decide +kernel)
      obtain ⟨rfl, rfl⟩ := ladriseWitness hj hev hh hcap
      exact ⟨_, _, hev, rfl, rfl, hrowt⟩
    · obtain ⟨j, ev, hj, hev, _, hh, hcap, hrowt⟩ := hall 8 ha8 (by decide +kernel)
      obtain ⟨rfl, rfl⟩ := ladriseWitness hj hev hh hcap
      exact ⟨_, _, hev, rfl, rfl, hrowt⟩


#print axioms frozen_selected_witness

end AvailableChain.FGCompose.Tests.POP6bFrozen
end
