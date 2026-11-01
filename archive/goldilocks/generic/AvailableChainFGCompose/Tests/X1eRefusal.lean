module
public import AvailableChainFGCompose.Proofs.ExecutionAcceptanceOrdinary

set_option linter.privateModule false

public section

namespace AvailableChain.FGCompose.Tests.X1eRefusal
open AvailableChain AvailableChain.FGCompose AvailableChain.SimplexFG AvailableChain.KitFG
private abbrev aE : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private abbrev aCfg : FGConfig := ⟨4⟩
private abbrev aBoot : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private abbrev aU : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 [aBoot]
private abbrev aTarget : Row (Fin 1) := ⟨0, .vote 2 ⟨1⟩ false, none⟩
private abbrev aD : FGBlock (Fin 1) := .node aU 2 ⟨2⟩ 0 [aTarget]
private abbrev aSigned : Row (Fin 1) := ⟨0, .vote 3 ⟨2⟩ false, some ⟨2, ⟨1⟩⟩⟩
private abbrev aX : FGBlock (Fin 1) := .node aD 6 ⟨6⟩ 0 [aSigned]

private def aErase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node p s r x rs => .node (aErase p) s r (encFGBody x rs)

private abbrev aP : V2.ProtocolSpecD Unit where
  State := SimplexFG.Store (Fin 1)
  Label := Nat
  Duty := Nat
  signLabel := id
  seats _ := 1
  Payload := FGBlock (Fin 1)
  Durable := SimplexFG.Store (Fin 1)
  init := SimplexFG.Store.init
  clock st _ := st
  actTime s := (s : Time)
  duties t := if 0 ≤ t then [t.toNat] else []
  duties_spec s t := by
    split
    · next ht =>
      simp only [List.mem_singleton]
      constructor
      · intro hs; subst s; exact Int.toNat_of_nonneg ht
      · intro hs; subst t; simp
    · next ht =>
      constructor
      · intro hm; cases hm
      · intro hs; exact False.elim (ht (hs ▸ Int.natCast_nonneg s))
  duties_nodup t := by split <;> simp
  act _ _ _ := none
  gossip _ _ := []
  process st o := SimplexFG.Window.on_block aE aCfg 2 st o.payload
  selfVisible _ := true
  recordOwn st _ := st
  durable st := st
  restore st _ := st
  wellFormed _ := true
  depsPresent _ _ := true
  processed _ _ := false
  excludes _ _ := false
  handles _ _ _ := False
  carries _ _ := False

private noncomputable abbrev aObj (B : FGBlock (Fin 1)) : aP.Object := ⟨.none, B⟩
private abbrev aEnv : Generic.Env Unit :=
  ⟨10, by decide, 0, le_rfl, fun _ t => decide (t = 1 ∨ t = 2 ∨ t = 3)⟩

/-- Ordered deliveries U, D, X, then a restart. `early` delivers X before its parent. -/
private noncomputable abbrev aRun (early : Bool) : V2.D.Run Unit aP where
  honest := {()}
  horizon := 10
  events := if early then [.deliver () (aObj aX) 1, .deliver () (aObj aU) 2,
      .deliver () (aObj aD) 3, .restart () 4]
    else [.deliver () (aObj aU) 1, .deliver () (aObj aD) 2,
      .deliver () (aObj aX) 3, .restart () 4]
  seatOf _ _ := ()
  input _ _ := ()


-- Same non-genesis child and window protocol as the accepted receipt fixture.
-- Awake delivery, original token, horizon 10. The parent is absent at event zero.
private theorem delivery_marked :
    (ordinaryFGExecutionObs aEnv (aRun true)).accepts () 0
      (fgEventToken (aRun true) () 0 (aObj aX) 1) :=
  ⟨0, aObj aX, 1, rfl, rfl, rfl⟩

private theorem child_refused :
    SimplexFG.Window.on_block aE aCfg 2 Store.init aX = Store.init := by
  apply KitFG.Window.window_on_block_of_refused
  exact Or.inr (Or.inl (by decide +kernel))

private theorem claimed_leaf_effect_impossible :
    (ordinaryFGExecutionObs aEnv (aRun true)).cutState () 1 ≠
      SimplexFG.Window.update_finality aE aCfg 2
        { (ordinaryFGExecutionObs aEnv (aRun true)).cutState () 0 with
          TF := insert aX ((ordinaryFGExecutionObs aEnv (aRun true)).cutState () 0).TF } aX := by
  intro h
  have ht := congrArg (fun st : Store (Fin 1) => st.TF) h
  have hne :
      ((ordinaryFGExecutionObs aEnv (aRun true)).cutState () 1).TF ≠
        (SimplexFG.Window.update_finality aE aCfg 2
          { (ordinaryFGExecutionObs aEnv (aRun true)).cutState () 0 with
            TF := insert aX ((ordinaryFGExecutionObs aEnv (aRun true)).cutState () 0).TF }
          aX).TF := by decide +kernel
  exact hne ht

#print axioms delivery_marked
#print axioms child_refused
#print axioms claimed_leaf_effect_impossible

private noncomputable abbrev aR : FGCoreReads aP 1 Unit Unit (Row (Fin 1)) where
  core st := ⟨(), st, [], []⟩
  erase := aErase
  source _ := none
  headVote _ _ := .genesis
  finalityHead _ := none
  proposalFG _ o := some o.payload

private noncomputable abbrev aS : FGSafetyReads aP 1 (Row (Fin 1)) where
  proposalErase o := some (aErase o.payload)
  proposalRows o := o.payload.rows
  encode _ := aObj aX
  decode := some
  decodeObject _ := none
  fgLabel := 0
  fgSeats := Equiv.refl _
  record _ := RecordOnce.initial
  inputs _ := (none, ⟨0, genesisRoot, 0⟩)
  enabled _ := false
  finalizedOut st := aErase st.F

private noncomputable abbrev aH : FGHistoricalReads aP.State (FGBlock (Fin 1)) where
  acceptedBlocks st := st.TF.image aErase
  acceptedBodies st := [.genesis, aU, aD, aX].filter (fun B => B ∈ st.TF)
  erase := aErase
  root := FGBlock.root
  parent := FGBlock.parent
  slot := FGBlock.slot
  readBlock st := historicalLookup FGBlock.root
    ([.genesis, aU, aD, aX].filter (fun B => B ∈ st.TF))
  preceq := FGBlock.Preceq
  depth B := (aErase B).depth
  lca A B := Block.meet (aErase A) (aErase B)

private noncomputable abbrev aWr : FGDependencyWireReads aP (FGBlock (Fin 1))
    (Row (Fin 1)) where
  decodeBody o := some o.payload
  namedRoots o := some (o.payload.root, o.payload.parent.root)
  proposalErase o := some (aErase o.payload)
  decodedRows o := o.payload.rows
  bodyRows := FGBlock.rows

private theorem aSchedule : V2.D.ScheduleWellFormed aEnv (aRun false) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro v t h; simp at h
  · intro v hv t hp hn ht ha
    change decide (t = 1 ∨ t = 2 ∨ t = 3) = true at ha
    simp only [decide_eq_true_eq] at ha
    rcases ha with rfl | rfl | rfl
    all_goals obtain ⟨k, hk⟩ := hp
    all_goals change _ = (k : Int) * 10 at hk
    all_goals omega

private noncomputable def aSelected :
    FGSelectedAcceptance aR aS aEnv (aRun false) aH aWr
      (ordinaryFGExecutionObs aEnv (aRun false))
      (SimplexFG.Window.update_finality aE aCfg 2) () aX 4 :=
  ordinary_selectedAcceptance aR aS aEnv (aRun false) aH aWr aE aCfg 2
    (j := 2) (o := aObj aX) (t := 3) (b := aX) (by decide) rfl
    ⟨rfl, rfl, rfl, rfl, by decide, rfl, rfl, rfl, rfl⟩ rfl rfl (by decide)
    (by decide +kernel)

private theorem aSelected_step : aSelected.step = 6 :=
  (ordinary_selectedAcceptance_fields aR aS aEnv (aRun false) aH aWr aE aCfg 2
    (j := 2) (o := aObj aX) (t := 3) (d := 4) (b := aX) (W := aX) (by decide) rfl
    ⟨rfl, rfl, rfl, rfl, by decide, rfl, rfl, rfl, rfl⟩ rfl rfl (by decide)
    (by decide +kernel)).1

private theorem aSelected_token :
    aSelected.token = fgEventToken (aRun false) () 2 (aObj aX) 3 :=
  (ordinary_selectedAcceptance_fields aR aS aEnv (aRun false) aH aWr aE aCfg 2
    (j := 2) (o := aObj aX) (t := 3) (d := 4) (b := aX) (W := aX) (by decide) rfl
    ⟨rfl, rfl, rfl, rfl, by decide, rfl, rfl, rfl, rfl⟩ rfl rfl (by decide)
    (by decide +kernel)).2.2.1

private theorem aRetention : FGObservedFinalityLaws aR (aRun false)
    (ordinaryFGExecutionObs aEnv (aRun false)) where
  f_step x k hk := by
    cases x
    change k < 12 at hk
    interval_cases k <;> decide +kernel
  restore_f j x t he := by
    cases x
    rcases j with _ | _ | _ | _ | j
    all_goals simp at he
    subst t
    rfl

private theorem aEffect : FGAcceptanceEffectLaws aR aS aEnv (aRun false) aH aWr
    (ordinaryFGExecutionObs aEnv (aRun false)) aE aCfg 2 () aX 4 aSelected :=
  (ordinary_acceptanceEffect_iff aR aS aEnv (aRun false) aH aWr aE aCfg 2 aSelected).mpr
    ⟨by rw [aSelected_step]; decide +kernel, aRetention⟩

private theorem aGuards : FGAcceptanceGuards aR (ordinaryFGExecutionObs aEnv (aRun false))
    aE aCfg 2 () aSelected.step aX aU where
  invariant := by rw [aSelected_step]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
  finCmp := Or.inl (by rw [aSelected_step]; decide +kernel)
  jPath _ := Or.inl (by rw [aSelected_step]; decide +kernel)
  cap _ := by rw [aSelected_step]; decide +kernel

private theorem aNonempty : ¬ aE.IsQuorum ∅ := by
  unfold Electorate.IsQuorum
  decide +kernel

private theorem aFold : PendingFold_W aE aCfg 2 2 aU aX :=
  ⟨by decide, ⟨2, aU, ∅⟩, by decide +kernel, rfl, rfl, {0},
    by unfold Electorate.IsQuorum; decide +kernel,
    fun i _ => Or.inr ⟨aSigned, by decide, Subsingleton.elim _ _, rfl⟩⟩

/-- Exact ordinary run, successful receipt and all consumer premises; horizon exceeds 4. -/
private theorem ordinary_premises_sat :
    (aRun false).events = [.deliver () (aObj aU) 1, .deliver () (aObj aD) 2,
      .deliver () (aObj aX) 3, .restart () 4] ∧ 4 < (aRun false).horizon ∧
    (aRun false).honest = {()} ∧ V2.D.ScheduleWellFormed aEnv (aRun false) ∧
    FGExecutionObsLaws aEnv (aRun false) (ordinaryFGExecutionObs aEnv (aRun false)) ∧
    ¬ aE.IsQuorum ∅ ∧ 2 ≤ (2 : Nat) ∧
    FGAcceptanceEffectLaws aR aS aEnv (aRun false) aH aWr
      (ordinaryFGExecutionObs aEnv (aRun false)) aE aCfg 2 () aX 4 aSelected ∧
    FGAcceptanceGuards aR (ordinaryFGExecutionObs aEnv (aRun false))
      aE aCfg 2 () aSelected.step aX aU ∧ PendingFold_W aE aCfg 2 2 aU aX :=
  ⟨rfl, by decide, rfl, aSchedule, ordinaryFGExecutionObs_laws aEnv (aRun false),
    aNonempty, le_rfl, aEffect, aGuards, aFold⟩

private theorem ordinary_acceptance :
    aSelected.token.receiptTime < 4 ∧ AcceptsFinalBefore aR aEnv (aRun false) () aU 4 :=
  acceptBefore_ordinary aR aS aEnv (aRun false) aH aWr aE aCfg 2 aNonempty le_rfl
    aSchedule () aX aU 4 aSelected aEffect (by decide) (by decide +kernel) aGuards

private theorem ordinary_pending :
    aSelected.token.receiptTime < 4 ∧ AcceptsFinalBefore aR aEnv (aRun false) () aU 4 :=
  finalizePending_ordinary aR aS aEnv (aRun false) aH aWr aE aCfg 2 aNonempty le_rfl
    aSchedule () 2 aU aX 4 aSelected aEffect (by decide) aFold aGuards

/-- At the boundary the SAME successful receipt and accepting leaf have time 3.
The selected insertion and guards still hold, but the strict read excludes that event. -/
private theorem ordinary_deadline_rejected :
    aSelected.token.receiptTime = 3 ∧
    (ordinaryFGExecutionObs aEnv (aRun false)).cutTime () aSelected.step = 3 ∧
    ¬ aSelected.token.receiptTime < 3 ∧
    ¬ AcceptsFinalBefore aR aEnv (aRun false) () aU 3 := by
  rw [aSelected_step, aSelected_token]
  unfold AcceptsFinalBefore Gen.V2.Duty.HoldsBefore
  decide +kernel

#print axioms ordinary_premises_sat
#print axioms ordinary_acceptance
#print axioms ordinary_pending
#print axioms ordinary_deadline_rejected

end AvailableChain.FGCompose.Tests.X1eRefusal
end
