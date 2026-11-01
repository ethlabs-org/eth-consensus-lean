module
public import AvailableChainFGCompose.Proofs.ExecutionAcceptance

set_option linter.privateModule false

public section

/-! Finite driver-interface executions, not concrete PC executions. States 2 and 3 keep
one queued child; state 4 completes its successful leaf. The old token is unchanged.
Both variants have the same receipts; the final event is a delivery or a restart. -/
namespace AvailableChain.FGCompose.Tests.X1e
open AvailableChain.SimplexFG AvailableChain.KitFG

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
  State := Nat
  Label := Unit
  Duty := Empty
  signLabel := Empty.elim
  seats _ := 1
  Payload := FGBlock (Fin 1)
  Durable := Nat
  init := 0
  clock st _ := st
  actTime := Empty.elim
  duties _ := []
  duties_spec d := Empty.elim d
  duties_nodup _ := List.nodup_nil
  act _ d _ := Empty.elim d
  gossip _ _ := []
  process st _ := st
  selfVisible _ := false
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
  ⟨10, by decide, 0, le_rfl, fun _ t => decide (t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4)⟩

private noncomputable abbrev aRun (restart : Bool) : V2.D.Run Unit aP where
  honest := {()}
  horizon := 10
  events := [.deliver () (aObj aU) 1, .deliver () (aObj aX) 2,
    .deliver () (aObj aD) 3, if restart then .restart () 4 else .deliver () (aObj aD) 4]
  seatOf _ _ := ()
  input _ _ := ()

private def aStore (st : Nat) : Store (Fin 1) :=
  let u := SimplexFG.Window.on_block aE aCfg 2 Store.init aU
  let d := SimplexFG.Window.on_block aE aCfg 2 u aD
  if st = 0 then Store.init else if st < 3 then u else if st = 3 then d
  else SimplexFG.Window.on_block aE aCfg 2 d aX

private noncomputable abbrev aR : FGCoreReads aP 1 Unit Unit (Row (Fin 1)) where
  core st := ⟨(), aStore st, [], []⟩
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
  fgLabel := ()
  fgSeats := Equiv.refl _
  record _ := RecordOnce.initial
  inputs _ := (none, ⟨0, genesisRoot, 0⟩)
  enabled _ := false
  finalizedOut st := aErase (aStore st).F

private noncomputable abbrev aH : FGHistoricalReads aP.State (FGBlock (Fin 1)) where
  acceptedBlocks st := (aStore st).TF.image aErase
  acceptedBodies st := [.genesis, aU, aD, aX].filter (fun B => B ∈ (aStore st).TF)
  erase := aErase
  root := FGBlock.root
  parent := FGBlock.parent
  slot := FGBlock.slot
  readBlock st := historicalLookup FGBlock.root
    ([.genesis, aU, aD, aX].filter (fun B => B ∈ (aStore st).TF))
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

private def aCut (k : Nat) : Nat :=
  if k < 1 then 0 else if k < 6 then 1 else if k < 11 then 2 else if k < 18 then 3 else 4

private noncomputable abbrev aToken (r : Bool) : FGReceiptToken Unit aP.Object :=
  fgEventToken (aRun r) () 1 (aObj aX) 2

private noncomputable abbrev aObs (r : Bool) : FGExecutionObs Unit aP where
  stateBefore j _ := if j < 4 then j else 4
  cutLength _ := 20
  cutState _ := aCut
  cutTime _ k := (k / 5 + 1 : Nat)
  start _ j := 5 * j
  entry _ j := 5 * j + 1
  duty _ j := 5 * j + 3
  done _ j := 5 * j + 3
  released _ _ := []
  finish _ st := st
  accepts _ k o := k = 17 ∧ o = aToken r
  ownWrites _ _ := []

private theorem aEvents (r : Bool) (j : Nat) (e : V2.Event Unit aP.Object)
    (he : (aRun r).events[j]? = some e) :
    (j = 0 ∧ e = .deliver () (aObj aU) 1) ∨
    (j = 1 ∧ e = .deliver () (aObj aX) 2) ∨
    (j = 2 ∧ e = .deliver () (aObj aD) 3) ∨
    (j = 3 ∧ e = if r then .restart () 4 else .deliver () (aObj aD) 4) := by
  rcases j with _ | _ | _ | _ | j
  all_goals simp at he
  all_goals subst he
  all_goals simp

private theorem aSchedule (r : Bool) : V2.D.ScheduleWellFormed aEnv (aRun r) := by
  refine ⟨by change (0 : Time) ≤ 10; decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases r <;> decide
  · cases r <;> decide
  · cases r <;> decide
  · cases r <;> decide
  · intro v t h
    cases r <;> simp at h
  · intro v hv t hp hn ht ha
    change decide (t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4) = true at ha
    simp only [decide_eq_true_eq] at ha
    rcases ha with rfl | rfl | rfl | rfl
    all_goals obtain ⟨k, hk⟩ := hp
    all_goals change _ = (k : Int) * 10 at hk
    all_goals omega

private theorem aLaws (r : Bool) : FGExecutionObsLaws aEnv (aRun r) (aObs r) where
  init_state _ := rfl
  start_state j e x he := by
    rcases aEvents r j e he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals rfl
  done_state j e x he := by
    rcases aEvents r j e he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals rfl
  cut_order j e x he := by
    have hj : j < 4 := by
      rcases aEvents r j e he with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
      all_goals decide
    change 5 * j < 5 * j + 1 ∧ 5 * j + 1 ≤ 5 * j + 3 ∧
      5 * j + 3 ≤ 5 * j + 3 ∧ 5 * j + 3 ≤ 20
    omega
  event_order i j ei ej x _ _ hij := by change 5 * i + 3 < 5 * j; omega
  segment_time j e x k he h1 h2 := by
    change 5 * j ≤ k at h1
    change k ≤ 5 * j + 3 at h2
    have hk : k / 5 = j := by omega
    change (k / 5 + 1 : Nat) = e.time
    rw [hk]
    rcases aEvents r j e he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals cases r <;> rfl
  tick_entry j x t he := by
    cases x
    rcases aEvents r j _ he with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
    all_goals cases r <;> cases h
  restart_entry j x t he := by
    cases x
    rcases aEvents r j _ he with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨rfl, h⟩
    all_goals cases r <;> cases h
    rfl
  released_tick j x t he := by
    cases x
    rcases aEvents r j _ he with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
    all_goals cases r <;> cases h
  released_other _ _ _ := rfl
  tick_done j x t he := by
    cases x
    rcases aEvents r j _ he with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
    all_goals cases r <;> cases h
  accept_origin x k o h := by
    obtain ⟨rfl, rfl⟩ := h
    cases x
    exact ⟨by change 17 < 20; decide, rfl, rfl, rfl, by change 5 ≤ 17; decide⟩
  accept_time x k o h := by obtain ⟨rfl, rfl⟩ := h; change (2 : Time) ≤ 4; decide
  tail_state j x hj := by
    change 4 ≤ j at hj
    change (if j < 4 then j else 4) = 4
    rw [ite_eq_right (by omega)]
  own_source x k h := (h rfl).elim
  own_state x k h := (h rfl).elim
  own_complete j x t _ := by
    change (List.range ((5 * j + 3) - (5 * j + 3))).flatMap (fun _ => []) = []
    rw [Nat.sub_self]; rfl

private theorem aFinality (r : Bool) : FGObservedFinalityLaws aR (aRun r) (aObs r) where
  f_step x k hk := by
    change k < 20 at hk
    interval_cases k <;> cases x <;> cases r <;> decide +kernel
  restore_f j x t he := by
    cases x
    rcases aEvents r j _ he with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨rfl, h⟩
    all_goals cases r <;> cases h
    exact KitFG.preceq_antisymm (KitFG.preceq_refl _) (KitFG.preceq_refl _)

private noncomputable def aSelected (r : Bool) :
    FGSelectedAcceptance aR aS aEnv (aRun r) aH aWr (aObs r)
      (SimplexFG.Window.update_finality aE aCfg 2) () aX 5 where
  step := 17
  eventIndex := 3
  token := aToken r
  body := aX
  honest := by change () ∈ ({()} : Finset Unit); decide
  accepts := ⟨rfl, rfl⟩
  origin := ⟨rfl, rfl, rfl, rfl, by change aEnv.awake () 2 = true; decide, rfl, rfl, rfl, rfl⟩
  erase_eq := rfl
  rows_eq := rfl
  segment := ⟨by change 15 ≤ 17; decide, by change 17 < 18; decide⟩
  event_some := ⟨_, rfl⟩
  before_deadline := by change (4 : Time) < 5; decide
  effect := by cases r <;> decide +kernel

private theorem aEffect (r : Bool) :
    FGAcceptanceEffectLaws aR aS aEnv (aRun r) aH aWr (aObs r)
      aE aCfg 2 () aX 5 (aSelected r) :=
  ⟨⟨(aSelected r).effect, by cases r <;> decide +kernel⟩, aFinality r⟩

private theorem aGuards (r : Bool) :
    FGAcceptanceGuards aR (aObs r) aE aCfg 2 () (aSelected r).step aX aU where
  invariant := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> cases r <;> decide +kernel
  finCmp := Or.inl (by cases r <;> decide +kernel)
  jPath _ := Or.inl (by cases r <;> decide +kernel)
  cap _ := by cases r <;> decide +kernel

private theorem aNonempty : ¬ aE.IsQuorum ∅ := by
  unfold Electorate.IsQuorum
  decide +kernel

private theorem aFold : PendingFold_W aE aCfg 2 2 aU aX :=
  ⟨by decide, ⟨2, aU, ∅⟩, by decide +kernel, rfl, rfl, {0},
    by unfold Electorate.IsQuorum; decide +kernel,
    fun i _ => Or.inr ⟨aSigned, by decide, Subsingleton.elim _ _, rfl⟩⟩

/-- The explicit pending field of the finite interface state, retaining the original token. -/
private noncomputable def aQueue (r : Bool) (st : Nat) : List (FGReceiptToken Unit aP.Object) :=
  if st = 2 ∨ st = 3 then [aToken r] else []

private theorem queued_storage_inspected (r : Bool) :
    aQueue r ((aObs r).cutState () 6) = [aToken r] ∧
    aQueue r ((aObs r).cutState () 16) = [aToken r] ∧
    aQueue r ((aObs r).cutState () 18) = [] := ⟨rfl, rfl, rfl⟩

/-- The exact finite runs inhabit every decisive acceptance/pending premise. -/
private theorem queued_premises_sat (r : Bool) :
    (aRun r).events = [.deliver () (aObj aU) 1, .deliver () (aObj aX) 2,
      .deliver () (aObj aD) 3, if r then .restart () 4 else .deliver () (aObj aD) 4] ∧
    5 < (aRun r).horizon ∧ (aRun r).honest = {()} ∧
    FGExecutionObsLaws aEnv (aRun r) (aObs r) ∧
    V2.D.ScheduleWellFormed aEnv (aRun r) ∧ ¬ aE.IsQuorum ∅ ∧ 2 ≤ (2 : Nat) ∧
    FGAcceptanceEffectLaws aR aS aEnv (aRun r) aH aWr (aObs r)
      aE aCfg 2 () aX 5 (aSelected r) ∧
    FGAcceptanceGuards aR (aObs r) aE aCfg 2 () (aSelected r).step aX aU ∧
    PendingFold_W aE aCfg 2 2 aU aX :=
  ⟨rfl, by change (5 : Time) < 10; decide, rfl, aLaws r, aSchedule r, aNonempty,
    le_rfl, aEffect r, aGuards r, aFold⟩

private theorem completed_restart_premises_sat :
    (aRun true).events = [.deliver () (aObj aU) 1, .deliver () (aObj aX) 2,
      .deliver () (aObj aD) 3, if true then .restart () 4 else .deliver () (aObj aD) 4] ∧
    5 < (aRun true).horizon ∧ (aRun true).honest = {()} ∧
    FGExecutionObsLaws aEnv (aRun true) (aObs true) ∧
    V2.D.ScheduleWellFormed aEnv (aRun true) ∧ ¬ aE.IsQuorum ∅ ∧ 2 ≤ (2 : Nat) ∧
    FGAcceptanceEffectLaws aR aS aEnv (aRun true) aH aWr (aObs true)
      aE aCfg 2 () aX 5 (aSelected true) ∧
    FGAcceptanceGuards aR (aObs true) aE aCfg 2 () (aSelected true).step aX aU ∧
    PendingFold_W aE aCfg 2 2 aU aX :=
  queued_premises_sat true

/-- Apply the named pending consumer, inspecting the same A rather than assuming coverage. -/
private theorem queued_acceptance (r : Bool) :
    (aSelected r).token.receiptTime < 5 ∧
    FGBlock.Preceq aU (aR.core ((aObs r).cutState () 18)).fg.F ∧
    AcceptsFinalBefore_obs aR (aRun r) (aObs r) () aU 5 ∧
    ∀ k, 17 < k → k ≤ 20 → FGBlock.Preceq aU (aR.core ((aObs r).cutState () k)).fg.F :=
  finalizePending_driver aR aS aEnv (aRun r) aH aWr (aObs r) aE aCfg 2 aNonempty
    le_rfl (aLaws r) (aSchedule r) () 2 aU aX 5 (aSelected r) (aEffect r)
    (by change (5 : Time) ≤ 10; decide) aFold (aGuards r)

/-- The acceptance consumer independently takes the carrier-finality premise. -/
private theorem queued_accept_before : AcceptsFinalBefore_obs aR (aRun false)
    (aObs false) () aU 5 :=
  (acceptBefore_driver aR aS aEnv (aRun false) aH aWr (aObs false) aE aCfg 2
    aNonempty le_rfl (aLaws false) (aSchedule false) () aX aU 5 (aSelected false)
    (aEffect false) (by decide) (by decide +kernel) (aGuards false)).2.2.1

/-- Inspect all five immutable token fields and the strictly later accepting event.
The child is absent before its leaf and present afterwards; its parent is now present. -/
private theorem queued_witness_inspected (r : Bool) :
    (aSelected r).token.receiver = () ∧ (aSelected r).token.wire = aObj aX ∧
    (aSelected r).token.eventIndex = 1 ∧ (aSelected r).token.receiptTime = 2 ∧
    (aSelected r).token.receiptEpoch = 0 ∧ (aSelected r).eventIndex = 3 ∧
    (aObs r).cutTime () (aSelected r).step = 4 ∧
    aX ∉ (aR.core ((aObs r).cutState () 17)).fg.TF ∧
    aX.parent ∈ (aR.core ((aObs r).cutState () 17)).fg.TF ∧
    aX ∈ (aR.core ((aObs r).cutState () 18)).fg.TF := by
  cases r <;> decide +kernel

/-- Restart keeps the raw state, then the completed drain admits the queued child.
The receiver is in a new epoch, but the selected token still has its receipt epoch zero. -/
private theorem completed_restart :
    (aRun true).events[3]? = some (.restart () 4) ∧
    (aObs true).cutState () ((aObs true).entry () 3) = 3 ∧
    (aObs true).cutState () ((aObs true).done () 3) = 4 ∧
    dependencyReceiverEpoch (aRun true) () 4 = 4 ∧
    (aSelected true).token.receiptEpoch = 0 ∧
    AcceptsFinalBefore_obs aR (aRun true) (aObs true) () aU 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, (queued_acceptance true).2.2.1⟩

private theorem prior_coverage_premises_sat :
    (aRun false).events = [.deliver () (aObj aU) 1, .deliver () (aObj aX) 2,
      .deliver () (aObj aD) 3, if false then .restart () 4 else .deliver () (aObj aD) 4] ∧
    5 < (aRun false).horizon ∧ (aRun false).honest = {()} ∧
    FGExecutionObsLaws aEnv (aRun false) (aObs false) ∧
    V2.D.ScheduleWellFormed aEnv (aRun false) ∧ ¬ aE.IsQuorum ∅ ∧ 2 ≤ (2 : Nat) ∧
    FGAcceptanceEffectLaws aR aS aEnv (aRun false) aH aWr (aObs false)
      aE aCfg 2 () aX 5 (aSelected false) ∧
    FGAcceptanceGuards aR (aObs false) aE aCfg 2 () (aSelected false).step aX aU ∧
    PendingFold_W aE aCfg 2 2 aU aX :=
  queued_premises_sat false

/-- Coverage at a later read does not make that read an accepting operation. -/
private theorem prior_coverage_not_acceptance :
    FGBlock.Preceq aU (aR.core ((aObs false).cutState () 19)).fg.F ∧
    ¬ ∃ o, (aObs false).accepts () 19 o := by
  refine ⟨(queued_acceptance false).2.2.2 19 (by decide) (by decide), ?_⟩
  rintro ⟨o, h, _⟩
  exact (by decide : ¬ (19 : Nat) = 17) h

private theorem strict_deadline_premises_sat :
    (aRun false).events = [.deliver () (aObj aU) 1, .deliver () (aObj aX) 2,
      .deliver () (aObj aD) 3, if false then .restart () 4 else .deliver () (aObj aD) 4] ∧
    5 < (aRun false).horizon ∧ (aRun false).honest = {()} ∧
    FGExecutionObsLaws aEnv (aRun false) (aObs false) ∧
    V2.D.ScheduleWellFormed aEnv (aRun false) ∧ ¬ aE.IsQuorum ∅ ∧ 2 ≤ (2 : Nat) ∧
    FGAcceptanceEffectLaws aR aS aEnv (aRun false) aH aWr (aObs false)
      aE aCfg 2 () aX 5 (aSelected false) ∧
    FGAcceptanceGuards aR (aObs false) aE aCfg 2 () (aSelected false).step aX aU ∧
    PendingFold_W aE aCfg 2 2 aU aX :=
  queued_premises_sat false

/-- The unchanged original receipt is exactly at deadline 2. All mechanics and guards
are inhabited at deadline 5, but the strict bound cannot be weakened to ≤ at deadline 2. -/
private theorem receipt_at_deadline_rejected :
    (aSelected false).token.receiptTime = 2 ∧
    ¬ (aSelected false).token.receiptTime < 2 ∧
    ¬ Nonempty (FGSelectedAcceptance aR aS aEnv (aRun false) aH aWr (aObs false)
      (SimplexFG.Window.update_finality aE aCfg 2) () aX 2) := by
  refine ⟨rfl, by decide, ?_⟩
  rintro ⟨A⟩
  have h := (aLaws false).accept_time () A.step A.token A.accepts
  have ht : A.token = aToken false := A.accepts.2
  rw [ht] at h
  have hb := A.before_deadline
  change (aObs false).cutTime () A.step < 2 at hb
  change (2 : Time) ≤ (aObs false).cutTime () A.step at h
  exact (not_lt_of_ge h) hb

#print axioms queued_storage_inspected
#print axioms queued_premises_sat
#print axioms completed_restart_premises_sat
#print axioms queued_acceptance
#print axioms queued_accept_before
#print axioms queued_witness_inspected
#print axioms completed_restart
#print axioms prior_coverage_premises_sat
#print axioms prior_coverage_not_acceptance
#print axioms strict_deadline_premises_sat
#print axioms receipt_at_deadline_rejected

end AvailableChain.FGCompose.Tests.X1e
end
