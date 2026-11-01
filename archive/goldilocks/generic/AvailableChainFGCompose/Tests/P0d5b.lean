module
public import AvailableChainFGCompose.Proofs.Healing.PromotionAge
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchHG2a

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.P0d5b
open AvailableChain.SimplexFG AvailableChain.KitFG

-- These are inhabited event-fold interface tests, not ExecutionValid claims.
-- The trace emits a signed row, has a quiet tick, and then raises the frontier.
private def d5bA : FGBlock (Fin 1) := .node .genesis 1 ⟨41⟩ 7 [⟨0, .vote 1 genesisRoot false, none⟩]
private def d5bB : FGBlock (Fin 1) := .node .genesis 1 ⟨42⟩ 8 [⟨0, .vote 1 genesisRoot false, none⟩]
private def d5bC : FGBlock (Fin 1) := .node d5bA 2 ⟨43⟩ 9 [⟨0, .vote 2 d5bA.root false, none⟩]
private def d5bD : FGBlock (Fin 1) := .node d5bB 2 ⟨44⟩ 10 [⟨0, .vote 2 d5bB.root false, none⟩]
private def d5bE : FGBlock (Fin 1) := .node d5bC 3 ⟨45⟩ 11 [⟨0, .vote 3 d5bC.root false, none⟩]
private def d5bF : FGBlock (Fin 1) := .node d5bD 3 ⟨46⟩ 12 [⟨0, .vote 3 d5bD.root false, none⟩]
private def d5bRow : Row (Fin 1) := ⟨0, .vote 3 d5bC.root false, some ⟨0, genesisRoot⟩⟩
private def d5bStopRow : Row (Fin 1) := ⟨0, .vote 4 d5bE.root true, some ⟨1, d5bA.root⟩⟩
private def d5bElectorate : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private def d5bHeight : FGHeightView (Fin 1) := simplexHeightView d5bElectorate ⟨0⟩
private def d5bErase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node P s root body _ => .node (d5bErase P) s root body
private def d5bPhase (contested : Bool) : Store (Fin 1) :=
  ⟨if contested then {.genesis, d5bA, d5bB, d5bC, d5bD} else {.genesis, d5bA, d5bC},
    .genesis, d5bA, 2, 3⟩
private def d5bHigh (contested : Bool) : Store (Fin 1) :=
  ⟨if contested then {.genesis, d5bA, d5bB, d5bC, d5bD, d5bE, d5bF}
    else {.genesis, d5bA, d5bC, d5bE}, .genesis, d5bC, 3, 4⟩
private def d5bKind (contested : Bool) : PhaseKind := if contested then .contest else .topJ
private def d5bLast (contested : Bool) : Time := if contested then 29 else 49

private abbrev d5bProtocol (contested : Bool) (first : Store (Fin 1)) :
    V2.ProtocolSpecD Unit where
  State := Store (Fin 1)
  Label := Nat
  Duty := Nat
  signLabel := id
  seats _ := 1
  Payload := Row (Fin 1)
  Durable := Store (Fin 1)
  init := first
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
  gossip _ _ := [d5bRow]
  process _ o := if o.payload = d5bStopRow then d5bHigh contested else d5bPhase contested
  selfVisible _ := false
  recordOwn st _ := st
  durable := id
  restore st _ := st
  wellFormed _ := true
  depsPresent _ _ := true
  processed _ _ := false
  excludes _ _ := false
  handles _ _ _ := False
  carries _ _ := False

private def d5bCore (b : Bool) (first : Store (Fin 1)) :
    FGCoreReads (d5bProtocol b first) 1 Unit Unit (Row (Fin 1)) where
  core nd := ⟨(), nd, [], []⟩
  erase := d5bErase
  source nd := if nd.h_max = 4 then some d5bE else some d5bC
  headVote nd _ := if nd.h_max = 4 then d5bErase d5bE else d5bErase d5bC
  finalityHead nd := if nd.h_max = 4 then some d5bE else some d5bC
  proposalFG _ _ := none
private def d5bSafety (b : Bool) (first : Store (Fin 1)) :
    FGSafetyReads (d5bProtocol b first) 1 (Row (Fin 1)) where
  proposalErase _ := none
  proposalRows _ := []
  encode a := ⟨.none, a⟩
  decode := some
  decodeObject o := some o.payload
  fgLabel := 0
  fgSeats := Equiv.refl _
  record _ := RecordOnce.initial
  inputs _ := (some d5bC, ⟨3, d5bC.root, 2⟩)
  enabled _ := true
  finalizedOut _ := .genesis
private def d5bObs (b : Bool) (first : Store (Fin 1)) :
    FGObservationReads (d5bCore b first) where
  height := d5bHeight
  finality _ := ⟨.genesis, 0⟩
  controls nd := treeStoreControlsView d5bHeight nd
  viable nd X := treeStoreFrameView d5bHeight nd X
private def d5bTiming : FGTiming where
  delta := 1
  roundSlots := 2
  proposal s := 4 * (s : Time)
  vote s := 4 * (s : Time) + 1
  early s := 4 * (s : Time) + 2
  freeze s := 4 * (s : Time) + 3
  release s := 4 * (s : Time) + 5
  gate s := 4 * (s : Time) + 6
  action r := 8 * (r : Time) + 6
private abbrev d5bEnv : Generic.Env Unit := ⟨6, by decide, 0, by decide, fun _ t =>
    decide (t = 1 ∨ t = 6 ∨ t = 29 ∨ t = 49)⟩
private def d5bTrace (b : Bool) : V2.D.Run Unit (d5bProtocol b Store.init) where
  honest := {()}
  horizon := d5bLast b
  events := [.deliver () ⟨.none, d5bRow⟩ 1, .tick () 6,
    .deliver () ⟨.none, d5bStopRow⟩ (d5bLast b)]
  seatOf _ _ := ()
  input _ _ := ()
private theorem d5bUnitExists (P : Unit → Prop) : (∃ x, P x) ↔ P () := by
  constructor
  · rintro ⟨x, h⟩
    cases x
    exact h
  · intro h
    exact ⟨(), h⟩

private theorem d5bFront (b : Bool) :
    frontierAtIdx (d5bCore b Store.init) d5bEnv (d5bTrace b) 1 = 3 := by
  cases b <;> decide +kernel
private theorem d5bTimingLaws : FGTimingLaws d5bTiming where
  delta_pos := by decide
  rounds := by decide
  proposal_eq s := by simp [d5bTiming]
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq r := by simp [d5bTiming]; ring

private theorem d5bSchedule (b : Bool) : V2.D.ScheduleWellFormed d5bEnv (d5bTrace b) where
  horizon_nonneg := by cases b <;> decide
  sorted := by cases b <;> decide
  nodup := by cases b <;> decide
  in_horizon := by
    intro e he
    simp only [d5bTrace, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> cases b <;> decide
  honest_only := by intro e he; simp [d5bTrace]
  tick_public := by
    intro v t ht
    have ht' : t = 6 := by simpa [d5bTrace] using ht
    subst t
    exact ⟨1, rfl⟩
  tick_total := by
    intro v hv t ht hn hh ha
    obtain ⟨k, hk⟩ := ht
    change t = (k : Time) * 6 at hk
    have ha' : t = 1 ∨ t = 6 ∨ t = 29 ∨ t = 49 := of_decide_eq_true ha
    have ht6 : t = 6 := by
      simp only [Time] at *
      omega
    subst t
    cases v
    simp only [d5bTrace, List.mem_cons, V2.Event.tick.injEq, reduceCtorEq,
      false_or]
    exact Or.inl ⟨True.intro, ht6⟩


private theorem d5bFirstRise (b : Bool) :
    FrontierRiseBy (d5bCore b Store.init) d5bEnv (d5bTrace b) 0 3 (d5bLast b) := by
  apply frontierSearch_first_rise _ _ _ (d5bSchedule b)
  · refine ⟨2, by decide, ?_, ?_⟩
    · cases b <;> decide
    · cases b <;> decide +kernel
  · exact (d5bFront b).le

-- G0 (first rise before maturity): the left HG.2a arm holds at the terminal deadline
-- for an entry whose earliest mature proposal (slot U.slot + 2R) is read after the rise.
private def d5bIface : V2.D.Interface (d5bProtocol false Store.init) where
  confirmed _ := .genesis
  stable _ := .genesis
  block _ := none
  opening _ := False
  propLabel s := s
  propDuty s := s
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective _ _ h := h

private def d5bLateEntry : FGBlock (Fin 1) := .node .genesis 20 ⟨47⟩ 13 []

private theorem d5bRiseBeforeMaturity :
    FrontierHG2aResult (d5bCore false Store.init) d5bEnv (d5bTrace false)
      (d5bObs false Store.init) d5bTiming d5bIface 8 1 0 3 5
      d5bLateEntry ∧
    d5bLast false < d5bTiming.proposal (d5bLateEntry.slot + 2 * d5bTiming.roundSlots) := by
  refine ⟨Or.inl (frontierSearch_rise_mono _ _ _ ?_ (d5bFirstRise false)), by decide⟩
  decide

-- G0 (entry age): the strict trigger gives carrier and maturity; at equality it does not.
private theorem d5bAgePositive :
    carrierTimeW d5bTiming 1 0 ≤ d5bTiming.proposal 5 ∧ 1 + 2 * 2 ≤ 5 := by
  obtain ⟨hc, hage⟩ := promotion_age_grid d5bTiming d5bTimingLaws 0 5 d5bA 1 (by decide)
  exact ⟨hc, healing_promotion_maturity d5bTiming d5bTimingLaws (δt := 2 * 2) rfl hage⟩

private theorem d5bAgeEqualityFails :
    ¬ (max ((0 : Nat) * FGCompose.P d5bTiming + betaF d5bTiming 1 - 4 * d5bTiming.delta)
      (d5bTiming.proposal d5bA.slot + 2 * FGCompose.P d5bTiming - 4 * d5bTiming.delta) <
        d5bTiming.proposal 4) ∧ ¬ (d5bA.slot + 2 * 2 ≤ 4) := by
  decide

-- G0 (target/progress priority, exact fixed batch): progress accepts either timeout bit
-- at the exact entry; target excludes timeout; another height or root is not the batch.
private theorem d5bPriority :
    NamesEntry Row.height_pair .progress d5bStopRow 4 d5bE ∧
    ¬ NamesEntry Row.height_pair .target d5bStopRow 4 d5bE ∧
    ¬ NamesEntry Row.height_pair .progress d5bStopRow 3 d5bE ∧
    ¬ NamesEntry Row.height_pair .progress d5bStopRow 4 d5bC := by
  refine ⟨⟨true, rfl⟩, ?_, ?_, ?_⟩
  · intro h; cases h
  · rintro ⟨t, h⟩; cases h
  · rintro ⟨t, h⟩
    injection h with _ hr _
    revert hr
    decide

-- G0 (strict receipt): an object processed exactly at d is not held before d.
private theorem d5bStrictReceipt :
    ¬ Gen.V2.Duty.HoldsBefore d5bEnv (d5bTrace false)
      (fun nd => d5bE ∈ ((d5bCore false Store.init).core nd).fg.TF) (d5bLast false) () ∧
    Gen.V2.Duty.HoldsBefore d5bEnv (d5bTrace false)
      (fun nd => d5bE ∈ ((d5bCore false Store.init).core nd).fg.TF) (d5bLast false + 1) () := by
  rw [Gen.V2.Duty.HoldsBefore_def, Gen.V2.Duty.HoldsBefore_def]
  constructor <;> decide +kernel

-- G0 (HG.2a budgets): the gate budget is 5Δ after the terminal budget, and the HG.4
-- guard bound is tight at its premises and fails one step past the opening bound.
private theorem d5bBudget :
    max (6 + Γ d5bTiming 8 + 4 * d5bTiming.delta + epsF d5bTiming 1)
      (8 + 2 * FGCompose.P d5bTiming + Γ d5bTiming 8 + 2 * d5bTiming.delta) =
    max (6 + Γ d5bTiming 8 - d5bTiming.delta + epsF d5bTiming 1)
      (8 + 2 * FGCompose.P d5bTiming + Γ d5bTiming 8 - 3 * d5bTiming.delta) +
        5 * d5bTiming.delta ∧
    max (10 + Γ d5bTiming 8 - d5bTiming.delta + epsF d5bTiming 1)
      (8 + 2 * FGCompose.P d5bTiming + Γ d5bTiming 8 - 3 * d5bTiming.delta) ≤
        14 + (2 * FGCompose.P d5bTiming + Γ d5bTiming 8 - 9 * d5bTiming.delta) := by
  exact ⟨frontierSearch_hg2a_gate_cost d5bTiming 8 1 6 8,
    frontierSearch_hg2a_bound d5bTiming d5bTimingLaws 8 1 14 10 8 ⟨by decide⟩
      (by decide) (by decide)⟩

private theorem d5bBudgetPastOpening :
    ¬ (max (19 + Γ d5bTiming 8 - d5bTiming.delta + epsF d5bTiming 6)
      (8 + 2 * FGCompose.P d5bTiming + Γ d5bTiming 8 - 3 * d5bTiming.delta) ≤
        14 + (2 * FGCompose.P d5bTiming + Γ d5bTiming 8 - 9 * d5bTiming.delta)) := by
  decide

#print axioms d5bRiseBeforeMaturity
#print axioms d5bAgePositive
#print axioms d5bAgeEqualityFails
#print axioms d5bPriority
#print axioms d5bStrictReceipt
#print axioms d5bBudget
#print axioms d5bBudgetPastOpening
end AvailableChain.FGCompose.Tests.P0d5b
end
