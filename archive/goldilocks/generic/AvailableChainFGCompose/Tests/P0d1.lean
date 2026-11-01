module
public import AvailableChainFGCompose.Proofs.Healing.PhaseSettle

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.P0d1
open AvailableChain.SimplexFG AvailableChain.KitFG

-- An inhabited event-fold interface model. This is not an FG-SA ExecutionValid fixture.
-- The separate FG-SA test checks the full law and receipt producers.
private def d1A : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 []
private def d1B : FGBlock (Fin 1) := .node .genesis 1 ⟨2⟩ 0 []
private def d1C : FGBlock (Fin 1) := .node d1A 2 ⟨3⟩ 0 []
private def d1D : FGBlock (Fin 1) := .node d1B 2 ⟨4⟩ 0 []
private def d1E : FGBlock (Fin 1) := .node d1C 3 ⟨5⟩ 0 []

private def d1Height (W : FGBlock (Fin 1)) : FGHeight (Fin 1) :=
  if W = d1E then ⟨W, W.slot, 4, W, ∅, ∅, 2, d1A⟩
  else if W = d1C ∨ W = d1D then ⟨W, W.slot, 3, W, ∅, ∅, 2, W.parent⟩
  else if W = d1A ∨ W = d1B then ⟨W, W.slot, 2, W, ∅, ∅, 0, .genesis⟩
  else ⟨W, W.slot, 1, .genesis, ∅, ∅, 0, .genesis⟩

private abbrev d1Protocol (first next : Store (Fin 1)) : V2.ProtocolSpecD Unit where
  State := Store (Fin 1)
  Label := Unit
  Duty := Empty
  signLabel _ := ()
  seats _ := 1
  Payload := Unit
  Durable := Store (Fin 1)
  init := first
  clock st _ := st
  actTime d := nomatch d
  duties _ := []
  duties_spec d := nomatch d
  duties_nodup _ := List.nodup_nil
  act _ d := nomatch d
  gossip _ _ := []
  process _ _ := next
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

private def d1Core (first next : Store (Fin 1)) :
    FGCoreReads (d1Protocol first next) 1 Unit Unit Unit where
  core nd := ⟨(), nd, [], []⟩
  erase _ := .genesis
  source _ := none
  headVote _ _ := .genesis
  finalityHead _ := none
  proposalFG _ _ := none

private def d1Obs (first next : Store (Fin 1)) :
    FGObservationReads (d1Core first next) where
  height := d1Height
  finality _ := ⟨.genesis, 0⟩
  controls nd := treeStoreControlsView d1Height nd
  viable nd X := treeStoreFrameView d1Height nd X

private abbrev d1Env : Generic.Env Unit where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake _ _ := true

private def d1Trace (first next : Store (Fin 1)) :
    V2.D.Run Unit (d1Protocol first next) where
  honest := {()}
  horizon := 10
  events := [.deliver () ⟨.seat () 0, ()⟩ 1, .deliver () ⟨.seat () 0, ()⟩ 5, .tick () 6]
  seatOf _ _ := ()
  input _ _ := ()

private def d1Initial : Store (Fin 1) := Store.init
private def d1Contest (J : FGBlock (Fin 1)) : Store (Fin 1) :=
  ⟨{.genesis, d1A, d1B, d1C, d1D}, .genesis, J, 2, 3⟩
private def d1OnlyA : Store (Fin 1) := ⟨{.genesis, d1A, d1C}, .genesis, d1A, 2, 3⟩
private def d1Gap (F : FGBlock (Fin 1)) : Store (Fin 1) :=
  ⟨{.genesis, d1A, d1C, d1E}, F, d1A, 2, 4⟩

private theorem d1G0_observations (a b : Store (Fin 1)) :
    FGObservationLaws (d1Core a b) (d1Obs a b) := ⟨fun _ => rfl, fun _ _ => rfl⟩

private theorem d1G0_m1 :
    AttemptPhaseAt (d1Core d1Initial d1Initial) d1Env (d1Trace d1Initial d1Initial)
      (d1Obs d1Initial d1Initial) 0 1 .topJ ∧
      ((d1Obs d1Initial d1Initial).controls d1Initial).J = .genesis  := by
  simp only [AttemptPhaseAt, TopEvidence, ContestEvidence, d1Trace, Finset.mem_singleton]
  decide +kernel

private theorem d1G0_quiet_lower_F :
    (d1Gap .genesis).F ≠ (d1Gap d1A).F ∧
    ¬ EffectiveEvent (d1Core (d1Gap .genesis) (d1Gap d1A)) d1Env
      (d1Trace (d1Gap .genesis) (d1Gap d1A)) (d1Obs (d1Gap .genesis) (d1Gap d1A)) 0  := by
  simp only [EffectiveEvent, TopEvidence, ContestEvidence, d1Trace, Finset.mem_singleton]
  decide +kernel

private theorem d1G0_fixed_frontier_top :
    let R := d1Core d1OnlyA (d1Contest d1B)
    let rho := d1Trace d1OnlyA (d1Contest d1B)
    frontierAtIdx R d1Env rho 0 = 3 ∧ frontierAtIdx R d1Env rho 1 = 3 ∧
      TopEvidence R d1Env rho 0 3 ∧ TopEvidence R d1Env rho 1 3  := by
  dsimp only
  simp only [TopEvidence, d1Trace, Finset.mem_singleton]
  decide +kernel

private theorem d1G0_changed_J_contest :
    let a := d1Contest d1A
    let b := d1Contest d1B
    let R := d1Core a b
    let rho := d1Trace a b
    a.J ≠ b.J ∧ ContestEvidence R d1Env rho (d1Obs a b) 0 3 ∧
      ContestEvidence R d1Env rho (d1Obs a b) 1 3  := by
  dsimp only
  simp only [ContestEvidence, d1Trace, Finset.mem_singleton]
  decide +kernel

-- Negative: equal frontier and cached J do not replace cumulative witness retention.
private theorem d1G0_without_keep_loses_contest :
    let a := d1Contest d1A
    let R := d1Core a d1OnlyA
    let rho := d1Trace a d1OnlyA
    ¬ a.TF ⊆ d1OnlyA.TF ∧
      frontierAtIdx R d1Env rho 0 = frontierAtIdx R d1Env rho 1 ∧
      ContestEvidence R d1Env rho (d1Obs a d1OnlyA) 0 3 ∧
      ¬ ContestEvidence R d1Env rho (d1Obs a d1OnlyA) 1 3  := by
  dsimp only
  simp only [ContestEvidence, d1Trace, Finset.mem_singleton]
  decide +kernel

private def d1ReceiptAtFive (_ : Block) (deadline : Time) (_ : Unit) : Prop := 5 < deadline

-- The tick at index 2 is real in the interface trace. Receipt at the deadline is too late.
private theorem d1G0_strict_receipt :
    ¬ WitnessReceiptScope (d1Core d1Initial d1Initial) d1Env
      (d1Trace d1Initial d1Initial) (fun _ => true) d1ReceiptAtFive .genesis 5 := by
  intro h
  have bad := h.atRead 2 () 6 (by decide) rfl rfl (by decide) (by decide)
  exact (by decide : ¬ (5 : Time) < 5) bad

private theorem d1G0_later_deadline_differs :
    WitnessReceiptScope (d1Core d1Initial d1Initial) d1Env
      (d1Trace d1Initial d1Initial) (fun _ => true) d1ReceiptAtFive .genesis 6 := by
  constructor
  intro _ _ _ _ _ _ _ _
  exact (by decide : (5 : Time) < 6)

-- A separate receipt model delivers the selected non-genesis body at time 5.
private def d1ReceiptBody : Block := .node .genesis 2 ⟨3⟩ 17
private def d1OtherBody : Block := .node .genesis 2 ⟨3⟩ 18

private abbrev d1ReceiptProtocol : V2.ProtocolSpecD Unit where
  State := Store (Fin 1)
  Label := Unit
  Duty := Empty
  signLabel _ := ()
  seats _ := 1
  Payload := Block
  Durable := Store (Fin 1)
  init := d1OnlyA
  clock st _ := st
  actTime d := nomatch d
  duties _ := []
  duties_spec d := nomatch d
  duties_nodup _ := List.nodup_nil
  act _ d := nomatch d
  gossip _ _ := []
  process st _ := st
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

private noncomputable def d1ReceiptCore : FGCoreReads d1ReceiptProtocol 1 Unit Unit Unit where
  core nd := ⟨(), nd, [], []⟩
  erase W := if W = d1C then d1ReceiptBody else .genesis
  source _ := none
  headVote _ _ := .genesis
  finalityHead _ := none
  proposalFG _ _ := none

private noncomputable def d1ReceiptTrace : V2.D.Run Unit d1ReceiptProtocol where
  honest := {()}
  horizon := 10
  events := [.deliver () ⟨.seat () 0, d1ReceiptBody⟩ 5, .tick () 6]
  seatOf _ _ := ()
  input _ _ := ()

private def d1BodyReceipt (B : Block) (deadline : Time) (y : Unit) : Prop :=
  d1ReceiptTrace.events[0]? = some (.deliver y ⟨.seat () 0, B⟩ 5) ∧ 5 < deadline

private def d1ReceiptJoined (st : Store (Fin 1)) : Bool := d1C ∈ st.TF

-- The selected carrier, delivery, joined tick, and both floor guards are inhabited.
private theorem d1G0_non_genesis_receipt_guards :
    d1C ≠ .genesis ∧ d1ReceiptCore.erase d1C = d1ReceiptBody ∧
    d1ReceiptBody ≠ .genesis ∧ () ∈ d1ReceiptTrace.honest ∧
    d1ReceiptTrace.events[0]? = some (.deliver () ⟨.seat () 0, d1ReceiptBody⟩ 5) ∧
    d1ReceiptTrace.events[1]? = some (.tick () 6) ∧
    d1ReceiptJoined (d1ReceiptProtocol.clock
      (d1ReceiptTrace.stateBefore d1Env 1 ()) 6) = true ∧
    Block.Preceq (d1ReceiptCore.erase
      (d1ReceiptCore.core (d1ReceiptTrace.stateBeforeTime d1Env 5 ())).fg.F)
      (d1ReceiptCore.erase d1C) ∧
    Block.Preceq (d1ReceiptCore.erase
      (d1ReceiptCore.core (d1ReceiptTrace.stateBeforeTime d1Env 6 ())).fg.F)
      (d1ReceiptCore.erase d1C) := by
  decide +kernel

private theorem d1G0_body_receipt_strict_cuts :
    ¬ d1BodyReceipt (d1ReceiptCore.erase d1C) 5 () ∧
    d1BodyReceipt (d1ReceiptCore.erase d1C) 6 () ∧
    ¬ d1BodyReceipt .genesis 6 () ∧
    d1OtherBody.root = d1ReceiptBody.root ∧
    ¬ d1BodyReceipt d1OtherBody 6 () := by
  simp [d1BodyReceipt, d1ReceiptTrace, d1ReceiptCore, d1ReceiptBody, d1OtherBody,
    Block.root]

private theorem d1G0_non_genesis_receipt_rejected :
    ¬ WitnessReceiptScope d1ReceiptCore d1Env d1ReceiptTrace
      d1ReceiptJoined d1BodyReceipt d1C 5 := by
  intro h
  have bad := h.atRead 1 () 6 (by decide) rfl (by decide +kernel)
    (by decide) (by decide +kernel)
  exact d1G0_body_receipt_strict_cuts.1 bad

private theorem d1G0_non_genesis_receipt_accepted :
    WitnessReceiptScope d1ReceiptCore d1Env d1ReceiptTrace
      d1ReceiptJoined d1BodyReceipt d1C 6 := by
  constructor
  intro _ y _ _ _ _ _ _
  cases y
  exact d1G0_body_receipt_strict_cuts.2.1

#print axioms d1G0_non_genesis_receipt_guards
#print axioms d1G0_body_receipt_strict_cuts
#print axioms d1G0_non_genesis_receipt_rejected
#print axioms d1G0_non_genesis_receipt_accepted

private theorem d1G0_start_cut :
    let R := d1Core d1Initial d1OnlyA
    let rho := d1Trace d1Initial d1OnlyA
    frontierAtIdx R d1Env rho 0 = 1 ∧ frontierAtIdx R d1Env rho (0 + 1) = 3  := by
  decide +kernel

-- The held block C is absent from this interface model's frozen HEAD read.
private def d1HeadTiming : FGTiming :=
  ⟨1, 2, fun _ => 0, fun _ => 6, fun _ => 2, fun _ => 3,
    fun _ => 5, fun _ => 6, fun _ => 6⟩

private def d1FrozenRead (nd : Store (Fin 1)) (_ : Slot) : Finset (FGBlock (Fin 1)) :=
  nd.TF.filter (fun W => W ≠ d1C)

private theorem d1G0_held_not_frozen :
    d1C ∈ d1OnlyA.TF ∧ d1C ∉ d1FrozenRead d1OnlyA 1 := by
  decide +kernel

-- A cumulative-TF read cannot satisfy the required native-read projection.
private theorem d1G0_cumulative_not_native :
    ¬ (fun (nd : Store (Fin 1)) (_ : Slot) => nd.TF) = d1FrozenRead := by
  intro h
  have he := congrFun (congrFun h d1OnlyA) 1
  exact d1G0_held_not_frozen.2 (he ▸ d1G0_held_not_frozen.1)

-- All bridge guards are inhabited: strict cut 2, actual tick 6, and frontier 3.
-- Held membership alone cannot supply frozenHeadMem for the native read.
private theorem d1G0_without_frozenHeadMem :
    let R := d1Core d1OnlyA d1OnlyA
    let rho := d1Trace d1OnlyA d1OnlyA
    let O := d1Obs d1OnlyA d1OnlyA
    ¬ (∀ d y (W : FGBlock (Fin 1)) s nd,
      (0 : Time) ≤ d → 0 < d → y ∈ rho.honest →
      frontierAtIdx R d1Env rho (timeIdx rho (d1HeadTiming.vote s)) ≤ (O.height W).h →
      d ≤ d1HeadTiming.vote s → d ≤ d1HeadTiming.freeze (s - 1) →
      W ∈ (R.core (rho.stateBefore d1Env (rho.idxBefore d) y)).fg.TF →
      postClock d1Env rho y (d1HeadTiming.vote s) = some nd →
      W ∈ d1FrozenRead nd s) := by
  dsimp only
  intro frozenHeadMem
  have bad := healing_phase_head_inclusion
    (R := d1Core d1OnlyA d1OnlyA) (E := d1Env) (rho := d1Trace d1OnlyA d1OnlyA)
    (O := d1Obs d1OnlyA d1OnlyA) (T := d1HeadTiming) (Jst := 0)
    d1FrozenRead frozenHeadMem (d := 2) (y := ()) (W := d1C) (s := 1) (nd := d1OnlyA)
    (by decide) (by decide) (by decide) (by decide +kernel)
    (by decide) (by decide) (by decide +kernel) (by rfl)
  exact d1G0_held_not_frozen.2 bad

#print axioms d1G0_held_not_frozen
#print axioms d1G0_cumulative_not_native
#print axioms d1G0_without_frozenHeadMem

#print axioms d1G0_observations
#print axioms d1G0_m1
#print axioms d1G0_quiet_lower_F
#print axioms d1G0_fixed_frontier_top
#print axioms d1G0_changed_J_contest
#print axioms d1G0_without_keep_loses_contest
#print axioms d1G0_strict_receipt
#print axioms d1G0_later_deadline_differs
#print axioms d1G0_start_cut

end AvailableChain.FGCompose.Tests.P0d1
end
