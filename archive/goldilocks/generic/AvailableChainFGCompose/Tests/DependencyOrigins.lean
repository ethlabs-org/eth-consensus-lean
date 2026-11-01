module
public import AvailableChainFGCompose.Proofs.Dependency
public import Mathlib.Tactic.IntervalCases -- shake: keep (own interval_cases use)
public import AvailableChainFGCompose.Proofs.ExecutionHistory

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.DependencyOrigins

/-- A finite interface model. This is not an ExecutionValid protocol fixture. -/
private noncomputable abbrev do_protocol : V2.ProtocolSpecD Unit where
  State := Nat
  Label := Unit
  Duty := Empty
  signLabel := Empty.elim
  seats := fun _ => 1
  Payload := Fin 4
  Durable := Nat
  init := 0
  clock := fun st _ => st
  actTime := Empty.elim
  duties := fun _ => []
  duties_spec := by intro d; cases d
  duties_nodup := by intro _; exact List.nodup_nil
  act := fun _ d _ => Empty.elim d
  gossip := fun _ _ => []
  process st wire := if st = 0 ∧ wire.payload = 2 then 1
    else if st = 1 ∧ wire.payload = 1 then 6 else st
  selfVisible := fun _ => false
  recordOwn := fun st _ => st
  durable := id
  restore := fun st _ => st
  wellFormed wire := decide (wire.payload ≠ 3)
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

private noncomputable abbrev do_leafProtocol : V2.ProtocolSpecD Unit :=
  { do_protocol with process := fun st wire =>
    if st = 2 ∧ wire.payload = 1 then 3
    else if st = 3 ∧ wire.payload = 2 then 4 else st }

private noncomputable abbrev do_env : Generic.Env Bool where
  Δ := 3
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ _ => true

private noncomputable abbrev do_wire (b : Fin 4) : do_protocol.Object := ⟨.seat () 0, b⟩

private noncomputable abbrev do_run : V2.D.Run Bool do_protocol where
  honest := {false}
  horizon := 10
  events := [.deliver false (do_wire 2) 0, .restart false 1,
    .deliver false (do_wire 1) 1, .tick false 4]
  seatOf := fun _ _ => false
  input := fun _ _ => ()

private noncomputable abbrev do_body (b : Fin 4) : Block :=
  if b = 0 then .genesis else if b = 1 then .node .genesis 1 ⟨1⟩ 0
  else .node (.node .genesis 1 ⟨1⟩ 0) 2 ⟨2⟩ 0

private noncomputable abbrev do_history : FGHistoricalReads Nat (Fin 4) where
  acceptedBlocks st := (if 4 ≤ st then [do_body 0, do_body 1, do_body 2]
    else if 3 ≤ st then [do_body 0, do_body 1] else [do_body 0]).toFinset
  acceptedBodies st := if 4 ≤ st then [0, 1, 2] else if 3 ≤ st then [0, 1] else [0]
  erase := do_body
  root b := (do_body b).root
  parent b := if b = 2 ∨ b = 3 then 1 else 0
  slot b := (do_body b).slot
  readBlock _ _ := none
  preceq b c := Block.Preceq (do_body b) (do_body c)
  depth b := (do_body b).depth
  lca b c := Block.meet (do_body b) (do_body c)

private noncomputable abbrev do_wireReads : FGDependencyWireReads do_protocol (Fin 4) Nat where
  decodeBody wire := some wire.payload
  namedRoots wire := some (do_history.root wire.payload,
    do_history.root (do_history.parent wire.payload))
  proposalErase wire := some (do_body wire.payload)
  decodedRows wire := [wire.payload.val]
  bodyRows b := [b.val]

private noncomputable abbrev do_child : FGReceiptToken Bool do_protocol.Object :=
  ⟨false, 0, do_wire 2, 0, 0⟩
private noncomputable abbrev do_parent : FGReceiptToken Bool do_protocol.Object :=
  ⟨false, 2, do_wire 1, 1, 2⟩

private noncomputable abbrev do_reads : FGDependencyReads Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) Nat where
  accepted st b := b = 0 ∨ (b = 1 ∧ 3 ≤ st) ∨ (b = 2 ∧ 4 ≤ st)
  refused _ _ _ _ := False
  pending st b o := (b = 2 ∧ 1 ≤ st ∧ st < 4 ∧ o = do_child) ∨
    (b = 1 ∧ st = 2 ∧ o = do_parent)
  originAvailable st b o := (b = 2 ∧ 1 ≤ st ∧ o = do_child) ∨
    (b = 1 ∧ 2 ≤ st ∧ o = do_parent)
  validBody b := b ≠ 3
  priorChecks st b := (b = 1 ∧ st = 2) ∨ (b = 2 ∧ st = 3)
  timely _ _ := True
  conflictsFinal _ _ := False
  latest := id
  notified st b := b = 0 ∨ (b = 1 ∧ 5 ≤ st) ∨ (b = 2 ∧ 6 ≤ st)
  matching _ b := b = 2
  companionHeld st b := b = 2 ∧ 6 ≤ st
  latestKey _ _ := some (2, do_history.root 2)
  latestCompanion st _ := if 6 ≤ st then some 2 else none

private noncomputable abbrev do_leaf : FGDependencyLeaf Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) where
  step a b o outcome z := outcome = .accepted ∧
    ((a = 2 ∧ b = 1 ∧ o = do_parent ∧ z = 3) ∨
     (a = 3 ∧ b = 2 ∧ o = do_child ∧ z = 4))
  callback a b o z := (a = 2 ∧ b = 1 ∧ o = do_parent ∧ z = 3) ∨
    (a = 3 ∧ b = 2 ∧ o = do_child ∧ z = 4)
  report _ _ _ _ := False
  initial := 0
  genesis := 0

private noncomputable abbrev do_step (kind : FGDependencyStepKind) (_ : Bool) (a z : Nat) : Prop :=
  a = z ∨ (kind = .arrival ∧ ((a = 0 ∧ z = 1) ∨ (a = 1 ∧ z = 2))) ∨
    (kind = .leafRetry ∧ ((a = 2 ∧ z = 3) ∨ (a = 3 ∧ z = 4))) ∨
    (kind = .notification ∧ ((a = 4 ∧ z = 5) ∨ (a = 5 ∧ z = 6)))

private noncomputable abbrev do_driver : FGDependencyDriver Bool (Fin 4) do_protocol where
  enter st wire _ := if st = 0 ∧ wire.payload = 2 then 1
    else if st = 1 ∧ wire.payload = 1 then 2 else st
  enterProgram st wire _ := .finish (if st = 0 ∧ wire.payload = 2 then 1
    else if st = 1 ∧ wire.payload = 1 then 2 else st)
  hookProgram st op := match op with
    | .leaf b _ _ => .finish (do_leafProtocol.process st (do_wire b))
    | .notification b _ =>
        let z := if st = 4 ∧ b = 1 then 5 else if st = 5 ∧ b = 2 then 6 else st
        if st = 5 ∧ b = 2 then .read .ac z .finish else .finish z
    | _ => .finish st
  drain st := if 2 ≤ st ∧ st ≤ 5 then 6 else st
  reconstruct st _ := st
  rebuild st _ := st
  retry st b _ _ := do_leafProtocol.process st (do_wire b)
  work st e := if st = 2 then
    [.step (.leaf 1 do_parent .accepted), .step (.leaf 2 do_child .accepted),
      .step (.notification 1 do_parent), .step (.notification 2 do_child)]
    else match e with
      | .deliver _ _ _ => if st = 1 then [.step .idle] else []
      | .restart _ t => [.step (.reconstruct t), .step (.rebuild t)]
      | _ => []
  inheritRefusal st _ _ := st
  notify st b _ := if st = 4 ∧ b = 1 then 5 else if st = 5 ∧ b = 2 then 6 else st
  replay st _ _ := st

private noncomputable abbrev do_op (k : Nat) :
    FGDependencyOperation (Fin 4) (FGReceiptToken Bool do_protocol.Object) do_protocol.Object :=
  match k with
  | 0 => .arrival 2 do_child
  | 3 => .restore 1
  | 4 => .reconstruct 1
  | 5 => .rebuild 1
  | 7 => .arrival 1 do_parent
  | 8 => .leaf 1 do_parent .accepted
  | 9 => .leaf 2 do_child .accepted
  | 10 => .notification 1 do_parent
  | 11 => .notification 2 do_child
  | 13 => .clock 4
  | _ => .idle

private noncomputable abbrev do_trace : FGDependencyTrace Nat where
  length := 14
  state k := [0, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 6, 6][k]?.getD 6
  time k := [0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4][k]?.getD 4
  start j := [0, 3, 7, 13][j]?.getD 14
  done j := [2, 6, 12, 14][j]?.getD 14
  readCut _ := 14
  entryCut j := [1, 4, 8, 14][j]?.getD 14
  dutyCut j := [2, 5, 12, 14][j]?.getD 14
  hookRead j index kind cut st := j = 2 ∧ index = 0 ∧ kind = .ac ∧ cut = 12 ∧ st = 6

private noncomputable abbrev do_read (_ : Bool) (i st : Nat) : Prop :=
  12 ≤ i ∧ i < 16 ∧ st = 6

private theorem do_child_origin :
    FGReceiptOrigin do_env do_run do_history do_wireReads false 2 do_child := by
  constructor <;> rfl

private theorem do_parent_origin :
    FGReceiptOrigin do_env do_run do_history do_wireReads false 1 do_parent := by
  constructor <;> rfl

private theorem do_closed (st : Nat) (h : st = 1 ∨ st = 6) :
    dependencyClosed do_history do_reads st := by
  intro work
  cases work with
  | inherit b o pending refused unresolved => exact refused.elim
  | retry b o pending valid prior timely held unresolved =>
    rcases h with rfl | rfl <;> simp_all
  | notify b resolved missing =>
    rcases h with rfl | rfl <;> simp_all [dependencyResolved, dependencyRefused]
  | companion b accepted matching missing =>
    rcases h with rfl | rfl <;> simp_all

private theorem do_events_bound {j : Nat} {e : V2.Event Bool do_protocol.Object}
    (h : do_run.events[j]? = some e) : j < 4 :=
  (List.getElem?_eq_some_iff.mp h).1

private theorem do_step_laws :
    FGDependencyStepLaws do_history do_reads do_leaf do_step (fun s _ => s)
      (fun _ _ => False) where
  accepted_keep k x a z b step held := by
    have le : a ≤ z := by rcases step with h | h | h | h <;> omega
    rcases held with rfl | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, Nat.le_trans h le⟩)
    · exact Or.inr (Or.inr ⟨rfl, Nat.le_trans h le⟩)
  refused_keep _ _ _ _ _ _ _ _ h := h.elim
  pending_effect k x a z b o step pending := by
    have le : a ≤ z := by rcases step with h | h | h | h <;> omega
    rcases pending with ⟨rfl, ha, hb, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · refine ⟨Or.inl ⟨rfl, by omega, rfl⟩, ?_⟩
      by_cases hz : z < 4
      · exact Or.inl (Or.inl ⟨rfl, by omega, hz, rfl⟩)
      · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨rfl, by omega⟩)))
    · refine ⟨Or.inr ⟨rfl, le, rfl⟩, ?_⟩
      by_cases hz : z = 2
      · exact Or.inl (Or.inr ⟨rfl, hz, rfl⟩)
      · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨rfl, by omega⟩)))
  origin_keep k x a z b o step origin := by
    have le : a ≤ z := by rcases step with h | h | h | h <;> omega
    rcases origin with ⟨rfl, h, rfl⟩ | ⟨rfl, h, rfl⟩
    · exact Or.inl ⟨rfl, Nat.le_trans h le, rfl⟩
    · exact Or.inr ⟨rfl, Nat.le_trans h le, rfl⟩
  metadata_fg_eq k x a z step notArrival notLeaf := by
    rcases step with rfl | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · rfl
    · exact (notArrival rfl).elim
    · exact (notLeaf rfl).elim
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  insertion_leaf k x a z b step held fresh := by
    rcases step with rfl | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact (fresh held).elim
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp_all
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hb : b = 1 := by simp_all
        subst b
        exact ⟨do_parent, rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
      · have hb : b = 2 := by simp_all
        subst b
        exact ⟨do_child, rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
  one_body a z b o result leaf c held := by
    rcases leaf with ⟨rfl, (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩)⟩
    all_goals simp_all
    all_goals tauto
  restore_exact _ _ := ⟨rfl, rfl, fun _ _ _ => Iff.rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  no_signing _ _ _ _ _ := not_false

private theorem do_state_laws : FGDependencyStateLaws do_history do_reads do_leaf where
  accepted_domain st b := by
    by_cases h4 : 4 ≤ st
    · have h3 : 3 ≤ st := by omega
      simp [h4, h3]
    · by_cases h3 : 3 ≤ st <;> simp [h4, h3]
  accepted_refused_disjoint _ _ _ _ h := h.elim
  pending_valid st b o h := by
    rcases h with ⟨rfl, lo, _, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨by decide, Or.inl ⟨rfl, lo, rfl⟩⟩
    · exact ⟨by decide, Or.inr ⟨rfl, Nat.le_refl _, rfl⟩⟩
  refused_valid _ _ _ _ h := h.elim
  genesis_accepted := Or.inl rfl
  initial_pending b o h := by simp at h
  initial_refused _ _ _ := not_false
  accepted_leaf st b held nonGenesis := by
    rcases held with rfl | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact (nonGenesis rfl).elim
    · exact ⟨2, 3, do_parent, ⟨rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩,
        by decide, Or.inr (Or.inl ⟨rfl, by decide⟩),
        Or.inr ⟨rfl, by omega, rfl⟩⟩
    · exact ⟨3, 4, do_child, ⟨rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩,
        by decide, Or.inr (Or.inr ⟨rfl, by decide⟩),
        Or.inl ⟨rfl, by omega, rfl⟩⟩

private noncomputable abbrev do_arrival (a : Nat) (b : Fin 4)
    (o : FGReceiptToken Bool do_protocol.Object) (z : Nat) : Prop :=
  (a = 0 ∧ b = 2 ∧ o = do_child ∧ z = 1) ∨
    (a = 1 ∧ b = 1 ∧ o = do_parent ∧ z = 2)

private noncomputable abbrev do_notify (a : Nat) (b : Fin 4) (z : Nat) : Prop :=
  (a = 4 ∧ b = 1 ∧ z = 5) ∨ (a = 5 ∧ b = 2 ∧ z = 6)

private theorem do_arrival_laws :
    FGDependencyArrivalLeafLaws do_history do_reads do_leaf do_arrival do_notify where
  direct_refusal_iff a b o z invoked := by
    simp
  arrival_effect a z b o arrived valid timely := by
    rcases arrived with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
      simp [Effect, dependencyResolved, dependencyRefused]
  arrival_inherits _ _ _ _ _ _ h := h.elim
  arrival_pending a z b o arrived valid timely fresh missing noRefusal noSelf := by
    rcases arrived with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inl ⟨rfl, by decide, by decide, rfl⟩
    · exact (missing (Or.inl rfl)).elim
  held_parent_accepts a z b o invoked := by
    obtain ⟨result, _, step⟩ := invoked
    rcases step with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
      simp [do_body]
  accepted_callback _ _ _ _ leaf := leaf.2
  callback_only a z b o callback := by
    refine ⟨⟨rfl, callback⟩, ?_, not_false⟩
    rcases callback with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> decide +kernel
  refusal_report _ _ _ _ h := h.elim
  rejected_no_refusal _ _ _ _ _ _ _ h := h.elim
  notification_resolved a z b notify := by
    rcases notify with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      simp [dependencyResolved, dependencyRefused]
  notification_keys _ _ _ _ := rfl
  notification_fields a z b i notify unmatched := by
    rcases notify with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rfl
    · simp at unmatched
  notification_matching a z b i slot notify held matching := by
    rcases notify with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have bad : (2 : Nat) = 1 :=
        congrArg BlockId.value (congrArg Prod.snd (Option.some.inj matching))
      omega
    · rfl
  refused_notification _ _ _ _ refused := refused.elim
  callback_latest a z b notify accepted := by
    rcases notify with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide +kernel

private theorem do_micro_steps (k : Nat) (hk : k < do_trace.length) :
    ∃ kind, do_step kind false (do_trace.state k) (do_trace.state (k + 1)) := by
  change k < 14 at hk
  interval_cases k <;> first
    | exact ⟨.arrival, Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)⟩
    | exact ⟨.arrival, Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)⟩
    | exact ⟨.leafRetry, Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩))⟩
    | exact ⟨.leafRetry, Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩))⟩
    | exact ⟨.notification, Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩))⟩
    | exact ⟨.notification, Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩))⟩
    | exact ⟨.ordinary, Or.inl rfl⟩

private theorem do_entry_steps (x : Bool) : FGDependencySteps do_step x 2 6 := by
  have s1 : do_step .leafRetry x 2 3 := by simp [do_step]
  have s2 : do_step .leafRetry x 3 4 := by simp [do_step]
  have s3 : do_step .notification x 4 5 := by simp [do_step]
  have s4 : do_step .notification x 5 6 := by simp [do_step]
  exact .tail .notification (.tail .notification
    (.tail .leafRetry (.tail .leafRetry (.refl 2) s1) s2) s3) s4

private theorem do_trace_facts (k : Nat) (hk : k ≤ 14) :
    (1 ≤ do_trace.state k → do_trace.start 0 < k) ∧
    (2 ≤ do_trace.state k → do_trace.start 2 < k) ∧
    (∀ b, do_reads.notified (do_trace.state (k + 1)) b →
      ¬ do_reads.notified (do_trace.state k) b →
      (k = 10 ∧ b = 1) ∨ (k = 11 ∧ b = 2)) ∧
    (∀ b, do_reads.accepted (do_trace.state (k + 1)) b →
      ¬ do_reads.accepted (do_trace.state k) b →
      (k = 8 ∧ b = 1) ∨ (k = 9 ∧ b = 2)) := by
  interval_cases k <;> refine ⟨by decide, by decide, ?_, ?_⟩ <;> decide

private theorem do_trace_laws :
    FGDependencyTraceLaws do_env do_run false do_history do_wireReads do_reads do_leaf
      do_step do_trace do_driver do_op do_arrival do_notify
      (Leaf := do_leafProtocol) id id do_read where
  arrival_laws := do_arrival_laws
  initial := rfl
  initial_accepted b h := by simpa [do_reads, do_protocol, do_leaf] using h
  micro_step := do_micro_steps
  external_step j e h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> exact ⟨rfl, rfl⟩
  step_kind k hk := by
    change k < 14 at hk
    interval_cases k <;> decide
  operation_bound k hk := by
    change k < 14 at hk
    interval_cases k <;> simp only [do_op]
    all_goals first
      | rfl
      | exact ⟨Or.inl ⟨rfl, rfl, rfl, rfl⟩, rfl, do_child_origin, rfl⟩
      | exact ⟨Or.inr ⟨rfl, rfl, rfl, rfl⟩, rfl, do_parent_origin, rfl⟩
      | exact ⟨rfl, 1, rfl, rfl⟩
      | exact ⟨rfl, 1, rfl, by decide, by decide, fun q lo hi => by
          norm_num at lo hi; interval_cases q⟩
      | simp [dependencyResolved, dependencyRefused, do_notify]
  delivery_entry j wire t h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> rfl
  work_execution j e h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> exact ⟨rfl, rfl⟩
  work_step j e k h lo hi := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      norm_num [do_trace] at lo hi <;> interval_cases k <;> rfl
  hook_correspondence j e index kind cut st h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e
    · change (0 = 2 ∧ _) ↔ ∃ r, ([] : List (FGDependencyWorkRead Nat))[index]? = some r ∧ _
      simp
    · change (1 = 2 ∧ _) ↔ ∃ r, ([] : List (FGDependencyWorkRead Nat))[index]? = some r ∧ _
      simp
    · change (2 = 2 ∧ index = 0 ∧ kind = .ac ∧ cut = 12 ∧ st = 6) ↔
        ∃ r, ([⟨4, .ac, 6⟩] : List (FGDependencyWorkRead Nat))[index]? = some r ∧
          r.kind = kind ∧ cut = 8 + r.offset ∧ st = r.consumed
      cases index <;> simp [eq_comm]
    · change (3 = 2 ∧ _) ↔ ∃ r, ([] : List (FGDependencyWorkRead Nat))[index]? = some r ∧ _
      simp
  hook_reads j e r h member := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e
    · change r ∈ ([] : List (FGDependencyWorkRead Nat)) at member
      cases member
    · change r ∈ ([] : List (FGDependencyWorkRead Nat)) at member
      cases member
    · change r ∈ ([⟨4, .ac, 6⟩] : List (FGDependencyWorkRead Nat)) at member
      have hr := List.mem_singleton.mp member
      subst r
      exact ⟨by decide, rfl, do_entry_steps false, do_closed 6 (Or.inr rfl)⟩
    · change r ∈ ([] : List (FGDependencyWorkRead Nat)) at member
      cases member
  receipt_entry j wire t b h awake valid decoded := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    · obtain ⟨_, rfl, rfl⟩ := V2.Event.deliver.inj h
      have hb := Option.some.inj decoded
      subst b
      simp [Effect, dependencyResolved, dependencyRefused, dependencyReceiverEpoch,
        do_op, do_arrival]
    · cases h
    · obtain ⟨_, rfl, rfl⟩ := V2.Event.deliver.inj h
      have hb := Option.some.inj decoded
      subst b
      simp [Effect, dependencyResolved, dependencyRefused, dependencyReceiverEpoch,
        do_op, do_arrival]
    · cases h
  entry_boundary j e h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      exact ⟨rfl, by decide, by decide, rfl, rfl⟩
  drain_operations j e k h lo hi := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      norm_num [do_trace] at lo hi <;> interval_cases k
    all_goals first
      | exact Or.inl ⟨_, _, _, rfl⟩
      | exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨_, rfl, rfl, rfl⟩))))))
      | refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr ⟨_, rfl, by decide, rfl, ?_⟩))))))
    all_goals intro q lo hi; norm_num [do_trace] at lo hi; omega
  boundary_idle k hk outside := by
    change k < 14 at hk
    interval_cases k <;> simp only [do_op]
    all_goals exfalso; apply outside
    all_goals first
      | exact ⟨0, _, rfl, by decide, by decide⟩
      | exact ⟨1, _, rfl, by decide, by decide⟩
      | exact ⟨2, _, rfl, by decide, by decide⟩
      | exact ⟨3, _, rfl, by decide, by decide⟩
  raw_restore j t h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> rfl
  raw_clock j t h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> rfl
  restore_data _ _ := ⟨rfl, rfl, fun _ _ _ => Iff.rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  reconstruct_program _ _ := rfl
  reconstruct_data st _ := by
    refine ⟨rfl, rfl, fun _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => Iff.rfl, ?_, ?_⟩
    · intro b o h
      rcases h with (⟨rfl, rfl, rfl, hz⟩ | ⟨rfl, rfl, rfl, hz⟩) <;> cases hz
    · intro b o h; exact h.elim
  restart_reconstruct j t h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> exact ⟨by decide, rfl⟩
  restart_drain_closed j t h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h
    exact do_closed 1 (Or.inl rfl)
  restart_replay_order j t k b o h lo hi op := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> norm_num [do_trace] at lo hi ⊢
    all_goals interval_cases k <;> first | decide | cases op
  rebuild_program _ _ := rfl
  rebuild_data st _ := by
    refine ⟨rfl, rfl, fun _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => Iff.rfl, ?_, ?_⟩
    · intro b o h
      rcases h with (⟨rfl, rfl, rfl, hz⟩ | ⟨rfl, rfl, rfl, hz⟩) <;> cases hz
    · intro b o h; exact h.elim
  restart_rebuild j t h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h
    refine ⟨5, by decide, by decide, rfl, ?_, ?_, ?_, rfl⟩
    · intro q t lo hi op
      norm_num [do_trace] at lo hi
      interval_cases q <;> first | rfl | cases op
    · intro q lo hi
      norm_num [do_trace] at lo hi
      interval_cases q
    · intro q lo hi
      norm_num [do_trace] at lo hi
      interval_cases q
  clock_no_insert _ _ := ⟨rfl, rfl⟩
  refusal_creation _ _ _ refused _ := refused.elim
  refusal_history _ _ _ refused := refused.elim
  notification_creation k b hk notified fresh := by
    change k < 14 at hk
    have key := (do_trace_facts k (Nat.le_of_lt hk)).2.2.1 b notified fresh
    rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨do_parent, rfl, Or.inl ⟨rfl, rfl, rfl⟩, 8, by decide,
        Or.inl ⟨by decide, Or.inl ⟨rfl, rfl, rfl, rfl⟩, rfl⟩⟩
    · exact ⟨do_child, rfl, Or.inr ⟨rfl, rfl, rfl⟩, 9, by decide,
        Or.inl ⟨by decide, Or.inr ⟨rfl, rfl, rfl, rfl⟩, rfl⟩⟩
  actual_read i st := by
    constructor
    · rintro ⟨lo, hi, rfl⟩
      interval_cases i
      · exact ⟨3, .tick false 4, .fg, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
      · exact ⟨3, .tick false 4, .proposer, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
      · exact ⟨3, .tick false 4, .head, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
      · exact ⟨3, .tick false 4, .ac, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
    · rintro ⟨j, e, kind, he, required, rfl, rfl⟩
      have hj := do_events_bound he
      interval_cases j <;> simp only [List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.some.injEq] at he <;> subst e
      all_goals simp [dependencyReadRequired] at required
      all_goals cases kind <;> exact ⟨by decide, by decide, rfl⟩
  read_order j e kind h required := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e
    all_goals simp [dependencyReadRequired] at required
    all_goals exact ⟨Nat.le_refl 14, Nat.le_refl 14, rfl, .refl _⟩
  wire_validation wire b valid decoded := by
    have hb : wire.payload = b := Option.some.inj decoded
    simpa [do_protocol, do_reads, hb] using valid
  origin_valid k b o hk origin := by
    change k ≤ 14 at hk
    rcases origin with ⟨rfl, h, rfl⟩ | ⟨rfl, h, rfl⟩
    · refine ⟨do_child_origin, ?_⟩
      exact (do_trace_facts k hk).1 h
    · refine ⟨do_parent_origin, ?_⟩
      exact (do_trace_facts k hk).2.1 h
  leaf_step k b o z hk leaf hz := by
    change k < 14 at hk
    rcases leaf with ⟨_, (⟨ha, rfl, rfl, rfl⟩ | ⟨ha, rfl, rfl, rfl⟩)⟩
    · refine ⟨do_parent_origin, ?_, ?_⟩
      · apply (do_trace_facts k (Nat.le_of_lt hk)).2.1
        rw [ha]
      · change 3 = do_leafProtocol.process (do_trace.state k) (do_wire 1)
        rw [ha]
        rfl
    · refine ⟨do_child_origin, ?_, ?_⟩
      · apply (do_trace_facts k (Nat.le_of_lt hk)).1
        rw [ha]
        decide
      · change 4 = do_leafProtocol.process (do_trace.state k) (do_wire 2)
        rw [ha]
        rfl
  origin_attribution k b hk held fresh := by
    have key := (do_trace_facts k (Nat.le_of_lt hk)).2.2.2 b held fresh
    rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨do_parent, ⟨rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩,
        Or.inr ⟨rfl, by decide, rfl⟩, rfl, rfl, rfl⟩
    · exact ⟨do_child, ⟨rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩,
        Or.inl ⟨rfl, by decide, rfl⟩, rfl, rfl, rfl⟩
  read_correspondence i st read := by
    rcases read with ⟨_, _, rfl⟩
    exact ⟨Nat.le_refl 14, rfl, do_closed 6 (Or.inr rfl)⟩
  order_and_time i j ei ej hi hj le := by
    have bi := do_events_bound hi
    have bj := do_events_bound hj
    interval_cases i <;> interval_cases j <;>
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.some.injEq] at hi hj <;> subst ei <;> subst ej <;>
      decide +kernel
  finite_segment j e h := by
    have hj := do_events_bound h
    interval_cases j <;> decide +kernel
  event_drain j y wire t h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq, V2.Event.deliver.injEq] at h
    · exact do_closed 1 (Or.inl rfl)
    · cases h
    · exact do_closed 6 (Or.inr rfl)
    · cases h
  entry_drain j e h := by
    have hj := do_events_bound h
    interval_cases j
    · exact do_closed 1 (Or.inl rfl)
    · exact do_closed 1 (Or.inl rfl)
    · exact do_closed 6 (Or.inr rfl)
    · exact do_closed 6 (Or.inr rfl)
  segment_time j e k h lower upper := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      norm_num [do_trace] at lower upper <;> interval_cases k <;> rfl
  event_order i j ei ej hi hj lt := by
    have bi := do_events_bound hi
    have bj := do_events_bound hj
    interval_cases i <;> interval_cases j <;> decide
  completion_cut j e deadline h strict := by
    have hj := do_events_bound h
    refine ⟨?_, ?_, ?_⟩
    · interval_cases j <;> decide +kernel
    · interval_cases j <;> simp only [List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> exact strict
    · intro i ei hi before
      have bi := do_events_bound hi
      interval_cases i <;> interval_cases j <;>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.some.injEq] at hi h <;> subst ei <;> subst e <;>
        norm_num [do_trace] at before <;>
        exact lt_of_le_of_lt (by decide) strict
  tick_records j t h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> rfl
  atomic_tick j t h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    · cases h
    · cases h
    · cases h
    · have ht : (4 : Time) = t := V2.Event.tick.inj h |>.2
      subst t
      exact ⟨by decide, by decide, rfl, do_closed 6 (Or.inr rfl), .refl _⟩

/-- This second complete interface trace has no hook read before its deadline. -/
private noncomputable abbrev do_noReadDriver : FGDependencyDriver Bool (Fin 4) do_protocol :=
  { do_driver with hookProgram := fun st op => match op with
      | .notification b _ => .finish
          (if st = 4 ∧ b = 1 then 5 else if st = 5 ∧ b = 2 then 6 else st)
      | _ => do_driver.hookProgram st op }

private noncomputable abbrev do_noReadTrace : FGDependencyTrace Nat :=
  { do_trace with hookRead := fun _ _ _ _ _ => False }

private theorem do_no_read_trace_laws :
    FGDependencyTraceLaws do_env do_run false do_history do_wireReads do_reads do_leaf
      do_step do_noReadTrace do_noReadDriver do_op do_arrival do_notify
      (Leaf := do_leafProtocol) id id do_read :=
  { do_trace_laws with
    external_step := by
      intro j e h
      have hj := do_events_bound h
      interval_cases j <;> simp only [List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> exact ⟨rfl, rfl⟩
    work_execution := by
      intro j e h
      have hj := do_events_bound h
      interval_cases j <;> simp only [List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> exact ⟨rfl, rfl⟩
    work_step := by
      intro j e k h lo hi
      have hj := do_events_bound h
      interval_cases j <;> simp only [List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
        norm_num [do_noReadTrace, do_trace] at lo hi <;> interval_cases k <;> rfl
    hook_correspondence := by
      intro j e index kind cut st h
      have hj := do_events_bound h
      interval_cases j <;> simp only [List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e
      all_goals change False ↔
        ∃ r, ([] : List (FGDependencyWorkRead Nat))[index]? = some r ∧ _
      all_goals simp
    hook_reads := by
      intro j e r h member
      have hj := do_events_bound h
      interval_cases j <;> simp only [List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e
      all_goals change r ∈ ([] : List (FGDependencyWorkRead Nat)) at member
      all_goals cases member
    actual_read := by
      intro i st
      constructor
      · rintro ⟨lo, hi, rfl⟩
        interval_cases i
        · exact ⟨3, .tick false 4, .fg, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
        · exact ⟨3, .tick false 4, .proposer, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
        · exact ⟨3, .tick false 4, .head, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
        · exact ⟨3, .tick false 4, .ac, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
      · rintro ⟨j, e, kind, he, required, rfl, rfl⟩
        have hj := do_events_bound he
        interval_cases j <;> simp only [List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.some.injEq] at he <;> subst e
        all_goals simp [dependencyReadRequired] at required
        all_goals cases kind <;> exact ⟨by decide, by decide, rfl⟩
    atomic_tick := by
      intro j t h
      have hj := do_events_bound h
      interval_cases j <;> simp only [List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.some.injEq] at h
      · cases h
      · cases h
      · cases h
      · have ht := (V2.Event.tick.inj h).2
        subst t
        exact ⟨by decide, by decide, rfl, do_closed 6 (Or.inr rfl), .refl _⟩ }

private theorem do_strict_completion_without_any_read :
    dependencyStrictPrefix do_run do_noReadTrace 3 (do_noReadTrace.done 2) ∧
    dependencyResolved do_history do_reads (do_noReadTrace.state (do_noReadTrace.done 2)) 2 ∧
    do_reads.notified (do_noReadTrace.state (do_noReadTrace.done 2)) 2 ∧
    (∀ i st, do_read false i st → ¬ do_noReadTrace.time (do_noReadTrace.readCut i) < 3) ∧
    (∀ j index kind cut st, ¬ do_noReadTrace.hookRead j index kind cut st) := by
  refine ⟨(dependency_drain_before_deadline do_no_read_trace_laws
      (j := 2) (wire := do_wire 1) (t := 1) (deadline := 3) rfl (by decide)).2.2,
    ?_, ?_, fun _ _ _ => (by decide : ¬ (4 : Time) < 3), fun _ _ _ _ _ => not_false⟩
  · simp [dependencyResolved, dependencyRefused]
  · simp

#print axioms do_no_read_trace_laws
#print axioms do_strict_completion_without_any_read

private theorem do_same_time_positive :
    do_trace.time 9 = 1 ∧ do_trace.time 10 = 1 ∧ do_trace.time 11 = 1 ∧
    do_trace.time 12 = 1 ∧ do_trace.done 2 = 12 ∧
    dependencyResolved do_history do_reads (do_trace.state 12) 2 ∧
    do_reads.notified (do_trace.state 12) 2 ∧
    do_reads.companionHeld (do_reads.latest (do_trace.state 12)) 2 := by
  unfold dependencyResolved dependencyRefused
  decide +kernel

private theorem do_original_epoch_after_restart :
    dependencyReceiverEpoch do_run false 2 = 2 ∧ do_child.receiptEpoch = 0 ∧
    FGReceiptOrigin do_env do_run do_history do_wireReads false 2 do_child :=
  ⟨rfl, rfl, do_child_origin⟩

private theorem do_wrong_receiver :
    ¬ FGReceiptOrigin do_env do_run do_history do_wireReads true 2 do_child := by
  intro h
  cases h.receiver_eq

private theorem do_same_root_forgery :
    do_history.root 2 = do_history.root 3 ∧
    ¬ FGReceiptOrigin do_env do_run do_history do_wireReads false 3 do_child := by
  refine ⟨rfl, ?_⟩
  intro h
  have bad : (2 : Fin 4) = 3 := Option.some.inj h.decoded
  exact (by decide : (2 : Fin 4) ≠ 3) bad

private theorem do_epoch_forgery :
    ¬ FGReceiptOrigin do_env do_run do_history do_wireReads false 2
      { do_child with receiptEpoch := 2 } := by
  intro h
  have bad : (2 : Nat) = 0 := h.epoch_eq
  omega

private theorem do_future_forgery :
    ¬ FGReceiptOrigin do_env do_run do_history do_wireReads false 2
      { do_child with eventIndex := 20 } := by
  intro h
  have bad : (none : Option (V2.Event Bool do_protocol.Object)) = some _ := h.delivered
  cases bad

private theorem do_delayed_drain_enabled :
    FGDependencyEnabled do_history do_reads 3 := by
  exact .retry 2 do_child (Or.inl ⟨rfl, by decide, by decide, rfl⟩)
    (by decide) (Or.inr ⟨rfl, rfl⟩) trivial (Or.inr (Or.inl ⟨rfl, by decide⟩))
    (by simp [dependencyResolved, dependencyRefused])

private theorem do_delayed_notification_enabled :
    FGDependencyEnabled do_history do_reads 4 := by
  exact .notify 2 (Or.inl (Or.inr (Or.inr ⟨rfl, by decide⟩)))
    (by simp)

private theorem do_later_read_closed_but_late :
    dependencyClosed do_history do_reads (do_trace.state 14) ∧
    ¬ do_trace.time 14 < (3 : Time) :=
  ⟨do_closed 6 (Or.inr rfl), by decide⟩

private theorem do_retained_only_entry :
    dependencyClosed do_history do_reads (do_trace.state (do_trace.done 1)) ∧
    do_trace.time (do_trace.done 1) = 1 ∧
    Effect do_history do_reads (do_trace.state (do_trace.done 1)) 2 do_child :=
  ⟨do_closed 1 (Or.inl rfl), rfl,
    Or.inl ⟨rfl, by decide, rfl⟩, Or.inl (Or.inl ⟨rfl, by decide, by decide, rfl⟩)⟩

private theorem do_terminal_equality_not_strict : ¬ (3 : Time) < 3 := by decide

/-- Only logical time changes in these weak models. Retention and origin data stay exact. -/
private noncomputable abbrev do_delayed (firstLate : Nat) : FGDependencyTrace Nat :=
  { do_trace with time := fun k => if firstLate ≤ k then 4 else do_trace.time k }

private theorem do_weak_delayed_model (firstLate : Nat) :
    (∀ k, k < (do_delayed firstLate).length → ∃ kind,
      do_step kind false ((do_delayed firstLate).state k)
        ((do_delayed firstLate).state (k + 1))) ∧
    (∀ k b o, k ≤ (do_delayed firstLate).length →
      do_reads.originAvailable ((do_delayed firstLate).state k) b o →
      FGReceiptOrigin do_env do_run do_history do_wireReads false b o) ∧
    (∀ i st, do_read false i st →
      (do_delayed firstLate).state ((do_delayed firstLate).readCut i) = st ∧
      dependencyClosed do_history do_reads st) := by
  refine ⟨do_micro_steps, ?_, ?_⟩
  · intro k b o bound origin
    exact (do_trace_laws.origin_valid k b o bound origin).1
  · intro i st read
    exact (do_trace_laws.read_correspondence i st read).2

private theorem do_delayed_child_countermodel :
    ¬ FGDependencyTraceLaws do_env do_run false do_history do_wireReads do_reads do_leaf
      do_step (do_delayed 10) do_driver do_op do_arrival do_notify
      (Leaf := do_leafProtocol) id id do_read := by
  intro laws
  have cutoff := laws.completion_cut 2 (.deliver false (do_wire 1) 1) 3 rfl (by decide)
  exact (by decide : ¬ (4 : Time) < 3) cutoff.2.1

private theorem do_delayed_notification_countermodel :
    do_trace.time 10 = 1 ∧
    ¬ FGDependencyTraceLaws do_env do_run false do_history do_wireReads do_reads do_leaf
      do_step (do_delayed 11) do_driver do_op do_arrival do_notify
      (Leaf := do_leafProtocol) id id do_read := by
  refine ⟨rfl, ?_⟩
  intro laws
  have cutoff := laws.completion_cut 2 (.deliver false (do_wire 1) 1) 3 rfl (by decide)
  exact (by decide : ¬ (4 : Time) < 3) cutoff.2.1

private theorem do_early_read_countermodel :
    ¬ FGDependencyTraceLaws do_env do_run false do_history do_wireReads do_reads do_leaf
      do_step { do_trace with readCut := fun _ => 9 }
      do_driver do_op do_arrival do_notify
      (Leaf := do_leafProtocol) id id do_read := by
  intro laws
  have eq := (laws.read_correspondence 15 6 ⟨by decide, by decide, rfl⟩).2.1
  exact (by decide : (3 : Nat) ≠ 6) eq

private theorem do_future_in_range_receipt :
    FGReceiptOrigin do_env do_run do_history do_wireReads false 1 do_parent ∧
    ¬ do_trace.start do_parent.eventIndex < 2 :=
  ⟨do_parent_origin, by decide⟩

private theorem do_positive_strict_no_early_read :
    dependencyStrictPrefix do_run do_trace 3 (do_trace.done 2) ∧
    (∀ i st, do_read false i st → ¬ do_trace.time (do_trace.readCut i) < 3) ∧
    do_trace.done 1 < do_trace.start 2 ∧
    do_trace.time (do_trace.done 1) = do_trace.time (do_trace.start 2) := by
  exact ⟨(dependency_drain_before_deadline do_trace_laws
    (j := 2) (wire := do_wire 1) (t := 1) (deadline := 3) rfl (by decide)).2.2,
    fun _ _ _ => (by decide : ¬ (4 : Time) < 3), by decide, rfl⟩

private theorem do_retained_only_path_consumer :
    ∃ j k, k = do_trace.done j ∧ 3 ≤ j ∧ dependencyStrictPrefix do_run do_trace 7 k ∧
      dependencyResolved do_history do_reads (do_trace.state k) 2 ∧
      do_reads.notified (do_trace.state k) 2 ∧
      (do_reads.accepted (do_trace.state k) 2 →
        do_reads.matching (do_reads.latest (do_trace.state k)) 2 →
        do_reads.companionHeld (do_reads.latest (do_trace.state k)) 2) := by
  have delivery : FGDependencyDeliveryLaws do_env do_run false do_history do_wireReads
      do_reads do_trace do_driver (fun _ _ _ => False) :=
    ⟨fun _ _ _ _ _ _ _ _ _ _ out => out.elim⟩
  apply dependency_finite_path_resolved_before do_trace_laws do_step_laws delivery
    (path := [1, 2]) (entry := 3) (tau := 4) (wake := 4)
    (event := .tick false 4)
  · exact .snoc (parent := 1) (b := 2) (path := [1])
      (.snoc (parent := 0) (b := 1) (path := []) .root rfl) rfl
  · rfl
  · rfl
  · exact Or.inl rfl
  · decide
  · exact le_rfl
  · intro t _ _; rfl
  · intro j t h after
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    · cases h
    · have ht := (V2.Event.restart.inj h).2
      subst t
      exact (by decide : ¬ (4 : Time) < 1) after |>.elim
    · cases h
    · cases h
  · decide
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · refine ⟨by decide, ?_⟩
      intro k _ o pending _
      rcases pending with ⟨bad, _⟩ | ⟨_, eq, _⟩
      · cases bad
      · exact ⟨Or.inl ⟨rfl, eq⟩, trivial⟩
    · have hb' : b = 2 := by simpa using hb
      subst b
      refine ⟨by decide, ?_⟩
      intro k _ o pending parent
      rcases pending with ⟨_, lo, hi, _⟩ | ⟨bad, _⟩
      · have parentHeld : 3 ≤ do_trace.state k := by simpa using parent
        exact ⟨Or.inr ⟨rfl, by omega⟩, trivial⟩
      · cases bad
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Or.inl ⟨do_parent, Or.inr ⟨rfl, by decide, rfl⟩,
        Or.inr (Or.inl (Or.inr (Or.inl ⟨rfl, by decide⟩)))⟩
    · have hb' : b = 2 := by simpa using hb
      subst b
      exact Or.inl ⟨do_child, Or.inl ⟨rfl, by decide, rfl⟩,
        Or.inr (Or.inl (Or.inr (Or.inr ⟨rfl, by decide⟩)))⟩

private noncomputable def do_site (i : Nat) : FGDependencyReadSite Nat :=
  ⟨i / 4, match i % 4 with
    | 0 => .fg | 1 => .proposer | 2 => .head | _ => .ac,
    do_trace.entryCut (i / 4), do_trace.readCut i, 6⟩

private theorem do_read_closure_laws :
    FGDependencyReadClosureLaws do_env do_run false do_history do_reads do_step
      do_trace do_driver do_site do_read do_wireReads do_leaf do_op do_arrival do_notify
      (Leaf := do_leafProtocol) id id where
  trace_bound := do_trace_laws
  actual_read := do_trace_laws.actual_read
  site_correspondence i st h := by
    rcases h with ⟨lo, hi, rfl⟩
    interval_cases i <;> exact ⟨.tick false 4, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
  hook_correspondence := do_trace_laws.hook_correspondence
  hook_completion := do_trace_laws.hook_reads
  read_closed i st h := (do_trace_laws.read_correspondence i st h).2.2
  finite_completion i st h := by
    rcases h with ⟨lo, hi, rfl⟩
    interval_cases i <;>
      exact ⟨by decide, by decide, rfl, rfl, .refl _, do_closed 6 (Or.inr rfl)⟩

private theorem do_bridge_original_child_rows : ∃ o,
    FGReceiptOrigin do_env do_run do_history do_wireReads false 2 o ∧
    do_wireReads.proposalErase o.wire = some (do_body 2) ∧
    do_wireReads.decodedRows o.wire = [2] := by
  exact dependency_accepted_origin_bridge do_trace_laws (i := 15) (st := 6)
    ⟨by decide, by decide, rfl⟩ (Or.inr (Or.inr ⟨rfl, by decide⟩)) (by decide)

private noncomputable abbrev do_sending (body : Fin 4) : V2.ProtocolSpecD Unit where
  State := Nat
  Label := Unit
  Duty := Unit
  signLabel := fun _ => ()
  seats := fun _ => 1
  Payload := Fin 4
  Durable := Nat
  init := 0
  clock := fun st _ => st
  actTime := fun _ => -1
  duties t := if t = -1 then [()] else []
  duties_spec := by intro d t; cases d; simp [eq_comm]
  duties_nodup := by intro t; split <;> simp
  act := fun _ _ _ => some body
  gossip := fun _ _ => []
  process := fun st _ => st
  selfVisible := fun _ => false
  recordOwn := fun st _ => st
  durable := id
  restore := fun st _ => st
  wellFormed wire := decide (wire.payload ≠ 3)
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

private noncomputable abbrev do_sendReads (body : Fin 4) :
    FGDependencyWireReads (do_sending body) (Fin 4) Nat where
  decodeBody wire := some wire.payload
  namedRoots wire := some (do_history.root wire.payload,
    do_history.root (do_history.parent wire.payload))
  proposalErase wire := some (do_body wire.payload)
  decodedRows wire := [wire.payload.val]
  bodyRows b := [b.val]

private noncomputable abbrev do_sentRun (body : Fin 4) (horizon : Time) :
    V2.D.Run Bool (do_sending body) where
  honest := {true}
  horizon := horizon
  events := [.tick true (-1)]
  seatOf := fun _ _ => true
  input := fun _ _ => ()

private noncomputable abbrev do_asleep : Generic.Env Bool :=
  { do_env with awake := fun x _ => x }

private noncomputable abbrev do_emptyTrace : FGDependencyTrace Nat where
  length := 1
  state _ := 0
  time _ := -1
  start _ := 0
  done _ := 1
  readCut _ := 1
  entryCut _ := 1
  dutyCut _ := 1
  hookRead _ _ _ _ _ := False

private noncomputable abbrev do_sendDriver (body : Fin 4) :
    FGDependencyDriver Bool (Fin 4) (do_sending body) where
  enter st _ _ := st
  enterProgram st _ _ := .finish st
  hookProgram st _ := .finish st
  drain := id
  reconstruct st _ := st
  rebuild st _ := st
  retry st _ _ _ := st
  work _ _ := []
  inheritRefusal st _ _ := st
  notify st _ _ := st
  replay st _ _ := st

private theorem do_honest_old_send (body : Fin 4) (horizon : Time) :
    dependencyEmits do_asleep (do_sentRun body horizon) (do_sendDriver body)
      true (do_wire body) (-1) ∧
    dependencyEmits do_env (do_sentRun body horizon) (do_sendDriver body)
      true (do_wire body) (-1) := by
  constructor <;> refine ⟨0, rfl, ?_⟩ <;>
    change do_wire body ∈ [do_wire body] <;> exact List.mem_singleton_self _

/-- Without the awake interval, actual old honest sends can have no receiver delivery. -/
private theorem do_awake_guard_countermodel :
    FGDependencyDeliveryLaws do_asleep (do_sentRun 1 10) false do_history (do_sendReads 1)
      do_reads do_emptyTrace (do_sendDriver 1) (fun _ _ _ => True) ∧
    dependencyEmits do_asleep (do_sentRun 1 10) (do_sendDriver 1) true (do_wire 1) (-1) ∧
    ¬ dependencyResolved do_history do_reads (do_emptyTrace.state 1) 1 := by
  refine ⟨⟨?_⟩, (do_honest_old_send 1 10).1, ?_⟩
  · intro sender wire sent wake deadline b honest emit decode valid outstanding
      sentlt wakelt awake noRestart horizon bound
    have impossible : false = true := awake wake le_rfl wakelt
    cases impossible
  · simp [dependencyResolved, dependencyRefused]

/-- The horizon guard is independent of sleeping: this receiver is always awake. -/
private theorem do_horizon_guard_countermodel :
    FGDependencyDeliveryLaws do_env (do_sentRun 1 0) false do_history (do_sendReads 1)
      do_reads do_emptyTrace (do_sendDriver 1) (fun _ _ _ => True) ∧
    dependencyEmits do_env (do_sentRun 1 0) (do_sendDriver 1) true (do_wire 1) (-1) ∧
    ¬ dependencyResolved do_history do_reads (do_emptyTrace.state 1) 1 := by
  refine ⟨⟨?_⟩, (do_honest_old_send 1 0).2, ?_⟩
  · intro sender wire sent wake deadline b honest emit decode valid outstanding
      sentlt wakelt awake noRestart horizon bound
    change deadline ≤ (0 : Time) at horizon
    change max (max sent (0 : Time)) wake + 3 ≤ deadline at bound
    have nonneg : (0 : Time) ≤ max (max sent 0) wake :=
      le_trans (le_max_right sent 0) (le_max_left _ wake)
    have floor : (3 : Time) ≤ max (max sent 0) wake + 3 :=
      Int.add_le_add nonneg (Int.le_refl 3)
    exact ((by decide : ¬ (3 : Time) ≤ 0)
      (le_trans (le_trans floor bound) horizon)).elim
  · simp [dependencyResolved, dependencyRefused]

private theorem do_validation_guard_countermodel :
    FGDependencyDeliveryLaws do_env (do_sentRun 3 10) false do_history (do_sendReads 3)
      do_reads do_emptyTrace (do_sendDriver 3) (fun wire _ _ => wire.payload = 3) ∧
    dependencyEmits do_env (do_sentRun 3 10) (do_sendDriver 3) true (do_wire 3) (-1) ∧
    ¬ dependencyResolved do_history do_reads (do_emptyTrace.state 1) 3 := by
  refine ⟨⟨?_⟩, (do_honest_old_send 3 10).2, ?_⟩
  · intro sender wire sent wake deadline b honest emit decode valid outstanding
    have hb : wire.payload = b := Option.some.inj decode
    exact (valid (hb.symm.trans outstanding)).elim
  · simp [dependencyResolved, dependencyRefused]

private theorem do_retained_outcome_countermodel :
    FGReceiptOrigin do_env do_run do_history do_wireReads false 2 do_child ∧
    ¬ Effect do_history do_reads 0 2 do_child ∧
    ¬ dependencyResolved do_history do_reads 0 2 := by
  exact ⟨do_child_origin, by simp [Effect, dependencyResolved, dependencyRefused],
    by simp [dependencyResolved, dependencyRefused]⟩

/-- The first valid receipt cannot disappear before pending retention has a premise. -/
private noncomputable abbrev do_lostTrace : FGDependencyTrace Nat :=
  { do_trace with state := fun k => if k ≤ 2 then 0 else do_trace.state k }

private noncomputable abbrev do_lostDriver : FGDependencyDriver Bool (Fin 4) do_protocol :=
  { do_driver with enter := fun st wire o =>
      if wire.payload = 2 then st else do_driver.enter st wire o }

private def do_silentArrival (a : Nat) (b : Fin 4)
    (o : FGReceiptToken Bool do_protocol.Object) (z : Nat) : Prop :=
  do_arrival a b o z ∨ (a = 0 ∧ b = 2 ∧ o = do_child ∧ z = 0)

private theorem do_silent_first_receipt_rejected :
    FGReceiptOrigin do_env do_run do_history do_wireReads false 2 do_child ∧
    ¬ FGDependencyTraceLaws do_env do_run false do_history do_wireReads do_reads do_leaf
      do_step do_lostTrace do_lostDriver do_op do_silentArrival do_notify
      (Leaf := do_leafProtocol) id id do_read := by
  refine ⟨do_child_origin, ?_⟩
  intro laws
  have effect := (laws.receipt_entry 0 (do_wire 2) 0 2 rfl rfl rfl rfl).2.2 trivial
  have absent : ¬ Effect do_history do_reads 0 2 do_child := by
    simp [Effect, dependencyResolved, dependencyRefused]
  exact absent effect

/-- A real receipt and a hypothetical conflicting leaf do not justify a run refusal. -/
private noncomputable abbrev do_badRefusalReads : FGDependencyReads Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) Nat :=
  { do_reads with
    accepted := fun st b => b = 0 ∨ (b = 1 ∧ 3 ≤ st)
    refused := fun st b r pr => 4 ≤ st ∧ b = 2 ∧ r = do_history.root b ∧
      pr = do_history.root (do_history.parent b)
    priorChecks := fun st b => do_reads.priorChecks st b ∨ (st = 99 ∧ b = 2)
    conflictsFinal := fun st _ => st = 99 }

private noncomputable abbrev do_hypotheticalLeaf : FGDependencyLeaf Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) :=
  { do_leaf with
    step := fun a b o result z => do_leaf.step a b o result z ∨
      (a = 99 ∧ b = 2 ∧ o = do_child ∧ result = .definitiveRefused ∧ z = 100)
    report := fun a b o z => a = 99 ∧ b = 2 ∧ o = do_child ∧ z = 100 }

private theorem do_hypothetical_refusal_rejected :
    FGReceiptOrigin do_env do_run do_history do_wireReads false 2 do_child ∧
    do_hypotheticalLeaf.step 99 2 do_child .definitiveRefused 100 ∧
    do_badRefusalReads.accepted 99 (do_history.parent 2) ∧
    do_badRefusalReads.conflictsFinal 99 2 ∧
    ¬ do_badRefusalReads.conflictsFinal (do_trace.state 9) 2 ∧
    ¬ FGDependencyTraceLaws do_env do_run false do_history do_wireReads
      do_badRefusalReads do_hypotheticalLeaf do_step do_trace do_driver do_op
      do_arrival do_notify (Leaf := do_leafProtocol) id id do_read := by
  refine ⟨do_child_origin, Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩,
    Or.inr ⟨rfl, by decide⟩, rfl, by decide, ?_⟩
  intro laws
  have created := laws.refusal_creation 9 2 (by decide)
    ⟨by decide, rfl, rfl, rfl⟩ (by simp [dependencyRefused])
  rcases created with ⟨o, operation, _⟩ | ⟨o, operation, _⟩
  · cases operation
  · rcases operation with operation | operation <;> cases operation

#print axioms do_silent_first_receipt_rejected
#print axioms do_hypothetical_refusal_rejected

private noncomputable abbrev do_silentNotificationReads : FGDependencyReads Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) Nat :=
  { do_reads with notified := fun st b => b = 0 ∨ (b = 1 ∧ 3 ≤ st) ∨ (b = 2 ∧ 4 ≤ st) }

private theorem do_status_flag_without_hook_rejected :
    ¬ FGDependencyTraceLaws do_env do_run false do_history do_wireReads
      do_silentNotificationReads do_leaf do_step do_trace do_driver do_op
      do_arrival do_notify (Leaf := do_leafProtocol) id id do_read := by
  intro laws
  obtain ⟨o, operation, _⟩ := laws.notification_creation 8 1 (by decide)
    (by simp) (by simp)
  cases operation

private noncomputable abbrev do_changedKeys : FGDependencyReads Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) Nat :=
  { do_reads with latestKey := fun st _ => if st < 5 then some (2, ⟨2⟩) else none }

private theorem do_notification_key_change_rejected :
    ¬ FGDependencyArrivalLeafLaws do_history do_changedKeys do_leaf do_arrival do_notify := by
  intro laws
  have eq := congrFun (laws.notification_keys 4 5 1 (Or.inl ⟨rfl, rfl, rfl⟩)) 0
  change none = some (2, (⟨2⟩ : BlockId)) at eq
  cases eq

private noncomputable abbrev do_futureOriginReads : FGDependencyReads Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) Nat :=
  { do_reads with originAvailable := fun st b o => do_reads.originAvailable st b o ∨
      (st = 1 ∧ b = 1 ∧ o = do_parent) }

private theorem do_future_origin_at_run_cut_rejected :
    ¬ FGDependencyTraceLaws do_env do_run false do_history do_wireReads
      do_futureOriginReads do_leaf do_step do_trace do_driver do_op
      do_arrival do_notify (Leaf := do_leafProtocol) id id do_read := by
  intro laws
  have order := (laws.origin_valid 1 1 do_parent (by decide)
    (Or.inr ⟨rfl, rfl, rfl⟩)).2
  change 7 < 1 at order
  omega

/-- The parent receipt has four real work transitions after its entry boundary. -/
private theorem do_nonempty_entry_segment :
    do_trace.entryCut 2 < do_trace.done 2 ∧
    FGDependencySteps do_step false (do_trace.state (do_trace.entryCut 2))
      (do_trace.state (do_trace.done 2)) := by
  refine ⟨by decide, ?_⟩
  have s1 : do_step .leafRetry false 2 3 := by simp [do_step]
  have s2 : do_step .leafRetry false 3 4 := by simp [do_step]
  have s3 : do_step .notification false 4 5 := by simp [do_step]
  have s4 : do_step .notification false 5 6 := by simp [do_step]
  exact .tail .notification (.tail .notification
    (.tail .leafRetry (.tail .leafRetry (.refl 2) s1) s2) s3) s4

private noncomputable abbrev do_ordinaryProtocol : V2.ProtocolSpecD Unit :=
  { do_protocol with process := fun st wire =>
      if wire.payload = 0 then st + 1 else do_protocol.process st wire }

private noncomputable abbrev do_ordinaryRun : V2.D.Run Bool do_ordinaryProtocol :=
  { do_run with events := [.deliver false (do_wire 0) 0] }

private noncomputable abbrev do_ordinaryWireReads :
    FGDependencyWireReads do_ordinaryProtocol (Fin 4) Nat :=
  { do_wireReads with decodeBody := fun wire =>
      if wire.payload = 0 then none else some wire.payload }

private noncomputable abbrev do_silentOrdinaryDriver :
    FGDependencyDriver Bool (Fin 4) do_ordinaryProtocol where
  enter st _ _ := st
  enterProgram st _ _ := .finish st
  hookProgram st _ := .finish st
  drain := id
  reconstruct st _ := st
  rebuild st _ := st
  retry st _ _ _ := st
  work _ _ := []
  inheritRefusal st _ _ := st
  notify st _ _ := st
  replay st _ _ := st

private noncomputable abbrev do_ordinaryTrace : FGDependencyTrace Nat where
  length := 1
  state _ := 0
  time _ := 0
  start _ := 0
  entryCut _ := 1
  dutyCut _ := 1
  done _ := 1
  readCut _ := 1
  hookRead _ _ _ _ _ := False

/-- The actual standalone input changes knowledge. An idle entry is rejected. -/
private theorem do_silent_ordinary_rejected :
    do_ordinaryProtocol.process 0 (do_wire 0) = 1 ∧
    dependencyStateBefore do_env do_ordinaryRun do_silentOrdinaryDriver false 1 = 0 ∧
    ¬ FGDependencyTraceLaws do_env do_ordinaryRun false do_history do_ordinaryWireReads
      do_reads do_leaf do_step do_ordinaryTrace do_silentOrdinaryDriver (fun _ => .idle)
      do_arrival do_notify (Leaf := do_leafProtocol) id id (fun _ _ _ => False) := by
  refine ⟨rfl, rfl, ?_⟩
  intro laws
  have bad := laws.delivery_entry 0 (do_wire 0) 0 rfl
  change FGDependencyOperation.idle = .ordinary (do_wire 0) at bad
  cases bad

private noncomputable abbrev do_otherOrdinary : do_protocol.Object := ⟨.none, 0⟩

private noncomputable abbrev do_substitutedDriver :
    FGDependencyDriver Bool (Fin 4) do_ordinaryProtocol :=
  { do_silentOrdinaryDriver with
    enter := fun st _ _ => do_ordinaryProtocol.process st do_otherOrdinary
    enterProgram := fun st _ _ => .finish (do_ordinaryProtocol.process st do_otherOrdinary) }

private noncomputable abbrev do_substitutedTrace : FGDependencyTrace Nat :=
  { do_ordinaryTrace with state := fun k => if k = 0 then 0 else 1 }

private theorem do_substituted_ordinary_wire_rejected :
    do_ordinaryWireReads.decodeBody (do_wire 0) = none ∧
    do_ordinaryWireReads.decodeBody do_otherOrdinary = none ∧
    do_ordinaryProtocol.wellFormed do_otherOrdinary = true ∧
    dependencyStateBefore do_env do_ordinaryRun do_substitutedDriver false 1 = 1 ∧
    ¬ FGDependencyTraceLaws do_env do_ordinaryRun false do_history do_ordinaryWireReads
      do_reads do_leaf do_step do_substitutedTrace do_substitutedDriver
      (fun _ => .ordinary do_otherOrdinary) do_arrival do_notify
      (Leaf := do_leafProtocol) id id (fun _ _ _ => False) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro laws
  have bad := laws.delivery_entry 0 (do_wire 0) 0 rfl
  change FGDependencyOperation.ordinary do_otherOrdinary = .ordinary (do_wire 0) at bad
  have auth := congrArg V2.Signed.auth (FGDependencyOperation.ordinary.inj bad)
  cases auth

private noncomputable abbrev do_rejectedRun : V2.D.Run Bool do_protocol :=
  { do_run with events := [.deliver false (do_wire 3) 0] }

private theorem do_rejected_delivery_bound :
    ¬ FGDependencyTraceLaws do_env do_rejectedRun false do_history do_wireReads
      do_reads do_leaf do_step do_trace do_driver (fun _ => .idle) do_arrival do_notify
      (Leaf := do_leafProtocol) id id do_read := by
  intro laws
  have bad := laws.delivery_entry 0 (do_wire 3) 0 rfl
  change FGDependencyOperation.idle = .rejected (do_wire 3) at bad
  cases bad

private theorem do_omitted_hook_read_rejected :
    ¬ FGDependencyTraceLaws do_env do_run false do_history do_wireReads do_reads do_leaf
      do_step { do_trace with hookRead := fun _ _ _ _ _ => False } do_driver do_op
      do_arrival do_notify (Leaf := do_leafProtocol) id id do_read := by
  intro laws
  have actual := (laws.hook_correspondence 2 (.deliver false (do_wire 1) 1)
    0 .ac 12 6 rfl).mpr ⟨⟨4, .ac, 6⟩, rfl, rfl, rfl, rfl⟩
  exact actual

private noncomputable abbrev do_entryReadDriver : FGDependencyDriver Bool (Fin 4) do_protocol :=
  { do_driver with
    enterProgram := fun st wire o => .read .ac (do_driver.enter st wire o) .finish }

private theorem do_omitted_entry_read_rejected :
    ¬ FGDependencyTraceLaws do_env do_run false do_history do_wireReads do_reads do_leaf
      do_step do_trace do_entryReadDriver do_op do_arrival do_notify
      (Leaf := do_leafProtocol) id id do_read := by
  intro laws
  have actual := (laws.hook_correspondence 0 (.deliver false (do_wire 2) 0)
    0 .ac 1 1 rfl).mpr ⟨⟨0, .ac, 1⟩, rfl, rfl, rfl, rfl⟩
  cases actual.1

#print axioms do_omitted_entry_read_rejected

private theorem do_hook_read_nonempty_completion :
    do_trace.hookRead 2 0 .ac 12 6 ∧ do_trace.entryCut 2 < 12 ∧
    FGDependencySteps do_step false (do_trace.state (do_trace.entryCut 2)) 6 ∧
    dependencyClosed do_history do_reads 6 := by
  have completed := dependency_hook_read_completion do_trace_laws
    (e := .deliver false (do_wire 1) 1) rfl
    (show do_trace.hookRead 2 0 .ac 12 6 from ⟨rfl, rfl, rfl, rfl, rfl⟩)
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by decide, completed.2.2.2⟩

private theorem do_hook_original_receipt_and_rows :
    (∃ o, FGReceiptOrigin do_env do_run do_history do_wireReads false 2 o ∧
      do_wireReads.proposalErase o.wire = some (do_body 2) ∧
      do_wireReads.decodedRows o.wire = [2]) ∧
    FGReceiptOrigin do_env do_run do_history do_wireReads false 2 do_child ∧
    do_trace.start do_child.eventIndex < 12 := by
  have read : do_trace.hookRead 2 0 .ac 12 6 := ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨dependency_hook_accepted_origin_bridge do_trace_laws
      (e := .deliver false (do_wire 1) 1) rfl read
      (Or.inr (Or.inr ⟨rfl, by decide⟩)) (by decide),
    dependency_hook_origin_at_read do_trace_laws
      (e := .deliver false (do_wire 1) 1) rfl read (Or.inl ⟨rfl, by decide, rfl⟩)⟩

#print axioms do_hook_original_receipt_and_rows

/-- The public record rejects the former reflexive witness at a substituted closed cut. -/
private theorem do_substituted_closed_start_rejected :
    dependencyClosed do_history do_reads (do_trace.state 12) ∧
    ¬ FGDependencyReadClosureLaws do_env do_run false do_history do_reads do_step
      do_trace do_driver (fun i => { do_site i with entryCut := 12 }) do_read
      do_wireReads do_leaf do_op do_arrival do_notify (Leaf := do_leafProtocol) id id := by
  refine ⟨do_closed 6 (Or.inr rfl), ?_⟩
  intro laws
  obtain ⟨e, event, _, _, entry, _⟩ :=
    laws.site_correspondence 12 6 ⟨by decide, by decide, rfl⟩
  change 12 = 14 at entry
  omega

private theorem do_substituted_hook_start_rejected :
    FGDependencyEnabled do_history do_reads (do_trace.state (do_trace.entryCut 2)) ∧
    dependencyClosed do_history do_reads (do_trace.state 12) ∧
    ¬ FGDependencyReadClosureLaws do_env do_run false do_history do_reads do_step
      { do_trace with entryCut := fun j => if j = 2 then 12 else do_trace.entryCut j }
      do_driver do_site do_read do_wireReads do_leaf do_op do_arrival do_notify
      (Leaf := do_leafProtocol) id id := by
  refine ⟨?_, do_closed 6 (Or.inr rfl), ?_⟩
  · exact .retry 1 do_parent (Or.inr ⟨rfl, rfl, rfl⟩) (by decide)
      (Or.inl ⟨rfl, rfl⟩) trivial (Or.inl rfl)
      (by simp [dependencyResolved, dependencyRefused])
  · intro laws
    have wrong := (laws.trace_bound.entry_boundary 2 (.deliver false (do_wire 1) 1) rfl).1
    change 12 = 8 at wrong
    omega

#print axioms do_substituted_hook_start_rejected

private theorem do_wrong_read_kind_rejected :
    ¬ FGDependencyReadClosureLaws do_env do_run false do_history do_reads do_step
      do_trace do_driver (fun i => { do_site i with kind := .ac }) do_read
      do_wireReads do_leaf do_op do_arrival do_notify (Leaf := do_leafProtocol) id id := by
  intro laws
  obtain ⟨e, event, _, index, _⟩ :=
    laws.site_correspondence 12 6 ⟨by decide, by decide, rfl⟩
  change 12 = 15 at index
  omega

private theorem do_silence_fresh_refusal_rejected :
    ¬ FGDependencyTraceLaws do_env do_run false do_history do_wireReads
      do_badRefusalReads do_hypotheticalLeaf do_step do_trace do_driver
      (fun _ => .idle) do_arrival do_notify (Leaf := do_leafProtocol) id id do_read := by
  intro laws
  have created := laws.refusal_creation 9 2 (by decide)
    ⟨by decide, rfl, rfl, rfl⟩ (by simp [dependencyRefused])
  rcases created with ⟨o, operation, _⟩ | ⟨o, operation, _⟩
  · cases operation
  · rcases operation with operation | operation <;> cases operation

/-- A standalone PC-like object changes a latest key and enables a retained-body companion. -/
private noncomputable abbrev do_pcProtocol : V2.ProtocolSpecD Unit :=
  { do_protocol with process := fun st wire =>
      if st = 6 ∧ wire.payload = 0 then 7 else do_protocol.process st wire }

private noncomputable abbrev do_pcRun : V2.D.Run Bool do_pcProtocol :=
  { do_run with events := do_run.events ++ [.deliver false (do_wire 0) 5] }

private noncomputable abbrev do_pcReads : FGDependencyReads Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) Nat :=
  { do_reads with
    companionHeld := fun st b => b = 2 ∧ 6 ≤ st ∧ st ≠ 7
    latestKey := fun st _ => some (if 7 ≤ st then 3 else 2, do_history.root 2)
    latestCompanion := fun st _ => if 6 ≤ st ∧ st ≠ 7 then some 2 else none }

private noncomputable abbrev do_pcDriver : FGDependencyDriver Bool (Fin 4) do_pcProtocol :=
  { do_driver with
    enter := fun st wire o => if wire.payload = 0 then do_pcProtocol.process st wire
      else do_driver.enter st wire o
    enterProgram := fun st wire o => if wire.payload = 0 then
      .finish (do_pcProtocol.process st wire) else do_driver.enterProgram st wire o
    hookProgram := fun st op => match op with
      | .notification b _ => if st = 7 ∧ b = 2 then .read .ac 8 .finish
          else do_driver.hookProgram st op
      | _ => do_driver.hookProgram st op
    drain := fun st => if st = 7 then 8 else do_driver.drain st
    notify := fun st b o => if st = 7 ∧ b = 2 then 8 else do_driver.notify st b o
    work := fun st e => if st = 7 then [.step (.notification 2 do_child)]
      else do_driver.work st e }

private noncomputable abbrev do_pcWireReads : FGDependencyWireReads do_pcProtocol (Fin 4) Nat :=
  { do_wireReads with decodeBody := do_ordinaryWireReads.decodeBody }

private noncomputable abbrev do_pcNotify (a : Nat) (b : Fin 4) (z : Nat) : Prop :=
  do_notify a b z ∨ (a = 7 ∧ b = 2 ∧ z = 8)

private theorem do_pc_hook_laws :
    FGDependencyArrivalLeafLaws do_history do_pcReads do_leaf do_arrival do_pcNotify :=
  { do_arrival_laws with
    notification_resolved := by
      intro a z b h
      rcases h with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) | ⟨rfl, rfl, rfl⟩ <;>
        simp [dependencyResolved, dependencyRefused]
    notification_keys := by
      intro a z b h
      rcases h with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) | ⟨rfl, rfl, rfl⟩ <;> rfl
    notification_fields := by
      intro a z b i h unmatched
      rcases h with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) | ⟨rfl, rfl, rfl⟩
      · rfl
      · simp at unmatched
      · simp at unmatched
    notification_matching := by
      intro a z b i slot h held matching
      rcases h with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) | ⟨rfl, rfl, rfl⟩
      · have bad : (2 : Nat) = 1 :=
          congrArg BlockId.value (congrArg Prod.snd (Option.some.inj matching))
        omega
      · rfl
      · rfl
    refused_notification := by intro _ _ _ _ h; exact h.elim
    callback_latest := by
      intro a z b h held
      rcases h with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) | ⟨rfl, rfl, rfl⟩ <;>
        decide +kernel }

private theorem do_retained_processing_hook_effect :
    do_pcNotify 7 2 8 ∧
    do_pcReads.latestKey 7 0 = some (3, do_history.root 2) ∧
    do_pcReads.latestKey 8 0 = do_pcReads.latestKey 7 0 ∧
    do_pcReads.latestCompanion 7 0 = none ∧ do_pcReads.latestCompanion 8 0 = some 2 ∧
    (dependencyExecuteWork do_pcDriver 7
      (do_pcDriver.work 7 (.deliver false (do_wire 0) 5))).reads = [⟨1, .ac, 8⟩] :=
  ⟨Or.inr ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

#print axioms do_pc_hook_laws
#print axioms do_retained_processing_hook_effect

private theorem do_retained_processing_enables_and_completes :
    dependencyStateBefore do_env do_pcRun do_pcDriver false 4 = 6 ∧
    FGReceiptOrigin do_env do_pcRun do_history do_pcWireReads false 2 do_child ∧
    Effect do_history do_pcReads 6 1 do_parent ∧
    Effect do_history do_pcReads 6 2 do_child ∧
    do_pcProtocol.process 6 (do_wire 0) = 7 ∧
    dependencyEventEntry do_pcRun do_pcDriver false 4 6
      (.deliver false (do_wire 0) 5) = 7 ∧
    FGDependencyEnabled do_history do_pcReads 7 ∧
    (dependencyExecuteWork do_pcDriver 7
      (do_pcDriver.work 7 (.deliver false (do_wire 0) 5))).operations =
      [.notification 2 do_child] ∧
    dependencyStateBefore do_env do_pcRun do_pcDriver false 5 = 8 ∧
    dependencyClosed do_history do_pcReads 8 ∧
    do_pcReads.companionHeld (do_pcReads.latest 8) 2 := by
  refine ⟨rfl, ?_, ?_, ?_, rfl, rfl, ?_, rfl, rfl, ?_, ?_⟩
  · constructor <;> rfl
  · simp [Effect, dependencyResolved, dependencyRefused]
  · simp [Effect, dependencyResolved, dependencyRefused]
  · exact .companion 2 (Or.inr (Or.inr ⟨rfl, by decide⟩)) rfl (by simp)
  · intro work
    cases work <;> simp_all [dependencyResolved, dependencyRefused]
  · exact ⟨rfl, by decide, by decide⟩

#print axioms do_silent_ordinary_rejected
#print axioms do_substituted_ordinary_wire_rejected
#print axioms do_rejected_delivery_bound
#print axioms do_omitted_hook_read_rejected
#print axioms do_hook_read_nonempty_completion
#print axioms do_substituted_closed_start_rejected
#print axioms do_wrong_read_kind_rejected
#print axioms do_silence_fresh_refusal_rejected
#print axioms do_retained_processing_enables_and_completes

#print axioms do_status_flag_without_hook_rejected
#print axioms do_notification_key_change_rejected
#print axioms do_future_origin_at_run_cut_rejected
#print axioms do_nonempty_entry_segment

#print axioms do_read_closure_laws
#print axioms do_bridge_original_child_rows
#print axioms do_honest_old_send
#print axioms do_awake_guard_countermodel
#print axioms do_horizon_guard_countermodel
#print axioms do_validation_guard_countermodel
#print axioms do_retained_outcome_countermodel
#print axioms do_weak_delayed_model
#print axioms do_delayed_child_countermodel
#print axioms do_delayed_notification_countermodel
#print axioms do_early_read_countermodel
#print axioms do_future_in_range_receipt
#print axioms do_positive_strict_no_early_read
#print axioms do_retained_only_path_consumer
#print axioms do_state_laws
#print axioms do_arrival_laws
#print axioms do_step_laws
#print axioms do_trace_laws
#print axioms do_child_origin
#print axioms do_parent_origin
#print axioms do_same_time_positive
#print axioms do_original_epoch_after_restart
#print axioms do_wrong_receiver
#print axioms do_same_root_forgery
#print axioms do_epoch_forgery
#print axioms do_future_forgery
#print axioms do_delayed_drain_enabled
#print axioms do_delayed_notification_enabled
#print axioms do_later_read_closed_but_late
#print axioms do_retained_only_entry
#print axioms do_terminal_equality_not_strict

/-- Restart reconstruction on two retained non-genesis carriers, in parent order. -/
private noncomputable abbrev dr4_protocol : V2.ProtocolSpecD Unit :=
  { do_protocol with restore := fun st _ => if st = 6 then 7 else st }

private noncomputable abbrev dr4_wireReads :
    FGDependencyWireReads dr4_protocol (Fin 4) Nat where
  decodeBody := do_wireReads.decodeBody
  namedRoots := do_wireReads.namedRoots
  proposalErase := do_wireReads.proposalErase
  decodedRows := do_wireReads.decodedRows
  bodyRows := do_wireReads.bodyRows

private noncomputable abbrev dr4_run : V2.D.Run Bool dr4_protocol :=
  { do_run with events := [.deliver false (do_wire 2) 0, .restart false 1,
    .deliver false (do_wire 1) 1, .tick false 4, .restart false 5] }

private noncomputable abbrev dr4_reads : FGDependencyReads Nat (Fin 4)
    (FGReceiptToken Bool dr4_protocol.Object) Nat :=
  { do_reads with
    matching := fun st b => st ≠ 7 ∧ b = 2
    companionHeld := fun st b => b = 2 ∧ 6 ≤ st ∧ st ≠ 8 ∧ st ≠ 9
    latestKey := fun st _ => if st = 7 then none
      else some (if 8 ≤ st then 3 else 2, do_history.root 2)
    latestCompanion := fun st _ =>
      if 6 ≤ st ∧ st ≠ 7 ∧ st ≠ 8 ∧ st ≠ 9 then some 2 else none }

private noncomputable abbrev dr4_driver : FGDependencyDriver Bool (Fin 4) dr4_protocol :=
  { do_driver with
    replay := fun st b _ => if st = 7 ∧ b = 1 then 8 else st
    rebuild := fun st _ => if st = 8 then 9 else st
    drain := fun st => if st = 9 then 10 else do_driver.drain st
    hookProgram := fun st op => match op with
      | .replay b _ => if st = 7 ∧ b = 1 then .finish 8
          else if st = 9 ∧ b = 2 then .read .ac st .finish else .finish st
      | .rebuild _ => .finish (if st = 8 then 9 else st)
      | .notification b _ => if st = 9 ∧ b = 2 then .read .ac 10 .finish
          else do_driver.hookProgram st op
      | _ => do_driver.hookProgram st op
    notify := fun st b o => if st = 9 ∧ b = 2 then 10 else do_driver.notify st b o
    work := fun st e => if st = 7 then
      [.step (.reconstruct 5), .step (.replay 1 do_parent),
        .step (.replay 2 do_child), .step (.rebuild 5), .step (.notification 2 do_child)]
      else do_driver.work st e }

private noncomputable abbrev dr4_notify (a : Nat) (b : Fin 4) (z : Nat) : Prop :=
  do_notify a b z ∨ (a = 9 ∧ b = 2 ∧ z = 10)

private noncomputable abbrev dr4_step (kind : FGDependencyStepKind) (x : Bool)
    (a z : Nat) : Prop :=
  do_step kind x a z ∨ (kind = .restore ∧ a = 6 ∧ z = 7) ∨
    (kind = .ordinary ∧ a = 7 ∧ z = 8) ∨ (kind = .notification ∧ a = 9 ∧ z = 10) ∨
    (kind = .ordinary ∧ a = 8 ∧ z = 9)

private noncomputable abbrev dr4_op (k : Nat) :
    FGDependencyOperation (Fin 4) (FGReceiptToken Bool dr4_protocol.Object)
      dr4_protocol.Object :=
  match k with
  | 0 => .arrival 2 do_child
  | 3 => .restore 1
  | 4 => .reconstruct 1
  | 5 => .rebuild 1
  | 7 => .arrival 1 do_parent
  | 8 => .leaf 1 do_parent .accepted
  | 9 => .leaf 2 do_child .accepted
  | 10 => .notification 1 do_parent
  | 11 => .notification 2 do_child
  | 13 => .clock 4
  | 15 => .restore 5
  | 16 => .reconstruct 5
  | 17 => .replay 1 do_parent
  | 18 => .replay 2 do_child
  | 19 => .rebuild 5
  | 20 => .notification 2 do_child
  | _ => .idle

private noncomputable abbrev dr4_trace : FGDependencyTrace Nat where
  length := 21
  state k := [0, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 6, 6, 6, 7, 7, 8, 8, 9, 10][k]?.getD 10
  time k := [0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 5, 5, 5, 5, 5, 5][k]?.getD 5
  start j := [0, 3, 7, 13, 15][j]?.getD 21
  done j := [2, 6, 12, 14, 21][j]?.getD 21
  readCut _ := 14
  entryCut j := [1, 4, 8, 14, 16][j]?.getD 21
  dutyCut j := [2, 5, 12, 14, 17][j]?.getD 21
  hookRead j index kind cut st := do_trace.hookRead j index kind cut st ∨
    (j = 4 ∧ kind = .ac ∧ index = 0 ∧ cut = 21 ∧ st = 10)

private theorem dr4_child_origin :
    FGReceiptOrigin do_env dr4_run do_history dr4_wireReads false 2 do_child := by
  constructor <;> rfl

private theorem dr4_parent_origin :
    FGReceiptOrigin do_env dr4_run do_history dr4_wireReads false 1 do_parent := by
  constructor <;> rfl

private theorem dr4_closed (st : Nat) (h : st = 1 ∨ st = 6 ∨ st = 7 ∨ st = 10) :
    dependencyClosed do_history dr4_reads st := by
  rcases h with rfl | rfl | rfl | rfl <;> intro work <;> cases work <;>
    simp_all [dependencyResolved, dependencyRefused]

private theorem dr4_events_bound {j : Nat} {e : V2.Event Bool dr4_protocol.Object}
    (h : dr4_run.events[j]? = some e) : j < 5 :=
  (List.getElem?_eq_some_iff.mp h).1

private theorem dr4_micro_steps (k : Nat) (hk : k < dr4_trace.length) :
    ∃ kind, dr4_step kind false (dr4_trace.state k) (dr4_trace.state (k + 1)) := by
  change k < 21 at hk
  interval_cases k <;> solve
    | exact ⟨.ordinary, Or.inl (Or.inl rfl)⟩
    | (refine ⟨.arrival, ?_⟩; simp [dr4_step, do_step])
    | (refine ⟨.leafRetry, ?_⟩; simp [dr4_step, do_step])
    | (refine ⟨.notification, ?_⟩; simp [dr4_step, do_step])
    | (refine ⟨.restore, ?_⟩; simp [dr4_step, do_step])
    | (refine ⟨.ordinary, ?_⟩; simp [dr4_step, do_step])

private theorem dr4_entry_steps (x : Bool) : FGDependencySteps dr4_step x 2 6 := by
  have lift : ∀ a z, FGDependencySteps do_step x a z → FGDependencySteps dr4_step x a z := by
    intro a z steps
    induction steps with
    | refl => exact .refl _
    | tail k _ h ih => exact .tail k ih (Or.inl h)
  exact lift _ _ (do_entry_steps x)

private theorem dr4_replay_steps : FGDependencySteps dr4_step false 7 10 :=
  .tail .notification (.tail .ordinary (.tail .ordinary (.refl _)
    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))))
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))

private theorem dr4_hook_laws :
    FGDependencyArrivalLeafLaws do_history dr4_reads do_leaf do_arrival dr4_notify :=
  { do_arrival_laws with
    notification_resolved := by
      intro a z b h
      rcases h with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) | ⟨rfl, rfl, rfl⟩ <;>
        simp [dependencyResolved, dependencyRefused]
    notification_keys := by
      intro a z b h
      rcases h with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) | ⟨rfl, rfl, rfl⟩ <;> rfl
    notification_fields := by
      intro a z b i h unmatched
      rcases h with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) | ⟨rfl, rfl, rfl⟩
      · rfl
      · simp at unmatched
      · simp at unmatched
    notification_matching := by
      intro a z b i slot h held matching
      rcases h with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) | ⟨rfl, rfl, rfl⟩
      · have bad : (2 : Nat) = 1 :=
          congrArg BlockId.value (congrArg Prod.snd (Option.some.inj matching))
        omega
      · rfl
      · rfl
    refused_notification := by intro _ _ _ _ h; exact h.elim
    callback_latest := by
      intro a z b h held
      rcases h with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) | ⟨rfl, rfl, rfl⟩ <;>
        first | decide +kernel | simp }


private theorem dr4_state_laws : FGDependencyStateLaws do_history dr4_reads do_leaf :=
  { do_state_laws with }

private theorem dr4_step_laws :
    FGDependencyStepLaws do_history dr4_reads do_leaf dr4_step (fun s t => dr4_protocol.restore s t)
      (fun _ _ => False) where
  accepted_keep k x a z b step held := by
    have le : a ≤ z := by rcases step with (h | h | h | h) | h | h | h | h <;> omega
    rcases held with rfl | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, Nat.le_trans h le⟩)
    · exact Or.inr (Or.inr ⟨rfl, Nat.le_trans h le⟩)
  refused_keep _ _ _ _ _ _ _ _ h := h.elim
  pending_effect k x a z b o step pending := by
    have le : a ≤ z := by rcases step with (h | h | h | h) | h | h | h | h <;> omega
    rcases pending with ⟨rfl, ha, hb, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · refine ⟨Or.inl ⟨rfl, by omega, rfl⟩, ?_⟩
      by_cases hz : z < 4
      · exact Or.inl (Or.inl ⟨rfl, by omega, hz, rfl⟩)
      · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨rfl, by omega⟩)))
    · refine ⟨Or.inr ⟨rfl, le, rfl⟩, ?_⟩
      by_cases hz : z = 2
      · exact Or.inl (Or.inr ⟨rfl, hz, rfl⟩)
      · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨rfl, by omega⟩)))
  origin_keep k x a z b o step origin := by
    have le : a ≤ z := by rcases step with (h | h | h | h) | h | h | h | h <;> omega
    rcases origin with ⟨rfl, h, rfl⟩ | ⟨rfl, h, rfl⟩
    · exact Or.inl ⟨rfl, Nat.le_trans h le, rfl⟩
    · exact Or.inr ⟨rfl, Nat.le_trans h le, rfl⟩
  metadata_fg_eq k x a z step notArrival notLeaf := by
    rcases step with old | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩
    · exact do_step_laws.metadata_fg_eq k x a z old notArrival notLeaf
    all_goals rfl
  insertion_leaf k x a z b step held fresh := by
    rcases step with old | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩
    · exact do_step_laws.insertion_leaf k x a z b old held fresh
    all_goals simp_all
  one_body a z b o result leaf c held := by
    rcases leaf with ⟨rfl, (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩)⟩
    all_goals simp_all
    all_goals tauto
  restore_exact st t := by
    by_cases h : st = 6
    · subst st
      simp [dr4_protocol]
    · simp [dr4_protocol, h]
  no_signing _ _ _ _ _ := not_false


private theorem dr4_trace_facts (k : Nat) (hk : k ≤ 21) :
    (1 ≤ dr4_trace.state k → dr4_trace.start 0 < k) ∧
    (2 ≤ dr4_trace.state k → dr4_trace.start 2 < k) ∧
    (∀ b, dr4_reads.notified (dr4_trace.state (k + 1)) b →
      ¬ dr4_reads.notified (dr4_trace.state k) b →
      (k = 10 ∧ b = 1) ∨ (k = 11 ∧ b = 2)) ∧
    (∀ b, dr4_reads.accepted (dr4_trace.state (k + 1)) b →
      ¬ dr4_reads.accepted (dr4_trace.state k) b →
      (k = 8 ∧ b = 1) ∨ (k = 9 ∧ b = 2)) := by
  interval_cases k <;> refine ⟨by decide, by decide, ?_, ?_⟩ <;> decide

set_option maxHeartbeats 800000 in
-- Finite cases cover 21 microsteps, five events, and one read in the restart segment.
private theorem dr4_trace_laws :
    FGDependencyTraceLaws do_env dr4_run false do_history dr4_wireReads dr4_reads do_leaf
      dr4_step dr4_trace dr4_driver dr4_op do_arrival dr4_notify
      (Leaf := do_leafProtocol) id id do_read where
  arrival_laws := dr4_hook_laws
  initial := rfl
  initial_accepted b h := by simpa [dr4_reads, do_protocol, do_leaf] using h
  micro_step := dr4_micro_steps
  external_step j e h := by
    have hj := dr4_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> exact ⟨rfl, rfl⟩
  step_kind k hk := by
    change k < 21 at hk
    interval_cases k <;> decide
  operation_bound k hk := by
    change k < 21 at hk
    interval_cases k <;> simp only [dr4_op]
    all_goals first
      | rfl
      | exact ⟨Or.inl ⟨rfl, rfl, rfl, rfl⟩, rfl, dr4_child_origin, rfl⟩
      | exact ⟨Or.inr ⟨rfl, rfl, rfl, rfl⟩, rfl, dr4_parent_origin, rfl⟩
      | exact ⟨rfl, 1, rfl, rfl⟩
      | exact ⟨rfl, 4, rfl, rfl⟩
      | exact ⟨rfl, 1, rfl, by decide, by decide, fun q lo hi => by
          norm_num at lo hi; interval_cases q⟩
      | exact ⟨rfl, 4, rfl, by decide, by decide, fun q lo hi => by
          norm_num at lo hi; interval_cases q <;> simp⟩
      | simp [dependencyResolved, dependencyRefused, dr4_notify, do_notify]
  delivery_entry j wire t h := by
    have hj := dr4_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> rfl
  work_execution j e h := by
    have hj := dr4_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> exact ⟨rfl, rfl⟩
  work_step j e k h lo hi := by
    have hj := dr4_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      norm_num [dr4_trace] at lo hi <;> interval_cases k <;> rfl
  hook_correspondence j e index kind cut st h := by
    have hj := dr4_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e
    · change ((0 = 2 ∧ _) ∨ (0 = 4 ∧ _)) ↔
        ∃ r, ([] : List (FGDependencyWorkRead Nat))[index]? = some r ∧ _
      simp
    · change ((1 = 2 ∧ _) ∨ (1 = 4 ∧ _)) ↔
        ∃ r, ([] : List (FGDependencyWorkRead Nat))[index]? = some r ∧ _
      simp
    · change ((2 = 2 ∧ index = 0 ∧ kind = .ac ∧ cut = 12 ∧ st = 6) ∨
        (2 = 4 ∧ _)) ↔
        ∃ r, ([⟨4, .ac, 6⟩] : List (FGDependencyWorkRead Nat))[index]? = some r ∧
          r.kind = kind ∧ cut = 8 + r.offset ∧ st = r.consumed
      cases index <;> simp [eq_comm]
    · change ((3 = 2 ∧ _) ∨ (3 = 4 ∧ _)) ↔
        ∃ r, ([] : List (FGDependencyWorkRead Nat))[index]? = some r ∧ _
      simp
    · change ((4 = 2 ∧ _) ∨ (4 = 4 ∧ kind = .ac ∧ index = 0 ∧ cut = 21 ∧ st = 10)) ↔
        ∃ r, ([⟨5, .ac, 10⟩] :
          List (FGDependencyWorkRead Nat))[index]? = some r ∧
          r.kind = kind ∧ cut = 16 + r.offset ∧ st = r.consumed
      cases index <;> simp [eq_comm]
  hook_reads j e r h member := by
    have hj := dr4_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e
    · change r ∈ ([] : List (FGDependencyWorkRead Nat)) at member
      cases member
    · change r ∈ ([] : List (FGDependencyWorkRead Nat)) at member
      cases member
    · change r ∈ ([⟨4, .ac, 6⟩] : List (FGDependencyWorkRead Nat)) at member
      have hr := List.mem_singleton.mp member
      subst r
      exact ⟨by decide, rfl, dr4_entry_steps false, dr4_closed 6 (Or.inr (Or.inl rfl))⟩
    · change r ∈ ([] : List (FGDependencyWorkRead Nat)) at member
      cases member
    · change r ∈ ([⟨5, .ac, 10⟩] : List (FGDependencyWorkRead Nat)) at member
      have hr := List.mem_singleton.mp member
      subst r
      exact ⟨by decide, rfl, dr4_replay_steps, dr4_closed 10 (Or.inr (Or.inr (Or.inr rfl)))⟩
  receipt_entry j wire t b h awake valid decoded := by
    have hj := dr4_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    · obtain ⟨_, rfl, rfl⟩ := V2.Event.deliver.inj h
      have hb := Option.some.inj decoded
      subst b
      simp [Effect, dependencyResolved, dependencyRefused, dependencyReceiverEpoch,
        dr4_op, do_arrival]
    · cases h
    · obtain ⟨_, rfl, rfl⟩ := V2.Event.deliver.inj h
      have hb := Option.some.inj decoded
      subst b
      simp [Effect, dependencyResolved, dependencyRefused, dependencyReceiverEpoch,
        dr4_op, do_arrival]
    · cases h
    · cases h
  entry_boundary j e h := by
    have hj := dr4_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      exact ⟨rfl, by decide, by decide, rfl, rfl⟩
  drain_operations j e k h lo hi := by
    have hj := dr4_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      norm_num [dr4_trace] at lo hi <;> interval_cases k
    all_goals first
      | exact Or.inl ⟨_, _, _, rfl⟩
      | exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨_, rfl, rfl, rfl⟩))))))
      | refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr ⟨_, rfl, by decide, rfl, ?_⟩))))))
    all_goals intro q lo hi; norm_num at lo hi; interval_cases q <;> exact ⟨_, _, rfl⟩
  boundary_idle k hk outside := by
    change k < 21 at hk
    interval_cases k <;> simp only [dr4_op]
    all_goals exfalso; apply outside
    all_goals first
      | exact ⟨0, _, rfl, by decide, by decide⟩
      | exact ⟨1, _, rfl, by decide, by decide⟩
      | exact ⟨2, _, rfl, by decide, by decide⟩
      | exact ⟨3, _, rfl, by decide, by decide⟩
      | exact ⟨4, _, rfl, by decide, by decide⟩
  raw_restore j t h := by
    have hj := dr4_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> rfl
  raw_clock j t h := by
    have hj := dr4_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> rfl
  restore_data := dr4_step_laws.restore_exact
  reconstruct_program _ _ := rfl
  reconstruct_data st _ := by
    refine ⟨rfl, rfl, fun _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => Iff.rfl, ?_, ?_⟩
    · intro b o h
      rcases h with (⟨rfl, rfl, rfl, hz⟩ | ⟨rfl, rfl, rfl, hz⟩) <;> cases hz
    · intro b o h; exact h.elim
  restart_reconstruct j t h := by
    have hj := dr4_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> exact ⟨by decide, rfl⟩
  restart_drain_closed j t h := by
    have hj := dr4_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h
    · exact dr4_closed 1 (Or.inl rfl)
    · exact dr4_closed 7 (Or.inr (Or.inr (Or.inl rfl)))
  restart_replay_order j t k b o h lo hi op := by
    have hj := dr4_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> norm_num [dr4_trace] at lo hi ⊢
    all_goals interval_cases k <;> first | decide | cases op
  rebuild_program _ _ := rfl
  rebuild_data st t := by
    by_cases h : st = 8
    · subst st
      refine ⟨rfl, rfl, ?_, fun _ _ _ => Iff.rfl, ?_, ?_, ?_, ?_, fun _ _ h => h.elim⟩ <;>
        simp
    · rw [show dr4_driver.rebuild st t = st by
        change (if st = 8 then 9 else st) = st; simp [h]]
      refine ⟨rfl, rfl, fun _ => Iff.rfl, fun _ _ _ => Iff.rfl,
        fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => Iff.rfl, ?_, fun _ _ h => h.elim⟩
      intro b o h
      rcases h with (⟨rfl, rfl, rfl, hz⟩ | ⟨rfl, rfl, rfl, hz⟩) <;> cases hz
  restart_rebuild j t h := by
    have hj := dr4_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h
    · refine ⟨5, by decide, by decide, rfl, ?_, ?_, ?_, rfl⟩
      · intro q t lo hi op
        norm_num [dr4_trace] at lo hi
        interval_cases q <;> first | rfl | cases op
      · intro q lo hi
        norm_num [dr4_trace] at lo hi
        interval_cases q
      · intro q lo hi
        norm_num [dr4_trace] at lo hi
        interval_cases q
    · refine ⟨19, by decide, by decide, rfl, ?_, ?_, ?_, rfl⟩
      · intro q t lo hi op
        norm_num [dr4_trace] at lo hi
        interval_cases q <;> first | rfl | cases op
      · intro q lo hi
        norm_num [dr4_trace] at lo hi
        interval_cases q <;> simp [dr4_op]
      · intro q lo hi
        norm_num [dr4_trace] at lo hi
        interval_cases q; simp [dr4_op]
  clock_no_insert _ _ := ⟨rfl, rfl⟩
  refusal_creation _ _ _ refused _ := refused.elim
  refusal_history _ _ _ refused := refused.elim
  notification_creation k b hk notified fresh := by
    change k < 21 at hk
    have key := (dr4_trace_facts k (Nat.le_of_lt hk)).2.2.1 b notified fresh
    rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨do_parent, rfl, Or.inl (Or.inl ⟨rfl, rfl, rfl⟩), 8, by decide,
        Or.inl ⟨by decide, Or.inl ⟨rfl, rfl, rfl, rfl⟩, rfl⟩⟩
    · exact ⟨do_child, rfl, Or.inl (Or.inr ⟨rfl, rfl, rfl⟩), 9, by decide,
        Or.inl ⟨by decide, Or.inr ⟨rfl, rfl, rfl, rfl⟩, rfl⟩⟩
  actual_read i st := by
    constructor
    · rintro ⟨lo, hi, rfl⟩
      interval_cases i
      · exact ⟨3, .tick false 4, .fg, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
      · exact ⟨3, .tick false 4, .proposer, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
      · exact ⟨3, .tick false 4, .head, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
      · exact ⟨3, .tick false 4, .ac, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
    · rintro ⟨j, e, kind, he, required, rfl, rfl⟩
      have hj := dr4_events_bound he
      interval_cases j <;> simp only [List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.some.injEq] at he <;> subst e
      all_goals simp [dependencyReadRequired] at required
      all_goals cases kind <;> exact ⟨by decide, by decide, rfl⟩
  read_order j e kind h required := by
    have hj := dr4_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e
    all_goals simp [dependencyReadRequired] at required
    all_goals exact ⟨Nat.le_refl 14, Nat.le_refl 14, rfl, .refl _⟩
  wire_validation wire b valid decoded := by
    have hb : wire.payload = b := Option.some.inj decoded
    simpa [do_protocol, dr4_reads, hb] using valid
  origin_valid k b o hk origin := by
    change k ≤ 21 at hk
    rcases origin with ⟨rfl, h, rfl⟩ | ⟨rfl, h, rfl⟩
    · refine ⟨dr4_child_origin, ?_⟩
      exact (dr4_trace_facts k hk).1 h
    · refine ⟨dr4_parent_origin, ?_⟩
      exact (dr4_trace_facts k hk).2.1 h
  leaf_step k b o z hk leaf hz := by
    change k < 21 at hk
    rcases leaf with ⟨_, (⟨ha, rfl, rfl, rfl⟩ | ⟨ha, rfl, rfl, rfl⟩)⟩
    · refine ⟨dr4_parent_origin, ?_, ?_⟩
      · apply (dr4_trace_facts k (Nat.le_of_lt hk)).2.1
        rw [ha]
      · change 3 = do_leafProtocol.process (dr4_trace.state k) (do_wire 1)
        rw [ha]
        rfl
    · refine ⟨dr4_child_origin, ?_, ?_⟩
      · apply (dr4_trace_facts k (Nat.le_of_lt hk)).1
        rw [ha]
        decide
      · change 4 = do_leafProtocol.process (dr4_trace.state k) (do_wire 2)
        rw [ha]
        rfl
  origin_attribution k b hk held fresh := by
    have key := (dr4_trace_facts k (Nat.le_of_lt hk)).2.2.2 b held fresh
    rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨do_parent, ⟨rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩,
        Or.inr ⟨rfl, by decide, rfl⟩, rfl, rfl, rfl⟩
    · exact ⟨do_child, ⟨rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩,
        Or.inl ⟨rfl, by decide, rfl⟩, rfl, rfl, rfl⟩
  read_correspondence i st read := by
    rcases read with ⟨_, _, rfl⟩
    exact ⟨by change 14 ≤ 21; decide, rfl, dr4_closed 6 (Or.inr (Or.inl rfl))⟩
  order_and_time i j ei ej hi hj le := by
    have bi := dr4_events_bound hi
    have bj := dr4_events_bound hj
    interval_cases i <;> interval_cases j <;>
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.some.injEq] at hi hj <;> subst ei <;> subst ej <;>
      decide +kernel
  finite_segment j e h := by
    have hj := dr4_events_bound h
    interval_cases j <;> decide +kernel
  event_drain j y wire t h := by
    have hj := dr4_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq, V2.Event.deliver.injEq] at h
    · exact dr4_closed 1 (Or.inl rfl)
    · cases h
    · exact dr4_closed 6 (Or.inr (Or.inl rfl))
    · cases h
    · cases h
  entry_drain j e h := by
    have hj := dr4_events_bound h
    interval_cases j
    · exact dr4_closed 1 (Or.inl rfl)
    · exact dr4_closed 1 (Or.inl rfl)
    · exact dr4_closed 6 (Or.inr (Or.inl rfl))
    · exact dr4_closed 6 (Or.inr (Or.inl rfl))
    · exact dr4_closed 10 (Or.inr (Or.inr (Or.inr rfl)))
  segment_time j e k h lower upper := by
    have hj := dr4_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      norm_num [dr4_trace] at lower upper <;> interval_cases k <;> rfl
  event_order i j ei ej hi hj lt := by
    have bi := dr4_events_bound hi
    have bj := dr4_events_bound hj
    interval_cases i <;> interval_cases j <;> decide
  completion_cut j e deadline h strict := by
    have hj := dr4_events_bound h
    refine ⟨?_, ?_, ?_⟩
    · interval_cases j <;> decide +kernel
    · interval_cases j <;> simp only [List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> exact strict
    · intro i ei hi before
      have bi := dr4_events_bound hi
      interval_cases i <;> interval_cases j <;>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.some.injEq] at hi h <;> subst ei <;> subst e <;>
        norm_num [dr4_trace] at before <;>
        exact lt_of_le_of_lt (by decide) strict
  tick_records j t h := by
    have hj := dr4_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> rfl
  atomic_tick j t h := by
    have hj := dr4_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    · cases h
    · cases h
    · cases h
    · have ht : (4 : Time) = t := V2.Event.tick.inj h |>.2
      subst t
      exact ⟨by decide, by decide, rfl, dr4_closed 6 (Or.inr (Or.inl rfl)), .refl _⟩
    · cases h

/-- The retained parent carries nonempty content; replay fills a cleared open role. -/
private theorem dr4_restart_replay_completes :
    dependencyStateBefore do_env dr4_run dr4_driver false 4 = 6 ∧
    dependencyEventEntry dr4_run dr4_driver false 4 6 (.restart false 5) = 7 ∧
    (1 : Fin 4) ≠ do_leaf.genesis ∧ dr4_wireReads.bodyRows 1 = [1] ∧
    dr4_reads.latestKey 7 0 = none ∧
    dr4_reads.latestKey 8 0 = some (3, do_history.root 2) ∧
    FGDependencyEnabled do_history dr4_reads 8 ∧
    dependencyStateBefore do_env dr4_run dr4_driver false 5 = 10 ∧
    dr4_trace.time (dr4_trace.done 4) = 5 ∧
    dependencyClosed do_history dr4_reads (dr4_trace.state (dr4_trace.done 4)) ∧
    dependencyStrictPrefix dr4_run dr4_trace 6 (dr4_trace.done 4) := by
  refine ⟨rfl, rfl, by decide, rfl, rfl, rfl, ?_, rfl, rfl, ?_, ?_⟩
  · exact .companion 2 (Or.inr (Or.inr ⟨rfl, by decide⟩))
      ⟨by decide, rfl⟩ (by simp)
  · exact dr4_trace_laws.entry_drain 4 (.restart false 5) rfl
  · exact dr4_trace_laws.completion_cut 4 (.restart false 5) 6 rfl (by decide)

private theorem dr4_replay_reads_and_provenance :
    (dependencyEventReads dr4_run dr4_driver false 4 6 (.restart false 5)) =
      [⟨5, .ac, 10⟩] ∧
    dr4_trace.hookRead 4 0 .ac 21 10 ∧
    FGReceiptOrigin do_env dr4_run do_history dr4_wireReads false 1 do_parent ∧
    FGReceiptOrigin do_env dr4_run do_history dr4_wireReads false 2 do_child ∧
    ¬ do_leaf.callback 7 1 do_parent 8 ∧
    ¬ do_leaf.step 7 1 do_parent .duplicate 8 := by
  exact ⟨rfl, Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩,
    dr4_parent_origin, dr4_child_origin, by simp, by simp⟩

private noncomputable abbrev dr4_omittedTrace : FGDependencyTrace Nat :=
  { dr4_trace with done := fun j => if j = 4 then 17 else dr4_trace.done j }

private theorem dr4_omitted_replay_rejected :
    ¬ FGDependencyTraceLaws do_env dr4_run false do_history dr4_wireReads dr4_reads do_leaf
      dr4_step dr4_omittedTrace dr4_driver dr4_op do_arrival dr4_notify
      (Leaf := do_leafProtocol) id id do_read := by
  intro laws
  have bad : (10 : Nat) = 7 := (laws.work_execution 4 (.restart false 5) rfl).1
  omega

private noncomputable abbrev dr4_substitutedOp (k : Nat) :=
  if k = 17 then FGDependencyOperation.replay 2 do_child else dr4_op k

private theorem dr4_substituted_carrier_rejected :
    ¬ FGDependencyTraceLaws do_env dr4_run false do_history dr4_wireReads dr4_reads do_leaf
      dr4_step dr4_trace dr4_driver dr4_substitutedOp do_arrival dr4_notify
      (Leaf := do_leafProtocol) id id do_read := by
  intro laws
  have bad : (8 : Nat) = 7 := (laws.operation_bound 17 (by decide)).2.2.2.2.1
  omega

private noncomputable abbrev dr4_omittedReadTrace : FGDependencyTrace Nat :=
  { dr4_trace with hookRead := fun j index kind cut st =>
      dr4_trace.hookRead j index kind cut st ∧ ¬ (j = 4 ∧ index = 0) }

private theorem dr4_omitted_replay_read_rejected :
    ¬ FGDependencyTraceLaws do_env dr4_run false do_history dr4_wireReads dr4_reads do_leaf
      dr4_step dr4_omittedReadTrace dr4_driver dr4_op do_arrival dr4_notify
      (Leaf := do_leafProtocol) id id do_read := by
  intro laws
  have read := (laws.hook_correspondence 4 (.restart false 5) 0 .ac 21 10 rfl).mpr
    ⟨⟨5, .ac, 10⟩, rfl, rfl, rfl, rfl⟩
  exact read.2 ⟨rfl, rfl⟩

#print axioms dr4_state_laws
#print axioms dr4_step_laws
#print axioms dr4_hook_laws
#print axioms dr4_trace_laws
#print axioms dr4_restart_replay_completes
#print axioms dr4_replay_reads_and_provenance
#print axioms dr4_omitted_replay_rejected
#print axioms dr4_substituted_carrier_rejected
#print axioms dr4_omitted_replay_read_rejected

/-- Rebuild-owned observation of this interface model: the post-replay scan has run. -/
private def dr4_scanned (st : Nat) : Prop := 9 ≤ st

/-- The rebuild runs once at the restart time, after both replays and before the final drain. -/
private theorem dr4_rebuild_after_replay :
    (dependencyExecuteWork dr4_driver 7 (dr4_driver.work 7 (.restart false 5))).operations =
      [.reconstruct 5, .replay 1 do_parent, .replay 2 do_child, .rebuild 5,
        .notification 2 do_child] ∧
    dr4_trace.dutyCut 4 = 17 ∧ dr4_op 17 = .replay 1 do_parent ∧
    dr4_op 18 = .replay 2 do_child ∧ dr4_op 19 = .rebuild 5 ∧
    dr4_op 20 = .notification 2 do_child ∧ dr4_trace.done 4 = 21 ∧
    dr4_trace.time 19 = 5 ∧ ¬ dr4_scanned (dr4_trace.state 19) ∧
    dr4_scanned (dr4_trace.state 20) ∧
    dr4_trace.state 21 = dr4_driver.drain (dr4_trace.state 20) ∧
    do_history.acceptedBodies (dr4_trace.state 20) = do_history.acceptedBodies 8 ∧
    (∀ b, dr4_reads.accepted (dr4_trace.state 20) b ↔ dr4_reads.accepted 8 b) ∧
    (∀ b r pr, dr4_reads.refused (dr4_trace.state 20) b r pr ↔ dr4_reads.refused 8 b r pr) ∧
    (∀ b o, dr4_reads.pending (dr4_trace.state 20) b o ↔ dr4_reads.pending 8 b o) ∧
    (∀ b o, dr4_reads.originAvailable (dr4_trace.state 20) b o ↔
      dr4_reads.originAvailable 8 b o) ∧
    (∀ b, dr4_reads.notified (dr4_trace.state 20) b ↔ dr4_reads.notified 8 b) := by
  have data := dr4_trace_laws.rebuild_data 8 5
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by unfold dr4_scanned; decide,
    by unfold dr4_scanned; decide, rfl, data.2.1,
    data.2.2.1, data.2.2.2.1, data.2.2.2.2.1, data.2.2.2.2.2.1, data.2.2.2.2.2.2.1⟩

/-- An explicit driver that rebuilds before the replays. The scan misses them. -/
private noncomputable abbrev dr4_earlyDriver : FGDependencyDriver Bool (Fin 4) dr4_protocol :=
  { dr4_driver with work := fun st e => if st = 7 then
      [.step (.reconstruct 5), .step (.rebuild 5), .step (.replay 1 do_parent),
        .step (.replay 2 do_child), .step (.notification 2 do_child)]
      else dr4_driver.work st e }

private noncomputable abbrev dr4_earlyOp (k : Nat) :
    FGDependencyOperation (Fin 4) (FGReceiptToken Bool dr4_protocol.Object)
      dr4_protocol.Object :=
  match k with
  | 17 => .rebuild 5
  | 18 => .replay 1 do_parent
  | 19 => .replay 2 do_child
  | 20 => .notification 2 do_child
  | k => dr4_op k

private noncomputable abbrev dr4_earlyTrace : FGDependencyTrace Nat :=
  { dr4_trace with
    state := fun k => if 18 ≤ k then (if 19 ≤ k then 8 else 7) else dr4_trace.state k
    hookRead := fun j index kind cut st => do_trace.hookRead j index kind cut st }

private theorem dr4_rebuild_before_replay_rejected :
    (dependencyExecuteWork dr4_earlyDriver 7
      (dr4_earlyDriver.work 7 (.restart false 5))).operations =
      [.reconstruct 5, .rebuild 5, .replay 1 do_parent, .replay 2 do_child,
        .notification 2 do_child] ∧
    dependencyStateBefore do_env dr4_run dr4_earlyDriver false 5 = 8 ∧
    ¬ dr4_scanned (dependencyStateBefore do_env dr4_run dr4_earlyDriver false 5) ∧
    ¬ FGDependencyTraceLaws do_env dr4_run false do_history dr4_wireReads dr4_reads do_leaf
      dr4_step dr4_earlyTrace dr4_earlyDriver dr4_earlyOp do_arrival dr4_notify
      (Leaf := do_leafProtocol) id id do_read := by
  refine ⟨rfl, rfl, by unfold dr4_scanned; decide, ?_⟩
  intro laws
  obtain ⟨r, _, _, _, unique, _, suffix, _⟩ := laws.restart_rebuild 4 5 rfl
  have hr : 17 = r := unique 17 5 (by decide) (by decide) rfl
  subst r
  rcases suffix 18 (by decide) (by decide) with
    ⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | h <;> cases h

/-- An explicit driver that rebuilds twice after the replays. -/
private noncomputable abbrev dr4_twiceDriver : FGDependencyDriver Bool (Fin 4) dr4_protocol :=
  { dr4_driver with work := fun st e => if st = 7 then
      [.step (.reconstruct 5), .step (.replay 1 do_parent), .step (.replay 2 do_child),
        .step (.rebuild 5), .step (.rebuild 5), .step (.notification 2 do_child)]
      else dr4_driver.work st e }

private noncomputable abbrev dr4_twiceOp (k : Nat) :=
  if k = 20 then FGDependencyOperation.rebuild 5
  else if k = 21 then .notification 2 do_child else dr4_op k

private noncomputable abbrev dr4_twiceTrace : FGDependencyTrace Nat :=
  { dr4_trace with
    length := 22
    state := fun k => if k = 21 then 9 else dr4_trace.state k
    done := fun j => if j = 4 then 22 else dr4_trace.done j
    hookRead := fun j index kind cut st => do_trace.hookRead j index kind cut st ∨
      (j = 4 ∧ kind = .ac ∧ index = 0 ∧ cut = 22 ∧ st = 10) }

private theorem dr4_rebuild_twice_rejected :
    (dependencyExecuteWork dr4_twiceDriver 7
      (dr4_twiceDriver.work 7 (.restart false 5))).operations =
      [.reconstruct 5, .replay 1 do_parent, .replay 2 do_child, .rebuild 5, .rebuild 5,
        .notification 2 do_child] ∧
    dependencyStateBefore do_env dr4_run dr4_twiceDriver false 5 = 10 ∧
    ¬ FGDependencyTraceLaws do_env dr4_run false do_history dr4_wireReads dr4_reads do_leaf
      dr4_step dr4_twiceTrace dr4_twiceDriver dr4_twiceOp do_arrival dr4_notify
      (Leaf := do_leafProtocol) id id do_read := by
  refine ⟨rfl, rfl, ?_⟩
  intro laws
  obtain ⟨r, _, _, _, unique, _⟩ := laws.restart_rebuild 4 5 rfl
  have first : 19 = r := unique 19 5 (by decide) (by decide) rfl
  have second : 20 = r := unique 20 5 (by decide) (by decide) rfl
  omega

/-- An explicit rebuild hook that drops the accepted parent and its retained origin. -/
private noncomputable abbrev dr4_alterDriver : FGDependencyDriver Bool (Fin 4) dr4_protocol :=
  { dr4_driver with
    rebuild := fun st _ => if st = 8 then 1 else st
    hookProgram := fun st op => match op with
      | .rebuild _ => .finish (if st = 8 then 1 else st)
      | _ => dr4_driver.hookProgram st op }

private noncomputable abbrev dr4_alterTrace : FGDependencyTrace Nat :=
  { dr4_trace with state := fun k => if 20 ≤ k then 1 else dr4_trace.state k }

private theorem dr4_rebuild_alters_data_rejected :
    (dependencyExecuteWork dr4_alterDriver 7
      (dr4_alterDriver.work 7 (.restart false 5))).operations =
      [.reconstruct 5, .replay 1 do_parent, .replay 2 do_child, .rebuild 5,
        .notification 2 do_child] ∧
    dependencyStateBefore do_env dr4_run dr4_alterDriver false 5 = 1 ∧
    dr4_reads.accepted 8 1 ∧ ¬ dr4_reads.accepted (dr4_alterDriver.rebuild 8 5) 1 ∧
    dr4_reads.originAvailable 8 1 do_parent ∧
    ¬ dr4_reads.originAvailable (dr4_alterDriver.rebuild 8 5) 1 do_parent ∧
    ¬ FGDependencyTraceLaws do_env dr4_run false do_history dr4_wireReads dr4_reads do_leaf
      dr4_step dr4_alterTrace dr4_alterDriver dr4_op do_arrival dr4_notify
      (Leaf := do_leafProtocol) id id do_read := by
  refine ⟨rfl, rfl, by decide, by decide, Or.inr ⟨rfl, by decide, rfl⟩, ?_, ?_⟩
  · rintro (⟨bad, _⟩ | ⟨_, bad, _⟩) <;> simp at bad
  · intro laws
    have accepted := ((laws.rebuild_data 8 5).2.2.1 1).mpr (by decide)
    exact (by decide : ¬ dr4_reads.accepted 1 1) accepted

#print axioms dr4_rebuild_after_replay
#print axioms dr4_rebuild_before_replay_rejected
#print axioms dr4_rebuild_twice_rejected
#print axioms dr4_rebuild_alters_data_rejected

/-- Saved standalone knowledge and a labelled freeze in a finite interface model. -/
private structure sr_State where
  mLatest : Nat := 0
  mHeld : Nat := 0
  freezeLabel : Nat := 0
  freezeLatest : Nat := 0
  freezeHeld : Nat := 0
  sleepTime : Time := 2
  lastCompleted : Time := 1
  restartTime : Time := 0
  signed : Nat := 0
  bodyToken : Bool := false

private def sr_receive (st : sr_State) : sr_State := { st with mLatest := 7 }

private def sr_reconstruct (st : sr_State) (wake : Time) : sr_State :=
  if st.lastCompleted < 2 ∧ st.sleepTime ≤ 2 ∧ 2 ≤ wake then
    { st with
      freezeLabel := 2
      freezeLatest := st.mLatest
      freezeHeld := st.mHeld
      lastCompleted := 2
      restartTime := wake }
  else { st with restartTime := wake }

private noncomputable abbrev sr_protocol : V2.ProtocolSpecD Unit where
  State := sr_State
  Label := Unit
  Duty := Empty
  signLabel := Empty.elim
  seats := fun _ => 1
  Payload := Unit
  Durable := sr_State
  init := {}
  clock := fun st _ => st
  actTime := Empty.elim
  duties := fun _ => []
  duties_spec := by intro d; cases d
  duties_nodup := by intro _; exact List.nodup_nil
  act := fun _ d _ => Empty.elim d
  gossip := fun _ _ => []
  process := fun st _ => sr_receive st
  selfVisible := fun _ => false
  recordOwn := fun st _ => st
  durable := id
  restore := fun st _ => st
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

private noncomputable abbrev sr_wire : sr_protocol.Object := ⟨.none, ()⟩

private noncomputable abbrev sr_run : V2.D.Run Bool sr_protocol where
  honest := {false}
  horizon := 3
  events := [.deliver false sr_wire 0, .restart false 2]
  seatOf := fun _ _ => false
  input := fun _ _ => ()

private noncomputable abbrev sr_history : FGHistoricalReads sr_State Unit where
  acceptedBlocks := fun _ => {Block.genesis}
  acceptedBodies := fun _ => [()]
  erase := fun _ => .genesis
  root := fun _ => Block.genesis.root
  parent := id
  slot := fun _ => 0
  readBlock := fun _ _ => none
  preceq := fun _ _ => True
  depth := fun _ => 0
  lca := fun _ _ => .genesis

private noncomputable abbrev sr_wireReads : FGDependencyWireReads sr_protocol Unit Unit where
  decodeBody := fun _ => none
  namedRoots := fun _ => none
  proposalErase := fun _ => none
  decodedRows := fun _ => []
  bodyRows := fun _ => []

private noncomputable abbrev sr_reads : FGDependencyReads sr_State Unit
    (FGReceiptToken Bool sr_protocol.Object) Unit where
  accepted := fun _ _ => True
  refused := fun _ _ _ _ => False
  pending := fun _ _ _ => False
  originAvailable := fun _ _ _ => False
  validBody := fun _ => True
  priorChecks := fun _ _ => True
  timely := fun _ _ => True
  conflictsFinal := fun _ _ => False
  latest := fun _ => ()
  notified := fun _ _ => True
  matching := fun _ _ => False
  companionHeld := fun _ _ => True
  latestKey := fun _ _ => none
  latestCompanion := fun _ _ => none

private noncomputable abbrev sr_leaf : FGDependencyLeaf sr_State Unit
    (FGReceiptToken Bool sr_protocol.Object) where
  step := fun _ _ _ _ _ => False
  callback := fun _ _ _ _ => False
  report := fun _ _ _ _ => False
  initial := {}
  genesis := ()

private def sr_step (kind : FGDependencyStepKind) (_ : Bool) (a z : sr_State) : Prop :=
  (z = a ∧ (kind = .ordinary ∨ kind = .restore)) ∨
  (kind = .ordinary ∧ z = sr_receive a) ∨
  (kind = .ordinary ∧ z = sr_reconstruct a 2)

private noncomputable abbrev sr_driver : FGDependencyDriver Bool Unit sr_protocol where
  enter := fun st _ _ => sr_receive st
  enterProgram := fun st _ _ => .finish (sr_receive st)
  hookProgram st op := match op with
    | .reconstruct t => .finish (sr_reconstruct st t)
    | _ => .finish st
  drain := id
  reconstruct := sr_reconstruct
  rebuild := fun st _ => st
  retry := fun st _ _ _ => st
  work _ e := match e with
    | .restart _ t => [.step (.reconstruct t), .step .idle, .step (.rebuild t)]
    | _ => []
  inheritRefusal := fun st _ _ => st
  notify := fun st _ _ => st
  replay := fun st _ _ => st

private noncomputable abbrev sr_saved : sr_State := sr_receive {}
private noncomputable abbrev sr_rebuilt : sr_State := sr_reconstruct sr_saved 2

private noncomputable abbrev sr_trace : FGDependencyTrace sr_State where
  length := 6
  state k := [{}, sr_saved, sr_saved, sr_saved, sr_rebuilt, sr_rebuilt][k]?.getD sr_rebuilt
  time k := [0, 0, 2, 2, 2, 2][k]?.getD 2
  start j := [0, 2][j]?.getD 6
  entryCut j := [1, 3][j]?.getD 6
  dutyCut j := [1, 5][j]?.getD 6
  done j := [1, 6][j]?.getD 6
  readCut := fun _ => 6
  hookRead := fun _ _ _ _ _ => False

private noncomputable abbrev sr_op (k : Nat) :
    FGDependencyOperation Unit (FGReceiptToken Bool sr_protocol.Object) sr_protocol.Object :=
  match k with
  | 0 => .ordinary sr_wire
  | 2 => .restore 2
  | 3 => .reconstruct 2
  | 5 => .rebuild 2
  | _ => .idle

private theorem sr_closed (st : sr_State) : dependencyClosed sr_history sr_reads st := by
  intro work
  cases work <;> simp_all

private theorem sr_step_laws :
    FGDependencyStepLaws sr_history sr_reads sr_leaf sr_step (fun st _ => st)
      (fun a z => a.signed < z.signed) where
  accepted_keep := by intros; trivial
  refused_keep := by intros; contradiction
  pending_effect := by intros; contradiction
  origin_keep := by intros; contradiction
  metadata_fg_eq := by intros; rfl
  insertion_leaf := by intros; contradiction
  one_body := by intros; contradiction
  restore_exact := by intros; exact ⟨rfl, rfl, fun _ _ _ => Iff.rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  no_signing := by
    intro k x a z step
    rcases step with ⟨rfl, _⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Nat.lt_irrefl _
    · exact Nat.lt_irrefl _
    · simp only [sr_reconstruct]; split <;> exact Nat.lt_irrefl _

private theorem sr_arrival_laws :
    FGDependencyArrivalLeafLaws sr_history sr_reads sr_leaf
      (fun _ _ _ _ => False) (fun _ _ _ => False) := by
  constructor <;> simp

private theorem sr_events_bound {j : Nat} {e : V2.Event Bool sr_protocol.Object}
    (h : sr_run.events[j]? = some e) : j < 2 :=
  (List.getElem?_eq_some_iff.mp h).1

private theorem sr_trace_laws :
    FGDependencyTraceLaws do_env sr_run false sr_history sr_wireReads sr_reads sr_leaf
      sr_step sr_trace sr_driver sr_op (fun _ _ _ _ => False) (fun _ _ _ => False)
      (Leaf := sr_protocol) id id (fun _ _ _ => False) where
  arrival_laws := sr_arrival_laws
  initial := rfl
  initial_accepted := by intros; rfl
  micro_step k hk := by
    change k < 6 at hk
    interval_cases k <;> first
      | exact ⟨.ordinary, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      | exact ⟨.ordinary, Or.inl ⟨rfl, Or.inl rfl⟩⟩
      | exact ⟨.ordinary, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  external_step j e h := by
    have hj := sr_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> exact ⟨rfl, rfl⟩
  step_kind k hk := by
    change k < 6 at hk
    interval_cases k <;> first
      | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | exact Or.inl ⟨rfl, Or.inl rfl⟩
      | exact Or.inl ⟨rfl, Or.inr rfl⟩
      | exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  operation_bound k hk := by
    change k < 6 at hk
    interval_cases k <;> first
      | exact ⟨rfl, rfl, rfl⟩
      | exact ⟨rfl, 1, rfl, rfl⟩
      | exact ⟨rfl, 1, rfl, by decide, by decide, fun q lo hi => by
          norm_num at lo hi; interval_cases q⟩
      | rfl
  delivery_entry j wire t h := by
    have hj := sr_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> rfl
  work_execution j e h := by
    have hj := sr_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> exact ⟨rfl, rfl⟩
  work_step j e k h lo hi := by
    have hj := sr_events_bound h
    interval_cases j <;> norm_num [sr_trace] at lo hi <;> first | omega | (interval_cases k <;> rfl)
  hook_correspondence j e index kind cut st h := by
    have hj := sr_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e
    all_goals change False ↔ ∃ r,
      ([] : List (FGDependencyWorkRead sr_State))[index]? = some r ∧ _
    all_goals simp
  hook_reads j e r h member := by
    have hj := sr_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e
    all_goals change r ∈ ([] : List (FGDependencyWorkRead sr_State)) at member
    all_goals cases member
  receipt_entry := by intros; contradiction
  entry_boundary j e h := by
    have hj := sr_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      exact ⟨rfl, by decide, by decide, rfl, rfl⟩
  drain_operations j e k h lo hi := by
    have hj := sr_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      norm_num [sr_trace] at lo hi <;> first | omega | (interval_cases k <;> simp [sr_op])
    all_goals intro q lo hi; interval_cases q
  boundary_idle k hk outside := by
    change k < 6 at hk
    interval_cases k <;> simp only [sr_op]
    all_goals exfalso; apply outside
    all_goals first
      | exact ⟨0, _, rfl, by decide, by decide⟩
      | exact ⟨1, _, rfl, by decide, by decide⟩
  raw_restore j t h := by
    have hj := sr_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> rfl
  raw_clock j t h := by
    have hj := sr_events_bound h
    interval_cases j <;> simp at h
  restore_data := by intros; exact ⟨rfl, rfl, fun _ _ _ => Iff.rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  reconstruct_program := by intros; rfl
  reconstruct_data := by intros; simp
  restart_reconstruct j t h := by
    have hj := sr_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> exact ⟨by decide, rfl⟩
  restart_drain_closed := by intros; exact sr_closed _
  restart_replay_order j t k b o h lo hi op := by
    have hj := sr_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> norm_num [sr_trace] at lo hi ⊢
    all_goals interval_cases k <;> cases op
  rebuild_program := by intros; rfl
  rebuild_data := by intros; simp
  restart_rebuild j t h := by
    have hj := sr_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h
    refine ⟨5, by decide, by decide, rfl, ?_, ?_, ?_, rfl⟩
    · intro q t lo hi op
      norm_num [sr_trace] at lo hi
      interval_cases q <;> simp_all [sr_op]
    · intro q lo hi
      norm_num [sr_trace] at lo hi
      interval_cases q
    · intro q lo hi
      norm_num [sr_trace] at lo hi
      interval_cases q
  clock_no_insert := by intros; exact ⟨rfl, rfl⟩
  wire_validation := by intros; trivial
  origin_valid := by intros; contradiction
  leaf_step := by intros; contradiction
  refusal_creation := by intros; contradiction
  refusal_history := by intros; contradiction
  notification_creation := by intros; contradiction
  origin_attribution := by intros; contradiction
  actual_read i st := by
    constructor
    · intro h; cases h
    · rintro ⟨j, e, kind, h, required, _⟩
      have hj := sr_events_bound h
      interval_cases j <;> simp only [List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> cases required
  read_order j e kind h required := by
    have hj := sr_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> cases required
  read_correspondence := by intros; contradiction
  order_and_time i j ei ej hi hj order := by
    have bi := sr_events_bound hi
    have bj := sr_events_bound hj
    interval_cases i <;> interval_cases j <;>
      simp_all only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    all_goals subst ei; subst ej; norm_num [V2.Event.time] at order ⊢
  finite_segment j e h := by
    have hj := sr_events_bound h
    interval_cases j <;> exact ⟨by decide, by decide⟩
  event_drain := by intros; exact sr_closed _
  entry_drain := by intros; exact sr_closed _
  segment_time j e k h lo hi := by
    have hj := sr_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      norm_num [sr_trace] at lo hi <;> first | omega | (interval_cases k <;> rfl)
  event_order i j ei ej hi hj order := by
    have bi := sr_events_bound hi
    have bj := sr_events_bound hj
    interval_cases i <;> interval_cases j; norm_num at order ⊢
  completion_cut j e deadline h before := by
    have hj := sr_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e
    all_goals refine ⟨by decide, before, ?_⟩
    all_goals intro i ei event starts
    all_goals have bi := sr_events_bound event
    all_goals interval_cases i <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at event <;> subst ei
    all_goals solve
      | exact before
      | norm_num [sr_trace] at starts
      | exact lt_trans (by decide : (0 : Time) < 2) before
  tick_records j t h := by
    have hj := sr_events_bound h
    interval_cases j <;> simp at h
  atomic_tick j t h := by
    have hj := sr_events_bound h
    interval_cases j <;> simp at h

/-- A standalone receipt supplies M; the equal-time missed freeze is reconstructed after raw. -/
private theorem sr_positive :
    FGDependencyTraceLaws do_env sr_run false sr_history sr_wireReads sr_reads sr_leaf
      sr_step sr_trace sr_driver sr_op (fun _ _ _ _ => False) (fun _ _ _ => False)
      (Leaf := sr_protocol) id id (fun _ _ _ => False) ∧
    FGDependencyStepLaws sr_history sr_reads sr_leaf sr_step (fun st _ => st)
      (fun a z => a.signed < z.signed) ∧
    sr_run.events[0]? = some (.deliver false sr_wire 0) ∧
    (∀ wire, sr_wireReads.decodeBody wire = none) ∧
    sr_trace.start 1 < sr_trace.entryCut 1 ∧
    sr_trace.entryCut 1 < 4 ∧ 4 < sr_trace.dutyCut 1 ∧
    sr_op 3 = .reconstruct 2 ∧
    (sr_trace.state 3).mLatest = 7 ∧ (sr_trace.state 3).mHeld = 0 ∧
    (sr_trace.state 3).lastCompleted = 1 ∧
    (sr_trace.state 3).freezeLabel = 0 ∧ (sr_trace.state 4).freezeLabel = 2 ∧
    (sr_trace.state 4).freezeLatest = 7 ∧ (sr_trace.state 4).freezeHeld = 0 ∧
    (sr_trace.state 4).lastCompleted = 2 ∧ (sr_trace.state 4).restartTime = 2 ∧
    sr_protocol.restore (sr_protocol.durable sr_saved) 2 = sr_saved ∧
    dependencyStateBefore do_env sr_run sr_driver false 2 = sr_rebuilt ∧
    sr_history.acceptedBlocks sr_rebuilt = sr_history.acceptedBlocks sr_saved ∧
    sr_history.acceptedBodies sr_rebuilt = sr_history.acceptedBodies sr_saved ∧
    (∀ b r pr, sr_reads.refused sr_rebuilt b r pr ↔ sr_reads.refused sr_saved b r pr) ∧
    (∀ b o, sr_reads.pending sr_rebuilt b o ↔ sr_reads.pending sr_saved b o) ∧
    (∀ b o, sr_reads.originAvailable sr_rebuilt b o ↔
      sr_reads.originAvailable sr_saved b o) ∧
    sr_step .ordinary false (sr_trace.state 3) (sr_trace.state 4) ∧
    ¬ (sr_trace.state 3).signed < (sr_trace.state 4).signed := by
  refine ⟨sr_trace_laws, sr_step_laws, rfl, fun _ => rfl,
    by decide, by decide, by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl,
    fun _ _ => Iff.rfl, ?_, ?_⟩
  · exact (dependency_reconstruct_metadata sr_trace_laws sr_step_laws
      (k := 3) (t := 2) (by decide) rfl).1
  · exact (dependency_reconstruct_metadata sr_trace_laws sr_step_laws
      (k := 3) (t := 2) (by decide) rfl).2.2

private noncomputable abbrev sr_wakeToken : FGReceiptToken Bool sr_protocol.Object :=
  ⟨false, 1, sr_wire, 2, 2⟩

private def sr_badHook (st : sr_State) (t : Time) : sr_State :=
  { sr_reconstruct st t with bodyToken := true }

private noncomputable abbrev sr_badDriver : FGDependencyDriver Bool Unit sr_protocol :=
  { sr_driver with
    reconstruct := sr_badHook
    hookProgram := fun st op => match op with
      | .reconstruct t => .finish (sr_badHook st t)
      | _ => .finish st }

private noncomputable abbrev sr_badReads : FGDependencyReads sr_State Unit
    (FGReceiptToken Bool sr_protocol.Object) Unit :=
  { sr_reads with originAvailable := fun st _ o => st.bodyToken = true ∧ o = sr_wakeToken }

private noncomputable abbrev sr_badTrace : FGDependencyTrace sr_State :=
  { sr_trace with state := fun k => if 4 ≤ k then sr_badHook sr_saved 2 else sr_trace.state k }

private noncomputable abbrev sr_replayOp (k : Nat) :=
  if k = 3 then .replay () sr_wakeToken else sr_op k

/-- The explicit bad hook invents a wake token from a standalone wire. Replay also fails. -/
private theorem sr_negative :
    dependencyStateBefore do_env sr_run sr_badDriver false 2 = sr_badHook sr_saved 2 ∧
    sr_badReads.originAvailable (sr_badTrace.state 4) () sr_wakeToken ∧
    ¬ sr_badReads.originAvailable sr_saved () sr_wakeToken ∧
    ¬ (∀ st t b o, sr_badReads.originAvailable (sr_badDriver.reconstruct st t) b o ↔
      sr_badReads.originAvailable st b o) ∧
    ¬ FGDependencyTraceLaws do_env sr_run false sr_history sr_wireReads sr_badReads sr_leaf
      sr_step sr_badTrace sr_badDriver sr_op (fun _ _ _ _ => False) (fun _ _ _ => False)
      (Leaf := sr_protocol) id id (fun _ _ _ => False) ∧
    ¬ FGDependencyTraceLaws do_env sr_run false sr_history sr_wireReads sr_reads sr_leaf
      sr_step sr_trace sr_driver sr_replayOp (fun _ _ _ _ => False) (fun _ _ _ => False)
      (Leaf := sr_protocol) id id (fun _ _ _ => False) := by
  refine ⟨rfl, ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rintro ⟨bad, _⟩; cases bad
  · intro law
    have bad := (law sr_saved 2 () sr_wakeToken).mp ⟨rfl, rfl⟩
    cases bad.1
  · intro laws
    have data := (laws.reconstruct_data sr_saved 2).2.2.2.2.2.1 () sr_wakeToken
    have bad := data.mp ⟨rfl, rfl⟩
    cases bad.1
  · intro laws
    have bad : sr_reads.originAvailable (sr_trace.state 3) () sr_wakeToken :=
      (laws.operation_bound 3 (by decide)).2.2.1
    exact bad.elim

private theorem sr_bad_origin_invalid :
    ¬ FGDependencyTraceLaws do_env sr_run false sr_history sr_wireReads sr_badReads sr_leaf
      sr_step sr_badTrace sr_badDriver sr_op (fun _ _ _ _ => False) (fun _ _ _ => False)
      (Leaf := sr_protocol) id id (fun _ _ _ => False) := by
  intro laws
  have bad := (laws.origin_valid 4 () sr_wakeToken (by decide) ⟨rfl, rfl⟩).1.decoded
  cases bad

#print axioms sr_step_laws
#print axioms sr_arrival_laws
#print axioms sr_trace_laws
#print axioms sr_bad_origin_invalid
#print axioms sr_positive
#print axioms sr_negative


/-- Sleep and wake both equal the cut. Only an unfinished cut is reconstructed. -/
private theorem sr_equal_cut_last_completed :
    sr_saved.sleepTime = 2 ∧ sr_saved.lastCompleted = 1 ∧
    (sr_reconstruct sr_saved 2).freezeLabel = 2 ∧
    (sr_reconstruct { sr_saved with lastCompleted := 2 } 2).freezeLabel = 0 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms sr_equal_cut_last_completed

/-- A restart with an empty replay list still runs exactly one rebuild, at the duty cut. -/
private theorem sr_empty_replay_rebuild :
    (dependencyExecuteWork sr_driver sr_saved
      (sr_driver.work sr_saved (.restart false 2))).operations =
      [.reconstruct 2, .idle, .rebuild 2] ∧
    sr_trace.dutyCut 1 = 5 ∧ sr_op 5 = .rebuild 2 ∧ sr_trace.done 1 = 6 ∧
    sr_trace.time 5 = 2 ∧
    (∀ q b o, q < sr_trace.done 1 → sr_op q ≠ .replay b o) ∧
    ∃ r, sr_trace.dutyCut 1 ≤ r ∧ r < sr_trace.done 1 ∧ sr_op r = .rebuild 2 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro q b o hq
    change q < 6 at hq
    interval_cases q <;> simp [sr_op]
  · obtain ⟨r, lo, hi, op, _⟩ := sr_trace_laws.restart_rebuild 1 2 rfl
    exact ⟨r, lo, hi, op⟩

/-- An explicit driver whose delivery work runs the rebuild of a later restart. -/
private noncomputable abbrev sr_outsideDriver : FGDependencyDriver Bool Unit sr_protocol :=
  { sr_driver with work := fun _ e => match e with
      | .restart _ t => [.step (.reconstruct t), .step .idle, .step (.rebuild t)]
      | .deliver _ _ _ => [.step (.rebuild 2)]
      | _ => [] }

private noncomputable abbrev sr_outsideTrace : FGDependencyTrace sr_State where
  length := 7
  state k := [{}, sr_saved, sr_saved, sr_saved, sr_saved, sr_rebuilt, sr_rebuilt][k]?.getD
    sr_rebuilt
  time k := [0, 0, 0, 2, 2, 2, 2][k]?.getD 2
  start j := [0, 3][j]?.getD 7
  entryCut j := [1, 4][j]?.getD 7
  dutyCut j := [1, 6][j]?.getD 7
  done j := [2, 7][j]?.getD 7
  readCut := fun _ => 7
  hookRead := fun _ _ _ _ _ => False

private noncomputable abbrev sr_outsideOp (k : Nat) :
    FGDependencyOperation Unit (FGReceiptToken Bool sr_protocol.Object) sr_protocol.Object :=
  match k with
  | 0 => .ordinary sr_wire
  | 1 => .rebuild 2
  | 3 => .restore 2
  | 4 => .reconstruct 2
  | 6 => .rebuild 2
  | _ => .idle

private theorem sr_rebuild_outside_restart_rejected :
    (dependencyExecuteWork sr_outsideDriver sr_saved
      (sr_outsideDriver.work sr_saved (.deliver false sr_wire 0))).operations = [.rebuild 2] ∧
    dependencyStateBefore do_env sr_run sr_outsideDriver false 2 = sr_rebuilt ∧
    ¬ FGDependencyTraceLaws do_env sr_run false sr_history sr_wireReads sr_reads sr_leaf
      sr_step sr_outsideTrace sr_outsideDriver sr_outsideOp (fun _ _ _ _ => False)
      (fun _ _ _ => False) (Leaf := sr_protocol) id id (fun _ _ _ => False) := by
  refine ⟨rfl, rfl, ?_⟩
  intro laws
  rcases laws.drain_operations 0 (.deliver false sr_wire 0) 1 rfl (by decide) (by decide) with
    ⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h, _⟩ | h | ⟨_, h, _⟩ |
      ⟨_, h, _⟩ <;> cases h

#print axioms sr_empty_replay_rebuild
#print axioms sr_rebuild_outside_restart_rejected

/-- An inhabited standalone history has distinct raw, reconstruction and drain cuts. -/
theorem dependency_standalone_reconstruct_nontrivial :
    ∃ (P : V2.ProtocolSpecD Unit) (E : Generic.Env Bool) (wire : P.Object)
      (rho : V2.D.Run Bool P) (H : FGHistoricalReads P.State Unit)
      (W : FGDependencyWireReads P Unit Unit)
      (D : FGDependencyReads P.State Unit (FGReceiptToken Bool P.Object) Unit)
      (L : FGDependencyLeaf P.State Unit (FGReceiptToken Bool P.Object))
      (Step : FGDependencyStepKind → Bool → P.State → P.State → Prop)
      (T : FGDependencyTrace P.State) (F : FGDependencyDriver Bool Unit P)
      (Op : Nat → FGDependencyOperation Unit (FGReceiptToken Bool P.Object) P.Object)
      (m label frozen : P.State → Nat) (sleepTime lastCompleted : P.State → Time)
      (signs : P.State → P.State → Prop),
    FGDependencyTraceLaws E rho false H W D L Step T F Op
      (fun _ _ _ _ => False) (fun _ _ _ => False)
      (Leaf := P) id id (fun _ _ _ => False) ∧
    FGDependencyStepLaws H D L Step (fun st t => P.restore (P.durable st) t) signs ∧
    rho.events = [.deliver false wire 0, .restart false 2] ∧
    (∀ w, W.decodeBody w = none) ∧
    T.start 1 < T.entryCut 1 ∧ T.entryCut 1 < 4 ∧ 4 < T.dutyCut 1 ∧
    Op (T.entryCut 1) = .reconstruct 2 ∧
    m (T.state (T.start 1)) = 7 ∧ m (T.state (T.entryCut 1)) = 7 ∧
    sleepTime (T.state (T.entryCut 1)) = 2 ∧
    lastCompleted (T.state (T.entryCut 1)) = 1 ∧
    label (T.state (T.entryCut 1)) = 0 ∧ label (T.state 4) = 2 ∧
    frozen (T.state 4) = 7 ∧
    lastCompleted (T.state 4) = 2 ∧
    dependencyStateBefore E rho F false 2 = T.state (T.done 1) ∧
    H.acceptedBlocks (T.state 4) = H.acceptedBlocks (T.state (T.entryCut 1)) ∧
    H.acceptedBodies (T.state 4) = H.acceptedBodies (T.state (T.entryCut 1)) ∧
    (∀ b r pr, D.refused (T.state 4) b r pr ↔ D.refused (T.state (T.entryCut 1)) b r pr) ∧
    (∀ b o, D.pending (T.state 4) b o ↔ D.pending (T.state (T.entryCut 1)) b o) ∧
    (∀ b o, D.originAvailable (T.state 4) b o ↔
      D.originAvailable (T.state (T.entryCut 1)) b o) ∧
    ¬ signs (T.state (T.entryCut 1)) (T.state 4) := by
  refine ⟨sr_protocol, do_env, sr_wire, sr_run, sr_history, sr_wireReads, sr_reads, sr_leaf,
    sr_step, sr_trace, sr_driver, sr_op, sr_State.mLatest, sr_State.freezeLabel,
    sr_State.freezeLatest, sr_State.sleepTime, sr_State.lastCompleted,
    fun a z => a.signed < z.signed,
    sr_positive.1, sr_positive.2.1, rfl, fun _ => rfl, by decide, by decide, by decide,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, ?_⟩
  exact (dependency_reconstruct_metadata sr_trace_laws sr_step_laws
    (k := 3) (t := 2) (by decide) rfl).2.2

/-- A decoded child receipt is retained before restart; the bad hook replaces its token. -/
private noncomputable abbrev rr_run : V2.D.Run Bool do_protocol :=
  { do_run with events := [.deliver false (do_wire 2) 0, .restart false 1] }

private noncomputable abbrev rr_wake : FGReceiptToken Bool do_protocol.Object :=
  ⟨false, 1, do_wire 2, 1, 2⟩

private noncomputable abbrev rr_reads : FGDependencyReads Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) Nat :=
  { do_reads with originAvailable := fun st b o =>
    if st = 7 then b = 2 ∧ o = rr_wake else do_reads.originAvailable st b o }

private noncomputable abbrev rr_driver : FGDependencyDriver Bool (Fin 4) do_protocol :=
  { do_driver with
    reconstruct := fun _ _ => 7
    hookProgram := fun st op => match op with
      | .reconstruct _ => .finish 7
      | _ => do_driver.hookProgram st op }

private theorem rr_original_origin :
    FGReceiptOrigin do_env rr_run do_history do_wireReads false 2 do_child := by
  constructor <;> rfl

private theorem rr_replacement_rejected :
    (∀ b o, ¬ rr_reads.originAvailable do_protocol.init b o) ∧
    dependencyStateBefore do_env rr_run rr_driver false 1 = 1 ∧
    do_protocol.restore (do_protocol.durable 1) 1 = 1 ∧
    rr_reads.originAvailable 1 2 do_child ∧
    ¬ rr_reads.originAvailable 1 2 rr_wake ∧
    dependencyStateBefore do_env rr_run rr_driver false 2 = rr_driver.reconstruct 1 1 ∧
    rr_reads.originAvailable (rr_driver.reconstruct 1 1) 2 rr_wake ∧
    ¬ rr_reads.originAvailable (rr_driver.reconstruct 1 1) 2 do_child ∧
    ¬ (∀ st t b o, rr_reads.originAvailable (rr_driver.reconstruct st t) b o ↔
      rr_reads.originAvailable st b o) ∧
    ¬ FGReceiptOrigin do_env rr_run do_history do_wireReads false 2 rr_wake := by
  refine ⟨?_, rfl, rfl, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · intro b o; simp
  · exact Or.inl ⟨rfl, by decide, rfl⟩
  · simp [rr_wake, do_child]
  · exact ⟨rfl, rfl⟩
  · intro h
    have bad := congrArg FGReceiptToken.eventIndex h.2
    cases bad
  · intro law
    have bad := (law 1 1 2 do_child).mpr (Or.inl ⟨rfl, by decide, rfl⟩)
    have index := congrArg FGReceiptToken.eventIndex bad.2
    cases index
  · intro origin
    cases origin.delivered

#print axioms rr_original_origin
#print axioms rr_replacement_rejected

/-- Concrete wake-token insertion, retained-token replacement and replay tags fail the laws. -/
theorem dependency_reconstruct_wrong_origin_rejected :
    (∃ (P : V2.ProtocolSpecD Unit) (E : Generic.Env Bool) (wire : P.Object)
      (rho : V2.D.Run Bool P) (H : FGHistoricalReads P.State Unit)
      (W : FGDependencyWireReads P Unit Unit)
      (D badD : FGDependencyReads P.State Unit (FGReceiptToken Bool P.Object) Unit)
      (L : FGDependencyLeaf P.State Unit (FGReceiptToken Bool P.Object))
      (Step : FGDependencyStepKind → Bool → P.State → P.State → Prop)
      (T badT : FGDependencyTrace P.State) (F badF : FGDependencyDriver Bool Unit P)
      (Op replayOp : Nat → FGDependencyOperation Unit (FGReceiptToken Bool P.Object) P.Object)
      (o : FGReceiptToken Bool P.Object),
    rho.events = [.deliver false wire 0, .restart false 2] ∧
    (∀ w, W.decodeBody w = none) ∧
    o.eventIndex = 1 ∧ o.receiptTime = 2 ∧ o.receiptEpoch = 2 ∧
    dependencyStateBefore E rho badF false 2 = badT.state (badT.done 1) ∧
    badD.originAvailable (badT.state 4) () o ∧
    ¬ badD.originAvailable (badT.state 3) () o ∧
    ¬ (∀ st t b token, badD.originAvailable (badF.reconstruct st t) b token ↔
      badD.originAvailable st b token) ∧
    ¬ FGDependencyTraceLaws E rho false H W badD L Step badT badF Op
      (fun _ _ _ _ => False) (fun _ _ _ => False)
      (Leaf := P) id id (fun _ _ _ => False) ∧
    replayOp 3 = .replay () o ∧
    ¬ FGDependencyTraceLaws E rho false H W D L Step T F replayOp
      (fun _ _ _ _ => False) (fun _ _ _ => False)
      (Leaf := P) id id (fun _ _ _ => False)) ∧
    ∃ (P : V2.ProtocolSpecD Unit) (E : Generic.Env Bool) (wire : P.Object)
      (rho : V2.D.Run Bool P) (H : FGHistoricalReads P.State (Fin 4))
      (W : FGDependencyWireReads P (Fin 4) Nat)
      (D : FGDependencyReads P.State (Fin 4) (FGReceiptToken Bool P.Object) Nat)
      (F : FGDependencyDriver Bool (Fin 4) P) (raw : P.State)
      (original wake : FGReceiptToken Bool P.Object),
    rho.events = [.deliver false wire 0, .restart false 1] ∧
    W.decodeBody wire = some 2 ∧
    FGReceiptOrigin E rho H W false 2 original ∧
    original.eventIndex = 0 ∧ original.receiptTime = 0 ∧ original.receiptEpoch = 0 ∧
    wake.eventIndex = 1 ∧ wake.receiptTime = 1 ∧ wake.receiptEpoch = 2 ∧
    wake.wire = original.wire ∧
    (∀ b o, ¬ D.originAvailable P.init b o) ∧
    dependencyStateBefore E rho F false 1 = raw ∧
    P.restore (P.durable raw) 1 = raw ∧
    D.originAvailable raw 2 original ∧ ¬ D.originAvailable raw 2 wake ∧
    dependencyStateBefore E rho F false 2 = F.reconstruct raw 1 ∧
    D.originAvailable (F.reconstruct raw 1) 2 wake ∧
    ¬ D.originAvailable (F.reconstruct raw 1) 2 original ∧
    ¬ (∀ st t b o, D.originAvailable (F.reconstruct st t) b o ↔ D.originAvailable st b o) ∧
    ¬ FGReceiptOrigin E rho H W false 2 wake := by
  constructor
  · refine ⟨sr_protocol, do_env, sr_wire, sr_run, sr_history, sr_wireReads,
      sr_reads, sr_badReads, sr_leaf, sr_step, sr_trace, sr_badTrace, sr_driver, sr_badDriver,
      sr_op, sr_replayOp, sr_wakeToken, rfl, fun _ => rfl, rfl, rfl, rfl,
      sr_negative.1, sr_negative.2.1, sr_negative.2.2.1, sr_negative.2.2.2.1,
      sr_negative.2.2.2.2.1, rfl, sr_negative.2.2.2.2.2⟩
  · exact ⟨do_protocol, do_env, do_wire 2, rr_run, do_history, do_wireReads, rr_reads,
      rr_driver, 1, do_child, rr_wake, rfl, rfl, rr_original_origin,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rr_replacement_rejected⟩

#print axioms dependency_standalone_reconstruct_nontrivial
#print axioms dependency_reconstruct_wrong_origin_rejected


/-! ## X1b controls

Appended for X1b (lead ruling option D). Levels: (a), (b), (d) are driver-interface
executions with proved c3 trace laws (finite interface models, not ExecutionValid protocol
fixtures); (c) is a generic observation (an open driver-level control for E1F); the
converse control is a generic event fold. -/

section X1bControls
open AvailableChain.SimplexFG

/-! ### (a), (d) on the do_run driver fixture -/

private noncomputable abbrev doObs : FGExecutionObs Bool do_protocol :=
  driverFGExecutionObs do_env do_run do_driver (fun _ => do_trace) (fun _ => do_op)

private theorem do_hacc : ∀ k b, k ≤ do_trace.length →
    (b ∈ do_history.acceptedBodies (do_trace.state k) ↔
      do_reads.accepted (do_trace.state k) b) := by
  intro k b hk
  change k ≤ 14 at hk
  revert b
  interval_cases k <;> decide

private theorem do_origin :
    FGAcceptedBodyOrigin do_env do_run do_history do_wireReads doObs false :=
  accepted_body_origin_driver_at (Leaf := do_leafProtocol) do_env do_run do_history do_wireReads
    do_reads do_leaf do_step do_driver (fun _ => do_trace) (fun _ => do_op) do_arrival do_notify
    id id do_read false do_trace_laws do_hacc

/-- (a) The child body 2, received first, is admitted at microstep 9 by the drain of the
parent's arrival event 2; the bridge returns its own original token. -/
private theorem child_admitted_by_parent :
    ∃ o, doObs.accepts false 9 o ∧
      FGReceiptOrigin do_env do_run do_history do_wireReads false 2 o ∧ o = do_child ∧
      doObs.start false 2 ≤ 9 ∧ 9 < doObs.done false 2 ∧
      do_run.events[2]? = some (.deliver false (do_wire 1) 1) := by
  have hnew : (2 : Fin 4) ∈ do_history.acceptedBodies (doObs.cutState false (9 + 1)) := by decide
  have hold : (2 : Fin 4) ∉ do_history.acceptedBodies (doObs.cutState false 9) := by decide
  rcases do_origin.origin 9 2 (by decide) hnew hold with
    ⟨o, ⟨_, b, hop⟩, horig⟩ | ⟨j, t, wire, hj, _, hd, _, _⟩
  · have ho : o = do_child := by
      change FGDependencyOperation.leaf 2 do_child .accepted = .leaf b o .accepted at hop
      cases hop; rfl
    exact ⟨o, ⟨by decide, b, hop⟩, horig, ho, by decide, by decide, rfl⟩
  · have hj4 : j < 4 := (List.getElem?_eq_some_iff.mp hj).1
    interval_cases j <;> first | exact absurd hd (by decide) | simp at hj

/-- (d) The delayed old row: the acceptance at microstep 9 (time 1) carries the unchanged
original receipt of event 0 (time 0, same wire, rows equal to the body rows). -/
private theorem delayed_old_row :
    ∃ o, doObs.accepts false 9 o ∧
      FGReceiptOrigin do_env do_run do_history do_wireReads false 2 o ∧
      o.eventIndex = 0 ∧ o.receiptTime = 0 ∧ doObs.cutTime false 9 = 1 ∧
      o.wire = do_wire 2 ∧
      do_wireReads.decodedRows o.wire = do_wireReads.bodyRows 2 := by
  obtain ⟨o, hacc, horig, rfl, _⟩ := child_admitted_by_parent
  exact ⟨_, hacc, horig, rfl, rfl, rfl, rfl, horig.rows⟩

/-! ### (b) Admission during a completed restart: a new driver fixture -/

/-- The child arrives at 0, the parent at 1 is accepted, and the child's prior checks pass
only after the restart's reconstruction at 2; the restart's first drain admits the child. -/
private noncomputable abbrev rs_run : V2.D.Run Bool do_protocol :=
  { do_run with events := [.deliver false (do_wire 2) 0, .deliver false (do_wire 1) 1,
    .restart false 2] }

private noncomputable abbrev rs_history : FGHistoricalReads Nat (Fin 4) :=
  { do_history with
    acceptedBlocks := fun st => (if 6 ≤ st then [do_body 0, do_body 1, do_body 2]
      else if 3 ≤ st then [do_body 0, do_body 1] else [do_body 0]).toFinset
    acceptedBodies := fun st => if 6 ≤ st then [0, 1, 2] else if 3 ≤ st then [0, 1] else [0] }

private noncomputable abbrev rs_child : FGReceiptToken Bool do_protocol.Object :=
  ⟨false, 0, do_wire 2, 0, 0⟩
private noncomputable abbrev rs_parent : FGReceiptToken Bool do_protocol.Object :=
  ⟨false, 1, do_wire 1, 1, 0⟩

private noncomputable abbrev rs_reads : FGDependencyReads Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) Nat where
  accepted st b := b = 0 ∨ (b = 1 ∧ 3 ≤ st) ∨ (b = 2 ∧ 6 ≤ st)
  refused _ _ _ _ := False
  pending st b o := (b = 2 ∧ 1 ≤ st ∧ st < 6 ∧ o = rs_child) ∨
    (b = 1 ∧ st = 2 ∧ o = rs_parent)
  originAvailable st b o := (b = 2 ∧ 1 ≤ st ∧ o = rs_child) ∨
    (b = 1 ∧ 2 ≤ st ∧ o = rs_parent)
  validBody b := b ≠ 3
  priorChecks st b := (b = 1 ∧ st = 2) ∨ (b = 2 ∧ st = 5)
  timely _ _ := True
  conflictsFinal _ _ := False
  latest := id
  notified st b := b = 0 ∨ (b = 1 ∧ 4 ≤ st) ∨ (b = 2 ∧ 7 ≤ st)
  matching _ b := b = 2
  companionHeld st b := b = 2 ∧ 7 ≤ st
  latestKey _ _ := some (2, do_history.root 2)
  latestCompanion st _ := if 7 ≤ st then some 2 else none

private noncomputable abbrev rs_leafProtocol : V2.ProtocolSpecD Unit :=
  { do_protocol with process := fun st wire =>
    if st = 2 ∧ wire.payload = 1 then 3
    else if st = 5 ∧ wire.payload = 2 then 6 else st }

private noncomputable abbrev rs_leaf : FGDependencyLeaf Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) where
  step a b o outcome z := outcome = .accepted ∧
    ((a = 2 ∧ b = 1 ∧ o = rs_parent ∧ z = 3) ∨
     (a = 5 ∧ b = 2 ∧ o = rs_child ∧ z = 6))
  callback a b o z := (a = 2 ∧ b = 1 ∧ o = rs_parent ∧ z = 3) ∨
    (a = 5 ∧ b = 2 ∧ o = rs_child ∧ z = 6)
  report _ _ _ _ := False
  initial := 0
  genesis := 0

private noncomputable abbrev rs_step (kind : FGDependencyStepKind) (_ : Bool) (a z : Nat) : Prop :=
  a = z ∨ (kind = .arrival ∧ ((a = 0 ∧ z = 1) ∨ (a = 1 ∧ z = 2))) ∨
    (kind = .leafRetry ∧ ((a = 2 ∧ z = 3) ∨ (a = 5 ∧ z = 6))) ∨
    (kind = .notification ∧ ((a = 3 ∧ z = 4) ∨ (a = 6 ∧ z = 7))) ∨
    (kind = .ordinary ∧ a = 4 ∧ z = 5)

private noncomputable abbrev rs_driver : FGDependencyDriver Bool (Fin 4) do_protocol where
  enter st wire _ := if st = 0 ∧ wire.payload = 2 then 1
    else if st = 1 ∧ wire.payload = 1 then 2 else st
  enterProgram st wire _ := .finish (if st = 0 ∧ wire.payload = 2 then 1
    else if st = 1 ∧ wire.payload = 1 then 2 else st)
  hookProgram st op := match op with
    | .leaf b _ _ => .finish (rs_leafProtocol.process st (do_wire b))
    | .notification b _ =>
        .finish (if st = 3 ∧ b = 1 then 4 else if st = 6 ∧ b = 2 then 7 else st)
    | .reconstruct _ => .finish (if st = 4 then 5 else st)
    | _ => .finish st
  drain st := if 2 ≤ st ∧ st ≤ 3 then 4 else if 5 ≤ st ∧ st ≤ 6 then 7 else st
  reconstruct st _ := if st = 4 then 5 else st
  rebuild st _ := st
  retry st b _ _ := rs_leafProtocol.process st (do_wire b)
  work st e := if st = 2 then
    [.step (.leaf 1 rs_parent .accepted), .step (.notification 1 rs_parent)]
    else match e with
      | .deliver _ _ _ => if st = 1 then [.step .idle] else []
      | .restart _ t => if st = 4 then [.step (.reconstruct t),
          .step (.leaf 2 rs_child .accepted), .step (.notification 2 rs_child),
          .step (.rebuild t)] else [.step (.reconstruct t), .step (.rebuild t)]
      | _ => []
  inheritRefusal st _ _ := st
  notify st b _ := if st = 3 ∧ b = 1 then 4 else if st = 6 ∧ b = 2 then 7 else st
  replay st _ _ := st

private noncomputable abbrev rs_op (k : Nat) :
    FGDependencyOperation (Fin 4) (FGReceiptToken Bool do_protocol.Object) do_protocol.Object :=
  match k with
  | 0 => .arrival 2 rs_child
  | 3 => .arrival 1 rs_parent
  | 4 => .leaf 1 rs_parent .accepted
  | 5 => .notification 1 rs_parent
  | 7 => .restore 2
  | 8 => .reconstruct 2
  | 9 => .leaf 2 rs_child .accepted
  | 10 => .notification 2 rs_child
  | 11 => .rebuild 2
  | _ => .idle

private noncomputable abbrev rs_trace : FGDependencyTrace Nat where
  length := 12
  state k := [0, 1, 1, 1, 2, 3, 4, 4, 4, 5, 6, 7, 7][k]?.getD 7
  time k := [0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2][k]?.getD 2
  start j := [0, 3, 7][j]?.getD 12
  done j := [2, 6, 12][j]?.getD 12
  readCut _ := 12
  entryCut j := [1, 4, 8][j]?.getD 12
  dutyCut j := [2, 6, 11][j]?.getD 12
  hookRead _ _ _ _ _ := False

private noncomputable abbrev rs_arrival (a : Nat) (b : Fin 4)
    (o : FGReceiptToken Bool do_protocol.Object) (z : Nat) : Prop :=
  (a = 0 ∧ b = 2 ∧ o = rs_child ∧ z = 1) ∨ (a = 1 ∧ b = 1 ∧ o = rs_parent ∧ z = 2)

private noncomputable abbrev rs_notify (a : Nat) (b : Fin 4) (z : Nat) : Prop :=
  (a = 3 ∧ b = 1 ∧ z = 4) ∨ (a = 6 ∧ b = 2 ∧ z = 7)

private theorem rs_child_origin :
    FGReceiptOrigin do_env rs_run rs_history do_wireReads false 2 rs_child := by
  constructor <;> rfl

private theorem rs_parent_origin :
    FGReceiptOrigin do_env rs_run rs_history do_wireReads false 1 rs_parent := by
  constructor <;> rfl

private theorem rs_closed (st : Nat) (h : st = 1 ∨ st = 4 ∨ st = 7) :
    dependencyClosed rs_history rs_reads st := by
  intro work
  cases work with
  | inherit b o pending refused unresolved => exact refused.elim
  | retry b o pending valid prior timely held unresolved =>
    rcases h with rfl | rfl | rfl <;> simp_all
  | notify b resolved missing =>
    rcases h with rfl | rfl | rfl <;> simp_all [dependencyResolved, dependencyRefused]
  | companion b accepted matching missing =>
    rcases h with rfl | rfl | rfl <;> simp_all

private theorem rs_events_bound {j : Nat} {e : V2.Event Bool do_protocol.Object}
    (h : rs_run.events[j]? = some e) : j < 3 :=
  (List.getElem?_eq_some_iff.mp h).1

private theorem rs_arrival_laws :
    FGDependencyArrivalLeafLaws rs_history rs_reads rs_leaf rs_arrival rs_notify where
  direct_refusal_iff a b o z invoked := by
    simp
  arrival_effect a z b o arrived valid timely := by
    rcases arrived with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
      simp [Effect, dependencyResolved, dependencyRefused]
  arrival_inherits _ _ _ _ _ _ h := h.elim
  arrival_pending a z b o arrived valid timely fresh missing noRefusal noSelf := by
    rcases arrived with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inl ⟨rfl, by decide, by decide, rfl⟩
    · exact (missing (Or.inl rfl)).elim
  held_parent_accepts a z b o invoked := by
    obtain ⟨result, _, step⟩ := invoked
    rcases step with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
      simp [do_body]
  accepted_callback _ _ _ _ leaf := leaf.2
  callback_only a z b o callback := by
    refine ⟨⟨rfl, callback⟩, ?_, not_false⟩
    rcases callback with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> decide +kernel
  refusal_report _ _ _ _ h := h.elim
  rejected_no_refusal _ _ _ _ _ _ _ h := h.elim
  notification_resolved a z b notify := by
    rcases notify with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      simp [dependencyResolved, dependencyRefused]
  notification_keys _ _ _ _ := rfl
  notification_fields a z b i notify unmatched := by
    rcases notify with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rfl
    · simp at unmatched
  notification_matching a z b i slot notify held matching := by
    rcases notify with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have bad : (2 : Nat) = 1 :=
        congrArg BlockId.value (congrArg Prod.snd (Option.some.inj matching))
      omega
    · rfl
  refused_notification _ _ _ _ refused := refused.elim
  callback_latest a z b notify accepted := by
    rcases notify with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide +kernel

private theorem rs_micro_steps (k : Nat) (hk : k < rs_trace.length) :
    ∃ kind, rs_step kind false (rs_trace.state k) (rs_trace.state (k + 1)) := by
  change k < 12 at hk
  interval_cases k <;> first
    | exact ⟨.arrival, Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)⟩
    | exact ⟨.arrival, Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)⟩
    | exact ⟨.leafRetry, Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩))⟩
    | exact ⟨.leafRetry, Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩))⟩
    | exact ⟨.notification, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)))⟩
    | exact ⟨.notification, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)))⟩
    | exact ⟨.ordinary, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))⟩
    | exact ⟨.ordinary, Or.inl rfl⟩

private noncomputable abbrev rs_read (_ : Bool) (_ _ : Nat) : Prop := False

private theorem rs_trace_facts (k : Nat) (hk : k ≤ 12) :
    (1 ≤ rs_trace.state k → rs_trace.start 0 < k) ∧
    (2 ≤ rs_trace.state k → rs_trace.start 1 < k) ∧
    (∀ b, rs_reads.notified (rs_trace.state (k + 1)) b →
      ¬ rs_reads.notified (rs_trace.state k) b →
      (k = 5 ∧ b = 1) ∨ (k = 10 ∧ b = 2)) ∧
    (∀ b, rs_reads.accepted (rs_trace.state (k + 1)) b →
      ¬ rs_reads.accepted (rs_trace.state k) b →
      (k = 4 ∧ b = 1) ∨ (k = 9 ∧ b = 2)) := by
  interval_cases k <;> refine ⟨by decide, by decide, ?_, ?_⟩ <;> decide

private theorem rs_trace_laws :
    FGDependencyTraceLaws do_env rs_run false rs_history do_wireReads rs_reads rs_leaf
      rs_step rs_trace rs_driver rs_op rs_arrival rs_notify
      (Leaf := rs_leafProtocol) id id rs_read where
  arrival_laws := rs_arrival_laws
  initial := rfl
  initial_accepted b h := by simpa [rs_reads, do_protocol, rs_leaf] using h
  micro_step := rs_micro_steps
  external_step j e h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> exact ⟨rfl, rfl⟩
  step_kind k hk := by
    change k < 12 at hk
    interval_cases k <;> decide
  operation_bound k hk := by
    change k < 12 at hk
    interval_cases k <;> simp only [rs_op]
    all_goals first
      | rfl
      | exact ⟨Or.inl ⟨rfl, rfl, rfl, rfl⟩, rfl, rs_child_origin, rfl⟩
      | exact ⟨Or.inr ⟨rfl, rfl, rfl, rfl⟩, rfl, rs_parent_origin, rfl⟩
      | exact ⟨rfl, 2, rfl, rfl⟩
      | exact ⟨rfl, 2, rfl, by decide, by decide, fun q lo hi => by
          norm_num at lo hi; omega⟩
      | simp [dependencyResolved, dependencyRefused, rs_notify]
  delivery_entry j wire t h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> rfl
  work_execution j e h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> exact ⟨rfl, rfl⟩
  work_step j e k h lo hi := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      norm_num [rs_trace] at lo hi <;> interval_cases k <;> rfl
  hook_correspondence j e index kind cut st h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      change False ↔ ∃ r, ([] : List (FGDependencyWorkRead Nat))[index]? = some r ∧ _ <;>
      simp
  hook_reads j e r h member := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      change r ∈ ([] : List (FGDependencyWorkRead Nat)) at member <;> cases member
  receipt_entry j wire t b h awake valid decoded := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    · obtain ⟨_, rfl, rfl⟩ := V2.Event.deliver.inj h
      have hb := Option.some.inj decoded
      subst b
      simp [Effect, dependencyResolved, dependencyRefused, dependencyReceiverEpoch,
        rs_op, rs_arrival]
    · obtain ⟨_, rfl, rfl⟩ := V2.Event.deliver.inj h
      have hb := Option.some.inj decoded
      subst b
      simp [Effect, dependencyResolved, dependencyRefused, dependencyReceiverEpoch,
        rs_op, rs_arrival]
    · cases h
  entry_boundary j e h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      exact ⟨rfl, by decide, by decide, rfl, rfl⟩
  drain_operations j e k h lo hi := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      norm_num [rs_trace] at lo hi <;> interval_cases k
    all_goals first
      | exact Or.inl ⟨_, _, _, rfl⟩
      | exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨_, rfl, rfl, rfl⟩))))))
      | refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr ⟨_, rfl, by decide, rfl, ?_⟩))))))
    all_goals intro q lo hi; norm_num [rs_trace] at lo hi; omega
  boundary_idle k hk outside := by
    change k < 12 at hk
    interval_cases k <;> simp only [rs_op]
    all_goals exfalso; apply outside
    all_goals first
      | exact ⟨0, _, rfl, by decide, by decide⟩
      | exact ⟨1, _, rfl, by decide, by decide⟩
      | exact ⟨2, _, rfl, by decide, by decide⟩
  raw_restore j t h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> rfl
  raw_clock j t h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h
  restore_data _ _ := ⟨rfl, rfl, fun _ _ _ => Iff.rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  reconstruct_program _ _ := rfl
  reconstruct_data st t := by
    dsimp only
    by_cases h4 : st = 4
    · subst h4
      rw [ite_eq_left (rfl : (4 : Nat) = 4)]
      refine ⟨rfl, rfl, ?_, fun _ _ _ => Iff.rfl, ?_, ?_, ?_, ?_, fun _ _ h => h.elim⟩
      · intro b; revert b; decide
      · intro b o; simp
      · intro b o; simp
      · intro b; revert b; decide
      · intro b o h; rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1
    · rw [ite_eq_right h4]
      refine ⟨rfl, rfl, fun _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl,
        fun _ _ => Iff.rfl, fun _ => Iff.rfl, ?_, fun _ _ h => h.elim⟩
      intro b o h; rcases h with ⟨h1, -, -, h2⟩ | ⟨h1, -, -, h2⟩ <;> omega
  restart_reconstruct j t h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h
    exact ⟨by decide, rfl⟩
  restart_drain_closed j t h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h
    exact rs_closed 7 (Or.inr (Or.inr rfl))
  restart_replay_order j t k b o h lo hi op := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h
    norm_num [rs_trace] at lo hi ⊢
    interval_cases k <;> first | decide | cases op
  rebuild_program _ _ := rfl
  rebuild_data st _ := by
    refine ⟨rfl, rfl, fun _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => Iff.rfl, ?_, ?_⟩
    · intro b o h
      rcases h with (⟨rfl, rfl, rfl, hz⟩ | ⟨rfl, rfl, rfl, hz⟩) <;> cases hz
    · intro b o h; exact h.elim
  restart_rebuild j t h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h
    refine ⟨11, by decide, by decide, rfl, ?_, ?_, ?_, rfl⟩
    · intro q t lo hi op
      norm_num [rs_trace] at lo hi
      interval_cases q <;> first | rfl | cases op
    · intro q lo hi
      norm_num [rs_trace] at lo hi
      omega
    · intro q lo hi
      norm_num [rs_trace] at lo hi
      omega
  clock_no_insert _ _ := ⟨rfl, rfl⟩
  refusal_creation _ _ _ refused _ := refused.elim
  refusal_history _ _ _ refused := refused.elim
  notification_creation k b hk notified fresh := by
    change k < 12 at hk
    have key := (rs_trace_facts k (Nat.le_of_lt hk)).2.2.1 b notified fresh
    rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rs_parent, rfl, Or.inl ⟨rfl, rfl, rfl⟩, 4, by decide,
        Or.inl ⟨by decide, Or.inl ⟨rfl, rfl, rfl, rfl⟩, rfl⟩⟩
    · exact ⟨rs_child, rfl, Or.inr ⟨rfl, rfl, rfl⟩, 9, by decide,
        Or.inl ⟨by decide, Or.inr ⟨rfl, rfl, rfl, rfl⟩, rfl⟩⟩
  actual_read i st := by
    constructor
    · intro h; exact h.elim
    · rintro ⟨j, e, kind, he, required, _, _⟩
      have hj := rs_events_bound he
      interval_cases j <;> simp only [List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.some.injEq] at he <;> subst e <;>
        simp [dependencyReadRequired] at required
  read_order j e kind h required := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      simp [dependencyReadRequired] at required
  wire_validation wire b valid decoded := by
    have hb : wire.payload = b := Option.some.inj decoded
    simpa [do_protocol, rs_reads, hb] using valid
  origin_valid k b o hk origin := by
    change k ≤ 12 at hk
    rcases origin with ⟨rfl, h, rfl⟩ | ⟨rfl, h, rfl⟩
    · refine ⟨rs_child_origin, ?_⟩
      exact (rs_trace_facts k hk).1 h
    · refine ⟨rs_parent_origin, ?_⟩
      exact (rs_trace_facts k hk).2.1 h
  leaf_step k b o z hk leaf hz := by
    change k < 12 at hk
    rcases leaf with ⟨_, (⟨ha, rfl, rfl, rfl⟩ | ⟨ha, rfl, rfl, rfl⟩)⟩
    · refine ⟨rs_parent_origin, ?_, ?_⟩
      · apply (rs_trace_facts k (Nat.le_of_lt hk)).2.1
        rw [ha]
      · change 3 = rs_leafProtocol.process (rs_trace.state k) (do_wire 1)
        rw [ha]
        rfl
    · refine ⟨rs_child_origin, ?_, ?_⟩
      · apply (rs_trace_facts k (Nat.le_of_lt hk)).1
        rw [ha]
        decide
      · change 6 = rs_leafProtocol.process (rs_trace.state k) (do_wire 2)
        rw [ha]
        rfl
  origin_attribution k b hk held fresh := by
    have key := (rs_trace_facts k (Nat.le_of_lt hk)).2.2.2 b held fresh
    rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rs_parent, ⟨rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩,
        Or.inr ⟨rfl, by decide, rfl⟩, rfl, rfl, rfl⟩
    · exact ⟨rs_child, ⟨rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩,
        Or.inl ⟨rfl, by decide, rfl⟩, rfl, rfl, rfl⟩
  read_correspondence i st read := read.elim
  order_and_time i j ei ej hi hj le := by
    have bi := rs_events_bound hi
    have bj := rs_events_bound hj
    interval_cases i <;> interval_cases j <;>
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.some.injEq] at hi hj <;> subst ei <;> subst ej <;>
      decide +kernel
  finite_segment j e h := by
    have hj := rs_events_bound h
    interval_cases j <;> decide +kernel
  event_drain j y wire t h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq, V2.Event.deliver.injEq] at h
    · exact rs_closed 1 (Or.inl rfl)
    · exact rs_closed 4 (Or.inr (Or.inl rfl))
    · cases h
  entry_drain j e h := by
    have hj := rs_events_bound h
    interval_cases j
    · exact rs_closed 1 (Or.inl rfl)
    · exact rs_closed 4 (Or.inr (Or.inl rfl))
    · exact rs_closed 7 (Or.inr (Or.inr rfl))
  segment_time j e k h lower upper := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      norm_num [rs_trace] at lower upper <;> interval_cases k <;> rfl
  event_order i j ei ej hi hj lt := by
    have bi := rs_events_bound hi
    have bj := rs_events_bound hj
    interval_cases i <;> interval_cases j <;> decide
  completion_cut j e deadline h strict := by
    have hj := rs_events_bound h
    refine ⟨?_, ?_, ?_⟩
    · interval_cases j <;> decide +kernel
    · interval_cases j <;> simp only [List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> exact strict
    · intro i ei hi before
      have bi := rs_events_bound hi
      interval_cases i <;> interval_cases j <;>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.some.injEq] at hi h <;> subst ei <;> subst e <;>
        norm_num [rs_trace] at before <;>
        exact lt_of_le_of_lt (by decide) strict
  tick_records j t h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h
  atomic_tick j t h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h

private noncomputable abbrev rsObs : FGExecutionObs Bool do_protocol :=
  driverFGExecutionObs do_env rs_run rs_driver (fun _ => rs_trace) (fun _ => rs_op)

private theorem rs_hacc : ∀ k b, k ≤ rs_trace.length →
    (b ∈ rs_history.acceptedBodies (rs_trace.state k) ↔
      rs_reads.accepted (rs_trace.state k) b) := by
  intro k b hk
  change k ≤ 12 at hk
  revert b
  interval_cases k <;> decide

private theorem rs_origin :
    FGAcceptedBodyOrigin do_env rs_run rs_history do_wireReads rsObs false :=
  accepted_body_origin_driver_at (Leaf := rs_leafProtocol) do_env rs_run rs_history do_wireReads
    rs_reads rs_leaf rs_step rs_driver (fun _ => rs_trace) (fun _ => rs_op) rs_arrival rs_notify
    id id rs_read false rs_trace_laws rs_hacc

/-- (b) Admission during a completed restart: body 2 enters accepted storage at microstep 9,
after the reconstruction at 8, inside the segment [7, 12) of the restart event 2. The bridge
returns the original token of event 0 (time 0, epoch 0), not a restart-time token. -/
private theorem child_admitted_in_restart :
    ∃ o, rsObs.accepts false 9 o ∧
      FGReceiptOrigin do_env rs_run rs_history do_wireReads false 2 o ∧ o = rs_child ∧
      rs_run.events[2]? = some (.restart false 2) ∧ rsObs.start false 2 < 8 ∧
      rs_op 8 = .reconstruct 2 ∧ 9 < rsObs.done false 2 ∧
      o.receiptTime = 0 ∧ o.receiptEpoch = 0 ∧ dependencyReceiverEpoch rs_run false 3 = 3 := by
  have hnew : (2 : Fin 4) ∈ rs_history.acceptedBodies (rsObs.cutState false (9 + 1)) := by decide
  have hold : (2 : Fin 4) ∉ rs_history.acceptedBodies (rsObs.cutState false 9) := by decide
  rcases rs_origin.origin 9 2 (by decide) hnew hold with
    ⟨o, ⟨_, b, hop⟩, horig⟩ | ⟨j, t, wire, hj, _, hd, _, _⟩
  · have ho : o = rs_child := by
      change FGDependencyOperation.leaf 2 rs_child .accepted = .leaf b o .accepted at hop
      cases hop; rfl
    subst ho
    exact ⟨_, ⟨by decide, b, hop⟩, horig, rfl, rfl, by decide, rfl, by decide, rfl, rfl,
      by decide⟩
  · have hj3 : j < 3 := (List.getElem?_eq_some_iff.mp hj).1
    interval_cases j <;> simp at hj

/-! ### (c) One body with two distinct wire histories (generic observation) -/

private noncomputable abbrev tw_w1 : do_protocol.Object := do_wire 2
private noncomputable abbrev tw_w2 : do_protocol.Object := ⟨.none, 2⟩

private noncomputable abbrev tw_run : V2.D.Run Bool do_protocol :=
  { do_run with events := [.deliver false tw_w1 0, .deliver false tw_w2 1] }

private noncomputable abbrev tw_history : FGHistoricalReads Nat (Fin 4) :=
  { do_history with
    acceptedBlocks := fun st => (if 1 ≤ st then [do_body 0, do_body 2] else [do_body 0]).toFinset
    acceptedBodies := fun st => if 1 ≤ st then [0, 2] else [0] }

private noncomputable abbrev tw_t1 : FGReceiptToken Bool do_protocol.Object :=
  ⟨false, 0, tw_w1, 0, 0⟩
private noncomputable abbrev tw_t2 : FGReceiptToken Bool do_protocol.Object :=
  ⟨false, 1, tw_w2, 1, 0⟩

/-- Body 2 is received twice, by different wires; the step from cut 1 accepts it from the
first receipt only. -/
private noncomputable abbrev twObs : FGExecutionObs Bool do_protocol where
  stateBefore j _ := if 1 ≤ j then 1 else 0
  cutLength _ := 6
  cutState _ k := if 2 ≤ k then 1 else 0
  cutTime _ k := if k < 3 then 0 else 1
  start _ j := 3 * j
  entry _ j := 3 * j + 1
  duty _ j := 3 * j + 1
  done _ j := 3 * j + 2
  released _ _ := []
  finish _ st := st
  accepts _ k o := k = 1 ∧ o = tw_t1
  ownWrites _ _ := []

private theorem tw_origin1 :
    FGReceiptOrigin do_env tw_run tw_history do_wireReads false 2 tw_t1 := by
  constructor <;> rfl

private theorem tw_origin2 :
    FGReceiptOrigin do_env tw_run tw_history do_wireReads false 2 tw_t2 := by
  constructor <;> rfl

private theorem tw_body_origin :
    FGAcceptedBodyOrigin do_env tw_run tw_history do_wireReads twObs false where
  origin k b hk hb hnb := by
    change k < 6 at hk
    have key : k = 1 ∧ b = 2 := by
      revert hb hnb; revert b
      interval_cases k <;> decide
    obtain ⟨rfl, rfl⟩ := key
    exact Or.inl ⟨tw_t1, ⟨rfl, rfl⟩, tw_origin1⟩

/-- (c) Both receipts are full receipt origins of the same body by distinct wires; the origin
bridge keeps the one actually accepted (event 0, wire `tw_w1`), not the later one. -/
private theorem two_wire_histories :
    tw_w1 ≠ tw_w2 ∧ FGReceiptOrigin do_env tw_run tw_history do_wireReads false 2 tw_t1 ∧
      FGReceiptOrigin do_env tw_run tw_history do_wireReads false 2 tw_t2 ∧
      twObs.accepts false 1 tw_t1 ∧ ¬ twObs.accepts false 1 tw_t2 := by
  refine ⟨by decide, tw_origin1, tw_origin2, ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨_, h⟩
  have := congrArg FGReceiptToken.eventIndex h
  simp at this

/-! ### The ordinary bridge is one-way (integer time) -/

private def cvRow : Row (Fin 1) := ⟨0, .vote 3 ⟨2⟩ false, none⟩
private def cvB : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 [cvRow]

private abbrev cvProtocol : V2.ProtocolSpecD Unit where
  State := Bool
  Label := Unit
  Duty := Empty
  signLabel := Empty.elim
  seats := fun _ => 1
  Payload := Unit
  Durable := Bool
  init := false
  clock := fun st _ => st
  actTime := Empty.elim
  duties := fun _ => []
  duties_spec := by intro d; cases d
  duties_nodup := by intro t; exact List.nodup_nil
  act := fun _ d _ => Empty.elim d
  gossip := fun _ _ => []
  process := fun _ _ => true
  selfVisible := fun _ => false
  recordOwn := fun st _ => st
  durable := fun st => st
  restore := fun d _ => d
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

private abbrev cvEnv : Generic.Env Unit where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ _ => true

private noncomputable abbrev cvObj : cvProtocol.Object := ⟨.none, ()⟩

/-- Tick at 1, admission by a delivery at 3, tick at 4. -/
private noncomputable abbrev cvTrace : V2.D.Run Unit cvProtocol where
  honest := {()}
  horizon := 5
  events := [.tick () 1, .deliver () cvObj 3, .tick () 4]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

private noncomputable abbrev cvReads : FGCoreReads cvProtocol 1 Unit Unit Unit where
  core st := ⟨(), ⟨if st then {.genesis, cvB} else {.genesis}, .genesis, .genesis, 0, 1⟩,
    [], []⟩
  erase := fun _ => .genesis
  source := fun _ => none
  headVote := fun _ _ => .genesis
  finalityHead := fun _ => none
  proposalFG := fun _ _ => none

private theorem cv_positive :
    FGChainRowsAtCut cvReads cvTrace (ordinaryFGExecutionObs cvEnv cvTrace) cvB 4 := by
  intro W hW _ _
  have hmem : cvB ∈ (cvReads.core
      ((ordinaryFGExecutionObs cvEnv cvTrace).cutState () 5)).fg.TF := by decide
  have hcl : ∀ B ∈ (cvReads.core
      ((ordinaryFGExecutionObs cvEnv cvTrace).cutState () 5)).fg.TF,
      B.parent ∈ (cvReads.core ((ordinaryFGExecutionObs cvEnv cvTrace).cutState () 5)).fg.TF := by
    decide
  refine ⟨(), Finset.mem_singleton_self _, Or.inr ⟨1, _, 5, rfl, by decide, le_rfl, ?_,
    KitFG.ancestor_closed_of_parent_closed _ hcl cvB hmem W hW⟩⟩
  intro i ei hi hle
  have hi3 : i < 3 := (List.getElem?_eq_some_iff.mp hi).1
  interval_cases i <;> simp at hi <;> subst ei <;> decide

/-- The converse of `ordinary_chainRows_atCut_of_before` fails: with integer time the block
admitted at time 3 has a strict-cut witness before 4 but no strict-time read `t < 4`. -/
private theorem ordinary_converse_fails :
    FGChainRowsAtCut cvReads cvTrace (ordinaryFGExecutionObs cvEnv cvTrace) cvB 4 ∧
      ¬ ChainRowsBefore cvReads cvEnv cvTrace cvB 4 := by
  refine ⟨cv_positive, ?_⟩
  intro h
  obtain ⟨x, t, _, ht, hheld⟩ := h cvB (KitFG.preceq_refl _) cvRow (List.mem_singleton_self _)
  rw [Gen.V2.Duty.HoldsBefore_def] at hheld
  cases x
  have h3 : ¬ ((3 : Time) < t) := fun h =>
    absurd ht (not_lt.mpr (by simpa using Int.add_one_le_of_lt h))
  have h4 : ¬ ((4 : Time) < t) := fun h => absurd ht (not_lt.mpr h.le)
  unfold V2.D.Run.stateBeforeTime at hheld
  by_cases h1 : (1 : Time) < t
  · simp [V2.Event.time, h1, h3, h4] at hheld
    revert hheld
    decide
  · simp [V2.Event.time, h1, h3, h4] at hheld
    revert hheld
    decide

#print axioms do_hacc
#print axioms do_origin
#print axioms child_admitted_by_parent
#print axioms delayed_old_row
#print axioms rs_trace_laws
#print axioms rs_hacc
#print axioms rs_origin
#print axioms child_admitted_in_restart
#print axioms tw_body_origin
#print axioms two_wire_histories
#print axioms cv_positive
#print axioms ordinary_converse_fails

end X1bControls

end AvailableChain.FGCompose.Tests.DependencyOrigins
end
