module
public import AvailableChainFGCompose.Proofs.Dependency

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.DependencyRetention

private def dr_history : FGHistoricalReads Bool Nat where
  acceptedBlocks _ := ∅
  acceptedBodies _ := []
  erase _ := .genesis
  root b := ⟨b⟩
  parent b := b - 1
  slot b := b
  readBlock _ _ := none
  preceq := (· ≤ ·)
  depth := id
  lca _ _ := .genesis

private def dr_reads : FGDependencyReads Bool Nat Nat Unit where
  accepted _ _ := False
  refused _ _ _ _ := False
  pending st b o := st = true ∧ b = 2 ∧ o = 7
  originAvailable _ b o := b = 2 ∧ o = 7
  validBody b := b = 2
  priorChecks _ _ := True
  timely _ _ := True
  conflictsFinal _ _ := False
  latest _ := ()
  notified _ _ := True
  matching _ _ := False
  companionHeld _ _ := False
  latestKey _ _ := none
  latestCompanion _ _ := none

private def dr_leaf : FGDependencyLeaf Bool Nat Nat where
  step _ _ _ _ _ := False
  callback _ _ _ _ := False
  report _ _ _ _ := False
  initial := false
  genesis := 0

private def dr_keep : FGDependencyStepKind → Unit → Bool → Bool → Prop :=
  fun _ _ a b => a = b

private theorem dr_keep_laws :
    FGDependencyStepLaws dr_history dr_reads dr_leaf dr_keep (fun s _ => s)
      (fun _ _ => False) where
  accepted_keep _ _ _ _ _ _ h := h.elim
  refused_keep _ _ _ _ _ _ _ _ h := h.elim
  pending_effect _ _ a b body origin h pending := by
    change a = b at h
    subst b
    exact ⟨pending.2, Or.inl pending⟩
  origin_keep _ _ _ _ _ _ _ h := h
  metadata_fg_eq _ _ _ _ _ _ _ := rfl
  insertion_leaf _ _ _ _ _ _ h _ := h.elim
  one_body _ _ _ _ _ h := h.elim
  restore_exact _ _ := ⟨rfl, rfl, fun _ _ _ => Iff.rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  no_signing _ _ _ _ _ := not_false

/-- Every named kind retains the original receipt, including restart before any PC. -/
private theorem dr_all_step_kinds (kind : FGDependencyStepKind) :
    Effect dr_history dr_reads true 2 7 :=
  dependency_effect_step dr_keep_laws (kind := kind) (x := ()) rfl
    ⟨⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl, rfl⟩⟩

private theorem dr_erase_then_quiesce :
    dependencyClosed dr_history dr_reads false ∧ ¬ Effect dr_history dr_reads false 2 7 := by
  constructor
  · intro work
    cases work <;> simp_all [dr_reads, dependencyResolved, dependencyRefused]
  · simp [Effect, dependencyResolved, dependencyRefused, dr_reads]

private theorem dr_erasure_rejected (kind : FGDependencyStepKind) :
    ¬ FGDependencyStepLaws dr_history dr_reads dr_leaf
      (fun k (_ : Unit) a b => k = kind ∧ a = true ∧ b = false)
      (fun s _ => s) (fun _ _ => False) := by
  intro laws
  exact dr_erase_then_quiesce.2
    (laws.pending_effect kind () true false 2 7 ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩)

private def dr_refusedReads : FGDependencyReads Nat Nat Nat Unit where
  accepted _ b := b = 0
  refused st b r pr := 0 < b ∧ b ≤ st ∧ r = ⟨b⟩ ∧ pr = ⟨b - 1⟩
  pending st b o := st < b ∧ b ≤ 3 ∧ o = b
  originAvailable _ b o := o = b
  validBody b := b ≤ 3
  priorChecks _ _ := True
  timely _ _ := True
  conflictsFinal _ _ := True
  latest _ := ()
  notified _ _ := True
  matching _ _ := False
  companionHeld _ _ := False
  latestKey _ _ := none
  latestCompanion _ _ := none

private def dr_refusedHistory : FGHistoricalReads Nat Nat where
  acceptedBlocks _ := {.genesis}
  acceptedBodies _ := [0]
  erase _ := .genesis
  root b := ⟨b⟩
  parent b := b - 1
  slot b := b
  readBlock _ _ := none
  preceq := (· ≤ ·)
  depth := id
  lca _ _ := .genesis

private def dr_refusalLeaf : FGDependencyLeaf Nat Nat Nat where
  step a b o result z := a = 0 ∧ b = 1 ∧ o = 1 ∧ result = .definitiveRefused ∧ z = 1
  callback _ _ _ _ := False
  report _ _ _ _ := True
  initial := 0
  genesis := 0

private def dr_directEvent (k b o : Nat) : Prop := k = 0 ∧ b = 1 ∧ o = 1
private def dr_inheritEvent (k b o : Nat) : Prop := k + 1 = b ∧ o = b ∧ 1 ≤ k

private theorem dr_direct_and_recursive_evidence :
    FGDependencyRefusalEvidence dr_refusedHistory dr_refusedReads dr_refusalLeaf
      id dr_directEvent dr_inheritEvent 3 3 3 := by
  have h1 : FGDependencyRefusalEvidence dr_refusedHistory dr_refusedReads dr_refusalLeaf
      id dr_directEvent dr_inheritEvent 1 1 1 := by
    refine .direct 0 1 1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [dr_directEvent, dr_refusedReads, dr_refusedHistory, dr_refusalLeaf]
  have h2 : FGDependencyRefusalEvidence dr_refusedHistory dr_refusedReads dr_refusalLeaf
      id dr_directEvent dr_inheritEvent 2 2 2 := by
    refine .inherited 1 1 2 2 1 ?_ ?_ ?_ ?_ ?_ h1 ?_ <;>
      simp [dr_inheritEvent, dr_refusedReads, dr_refusedHistory, dependencyRefused]
  refine .inherited 2 2 3 3 2 ?_ ?_ ?_ ?_ ?_ h2 ?_ <;>
    simp [dr_inheritEvent, dr_refusedReads, dr_refusedHistory, dependencyRefused]

private theorem dr_late_child_always_pending_rejected :
    FGDependencyEnabled dr_refusedHistory dr_refusedReads 1 := by
  exact .inherit 2 2 ⟨by decide, by decide, rfl⟩
    ⟨by decide, by decide, rfl, rfl⟩ (by
      simp [dependencyResolved, dependencyRefused, dr_refusedReads, dr_refusedHistory])

/-- The reverse order has the same enabled recursive work after the parent report. -/
private theorem dr_recursive_child_rejected :
    FGDependencyEnabled dr_refusedHistory dr_refusedReads 2 := by
  exact .inherit 3 3 ⟨by decide, by decide, rfl⟩
    ⟨by decide, by decide, rfl, rfl⟩ (by
      simp [dependencyResolved, dependencyRefused, dr_refusedReads, dr_refusedHistory])

private theorem dr_both_orders_and_restart :
    dependencyRefused dr_refusedHistory dr_refusedReads (max (max 0 1) 3) 3 ∧
    dependencyRefused dr_refusedHistory dr_refusedReads (max (max 0 3) 1) 3 ∧
    dependencyRefused dr_refusedHistory dr_refusedReads (id 3) 3 := by
  simp [dependencyRefused, dr_refusedHistory, dr_refusedReads]

/-- This inhabited retained state cannot be consumed by a closed read. -/
private theorem dr_early_read_rejected :
    ¬ dependencyClosed dr_refusedHistory dr_refusedReads 1 :=
  fun closed => closed dr_late_child_always_pending_rejected

private theorem dr_held_conflict_report
    {State Body Origin Latest : Type} {H : FGHistoricalReads State Body}
    {D : FGDependencyReads State Body Origin Latest}
    {L : FGDependencyLeaf State Body Origin}
    {Arrival : State → Body → Origin → State → Prop}
    {Notify : State → Body → State → Prop}
    (laws : FGDependencyArrivalLeafLaws H D L Arrival Notify) {a b o z}
    (leaf : L.step a b o .definitiveRefused z) :
    D.validBody b ∧ D.priorChecks a b ∧ D.timely a b ∧ ¬ D.accepted a b ∧
    D.accepted a (H.parent b) ∧ D.conflictsFinal a b := by
  have h := (laws.direct_refusal_iff a b o z ⟨_, leaf⟩).mp leaf
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

private theorem dr_invalid_future_duplicate_missing_no_new_refusal
    {State Body Origin Latest : Type} {H : FGHistoricalReads State Body}
    {D : FGDependencyReads State Body Origin Latest}
    {L : FGDependencyLeaf State Body Origin}
    {Arrival : State → Body → Origin → State → Prop}
    {Notify : State → Body → State → Prop}
    (laws : FGDependencyArrivalLeafLaws H D L Arrival Notify) {a b o z result}
    (leaf : L.step a b o result z)
    (bad : result = .invalid ∨ result = .future ∨ result = .duplicate ∨ result = .pending)
    (fresh : ¬ dependencyRefused H D a b) : ¬ dependencyRefused H D z b :=
  fun refused => fresh (laws.rejected_no_refusal a z b o result leaf bad refused)

private theorem dr_no_acceptance_callback_for_refusal
    {State Body Origin Latest : Type} {H : FGHistoricalReads State Body}
    {D : FGDependencyReads State Body Origin Latest}
    {L : FGDependencyLeaf State Body Origin}
    {Arrival : State → Body → Origin → State → Prop}
    {Notify : State → Body → State → Prop}
    (laws : FGDependencyArrivalLeafLaws H D L Arrival Notify) {a b o z}
    (refused : dependencyRefused H D z b) : ¬ L.callback a b o z :=
  fun callback => (laws.callback_only a z b o callback).2.2 refused

private theorem dr_late_arrival_pending_rejected :
    ¬ FGDependencyArrivalLeafLaws dr_refusedHistory dr_refusedReads dr_refusalLeaf
      (fun a b o z => a = 1 ∧ b = 2 ∧ o = 2 ∧ z = 1) (fun _ _ _ => False) := by
  intro laws
  have refused := (laws.arrival_inherits 1 1 2 2 ⟨rfl, rfl, rfl, rfl⟩
    (by change (2 : Nat) ≤ 3; decide) ⟨by decide, by decide, rfl, rfl⟩).1
  have impossible : (2 : Nat) ≤ 1 := refused.2.1
  omega

/-- An inhabited one-body refusal, report and notification interface model. -/
private def dr_lawfulReads : FGDependencyReads Nat Nat Nat Unit where
  accepted _ b := b = 0
  refused st b r pr := 1 ≤ st ∧ b = 1 ∧ r = ⟨1⟩ ∧ pr = ⟨0⟩
  pending _ _ _ := False
  originAvailable _ b o := b = 1 ∧ o = 1
  validBody b := b = 1
  priorChecks _ _ := True
  timely _ _ := True
  conflictsFinal _ _ := True
  latest _ := ()
  notified st b := b = 0 ∨ (b = 1 ∧ 2 ≤ st)
  matching _ _ := False
  companionHeld _ _ := False
  latestKey _ _ := none
  latestCompanion _ _ := none

private def dr_lawfulLeaf : FGDependencyLeaf Nat Nat Nat where
  step a b o result z := a = 0 ∧ b = 1 ∧ o = 1 ∧ result = .definitiveRefused ∧ z = 1
  callback _ _ _ _ := False
  report a b o z := a = 0 ∧ b = 1 ∧ o = 1 ∧ z = 1
  initial := 0
  genesis := 0

private def dr_lawfulNotify (a b z : Nat) : Prop := a = 1 ∧ b = 1 ∧ z = 2

private theorem dr_lawful_refusal_laws :
    FGDependencyArrivalLeafLaws dr_refusedHistory dr_lawfulReads dr_lawfulLeaf
      (fun _ _ _ _ => False) dr_lawfulNotify where
  direct_refusal_iff a b o z invoked := by
    obtain ⟨result, rfl, rfl, rfl, rfl, rfl⟩ := invoked
    simp [dr_lawfulLeaf, dr_lawfulReads, dependencyRefused, dr_refusedHistory]
  arrival_effect _ _ _ _ h := h.elim
  arrival_inherits _ _ _ _ h := h.elim
  arrival_pending _ _ _ _ h := h.elim
  held_parent_accepts a z b o invoked := by
    obtain ⟨result, rfl, rfl, rfl, rfl, rfl⟩ := invoked
    simp [dr_lawfulLeaf, dr_lawfulReads]
  accepted_callback a z b o h := by cases h.2.2.2.1
  callback_only _ _ _ _ h := h.elim
  refusal_report a z b o h := by
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    simp [dependencyRefused, dr_lawfulReads, dr_refusedHistory]
  rejected_no_refusal a z b o result h bad := by
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
    rcases bad with h | h | h | h <;> cases h
  notification_resolved a z b h := by
    rcases h with ⟨rfl, rfl, rfl⟩
    exact Or.inr ⟨by decide, rfl, rfl, rfl⟩
  notification_keys _ _ _ _ := rfl
  notification_fields _ _ _ _ _ _ := rfl
  notification_matching a z b i slot h accepted := by
    rcases h with ⟨rfl, rfl, rfl⟩
    cases accepted
  refused_notification a z b h _ := by
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨Or.inr ⟨rfl, by decide⟩, rfl⟩
  callback_latest a z b h accepted := by
    rcases h with ⟨rfl, rfl, rfl⟩
    cases accepted

private theorem dr_conflict_executes_refusal :
    dr_lawfulReads.validBody 1 ∧ dr_lawfulReads.priorChecks 0 1 ∧
    dr_lawfulReads.accepted 0 (dr_refusedHistory.parent 1) ∧
    dr_lawfulReads.conflictsFinal 0 1 ∧
    dr_lawfulLeaf.step 0 1 1 .definitiveRefused 1 ∧
    dr_lawfulLeaf.report 0 1 1 1 ∧ dr_lawfulNotify 1 1 2 ∧
    dr_lawfulReads.notified 2 1 ∧ ¬ dr_lawfulLeaf.callback 0 1 1 1 := by
  simp [dr_lawfulReads, dr_refusedHistory, dr_lawfulLeaf, dr_lawfulNotify]

/-- The specified bad handler creates a fresh refusal while returning a rejected outcome. -/
private def dr_badLeaf (outcome : FGDependencyOutcome) : FGDependencyLeaf Nat Nat Nat :=
  { dr_lawfulLeaf with
    step := fun a b o result z => a = 0 ∧ b = 1 ∧ o = 1 ∧ result = outcome ∧ z = 1 }

private theorem dr_bad_rejected_transition (outcome : FGDependencyOutcome)
    (bad : outcome = .invalid ∨ outcome = .future ∨
      outcome = .duplicate ∨ outcome = .pending)
    (reads : FGDependencyReads Nat Nat Nat Unit)
    (before : ¬ dependencyRefused dr_refusedHistory reads 0 1)
    (after : dependencyRefused dr_refusedHistory reads 1 1) :
    ¬ FGDependencyArrivalLeafLaws dr_refusedHistory reads (dr_badLeaf outcome)
      (fun _ _ _ _ => False) dr_lawfulNotify := by
  intro laws
  exact before (laws.rejected_no_refusal 0 1 1 1 outcome
    ⟨rfl, rfl, rfl, rfl, rfl⟩ bad after)

private def dr_invalidReads := { dr_lawfulReads with validBody := fun _ => False }
private def dr_futureReads := { dr_lawfulReads with timely := fun _ _ => False }
private def dr_duplicateReads :=
  { dr_lawfulReads with accepted := fun _ b => b = 0 ∨ b = 1 }
private def dr_missingReads := { dr_lawfulReads with accepted := fun _ _ => False }

private theorem dr_invalid_fresh_refusal_rejected :
    ¬ dr_invalidReads.validBody 1 ∧
    ¬ FGDependencyArrivalLeafLaws dr_refusedHistory dr_invalidReads (dr_badLeaf .invalid)
      (fun _ _ _ _ => False) dr_lawfulNotify :=
  ⟨not_false, dr_bad_rejected_transition .invalid (Or.inl rfl) _
    (by simp [dependencyRefused, dr_invalidReads, dr_lawfulReads])
    ⟨by decide, rfl, rfl, rfl⟩⟩

private theorem dr_future_fresh_refusal_rejected :
    ¬ dr_futureReads.timely 0 1 ∧
    ¬ FGDependencyArrivalLeafLaws dr_refusedHistory dr_futureReads (dr_badLeaf .future)
      (fun _ _ _ _ => False) dr_lawfulNotify :=
  ⟨not_false, dr_bad_rejected_transition .future (Or.inr (Or.inl rfl)) _
    (by simp [dependencyRefused, dr_futureReads, dr_lawfulReads])
    ⟨by decide, rfl, rfl, rfl⟩⟩

private theorem dr_duplicate_fresh_refusal_rejected :
    dr_duplicateReads.accepted 0 1 ∧
    ¬ FGDependencyArrivalLeafLaws dr_refusedHistory dr_duplicateReads (dr_badLeaf .duplicate)
      (fun _ _ _ _ => False) dr_lawfulNotify :=
  ⟨Or.inr rfl, dr_bad_rejected_transition .duplicate (Or.inr (Or.inr (Or.inl rfl))) _
    (by simp [dependencyRefused, dr_duplicateReads, dr_lawfulReads])
    ⟨by decide, rfl, rfl, rfl⟩⟩

private theorem dr_missing_fresh_refusal_rejected :
    ¬ dr_missingReads.accepted 0 (dr_refusedHistory.parent 1) ∧
    ¬ FGDependencyArrivalLeafLaws dr_refusedHistory dr_missingReads (dr_badLeaf .pending)
      (fun _ _ _ _ => False) dr_lawfulNotify :=
  ⟨not_false, dr_bad_rejected_transition .pending (Or.inr (Or.inr (Or.inr rfl))) _
    (by simp [dependencyRefused, dr_missingReads, dr_lawfulReads])
    ⟨by decide, rfl, rfl, rfl⟩⟩

private theorem dr_accepted_refused_coexistence_rejected :
    dr_duplicateReads.validBody 1 ∧ dr_duplicateReads.accepted 1 1 ∧
    dependencyRefused dr_refusedHistory dr_duplicateReads 1 1 ∧
    ¬ FGDependencyStateLaws dr_refusedHistory dr_duplicateReads dr_lawfulLeaf := by
  refine ⟨rfl, Or.inr rfl, ⟨by decide, rfl, rfl, rfl⟩, ?_⟩
  intro laws
  exact laws.accepted_refused_disjoint 1 1 rfl (Or.inr rfl)
    ⟨by decide, rfl, rfl, rfl⟩

#print axioms dr_lawful_refusal_laws
#print axioms dr_conflict_executes_refusal
#print axioms dr_invalid_fresh_refusal_rejected
#print axioms dr_future_fresh_refusal_rejected
#print axioms dr_duplicate_fresh_refusal_rejected
#print axioms dr_missing_fresh_refusal_rejected
#print axioms dr_accepted_refused_coexistence_rejected

/-- Executable receipt and refusal stores; neither arrival order is a maximum shortcut. -/
private abbrev dr_OrderState := Finset Nat × Finset Nat

private def dr_orderArrival (st : dr_OrderState) (b : Nat) : dr_OrderState :=
  (insert b st.1, if b - 1 ∈ st.2 then insert b st.2 else st.2)

private def dr_orderRefuse (st : dr_OrderState) (b : Nat) : dr_OrderState :=
  (st.1, insert b st.2)

private def dr_orderRestore (st : dr_OrderState) (_ : Time) := st

private def dr_orderHistory : FGHistoricalReads dr_OrderState Nat where
  acceptedBlocks _ := {.genesis}
  acceptedBodies _ := [0]
  erase _ := .genesis
  root b := ⟨b⟩
  parent b := b - 1
  slot := id
  readBlock _ _ := none
  preceq := (· ≤ ·)
  depth := id
  lca _ _ := .genesis

private def dr_orderReads : FGDependencyReads dr_OrderState Nat Nat Unit where
  accepted _ b := b = 0
  refused st b r pr := b ∈ st.2 ∧ r = ⟨b⟩ ∧ pr = ⟨b - 1⟩
  pending st b o := b ∈ st.1 ∧ b ∉ st.2 ∧ o = b
  originAvailable st b o := b ∈ st.1 ∧ o = b
  validBody _ := True
  priorChecks _ _ := True
  timely _ _ := True
  conflictsFinal _ _ := True
  latest _ := ()
  notified _ _ := True
  matching _ _ := False
  companionHeld _ _ := False
  latestKey _ _ := none
  latestCompanion _ _ := none

private def dr_orderLeaf : FGDependencyLeaf dr_OrderState Nat Nat where
  step a b o result z := b = 1 ∧ o = b ∧ b ∈ a.1 ∧
    result = .definitiveRefused ∧ z = dr_orderRefuse a b
  callback _ _ _ _ := False
  report a b o z := o = b ∧ z = dr_orderRefuse a b
  initial := (∅, ∅)
  genesis := 0

private def dr_orderStep (kind : FGDependencyStepKind) (_ : Unit)
    (a z : dr_OrderState) : Prop :=
  (kind = .arrival ∧ ∃ b, z = dr_orderArrival a b) ∨
  (kind = .leafRetry ∧ 1 ∈ a.1 ∧ z = dr_orderRefuse a 1) ∨
  (kind = .refusalPropagation ∧ ∃ b, b ∈ a.1 ∧ b - 1 ∈ a.2 ∧
    z = dr_orderRefuse a b) ∨ (kind = .restore ∧ z = dr_orderRestore a 0)

private theorem dr_order_store_growth {kind a z} (step : dr_orderStep kind () a z) :
    a.1 ⊆ z.1 ∧ a.2 ⊆ z.2 := by
  rcases step with ⟨_, b, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, b, _, _, rfl⟩ | ⟨_, rfl⟩
  · simp only [dr_orderArrival]
    split <;> simp
  · simp [dr_orderRefuse]
  · simp [dr_orderRefuse]
  · exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

private theorem dr_order_step_laws :
    FGDependencyStepLaws dr_orderHistory dr_orderReads dr_orderLeaf dr_orderStep
      dr_orderRestore (fun _ _ => False) where
  accepted_keep _ _ _ _ _ _ h := h
  refused_keep k x a z b r pr step h := by
    cases x
    exact ⟨(dr_order_store_growth step).2 h.1, h.2⟩
  pending_effect k x a z b o step h := by
    cases x
    have received := (dr_order_store_growth step).1 h.1
    refine ⟨⟨received, h.2.2⟩, ?_⟩
    by_cases refused : b ∈ z.2
    · exact Or.inr (Or.inr ⟨refused, rfl, rfl⟩)
    · exact Or.inl ⟨received, refused, h.2.2⟩
  origin_keep k x a z b o step h := by
    cases x
    exact ⟨(dr_order_store_growth step).1 h.1, h.2⟩
  metadata_fg_eq _ _ _ _ _ _ _ := rfl
  insertion_leaf _ _ _ _ _ _ held fresh := (fresh held).elim
  one_body _ _ _ _ _ _ _ held := Or.inl held
  restore_exact _ _ := ⟨rfl, rfl, fun _ _ _ => Iff.rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  no_signing _ _ _ _ _ := not_false

private def dr_childFirst : dr_OrderState :=
  dr_orderRestore
    (dr_orderRefuse (dr_orderRefuse
      (dr_orderArrival (dr_orderArrival (∅, ∅) 2) 1) 1) 2) 9

private def dr_parentFirst : dr_OrderState :=
  dr_orderArrival
    (dr_orderRestore (dr_orderRefuse (dr_orderArrival (∅, ∅) 1) 1) 9) 2

private theorem dr_reverse_order_executes_and_restores :
    FGDependencySteps dr_orderStep () (∅, ∅) dr_childFirst ∧
    FGDependencySteps dr_orderStep () (∅, ∅) dr_parentFirst ∧
    dependencyRefused dr_orderHistory dr_orderReads dr_childFirst 2 ∧
    dependencyRefused dr_orderHistory dr_orderReads dr_parentFirst 2 ∧
    Effect dr_orderHistory dr_orderReads dr_childFirst 2 2 ∧
    Effect dr_orderHistory dr_orderReads dr_parentFirst 2 2 := by
  have child : FGDependencySteps dr_orderStep () (∅, ∅) dr_childFirst := by
    apply FGDependencySteps.tail .restore
    · apply FGDependencySteps.tail .refusalPropagation
      · apply FGDependencySteps.tail .leafRetry
        · apply FGDependencySteps.tail .arrival
          · exact .tail .arrival (.refl _) (Or.inl ⟨rfl, 2, rfl⟩)
          · exact Or.inl ⟨rfl, 1, rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, by decide, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, 2, by decide, by decide, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  have parent : FGDependencySteps dr_orderStep () (∅, ∅) dr_parentFirst := by
    apply FGDependencySteps.tail .arrival
    · apply FGDependencySteps.tail .restore
      · exact .tail .leafRetry
          (.tail .arrival (.refl _) (Or.inl ⟨rfl, 1, rfl⟩))
          (Or.inr (Or.inl ⟨rfl, by decide, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · exact Or.inl ⟨rfl, 2, rfl⟩
  refine ⟨child, parent, ?_, ?_, ?_, ?_⟩ <;>
    simp [dependencyRefused, Effect, dependencyResolved, dr_orderReads,
      dr_orderHistory, dr_childFirst, dr_parentFirst, dr_orderArrival,
      dr_orderRefuse, dr_orderRestore]

#print axioms dr_order_step_laws
#print axioms dr_reverse_order_executes_and_restores

#print axioms dr_late_arrival_pending_rejected

#print axioms dr_direct_and_recursive_evidence
#print axioms dr_keep_laws
#print axioms dr_all_step_kinds
#print axioms dr_erase_then_quiesce
#print axioms dr_erasure_rejected
#print axioms dr_late_child_always_pending_rejected
#print axioms dr_recursive_child_rejected
#print axioms dr_both_orders_and_restart
#print axioms dr_early_read_rejected
#print axioms dr_held_conflict_report
#print axioms dr_invalid_future_duplicate_missing_no_new_refusal
#print axioms dr_no_acceptance_callback_for_refusal

end AvailableChain.FGCompose.Tests.DependencyRetention
end
