module
public import AvailableChainFGCompose.Statements.HistoricalReads

@[expose] public section

namespace AvailableChain.FGCompose

inductive FGDependencyOutcome where
  | accepted | definitiveRefused | pending | duplicate | future | invalid
  deriving DecidableEq

inductive FGDependencyStepKind where
  | arrival | leafRetry | refusalPropagation | notification
  | ordinary | ownRecord | clock | restore
  deriving DecidableEq

/-- Body identity comes from the cumulative historical store, never a frame. -/
structure FGDependencyReads (State Body Origin Latest : Type) where
  accepted : State → Body → Prop
  refused : State → Body → BlockId → BlockId → Prop
  pending : State → Body → Origin → Prop
  originAvailable : State → Body → Origin → Prop
  validBody : Body → Prop
  priorChecks : State → Body → Prop
  timely : State → Body → Prop
  conflictsFinal : State → Body → Prop
  latest : State → Latest
  notified : State → Body → Prop
  matching : Latest → Body → Prop
  companionHeld : Latest → Body → Prop
  latestKey : Latest → Fin 5 → Option (Slot × BlockId)
  latestCompanion : Latest → Fin 5 → Option Body

variable {State Body Origin Latest V : Type}

def dependencyRefused (H : FGHistoricalReads State Body)
    (D : FGDependencyReads State Body Origin Latest) (st : State) (b : Body) : Prop :=
  D.refused st b (H.root b) (H.root (H.parent b))

def dependencyResolved (H : FGHistoricalReads State Body)
    (D : FGDependencyReads State Body Origin Latest) (st : State) (b : Body) : Prop :=
  D.accepted st b ∨ dependencyRefused H D st b

def Effect (H : FGHistoricalReads State Body)
    (D : FGDependencyReads State Body Origin Latest)
    (st : State) (b : Body) (o : Origin) : Prop :=
  D.originAvailable st b o ∧ (D.pending st b o ∨ dependencyResolved H D st b)

/-- The witness relation is supplied by a one-body handler, not by metadata work. -/
structure FGDependencyLeaf (State Body Origin : Type) where
  step : State → Body → Origin → FGDependencyOutcome → State → Prop
  callback : State → Body → Origin → State → Prop
  report : State → Body → Origin → State → Prop
  initial : State
  genesis : Body

/-- Evidence is indexed by actual transition boundaries. Inheritance uses an earlier parent. -/
inductive FGDependencyRefusalEvidence (H : FGHistoricalReads State Body)
    (D : FGDependencyReads State Body Origin Latest)
    (L : FGDependencyLeaf State Body Origin) (state : Nat → State)
    (Direct Inherit : Nat → Body → Origin → Prop) : Nat → Body → Origin → Prop
  | direct (k b o) : Direct k b o → D.validBody b → D.priorChecks (state k) b →
      D.accepted (state k) (H.parent b) → D.conflictsFinal (state k) b →
      L.step (state k) b o .definitiveRefused (state (k + 1)) →
      L.report (state k) b o (state (k + 1)) →
      FGDependencyRefusalEvidence H D L state Direct Inherit (k + 1) b o
  | inherited (k p b o po) : Inherit k b o → p ≤ k → D.validBody b →
      D.originAvailable (state (k + 1)) b o → dependencyRefused H D (state k) (H.parent b) →
      FGDependencyRefusalEvidence H D L state Direct Inherit p (H.parent b) po →
      dependencyRefused H D (state (k + 1)) b →
      FGDependencyRefusalEvidence H D L state Direct Inherit (k + 1) b o

structure FGDependencyStateLaws (H : FGHistoricalReads State Body)
    (D : FGDependencyReads State Body Origin Latest)
    (L : FGDependencyLeaf State Body Origin) : Prop where
  accepted_domain : ∀ st b, D.accepted st b ↔ b ∈ H.acceptedBodies st
  accepted_refused_disjoint : ∀ st b, D.validBody b →
    D.accepted st b → ¬ dependencyRefused H D st b
  pending_valid : ∀ st b o, D.pending st b o → D.validBody b ∧ D.originAvailable st b o
  refused_valid : ∀ st b r pr, D.refused st b r pr → ∃ o,
    D.validBody b ∧ H.root b = r ∧ H.root (H.parent b) = pr ∧
    D.originAvailable st b o
  genesis_accepted : D.accepted L.initial L.genesis
  initial_pending : ∀ b o, ¬ D.pending L.initial b o
  initial_refused : ∀ b r pr, ¬ D.refused L.initial b r pr
  accepted_leaf : ∀ st b, D.accepted st b → b ≠ L.genesis → ∃ a z o,
    L.step a b o .accepted z ∧ ¬ D.accepted a b ∧ D.accepted z b ∧
    D.originAvailable st b o

structure FGDependencyStepLaws (H : FGHistoricalReads State Body)
    (D : FGDependencyReads State Body Origin Latest)
    (L : FGDependencyLeaf State Body Origin)
    (Step : FGDependencyStepKind → V → State → State → Prop)
    (restore : State → Time → State) (emitsSigning : State → State → Prop) : Prop where
  accepted_keep : ∀ k x st st' b, Step k x st st' → D.accepted st b → D.accepted st' b
  refused_keep : ∀ k x st st' b r pr, Step k x st st' →
    D.refused st b r pr → D.refused st' b r pr
  pending_effect : ∀ k x st st' b o, Step k x st st' → D.pending st b o → Effect H D st' b o
  origin_keep : ∀ k x st st' b o, Step k x st st' →
    D.originAvailable st b o → D.originAvailable st' b o
  metadata_fg_eq : ∀ k x st st', Step k x st st' →
    k ≠ .arrival → k ≠ .leafRetry → H.acceptedBlocks st' = H.acceptedBlocks st
  insertion_leaf : ∀ k x st st' b, Step k x st st' →
    D.accepted st' b → ¬ D.accepted st b → ∃ o, L.step st b o .accepted st'
  one_body : ∀ st st' b o result, L.step st b o result st' →
    ∀ c, D.accepted st' c → D.accepted st c ∨ (c = b ∧ result = .accepted)
  restore_exact : ∀ st t,
    H.acceptedBlocks (restore st t) = H.acceptedBlocks st ∧
    H.acceptedBodies (restore st t) = H.acceptedBodies st ∧
    (∀ b r pr, D.refused (restore st t) b r pr ↔ D.refused st b r pr) ∧
    (∀ b o, D.pending (restore st t) b o ↔ D.pending st b o) ∧
    (∀ b o, D.originAvailable (restore st t) b o ↔ D.originAvailable st b o)
  no_signing : ∀ k x st st', Step k x st st' → ¬ emitsSigning st st'

structure FGDependencyArrivalLeafLaws (H : FGHistoricalReads State Body)
    (D : FGDependencyReads State Body Origin Latest)
    (L : FGDependencyLeaf State Body Origin)
    (Arrival : State → Body → Origin → State → Prop)
    (Notify : State → Body → State → Prop) : Prop where
  direct_refusal_iff : ∀ st b o st', (∃ result, L.step st b o result st') →
    (L.step st b o .definitiveRefused st' ↔
    D.validBody b ∧ D.priorChecks st b ∧ D.timely st b ∧ ¬ D.accepted st b ∧
    D.accepted st (H.parent b) ∧ D.conflictsFinal st b ∧
    dependencyRefused H D st' b ∧ D.originAvailable st' b o ∧ L.report st b o st')
  arrival_effect : ∀ st st' b o, Arrival st b o st' → D.validBody b →
    D.timely st b → Effect H D st' b o
  arrival_inherits : ∀ st st' b o, Arrival st b o st' → D.validBody b →
    dependencyRefused H D st (H.parent b) →
    dependencyRefused H D st' b ∧ D.originAvailable st' b o ∧ L.report st b o st'
  arrival_pending : ∀ st st' b o, Arrival st b o st' → D.validBody b → D.timely st b →
    ¬ D.accepted st b → ¬ D.accepted st (H.parent b) →
    ¬ dependencyRefused H D st (H.parent b) → ¬ dependencyRefused H D st b →
    D.pending st' b o
  held_parent_accepts : ∀ st st' b o, (∃ result, L.step st b o result st') →
    (L.step st b o .accepted st' ↔
    D.validBody b ∧ D.priorChecks st b ∧ D.timely st b ∧ ¬ D.accepted st b ∧
    D.accepted st (H.parent b) ∧ ¬ D.conflictsFinal st b ∧ D.accepted st' b ∧
    D.originAvailable st' b o ∧ H.erase b ∈ H.acceptedBlocks st')
  accepted_callback : ∀ st st' b o, L.step st b o .accepted st' → L.callback st b o st'
  callback_only : ∀ st st' b o, L.callback st b o st' →
    L.step st b o .accepted st' ∧ ¬ D.accepted st b ∧ ¬ dependencyRefused H D st' b
  refusal_report : ∀ st st' b o, L.report st b o st' →
    dependencyRefused H D st' b ∧ ¬ D.accepted st' b
  rejected_no_refusal : ∀ st st' b o result, L.step st b o result st' →
    (result = .invalid ∨ result = .future ∨ result = .duplicate ∨ result = .pending) →
    dependencyRefused H D st' b → dependencyRefused H D st b
  notification_resolved : ∀ st st' b, Notify st b st' → dependencyResolved H D st b
  notification_keys : ∀ st st' b, Notify st b st' →
    D.latestKey (D.latest st') = D.latestKey (D.latest st)
  notification_fields : ∀ st st' b i, Notify st b st' →
    (¬ D.accepted st b ∨
      ¬ ∃ slot, D.latestKey (D.latest st) i = some (slot, H.root b)) →
    D.latestCompanion (D.latest st') i = D.latestCompanion (D.latest st) i
  notification_matching : ∀ st st' b i slot, Notify st b st' → D.accepted st b →
    D.latestKey (D.latest st) i = some (slot, H.root b) →
    D.latestCompanion (D.latest st') i = some b
  refused_notification : ∀ st st' b, Notify st b st' → dependencyRefused H D st b →
    D.notified st' b ∧ D.latest st' = D.latest st
  callback_latest : ∀ st st' b, Notify st b st' → D.accepted st b →
    D.notified st' b ∧
    (∀ c, D.matching (D.latest st) c → c = b → D.companionHeld (D.latest st') c) ∧
    (∀ c, c ≠ b → (D.companionHeld (D.latest st') c ↔ D.companionHeld (D.latest st) c))

/-- Enabled work is fixed by retained inputs and outcomes. It is not a queue flag. -/
inductive FGDependencyEnabled (H : FGHistoricalReads State Body)
    (D : FGDependencyReads State Body Origin Latest) (st : State) : Prop
  | inherit (b o) : D.pending st b o → dependencyRefused H D st (H.parent b) →
      ¬ dependencyResolved H D st b → FGDependencyEnabled H D st
  | retry (b o) : D.pending st b o → D.validBody b → D.priorChecks st b →
      D.timely st b → D.accepted st (H.parent b) → ¬ dependencyResolved H D st b →
      FGDependencyEnabled H D st
  | notify (b) : dependencyResolved H D st b → ¬ D.notified st b →
      FGDependencyEnabled H D st
  | companion (b) : D.accepted st b → D.matching (D.latest st) b →
      ¬ D.companionHeld (D.latest st) b → FGDependencyEnabled H D st

def dependencyClosed (H : FGHistoricalReads State Body)
    (D : FGDependencyReads State Body Origin Latest) (st : State) : Prop :=
  ¬ FGDependencyEnabled H D st

/-- Every boundary in a finite segment is a typed transition. -/
inductive FGDependencySteps
    (Step : FGDependencyStepKind → V → State → State → Prop) (x : V) : State → State → Prop
  | refl (st) : FGDependencySteps Step x st st
  | tail {a b c} (k) : FGDependencySteps Step x a b → Step k x b c →
      FGDependencySteps Step x a c

inductive FGDependencyReadKind where
  | fg | proposer | head | ac
  deriving DecidableEq

/-- Each read names its actual entry and consumed cut, not an existential start state. -/
structure FGDependencyReadSite (State : Type) where
  eventIndex : Nat
  kind : FGDependencyReadKind
  entryCut : Nat
  consumedCut : Nat
  consumed : State

/-- A finite named parent path, with genesis as its held base. -/
inductive FGDependencyPath (H : FGHistoricalReads State Body) (genesis : Body) :
    Body → List Body → Prop
  | root : FGDependencyPath H genesis genesis []
  | snoc {parent b path} : FGDependencyPath H genesis parent path → H.parent b = parent →
      FGDependencyPath H genesis b (path ++ [b])

end AvailableChain.FGCompose
end
