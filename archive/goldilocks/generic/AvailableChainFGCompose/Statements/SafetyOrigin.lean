module
public import AvailableChainFGCompose.Statements.SafetyStore -- shake: keep (frozen record)

@[expose] public section

/-! Origin laws for a protocol whose delivery event can admit several bodies: the
delivered one and bodies that were pending before the event. They replace
`FGSafetyStoreLaws.process_new`, which allows one new block per delivery, and that block
is the delivered object. PROVISIONAL, as the other safety contracts. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In : Type} {P : V2.ProtocolSpecD In}
variable {n : Nat} {Base Proposal Wire : Type}

/-- Each block that a delivery adds to the store has an origin object with its erasure and
its rows. The origin is the delivered object, or an object that was pending before the
delivery. -/
def FGProcessOrigin (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
    (Good : P.State → Prop) (pending : P.State → P.Object → Prop) : Prop :=
  ∀ nd o B, Good nd →
    B ∈ (R.core (P.process nd o)).fg.TF → B ∉ (R.core nd).fg.TF →
    ∃ origin, (origin = o ∨ pending nd origin) ∧
      S.proposalErase origin = some (R.erase B) ∧
      B.rows = (S.proposalRows origin).filterMap S.decode

theorem FGProcessOrigin_def (R : FGCoreReads P n Base Proposal Wire)
    (S : FGSafetyReads P n Wire) (Good : P.State → Prop)
    (pending : P.State → P.Object → Prop) :
    FGProcessOrigin R S Good pending =
      (∀ nd o B, Good nd →
        B ∈ (R.core (P.process nd o)).fg.TF → B ∉ (R.core nd).fg.TF →
        ∃ origin, (origin = o ∨ pending nd origin) ∧
          S.proposalErase origin = some (R.erase B) ∧
          B.rows = (S.proposalRows origin).filterMap S.decode) := rfl

/-- A pending object comes from a delivery only. No object is pending at the start. A
delivery adds at most the delivered object. The other operations add none. -/
def FGPendingOrigin (Good : P.State → Prop) (pending : P.State → P.Object → Prop) : Prop :=
  (∀ o, ¬ pending P.init o) ∧
  (∀ nd t o, Good nd → pending (P.clock nd t) o → pending nd o) ∧
  (∀ nd o q, Good nd → pending (P.process nd o) q → pending nd q ∨ q = o) ∧
  (∀ nd o q, Good nd → pending (P.recordOwn nd o) q → pending nd q) ∧
  (∀ nd t o, Good nd → pending (P.restore (P.durable nd) t) o → pending nd o)

theorem FGPendingOrigin_def (Good : P.State → Prop) (pending : P.State → P.Object → Prop) :
    FGPendingOrigin Good pending =
      ((∀ o, ¬ pending P.init o) ∧
      (∀ nd t o, Good nd → pending (P.clock nd t) o → pending nd o) ∧
      (∀ nd o q, Good nd → pending (P.process nd o) q → pending nd q ∨ q = o) ∧
      (∀ nd o q, Good nd → pending (P.recordOwn nd o) q → pending nd q) ∧
      (∀ nd t o, Good nd → pending (P.restore (P.durable nd) t) o → pending nd o)) := rfl

/-- `FGSafetyStoreLaws` without `process_new`, with the two origin laws. The frozen record
implies this one with no pending object (`safetyStoreOriginLaws_of_storeLaws`). -/
structure FGSafetyStoreOriginLaws (R : FGCoreReads P n Base Proposal Wire)
    (S : FGSafetyReads P n Wire) (H : FGHeightView (Fin n))
    (f : FGFinalityView (Fin n)) (Good : P.State → Prop)
    (pending : P.State → P.Object → Prop) : Prop where
  initial_good : Good P.init
  clock_good : ∀ nd t, Good nd → Good (P.clock nd t)
  process_good : ∀ nd o, Good nd → Good (P.process nd o)
  own_good : ∀ nd o, Good nd → Good (P.recordOwn nd o)
  restart_good : ∀ nd t, Good nd → Good (P.restore (P.durable nd) t)
  invariant : ∀ nd, Good nd → FGStoreInvariant H f (R.core nd).fg
  initial_tf : ∀ B ∈ (R.core P.init).fg.TF, B = .genesis
  restart_tf : ∀ nd t B, Good nd →
    B ∈ (R.core (P.restore (P.durable nd) t)).fg.TF → B ∈ (R.core nd).fg.TF
  process_origin : FGProcessOrigin R S Good pending
  pending_origin : FGPendingOrigin Good pending

end AvailableChain.FGCompose
end
