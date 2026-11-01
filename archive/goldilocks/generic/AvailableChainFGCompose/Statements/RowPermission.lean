module
public import AvailableChainFGCompose.Statements.Channels
public import AvailableChainFGCompose.Statements.SafetyClient -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In : Type} {P : V2.ProtocolSpecD In} {n : Nat} {Wire : Type}

/-- The durable record agrees with every earlier target and timeout. -/
structure FGRowRecordHistory (Λ : RecordOnce) : Prop where
  invariant : ∀ h T, Λ.lock h = some T →
    Λ.timeout h = false ∧ (Λ.target h = none ∨ Λ.target h = some T)
  sent_history : ∀ h T timeout fp, (.vote h T timeout, fp) ∈ Λ.sent →
    (timeout = false → Λ.target h = some T) ∧ (timeout = true → Λ.timeout h = true)

/-- A decoded emitted object has the same wire, signer, and named entry. -/
structure FGRowPermissionWireLaws (S : FGSafetyReads P n Wire)
    (entry : Wire → Option (Height × BlockId)) : Prop where
  decoded_wire : ∀ o u, S.decodeObject o = some u →
    ∃ a, S.encode a = o ∧ S.decode a = some u ∧ entry a = namedEntry u.height_pair

/-- Permission is a lock condition, with the selected source at the same client read. -/
structure FGRowPermissionInputs (S : FGSafetyReads P n Wire)
    (H : FGHeightView (Fin n)) (nd : P.State) (C : FGBlock (Fin n)) : Prop where
  source_eq : (S.inputs nd).1 = some C
  permitted_lock :
    own_lock (S.record nd).toRecord (H C).h
        (finality_pair (S.record nd).toRecord (S.inputs nd).2) = none ∨
      own_lock (S.record nd).toRecord (H C).h
        (finality_pair (S.record nd).toRecord (S.inputs nd).2) = some (H C).T_h.root

end AvailableChain.FGCompose
end
