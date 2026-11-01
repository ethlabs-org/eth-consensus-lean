module
public import AvailableChainFGCompose.Statements.EventReads -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.FGCompose

structure FGTiming where
  delta : Time
  roundSlots : Nat
  proposal : Slot → Time
  vote : Slot → Time
  early : Slot → Time
  freeze : Slot → Time
  release : Slot → Time
  gate : Slot → Time
  action : Nat → Time

structure FGTimingLaws (T : FGTiming) : Prop where
  delta_pos : 0 < T.delta
  rounds : 2 ≤ T.roundSlots
  proposal_eq : ∀ s, T.proposal s = 4 * (s : Time) * T.delta
  vote_eq : ∀ s, T.vote s = T.proposal s + T.delta
  early_eq : ∀ s, T.early s = T.proposal s + 2 * T.delta
  freeze_eq : ∀ s, T.freeze s = T.proposal s + 3 * T.delta
  release_eq : ∀ s, T.release s = T.proposal s + 5 * T.delta
  gate_eq : ∀ s, T.gate s = T.proposal s + 6 * T.delta
  action_eq : ∀ r, T.action r = T.gate (r * T.roundSlots)

def slotStartZ (T : FGTiming) (s : Int) : Time := 4 * T.delta * s
def slotAt (T : FGTiming) (t : Time) : Slot := (t / (4 * T.delta)).toNat

end AvailableChain.FGCompose
end
