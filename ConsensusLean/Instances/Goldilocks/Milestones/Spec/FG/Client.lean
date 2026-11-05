module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Client

@[expose] public section

/-! # Goldilocks milestone vocabulary: client runs

The part of `Spec/FG/Client` that no Challenge statement reaches (`docs/decisions.md`
§"Trusted surface and Challenge scope"): the milestone statements use it; it is not on the trusted
surface. Names and bodies are unchanged.

`Record.run`: the record and the attestations sent, from a sequence of entry states. -/

namespace Consensus.Goldilocks.FG

namespace Record

/-- A client run: the record and the attestations sent, from a sequence of entry
states of sources (in the order of the FG updates). -/
def run {n : Nat} (v : Fin n) : Record → List (ChainState n) → Record × List (Att n)
  | Λ, [] => (Λ, [])
  | Λ, σe :: rest =>
      match Λ.createAtt v σe with
      | none => Record.run v Λ rest
      | some (a, Λ') => let r := Record.run v Λ' rest; (r.1, a :: r.2)

end Record

end Consensus.Goldilocks.FG

end
