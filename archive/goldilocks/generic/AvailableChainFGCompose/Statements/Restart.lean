module
public import AvailableChainFGCompose.Statements.CoreReads

@[expose] public section

namespace AvailableChain.FGCompose
variable {In : Type} {P : V2.ProtocolSpecD In}
variable {n : Nat} {Base Proposal Wire : Type}

/-- Restore retains every block in the accepted FG tree. -/
structure FGTreeKeepLaws (R : FGCoreReads P n Base Proposal Wire) : Prop where
  restart_keep : ∀ nd t,
    (R.core nd).fg.TF ⊆ (R.core (P.restore (P.durable nd) t)).fg.TF

/-- Restore preserves the accepted FG tree exactly, including at tick time. -/
structure FGTreeRestoreLaws (R : FGCoreReads P n Base Proposal Wire) : Prop where
  restart_eq : ∀ nd t,
    (R.core (P.restore (P.durable nd) t)).fg.TF = (R.core nd).fg.TF

end AvailableChain.FGCompose
end
