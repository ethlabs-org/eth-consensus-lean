module
public import ConsensusShape.Compile
public import ConsensusShape.Constants
@[expose] public section

namespace Consensus.Shape
open AvailableChain (Slot Time)
open AvailableChain.Generic (Env)
open Model

abbrev compiled (F : Family) : Model.Family := fun pub => compile (F pub)

abbrev protoOf {V : Type} [Fintype V] (F : Family) (E : Env V) := F (Model.pubOf E)

abbrev Output {V : Type} [Fintype V] (F : Family) (E : Env V) := (protoOf F E).State → Chain

variable {V : Type} [Fintype V] [DecidableEq V] {F : Family} {E : Env V}

namespace Run

variable (rho : Model.Run (compiled F) E)

def proposerOf (s : Slot) : V := rho.holder (.inr s) ⟨0, by exact Nat.zero_lt_succ 0⟩


def ShapeValid : Prop := rho.ExecutionValid

/-- Catch-up is a duration, rather than a coefficient of Δ. -/
def ReadyProposer (c : Time) (s : Slot) : Prop :=
  rho.Ready c (proposerOf rho s) ((protoOf F E).proposalTime s)

def Recurrence (c start : Time) (k : Nat) : Prop :=
  ∀ t, start ≤ t → t + (k : Time) * (protoOf F E).slotLen ≤ rho.horizon →
    ∃ s : Slot, t < (protoOf F E).proposalTime s ∧
      (protoOf F E).proposalTime s ≤ t + (k : Time) * (protoOf F E).slotLen ∧
      ReadyProposer rho c s

def readChainIdx (g : Output F E) (v : V) (i : Nat) : Chain :=
  g (rho.stateBefore i v).st.1

/-- Use exactly the L0 end cut, also on malformed runs. -/
def endCut (t : Time) : Nat := (Model.sysOf (compiled F) V).endCut ⟨E, rho⟩ t

def readChainOut (g : Output F E) (v : V) (t : Time) : Chain :=
  readChainIdx rho g v (endCut rho t)

def HonestProposal (s : Slot) (h : Header) : Prop :=
  proposerOf rho s ∈ rho.honest ∧ h.slot = s ∧ ∃ cs,
    rho.releases (proposerOf rho s)
      (.mk (.signed (.inr s) ⟨0, by exact Nat.zero_lt_succ 0⟩) (.item h) cs)
      ((protoOf F E).proposalTime s)

def InCuts (t₀ : Time) (i : Nat) : Prop :=
  endCut rho (t₀ - 1) < i ∧ i ≤ rho.events.length

end Run

end Consensus.Shape
end
