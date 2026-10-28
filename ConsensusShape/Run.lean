module
public import ConsensusShape.Compile
public import ConsensusShape.Constants
@[expose] public section

namespace Consensus.Shape
open AvailableChain (Slot)
open Model

abbrev compiled (F : Family) : Model.Family := fun pub => compile (F pub)

abbrev protoOf {V : Type} [Fintype V] (F : Family) (E : Env V) := F (Model.pubOf E)

abbrev Output {V : Type} [Fintype V] (F : Family) (E : Env V) := (protoOf F E).State → Chain

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] {F : Family} {E : Env V}

namespace Run

variable (rho : Model.Run (compiled F) E)

/-- A nonempty validator set has exactly one seat for every slot label. -/
def proposerOf (s : Slot) : V :=
  rho.holder (.inr s) ⟨0, Nat.lt_min.mpr ⟨by decide, Fintype.card_pos⟩⟩

/-- Catch-up is a duration, rather than a coefficient of Δ. -/
def ReadyProposer (c : Time) (s : Slot) : Prop :=
  rho.point.Ready c (proposerOf rho s) ((protoOf F E).proposalTime s)

def Recurrence (c start : Time) (k : Nat) : Prop :=
  ∀ t, start ≤ t → t + (k : Time) * (protoOf F E).slotLen ≤ rho.horizon →
    ∃ s : Slot, t < (protoOf F E).proposalTime s ∧
      (protoOf F E).proposalTime s ≤ t + (k : Time) * (protoOf F E).slotLen ∧
      ReadyProposer rho c s

def readChainIdx (g : Output F E) (v : V) (i : Nat) : Chain :=
  g (rho.stateBefore i v).st.1

/-- The block trace uses exactly the model's environment and event cuts. -/
def chainTrace : Trace V Header where
  point := rho.point
  cuts := rho.events.length
  cutTime := rho.cutTime
  read g := readChainIdx rho (match g with
    | .confirmed => (protoOf F E).confirmed
    | .stable => (protoOf F E).stable
    | .finalized => (protoOf F E).finalized)

abbrev endCut (t : Time) : Nat := (chainTrace rho).endCut t

def readChainOut (g : Output F E) (v : V) (t : Time) : Chain :=
  readChainIdx rho g v (endCut rho t)

def HonestProposal (s : Slot) (h : Header) : Prop :=
  proposerOf rho s ∈ rho.honest ∧ h.slot = s ∧ ∃ cs,
    rho.releases (proposerOf rho s)
      (.mk (.signed (.inr s) ⟨0, Nat.lt_min.mpr ⟨by decide, Fintype.card_pos⟩⟩)
        (.item h) cs)
      ((protoOf F E).proposalTime s)

def InCuts (t₀ : Time) (i : Nat) : Prop :=
  (chainTrace rho).InCuts t₀ i

end Run

end Consensus.Shape
end
