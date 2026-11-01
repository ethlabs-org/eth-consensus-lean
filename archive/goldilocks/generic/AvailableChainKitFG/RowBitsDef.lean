module
public import AvailableChainSimplexFG.ChainState

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

/-- The three row bit sets in the FG carrier.
DC: ChainState/Chain.lean:125,136,149; same: carrier adapter of the step cores. -/
inductive ChainBit
  | target
  | progress
  | finality
  deriving DecidableEq

/-- Select a row bit set.
DC: ChainState/Chain.lean:125,136,149; same: carrier adapter of the step cores. -/
def chainBits {V : Type} (kind : ChainBit)
    (σ : ChainState V) : Finset V :=
  match kind with
  | .target => σ.target_participation
  | .progress => σ.progress
  | .finality => σ.finalize

/-- The complete defining equation.
DC: ChainState/Chain.lean:125,136,149; same: carrier adapter of the step cores. -/
theorem chainBits_def {V : Type} (kind : ChainBit)
    (σ : ChainState V) :
    chainBits kind σ =
      (match kind with
       | .target => σ.target_participation
       | .progress => σ.progress
       | .finality => σ.finalize) := by rfl

/-- The keys whose equality excludes a reset on a derived chain.
DC: none; derived carrier key (no DC counterpart); GLY r3.19 G20.
Finality consumption keeps finalize, so h_F is not a key. -/
def sameBitState {V : Type} [RowCodec V]
    (kind : ChainBit) (σ τ : ChainState V) : Prop :=
  match kind with
  | .target | .progress =>
      σ.h = τ.h ∧ σ.T_h.root = τ.T_h.root
  | .finality =>
      σ.h_j = τ.h_j ∧ σ.J.root = τ.J.root

/-- The complete defining equation.
DC: none; derived carrier key (no DC counterpart); GLY r3.19 G20.
Finality consumption keeps finalize, so h_F is not a key. -/
theorem sameBitState_def {V : Type} [RowCodec V]
    (kind : ChainBit) (σ τ : ChainState V) :
    sameBitState kind σ τ =
      (match kind with
       | .target | .progress =>
           σ.h = τ.h ∧ σ.T_h.root = τ.T_h.root
       | .finality =>
           σ.h_j = τ.h_j ∧ σ.J.root = τ.J.root) := by rfl

/-- A sufficient matching condition for a row to set its signer bit.
DC: ChainState/Chain.lean:125,136,149; same: carrier adapter of the step cores.
The FG model binds timeout progress to the entry root (Certificates.lean:95–96). -/
def rowMatchesBit {V : Type} [DecidableEq V] [RowCodec V]
    (kind : ChainBit) (σ : ChainState V) (a : Row V) : Prop :=
  match kind with
  | .target =>
      a.height_pair = .vote σ.h σ.T_h.root false
  | .progress =>
      a.height_pair.matchesEntry σ.h σ.T_h.root = true
  | .finality =>
      σ.h_F < σ.h_j ∧
        a.finality_pair = some ⟨σ.h_j, σ.J.root⟩

/-- The complete defining equation.
DC: ChainState/Chain.lean:125,136,149; same: carrier adapter of the step cores.
The FG model binds timeout progress to the entry root (Certificates.lean:95–96). -/
theorem rowMatchesBit_def {V : Type} [DecidableEq V] [RowCodec V]
    (kind : ChainBit) (σ : ChainState V) (a : Row V) :
    rowMatchesBit kind σ a =
      (match kind with
       | .target =>
           a.height_pair = .vote σ.h σ.T_h.root false
       | .progress =>
           a.height_pair.matchesEntry σ.h σ.T_h.root = true
       | .finality =>
           σ.h_F < σ.h_j ∧
             a.finality_pair = some ⟨σ.h_j, σ.J.root⟩) := by rfl

/-- Bits persist between comparable chain states with equal keys.
DC: none; derived carrier lemma; witnesses MatchingProgress.lean:147,
FinalityCertificates.lean:133. GLY r3.19 G20. -/
def BitPersistStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig)
    (kind : ChainBit) (B W : FGBlock V),
    FGBlock.Preceq B W →
    sameBitState kind (derive E cfg B) (derive E cfg W) →
    chainBits kind (derive E cfg B) ⊆
      chainBits kind (derive E cfg W)

/-- The complete defining equation.
DC: none; derived carrier lemma; witnesses MatchingProgress.lean:147,
FinalityCertificates.lean:133. GLY r3.19 G20. -/
theorem BitPersistStatement_def :
    BitPersistStatement =
      (∀ {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
        (E : Electorate V) (cfg : FGConfig)
        (kind : ChainBit) (B W : FGBlock V),
        FGBlock.Preceq B W →
        sameBitState kind (derive E cfg B) (derive E cfg W) →
        chainBits kind (derive E cfg B) ⊆
          chainBits kind (derive E cfg W)) := by rfl

/-- A matching row occurrence sets a bit if the chain keeps its key.
DC: none; derived carrier lemma; witnesses MatchingProgress.lean:147,
FinalityCertificates.lean:133. GLY r3.19 G20.
This is a forward implication only; it does not identify a row from a bit. -/
def BitFromRowStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig)
    (kind : ChainBit) (parent W : FGBlock V)
    (slot : Slot) (r_slot : BlockId) (body : Nat) (rows : List (Row V)) (a : Row V),
    a ∈ rows →
    FGBlock.Preceq (.node parent slot r_slot body rows) W →
    rowMatchesBit kind (derive E cfg parent) a →
    sameBitState kind (derive E cfg parent) (derive E cfg W) →
    a.signer ∈ chainBits kind (derive E cfg W)

/-- The complete defining equation.
DC: none; derived carrier lemma; witnesses MatchingProgress.lean:147,
FinalityCertificates.lean:133. GLY r3.19 G20.
This is a forward implication only; it does not identify a row from a bit. -/
theorem BitFromRowStatement_def :
    BitFromRowStatement =
      (∀ {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
        (E : Electorate V) (cfg : FGConfig)
        (kind : ChainBit) (parent W : FGBlock V)
        (slot : Slot) (r_slot : BlockId) (body : Nat) (rows : List (Row V)) (a : Row V),
        a ∈ rows →
        FGBlock.Preceq (.node parent slot r_slot body rows) W →
        rowMatchesBit kind (derive E cfg parent) a →
        sameBitState kind (derive E cfg parent) (derive E cfg W) →
        a.signer ∈ chainBits kind (derive E cfg W)) := by rfl

end AvailableChain.KitFG
end
