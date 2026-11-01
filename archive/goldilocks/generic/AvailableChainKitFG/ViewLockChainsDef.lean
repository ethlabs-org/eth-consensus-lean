module
public import AvailableChainKitFG.RootScopeDef
public import AvailableChainKitFG.ViewLock
public import AvailableChainSimplexFG.Evidence

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

/-- A carrier's finalized checkpoint locks each chain in a finite view.
DC: ChainState/FinalityComparison.lean:50–56; same: strict height and finalized ancestry.
The finite view applies DC's chain comparison to each member. The agreement
premise is local to the compared chains, so no run premises are required.
INTENTIONAL: root is a function of the content; record K/Accountable:15–18, GLY:57–58. -/
def ViewLockOfChainsStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig)
    (K Fb : FGBlock V) (vw : View V) (θ : Nat),
    (∀ W ∈ vw, RootInjectiveOn K W) →
    (derive E cfg K).F = Fb →
    (derive E cfg K).h_F ≤ θ →
    (∀ W ∈ vw,
      ¬ HasSlashableWeightBetween E (chainRows K) (chainRows W)) →
    ViewLock E cfg θ Fb vw

/-- The complete argument list of the local chain comparison.
DC: ChainState/FinalityComparison.lean:50–56; same: strict height and finalized ancestry. -/
theorem ViewLockOfChainsStatement_def :
    ViewLockOfChainsStatement =
      (∀ {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
        (E : Electorate V) (cfg : FGConfig)
        (K Fb : FGBlock V) (vw : View V) (θ : Nat),
    (∀ W ∈ vw, RootInjectiveOn K W) →
        (derive E cfg K).F = Fb →
        (derive E cfg K).h_F ≤ θ →
        (∀ W ∈ vw,
          ¬ HasSlashableWeightBetween E (chainRows K) (chainRows W)) →
        ViewLock E cfg θ Fb vw) := by rfl

/-- The fault weight bound and honest rows exclude slashable chain evidence.
DC: ChainState/FinalityComparison.lean:50–56; same: strict height and finalized ancestry.
This form supplies the local agreement premise from the weight bound and
only the `noSlash` content of `HonestRows`; emission and height caps are unused.
INTENTIONAL: root is a function of the content; record K/Accountable:15–18, GLY:57–58. -/
def ViewLockOfHonestChainsStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig)
    (K Fb : FGBlock V) (vw : View V) (θ : Nat)
    (faulty : Finset V),
    (∀ W ∈ vw, RootInjectiveOn K W) →
    (derive E cfg K).F = Fb →
    (derive E cfg K).h_F ≤ θ →
    E.weightOf faulty + E.totalWeight < 2 * E.q →
    (∀ W ∈ vw, ∀ a ∈ chainRows K, ∀ b ∈ chainRows W,
      a.signer ∉ faulty → ¬ Slashable a b) →
    ViewLock E cfg θ Fb vw

/-- The complete argument list of the fault weight form.
DC: ChainState/FinalityComparison.lean:50–56; same: strict height and finalized ancestry. -/
theorem ViewLockOfHonestChainsStatement_def :
    ViewLockOfHonestChainsStatement =
      (∀ {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
        (E : Electorate V) (cfg : FGConfig)
        (K Fb : FGBlock V) (vw : View V) (θ : Nat)
        (faulty : Finset V),
    (∀ W ∈ vw, RootInjectiveOn K W) →
        (derive E cfg K).F = Fb →
        (derive E cfg K).h_F ≤ θ →
        E.weightOf faulty + E.totalWeight < 2 * E.q →
        (∀ W ∈ vw, ∀ a ∈ chainRows K, ∀ b ∈ chainRows W,
          a.signer ∉ faulty → ¬ Slashable a b) →
        ViewLock E cfg θ Fb vw) := by rfl

end AvailableChain.KitFG
end
