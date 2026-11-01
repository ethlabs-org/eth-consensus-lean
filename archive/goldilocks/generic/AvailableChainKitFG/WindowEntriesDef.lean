module
public import AvailableChainSimplexFG.Window

@[expose] public section

namespace AvailableChain.KitFG.Window

open AvailableChain.SimplexFG hiding derive
open AvailableChain.SimplexFG.Window

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- [f07w plan §1.1; bp 01:421–424] The window key `(j, U)` is retained at `B`: some
entry of `σ(B) = derive E cfg K B` has certificate height `j` and block `U`. The key is
`(j, U)`, not `U` alone and not the latest `(h_j, J)`. -/
def RetainedW (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (B : FGBlock V) (j : Height) (U : FGBlock V) : Prop :=
  ∃ e ∈ (derive E cfg K B).W, e.j = j ∧ e.X = U

theorem RetainedW_def (E : Electorate V) (cfg : FGConfig) (K : Nat) (B : FGBlock V) (j : Height)
    (U : FGBlock V) :
    RetainedW E cfg K B j U = ∃ e ∈ (derive E cfg K B).W, e.j = j ∧ e.X = U := rfl

/-- [f07w plan §1.1; bp 01:405–409] The window key `(j, U)` is covered at `B`:
`j ≤ h_F` and `U ⪯ F` in `σ(B) = derive E cfg K B`. -/
def CoveredW (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (B : FGBlock V) (j : Height) (U : FGBlock V) : Prop :=
  j ≤ (derive E cfg K B).h_F ∧ FGBlock.Preceq U (derive E cfg K B).F

theorem CoveredW_def (E : Electorate V) (cfg : FGConfig) (K : Nat) (B : FGBlock V) (j : Height)
    (U : FGBlock V) :
    CoveredW E cfg K B j U =
      (j ≤ (derive E cfg K B).h_F ∧ FGBlock.Preceq U (derive E cfg K B).F) := rfl

/-- An identity bit in the retained entry with the exact key `(j, U)`. -/
def EntryBitW (E : Electorate V) (cfg : FGConfig) (K : Nat) (B : FGBlock V) (j : Height)
    (U : FGBlock V) (i : V) : Prop :=
  ∃ e ∈ (derive E cfg K B).W, e.j = j ∧ e.X = U ∧ i ∈ e.Q

theorem EntryBitW_def (E : Electorate V) (cfg : FGConfig) (K : Nat) (B : FGBlock V) (j : Height)
    (U : FGBlock V) (i : V) :
    EntryBitW E cfg K B j U i =
      (∃ e ∈ (derive E cfg K B).W, e.j = j ∧ e.X = U ∧ i ∈ e.Q) := rfl

/-- Add the signer bit to the entry with the exact finality key. -/
def window_addBit (a : Row V) (e : Entry V) : Entry V :=
  if a.finality_pair = some ⟨e.j, e.X.root⟩ then
    { e with Q := insert a.signer e.Q } else e

omit [Fintype V] in
theorem window_addBit_def (a : Row V) (e : Entry V) :
    window_addBit a e =
      if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e := rfl

end AvailableChain.KitFG.Window
end
