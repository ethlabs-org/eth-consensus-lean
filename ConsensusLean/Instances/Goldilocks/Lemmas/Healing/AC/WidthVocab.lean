module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting

public section

/-! # Goldilocks Healing: the width vocabulary

H.1's slow-lock vocabulary at a formation width `w` (a write mode's `width`, for lock rules whose
slow lock of slot `s` reads the saved results of the previous `w − 1` slots):

* `SlowLockAtW w`: `SlowLockAt` with the `w − 1` previous saved results (`SlowLockAt` at `w = k`,
  `slowLockAtW_k`).

This is vocabulary only: H.1 at a width below `k` is not stated here (its transfer step needs the
old slow locks of the formation window to be compatible, which is not proved). -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-- **A slow lock of width `w`** of slot `s` on `B`, written at cut `i` of `x`: the update of slot
`s` returns `C`, and `B` is the deepest block of `C`'s path that conflicts with no live lock and
has the `w − 1` previous saved results as descendants. -/
def SlowLockAtW (w : Nat) (tr : SATrace sp FGP ro) (x : Fin sp.n) (i s : Nat)
    (B : Blk sp.n FGP) : Prop :=
  ∃ ℓ C, UpdateAt tr x i s ℓ ∧ getConfirmation sp (tr.state x i) ℓ.frame s = some C ∧
    deepest ℓ.frame {X | X ∈ confirmationPath sp ℓ.frame C ∧
      ¬ conflictsWithLock sp (tr.state x i).locks ℓ.frame (tr.time i) X ∧
      ∀ j : Int, (s : Int) - w < j → j < s →
        ∃ S ∈ ℓ.frame.tree, (tr.state x i).saved j = some S.root ∧ ℓ.frame.Anc X S} =
      some B

theorem slowLockAtW_k {tr : SATrace sp FGP ro} {x : Fin sp.n} {i s : Nat} {B : Blk sp.n FGP} :
    SlowLockAtW sp.k tr x i s B ↔ SlowLockAt tr x i s B :=
  Iff.rfl

theorem slowLockAtW_iff {w : Nat} {tr : SATrace sp FGP ro} {x : Fin sp.n} {i s : Nat}
    {B : Blk sp.n FGP} : SlowLockAtW w tr x i s B ↔
      ∃ ℓ C, UpdateAt tr x i s ℓ ∧ getConfirmation sp (tr.state x i) ℓ.frame s = some C ∧
        deepest ℓ.frame {X | X ∈ confirmationPath sp ℓ.frame C ∧
          ¬ conflictsWithLock sp (tr.state x i).locks ℓ.frame (tr.time i) X ∧
          ∀ j : Int, (s : Int) - w < j → j < s →
            ∃ S ∈ ℓ.frame.tree, (tr.state x i).saved j = some S.root ∧ ℓ.frame.Anc X S} =
          some B :=
  Iff.rfl

end Consensus.Goldilocks.SA

end
