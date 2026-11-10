module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: the width vocabulary

H.1's slow-lock vocabulary at a formation width `w` (a write mode's `width`, for lock rules whose
slow lock of slot `s` reads the saved results of the previous `w − 1` slots):

* `SlowLockAtW w`: `SlowLockAt` with the `w − 1` previous saved results (`SlowLockAt` at `w = k`,
  `slowLockAtW_k`);
* `GoodOriginW w`: `GoodOrigin` with the slow window `[j − w + 1, j]` (`GoodOrigin` at `w = k`,
  `goodOriginW_k`);
* `exists_unpolluted_labelW`: an asynchrony of length at most `(4w − 5)Δ` leaves a slot start
  outside its pollution window among every `w` consecutive labels (the arithmetic of the outage
  route's `exists_unpolluted_label`, at `w`).

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

/-- **A good origin of width `w`** of label `j` on `B`: an honest fast lock write of slot `j ≥ r`,
or an honest slow lock write of width `w` of slot `j` whose window `[j − w + 1, j]` is `≥ r`. -/
def GoodOriginW (w : Nat) (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (g : Time)
    (B : Blk sp.n FGP) (j : Nat) : Prop :=
  (∃ x ∈ H, ∃ i CV, FastLockAt tr x i j B CV ∧ gbar g + 4 * sp.Δ ≤ sp.ts j) ∨
  (∃ x ∈ H, ∃ i, SlowLockAtW w tr x i j B ∧ gbar g + 4 * sp.Δ ≤ sp.ts ((j : Int) - w + 1))

theorem goodOriginW_iff {w : Nat} {tr : SATrace sp FGP ro} {H : Set (Fin sp.n)} {g : Time}
    {B : Blk sp.n FGP} {j : Nat} : GoodOriginW w tr H g B j ↔
      ((∃ x ∈ H, ∃ i CV, FastLockAt tr x i j B CV ∧ gbar g + 4 * sp.Δ ≤ sp.ts j) ∨
        (∃ x ∈ H, ∃ i, SlowLockAtW w tr x i j B ∧
          gbar g + 4 * sp.Δ ≤ sp.ts ((j : Int) - w + 1))) :=
  Iff.rfl

theorem goodOriginW_k {tr : SATrace sp FGP ro} {H : Set (Fin sp.n)} {g : Time}
    {B : Blk sp.n FGP} {j : Nat} : GoodOriginW sp.k tr H g B j ↔ GoodOrigin tr H g B j := by
  rw [goodOriginW_iff, goodOrigin_iff]
  rfl

/-- **An unpolluted label among every `w` consecutive ones**: when the asynchrony `[start, stop)`
lasts at most `(4w − 5)Δ`, among the labels `s − w + 1, …, s` there is one whose slot start
`t_m` has its vote window before `start` (`t_m + 2Δ ≤ start`) or after `stop` (`stop ≤ t_m + Δ`):
the polluted slot starts lie in the open interval `(start − 2Δ, stop − Δ)`, of length at most
`(4w − 4)Δ`, so at most `w − 1` of them. -/
theorem exists_unpolluted_labelW (sp : SAParams) {w : Nat} (hw : 2 ≤ w) {start stop : Time}
    (hgap : stop - start ≤ (4 * (w : Time) - 5) * sp.Δ) (s : Int) :
    ∃ m : Int, s - (w : Int) < m ∧ m ≤ s ∧
      (sp.ts m + 2 * sp.Δ ≤ start ∨ stop ≤ sp.ts m + sp.Δ) := by
  have hw' : (2 : Int) ≤ w := by exact_mod_cast hw
  by_contra hn
  have hfirst : start < sp.ts (s - w + 1) + 2 * sp.Δ := by
    by_contra h
    exact hn ⟨s - w + 1, by omega, by omega, Or.inl (le_of_not_gt h)⟩
  have hlast : sp.ts s + sp.Δ < stop := by
    by_contra h
    exact hn ⟨s, by omega, le_rfl, Or.inr (le_of_not_gt h)⟩
  simp only [SAParams.ts] at hfirst hlast
  linarith

end Consensus.Goldilocks.SA

end
