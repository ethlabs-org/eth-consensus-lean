module
public import AvailableChainGeneric.Statements.Pure.Schedule

@[expose] public section

namespace AvailableChain.Gen.Pure

/-! Blueprint 22:213–227, 1371–1448. The carrier offset and receipt tail are parameters.
DC class: INTENTIONAL; DC uses continuous strong windows, not these round samples. -/

def FGoodE_W (H : Slot → Prop) (R κ r : Nat) : Prop :=
  H (r * R) ∧ H ((r + 1) * R) ∧
    (∃ c : Slot, (r + 1) * R + κ ≤ c ∧ c ≤ (r + 2) * R ∧ H c) ∧
    H ((r + 2) * R + κ)

def FGood4_W (H : Slot → Prop) (R κ r : Nat) : Prop :=
  FGoodE_W H R κ r ∧ H ((r + 1) * R + κ)

def Tail_W (H : Slot → Prop) (R κ r : Nat) : Prop :=
  H (r * R) ∧
    (∃ c : Slot, r * R + κ ≤ c ∧ c ≤ (r + 1) * R ∧ H c) ∧
    H ((r + 1) * R + κ)

def RecFE_W (H : Slot → Prop) (R κ : Nat) (P Δ β GST horizon : Time) (g : Nat) : Prop :=
  1 ≤ g ∧ ∀ q : Nat, 1 ≤ q → GST ≤ (q : Time) * P →
    ((q : Time) + g + 1) * P + β + Δ ≤ horizon →
    ∃ r, InWindow q g r ∧ FGoodE_W H R κ r

def RecF4_W (H : Slot → Prop) (R κ : Nat) (P Δ β GST horizon : Time) (g : Nat) : Prop :=
  1 ≤ g ∧ ∀ q : Nat, 1 ≤ q → GST ≤ (q : Time) * P →
    ((q : Time) + g + 1) * P + β + Δ ≤ horizon →
    ∃ r, InWindow q g r ∧ FGood4_W H R κ r

theorem FGoodE_W_def (H : Slot → Prop) (R κ r : Nat) :
    FGoodE_W H R κ r =
      (H (r * R) ∧ H ((r + 1) * R) ∧
    (∃ c : Slot, (r + 1) * R + κ ≤ c ∧ c ≤ (r + 2) * R ∧ H c) ∧
    H ((r + 2) * R + κ)) := by rfl

theorem FGood4_W_def (H : Slot → Prop) (R κ r : Nat) :
    FGood4_W H R κ r =
      (FGoodE_W H R κ r ∧ H ((r + 1) * R + κ)) := by rfl

theorem Tail_W_def (H : Slot → Prop) (R κ r : Nat) :
    Tail_W H R κ r =
      (H (r * R) ∧
    (∃ c : Slot, r * R + κ ≤ c ∧ c ≤ (r + 1) * R ∧ H c) ∧
    H ((r + 1) * R + κ)) := by rfl

theorem RecFE_W_def (H : Slot → Prop) (R κ : Nat) (P Δ β GST horizon : Time) (g : Nat) :
    RecFE_W H R κ P Δ β GST horizon g =
      (1 ≤ g ∧ ∀ q : Nat, 1 ≤ q → GST ≤ (q : Time) * P →
    ((q : Time) + g + 1) * P + β + Δ ≤ horizon →
    ∃ r, InWindow q g r ∧ FGoodE_W H R κ r) := by rfl

theorem RecF4_W_def (H : Slot → Prop) (R κ : Nat) (P Δ β GST horizon : Time) (g : Nat) :
    RecF4_W H R κ P Δ β GST horizon g =
      (1 ≤ g ∧ ∀ q : Nat, 1 ≤ q → GST ≤ (q : Time) * P →
    ((q : Time) + g + 1) * P + β + Δ ≤ horizon →
    ∃ r, InWindow q g r ∧ FGood4_W H R κ r) := by rfl

end AvailableChain.Gen.Pure
