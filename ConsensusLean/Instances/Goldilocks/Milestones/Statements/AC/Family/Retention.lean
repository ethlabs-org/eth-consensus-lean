module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Family

/-! # Conditional lock-floor preservation and read-point consequences -/

@[expose] public section

namespace Consensus.Goldilocks.SA.FamilyFacts

variable {sp : SAParams} {FGP S M : Type} {ro : ReplayOrder sp FGP}

/-- An unexpired lock witness at a specified slot, above the protected block. -/
def LockFloor (L : Set Lock) (Φ : Frm sp.n FGP) (B₀ : Blk sp.n FGP)
    (j m : Nat) : Prop :=
  ∃ l ∈ L, l.slot = j ∧ m ≤ l.expiry ∧
    ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B

variable {A : SAOperations sp FGP S M} (F : SAFamily A ro) (tr : ACTrace A.toAC)
  (H : Set (Fin sp.n))

/-- Conditional floor preservation and read-point consequences. Sufficient conditions
for K are supplied separately; no parent-target or intermediate-release field is assumed. -/
structure Retention
    (K : Fin sp.n → Nat → ACLabel (goldilocksSA sp FGP ro) → Blk sp.n FGP → Prop) : Prop where
  step : ∀ x ∈ H, ∀ i ℓ B j m, (F.proj tr).CallAt x i ℓ →
    LockFloor ((F.proj tr).state x i).locks ℓ.frame B j m →
    sp.slot ((F.proj tr).time i) ≤ m → B ∈ ℓ.frame.tree →
    ℓ.frame.viableAncestor B = B →
    ((sp.slot ((F.proj tr).time i) : Int) - 1 ≤ j ∨ K x i ℓ B) →
    LockFloor ((F.proj tr).post i).locks ℓ.frame B j m
  read : ∀ x ∈ H, ∀ i ℓ e B (j m : Nat), CastAt (F.proj tr) x i ℓ e →
    B ∈ ℓ.frame.tree → ℓ.frame.viableAncestor B = B →
    sp.slot ((F.proj tr).time i) ≤ m →
    ((sp.slot ((F.proj tr).time i) : Int) - 1 ≤ j ∨ K x i ℓ B) →
    LockFloor ((F.proj tr).state x i).locks ℓ.frame B j m →
    ∃ C ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame ((F.proj tr).time i), ℓ.frame.Anc B C

end Consensus.Goldilocks.SA.FamilyFacts

end
