module
public import AvailableChainContract.Properties

@[expose] public section

/-! # Evidence and accountability

Evidence is generic: a validator is slashable on a set of objects if two of
them (possibly the same one) are held by it and the protocol's rule
`conflicts` convicts them. The evidence sets are what honest nodes saw
(`Run.ViewIdx`), with everything carried inside. The threshold is fixed: a third
of the validators. -/

namespace AvailableChain.Contract

open AvailableChain.Generic

variable {V : Type} [Fintype V] [DecidableEq V] {F : Family} {E : Env V}

namespace Run

variable (rho : Run F E)

/-- `x` is slashable on the objects `A`. -/
def Slashable (A : Set (protoOf F E).Object) (x : V) : Prop :=
  ∃ o ∈ A, ∃ o' ∈ A, rho.holder o.auth = some x ∧ rho.holder o'.auth = some x ∧
    (protoOf F E).conflicts o o' = true

/-- The validators slashable on `A`. -/
noncomputable def slashedBy (A : Set (protoOf F E).Object) : Finset V := by
  classical
  exact Finset.univ.filter (rho.Slashable A)

/-- Accountable safety of `g` from `t₀`: two honest reads, at any nodes and
event cuts, are compatible, or what the two readers saw before their cuts
slashes a third of the validators. -/
def AccountablySafeFrom (g : Output F E) (t₀ : Time) : Prop :=
  ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ i j, rho.InCuts t₀ i → rho.InCuts t₀ j →
    Chain.Compatible (rho.readIdx g u i) (rho.readIdx g v j) ∨
      Fintype.card V ≤ 3 * (rho.slashedBy (rho.ViewIdx u i ∪ rho.ViewIdx v j)).card

/-- The digest of an item: genesis (`none`) has digest `0`, a header its hash. -/
def itemDigest : Option Header → Nat
  | none => 0
  | some h => rho.hash h

/-- An item is observed: genesis always; a header if the honest nodes saw a
proposal of it under its own slot's key. -/
def ObservedItem : Option Header → Prop
  | none => True
  | some h => ∃ cs, (Obj.mk (.proposer h.slot) (.prop h) cs : (protoOf F E).Object) ∈ rho.Observed

/-- A hash collision was observed: two distinct observed items (genesis, or
headers proposed under their own slot's key) with the same digest. Every such
collision counts, whoever proposed the headers: it is a real collision of the
run's hash on headers that were really observed. (Honest code learns the hash
only through the digests the engine passes, of observed signed headers; it can
still choose what it proposes, so collision resistance of the deployed hash is
an assumption, not a theorem. `claims_iff_claimsInj` shows that the escape
adds nothing beyond the injective case.) -/
def HashCollision : Prop :=
  ∃ a b : Option Header, a ≠ b ∧ rho.itemDigest a = rho.itemDigest b ∧
    rho.ObservedItem a ∧ rho.ObservedItem b

/-- The hash is injective and never `0` (genesis's digest): no collision can
occur. -/
def InjectiveHash : Prop := Function.Injective rho.hash ∧ ∀ h, rho.hash h ≠ 0

/-- No honest validator is slashable on what the honest nodes saw. -/
def HonestNeverSlashed : Prop :=
  ∀ v ∈ rho.honest, ¬ rho.Slashable rho.Observed v

end Run

end AvailableChain.Contract

end
