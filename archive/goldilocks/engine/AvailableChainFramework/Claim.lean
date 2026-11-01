module
public import AvailableChainFramework.ClaimDomain

@[expose] public section

namespace AvailableChain.Framework

/-- How a claim can be refuted. The tag of a claim is the minimal refutation
form that the claim admits. `.run` means that one finite run for one constant
refutes the claim. `.family` means that a refutation must cover every valid
constant (for example, an inclusion claim with a delay). A claim with `.run`
can also have a `RefutationFamily`, which is stronger evidence. -/
inductive RefutationKind where
  /-- One finite run for one constant refutes the claim. -/
  | run
  /-- A refutation must cover every valid constant. -/
  | family
  /-- The claim has no refutation form. -/
  | none
  deriving DecidableEq, Repr

variable {K : ClaimDomain}

/-- A catalog claim over a claim domain `K` (design §4). `le k k'` means that
`k'` is at least as weak as `k`. `Point` holds the run parameters that the
claim quantifies over (for example `t₀`, or `T`, `b₀`, `b₁`). -/
structure ClaimSpec (K : ClaimDomain) where
  id : Lean.Name
  Const : Type
  valid : Const → Prop
  le : Const → Const → Bool
  le_refl : ∀ k, le k k = true
  le_trans : ∀ a b c, le a b = true → le b c = true → le a c = true
  Point : Type
  /-- The runs that the claim speaks about. -/
  regime : (I : K.Inst) → Const → (W : Validators) → K.Ctx I W → Point → Prop
  /-- What the claim states about such a run. -/
  conclusion : (I : K.Inst) → Const → (W : Validators) → K.Ctx I W → Point → Prop
  /-- `trigger I k W x p H`: the event that makes the claim non-vacuous occurs
  in the run at a time at least `H`, with its deadline inside the run
  (design §5; PHASE0-REPORT §6, I2). The type does not force this. A claim
  with a trigger other than `True` proves `<claim>_trigger_late`. For a `True`
  trigger, the horizon bound in `inhabited` carries the time. -/
  trigger : (I : K.Inst) → Const → (W : Validators) → K.Ctx I W → Point → Time → Prop
  /-- A weaker constant keeps the claim. A proof, not metadata. -/
  transport : ∀ (I : K.Inst) (k k' : Const), valid k → valid k' → le k k' = true →
    (∀ (W : Validators) (x : K.Ctx I W), K.admissible I W x → ∀ p,
      regime I k W x p → conclusion I k W x p) →
    (∀ (W : Validators) (x : K.Ctx I W), K.admissible I W x → ∀ p,
      regime I k' W x p → conclusion I k' W x p)
  refutable : RefutationKind

namespace ClaimSpec

/-- The claim holds for an instance at a constant. -/
def holds (c : ClaimSpec K) (I : K.Inst) (k : c.Const) : Prop :=
  ∀ (W : Validators) (x : K.Ctx I W), K.admissible I W x → ∀ p,
    c.regime I k W x p → c.conclusion I k W x p

/-- For every time `H`, the regime has an admissible run of the instance with
a horizon of at least `H`, in which the trigger occurs at a time of at least
`H` (design §5; I2). -/
def inhabited (c : ClaimSpec K) (I : K.Inst) (k : c.Const) : Prop :=
  ∀ H : Time, ∃ (W : Validators) (x : K.Ctx I W) (p : c.Point),
    K.admissible I W x ∧ H ≤ K.horizon I W x ∧ c.regime I k W x p ∧
      c.trigger I k W x p H

end ClaimSpec

end AvailableChain.Framework

end
