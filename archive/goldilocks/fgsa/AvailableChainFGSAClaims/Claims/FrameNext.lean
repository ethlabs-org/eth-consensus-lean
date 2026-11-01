module
public import AvailableChainFGSAClaims.Statements.Packages.Safety
public import AvailableChainFGSAClaims.Statements.ComposeNext

@[expose] public section

/-! Stage 0 claim targets; port r2 ruling A. Bounds and binders stay fixed.
`FrameClaimNext` is the future aggregate frame field type. `FGFoundationClaimNext`
is the future safety interface field type. `FGFoundationNext.frame` is its exact
frame channel. The canonical aggregate and all suppliers stay unchanged here.

```text
┌───────────────────────┬───────────────────┬───────┐
│ Next statement        │ Canonical         │ Class │
├───────────────────────┼───────────────────┼───────┤
│ FrameAtNext           │ FrameAt           │ B     │
│ FrameClaimNext        │ FrameClaim        │ B     │
│ FGFoundationClaimNext │ FGFoundationClaim │ B     │
└───────────────────────┴───────────────────┴───────┘
```

SWITCH deep-digest causes: `FrameAt`, `FrameClaim`, `FGFoundationClaim` ->
new frame dependencies (canonical-to-Next class B). Across SWITCH, `FrameAtNext`
and `FrameClaimNext` have class A by same-event transport of `Node.st` and fixed
Next readers. `FGFoundationClaimNext` has class B through `RStrat` emissions.
The run binder changes their deep closure independently of these classes.
`CleanCutPosClaim` -> Next foundation antecedent only; keep its conclusion and
premises otherwise fixed. WP00c records measured digests, not this module.
No claim needs a new premise. Contest equality requires a context invariant;
FaultQ alone does not give equality and does not change a B entry to C-i.
-/

namespace AvailableChain.FGSA.Run

/-- Next claim surface; counterpart `FGFoundationClaim`, census B. -/
def FGFoundationClaimNext (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    SourceDisciplinePrem p c E rho pt → FGFoundationNext p c E rho

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Next claim surface; counterpart `FrameClaim`, census B. -/
def FrameClaimNext : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    FrameAtNext p c E rho

end AvailableChain.FGSA.Run
end
