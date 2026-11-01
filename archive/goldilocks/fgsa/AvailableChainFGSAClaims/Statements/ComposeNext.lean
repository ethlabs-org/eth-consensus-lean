module
public import AvailableChainFGSAClaims.Statements.ComposeStmt -- shake: keep (foundation layer)

@[expose] public section

/-! Compose-dependent final foundation target. The lower `FrameNext` module
has no dependency on this module or `ComposeStmt`. At SWITCH, `ComposeStmt`
can import that lower module and use `RFrameExactNext` for `FGFoundation.frame`.
`FGFoundationNext` compares to canonical `FGFoundation` as class B. Across
SWITCH it is also B: `strat` reaches honest-row emissions through `RStrat`.
Its constructor and every projection inherit the structure's class and deep
cause.

```text
┌──────────────────┬───────────────────┬───────┐
│ Next             │ Canonical         │ Class │
├──────────────────┼───────────────────┼───────┤
│ FGFoundationNext │ FGFoundation      │ B     │
└──────────────────┴───────────────────┴───────┘
```

The frame field alone reads fixed Next controls (class A).
-/

namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Next frame surface; counterpart `FGFoundation`, census B. -/
structure FGFoundationNext : Prop where
  store : RStore p c E rho
  cumul : RStoreDurable p c E rho ∧ RStoreEpoch p c E rho
  mono : RMonoAll p c E rho
  frame : RFrameExactNext p c E rho ∧ RFrameNextEpoch p c E rho
  geo : RGeo p c E rho
  strat : RStrat p c E rho
  reconcile : RRec p c E rho

end AvailableChain.FGSA.Run
end
