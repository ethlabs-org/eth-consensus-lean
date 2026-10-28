module
public import ConsensusShape.Claims
@[expose] public section

namespace Consensus.Shape
open Run

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] {F : Family}

/-- Fixed shape premises, on the very same runs as the L0 system. -/
def profile (C : Constants) : System.Profile (Model.sysOf (compiled F) V) where
  sleepy r := Sleepy r.2 C
  live k r := LiveSleepy r.2 C k
  outage T b₀ b₁ r := Outage r.2 C T b₀ b₁ ∨ FastOutage r.2 C T b₀ b₁
  recovery k r := Recovery r.2 C k
  finality k r := Finality r.2 C k

/-- The reported bounds, as coefficients of `Δ`. -/
def bounds (C : Constants) : System.Bounds where
  catchUp := C.catchUp
  confirmedLive k := C.growth.eval k
  stableLive k := C.stableGrowth.eval k
  recovery k := C.recovery.eval k
  finStart k := C.finStart.eval k
  finLive k := C.finDelay.eval k

/-- The refinement: the shape's claims give the consensus problem's claims for
the compiled family, under the shape's profile and bounds. Proved as `refinement`
(Refinement.lean). -/
def RefinementStatement (F : Family) (C : Constants) (V : Type)
    [Fintype V] [DecidableEq V] [Nonempty V] : Prop :=
  ShapeClaims F C → System.ProblemClaims (Model.sysOf (fun pub => compile (F pub)) V)
    (profile C) (bounds C)

end Consensus.Shape
end
