module
public import ConsensusShape.Claims
@[expose] public section

namespace Consensus.Shape
open AvailableChain (Time)
open Run

variable {V : Type} [Fintype V] [DecidableEq V] {F : Family}

/-- Fixed shape premises, on the very same runs as the L0 system. -/
def profile (C : Constants) : System.Profile (Model.sysOf (compiled F) V) where
  valid r := ShapeValid r.2
  sleepy r := Sleepy r.2 C 0
  live k r := LiveSleepy r.2 C 0 k
  outage T b₀ b₁ r := Outage r.2 C T b₀ b₁
  outageFast T b₀ b₁ r := FastOutage r.2 C T b₀ b₁
  recovery k r := Recovery r.2 C k
  finality k r := Finality r.2 C k

/-- Bounds are durations and hence depend on the public Δ. L0 uses one
fixed set of bounds for an entire system; this system quantifies over Δ. -/
def bounds (C : Constants) (Δ : Time) : System.Bounds where
  catchUp := (C.catchUp : Time) * Δ
  confirmedLive k := (C.growth.eval k : Time) * Δ
  stableLive k := (C.stableGrowth.eval k : Time) * Δ
  recovery k := (C.recovery.eval k : Time) * Δ
  finStart k := (C.finStart.eval k : Time) * Δ
  finLive k := (C.finDelay.eval k : Time) * Δ

/-- Candidate refinement implication, stated only. The explicit Δ is necessary
because L0 Bounds stores durations, while sysOf ranges over all Δ. As written,
profile does not restrict runs to this Δ: this is NOT asserted to follow from
ShapeClaims. A future theorem needs run-dependent bounds in L0, or a system
restricted to a fixed Δ (and corresponding model laws). Neither lower layer is
changed here. -/
def RefinementStatement (F : Family) (C : Constants) (V : Type)
    [Fintype V] [DecidableEq V] [Nonempty V] (Δ : Time) : Prop :=
  ShapeClaims F C → System.ProblemClaims (Model.sysOf (fun pub => compile (F pub)) V)
    (profile C) (bounds C Δ)

end Consensus.Shape
end
