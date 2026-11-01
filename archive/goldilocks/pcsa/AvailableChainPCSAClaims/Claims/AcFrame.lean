module
public import AvailableChainPCSAClaims.Statements.Regimes

@[expose] public section

/-! [PC-SA claims; pcsa34-r4 5.0, stage 1; lead ruling 2026-10-06 (AC-only
instance)] The frame claim of the AC-only instance `pcsaAC p c`: honest
nodes send no FG row, so the FG frame never moves and `StageOneFrame` holds.
This claim discharges the `StageOneFrame` premise of the stage-1 claims for
`m = .idle`. Statement only. -/

namespace AvailableChain.PCSA.Run

/-- [PC-SA claims; pcsa34-r4 5.0, 5.2.2 (vi), stage 1; Protocol.lean
`pcsaAC`] Every run of the AC-only instance with the base run premises
(`Base₂`: a valid execution, linked FG seats) and `a < ⌈n/2⌉`
(`FaultsBelowQA`) satisfies `StageOneFrame`.
Proof idea: in mode `.idle` no honest node signs an FG row, and linked seats
with unforgeable signatures give each faulty FG seat to a faulty validator.
So every target, progress or finality row set has weight at most `a`, also
when a faulty seat signs several rows. With unit weights the FG quorum is
`(2n + 2)/3 > n/2 ≥ a`, so no set reaches it: no justification, height
(progress) or finality event occurs. At every honest event state `F = J =`
genesis, `h_max = 1` and `h_j = 0` (their initial values); no held block is
off `J`'s chain, so there is no contest, `lo = 0` and `Z` = genesis. -/
def AcOnlyFrameClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsaAC p c)),
    Base₂ p c E rho → FaultsBelowQA p c rho → StageOneFrame p c E rho

theorem AcOnlyFrameClaim_def (p : Params) : AcOnlyFrameClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsaAC p c)),
      Base₂ p c E rho → FaultsBelowQA p c rho → StageOneFrame p c E rho) := by
  rw [AcOnlyFrameClaim]

end AvailableChain.PCSA.Run

end
