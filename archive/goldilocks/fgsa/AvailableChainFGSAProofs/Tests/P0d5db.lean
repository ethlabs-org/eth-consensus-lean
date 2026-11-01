module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchCompose

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-! G0 for P0d5d-b on the FG-SA side: the canonical producer of the start-family premise
of `FGCompose.FrontierSearchFamilyStatement`. For both frozen allowance choices (ρΓ, and
ρ₁ under its window guard) the frozen `TRepair` and `frontierSearch_repair_start` give the
generic semantic repair allowance at every actual phase start after the recovery delay,
and `frontierSearch_allowance_nonneg` gives nonnegativity. Private test adapters only. -/

private def p0d5zTstCore (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGCoreReads (fgsa p c) p.n (GridCO.State p.n .root) (Wire p.n) (RowWire p.n) :=
  { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
    erase := eraseFG
    source := fun nd => FGSA.fgSource p nd.st
    headVote := fun nd s => FGSA.headVote p nd.st s
    finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
    proposalFG := fun nd o => match (toWire p o).decode with
      | some (.block _ N) => (parentFG nd.st N.erase).map (fun P => fgBlock P N.erase N.rows)
      | some (.vote _ _ _) => none
      | some (.row _ _) => none
      | none => none }


private def p0d5zTstTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime


private def p0d5zTstObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d5zTstCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem p0d5zTstPhase_iff (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} :
    FGCompose.PhaseInterval (p0d5zTstCore p c) E rho (p0d5zTstObs p c) u v m J contested ↔
      PhaseInterval p c E rho u v m J contested := by
  cases J <;> exact Iff.rfl

-- Local repair allowance: both frozen TRepair arms at the frozen first labels.
private theorem p0d5zTstAllowance [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF ρbar u : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho)
    (mode : FrontierRepairStart p E G u ρbar) :
    FGCompose.FrontierRepairAllowance (p0d5zTstCore p c) E rho (p0d5zTstObs p c) (p0d5zTstTiming p)
      (fgsaInterface p c) (recoveryStart p E) p.k G ρbar u := by
  have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
  have hG := (fgsa_gamma_bounds p G).1
  cases mode with
  | two β after least =>
    refine ⟨by
      change 0 ≤ 2 * ((4 * (p.k : Time) - 1) * p.Δ) + Γ p G + 8 * p.Δ
      nlinarith [p.deltaPos, hrec.gapPos], _, .two β after least, ?_⟩
    intro hG4 v m J contested hready hp
    obtain ⟨hafter, hex⟩ := (repair G u v m J contested (healing_proposal_gap hrec) hG4 hready
      ((p0d5zTstPhase_iff E rho).mp hp)).1 β after least
    refine ⟨fun s Q hls hg hQ => (hafter s Q hls hg hQ).1, fun hb => ?_⟩
    obtain ⟨s, Q, h1, h2, hQ, he⟩ := hex hb
    exact ⟨s, Q, h1, h2, hQ, he.1⟩
  | one b after least window sync =>
    refine ⟨by
      change 0 ≤ (4 * (p.k : Time) - 1) * p.Δ + Γ p G + 10 * p.Δ
      nlinarith [p.deltaPos, hrec.gapPos], _, .one b after least window sync, ?_⟩
    intro hG4 v m J contested hready hp
    obtain ⟨hafter, hex⟩ := (repair G u v m J contested (healing_proposal_gap hrec) hG4 hready
      ((p0d5zTstPhase_iff E rho).mp hp)).2 b after least window sync
    refine ⟨fun s Q hls hg hQ => (hafter s Q hls hg hQ).1, fun hb => ?_⟩
    obtain ⟨s, Q, h1, h2, hQ, he⟩ := hex hb
    exact ⟨s, Q, h1, h2.le, hQ, he.1⟩

-- G0 (canonical producer): both premises of the companion statement, for each frozen
-- allowance choice, from the frozen recovery regime and the frozen repair channel.
private theorem p0d5zTstFamily [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF ρbar : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho)
    (hmode : ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) :
    0 ≤ ρbar ∧
    ∀ i ev m kind, FGCompose.FrontierSearchStart (p0d5zTstCore p c) E rho (p0d5zTstObs p c)
        (p0d5zTstTiming p) (recoveryStart p E) i ev m kind →
      recoveryStart p E + 2 * FGCompose.P (p0d5zTstTiming p) ≤ ev.time →
      FGCompose.FrontierRepairAllowance (p0d5zTstCore p c) E rho (p0d5zTstObs p c)
        (p0d5zTstTiming p) (fgsaInterface p c) (recoveryStart p E) p.k G ρbar
        (ev.time + 3 * (p0d5zTstTiming p).delta) :=
  ⟨frontierSearch_allowance_nonneg E rho hrec hmode, fun _ _ _ _ _ hd =>
    p0d5zTstAllowance E rho hrec repair (frontierSearch_repair_start E G hd hmode)⟩

end AvailableChain.FGSA.Run
end
