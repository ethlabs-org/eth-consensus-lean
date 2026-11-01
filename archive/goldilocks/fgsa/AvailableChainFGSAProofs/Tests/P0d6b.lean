module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchCompose
public import AvailableChainFGSAProofs.Proofs.Healing.Reset

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-! G0 for P0d6b on the FG-SA side: the canonical producer of the allowance-side premises
of `FGCompose.healing_resetWitness`. The frozen budget choice
(`healing_reset_budget_choice`) selects ρΓ or the guarded ρ₁ with its budget equation for
`B'_resetF`; for that allowance the frozen `TRepair`, `frontierSearch_repair_start` and
`frontierSearch_allowance_nonneg` give nonnegativity and the generic semantic allowance
at every actual phase start. Private test adapters only (copies of the P0d5d-b ones). -/

private def p0d6zTstCore (p : Params) {In : Type} (c : AppCodec In) :
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


private def p0d6zTstTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime


private def p0d6zTstObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d6zTstCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem p0d6zTstPhase_iff (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} :
    FGCompose.PhaseInterval (p0d6zTstCore p c) E rho (p0d6zTstObs p c) u v m J contested ↔
      PhaseInterval p c E rho u v m J contested := by
  cases J <;> exact Iff.rfl

-- Local repair allowance: both frozen TRepair arms at the frozen first labels.
private theorem p0d6zTstAllowance [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF ρbar u : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho)
    (mode : FrontierRepairStart p E G u ρbar) :
    FGCompose.FrontierRepairAllowance (p0d6zTstCore p c) E rho (p0d6zTstObs p c) (p0d6zTstTiming p)
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
      ((p0d6zTstPhase_iff E rho).mp hp)).1 β after least
    refine ⟨fun s Q hls hg hQ => (hafter s Q hls hg hQ).1, fun hb => ?_⟩
    obtain ⟨s, Q, h1, h2, hQ, he⟩ := hex hb
    exact ⟨s, Q, h1, h2, hQ, he.1⟩
  | one b after least window sync =>
    refine ⟨by
      change 0 ≤ (4 * (p.k : Time) - 1) * p.Δ + Γ p G + 10 * p.Δ
      nlinarith [p.deltaPos, hrec.gapPos], _, .one b after least window sync, ?_⟩
    intro hG4 v m J contested hready hp
    obtain ⟨hafter, hex⟩ := (repair G u v m J contested (healing_proposal_gap hrec) hG4 hready
      ((p0d6zTstPhase_iff E rho).mp hp)).2 b after least window sync
    refine ⟨fun s Q hls hg hQ => (hafter s Q hls hg hQ).1, fun hb => ?_⟩
    obtain ⟨s, Q, h1, h2, hQ, he⟩ := hex hb
    exact ⟨s, Q, h1, h2.le, hQ, he.1⟩

-- G0 (canonical producer): for the allowance of the frozen budget choice, the three
-- allowance-side premises of the generic reset assembly: the budget equation of
-- B'_resetF, nonnegativity, and the allowance at every actual phase start.
private theorem p0d6zTstResetAllowance [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (repair : TRepair p c E rho) :
    ∃ ρbar,
      B'_resetF p ΔF G = 3 * FGCompose.P (p0d6zTstTiming p) +
        (FGCompose.E_gF (p0d6zTstTiming p) ΔF G ρbar +
          FGCompose.E_jF (p0d6zTstTiming p) ΔF G ρbar +
          FGCompose.B_cF (p0d6zTstTiming p) ΔF G ρbar) +
        (FGCompose.E_gF (p0d6zTstTiming p) ΔF G ρbar +
          FGCompose.E_jF (p0d6zTstTiming p) ΔF G ρbar +
          FGCompose.D_cF (p0d6zTstTiming p) ρbar) ∧
      0 ≤ ρbar ∧
      ∀ i ev m kind, FGCompose.FrontierSearchStart (p0d6zTstCore p c) E rho (p0d6zTstObs p c)
          (p0d6zTstTiming p) (recoveryStart p E) i ev m kind →
        recoveryStart p E + 2 * FGCompose.P (p0d6zTstTiming p) ≤ ev.time →
        FGCompose.FrontierRepairAllowance (p0d6zTstCore p c) E rho (p0d6zTstObs p c)
          (p0d6zTstTiming p) (fgsaInterface p c) (recoveryStart p E) p.k G ρbar
          (ev.time + 3 * (p0d6zTstTiming p).delta) := by
  obtain ⟨ρbar, hmode, hbudget⟩ := healing_reset_budget_choice p G ΔF
  exact ⟨ρbar, hbudget, frontierSearch_allowance_nonneg E rho hrec hmode, fun _ _ _ _ _ hd =>
    p0d6zTstAllowance E rho hrec repair (frontierSearch_repair_start E G hd hmode)⟩

end AvailableChain.FGSA.Run
end
