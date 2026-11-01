module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierOpen


public section

/-! TFrontier's per-opening conjunction, frontier plan §2.4 and §3.1 step 8.
This keeps the frozen seed premises and the closed cap. HG.1 supplies only
FrontierOpeningServed at strict later openings. INLINE rowCoverage has the
H-COMMON form; its Assembly producer is rowPermission_covered. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- H-FRONT-OPEN F4. DC: INTENTIONAL the complete per-r conjunct of TFrontier,
including q = rR, height one, and a_r = v = horizon. The initial phase ends
at d_q. Later fresh service is the only HG.1 input. No RMono or last-write
binder is used here; their work belongs to the future service producer. -/
theorem frontier_openings [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (crossing : RXing p c E rho)
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    (u v : Time) (m : Nat) (J : Option (FGBlock (Fin p.n))) (contested : Bool)
    (q : Nat) (Q : Block) (Qfg : FGBlock (Fin p.n))
    (hready : recoveryStart p E ≤ u) (_hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q) (hh : (heightView p Qfg).h = m)
    (hexact : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (_hphase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (_hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    (hserved : ∀ r, q < r * p.R → p.actionTime r ≤ v → FrontierOpeningServed E rho r Q) :
    ∀ r, q ≤ r * p.R → p.actionTime r ≤ v →
      OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r m ∧
      (∀ x K, x ∈ rho.honest → actionSourceFG p c E rho x r = some (some K) →
        (heightView p K).T_h = (heightView p Qfg).T_h) ∧
      ((∀ r', q ≤ r' * p.R → r ≤ r') →
        p.actionTime r - SA.gateTime p.toParams q ≤ P p - 4 * p.Δ) := by
  intro r hqr hav
  have hopen : OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r m ∧
      (∀ x K, x ∈ rho.honest → actionSourceFG p c E rho x r = some (some K) →
        (heightView p K).T_h = (heightView p Qfg).T_h) := by
    rcases lt_or_eq_of_le hqr with hlt | heq
    · exact frontier_open_later E rho hrec crossing rowCoverage hready hQfg hh hexact hu
        hlt hav hvh hcap (hserved r hlt hav)
    · exact frontier_open_q_eq E rho hrec crossing rowCoverage hready hQfg hh hexact hu
        heq hav hvh hcap
  exact ⟨hopen.1, hopen.2.1, hopen.2.2, frontier_open_time q r hqr⟩

end AvailableChain.FGSA.Run
end
