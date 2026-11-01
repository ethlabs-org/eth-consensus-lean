module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierOpenAll -- shake: keep (F1–F5 tests)

set_option linter.privateModule false

/-! H-FRONT-OPEN tests: the initial gate, strict later service, the frozen
opening conjunction, height one with genesis top J, and the closed horizon.
The concrete plateau test has unequal source bodies and equal full T_h. -/

public section
namespace AvailableChain.FGSA.Run.Tests.HealingFrontierOpen
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

section Signatures
variable [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho)
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))

include hrec crossing rowCoverage

variable {u v : Time} {m q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hgst : recoveryStart p E ≤ u) (hQfg : eraseFG Qfg = Q) (hh : (heightView p Qfg).h = m)
    (hexact : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)

-- F1: equality uses only the initial ExactService at the atomic clock.
example (hqr : q = r * p.R) (hav : p.actionTime r ≤ v) :
    OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r m ∧
      (∀ x K, x ∈ rho.honest → actionSourceFG p c E rho x r = some (some K) →
        (heightView p K).T_h = (heightView p Qfg).T_h) :=
  frontier_open_q_eq E rho hrec crossing rowCoverage hgst hQfg hh hexact hu hqr hav hvh hcap

-- F2: strict later service has no PhaseInterval through the opening.
example (hqr : q < r * p.R) (hav : p.actionTime r ≤ v)
    (hserved : FrontierOpeningServed E rho r Q) :
    OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r m ∧
      (∀ x K, x ∈ rho.honest → actionSourceFG p c E rho x r = some (some K) →
        (heightView p K).T_h = (heightView p Qfg).T_h) :=
  frontier_open_later E rho hrec crossing rowCoverage hgst hQfg hh hexact hu hqr hav hvh hcap
    hserved

-- F4: exactly the frozen per-r conjunct, with service only for q < rR.
-- An actual selected source can differ from Qfg. CAP still forces its height
-- to m, and the production theorem gives equality of the full entry blocks.
example (hqr : q < r * p.R) (hav : p.actionTime r ≤ v)
    (hserved : FrontierOpeningServed E rho r Q) {x : V} {K : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hK : actionSourceFG p c E rho x r = some (some K))
    (hstrict : FGBlock.Preceq Qfg K ∧ Qfg ≠ K) :
    (heightView p K).h = m ∧ (heightView p K).T_h = (heightView p Qfg).T_h ∧ Qfg ≠ K := by
  obtain ⟨_, hentry, hident⟩ := frontier_open_later E rho hrec crossing rowCoverage hgst
    hQfg hh hexact hu hqr hav hvh hcap hserved
  obtain ⟨e, he⟩ := hentry
  exact ⟨(he x K hx hK).1, hident x K hx hK, hstrict.2⟩

-- F4: exactly the frozen per-r conjunct, with service only for q < rR.
example {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hphase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v)
    (hserved : ∀ r, q < r * p.R → p.actionTime r ≤ v → FrontierOpeningServed E rho r Q) :
    ∀ r, q ≤ r * p.R → p.actionTime r ≤ v →
      OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r m ∧
      (∀ x K, x ∈ rho.honest → actionSourceFG p c E rho x r = some (some K) →
        (heightView p K).T_h = (heightView p Qfg).T_h) ∧
      ((∀ r', q ≤ r' * p.R → r ≤ r') →
        p.actionTime r - SA.gateTime p.toParams q ≤ P p - 4 * p.Δ) :=
  frontier_openings E rho hrec crossing rowCoverage u v m J contested q Q Qfg hgst hQ hQfg hh
    hexact hu hphase hqv hvh hcap hserved

-- F4 at the closed endpoint a_r = v = horizon, with an actual source and row
-- for every honest node. No strict horizon inequality is added.
example {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hphase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hqr : q ≤ r * p.R)
    (hav : p.actionTime r = v) (hhor : v = rho.horizon)
    (hserved : ∀ s, q < s * p.R → p.actionTime s ≤ v → FrontierOpeningServed E rho s Q) :
    OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r m ∧
      (∀ x K, x ∈ rho.honest → actionSourceFG p c E rho x r = some (some K) →
        (heightView p K).T_h = (heightView p Qfg).T_h) ∧
      ((∀ r', q ≤ r' * p.R → r ≤ r') →
        p.actionTime r - SA.gateTime p.toParams q ≤ P p - 4 * p.Δ) :=
  frontier_openings E rho hrec crossing rowCoverage u v m J contested q Q Qfg hgst hQ hQfg hh
    hexact hu hphase hqv hhor.le hcap hserved r hqr hav.le

end Signatures

section HeightOne
variable [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho)
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))

-- Height one, genesis top J, and q = 1 at R = 2 all use the same full theorem.
example {u v : Time} {Q : Block} {Qfg : FGBlock (Fin p.n)} (hR : p.R = 2)
    (hgst : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) 1 Q)
    (hQfg : eraseFG Qfg = Q) (hh : (heightView p Qfg).h = 1)
    (hexact : ExactService p c E rho 1 Q) (hu : u ≤ SA.proposalTime p.toParams 1)
    (hphase : PhaseInterval p c E rho u (SA.gateTime p.toParams 1) 1 (some .genesis) false)
    (hqv : SA.gateTime p.toParams 1 ≤ v) (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ 1)
    (hav : p.actionTime 1 ≤ v)
    (hserved : ∀ r, 1 < r * p.R → p.actionTime r ≤ v → FrontierOpeningServed E rho r Q) :
    OpeningCovered p c E rho 1 Q ∧ OpeningEntry p c E rho 1 1 ∧
      (∀ x K, x ∈ rho.honest → actionSourceFG p c E rho x 1 = some (some K) →
        (heightView p K).T_h = (heightView p Qfg).T_h) ∧
      p.actionTime 1 - SA.gateTime p.toParams 1 ≤ P p - 4 * p.Δ := by
  have h := frontier_openings E rho hrec crossing rowCoverage u v 1 (some .genesis) false 1 Q
    Qfg hgst hQ hQfg hh hexact hu hphase hqv hvh hcap hserved 1 (by rw [hR]; omega) hav
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2 (fun r' hr => by rw [hR] at hr; omega)⟩

end HeightOne

-- F3: q = rR gives zero elapsed time.
example (r : Nat) : p.actionTime r - SA.gateTime p.toParams (r * p.R) = 0 := by
  change p.actionTime r - p.actionTime r = 0
  exact sub_self _

-- q = 1 at R = 2 attains the bound; the first-opening premise is explicit.
example (hR : p.R = 2) :
    p.actionTime 1 - SA.gateTime p.toParams 1 = P p - 4 * p.Δ ∧
      p.actionTime 1 - SA.gateTime p.toParams 1 ≤ P p - 4 * p.Δ := by
  refine ⟨?_, frontier_open_time 1 1 (by rw [hR]; omega)
    (fun r' hr => by rw [hR] at hr; omega)⟩
  change 4 * p.Δ * ((1 * p.R : Nat) : Int) + 6 * p.Δ -
    (4 * p.Δ * ((1 : Nat) : Int) + 6 * p.Δ) = 4 * (p.R : Int) * p.Δ - 4 * p.Δ
  rw [hR]
  push_cast
  ring

-- The plateau theorem permits a strict descendant at the same height.
example {Qfg K : FGBlock (Fin p.n)} (hQK : FGBlock.Preceq Qfg K ∧ Qfg ≠ K)
    (hh : (heightView p Qfg).h = (heightView p K).h) :
    (heightView p K).T_h = (heightView p Qfg).T_h :=
  (frontier_open_plateau hh hQK.1 le_rfl).2

private abbrev p4 : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide, R := 2, δt := 1, RLarge := by decide, digest :=
        fun d => ⟨d.slot + 1⟩ }

private abbrev Q4 : FGBlock (Fin 4) := .node .genesis 1 ⟨1⟩ 0 []
private abbrev K4 : FGBlock (Fin 4) := .node Q4 2 ⟨2⟩ 0 []

-- Concrete, unequal, non-genesis bodies: K4 strictly extends Q4 at height one.
-- Full block equality is obtained from the production plateau theorem.
example : FGBlock.Preceq Q4 K4 ∧ Q4 ≠ K4 ∧
    (heightView p4 Q4).h = 1 ∧ (heightView p4 K4).h = 1 ∧
    (heightView p4 K4).T_h = (heightView p4 Q4).T_h := by
  have hQK : FGBlock.Preceq Q4 K4 := by decide
  have hQ : (heightView p4 Q4).h = 1 := by decide
  have hK : (heightView p4 K4).h = 1 := by decide
  exact ⟨hQK, by decide, hQ, hK, (frontier_open_plateau hQ hQK hK.le).2⟩

#print axioms frontier_open_q_eq
#print axioms frontier_open_later
#print axioms frontier_open_time
#print axioms frontier_openings

end AvailableChain.FGSA.Run.Tests.HealingFrontierOpen
end
