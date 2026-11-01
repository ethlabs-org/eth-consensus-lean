module
public import AvailableChainFGSAProofs.Proofs.Healing.CommonEntry -- shake: keep (C1–C7 tests)

set_option linter.privateModule false

/-! H-COMMON tests (plan §3F and §5). These test the frozen conjunction, opening
boundaries, both height branches, and the separate second-opening phase implication.
The two-branch check rejects compatibility from common ancestry alone. -/

public section
namespace AvailableChain.FGSA.Run.Tests.HealingCommon
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

section Signatures
variable [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (services : OpeningServiceScopes E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉
          @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
            (actView pre) w C)
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))

include hrec mono crossing services writes rowCoverage

-- C6: the exact frozen statement, with no repair provenance or circular contract.
example : TCommon p c E rho := healing_tCommon E rho hrec mono crossing services writes rowCoverage

variable {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hgst : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q) (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q)

-- C2: equality q = rR stays inside OpeningCovered.
example (hq : q = r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested) :
    OpeningCovered p c E rho r Q :=
  common_opening_covered E rho hrec mono crossing services writes rowCoverage hgst hQ hQfg hexact hu
    (le_of_eq hq) hphase

-- C2–C3: q + 1 = rR is the strict transfer boundary; sources remain compatible.
example (hq1 : q + 1 = r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested) :
    OpeningCovered p c E rho r Q ∧
      (∀ x y K K', x ∈ rho.honest → y ∈ rho.honest →
        actionSourceFG p c E rho x r = some (some K) →
        actionSourceFG p c E rho y r = some (some K') →
        Block.Compatible (eraseFG K) (eraseFG K')) :=
  ⟨common_opening_covered E rho hrec mono crossing services writes rowCoverage hgst hQ hQfg
    hexact hu
      (by omega) hphase,
    common_sources_compatible E rho hrec.toRecovery₂
      (common_sameLabel_scope E rho hrec mono crossing services writes hgst hQ hQfg hexact
        hu (by omega) hphase) hgst hu (by omega) hphase⟩

-- C4: a high pivot fixes T_h.root at the first opening.
example (hqr : q ≤ r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested)
    (hh : (heightView p Qfg).h = m) : OpeningEntry p c E rho r m :=
  common_entry_at_high E rho hrec mono crossing services writes hgst hQ hQfg hexact hu hqr hphase hh

-- C4: low, uncontested, with all selected sources low, gives the low entry.
example (hqr : q ≤ r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J false)
    (hh : (heightView p Qfg).h = m - 1)
    (hlow : ∀ x K, x ∈ rho.honest → actionSourceFG p c E rho x r = some (some K) →
      (heightView p K).h ≤ m - 1) : OpeningEntry p c E rho r (m - 1) := by
  apply common_entry_of_plateau E rho r (m - 1) Qfg hh
  intro x K hx hK
  exact ⟨(common_sources_extend_and_cap E rho hrec mono crossing services writes hgst hQ hQfg hexact
    hu hqr hphase x K hx hK).1, hlow x K hx hK⟩

-- C4–C5: actual low and high sources exclude either uniform first-opening height;
-- the high source gives entry m at the second opening only with the new phase premise.
example (hqr : q ≤ r * p.R)
    {x y : V} {L K : FGBlock (Fin p.n)} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hL : actionSourceFG p c E rho x r = some (some L))
    (hK : actionSourceFG p c E rho y r = some (some K))
    (hhL : (heightView p L).h = m - 1) (hhK : (heightView p K).h = m) :
    ¬ OpeningEntry p c E rho r (m - 1) ∧ ¬ OpeningEntry p c E rho r m ∧
      (PhaseInterval p c E rho u (p.actionTime (r + 1)) m J contested →
        OpeningEntry p c E rho (r + 1) m) := by
  have hm : 1 ≤ m := hhK ▸ (fgCertificateLaws p).height.one_le_h K
  refine ⟨?_, ?_, common_next_entry E rho hrec mono crossing services writes hgst hQ hQfg hexact hu
    hqr hy hK hhK⟩
  · rintro ⟨e, he⟩
    have hh := (he y K hy hK).1
    simp only [Height] at hh hhK
    omega
  · rintro ⟨e, he⟩
    have hh := (he x L hx hL).1
    simp only [Height] at hh hhL
    omega

-- C6: m = 1 uses the TCommon premise shape and includes covered rows.
example (hqr : q ≤ r * p.R) (hfirst : ∀ r', q ≤ r' * p.R → r ≤ r')
    (hphase : PhaseInterval p c E rho u (p.actionTime r) 1 J contested) :
    0 ≤ p.actionTime r - SA.gateTime p.toParams q ∧
      p.actionTime r - SA.gateTime p.toParams q ≤ P p - 4 * p.Δ ∧
      OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r 1 :=
  common_height_one E rho hrec mono crossing services writes rowCoverage hgst hQ hQfg hexact hu hqr
    hfirst hphase

-- C6: low branch, including its explicit phase implication, in the frozen conjunction.
example (hqr : q ≤ r * p.R) (hfirst : ∀ r', q ≤ r' * p.R → r ≤ r')
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J false)
    (hh : (heightView p Qfg).h = m - 1) :
    OpeningEntry p c E rho r (m - 1) ∨
      ((∃ x K, x ∈ rho.honest ∧ actionSourceFG p c E rho x r = some (some K) ∧
          (heightView p K).h = m) ∧
        (PhaseInterval p c E rho u (p.actionTime (r + 1)) m J false →
          OpeningEntry p c E rho (r + 1) m)) :=
  (healing_tCommon E rho hrec mono crossing services writes rowCoverage u m J false q Q Qfg r
    hgst hQ
    hQfg hexact hu hqr hfirst hphase).2.2.2.2.2 hh

end Signatures

section Boundary
variable (p : Params)

-- C1: q = rR has zero elapsed time.
example (r : Nat) : p.actionTime r - SA.gateTime p.toParams (r * p.R) = 0 := by
  change (4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ) -
    (4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ) = 0
  ring

-- C1: q = 1 attains the bound for every R ≥ 2, including R > 2.
example : (∀ r', 1 ≤ r' * p.R → 1 ≤ r') ∧
    p.actionTime 1 - SA.gateTime p.toParams 1 = P p - 4 * p.Δ ∧
    0 ≤ p.actionTime 1 - SA.gateTime p.toParams 1 ∧
    p.actionTime 1 - SA.gateTime p.toParams 1 ≤ P p - 4 * p.Δ := by
  have hfirst : ∀ r', 1 ≤ r' * p.R → 1 ≤ r' := by
    intro r' h
    by_contra hn
    have hz : r' = 0 := by omega
    subst r'
    simp at h
  have hle : 1 ≤ 1 * p.R := by have := p.RLarge; omega
  refine ⟨hfirst, ?_, common_first_time_bound (p := p) 1 1 hle hfirst⟩
  change 4 * p.Δ * ((1 * p.R : Nat) : Int) + 6 * p.Δ -
    (4 * p.Δ * ((1 : Nat) : Int) + 6 * p.Δ) = 4 * (p.R : Int) * p.Δ - 4 * p.Δ
  push_cast
  ring

example (hR : p.R = 2) : p.actionTime 1 - SA.gateTime p.toParams 1 = 4 * p.Δ := by
  change 4 * p.Δ * ((1 * p.R : Nat) : Int) + 6 * p.Δ -
    (4 * p.Δ * ((1 : Nat) : Int) + 6 * p.Δ) = 4 * p.Δ
  rw [hR]
  push_cast
  ring

example (hR : 2 < p.R) : 1 ≤ 1 * p.R ∧
    p.actionTime 1 - SA.gateTime p.toParams 1 = P p - 4 * p.Δ := by
  refine ⟨by omega, ?_⟩
  change 4 * p.Δ * ((1 * p.R : Nat) : Int) + 6 * p.Δ -
    (4 * p.Δ * ((1 : Nat) : Int) + 6 * p.Δ) = 4 * (p.R : Int) * p.Δ - 4 * p.Δ
  push_cast
  ring

-- C5: Params gives the two-label gap for any R, including R = 2.
example (r : Nat) : r * p.R + 2 ≤ (r + 1) * p.R := by
  rw [Nat.succ_mul]
  have := p.RLarge
  omega

end Boundary

-- C7: two branches above Q give common ancestry but fail compatibility.
example :
    Block.Preceq (.node .genesis 1 ⟨1⟩ 0) (.node (.node .genesis 1 ⟨1⟩ 0) 2 ⟨2⟩ 0) ∧
      Block.Preceq (.node .genesis 1 ⟨1⟩ 0) (.node (.node .genesis 1 ⟨1⟩ 0) 2 ⟨3⟩ 1) ∧
      ¬ Block.Compatible (.node (.node .genesis 1 ⟨1⟩ 0) 2 ⟨2⟩ 0) (.node (.node .genesis 1 ⟨1⟩
          0) 2 ⟨3⟩ 1) := by
  change Block.preceq (.node .genesis 1 ⟨1⟩ 0) (.node (.node .genesis 1 ⟨1⟩ 0) 2 ⟨2⟩ 0) = true ∧
    Block.preceq (.node .genesis 1 ⟨1⟩ 0) (.node (.node .genesis 1 ⟨1⟩ 0) 2 ⟨3⟩ 1) = true ∧
    ¬ Block.compatible (.node (.node .genesis 1 ⟨1⟩ 0) 2 ⟨2⟩ 0) (.node (.node .genesis 1 ⟨1⟩ 0)
        2 ⟨3⟩ 1) = true
  decide

end AvailableChain.FGSA.Run.Tests.HealingCommon
end
