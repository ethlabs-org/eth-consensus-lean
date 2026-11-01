module
public import AvailableChainFGSAProofs.Proofs.Healing.OpeningServiceOne -- shake: keep (O1–O6 tests)

set_option linter.privateModule false

/-! H-GATE tests (plan fgsa-s5-hgate-hcommon §5, §6). Signatures of the H-GATE supplier at
the exact §2.3 conclusion under the standing envelope (Recovery₂, RMono, RXing, B27
`writes`), the opening transfer, the body propagation to the next opening, OpeningCovered,
and the height-one handoff. The boundary cases q = rR, q + 1 = rR, q = 1 with R = 2, m = 1
and the next-opening label gap at R = 2. The §5 falsification candidates are comments; the
two-branch candidate also has a concrete check. -/

public section
namespace AvailableChain.FGSA.Run.Tests.HealingOpening
open AvailableChain.SimplexFG

section Signatures

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- O2: the exact §2.3 conclusion. GateService at rR is a conclusion, not a premise.
example
    [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
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
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hgst : recoveryStart p E ≤ u)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q)
    (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hqr : q ≤ r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (ht : rho.events[i]? = some (.tick x (p.actionTime r))) :
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
      (p.actionTime r)).st
    ∃ D : FGBlock (Fin p.n),
      Gen.AC.Duty.GateService (fgsaAC E rho) i (r * p.R) x (eraseFG D) ∧
      D ∈ domainR p st (treeT p st) ∧
      FGBlock.Preceq Qfg D ∧
      (frameR p st).lo ≤ (heightView p D).h :=
  later_opening_gateService_domain E rho hrec mono crossing services writes hgst hQ hQfg
    hexact hu hqr
    hphase hx ht

-- O2 boundary q = rR: the repair gate is itself the opening; the service is for Q itself.
example
    [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
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
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hgst : recoveryStart p E ≤ u)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q)
    (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hq : q = r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (ht : rho.events[i]? = some (.tick x (p.actionTime r))) :
    Gen.AC.Duty.GateService (fgsaAC E rho) i (r * p.R) x Q ∧
      Qfg ∈ domainR p (storeAt p c E rho i x) (treeT p (storeAt p c E rho i x)) :=
  let h := later_opening_service E rho hrec mono crossing services writes hgst hQ hQfg hexact hu
    (le_of_eq hq) hphase hx ht
  ⟨h.1, h.2.1⟩

-- O3 boundary q + 1 = rR: the opening HEAD v_(rR) = v_(q+1) is before d_q, and the
-- transfer still covers it.
example
    [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
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
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hgst : recoveryStart p E ≤ u)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q)
    (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hq1 : q + 1 = r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested) :
    SA.voteTime p.toParams (r * p.R) < SA.gateTime p.toParams q ∧
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z (r * p.R) = some K → Block.Preceq Q K := by
  have hd := p.deltaPos
  refine ⟨?_, (opening_transfer E rho hrec mono crossing services writes hgst hQ hQfg hexact hu
    (by omega) hphase).1⟩
  rw [← hq1]
  change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (q : Int) + 6 * p.Δ
  push_cast
  linarith

-- O4: the next opening serves an arbitrary selected body K of opening r; K has no
-- HonestProposal and its height is not used.
example
    [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
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
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hgst : recoveryStart p E ≤ u)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q)
    (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hqr : q ≤ r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime (r + 1)) m J contested)
    {y : V} {K : FGBlock (Fin p.n)} (hy : y ∈ rho.honest)
    (hK : actionSourceFG p c E rho y r = some (some K))
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (ht : rho.events[i]? = some (.tick x (p.actionTime (r + 1)))) :
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
      (p.actionTime (r + 1))).st
    ∃ D : FGBlock (Fin p.n),
      Gen.AC.Duty.GateService (fgsaAC E rho) i ((r + 1) * p.R) x (eraseFG D) ∧
      D ∈ domainR p st (treeT p st) ∧ FGBlock.Preceq K D ∧
      (frameR p st).lo ≤ (heightView p D).h :=
  next_opening_body_service E rho hrec mono crossing services writes hgst hQ hQfg hexact hu
    hqr hphase
    hy hK hx ht

-- O5: m = 1 at the exact TCommon premises, with the inline SO-COV body.
example
    [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
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
    {u : Time} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hgst : recoveryStart p E ≤ u)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q)
    (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hqr : q ≤ r * p.R)
    (hfirst : ∀ r', q ≤ r' * p.R → r ≤ r')
    (hphase : PhaseInterval p c E rho u (p.actionTime r) 1 J contested) :
    0 ≤ p.actionTime r - SA.gateTime p.toParams q ∧
    p.actionTime r - SA.gateTime p.toParams q ≤ P p - 4 * p.Δ ∧
    OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r 1 :=
  opening_height_one E rho hrec mono crossing services writes rowCoverage hgst hQ hQfg hexact hu hqr
    hfirst hphase

end Signatures

section Boundary

variable (p : Params)

-- q = 1 and R = 2: the first opening is r = 1 and the bound a_1 − d_1 = P − 4Δ is attained.
example (hR : p.R = 2) :
    (∀ r', 1 ≤ r' * p.R → 1 ≤ r') ∧
      p.actionTime 1 - SA.gateTime p.toParams 1 = P p - 4 * p.Δ ∧
      p.actionTime 1 - SA.gateTime p.toParams 1 ≤ P p - 4 * p.Δ := by
  refine ⟨fun r' h => ?_, ?_, (opening_first_time_bound (p := p) 1 1 (by rw [hR]; omega)
    (fun r' h => ?_)).2⟩
  · rw [hR] at h; omega
  · change 4 * p.Δ * ((1 * p.R : Nat) : Int) + 6 * p.Δ - (4 * p.Δ * ((1 : Nat) : Int) + 6 * p.Δ) =
      4 * (p.R : Int) * p.Δ - 4 * p.Δ
    rw [hR]
    push_cast
    ring
  · rw [hR] at h; omega

-- R = 2: the next opening label is at least rR + 2, so a body of rR reaches it by S1.
example (r : Nat) (hR : p.R = 2) : r * p.R + 2 ≤ (r + 1) * p.R := by
  rw [hR]; omega

-- Gap 3: the HEAD of q + 1 is before the gate d_q, so a transfer that starts after d_q
-- misses it.
example (q : Nat) : SA.voteTime p.toParams (q + 1) < SA.gateTime p.toParams q := by
  have hd := p.deltaPos
  change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (q : Int) + 6 * p.Δ
  push_cast
  linarith

end Boundary

section Falsification

/-! Plan §5 falsification candidates. None is a reachable Recovery₂ execution; each is
an invalid shortcut that the proofs above do not take.

* Old write + permission ⇒ OpeningCovered. A post-clock state can hold Q in its old fast
  set of label q and permit its height pair, but have an empty fresh set at rR or an
  expired Q lease; the selector is then empty. The proofs never reuse the lease of label q
  at rR: `opening_gateService_of_cover` builds fresh service from the ACTUAL raw result
  of the gate rR, and `openingSource_candidate_of_gateService` reads the fresh set of rR.
* Common ancestry ⇒ compatibility. Two branches A, B above Q at one height are not
  compatible (concrete check below). `opening_gate_guard` therefore proves each live
  lease compatible with the actual raw result C; for a lease above Q it shows target ⪯ C
  from the gate cover, not from Q ⪯ target.
* Send-once suppression. A record that already holds the same height pair emits no new
  row; the inline `rowCoverage` body gives an earlier-or-current row (rSent ≤ r).
* Kept-arm shortcut. Full-tree nonemptiness does not retain Qfg; `opening_domain_of_band`
  proves Qfg in the actual domain from the proposal band and the fixed phase frame. -/

-- Two children of one block at one slot are not compatible.
example :
    Block.preceq (.node .genesis 1 ⟨1⟩ 0) (.node (.node .genesis 1 ⟨1⟩ 0) 2 ⟨2⟩ 0) = true ∧
      Block.preceq (.node .genesis 1 ⟨1⟩ 0) (.node (.node .genesis 1 ⟨1⟩ 0) 2 ⟨3⟩ 1) = true ∧
      Block.compatible (.node (.node .genesis 1 ⟨1⟩ 0) 2 ⟨2⟩ 0) (.node (.node .genesis 1 ⟨1⟩ 0)
          2 ⟨3⟩ 1) =
        false := by
  decide

end Falsification

end AvailableChain.FGSA.Run.Tests.HealingOpening
end
