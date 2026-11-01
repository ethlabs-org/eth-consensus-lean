module
public import AvailableChainFGSAProofs.Proofs.Healing.CommonEntryHeight
public import AvailableChainFGSAProofs.Proofs.Healing.OpeningServiceOne
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

/-! H-COMMON: the frozen TCommon conjunction (blueprint 21 H.9; plan §3F.5).
Standing inputs are Recovery₂, RMono, RXing, the B27 last-write body, and SO-COV row
coverage. Assembly supplies the two INLINE facts. No sourceBodies premise is used. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

section Common
variable [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (services : OpeningServiceScopes E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
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

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9:1131–1144; plan §3E. DC: SAME H-GATE gives OpeningCovered
at every opening in the phase, including q = rR, with earlier-or-current signed rows. -/
theorem common_opening_covered
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q) (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q) (hqr : q ≤ r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested) :
    OpeningCovered p c E rho r Q :=
  later_opening_covered E rho hrec mono crossing services writes rowCoverage hready hQ hQfg
    hexact hu hqr
    hphase

omit rowCoverage in
/-- The actual opening fast write supplies the same-label retained receipt scope. -/
theorem common_sameLabel_scope
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q) (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q) (hqr : q ≤ r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested) :
    SameLabelServiceScope E rho (r * p.R) := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hn := card_eq_n_of_linked hrec.base.linked
  have hc : (Gen.V2.Duty.faulty rho).card + rho.honest.card = p.n := by
    rw [Gen.V2.Duty.faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hn]
    have hle := Finset.card_le_univ rho.honest
    rw [hn] at hle
    omega
  have hf := hrec.fault
  have hp := p.nPos
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < rho.honest.card by omega)
  have hqrI : (q : Int) ≤ ((r * p.R : Nat) : Int) := by exact_mod_cast hqr
  have hur : u ≤ SA.voteTime p.toParams (r * p.R) := by
    change u ≤ 4 * p.Δ * ((r * p.R : Nat) : Int) + p.Δ
    change u ≤ 4 * p.Δ * (q : Int) at hu
    nlinarith [p.deltaPos]
  have har : SA.voteTime p.toParams (r * p.R) ≤ p.actionTime r := by
    change 4 * p.Δ * ((r * p.R : Nat) : Int) + p.Δ ≤
      4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨i, ht⟩ := opening_action_tick E rho hs hrec.base.delta hx r hphase.2.1
    (hrec.awake x hx _ (hGST.trans (hur.trans har)) hphase.2.1)
  obtain ⟨K, hsrc, _⟩ := later_opening_source_extends E rho hrec mono crossing services writes
    hready hQ hQfg hexact hu hqr hphase hx ht
  have hnd := opening_postClock_of_tick E rho hs ht
  have hK : actionSourceFG p c E rho x r = some (some K) := by
    rw [actionSourceFG_def, hnd]
    exact congrArg some hsrc
  obtain ⟨_, _, _, hfw⟩ := opening_source_body E rho hs ht hK
  exact healing_recovery_same_label E rho hrec (r * p.R) (hGST.trans hur)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9:1100–1144, bp.commonEntry.v1; plan §3F.5.
DC: INTENTIONAL TCommon from its displayed hypotheses, in the frozen order.
INLINE producers at Assembly: fgsa_leaseOrigins_lastWrite (writes) and
rowPermission_covered (rowCoverage). The second opening has its own phase premise. -/
theorem healing_tCommon : TCommon p c E rho := by
  intro u m J contested q Q Qfg r hgst hQ hQfg hexact hu hqr hfirst hphase
  obtain ⟨h0, h1⟩ := common_first_time_bound (p := p) q r hqr hfirst
  exact ⟨h0, h1,
    common_opening_covered E rho hrec mono crossing services writes rowCoverage hgst hQ hQfg
      hexact hu
      hqr hphase,
    common_sources_compatible E rho hrec.toRecovery₂
      (common_sameLabel_scope E rho hrec mono crossing services writes
        hgst hQ hQfg hexact hu hqr hphase) hgst hu hqr hphase,
    common_entry_at_high E rho hrec mono crossing services writes hgst hQ hQfg hexact hu hqr hphase,
    common_entry_at_low E rho hrec mono crossing services writes hgst hQ hQfg hexact hu hqr hphase⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9 at m = 1; plan §4 handoff. DC: SAME time, covered sources,
and one height-one entry in the exact TCommon premise shape. This reuses H-GATE. -/
theorem common_height_one
    {u : Time} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q) (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q) (hqr : q ≤ r * p.R)
    (hfirst : ∀ r', q ≤ r' * p.R → r ≤ r')
    (hphase : PhaseInterval p c E rho u (p.actionTime r) 1 J contested) :
    0 ≤ p.actionTime r - SA.gateTime p.toParams q ∧
      p.actionTime r - SA.gateTime p.toParams q ≤ P p - 4 * p.Δ ∧
      OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r 1 :=
  opening_height_one E rho hrec mono crossing services writes rowCoverage hready hQ hQfg hexact
    hu hqr
    hfirst hphase

end Common
end AvailableChain.FGSA.Run
end
