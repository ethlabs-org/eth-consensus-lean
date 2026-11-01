module
public import AvailableChainFGCompose.Proofs.Healing.CommonEntry
public import AvailableChainFGSAProofs.Proofs.Healing.CommonEntryFacts

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

/-! H-COMMON height branches and the second opening (plan §3F.3–4).
H-GATE supplies a retained source above Qfg at the first opening and above an actual
selected body K at the second opening. Each opening has its own phase premise. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private def p0d3_height_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private def p0d3_height_core (p : Params) {In : Type} (c : AppCodec In) :
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
private def p0d3_height_obs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d3_height_core p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private theorem p0d3_height_phase_eq (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (u v : Time) (m : Nat)
    (J : Option (FGBlock (Fin p.n))) (contested : Bool) :
    FGCompose.PhaseInterval (p0d3_height_core p c) E rho (p0d3_height_obs p c)
      u v m J contested = PhaseInterval p c E rho u v m J contested := by
  cases J <;> delta FGCompose.PhaseInterval PhaseInterval p0d3_height_obs R_at
    frameR storeAt FGCompose.timeIdx timeIdx <;> rfl

private theorem p0d3_height_tick (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {x : V} {r : Nat} {nd : Node p}
    (hnd : FGCompose.postClock E rho x (p.actionTime r) = some nd) :
    ∃ i, rho.events[i]? = some (.tick x (p.actionTime r)) ∧
      nd = (fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r) := by
  unfold FGCompose.postClock FGCompose.preTick at hnd
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none, reduceCtorEq] at hnd
  | some i =>
    simp only [hi, Option.map_some] at hnd
    exact ⟨i, V2.D.Run.tickIdx?_spec hi, (Option.some.inj hnd).symm⟩

section Service
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

include hrec mono crossing services writes

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9; plan §3F.3. DC: SAME each selected source extends Qfg and
its own height is capped by the first-opening phase. -/
theorem common_sources_extend_and_cap
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q) (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q) (hqr : q ≤ r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested) :
    ∀ x K, x ∈ rho.honest → actionSourceFG p c E rho x r = some (some K) →
      FGBlock.Preceq Qfg K ∧ (heightView p K).h ≤ m := by
  apply FGCompose.common_sources_extend_and_cap (p0d3_height_core p c) E rho
    (heightView p) (p0d3_height_timing p)
  · intro x nd hx hnd
    obtain ⟨i, ht, rfl⟩ := p0d3_height_tick E rho hnd
    exact later_opening_source_extends E rho hrec mono crossing services
      writes hready hQ hQfg hexact hu hqr hphase hx ht
  · exact fun x K hx hK =>
      common_source_height_le E rho hrec.base.valid.toScheduleWellFormed hphase hx hK

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9; plan §3F.3. DC: SAME a high Qfg fixes the first-opening
height and T_h.root by the plateau. -/
theorem common_entry_at_high
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q) (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q) (hqr : q ≤ r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested)
    (hh : (heightView p Qfg).h = m) : OpeningEntry p c E rho r m := by
  exact FGCompose.common_entry_at_high (p0d3_height_core p c) E rho
    (heightView p) (p0d3_height_timing p) p.E (fgCertificateLaws p).height
    (common_sources_extend_and_cap E rho hrec mono crossing services writes
      hready hQ hQfg hexact hu hqr hphase) hh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9; plan §3F.4. DC: INTENTIONAL with the new phase premise,
each source of the next opening extends the actual selected body K. Service for K
comes from next_opening_body_service; K needs no HonestProposal. -/
theorem common_next_sources_extend_and_cap
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q) (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q) (hqr : q ≤ r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime (r + 1)) m J contested)
    {y : V} {K : FGBlock (Fin p.n)} (hy : y ∈ rho.honest)
    (hK : actionSourceFG p c E rho y r = some (some K)) :
    ∀ x L, x ∈ rho.honest → actionSourceFG p c E rho x (r + 1) = some (some L) →
      FGBlock.Preceq K L ∧ (heightView p L).h ≤ m := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  apply FGCompose.common_next_sources_extend_and_cap (p0d3_height_core p c) E rho
    (heightView p) (p0d3_height_timing p)
  · intro x nd hx hnd
    obtain ⟨i, ht, rfl⟩ := p0d3_height_tick E rho hnd
    have hS := hrec.base.valid.toScheduleWellFormed
    obtain ⟨D, hserv, hdom, hKD, _⟩ := next_opening_body_service E rho hrec mono crossing
      services writes hready hQ hQfg hexact hu hqr hphase hy hK hx ht
    have hcut : E.t_GST ≤ slotStartZ p (((r + 1) * p.R : Nat) : Int) := by
      have hqrI : (q : Int) ≤ ((r * p.R : Nat) : Int) := by exact_mod_cast hqr
      have hrr : ((r * p.R : Nat) : Int) ≤ (((r + 1) * p.R : Nat) : Int) := by
        exact_mod_cast (Nat.mul_le_mul_right p.R (Nat.le_succ r))
      change E.t_GST ≤ 4 * p.Δ * (((r + 1) * p.R : Nat) : Int)
      change u ≤ 4 * p.Δ * (q : Int) at hu
      nlinarith [p.deltaPos]
    have enabled := healing_gate_enabled_of_recovery hrec.toRecovery₂ hx ht hphase.2.1 hcut
    have hcand := openingSource_candidate_of_gateService E rho hS i x (r + 1) (eraseFG D) ht
      enabled hserv
    obtain ⟨L', hL', hDL'⟩ := openingSource_extends_served E rho i x (r + 1) D hdom hcand
    exact ⟨D, L', hL', hKD, hDL'⟩
  · exact fun x L hx hL =>
      common_source_height_le E rho hrec.base.valid.toScheduleWellFormed hphase hx hL

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9; plan §3F.4. DC: INTENTIONAL an actual high witness at r
fixes the next opening's entry only under the phase through a_(r+1). -/
theorem common_next_entry
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q) (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q) (hqr : q ≤ r * p.R)
    {y : V} {K : FGBlock (Fin p.n)} (hy : y ∈ rho.honest)
    (hK : actionSourceFG p c E rho y r = some (some K)) (hh : (heightView p K).h = m)
    (hphase : PhaseInterval p c E rho u (p.actionTime (r + 1)) m J contested) :
    OpeningEntry p c E rho (r + 1) m := by
  exact FGCompose.common_next_entry (p0d3_height_core p c) E rho
    (heightView p) (p0d3_height_timing p) p.E (fgCertificateLaws p).height hh
    (common_next_sources_extend_and_cap E rho hrec mono crossing services writes
      hready hQ hQfg hexact hu hqr hphase hy hK)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9; plan §3F.3–4. DC: INTENTIONAL the low pivot gives either
one low entry or an actual high source with the conditional second-opening entry. -/
theorem common_entry_at_low
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q) (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q) (hqr : q ≤ r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested)
    (hh : (heightView p Qfg).h = m - 1) :
    OpeningEntry p c E rho r (m - 1) ∨
      ((∃ x K, x ∈ rho.honest ∧ actionSourceFG p c E rho x r = some (some K) ∧
          (heightView p K).h = m) ∧
        (PhaseInterval p c E rho u (p.actionTime (r + 1)) m J contested →
          OpeningEntry p c E rho (r + 1) m)) := by
  have h := FGCompose.common_entry_at_low (p0d3_height_core p c) E rho
    (heightView p) (p0d3_height_timing p) p.E (fgCertificateLaws p).height
    (p0d3_height_obs p c) (u := u) (J := J) (contested := contested) hh
    (common_sources_extend_and_cap E rho hrec mono crossing services writes
      hready hQ hQfg hexact hu hqr hphase)
    (fun y K hy hK hnext => common_next_sources_extend_and_cap E rho hrec mono
      crossing services writes hready hQ hQfg hexact hu hqr
      ((p0d3_height_phase_eq E rho u (p.actionTime (r + 1)) m J contested).mp hnext) hy hK)
  simp only [p0d3_height_phase_eq] at h
  exact h

end Service
end AvailableChain.FGSA.Run
end
