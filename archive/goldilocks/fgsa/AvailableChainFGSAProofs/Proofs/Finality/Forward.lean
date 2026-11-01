module
public import AvailableChainFGSAProofs.Proofs.Finality.Joined
public import AvailableChainFGSAClaims.Statements.Packages.Finality
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthReads
public import AvailableChainFGCompose.Proofs.Finality.Forward

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.KitFG

/-- Paper 22:1371–1400; firstfin plan §3, §5. DC-CS/W4FKChainSecondCheckpoint.lean:43:
INTENTIONAL forward opening, height increment and strict receipt. The existential
keeps all data in Prop and retains the kernel's Afg and U. -/
def ForwardWitness_W (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (g : Nat) (w : HealingWitness) (t : Time) : Prop :=
  ∃ (q r : Nat) (A : Block) (Afg U : FGBlock (Fin p.n)) (d : Nat) (D : Time),
    t ≤ (q : Time) * P p ∧ (q : Time) * P p < t + P p ∧
    Gen.Pure.InWindow q g r ∧
    Gen.Pure.FGoodE_W (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c))
      p.R (kappaF p ΔF) r ∧
    t ≤ (r : Time) * P p ∧ HonestProposal E rho (fgsaInterface p c) (r * p.R) A ∧
    eraseFG Afg = A ∧ OpeningCarrier_W p c E rho (r * p.R) A Afg ∧
    Afg.slot = r * p.R ∧ (heightView p Afg).h = d ∧ w.M + 1 ≤ d ∧
    FGBlock.Preceq Afg U ∧ Afg ≠ U ∧ (heightView p U).h = d + 1 ∧
    D = kernelDeadlineW p ΔF (r + 2) ∧ D < t + W_W p ΔF g ∧ D ≤ rho.horizon ∧
    ExactService p c E rho (r * p.R) A ∧
    SA.gateTime p.toParams (r * p.R) ≤ rho.horizon ∧
    (∀ x ∈ rho.honest,
      Block.Preceq (V2.D.Run.readAt E rho t x).st.base.stableRecord A) ∧
    ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x U D

/-- Paper 22:1371–1400; firstfin plan §3. DC: SAME forward witness fields. -/
theorem ForwardWitness_W_def (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (g : Nat) (w : HealingWitness) (t : Time) :
    ForwardWitness_W p c E rho ΔF g w t =
  (∃ (q r : Nat) (A : Block) (Afg U : FGBlock (Fin p.n)) (d : Nat) (D : Time),
    t ≤ (q : Time) * P p ∧ (q : Time) * P p < t + P p ∧
    Gen.Pure.InWindow q g r ∧
    Gen.Pure.FGoodE_W (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c))
      p.R (kappaF p ΔF) r ∧
    t ≤ (r : Time) * P p ∧ HonestProposal E rho (fgsaInterface p c) (r * p.R) A ∧
    eraseFG Afg = A ∧ OpeningCarrier_W p c E rho (r * p.R) A Afg ∧
    Afg.slot = r * p.R ∧ (heightView p Afg).h = d ∧ w.M + 1 ≤ d ∧
    FGBlock.Preceq Afg U ∧ Afg ≠ U ∧ (heightView p U).h = d + 1 ∧
    D = kernelDeadlineW p ΔF (r + 2) ∧ D < t + W_W p ΔF g ∧ D ≤ rho.horizon ∧
    ExactService p c E rho (r * p.R) A ∧
    SA.gateTime p.toParams (r * p.R) ≤ rho.horizon ∧
    (∀ x ∈ rho.honest,
      Block.Preceq (V2.D.Run.readAt E rho t x).st.base.stableRecord A) ∧
    ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x U D) := by rfl

/-- The SA slot clock as the shared FG timing (fieldwise, definitional). -/
private def d7bf_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem d7bf_timing_laws (p : Params) : FGCompose.FGTimingLaws (d7bf_timing p) where
  delta_pos := p.deltaPos
  rounds := p.RLarge
  proposal_eq s := by
    change 4 * p.Δ * (s : Time) = 4 * (s : Time) * p.Δ
    ring
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq _ := rfl

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- The local Finality window has nonnegative length. -/
theorem finality_window_nonneg (ΔF : Time) (g : Nat) : 0 ≤ W_W p ΔF g := by
  have hΔ : 0 ≤ p.Δ := p.deltaPos.le
  rw [W_W_def, betaF_def]
  change 0 ≤ ((g : Time) + 2) * (4 * (p.R : Time) * p.Δ) +
    4 * (kappaF p ΔF : Time) * p.Δ + p.Δ
  positivity

omit [DecidableEq V] [Fintype V] in
private theorem forward_timeIdx_le_gate {t a : Time} (hta : t < a) :
    timeIdx rho t ≤ afterTicksIdx rho a := by
  change (rho.events.filter (fun e => decide (e.time ≤ t))).length ≤
    (rho.events.filter (cutPred a)).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro e _ he
  exact decide_eq_true (Prod.Lex.toLex_le_toLex.mpr
    (Or.inl (lt_of_le_of_lt (of_decide_eq_true he) hta)))

private theorem forward_output_le {ΔF t : Time} {w : HealingWitness} {r : Nat} {A : Block}
    (hrec : Recovery₂ p c E rho G ΔF)
    (hs : V2.D.ScheduleWellFormed E rho) (input : HealingInput p c E rho w ΔF)
    (start : tstar p w ≤ t) (htr : t ≤ (r : Time) * P p)
    (ex : ExactService p c E rho (r * p.R) A)
    (hhor : SA.gateTime p.toParams (r * p.R) ≤ rho.horizon) :
    ∀ x ∈ rho.honest,
      Block.Preceq (V2.D.Run.readAt E rho t x).st.base.stableRecord A := by
  have hta : t < p.actionTime r := by
    rw [kmid_period_eq] at htr
    rw [kmid_actionTime_eq]
    have := p.deltaPos
    linarith
  have hidx := forward_timeIdx_le_gate p c rho hta
  have hsuffix : HealSuffix p c rho (tstar p w) (afterTicksIdx rho (p.actionTime r)) :=
    ⟨(fgsa_healSuffix_timeIdx E rho hs start).1.trans hidx,
      List.length_filter_le _ _⟩
  intro x hx
  have hstartHor : tstar p w ≤ rho.horizon := start.trans (htr.trans (by
    rw [kmid_period_eq]
    change 4 * p.Δ * ((r * p.R : Nat) : Int) ≤ rho.horizon
    change 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ ≤ rho.horizon at hhor
    linarith [p.deltaPos]))
  have hmono := input.healed.2.1 _ _ x
    (fgsa_healSuffix_timeIdx E rho hs start) hsuffix hidx
    (finality_input_suffix_confirmed p c E rho hrec input hx
      (fgsa_healSuffix_timeIdx E rho hs start) hstartHor)
    (finality_input_suffix_confirmed p c E rho hrec input hx hsuffix hstartHor)
  have hreader := finality_recovery_confirmed p c E rho hrec hx (r * p.R) _ _
    (by
      have hsync := input.wit.synchronous
      have hlow : (w.sStar : Int) + 2 ≤ (w.u : Int) := by
        exact_mod_cast input.wit.proposal_lower
      have hst := start.trans htr
      rw [kmid_period_eq] at hst
      change 4 * p.Δ * (w.u : Int) + 6 * p.Δ ≤ _ at hst
      change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hsync
      change E.t_GST ≤ 4 * p.Δ * _
      nlinarith [p.deltaPos]) le_rfl hhor
    (fun j hj => kmid_tick_lt_afterTicks p c E rho hs hj le_rfl)
  have hstable := (ex.2 hhor x hx hreader).2.2.2.1
  rw [afterTicks_eq_stateBefore E rho hs] at hstable
  have hout := fgsa_outputAt_eq_S_at E rho hs (fgsaInterface p c).stable
    (by simp) x t
  change (V2.D.Run.readAt E rho t x).st.base.stableRecord = _ at hout
  rw [hout]
  exact hstable ▸ hmono

/-- Paper 22:1371–1400; firstfin plan §5 A. DC-CS/W4FKChainSecondCheckpoint.lean:43:
INTENTIONAL full FE guard and actual opening. K-JOIN is applied once; its Afg/U
are retained with high-A, exact gate service and each inclusive output bound. -/
theorem forward_witness_FE_of
    (hServices : FinalityActionReceipts p c E rho)
    (G ΔF : Time) (g : Nat) (w : HealingWitness)
    (hδ : p.δt = 2 * p.R) (pt : PtT)
    (h : FinalityLivenessPrem_W p c G ΔF .recFE g w E rho pt)
    (hsel : TRowsSelect p c E rho)
    (horigin : ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : BatchCoverage p ΔF .target)
    (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hI3 : FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2) :
    ForwardWitness_W p c E rho ΔF g w pt.t := by
  have ht : 0 < pt.t := by
    have hd := p.deltaPos
    have hu := Int.natCast_nonneg w.u
    have hs := h.start
    change 4 * p.Δ * (w.u : Time) + 6 * p.Δ ≤ pt.t at hs
    nlinarith
  have hstart := (finality_healing_recoveryStart p c E rho h.input).trans h.start
  have hrec : FE_W p ΔF (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c))
      (recoveryStart p E) rho.horizon g := h.set.recur
  obtain ⟨q, r, htq, hqt, hr, hgood, htr, hD, hhor⟩ :
      ∃ q r : Nat, pt.t ≤ (q : Time) * P p ∧ (q : Time) * P p < pt.t + P p ∧
        Gen.Pure.InWindow q g r ∧
        Gen.Pure.FGoodE_W (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c))
          p.R (kappaF p ΔF) r ∧
        pt.t ≤ (r : Time) * P p ∧ kernelDeadlineW p ΔF (r + 2) < pt.t + W_W p ΔF g ∧
        kernelDeadlineW p ΔF (r + 2) ≤ rho.horizon :=
    FGCompose.forward_round_FE (d7bf_timing p) (d7bf_timing_laws p) hrec ht hstart h.hhor
  let kpt : KernelPt := ⟨w, r⟩
  have hK : KernelPrem_W p c G ΔF E rho kpt := {
    set := h.set.core.toRecovery₂, bound := h.set.bound, window := hgood
    start := h.start.trans htr, hhor := hhor, input := h.input
    services := fgsa_coreServices E rho h.set.core.base w
      (finality_vote_receipts h.set.core.toRecovery₂) }
  have hs := h.set.core.base.valid.toScheduleWellFormed
  obtain ⟨A, hA⟩ := kmid_window_proposal hK hgood.1 le_rfl
    (Nat.mul_le_mul_right _ (by omega : r ≤ r + 2))
  have hJ : KernelJoinedPrem p c G ΔF E rho ⟨r⟩ := {
    set := h.set.core.toRecovery₂, bound := h.set.bound, window := hgood
    start := ⟨w, h.input, h.start.trans htr⟩, hhor := hhor }
  obtain ⟨Afg, heA, hcA, _, U, hAU, hne, hU, hacc⟩ :=
    finality_kernel_joined_W_of p c E rho hServices G ΔF hδ ⟨r⟩ hJ
      hsel horigin hBatch hQC hXing hI3 hStrat hEmittedSource hcapBefore A hA
  obtain ⟨A₀, he₀, _, hslot, _⟩ := kmid_opening_carrier p c E rho hs hA
  have hsame : A₀ = Afg := kmid_eraseFG_inj p (he₀.trans heA.symm)
  subst A₀
  have exA := kmid_window_exact hK hA le_rfl
  have hhA := kmid_slot_horizon hK
    (Nat.mul_le_mul_right _ (by omega : r ≤ r + 2))
  obtain ⟨_, y₀, _, C₀, hrow₀, _, hsrc₀, _, hC₀⟩ := h.input.wit.fresh
  have hpre := h.input.t.h2 y₀ w.rStar C₀ (r * p.R) A
    ((HonestRowAt_def p c E rho _ _ _ _).mp hrow₀).1 hsrc₀
    (show w.M + 1 ≤ (heightView p C₀).h by rw [hC₀]) hA
    (by rw [← h.input.wit.label]; exact (kmid_kernel_bounds hK).2.2.2.2.1)
  rw [← heA, eraseFG_parent] at hpre
  have highA : w.M + 1 ≤ (heightView p Afg).h := by
    have h1 := (fgCertificateLaws p).height.h_mono (kmid_lift_preceq p hpre)
    have h2 := (fgCertificateLaws p).height.h_mono (kmid_parent_preceq p Afg)
    rw [hC₀] at h1
    exact h1.trans h2
  exact ⟨q, r, A, Afg, U, (heightView p Afg).h, kernelDeadlineW p ΔF (r + 2),
    htq, hqt, hr, hgood, htr, hA, heA, hcA, hslot, rfl, highA, hAU, hne, hU,
    rfl, hD, hhor, exA, hhA.2.2,
    forward_output_le p c E rho h.set.core.toRecovery₂ hs h.input h.start htr exA hhA.2.2, hacc⟩

end AvailableChain.FGSA.Run
end
