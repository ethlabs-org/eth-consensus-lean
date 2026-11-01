module
public import AvailableChainFGSAClaims.Claims.OutageContinuation
public import AvailableChainFGSAClaims.Claims.Outage
public import AvailableChainFGSAClaims.Claims.WeakContinuation
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSAClaims.Claims.Healing
public import AvailableChainFGSAClaims.Claims.Finality
public import AvailableChainFGSAProofs.Proofs.Shared.Healed
public import AvailableChainFGSAClaims.Claims.Foundations
public import AvailableChainFGSAClaims.Claims.Clean
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthCausal
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthProposal
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthReads

/-! Holds claim → claim implications only; its Claims/* imports are an exact L42 exception.
P3 r3.5.8 R5-66. -/

public section

namespace AvailableChain.FGSA.Run

variable {ΔF : Time}
open Gen.Pure (CompatOn MonoOn)

variable {p : Params}

/-- The family-(0) client claim follows from the Linked-only claim. -/
theorem clientSafety_base (h : ClientSafetyClaim p) : ClientSafetyBaseClaim p :=
  fun c E rho _ hb => h c E rho hb.set.linked

theorem cleanHistory_of_cut (h : CleanCutClaim p) : CleanHistoryClaim p :=
  fun c E rho _ pt hc => (h c E rho pt ⟨hc.set.sleepPre⟩).1

theorem cleanPrefixTruncation_of_cut (h : CleanCutClaim p) : CleanPrefixTruncationClaim p :=
  fun c E rho _ pt hc => (h c E rho pt ⟨hc.set.sleepPre⟩).2

theorem cleanSafety_outputs (h : CleanSafetyClaim p)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {pt : Unit}
    (hc : CleanPrem p c E rho pt ΔF) :
    ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      ScopedCompat (confirmedReader p c E rho) (fun t x => V2.D.outputAt E rho g x t)
        (fun _ => True) ∧
      ScopedMono (confirmedReader p c E rho) (fun t x => V2.D.outputAt E rho g x t)
        (fun _ => True) :=
  (h c E rho pt hc).2.2

/-- Blueprint 21 H.20–H.22; f07w-rulings S4.5 DEFAULT REVISED.
DC: additive internal corollary, not a standalone frozen healing claim.
HTimeConcl supplies the input and both bound links. Restrict its healed suffix
to GST + B_HF; no recovery or service premise is added. -/
theorem uniformHealing_of_hTimeConcl (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G ΔF : Time) (h : HTimeConcl p c E rho G ΔF) :
    Healed p c E rho (recoveryStart p E + B_HF p ΔF G) := by
  obtain ⟨w, input, start, bound⟩ := h
  exact healed_mono_start p c E rho (start.trans bound.le) input.healed

private theorem fgsa_gst_window_nonneg (p : Params) (ΔF : Time) (g : Nat) :
    0 ≤ W_W p ΔF g := by
  have hΔ : 0 ≤ p.Δ := p.deltaPos.le
  rw [W_W_def, betaF_def]
  change 0 ≤ ((g : Time) + 2) * (4 * (p.R : Time) * p.Δ) +
    4 * (kappaF p ΔF : Time) * p.Δ + p.Δ
  positivity

private theorem claims_acceptsFinalBefore_mono_deadline (p : Params)
    {In V : Type} [DecidableEq V] (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hs : V2.D.ScheduleWellFormed E rho)
    {x : V} {X : SimplexFG.FGBlock (Fin p.n)} {d d' : Time}
    (hdd : d ≤ d') (h : AcceptsFinalBefore p c E rho x X d) :
    AcceptsFinalBefore p c E rho x X d' := by
  have hr : ∀ nd t, SimplexFG.FGBlock.Preceq X nd.st.fg.F →
      SimplexFG.FGBlock.Preceq X ((fgsa p c).restore ((fgsa p c).durable nd) t).st.fg.F := by
    intro nd t hp
    change SimplexFG.FGBlock.Preceq X (acRestart p nd.st t).fg.F
    rwa [acRestart_fg]
  obtain ⟨i, hi, hb, hX⟩ :=
    (Gen.V2.Duty.holdsBefore_iff_exists_idx_restore hs (fgsa_monoAlong_preceq_F p c X) hr).mp h
  apply (Gen.V2.Duty.holdsBefore_iff_exists_idx_restore hs
    (fgsa_monoAlong_preceq_F p c X) hr).mpr
  refine ⟨i, hi, ?_, hX⟩
  intro k hk
  obtain ⟨e, he, ht⟩ := hb k hk
  exact ⟨e, he, ht.trans_le hdd⟩

private theorem claims_h0_ready {In V : Type} [DecidableEq V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {w : HealingWitness} (h : H0 p c E rho w) : recoveryStart p E ≤ tstar p w := by
  obtain ⟨j, y, a, C, ha, hn, _, _, hh⟩ := h.fresh
  have hrow : w.u₀ < p.actionTime w.rStar := by
    by_contra he
    have hc := h.rowCap j y w.rStar a (w.M + 1) (heightView p C).T_h.root
      (p.actionTime w.rStar) ha ha.2.1 (le_of_not_gt he) hn
    change w.M + 1 ≤ w.M at hc
    omega
  have hp : 0 ≤ P p := by
    have := p.deltaPos
    change 0 ≤ 4 * (p.R : Time) * p.Δ
    positivity
  have hu := h.proposal_lower
  rw [h.label] at hu
  have hu' : ((w.rStar * p.R : Nat) : Time) + 2 ≤ (w.u : Time) := by
    exact_mod_cast hu
  have hd := p.deltaPos
  have ht : p.actionTime w.rStar ≤ tstar p w := by
    rw [tstar_def]
    change 4 * p.Δ * ((w.rStar * p.R : Nat) : Time) + 6 * p.Δ ≤
      4 * p.Δ * (w.u : Time) + 6 * p.Δ
    nlinarith
  exact (le_add_of_nonneg_right (mul_nonneg (by decide) hp)).trans
    (h.cut_lower.trans (hrow.le.trans ht))

private theorem fgsa_firstFinality_form (form : FinFormW) (hH : HTimeClaim p)
    (hL : ∀ (G ΔF : Time) (g : Nat) (w : HealingWitness) (_hδ : p.δt = 2 * p.R)
      {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtT),
      FinalityLivenessPrem_W p c G ΔF form g w E rho pt →
      FinalityLivenessConcl_W p c E rho pt.t (pt.t + W_W p ΔF g)) :
    ∀ (G ΔF : Time) (g : Nat) (_hδ : p.δt = 2 * p.R)
      {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
      FirstFinalityPrem_W p c G ΔF form g E rho pt →
      FirstFinalityConcl_W p c E rho ΔF G
        (recoveryStart p E + B_HF p ΔF G + W_W p ΔF g) := by
  intro G ΔF g hδ V _ _ In c E rho pt h
  have hW := fgsa_gst_window_nonneg p ΔF g
  have hhor : recoveryStart p E + B_HF p ΔF G ≤ rho.horizon :=
    (le_add_of_nonneg_right hW).trans h.hhor
  obtain ⟨w, input, start, bound⟩ := hH G ΔF hδ c E rho ()
    ⟨⟨h.set.core, h.set.bound⟩, hhor⟩
  have hstar := start.trans_lt bound
  have hdeadline : tstar p w + W_W p ΔF g ≤ recoveryStart p E + B_HF p ΔF G + W_W p ΔF g :=
    Int.add_le_add_right hstar.le _
  obtain ⟨U, hS, hF, haccept⟩ := hL G ΔF g w hδ c E rho ⟨tstar p w⟩
    ⟨h.set, input, le_rfl, hdeadline.trans h.hhor⟩
  refine ⟨w, input, hstar, U, hS, hF, ?_⟩
  intro x hx
  exact claims_acceptsFinalBefore_mono_deadline p c E rho
    h.set.core.base.valid.toScheduleWellFormed hdeadline (haccept x hx)

/-- Blueprint 22:1382–1384; FirstFinality plan §8. DC: INTENTIONAL GST form;
DC finalized (Generic/Claims.lean:39–44). H-time supplies one witness;
local liveness at tstar keeps its comparisons and uses the later GST deadline. -/
theorem fgsa_firstFinality_recFE (hH : HTimeClaim p)
    (hL : FinalityLivenessRecFEClaim_W p) : FirstFinalityRecFEClaim_W p := by
  exact fgsa_firstFinality_form .recFE hH hL

/-- Blueprint 22:1382–1384; FirstFinality plan §8. DC: INTENTIONAL GST form;
DC finalized (Generic/Claims.lean:39–44). H-time supplies one witness;
local liveness at tstar keeps its comparisons and uses the later GST deadline. -/
theorem fgsa_firstFinality_recF4 (hH : HTimeClaim p)
    (hL : FinalityLivenessRecF4Claim_W p) : FirstFinalityRecF4Claim_W p := by
  exact fgsa_firstFinality_form .recF4 hH hL

/-- Blueprint 22:1371–1380. DC: INTENTIONAL GST form; no healing output as premise;
DC finalized (Generic/Claims.lean:39–44). H-time and the local claim supply the result. -/
theorem fgsa_finalityLivenessGST_recFE (hH : HTimeClaim p)
    (hL : FinalityLivenessRecFEClaim_W p) (hP : ProposalFinalRecFEClaim_W p)
    (hDC : LiveDCFromWindowsStatement p) : FinalityLivenessGSTClaim_W p .recFE := by
  intro G ΔF g hδ V _ _ In c E rho pt h
  have hW := fgsa_gst_window_nonneg p ΔF g
  have hhor : recoveryStart p E + B_HF p ΔF G ≤ rho.horizon :=
    h.late.trans ((le_add_of_nonneg_right hW).trans h.hhor)
  obtain ⟨w, input, start, bound⟩ := hH G ΔF hδ c E rho ()
    ⟨⟨h.set.core, h.set.bound⟩, hhor⟩
  have ht : tstar p w ≤ pt.t := start.trans (bound.le.trans h.late)
  have hlocal := hL G ΔF g w hδ c E rho pt ⟨h.set, input, ht, h.hhor⟩
  refine ⟨w, input, start.trans_lt bound, hlocal, ?_⟩
  intro hlong
  apply hDC c E rho G ΔF g pt.t h.set.core ((claims_h0_ready input.wit).trans ht) ?_ ?_ hlong
  · obtain ⟨U, hU, _, ha⟩ := hlocal
    exact ⟨U, hU, ha⟩
  · intro s X hp hts hsHor
    exact hP G ΔF g w hδ c E rho ⟨s, X⟩ ⟨h.set, input, hp, ht.trans hts, hsHor⟩

/-- Blueprint 22:1371–1380. DC: INTENTIONAL GST form; no healing output as premise;
DC finalized (Generic/Claims.lean:39–44). H-time and the local claim supply the result. -/
theorem fgsa_finalityLivenessGST_recF4 (hH : HTimeClaim p)
    (hL : FinalityLivenessRecF4Claim_W p) (hP : ProposalFinalRecF4Claim_W p)
    (hDC : LiveDCFromWindowsStatement p) : FinalityLivenessGSTClaim_W p .recF4 := by
  intro G ΔF g hδ V _ _ In c E rho pt h
  have hW := fgsa_gst_window_nonneg p ΔF g
  have hhor : recoveryStart p E + B_HF p ΔF G ≤ rho.horizon :=
    h.late.trans ((le_add_of_nonneg_right hW).trans h.hhor)
  obtain ⟨w, input, start, bound⟩ := hH G ΔF hδ c E rho ()
    ⟨⟨h.set.core, h.set.bound⟩, hhor⟩
  have ht : tstar p w ≤ pt.t := start.trans (bound.le.trans h.late)
  have hlocal := hL G ΔF g w hδ c E rho pt ⟨h.set, input, ht, h.hhor⟩
  refine ⟨w, input, start.trans_lt bound, hlocal, ?_⟩
  intro hlong
  apply hDC c E rho G ΔF g pt.t h.set.core ((claims_h0_ready input.wit).trans ht) ?_ ?_ hlong
  · obtain ⟨U, hU, _, ha⟩ := hlocal
    exact ⟨U, hU, ha⟩
  · intro s X hp hts hsHor
    exact hP G ΔF g w hδ c E rho ⟨s, X⟩ ⟨h.set, input, hp, ht.trans hts, hsHor⟩

/-- Blueprint 22:1421–1430. DC: INTENTIONAL GST form; no healing output as premise;
DC finalized (Generic/Claims.lean:39–44). H-time and the local claim supply the result. -/
theorem fgsa_proposalFinalGST_recFE (hH : HTimeClaim p)
    (hL : ProposalFinalRecFEClaim_W p) : ProposalFinalGSTClaim_W p .recFE := by
  intro G ΔF g hδ V _ _ In c E rho pt h
  have hW := fgsa_gst_window_nonneg p ΔF g
  have hhor : recoveryStart p E + B_HF p ΔF G ≤ rho.horizon :=
    h.late.trans ((le_add_of_nonneg_right hW).trans h.hhor)
  obtain ⟨w, input, start, bound⟩ := hH G ΔF hδ c E rho ()
    ⟨⟨h.set.core, h.set.bound⟩, hhor⟩
  refine ⟨w, input, start.trans_lt bound, hL G ΔF g w hδ c E rho pt ?_⟩
  exact ⟨h.set, input, h.prop, start.trans (bound.le.trans h.late), h.hhor⟩

/-- Blueprint 22:1421–1430. DC: INTENTIONAL GST form; no healing output as premise;
DC finalized (Generic/Claims.lean:39–44). H-time and the local claim supply the result. -/
theorem fgsa_proposalFinalGST_recF4 (hH : HTimeClaim p)
    (hL : ProposalFinalRecF4Claim_W p) : ProposalFinalGSTClaim_W p .recF4 := by
  intro G ΔF g hδ V _ _ In c E rho pt h
  have hW := fgsa_gst_window_nonneg p ΔF g
  have hhor : recoveryStart p E + B_HF p ΔF G ≤ rho.horizon :=
    h.late.trans ((le_add_of_nonneg_right hW).trans h.hhor)
  obtain ⟨w, input, start, bound⟩ := hH G ΔF hδ c E rho ()
    ⟨⟨h.set.core, h.set.bound⟩, hhor⟩
  refine ⟨w, input, start.trans_lt bound, hL G ΔF g w hδ c E rho pt ?_⟩
  exact ⟨h.set, input, h.prop, start.trans (bound.le.trans h.late), h.hhor⟩

/-- Blueprint 22:1434–1451. DC: INTENTIONAL GST form; no healing output as premise;
DC finalized (Generic/Claims.lean:39–44). H-time and the local claim supply the result. -/
theorem fgsa_aboveFrontierGST_recFE (hH : HTimeClaim p)
    (hL : AboveFrontierRecFEClaim_W p) : AboveFrontierGSTClaim_W p .recFE := by
  intro G ΔF g hδ V _ _ In c E rho pt h
  have hW := fgsa_gst_window_nonneg p ΔF g
  have hhor : recoveryStart p E + B_HF p ΔF G ≤ rho.horizon :=
    h.late.trans ((le_add_of_nonneg_right (mul_nonneg (by decide) hW)).trans h.hhor)
  obtain ⟨w, input, start, bound⟩ := hH G ΔF hδ c E rho ()
    ⟨⟨h.set.core, h.set.bound⟩, hhor⟩
  refine ⟨w, input, start.trans_lt bound, hL G ΔF g w hδ c E rho pt ?_⟩
  have hsecond : pt.t + W_W p ΔF g + W_W p ΔF g ≤ rho.horizon := by
    simpa only [two_mul, ← add_assoc] using h.hhor
  exact ⟨h.set, input, start.trans (bound.le.trans h.late),
    (le_add_of_nonneg_right hW).trans hsecond, hsecond⟩

/-- Blueprint 22:1434–1451. DC: INTENTIONAL GST form; no healing output as premise;
DC finalized (Generic/Claims.lean:39–44). H-time and the local claim supply the result. -/
theorem fgsa_aboveFrontierGST_recF4 (hH : HTimeClaim p)
    (hL : AboveFrontierRecF4Claim_W p) : AboveFrontierGSTClaim_W p .recF4 := by
  intro G ΔF g hδ V _ _ In c E rho pt h
  have hW := fgsa_gst_window_nonneg p ΔF g
  have hhor : recoveryStart p E + B_HF p ΔF G ≤ rho.horizon :=
    h.late.trans ((le_add_of_nonneg_right (mul_nonneg (by decide) hW)).trans h.hhor)
  obtain ⟨w, input, start, bound⟩ := hH G ΔF hδ c E rho ()
    ⟨⟨h.set.core, h.set.bound⟩, hhor⟩
  refine ⟨w, input, start.trans_lt bound, hL G ΔF g w hδ c E rho pt ?_⟩
  have hsecond : pt.t + W_W p ΔF g + W_W p ΔF g ≤ rho.horizon := by
    simpa only [two_mul, ← add_assoc] using h.hhor
  exact ⟨h.set, input, start.trans (bound.le.trans h.late),
    (le_add_of_nonneg_right hW).trans hsecond, hsecond⟩

private theorem claims_recoveryStart_lower {V : Type} (E : Generic.Env V) :
    E.t_GST + 6 * p.Δ ≤ recoveryStart p E := by
  let a := max 0 E.t_GST + 4 * p.Δ - 1
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have ha : 0 ≤ a := by
    have hdelta : 1 ≤ p.Δ := by have := p.deltaPos; dsimp [Time] at *; omega
    dsimp [a]
    linarith [le_max_left 0 E.t_GST]
  have hq := Int.ediv_nonneg ha hd.le
  have hm := Int.emod_lt_of_pos a hd
  have he := Int.mul_ediv_add_emod a (4 * p.Δ)
  change E.t_GST + 6 * p.Δ ≤ 4 * p.Δ * ((a / (4 * p.Δ)).toNat : Int) + 6 * p.Δ
  rw [Int.toNat_of_nonneg hq]
  dsimp [a] at he hm
  dsimp [Time] at *
  nlinarith [le_max_right 0 E.t_GST]

private theorem claims_prefixTime_bounds {In V : Type}
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {j i : Nat} {x : V} {a t : Time}
    (hj : rho.events[j]? = some (.tick x a)) (hji : j < i) (hi : i ≤ rho.events.length)
    (ht : ∀ k < i, ∀ e, rho.events[k]? = some e → e.time ≤ t) :
    a ≤ prefixTime rho i ∧ prefixTime rho i ≤ t := by
  have hl : i - 1 < rho.events.length := by omega
  have he : (rho.events.take i).getLast? = some rho.events[i - 1] := by
    rw [List.getLast?_eq_getElem?]
    simp only [List.length_take, min_eq_left hi]
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hl]
  have hp : prefixTime rho i = rho.events[i - 1].time := by
    change ((rho.events.take i).getLast?.map (fun e => e.time)).getD 0 = _
    rw [he]
    rfl
  rw [hp]
  refine ⟨?_, ht (i - 1) (by omega) _ (List.getElem?_eq_getElem hl)⟩
  rcases (show j ≤ i - 1 by omega).lt_or_eq with hlt | rfl
  · obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
    have hsort := List.pairwise_iff_getElem.mp hs.sorted j (i - 1) hjl hl hlt
    rw [hje] at hsort
    exact V2.D.Engine.time_le_of_key_le _ _ hsort
  · have heq := Option.some.inj ((List.getElem?_eq_getElem hl).symm.trans hj)
    rw [heq]
    exact le_rfl

private theorem claims_recovery_readers {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {j i : Nat} {x : V} {s : Slot} {t : Time}
    (hx : x ∈ rho.honest) (hj : IsGateTick p c rho j x s)
    (hji : j < i) (_hi : i ≤ rho.events.length)
    (hgst : E.t_GST ≤ slotStartZ p (s : Int))
    (ht : SA.gateTime p.toParams s ≤ t) (hh : t ≤ rho.horizon)
    (hp : SA.gateTime p.toParams s ≤ prefixTime rho i ∧ prefixTime rho i ≤ t)
    (hw : WakesAppliedAtIdx E rho x i t) :
    confirmedReaderAtIdx p c E rho x i t ∧ confirmedReaderIdx p c E rho x i := by
  have hb (k : Nat) : ∀ w, (storeAt p c E rho k x).restartTime = some w →
      w ≤ slotStartZ p (s : Int) := by
    apply fgsa_restartTime_bound E rho k x _
    intro q w _ he
    by_contra hn
    have hwh := (hrec.base.valid.in_horizon _ (List.mem_of_getElem? he)).2
    change w ≤ rho.horizon at hwh
    exact hrec.suffixNoRestart x hx q w he (hgst.trans_lt (lt_of_not_ge hn))
      (by dsimp [Time] at *; omega)
  have hg : enabledGateAt p c E rho j x s := by
    refine ⟨hj, ?_⟩
    cases he : (storeAt p c E rho j x).restartTime with
    | none => trivial
    | some w => exact hb j w he
  have hstart : slotStartZ p (s : Int) ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hc (u : Time) (hgu : SA.gateTime p.toParams s ≤ u) (hut : u ≤ t) :
      confirmedReaderAtIdx p c E rho x i u := by
    refine ⟨hx, hrec.awake x hx u (hgst.trans (hstart.trans hgu)) (hut.trans hh), ?_⟩
    cases he : (storeAt p c E rho i x).restartTime with
    | none => trivial
    | some w =>
      refine ⟨s, j, hb i w he, hgu, hji, hg, ?_, ?_⟩
      · intro v _ hsv hvu
        exact hrec.awake x hx v (hgst.trans hsv) (hvu.trans (hut.trans hh))
      · intro v hsv hvu hm
        obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp hm
        exact hrec.suffixNoRestart x hx q v hq (hgst.trans_lt hsv)
          (by dsimp [Time] at *; omega)
  refine ⟨hc t ht le_rfl, hc _ hp.1 hp.2, ?_⟩
  intro w hw0 hwp hW
  exact hw w hw0 (hwp.trans hp.2) hW

private theorem claims_recovery_cut_readers {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {w : HealingWitness}
    (h0 : H0 p c E rho w) (t : Time) (phase : Nat) (hphase : 1 ≤ phase)
    (ht : tstar p w ≤ t) (hh : t ≤ rho.horizon) (x : V) (hx : x ∈ rho.honest) :
    let i := (rho.events.filter (fun e => decide (e.key ≤ toLex (t, phase)))).length
    confirmedReaderAtIdx p c E rho x i t ∧ confirmedReaderIdx p c E rho x i := by
  intro i
  have hs := hrec.base.valid.toScheduleWellFormed
  have hready := claims_h0_ready h0
  have hlo := claims_recoveryStart_lower (p := p) E
  have hcut : E.t_GST ≤ slotStartZ p (w.u : Int) := by
    rw [tstar_def] at hready
    change recoveryStart p E ≤ 4 * p.Δ * (w.u : Time) + 6 * p.Δ at hready
    change E.t_GST ≤ 4 * p.Δ * (w.u : Time)
    linarith
  have heq : ((4 * w.u + 6 : Nat) : Time) * p.Δ = tstar p w := by
    rw [tstar_def]
    change ((4 * w.u + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (w.u : Time) + 6 * p.Δ
    push_cast
    ring
  have hst : E.t_GST ≤ tstar p w := h0.after_gst
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hs hrec.base.delta x hx
    (4 * w.u + 6) (heq ▸ ht.trans hh) (heq ▸ hrec.awake x hx _ hst (ht.trans hh))
  rw [heq] at hj
  have hji : j < i := by
    by_contra hn
    have hf := V2.D.Engine.filter_false_of_index_ge hs
      (fun e => decide (e.key ≤ toLex (t, phase)))
      (fun e f hef hf => decide_eq_true (hef.trans (of_decide_eq_true hf)))
      (Nat.le_of_not_gt hn) hj
    have hk : (V2.Event.tick x (tstar p w) : V2.Event V (Obj p)).key ≤ toLex (t, phase) :=
      Prod.Lex.toLex_le_toLex.mpr
        (ht.lt_or_eq.imp id (fun h => ⟨h, hphase⟩))
    exact Bool.noConfusion ((decide_eq_true hk).symm.trans hf)
  have hi : i ≤ rho.events.length := List.length_filter_le _ _
  have hb : ∀ k < i, ∀ e, rho.events[k]? = some e → e.time ≤ t := by
    intro k hk e he
    have hfilt := V2.D.Engine.filter_eq_take hs
      (fun e => decide (e.key ≤ toLex (t, phase)))
      (fun e f hef hf => decide_eq_true (hef.trans (of_decide_eq_true hf)))
    have hm : e ∈ rho.events.take i := by
      apply List.mem_of_getElem? (i := k)
      rw [List.getElem?_take_of_lt hk]
      exact he
    rw [← hfilt] at hm
    have hf := (List.mem_filter.mp hm).2
    rcases Prod.Lex.toLex_le_toLex.mp (of_decide_eq_true hf) with h | ⟨h, _⟩
    · exact h.le
    · exact h.le
  have hw : WakesAppliedAtIdx E rho x i t := by
    intro a ha hat hW
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp
      (hrec.base.valid.wake_restart x hx a ha (hat.trans hh) hW)
    refine ⟨k, ?_, hk⟩
    by_contra hn
    have hf := V2.D.Engine.filter_false_of_index_ge hs
      (fun e => decide (e.key ≤ toLex (t, phase)))
      (fun e f hef hf => decide_eq_true (hef.trans (of_decide_eq_true hf)))
      (Nat.le_of_not_gt hn) hk
    have hkey : (V2.Event.restart x a : V2.Event V (Obj p)).key ≤ toLex (t, phase) :=
      Prod.Lex.toLex_le_toLex.mpr
        (hat.lt_or_eq.imp id (fun h => ⟨h, Nat.zero_le phase⟩))
    exact Bool.noConfusion ((decide_eq_true hkey).symm.trans hf)
  exact claims_recovery_readers hrec hx hj hji hi hcut ht hh
    (claims_prefixTime_bounds hs hj hji hi hb) hw

/-- A source healing gate supplies the exact confirmed read after its ticks.
The source recovery epoch supplies the receiver guard and applied wakes. -/
theorem fgsa_recovery_gate_readers {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {w : HealingWitness}
    (h0 : H0 p c E rho w) (hh : tstar p w ≤ rho.horizon)
    (x : V) (hx : x ∈ rho.honest) :
    confirmedReaderAtIdx p c E rho x (afterTicksIdx rho (tstar p w)) (tstar p w) :=
  (claims_recovery_cut_readers hrec h0 (tstar p w) 1 le_rfl le_rfl hh x hx).1

private theorem claims_recovery_time_readers {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {w : HealingWitness}
    (h0 : H0 p c E rho w) (t : Time) (ht : tstar p w ≤ t) (hh : t ≤ rho.horizon)
    (x : V) (hx : x ∈ rho.honest) :
    confirmedReader p c E rho x t ∧ confirmedReaderIdx p c E rho x (timeIdx rho t) := by
  have h := claims_recovery_cut_readers hrec h0 t 2 (by decide) ht hh x hx
  have he : (rho.events.filter (fun e => decide (e.key ≤ toLex (t, 2)))).length =
      timeIdx rho t := by
    apply congrArg List.length
    apply List.filter_congr
    intro e _
    have hp : e.phase ≤ 2 := by cases e <;> simp [V2.Event.phase]
    apply decide_eq_decide.mpr
    constructor
    · intro hk
      rcases Prod.Lex.toLex_le_toLex.mp hk with h | ⟨h, _⟩
      · exact h.le
      · exact h.le
    · intro ht
      exact Prod.Lex.toLex_le_toLex.mpr (ht.lt_or_eq.imp id (fun h => ⟨h, hp⟩))
  rw [he] at h
  exact h

/-- Blueprint 21 H.20–H.22; DC available/stableIncludedFast: INTENTIONAL GST output.
H-time supplies one healing witness. Gate service and suffix monotonicity
supply both public outputs at every later read within the horizon. -/
theorem fgsa_availableGST (hH : HTimeClaim p) : AvailableGSTClaim p := by
  intro G ΔF hδ V _ _ In c E rho hp
  have ht := hH G ΔF hδ c E rho () hp
  have healed := uniformHealing_of_hTimeConcl p c E rho G ΔF ht
  obtain ⟨w, input, hstar, hbound⟩ := ht
  refine ⟨w, input, hstar.trans_lt hbound, healed, ?_⟩
  intro pt hstart hprop hhor
  have hs := hp.set.base.valid.toScheduleWellFormed
  have hgate : recoveryStart p E + B_HF p ΔF G < SA.gateTime p.toParams pt.s := by
    change recoveryStart p E + B_HF p ΔF G < 4 * p.Δ * (pt.s : Time) + 6 * p.Δ
    change recoveryStart p E + B_HF p ΔF G ≤ 4 * p.Δ * (pt.s : Time) at hstart
    exact hstart.trans_lt (lt_add_of_pos_right _ (mul_pos (by decide) p.deltaPos))
  have hcut : HealSuffix p c rho (recoveryStart p E + B_HF p ΔF G)
      (afterTicksIdx rho (SA.gateTime p.toParams pt.s)) := by
    rw [HealSuffix_def]
    refine ⟨?_, List.length_filter_le _ _⟩
    rw [healStart_def]
    split
    · exact afterTicksIdx_mono rho hgate.le
    · change (rho.events.filter _).length ≤ (rho.events.filter _).length
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      apply List.countP_mono_left
      intro e _ he
      exact decide_eq_true (Prod.Lex.toLex_le_toLex.mpr
        (Or.inl ((of_decide_eq_true he).trans_lt hgate)))
  have service := healed.2.2.2 pt.s pt.P hstart hhor hprop
  have hbase : tstar p w ≤ SA.gateTime p.toParams pt.s :=
    (hstar.trans_lt hbound).le.trans hgate.le
  intro g hg t x ht hx
  have hgateRead := claims_recovery_cut_readers hp.set input.wit
    (SA.gateTime p.toParams pt.s) 1 le_rfl hbase hhor x hx.1
  have hgatePublic := claims_recovery_time_readers hp.set input.wit
    (SA.gateTime p.toParams pt.s) hbase hhor x hx.1
  have htimeRead := claims_recovery_time_readers hp.set input.wit t
    (hbase.trans ht.1) ht.2 x hx.1
  have hij : afterTicksIdx rho (SA.gateTime p.toParams pt.s) ≤ timeIdx rho t :=
    (preIdx_le_afterTicksIdx E rho hs _).2.trans
      (V2.D.Engine.read_length_mono _ _ ht.1)
  have hlater : HealSuffix p c rho (recoveryStart p E + B_HF p ΔF G) (timeIdx rho t) :=
    ⟨hcut.1.trans hij, List.length_filter_le _ _⟩
  have hb : Block.Preceq pt.P
      (S_at p c E rho (afterTicksIdx rho (SA.gateTime p.toParams pt.s)) x) := by
    have hb := service (SA.gateTime p.toParams pt.s) x rfl hgatePublic.1
    change Block.Preceq pt.P
      ((fgsaInterface p c).stable (afterTicks E rho (SA.gateTime p.toParams pt.s) x)) at hb
    rw [afterTicks_eq_stateBefore E rho hs] at hb
    exact hb
  have hm := healed.2.1 _ _ x hcut hlater hij hgateRead.2 htimeRead.2
  have hread : V2.D.outputAt E rho g x t = S_at p c E rho (timeIdx rho t) x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;>
      change (V2.D.Run.readAt E rho t x).st.base.stableRecord = _ <;>
      rw [S_at_def, V2.D.Engine.readAt_eq_stateBefore hs t] <;> rfl
  change Block.Preceq pt.P (V2.D.outputAt E rho g x t)
  rw [hread]
  exact Gen.Pure.block_preceq_trans hb hm

/-- OUTPUT-DIRECT §10. Claim-to-claim assembly stays in Shared/Claims.
One healthy cut supplies the individual arming inputs of the proved lane body.
The companion uses the amended OutageContinuationConcl with per-read repair readiness.
The frozen FGSAClaims record is unchanged. -/
theorem outageContinuation_of_body (p : Params)
    (hbody : ∀ {In V : Type} [DecidableEq V] {c : AppCodec In}
      {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} [Fintype V]
      {fast : Bool} {T b₀ b₁ ΔF : Time},
      RStore p c E rho → RFrameExactNext p c E rho → SrcFrameAboveStmt p c E rho →
      SourceDisciplineAt p c E rho →
      CleanHistoryAt p c E rho b₀ → CleanTruncAt p c E rho b₀ →
      OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF →
      RStoreCumul p c E rho → OutageContinuationConcl p c E rho fast T b₀ b₁)
    (hstore : StoreClaim p) (hactive : ActiveViewClaim p) (hframe : FrameClaim p)
    (hsrc : SrcFrameAboveClaim p) (hdisc : SourceDisciplineClaim p)
    (hcut : CleanCutClaim p) : OutageContinuationClaim p := by
  intro V _ _ In c E rho fast T b₀ b₁ ΔF h
  have hb0 : 0 < b₀ := by
    have hT := h.order.1
    have hlag := h.lag
    have hd := p.deltaPos
    have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
    cases fast with
    | false =>
      change T + ((4 * (p.k : Time) - 1) * p.Δ - 3 * p.Δ) ≤ b₀ at hlag
      nlinarith
    | true =>
      change T + 4 * p.Δ ≤ b₀ at hlag
      linarith
  have hsource : SourceDisciplinePrem p c E rho () :=
    ⟨h.pre.base, h.pre.faultQ_of_pos hb0⟩
  have hd := hdisc c E rho () hsource
  have hc := hcut c E rho (ΔF := ΔF) ⟨b₀⟩ ⟨h.sleepPre⟩
  exact hbody (hactive c E rho).1 (hframe c E rho).1 (hsrc c E rho () hsource)
    hd hc.1 hc.2 h ((hstore c E rho).2 h.pre.base.valid.toScheduleWellFormed).1

end AvailableChain.FGSA.Run
end

public section
namespace AvailableChain.FGSA.Run
variable {p : Params}

/-- Plan B1–B2; Blueprint 21 H.20–H.22: conditional GST growth uses one
H-time witness, recovery recurrence and awake proposers. The shared causal,
emission, healed-read and order lemmas supply both public outputs. -/
theorem fgsa_availableGrowthGST (hH : HTimeClaim p) : AvailableGrowthGSTClaim p := by
  intro G ΔF hδ V _ _ In c E rho t hp hlate hhor
  obtain ⟨w, input, hstar, available⟩ := fgsa_availableGST hH G ΔF hδ c E rho hp
  have hd := p.deltaPos
  have hgap := hp.set.gapPos
  have hzero : 0 ≤ tstar p w := by
    rw [tstar_def]
    change 0 ≤ 4 * p.Δ * (w.u : Time) + 6 * p.Δ
    positivity
  have ht : 0 ≤ t := hzero.trans (hstar.le.trans hlate)
  have hgst : E.t_GST ≤ t := input.wit.after_gst.trans (hstar.le.trans hlate)
  have h6 : 0 ≤ 6 * p.Δ := mul_nonneg (by decide) hd.le
  have hG : 0 ≤ G := (mul_nonneg (by decide : (0 : Time) ≤ 4) hd.le).trans hgap
  have hwindow : t + G ≤ rho.horizon := (le_add_of_nonneg_right h6).trans hhor
  have htD : t ≤ t + G + 6 * p.Δ :=
    (le_add_of_nonneg_right hG).trans (le_add_of_nonneg_right h6)
  obtain ⟨s, hfuture, hupper, hh, hjoined⟩ := hp.set.joinedGap t
    ((claims_h0_ready input.wit).trans (hstar.le.trans hlate)) hwindow
  have hs := hp.set.base.valid.toScheduleWellFormed
  have ha := hp.set.awake _ hh.2 _ (hgst.trans hfuture.le) (hupper.trans hwindow)
  obtain ⟨B, hprop, hslot⟩ := fgsa_honestProposal_exists_of_awake_slot E rho hs
    hp.set.base.delta hh ha hjoined.2.2 (hupper.trans hwindow)
  have hgate : SA.gateTime p.toParams s ≤ t + G + 6 * p.Δ := by
    change 4 * p.Δ * (s : Time) + 6 * p.Δ ≤ t + G + 6 * p.Δ
    change 4 * p.Δ * (s : Time) ≤ t + G at hupper
    simpa only [add_comm] using add_le_add_left hupper (6 * p.Δ)
  have hincl := available.2 ⟨s, B⟩ (hlate.trans hfuture.le) hprop (hgate.trans hhor)
  refine ⟨w, input, hstar, s, B, hfuture, hprop, ?_⟩
  intro g hg
  have hread (u : Time) (hu : t ≤ u) (huh : u ≤ rho.horizon) (x : V)
      (hx : x ∈ rho.honest) := claims_recovery_time_readers hp.set input.wit u
        (hstar.le.trans (hlate.trans hu)) huh x hx
  refine ⟨?_, ?_⟩
  · intro x hx
    have hmono := fgsa_healed_output_mono E rho hs available.1 hlate htD g hg x
      (hread t le_rfl (htD.trans hhor) x hx.1).2
      (hread _ htD hhor x hx.1).2
    have hinc := hincl g hg _ x ⟨hgate, hhor⟩ (hread _ htD hhor x hx.1).1
    have hn := fgsa_output_noFuture_of_slot E rho hs ht hfuture hslot.ge g hg x
    have hle : Block.Preceq (V2.D.outputAt E rho g x t) B := by
      rcases Gen.Pure.block_preceq_total_of_common hmono hinc with h | h
      · exact h
      · exact (hn h).elim
    have hne : V2.D.outputAt E rho g x t ≠ B := by
      intro he
      exact hn (he ▸ Gen.Pure.block_preceq_refl B)
    change (!decide (_ = B) && Block.preceq _ B) = true
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨hne, hle⟩
  · intro x hx
    exact hincl g hg _ x ⟨hgate, hhor⟩ hx

/-- WC plan §8 Job 4 and r2.1; DC safety projection with the same source witness.
Source cut coverage and continuation coverage discharge the live safety guard. -/
theorem weakContinuation_of_live {G : Time} (h : WeakContinuationLiveClaim p G) :
    WeakContinuationClaim p G := by
  intro V _ _ In c ΔF hδ E source hS
  obtain ⟨u, Q, iStar, cut, live⟩ := h c ΔF hδ E source hS
  refine ⟨u, Q, iStar, cut, ?_⟩
  intro E' rho hc
  exact (live E' rho hc).safety (cut.beforeEnd.le.trans hc.covered)

end AvailableChain.FGSA.Run
end
