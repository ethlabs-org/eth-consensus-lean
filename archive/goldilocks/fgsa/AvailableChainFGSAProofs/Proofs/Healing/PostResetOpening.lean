module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetRead
public import AvailableChainFGSAProofs.Proofs.Healing.OpeningService
public import AvailableChainFGSAProofs.Proofs.Healing.CommonEntryFacts
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetInvariant
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetHigh
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetGate
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedEndpoint

public import AvailableChainFGSAProofs.Proofs.Healing.FrontierService

public section

/-! Blueprint 21 H.17:2946–3048, especially 3031–3040; plan J6-3 O1.
DC: SAME stored proposal, raw-result parent transfer and J3 geometry.
The separate opening predicate extends at each cut without service.
Earlier opening sources use parent transfer; same-time selected sources
use the exact raw result at their earlier tick. The J3 witness view holds
only the reset copy and high sources. Its witness is below the proposal,
which then witnesses its own full-domain membership. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure RetainedWalk

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:3031–3040; plan J6-3 R2/O1; B1/B17/B18.
DC: SAME full-domain membership at each opening action before the cut. -/
def PostResetOpeningDomain (w : HealingWitness) (i : Nat) : Prop :=
  ∀ k, k < i → ∀ x v Q, x ∈ rho.honest → IsGateTick p c rho k x v →
    HonestProposal E rho (fgsaInterface p c) v Q → w.sStar + 2 ≤ v →
    ∀ r, v = r * p.R →
      let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho k x) (p.actionTime r)).st
      ∃ D, eraseFG D = Q ∧ D ∈ domainR p st (treeT p st)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:3031–3040; plan J6-3 R2/O1; B3a.
DC: SAME equation export of the separate opening-domain predicate. -/
theorem PostResetOpeningDomain_def (w : HealingWitness) (i : Nat) :
    PostResetOpeningDomain p c E rho w i = (
    ∀ k, k < i → ∀ x v Q, x ∈ rho.honest → IsGateTick p c rho k x v →
      HonestProposal E rho (fgsaInterface p c) v Q → w.sStar + 2 ≤ v →
      ∀ r, v = r * p.R →
        let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho k x) (p.actionTime r)).st
        ∃ D, eraseFG D = Q ∧ D ∈ domainR p st (treeT p st)) := by rfl

variable {p c E rho}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.17:2946–3012; plan J6/J6-3 O1; B1/B17/B18.
DC: SAME retained geometry at actual HEAD ticks. Recovery supplies
synchrony through the explicit HEAD horizon. H0Reset supplies only the GST
bound. There is no additional standing port or INLINE input on this route.
Blueprint 21 H.17:2946–3040; plan RE-BIND D2; DC: SAME per-label cone. -/
theorem healing_postReset_headGeometry_at [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (v : Slot) (hcone : PostResetConeAt p c E rho w v) (hv : w.sStar + 2 ≤ v)
    (hHeadHorizon : SA.voteTime p.toParams v ≤ rho.horizon)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams v)))
    (hseat : rho.seatOf (.prop v) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop v) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip) :
    ∃ D : FGBlock (Fin p.n), RetainedExactHeadRunGeometryOn E rho ip x v D N.erase := by
  rw [PostResetConeAt_def] at hcone
  obtain ⟨D, hinput⟩ := hcone hv hHeadHorizon hx hip hseat N hem
  have hCut : HealingWindow p E 2 v := healing_window_of_cut E (by
    have hresetCut := healing_reset_slot_cutoff hreset
    have hlabel : (w.sStar : Int) + 2 ≤ (v : Int) := by exact_mod_cast hv
    change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) at hresetCut
    change E.t_GST ≤ 4 * p.Δ * ((v : Int) - 2)
    nlinarith [p.deltaPos])
  have hHeads := healing_repair_head_services_recovery E rho hrec mono hCut hx hip hem
  have hFloor y hy ih hih := healing_retained_cone_reader_floor E rho hrec.base.valid
    mono hy hip hih N hem D (hinput y hy ih hih)
  have hreads := fgsa_retainedReads_H17_joined (hroots := hrec.base.receiptIdealization)
    E rho hrec.base.valid v hx hip hseat N hem D
    (fun y hy ih hih _ => hinput y hy ih hih)
    (fun y hy ih hih hj => hHeads.target hy hih hj (hFloor y hy ih hih))
  exact ⟨D, fgsa_retainedExactHead_geometry_on_run_on
    (hroots := hrec.base.receiptIdealization) E rho hrec.base.valid v hx hip hseat N hem D
    hreads (fun y hy ih hih hj => hHeads.scopes y hy ih hih hj (hFloor y hy ih hih))⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3012; plan J6/J6-3 O1; B1/B17/B18.
DC: SAME exact HEAD for every honest proposal at v ≥ sStar + 2.
The HEAD deadline is explicit and separate from the later gate deadline.
Blueprint 21 H.17:2946–3040; plan RE-BIND D2; DC: SAME per-label cone. -/
theorem healing_postReset_exactHead_at [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (w : HealingWitness) (hreset : H0Reset p c E rho w)
    {v : Slot} (hcone : PostResetConeAt p c E rho w v) :
    ∀ Q, HonestProposal E rho (fgsaInterface p c) v Q → w.sStar + 2 ≤ v →
      SA.voteTime p.toParams v ≤ rho.horizon →
      ∀ y ∈ rho.honest, headAtLabel p c E rho y v = some Q := by
  intro Q hp hv hHeadHorizon
  obtain ⟨ip, x, N, heN, hx, hip, hseat, hem⟩ := repair_proposal_emission E rho hp
  subst Q
  obtain ⟨D, hgeom⟩ := healing_postReset_headGeometry_at E rho hrec mono w hreset v hcone
    hv hHeadHorizon hx hip hseat N hem
  intro y hy
  exact exactService_head_of_retained_proposal_on E rho hrec.base.valid hrec.base.delta
    v hip N hem D hgeom hHeadHorizon y hy
    (healing_recovery_joined E rho hrec hy
      (healing_reset_vote_cutoff (s := v) hreset
        ((Nat.le_succ (w.sStar + 1)).trans hv))
      ((healing_window_of_cut E (healing_reset_vote_cutoff (s := v) hreset
        ((Nat.le_succ (w.sStar + 1)).trans hv))).sync)
      hHeadHorizon)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A3 carrier at the HEAD read: the proposal has an exact erased FG
representative in that reader's retained voter domain.
DC: SAME retained HEAD carrier; plan J6-3 O1; Blueprint 21:3031–3040.
Store cumulativity carries this representative to the later action read.
Blueprint 21 H.17:2946–3040; plan RE-BIND D2; DC: SAME per-label cone. -/
theorem healing_postReset_headCarrier_at [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (w : HealingWitness) (hreset : H0Reset p c E rho w)
    {v : Slot} (hcone : PostResetConeAt p c E rho w v)
    {Q : Block} (hp : HonestProposal E rho (fgsaInterface p c) v Q)
    (hv : w.sStar + 2 ≤ v)
    (hHeadHorizon : SA.voteTime p.toParams v ≤ rho.horizon)
    {y : V} {ih : Nat} (hy : y ∈ rho.honest)
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams v))) :
    let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams v)
    ∃ C : FGBlock (Fin p.n), eraseFG C = Q ∧ C ∈ domainR p dst (voterBlocks p dst v) := by
  intro dst
  obtain ⟨ip, x, N, heN, hx, hip, hseat, hem⟩ := repair_proposal_emission E rho hp
  subst Q
  obtain ⟨D, hgeom⟩ := healing_postReset_headGeometry_at E rho hrec mono w hreset v hcone
    hv hHeadHorizon hx hip hseat N hem
  have hm : N.erase ∈ erasedList dst (domainR p dst (voterBlocks p dst v)) := by
    rw [fgsa_domainR_eq_treeStoreFrameView]
    exact (hgeom.endpoint y hy ih hih (healing_recovery_joined E rho hrec hy
      (healing_reset_vote_cutoff (s := v) hreset
        ((Nat.le_succ (w.sStar + 1)).trans hv))
      ((healing_window_of_cut E (healing_reset_vote_cutoff (s := v) hreset
        ((Nat.le_succ (w.sStar + 1)).trans hv))).sync)
      hHeadHorizon)).proposal_mem
  obtain ⟨C, hC, heC⟩ := of_decide_eq_true (List.mem_filter.mp hm).2
  exact ⟨C, heC, hC⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:3031–3040; plan J6-3 O1; B1/B17/B18.
DC: SAME cumulative store from the exact HEAD carrier to the gate read.
The actual tick supplies its horizon; no service field is used.
Blueprint 21 H.17:2946–3040; plan RE-BIND D2; DC: SAME per-label cone. -/
theorem healing_postReset_opening_stored_at [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (w : HealingWitness) (hreset : H0Reset p c E rho w)
    {v : Slot} (hcone : PostResetConeAt p c E rho w v)
    {Q : Block} (hp : HonestProposal E rho (fgsaInterface p c) v Q)
    (hv : w.sStar + 2 ≤ v) {k : Nat} {x : V} (hx : x ∈ rho.honest)
    (ht : IsGateTick p c rho k x v) :
    ∃ D : FGBlock (Fin p.n), eraseFG D = Q ∧ D ∈ (storeAt p c E rho k x).fg.TF := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hh : SA.voteTime p.toParams v ≤ rho.horizon :=
    postReset_head_horizon p c rho ((hs.in_horizon _ (List.mem_of_getElem? ht)).2)
  have htime : ((4 * v + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams v := by
    change ((4 * v + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * (v : Int) + p.Δ
    push_cast
    ring
  obtain ⟨ih, hih, _⟩ := fgsa_tick_total E rho hs hrec.base.delta x hx
    (4 * v + 1) (htime ▸ hh)
    (htime ▸ hrec.awake x hx (SA.voteTime p.toParams v) (by
      apply hreset.synchronous.trans
      have hl : (w.sStar : Int) ≤ (v : Int) := by
        exact_mod_cast ((Nat.le_add_right w.sStar 2).trans hv)
      change 4 * p.Δ * (w.sStar : Int) + p.Δ ≤ 4 * p.Δ * (v : Int) + p.Δ
      nlinarith [p.deltaPos]) hh)
  rw [htime] at hih
  have hik : ih ≤ k := by
    by_contra hn
    have hki : k < ih := Nat.lt_of_not_ge hn
    obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp ht
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hih
    have hord := (List.pairwise_iff_getElem.mp hs.sorted) k ih hkl hil hki
    rw [hke, hie] at hord
    have hbad := V2.D.Engine.time_le_of_key_le _ _ hord
    change SA.gateTime p.toParams v ≤ SA.voteTime p.toParams v at hbad
    change 4 * p.Δ * (v : Int) + 6 * p.Δ ≤ 4 * p.Δ * (v : Int) + p.Δ at hbad
    linarith [p.deltaPos]
  obtain ⟨D, he, hD⟩ :=
    healing_postReset_headCarrier_at E rho hrec mono w hreset hcone hp hv hh hx hih
  have hm := ((KitFG.mem_filteredFromView _ _ _ _).mp hD).1
  have hstored : D ∈ (storeAt p c E rho ih x).fg.TF := by
    have hmem := Next.tree_subset_TF p _ (Finset.mem_filter.mp hm).1
    change D ∈ (clock p (storeAt p c E rho ih x) (SA.voteTime p.toParams v)).fg.TF at hmem
    rwa [clock_fg] at hmem
  exact ⟨D, he, (fgsa_store_durable p c E rho hik x).1 hstored⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:3031–3040; plan J6-3 O1; B1/B17/B18.
DC: SAME stored lift after the opening clock. Clocking leaves TF fixed.
Blueprint 21 H.17:2946–3040; plan RE-BIND D2; DC: SAME per-label cone. -/
theorem healing_postReset_opening_clock_stored_at [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (w : HealingWitness) (hreset : H0Reset p c E rho w)
    {v : Slot} (hcone : PostResetConeAt p c E rho w v)
    {Q : Block} (hp : HonestProposal E rho (fgsaInterface p c) v Q)
    (hv : w.sStar + 2 ≤ v) {k : Nat} {x : V} (hx : x ∈ rho.honest)
    (ht : IsGateTick p c rho k x v) (r : Nat) (_hr : v = r * p.R) :
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho k x) (p.actionTime r)).st
    ∃ D : FGBlock (Fin p.n), eraseFG D = Q ∧ D ∈ st.fg.TF := by
  intro st
  obtain ⟨D, he, hD⟩ :=
    healing_postReset_opening_stored_at E rho hrec mono w hreset hcone hp hv hx ht
  refine ⟨D, he, ?_⟩
  change D ∈ (clock p (storeAt p c E rho k x) (p.actionTime r)).fg.TF
  rwa [clock_fg]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2931–2938, H.17:3031–3040; plan J6-3 O1; B1/B17.
DC: SAME selected source below its raw result and the current proposal parent.
INLINE hgap has producer healing_source_row_label at proposal/HEAD reads.
At the action read that producer does not apply. -/
theorem healing_postReset_source_parent
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (w : HealingWitness) (i : Nat)
    (hraw : PostResetRawTransfer p c E rho w i)
    {K : FGBlock (Fin p.n)} {s v : Slot} {Q : Block}
    (hsource : SourceBefore p c E rho i K s) (hlower : w.sStar ≤ s)
    (hgap : s + 2 ≤ v) (hcut : timeIdx rho (SA.proposalTime p.toParams v) ≤ i)
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) :
    Block.Preceq (eraseFG K) Q.parent := by
  obtain ⟨j, y, r, a, hj, ha, hK, rfl⟩ := hsource
  obtain ⟨B, hB, hKB⟩ := common_source_below_raw E rho hs hK
  have hjg : IsGateTick p c rho j y (r * p.R) := ha.2.1
  rw [PostResetRawTransfer_def] at hraw
  exact block_preceq_trans hKB
    ((hraw j hj y (r * p.R) B ha.1 hlower hjg hB).2.2.1 v Q hgap hcut hp)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:3031–3040; plan J6-3 O1; B1/B17.
DC: SAME reset source and its two-label gap from H0Reset.fresh and label.
The source tick and proposal read must both be in the named transfer cut. -/
theorem healing_postReset_reset_parent
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (w : HealingWitness)
    (hreset : H0Reset p c E rho w) (i : Nat)
    (hraw : PostResetRawTransfer p c E rho w i)
    (hresetCut : afterTicksIdx rho (p.actionTime w.rStar) ≤ i)
    {v : Slot} {Q : Block} (hv : w.sStar + 2 ≤ v)
    (hcut : timeIdx rho (SA.proposalTime p.toParams v) ≤ i)
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) :
    Block.Preceq w.CStar Q.parent := by
  obtain ⟨j, y, a, C, ha, _, hC, he, _⟩ := hreset.fresh
  have hj : j < i := by
    have ht := ha.2.1
    have hc : cutPred (P := fgsa p c) (p.actionTime w.rStar)
        (.tick y (p.actionTime w.rStar)) = true := decide_eq_true le_rfl
    have hji : j < afterTicksIdx rho (p.actionTime w.rStar) := by
      by_contra hn
      have hf := V2.D.Engine.filter_false_of_index_ge hs (cutPred (p.actionTime w.rStar))
        (fun e f h ef => decide_eq_true (h.trans (of_decide_eq_true ef)))
        (Nat.le_of_not_gt hn) ht
      rw [hc] at hf
      contradiction
    exact hji.trans_le hresetCut
  have hsource : SourceBefore p c E rho i C w.sStar :=
    ⟨j, y, w.rStar, a, hj, ha, hC, hreset.label⟩
  have hgap : w.sStar + 2 ≤ v := by
    have hlabel := postReset_source_label_le_sub_two w hv
    omega
  rw [← he]
  exact healing_postReset_source_parent E rho hs w i hraw hsource le_rfl hgap hcut hp

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:3021–3030; plan J6-2/J6-3 O1/O2; B1/B17/B18.
DC: SAME exact HEAD gives the covered-prefix field of the gate receipt.
Blueprint 21 H.17:2946–3040; plan RE-BIND D2; DC: SAME per-label cone. -/
theorem healing_postReset_gate_covered_prefix_at [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (w : HealingWitness) (hreset : H0Reset p c E rho w)
    {v : Slot} (hcone : PostResetConeAt p c E rho w v)
    {Q : Block} (hp : HonestProposal E rho (fgsaInterface p c) v Q)
    (hv : w.sStar + 2 ≤ v)
    (hGateHorizon : SA.gateTime p.toParams v ≤ rho.horizon) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head v)) q ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head v)) q) (SA.voteTime p.toParams v) = true →
      ∀ K, HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head v)) q)
        (ofHead p ⟨.seat (.head v) q, K.root⟩) (SA.voteTime p.toParams v) K →
        Block.Preceq Q K := by
  intro q hy _ K he
  have hhead := healing_postReset_exactHead_at E rho hrec mono w hreset hcone Q hp hv
    (postReset_head_horizon p c rho hGateHorizon)
  have heq := exactService_emitted_head E rho hrec.base.valid.toScheduleWellFormed
    v Q hhead q hy K (SA.voteTime p.toParams v) he
  rw [heq]
  exact block_preceq_refl Q

section ServiceStep
variable [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (cap : RCap p c E rho)
    (rowCovered : ∀ (_hb : Base₂ p c E rho)
      (_hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
      (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ C : FGBlock (Fin p.n),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st → (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))

include hrec mono hreset cap rowCovered

omit mono in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.17:3024–3040; plan J6-3 O1/O2; B1/B13/B17/B18.
DC: SAME current F provenance and raw-result parent transfer at the cut.
Standing cap has producer fgsa_rCap_channel. INLINE rowCovered has producer
rowPermission_covered. postReset_selected_label supplies each high source's
reset lower bound. The F clock bound gives its two-label gap. -/
theorem healing_postReset_gate_finality (i : Nat)
    (hfp : PostResetFProv p c E rho w i)
    (hraw : PostResetRawTransfer p c E rho w i)
    {k : Nat} (hk : k < i) {x : V} {v : Slot} {Q : Block}
    (hx : x ∈ rho.honest) (ht : IsGateTick p c rho k x v)
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v)
    (hcut : timeIdx rho (SA.proposalTime p.toParams v) ≤ i) :
    Block.Preceq (eraseFG (storeAt p c E rho k x).fg.F) Q := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hresetTime : p.actionTime w.rStar < SA.gateTime p.toParams v := by
    have hvI : (w.sStar : Int) + 2 ≤ (v : Int) := by exact_mod_cast hv
    change SA.gateTime p.toParams (w.rStar * p.R) < _
    rw [← hreset.label]
    change 4 * p.Δ * (w.sStar : Int) + 6 * p.Δ < 4 * p.Δ * (v : Int) + 6 * p.Δ
    nlinarith [p.deltaPos]
  have hresetCut : afterTicksIdx rho (p.actionTime w.rStar) ≤ k :=
    (preIdx_le_afterTicksIdx E rho hs _).2.trans
      (healing_postReset_time_cut_le_tick E rho hs ht hresetTime)
  have hCQp := healing_postReset_reset_parent E rho hs w hreset i hraw
    (hresetCut.trans hk.le) hv hcut hp
  have hparent : Block.Preceq Q.parent Q := by
    cases Q with
    | genesis => exact block_preceq_refl _
    | node P s root body => exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl P))
  rw [PostResetFProv_def] at hfp
  rcases (hfp k hk x hx hresetCut).1 with hlow | ⟨K, s, hK, hh, htime, hFK⟩
  · exact block_preceq_trans hlow (block_preceq_trans hCQp hparent)
  · have hnow := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho hs ht x
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho k x)] at hnow
    have hbound : SA.gateTime p.toParams s + P p ≤ SA.gateTime p.toParams v :=
      htime.trans hnow
    have hgap : s + 2 ≤ v := by
      have hR : (2 : Int) ≤ p.R := by exact_mod_cast (show 2 ≤ p.R by have := p.RLarge; omega)
      change 4 * p.Δ * (s : Int) + 6 * p.Δ + 4 * (p.R : Int) * p.Δ ≤
        4 * p.Δ * (v : Int) + 6 * p.Δ at hbound
      have hgapI : (s : Int) + 2 ≤ v := by nlinarith [p.deltaPos]
      exact_mod_cast hgapI
    have hlower : w.sStar ≤ s := by
      obtain ⟨j, y, r, a, _, ha, hsrc, rfl⟩ := hK
      exact postReset_selected_label p c E rho rowCovered hrec.toRecovery₂ cap hreset ha.1 hsrc hh
    have hKi : SourceBefore p c E rho i K s := by
      obtain ⟨j, y, r, a, hj, ha, hsrc, he⟩ := hK
      exact ⟨j, y, r, a, hj.trans hk, ha, hsrc, he⟩
    have hKQp := healing_postReset_source_parent E rho hs w i hraw hKi hlower hgap hcut hp
    exact block_preceq_trans hFK (block_preceq_trans hKQp hparent)

end ServiceStep

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:3021–3030; plan J6-3 O1/O2; B1/B13/B17.
DC: SAME awake honest HEAD count and SA release threshold. -/
theorem healing_postReset_gate_participation [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) {v : Slot}
    (hgsts : E.t_GST ≤ SA.voteTime p.toParams v)
    (hh : SA.voteTime p.toParams v ≤ rho.horizon) :
    ∃ H : Finset (Fin p.n),
      (∀ q, q ∈ H ↔ rho.seatOf (.base (.head v)) q ∈ rho.honest ∧
        E.awake (rho.seatOf (.base (.head v)) q) (SA.voteTime p.toParams v) = true) ∧
      Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card ∧
      SA.releaseThreshold p.toParams ≤ H.card := by
  have hn : Fintype.card V = p.n :=
    (V2.D.CStar.seats_eq (ℓ := .base .fg) hrec.base.linked.toCStar trivial).symm
  have hf : (Gen.V2.Duty.faulty rho).card = p.n - rho.honest.card := by
    rw [Gen.V2.Duty.faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hn]
  have he : Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams v) = rho.honest := by
    rw [Gen.V2.Duty.awakeHonest_def]
    exact Finset.filter_eq_self.mpr (fun x hx => hrec.awake x hx _ hgsts hh)
  have hb : Gen.Pure.Batch (Gen.V2.Duty.awakeHonest E rho
      (SA.voteTime p.toParams v)).card (Gen.V2.Duty.faulty rho).card := by
    rw [he]
    constructor
    have hcard := Finset.card_le_univ rho.honest
    rw [hn] at hcard
    have hbound := hrec.fault
    rw [hf] at hbound ⊢
    have hpos := p.nPos
    omega
  have hcount : SA.releaseThreshold p.toParams ≤
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams v)).card := by
    have hn : Fintype.card V = p.n :=
      (V2.D.CStar.seats_eq (ℓ := .base (.head v)) hrec.base.cstar trivial).symm
    have he : Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams v) = rho.honest := by
      rw [Gen.V2.Duty.awakeHonest_def]
      exact Finset.filter_eq_self.mpr (fun x hx => hrec.awake x hx _ hgsts hh)
    rw [he]
    have hcard : (Gen.V2.Duty.faulty rho).card + rho.honest.card = p.n := by
      rw [Gen.V2.Duty.faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, hn]
      have hc := Finset.card_le_univ rho.honest
      rw [hn] at hc
      omega
    have hf := hrec.fault
    have hnpos := p.nPos
    change (p.n + 1) / 2 ≤ rho.honest.card
    omega
  exact exactService_participation_of_card E rho hrec.base.cstar v hb hcount

section OpeningRaw
variable [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (cap : RCap p c E rho)
    (rowCovered : ∀ (_hb : Base₂ p c E rho)
      (_hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
      (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ C : FGBlock (Fin p.n),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st → (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))

include hrec mono hreset cap rowCovered

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.17:3021–3040; plan J6-3 O1/O2; B1/B13/B17/B18.
DC: SAME exact raw result at an earlier tick in the cut. This result uses
no service or opening-domain input. It covers same-time selected sources.
Blueprint 21 H.17:2946–3040; plan RE-BIND D2; DC: SAME per-label cone. -/
theorem healing_postReset_gate_raw_at (i : Nat) {v : Slot} (hcone : PostResetConeAt p c E rho w v)
    (hfp : PostResetFProv p c E rho w i)
    (hraw : PostResetRawTransfer p c E rho w i)
    {k : Nat} (hk : k < i) {x : V} {Q : Block}
    (hx : x ∈ rho.honest) (ht : IsGateTick p c rho k x v)
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v)
    (hcut : timeIdx rho (SA.proposalTime p.toParams v) ≤ i) :
    gateResult p c E rho x v = some (some Q) := by
  classical
  have hs := hrec.base.valid.toScheduleWellFormed
  have hGateHorizon := (hs.in_horizon _ (List.mem_of_getElem? ht)).2
  have hh := postReset_head_horizon p c rho hGateHorizon
  have hFQ := healing_postReset_gate_finality E rho hrec w hreset cap rowCovered
    i hfp hraw hk hx ht hp hv hcut
  have hhead := healing_postReset_exactHead_at E rho hrec mono w hreset hcone Q hp hv hh
  have hreceipt : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams v)) v Q := by
    refine ⟨?_, healing_postReset_gate_covered_prefix_at E rho hrec mono w hreset hcone
      hp hv hGateHorizon⟩
    intro q hy _ K he
    have heq := exactService_emitted_head E rho hs v Q hhead q hy K
      (SA.voteTime p.toParams v) he
    simpa only [heq, clockPre_fg] using hFQ
  have hgsts : E.t_GST ≤ SA.voteTime p.toParams v := by
    refine (postReset_synchronous_window p c E rho w hreset hv).trans ?_
    change 4 * p.Δ * (v : Int) - p.Δ ≤ 4 * p.Δ * (v : Int) + p.Δ
    linarith [p.deltaPos]
  have hvd : SA.voteTime p.toParams v + E.Δ ≤ SA.gateTime p.toParams v := by
    rw [hrec.base.delta]
    change 4 * p.Δ * (v : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (v : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho
    (fun o => ¬ isRowObject o) _ _ hrec.sync (fgsaDelay_nonrow E.Δ _) hgsts hvd hGateHorizon
  obtain ⟨H, hH, hbatch, _⟩ := healing_postReset_gate_participation E rho hrec hgsts hh
  obtain ⟨hr, _, _, _⟩ := exactService_gate_raw_of_head_on (hroots := hrec.base.receiptIdealization)
    E rho hrec.base.valid hrec.base.delta hrec.base.cstar v Q
    (fun y hy _ => hhead y hy) hSync ht hreceipt
    (healing_gate_receipt_scope_recovery E rho hrec mono hgsts hx
      (healing_recovery_gate_enabled E rho hrec hx ht
        (healing_reset_slot_cutoff hreset |>.trans (by
          have hl : (w.sStar : Int) ≤ (v : Int) := by
            exact_mod_cast ((Nat.le_add_right w.sStar 2).trans hv)
          change 4 * p.Δ * (w.sStar : Int) ≤ 4 * p.Δ * (v : Int)
          nlinarith [p.deltaPos]))) hreceipt) H
    (fun q => by
      rw [hH q]
      constructor
      · rintro ⟨hy, _⟩
        exact ⟨hy, healing_recovery_joined E rho hrec hy
          (healing_reset_vote_cutoff (s := v) hreset
        ((Nat.le_succ (w.sStar + 1)).trans hv)) hgsts hh⟩
      · rintro ⟨hy, _⟩
        exact ⟨hy, hrec.awake _ hy _ hgsts hh⟩) hbatch
  have hEnabled := healing_recovery_gate_enabled E rho hrec hx ht
    (healing_reset_slot_cutoff hreset |>.trans (by
      have hl : (w.sStar : Int) ≤ (v : Int) := by
        exact_mod_cast ((Nat.le_add_right w.sStar 2).trans hv)
      change 4 * p.Δ * (w.sStar : Int) ≤ 4 * p.Δ * (v : Int)
      nlinarith [p.deltaPos]))
  apply (gateResult_eq_saved p c E rho hs ht).trans
  have hSaved := fgsa_gate_saved_result E rho hs ht
    (fgsa_gate_joined_of_enabled E rho hEnabled)
  have hRaw := hr
  rw [clockPre_fg] at hRaw
  exact hSaved.trans (congrArg some hRaw)

end OpeningRaw


section OpeningStep
variable [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (cap : RCap p c E rho)
    (rowCovered : ∀ (_hb : Base₂ p c E rho)
      (_hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
      (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ C : FGBlock (Fin p.n),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st → (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))

include hrec mono hreset cap rowCovered

omit hrec mono hreset cap rowCovered in
private theorem opening_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.17:3031–3040; plan J6-3 O1; B1/B13/B17/B18.
DC: SAME earlier-opening parent transfer. A same-time source uses the
exact raw result at its earlier tick, without service or opening_domain.
Standing cap and INLINE rowCovered have the gate_finality producer map.
Blueprint 21 H.17:2946–3040; plan RE-BIND D2; DC: SAME per-label cone. -/
theorem healing_postReset_opening_source_prefix_at (i : Nat) {v : Slot}
    (hcone : PostResetConeAt p c E rho w v)
    (hfp : PostResetFProv p c E rho w i)
    (hraw : PostResetRawTransfer p c E rho w i)
    {x : V} {Q : Block} (ht : IsGateTick p c rho i x v)
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v)
    (r : Nat) (hr : v = r * p.R)
    {K : FGBlock (Fin p.n)} {s : Slot}
    (hsource : SourceBefore p c E rho i K s) (hh : high p w K) :
    Block.Preceq (eraseFG K) Q := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hproposal : SA.proposalTime p.toParams v < SA.gateTime p.toParams v := by
    change 4 * p.Δ * (v : Int) < 4 * p.Δ * (v : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hcut := healing_postReset_time_cut_le_tick E rho hs ht hproposal
  have hle := (healing_source_read p c E rho hs hsource ht).2.2 rfl
  obtain ⟨j, y, rS, a, hj, ha, hsrc, hsr⟩ := hsource
  have hlower : w.sStar ≤ s := by
    rw [hsr]
    exact postReset_selected_label p c E rho rowCovered hrec.toRecovery₂ cap hreset ha.1 hsrc hh
  by_cases heq : s = v
  · have hsourceTick : IsGateTick p c rho j y v := by rw [← heq, hsr]; exact ha.2.1
    have hrawQ := healing_postReset_gate_raw_at E rho hrec mono w hreset cap rowCovered
      i hcone hfp hraw hj ha.1 hsourceTick hp hv hcut
    obtain ⟨B, hB, hKB⟩ := common_source_below_raw E rho hs hsrc
    rw [← hsr, heq] at hB
    have heB : B = Q := Option.some.inj (Option.some.inj (hB.symm.trans hrawQ))
    exact heB ▸ hKB
  · have hslt : s < v := lt_of_le_of_ne hle heq
    have hrlt : rS < r := by
      by_contra hn
      have hmul := Nat.mul_le_mul_right p.R (Nat.le_of_not_gt hn)
      rw [← hsr, ← hr] at hmul
      exact (not_le.mpr hslt) hmul
    have hgapR : s + p.R ≤ v := by
      calc
        s + p.R = (rS + 1) * p.R := by rw [hsr, Nat.add_mul, Nat.one_mul]
        _ ≤ r * p.R := Nat.mul_le_mul_right p.R (Nat.succ_le_of_lt hrlt)
        _ = v := hr.symm
    have hgap : s + 2 ≤ v := (Nat.add_le_add_left p.RLarge s).trans hgapR
    have hparent := healing_postReset_source_parent E rho hs w i hraw
      ⟨j, y, rS, a, hj, ha, hsrc, hsr⟩ hlower hgap hcut hp
    apply block_preceq_trans hparent
    cases Q with
    | genesis => exact block_preceq_refl _
    | node P s root body => exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl P))

variable (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
include xing origin

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.17:3031–3040; plan J6-3 O1; B1/B13/B17/B18.
DC: SAME J3 height, contest, floor, roots and witness at the new tick.
The witness view contains only the reset copy and high sources, so its
returned witness has a proved prefix bound. The proposal witnesses its
own membership in the full domain. No service field is used.
Standing xing/origin have producers fgsa_rXing/sourceDiscipline_qcOrigin.
Blueprint 21 H.17:2946–3040; plan RE-BIND D2; DC: SAME per-label cone. -/
theorem healing_postReset_openingDomain_new_tick_at (i : Nat) {v : Slot}
    (hcone : PostResetConeAt p c E rho w v)
    (hhigh : PostResetHighCompatible p c E rho w i)
    (hfp : PostResetFProv p c E rho w i)
    (hraw : PostResetRawTransfer p c E rho w i)
    {x : V} {Q : Block} (hx : x ∈ rho.honest)
    (ht : IsGateTick p c rho i x v)
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v) :
    ∀ r, v = r * p.R →
      let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)).st
      ∃ D, eraseFG D = Q ∧ D ∈ domainR p st (treeT p st) := by
  classical
  intro r hr st
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨D, heD, hD⟩ :=
    healing_postReset_opening_stored_at E rho hrec mono w hreset hcone hp hv hx ht
  have hprefix : ∀ K s, SourceBefore p c E rho i K s → high p w K → FGBlock.Preceq K D := by
    intro K s hK hh
    apply opening_lift
    rw [heD]
    exact healing_postReset_opening_source_prefix_at E rho hrec mono w hreset cap rowCovered
      i hcone hfp hraw ht hp hv r hr hK hh
  have hstored : ∀ K s, SourceBefore p c E rho i K s → high p w K →
      K ∈ (storeAt p c E rho i x).fg.TF := by
    intro K s hK hh
    obtain ⟨B, hB, heB⟩ := eraseFG_ancestor_mem (cstoreInv_stateBefore E rho i x).fg.closed
      hD (eraseFG_preceq (hprefix K s hK hh))
    exact eraseFG_injective heB ▸ hB
  have hresetTime : p.actionTime w.rStar < SA.gateTime p.toParams v := by
    have hvI : (w.sStar : Int) + 2 ≤ (v : Int) := by exact_mod_cast hv
    change SA.gateTime p.toParams (w.rStar * p.R) < _
    rw [← hreset.label]
    change 4 * p.Δ * (w.sStar : Int) + 6 * p.Δ < 4 * p.Δ * (v : Int) + 6 * p.Δ
    nlinarith [p.deltaPos]
  have hresetCut : afterTicksIdx rho (p.actionTime w.rStar) ≤ i :=
    (preIdx_le_afterTicksIdx E rho hs _).2.trans
      (healing_postReset_time_cut_le_tick E rho hs ht hresetTime)
  have hproposal : SA.proposalTime p.toParams v < SA.gateTime p.toParams v := by
    change 4 * p.Δ * (v : Int) < 4 * p.Δ * (v : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hcut := healing_postReset_time_cut_le_tick E rho hs ht hproposal
  have hCQp := healing_postReset_reset_parent E rho hs w hreset i hraw hresetCut hv hcut hp
  have hCQ : Block.Preceq w.CStar Q := by
    apply block_preceq_trans hCQp
    cases Q with
    | genesis => exact block_preceq_refl _
    | node P s root body => exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl P))
  obtain ⟨C, hC, heC⟩ := eraseFG_ancestor_mem (cstoreInv_stateBefore E rho i x).fg.closed
    hD (by rwa [heD])
  have hCD : FGBlock.Preceq C D := opening_lift (by rwa [heC, heD])
  have hheight := postReset_keep_height p c E rho hreset hC heC
  have hcontest := postReset_keep_contest (hroots := hrec.base.idealization) p c E rho hs origin
    hhigh hheight hx
  have hfloor := postReset_keep_floor p c E rho hcontest
  have hroots := postReset_keep_roots (hroots := hrec.base.idealization) p c E rho hs xing origin
    hreset hx hC heC
  have hrootBound : ∀ B ∈ [(R_at p c E rho i x).Z, (storeAt p c E rho i x).fg.F],
      FGBlock.Preceq B D := by
    intro B hB
    rcases hroots B hB with hBC | ⟨K, s, hK, hh, hBK⟩
    · exact KitFG.preceq_trans hBC hCD
    · exact KitFG.preceq_trans hBK (hprefix K s hK hh)
  let X := (storeAt p c E rho i x).fg.TF.filter (fun B =>
    B = C ∨ ∃ s, SourceBefore p c E rho i B s ∧ high p w B)
  have hX : X ⊆ (storeAt p c E rho i x).fg.TF := Finset.filter_subset _ _
  have hCX : C ∈ X := Finset.mem_filter.mpr ⟨hC, Or.inl rfl⟩
  have hcover : ∀ K s, SourceBefore p c E rho i K s → high p w K → K ∈ X := by
    intro K s hK hh
    exact Finset.mem_filter.mpr ⟨hstored K s hK hh, Or.inr ⟨s, hK, hh⟩⟩
  obtain ⟨B, hB, hBh⟩ := postReset_keep_witness (hroots := hrec.base.idealization) p c E rho
    origin hreset hx hX hCX heC hcover
  have hBD : FGBlock.Preceq B D := by
    rcases (Finset.mem_filter.mp hB).2 with rfl | ⟨s, hBsrc, hh⟩
    · exact hCD
    · exact hprefix B s hBsrc hh
  have hlo : (R_at p c E rho i x).lo ≤ (heightView p D).h :=
    hfloor.trans (hBh ▸ (fgCertificateLaws p).height.h_mono hBD)
  have hF : FGBlock.Preceq (storeAt p c E rho i x).fg.F D := hrootBound _ (by simp)
  have hZ : FGBlock.Preceq (R_at p c E rho i x).Z D := hrootBound _ (by simp)
  have hdom : D ∈ domainR p (storeAt p c E rho i x) (treeT p (storeAt p c E rho i x)) := by
    exact (KitFG.mem_filteredFromView _ _ _ _).mpr
      ⟨hD, hF, hZ, D, hD, KitFG.preceq_refl _, hlo⟩
  refine ⟨D, heD, ?_⟩
  rw [(opening_domain_clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)).1]
  exact hdom

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:3031–3040; plan J6-3 O1; B1/B13/B17/B18.
DC: SAME extension by the new action tick. Earlier ticks use the separate
opening predicate at i; all carrier fields stay at that cut.
Blueprint 21 H.17:2946–3040; plan RE-BIND D2; DC: SAME per-label cone. -/
theorem healing_postReset_openingDomain_step_at (i : Nat)
    (hcone : ∀ v, timeIdx rho (SA.voteTime p.toParams v) ≤ i →
      PostResetConeAt p c E rho w v)
    (hhigh : PostResetHighCompatible p c E rho w i)
    (hfp : PostResetFProv p c E rho w i)
    (hraw : PostResetRawTransfer p c E rho w i)
    (hopening : PostResetOpeningDomain p c E rho w i) :
    PostResetOpeningDomain p c E rho w (i + 1) := by
  rw [PostResetOpeningDomain_def] at hopening ⊢
  intro k hk x v Q hx ht hp hv
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | hki
  · exact hopening k hk x v Q hx ht hp hv
  · subst k
    exact healing_postReset_openingDomain_new_tick_at E rho hrec mono w hreset cap rowCovered
      xing origin i
      (hcone v (healing_postReset_head_cut_le_tick E rho
        hrec.base.valid.toScheduleWellFormed ht)) hhigh hfp hraw hx ht hp hv

end OpeningStep


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3040; plan RE-BIND D2/D3; DC: SAME cone at its label. -/
theorem healing_postReset_headGeometry [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w)
    (v : Slot) (hv : w.sStar + 2 ≤ v)
    (hHeadHorizon : SA.voteTime p.toParams v ≤ rho.horizon)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams v)))
    (hseat : rho.seatOf (.prop v) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop v) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip) :
    ∃ D : FGBlock (Fin p.n), RetainedExactHeadRunGeometryOn E rho ip x v D N.erase := by
  exact healing_postReset_headGeometry_at E rho hrec mono w hreset v
    ((postResetRetainedCone_iff_at p c E rho w).mp hcone v)
    hv hHeadHorizon hx hip hseat N hem

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3040; plan RE-BIND D2/D3; DC: SAME cone at its label. -/
theorem healing_postReset_exactHead [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w) :
    ∀ v Q, HonestProposal E rho (fgsaInterface p c) v Q → w.sStar + 2 ≤ v →
      SA.voteTime p.toParams v ≤ rho.horizon →
      ∀ y ∈ rho.honest, headAtLabel p c E rho y v = some Q := by
  exact fun v Q hp hv hh => healing_postReset_exactHead_at E rho hrec mono w hreset
    ((postResetRetainedCone_iff_at p c E rho w).mp hcone v) Q hp hv hh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3040; plan RE-BIND D2/D3; DC: SAME cone at its label. -/
theorem healing_postReset_headCarrier [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w)
    {v : Slot} {Q : Block} (hp : HonestProposal E rho (fgsaInterface p c) v Q)
    (hv : w.sStar + 2 ≤ v)
    (hHeadHorizon : SA.voteTime p.toParams v ≤ rho.horizon)
    {y : V} {ih : Nat} (hy : y ∈ rho.honest)
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams v))) :
    let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams v)
    ∃ C : FGBlock (Fin p.n), eraseFG C = Q ∧ C ∈ domainR p dst (voterBlocks p dst v) := by
  exact healing_postReset_headCarrier_at E rho hrec mono w hreset
    ((postResetRetainedCone_iff_at p c E rho w).mp hcone v)
    hp hv hHeadHorizon hy hih

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3040; plan RE-BIND D2/D3; DC: SAME cone at its label. -/
theorem healing_postReset_opening_stored [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w)
    {v : Slot} {Q : Block} (hp : HonestProposal E rho (fgsaInterface p c) v Q)
    (hv : w.sStar + 2 ≤ v) {k : Nat} {x : V} (hx : x ∈ rho.honest)
    (ht : IsGateTick p c rho k x v) :
    ∃ D : FGBlock (Fin p.n), eraseFG D = Q ∧ D ∈ (storeAt p c E rho k x).fg.TF := by
  exact healing_postReset_opening_stored_at E rho hrec mono w hreset
    ((postResetRetainedCone_iff_at p c E rho w).mp hcone v) hp hv hx ht

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3040; plan RE-BIND D2/D3; DC: SAME cone at its label. -/
theorem healing_postReset_opening_clock_stored [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w)
    {v : Slot} {Q : Block} (hp : HonestProposal E rho (fgsaInterface p c) v Q)
    (hv : w.sStar + 2 ≤ v) {k : Nat} {x : V} (hx : x ∈ rho.honest)
    (ht : IsGateTick p c rho k x v) (r : Nat) (_hr : v = r * p.R) :
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho k x) (p.actionTime r)).st
    ∃ D : FGBlock (Fin p.n), eraseFG D = Q ∧ D ∈ st.fg.TF := by
  exact healing_postReset_opening_clock_stored_at E rho hrec mono w hreset
    ((postResetRetainedCone_iff_at p c E rho w).mp hcone v)
    hp hv hx ht r _hr

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3040; plan RE-BIND D2/D3; DC: SAME cone at its label. -/
theorem healing_postReset_gate_covered_prefix [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w)
    {v : Slot} {Q : Block} (hp : HonestProposal E rho (fgsaInterface p c) v Q)
    (hv : w.sStar + 2 ≤ v)
    (hGateHorizon : SA.gateTime p.toParams v ≤ rho.horizon) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head v)) q ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head v)) q) (SA.voteTime p.toParams v) = true →
      ∀ K, HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head v)) q)
        (ofHead p ⟨.seat (.head v) q, K.root⟩) (SA.voteTime p.toParams v) K →
        Block.Preceq Q K := by
  exact healing_postReset_gate_covered_prefix_at E rho hrec mono w hreset
    ((postResetRetainedCone_iff_at p c E rho w).mp hcone v)
    hp hv hGateHorizon

section RunConeWrappers
variable [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w)
    (cap : RCap p c E rho)
    (rowCovered : ∀ (_hb : Base₂ p c E rho)
      (_hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
      (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ C : FGBlock (Fin p.n),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st → (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))

include hrec mono hreset hcone cap rowCovered

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3040; plan RE-BIND D2/D3; DC: SAME cone at its label. -/
theorem healing_postReset_gate_raw (i : Nat)
    (hfp : PostResetFProv p c E rho w i)
    (hraw : PostResetRawTransfer p c E rho w i)
    {k : Nat} (hk : k < i) {x : V} {v : Slot} {Q : Block}
    (hx : x ∈ rho.honest) (ht : IsGateTick p c rho k x v)
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v)
    (hcut : timeIdx rho (SA.proposalTime p.toParams v) ≤ i) :
    gateResult p c E rho x v = some (some Q) := by
  exact healing_postReset_gate_raw_at E rho hrec mono w hreset cap rowCovered i
    ((postResetRetainedCone_iff_at p c E rho w).mp hcone v)
    hfp hraw hk hx ht hp hv hcut

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3040; plan RE-BIND D2/D3; DC: SAME cone at its label. -/
theorem healing_postReset_opening_source_prefix (i : Nat)
    (hfp : PostResetFProv p c E rho w i)
    (hraw : PostResetRawTransfer p c E rho w i)
    {x : V} {v : Slot} {Q : Block} (ht : IsGateTick p c rho i x v)
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v)
    (r : Nat) (hr : v = r * p.R)
    {K : FGBlock (Fin p.n)} {s : Slot}
    (hsource : SourceBefore p c E rho i K s) (hh : high p w K) :
    Block.Preceq (eraseFG K) Q := by
  exact healing_postReset_opening_source_prefix_at E rho hrec mono w hreset cap rowCovered i
    ((postResetRetainedCone_iff_at p c E rho w).mp hcone v)
    hfp hraw ht hp hv r hr hsource hh

variable (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
include xing origin

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3040; plan RE-BIND D2/D3; DC: SAME cone at its label. -/
theorem healing_postReset_openingDomain_new_tick (i : Nat)
    (hhigh : PostResetHighCompatible p c E rho w i)
    (hfp : PostResetFProv p c E rho w i)
    (hraw : PostResetRawTransfer p c E rho w i)
    {x : V} {v : Slot} {Q : Block} (hx : x ∈ rho.honest)
    (ht : IsGateTick p c rho i x v)
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v) :
    ∀ r, v = r * p.R →
      let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)).st
      ∃ D, eraseFG D = Q ∧ D ∈ domainR p st (treeT p st) := by
  exact healing_postReset_openingDomain_new_tick_at E rho hrec mono w hreset cap rowCovered
    xing origin i
    ((postResetRetainedCone_iff_at p c E rho w).mp hcone v) hhigh hfp hraw hx ht hp hv

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3040; plan RE-BIND D2/D3; DC: SAME cone at its label. -/
theorem healing_postReset_openingDomain_step (i : Nat)
    (hhigh : PostResetHighCompatible p c E rho w i)
    (hfp : PostResetFProv p c E rho w i)
    (hraw : PostResetRawTransfer p c E rho w i)
    (hopening : PostResetOpeningDomain p c E rho w i) :
    PostResetOpeningDomain p c E rho w (i + 1) := by
  exact healing_postReset_openingDomain_step_at E rho hrec mono w hreset cap rowCovered
    xing origin i
    (fun v _ => (postResetRetainedCone_iff_at p c E rho w).mp hcone v)
    hhigh hfp hraw hopening

end RunConeWrappers

end AvailableChain.FGSA.Run
end
