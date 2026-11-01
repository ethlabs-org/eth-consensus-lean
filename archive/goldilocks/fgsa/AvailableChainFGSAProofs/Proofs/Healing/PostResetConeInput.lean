module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetConeFrame -- shake: keep frame port
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetJoint2 -- shake: keep J6
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetConePool
public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

/-! Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE C5.
DC: SAME retained cone at the actual proposer and every honest HEAD read. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure RetainedWalk

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

variable [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
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
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
include hrec mono emittedNonempty emittedName writes xing origin h0r

variable (cap : RCap p c E rho)
    (source : TSrc p c E rho)
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
include cap source rowCovered

omit [DecidableEq V] [Fintype V] hrec mono emittedNonempty emittedName writes xing
    origin h0r cap source rowCovered in
private theorem cone_timeIdx_mono {a b : Time} (hab : a ≤ b) :
    timeIdx rho a ≤ timeIdx rho b := by
  change (rho.events.filter (fun e => decide (e.time ≤ a))).length ≤
    (rho.events.filter (fun e => decide (e.time ≤ b))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true ((of_decide_eq_true he).trans hab))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE C5.
DC: SAME all six RetainedConeInput fields at one proposal label.
C1 and H.14 roots supply root coverage; C2 supplies live lease coverage;
C3 supplies one common pivot and both floors; C4 supplies the actual pool counts. -/
theorem postReset_coneInput_at_cut (i : Nat)
    (hrl : PostResetResetLeaseCompatible p c E rho w i)
    (hlease : PostResetLeaseSafe p c E rho w i)
    (hraw : PostResetRawTransfer p c E rho w i)
    {s : Slot} (hs : w.sStar + 2 ≤ s)
    (hHeadHorizon : SA.voteTime p.toParams s ≤ rho.horizon)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hcut : timeIdx rho (SA.voteTime p.toParams s) ≤ i) :
    ∃ D : FGBlock (Fin p.n), ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hpv : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hprevTime : SA.voteTime p.toParams (s - 1) ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * ((s - 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    have hm : ((s - 1 : Nat) : Int) ≤ (s : Int) := by exact_mod_cast Nat.sub_le s 1
    nlinarith [p.deltaPos]
  have hprev := (cone_timeIdx_mono p c rho hprevTime).trans hcut
  have hsucc : s - 1 + 1 = s := by simp only [Slot] at *; omega
  obtain ⟨D, _m, _hm, _hh, hDp, hDr, hDHeads⟩ :=
    postReset_commonPivot_at_cut p c E rho hrec mono emittedNonempty emittedName writes
      xing origin h0r cap source rowCovered i hraw hs hx hip hcut
  obtain ⟨k, z0, a, C0, ha, _, hsrc, he0, hh0⟩ := h0r.fresh
  have ht0 : IsGateTick p c rho k z0 w.sStar := by rw [h0r.label]; exact ha.2.1
  have htime : SA.gateTime p.toParams w.sStar ≤ SA.voteTime p.toParams s := by
    have hI : (w.sStar : Int) + 2 ≤ (s : Int) := by exact_mod_cast hs
    change 4 * p.Δ * (w.sStar : Int) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith [p.deltaPos]
  have hk : k < i :=
    ((V2.D.Engine.index_lt_read_length_iff hS _ ht0).mpr htime).trans_le hcut
  have hCHeads : ∀ y ∈ rho.honest, ∀ H, headAtLabel p c E rho y (s - 1) = some H →
      Block.Preceq w.CStar H := by
    have hselected := selectedBefore_of_sourceBefore p c E rho
      ⟨k, z0, w.rStar, a, hk, ha, hsrc, h0r.label⟩
    have hhigh : high p w C0 := by rw [high_def, hh0]
    intro y hy H hH
    exact he0 ▸ postReset_source_heads_at_cut p c E rho hrec cap source rowCovered h0r
      i hraw hselected hhigh (s := s - 1) (by simp only [Slot] at *; omega) hprev y hy H hH
  have hroots (j : Nat) (z : V) (t : Time) (hz : z ∈ rho.honest)
      (ht : rho.events[j]? = some (.tick z t))
      (htype : t = SA.proposalTime p.toParams s ∨ t = SA.voteTime p.toParams s) :
      ∀ y ∈ rho.honest, ∀ H, headAtLabel p c E rho y (s - 1) = some H →
        Block.Preceq (eraseFG (controls p (clock p (storeAt p c E rho j z) t)).Z) H := by
    have hlo : SA.proposalTime p.toParams s ≤ t := by
      rcases htype with rfl | rfl <;> first | exact le_rfl | exact hpv
    have hhi : t ≤ SA.voteTime p.toParams s := by
      rcases htype with rfl | rfl <;> first | exact le_rfl | exact hpv
    have hji : j ≤ i :=
      (((V2.D.Engine.index_lt_read_length_iff hS _ ht).mpr hhi).trans_le hcut).le
    obtain ⟨C, hC, heC⟩ := postReset_cone_reset_held p c E rho hrec cap source h0r
      mono xing hs hz ht hlo
    rw [repair_controls_clock]
    change ∀ y ∈ rho.honest, ∀ H, headAtLabel p c E rho y (s - 1) = some H →
      Block.Preceq (eraseFG (R_at p c E rho j z).Z) H
    exact postReset_root_heads_at_cut p c E rho hrec cap source rowCovered h0r xing origin
      i hraw hz ht hji htype hC heC hCHeads hprev _ (by simp)
  have hleases := postReset_liveLease_heads_at_cut p c E rho hrec cap source rowCovered h0r
    i hrl hlease hraw writes hs hcut
  have hlive (j : Nat) (z : V) (t : Time) (hz : z ∈ rho.honest)
      (ht : rho.events[j]? = some (.tick z t))
      (htype : t = SA.proposalTime p.toParams s ∨ t = SA.voteTime p.toParams s) :
      ∀ y ∈ rho.honest, ∀ H, headAtLabel p c E rho y (s - 1) = some H →
        Block.Preceq (liveRoot p (clock p (storeAt p c E rho j z) t)) H := by
    rcases repair_liveRoot_cases (clock p (storeAt p c E rho j z) t) with
      he | ⟨row, hrow, hlive, _, he⟩
    · rw [he]
      exact hroots j z t hz ht htype
    · obtain ⟨hrow', hnow⟩ := repair_read_row htype hrow
      rw [hnow] at hlive
      rw [he]
      have hlo : SA.proposalTime p.toParams s ≤ t := by
        rcases htype with rfl | rfl <;> first | exact le_rfl | exact hpv
      have hhi : t ≤ SA.voteTime p.toParams s := by
        rcases htype with rfl | rfl <;> first | exact le_rfl | exact hpv
      exact hleases j z t row hz ht hlo hhi hrow' hlive
  have hZHeads : ∀ y ∈ rho.honest, ∀ H, headAtLabel p c E rho y (s - 1) = some H →
      Block.Preceq (eraseFG (R_at p c E rho ip x).Z) H := by
    have h := hroots ip x _ hx hip (Or.inl rfl)
    rwa [repair_controls_clock] at h
  have hfloor : (controls p (clock p (storeAt p c E rho ip x)
      (SA.proposalTime p.toParams s))).lo ≤ (heightView p D).h := by
    rw [repair_controls_clock]
    exact hDp.2.2
  have hGST : E.t_GST ≤ SA.voteTime p.toParams (s - 1) := by
    have hl : w.sStar ≤ s - 1 := by simp only [Slot] at *; omega
    apply h0r.synchronous.trans
    have hI : (w.sStar : Int) ≤ ((s - 1 : Nat) : Int) := by exact_mod_cast hl
    change 4 * p.Δ * (w.sStar : Int) + p.Δ ≤ 4 * p.Δ * ((s - 1 : Nat) : Int) + p.Δ
    nlinarith [p.deltaPos]
  have prior (L : Block)
      (hL : ∀ y ∈ rho.honest, ∀ H, headAtLabel p c E rho y (s - 1) = some H →
        Block.Preceq L H) :
      RetainedPriorSupport p (clock p (storeAt p c E rho ip x)
        (SA.proposalTime p.toParams s)) s L := by
    have hip' : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s - 1 + 1))) :=
      hsucc.symm ▸ hip
    have hf' : (controls p (clock p (storeAt p c E rho ip x)
        (SA.proposalTime p.toParams (s - 1 + 1)))).lo ≤ (heightView p D).h := hsucc.symm ▸ hfloor
    have hjoinCut := healing_reset_vote_cutoff h0r (by
      simp only [Slot] at *
      omega : w.sStar + 1 ≤ s - 1)
    have h := postReset_priorSupport_at_cut E rho hrec xing mono hHeadHorizon hGST hjoinCut
      hL hx hip' (by rw [hsucc]; exact hpv) hZHeads D hDHeads hf'
    change RetainedPriorSupport p (clock p (storeAt p c E rho ip x)
      (SA.proposalTime p.toParams (s - 1 + 1))) (s - 1 + 1) L at h
    rwa [hsucc] at h
  refine ⟨D, ?_⟩
  intro y hy ih hih
  let src := clock p (storeAt p c E rho ip x) (SA.proposalTime p.toParams s)
  let dst := clock p (storeAt p c E rho ih y) (SA.voteTime p.toParams s)
  refine ⟨Or.inr (prior _ (hlive ip x _ hx hip (Or.inl rfl))),
    Or.inr (Or.inl (prior _ (hlive ih y _ hy hih (Or.inr rfl)))),
    Or.inr (prior _ hDHeads), hfloor, ?_, ?_⟩
  · change (controls p dst).lo ≤ _
    rw [repair_controls_clock]
    exact (hDr y hy ih hih).2.2
  · intro L hL hstrict
    have hcover : ∀ z ∈ rho.honest, ∀ H, headAtLabel p c E rho z (s - 1) = some H →
        Block.Preceq L H := by
      rcases hL with rfl | rfl
      · change ∀ z ∈ rho.honest, ∀ H, headAtLabel p c E rho z (s - 1) = some H →
          Block.Preceq (eraseFG (controls p src).Z) H
        change ∀ z ∈ rho.honest, ∀ H, headAtLabel p c E rho z (s - 1) = some H →
          Block.Preceq (eraseFG (controls p (clock p (storeAt p c E rho ip x)
            (SA.proposalTime p.toParams s))).Z) H
        rw [repair_controls_clock]
        exact hZHeads
      · exact hDHeads
    have hFL : Block.Preceq (eraseFG (storeAt p c E rho ih y).fg.F) L := by
      change ((!decide (ay p dst = L)) && Block.preceq (ay p dst) L) = true at hstrict
      have hF := F_preceq_liveRoot p dst (cstoreInv_clock p _
        (cstoreInv_stateBefore E rho ih y) _)
      change Block.Preceq (eraseFG (clock p _ _).fg.F) _ at hF
      rw [clock_fg] at hF
      exact block_preceq_trans hF (Bool.and_eq_true_iff.mp hstrict).2
    have hih' : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (s - 1 + 1))) :=
      hsucc.symm ▸ hih
    have hjoinCut := healing_reset_vote_cutoff h0r (by
      simp only [Slot] at *
      omega : w.sStar + 1 ≤ s - 1)
    have h := postReset_targetScores_at_cut E rho hrec xing mono hHeadHorizon hGST hjoinCut
      hcover hy hih' (by rw [hsucc]) hFL
    simpa only [hsucc] using h

end AvailableChain.FGSA.Run
end
