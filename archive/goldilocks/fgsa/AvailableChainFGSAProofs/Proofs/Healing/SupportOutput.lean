module
public import AvailableChainFGSARun.Proofs.AC
public import AvailableChainFGSAProofs.Proofs.Healing.SupportLease

public section

/-! H-SUPPORT S3 output clause (plan §4 step 8; G7). Ruling B31 guards the clause with
`d_s + 4Δ ≤ v`: it then starts at the cut after the honest gates d_(s+1). -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.AC

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

omit [DecidableEq V] in
private theorem output_idx_lt (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {a b : Nat} {y : V} {ta tb : Time}
    (ha : rho.events[a]? = some (.tick y ta)) (hb : rho.events[b]? = some (.tick y tb))
    (hlt : ta < tb) : a < b := by
  rcases lt_trichotomy a b with h | h | h
  · exact h
  · subst h
    rw [ha] at hb
    cases hb
    exact absurd hlt (lt_irrefl _)
  · exact absurd (fgsa_tick_time_strict E rho hs hb ha h) (not_lt.mpr hlt.le)

omit [DecidableEq V] in
private theorem output_time_le (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {b : Nat} {e : V2.Event V (Obj p)}
    (hb : rho.events[b]? = some e) {v : Time} (hv : b < timeIdx rho v) : e.time ≤ v := by
  have he : rho.events.filter (fun e => decide (e.time < v + 1)) =
      rho.events.filter (fun e => decide (e.time ≤ v)) :=
    List.filter_congr (fun e _ => by simp only [Int.lt_add_one_iff])
  have hlt : b < V2.D.Run.idxBefore rho (v + 1) := by
    rw [V2.D.Run.idxBefore_def, he]
    exact hv
  exact Int.lt_add_one_iff.mp ((Gen.V2.Duty.index_lt_idxBefore_iff hs hb (v + 1)).mp hlt)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:748–783 (H.3), 1148–1252 (F1 + F2 + F4); plan H-SUPPORT §4 steps
7–8.
DC: INTENTIONAL every honest frame inside the phase, after an honest label-i HEAD witness
W ⪰ B reaches it, has Z and F below W and lo ≤ h(W). The F-root case uses RXing; the
top-J case uses the common J. So honest finality and B are comparable. -/
theorem healing_support_frame_at (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (_mono : RMono p c E rho) (crossing : RXing p c E rho)
    (hE : V2.D.ExecutionValid E rho) (_hDelta : E.Δ = p.Δ)
    {ΔF : Time} (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (_hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {i : Slot} (hhead : u ≤ SA.voteTime p.toParams i)
    (hev : SA.voteTime p.toParams i + p.Δ ≤ v)
    {jz : Nat} {z : V} (hz : z ∈ rho.honest)
    (hjz : rho.events[jz]? = some (.tick z (SA.voteTime p.toParams i)))
    (y : V) (hServices : HeadCarrierServices E rho jz z i y)
    {B : Block}
    (hBK : Block.Preceq B (headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho jz z).st
      (SA.voteTime p.toParams i)) i))
    {a : Nat} (hy : y ∈ rho.honest)
    (ha1 : V2.D.Run.idxBefore rho (SA.voteTime p.toParams i + p.Δ) ≤ a)
    (ha0 : V2.D.Run.idxBefore rho u ≤ a) (hav : a ≤ timeIdx rho v)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∃ W ∈ (storeAt p c E rho a y).fg.TF, Block.Preceq B (eraseFG W) ∧
      FGBlock.Preceq (R_at p c E rho a y).Z W ∧
      FGBlock.Preceq (storeAt p c E rho a y).fg.F W ∧
      (R_at p c E rho a y).lo ≤ (heightView p W).h := by
  have hS := hE.toScheduleWellFormed
  have hd := p.deltaPos
  have hvq : SA.voteTime p.toParams i ≤ v := (le_add_of_nonneg_right hd.le).trans hev
  obtain ⟨Kfg, hKfull, hKe, W, _, hKW, hloW, hrelay⟩ :=
    healing_head_witness_relay_on (hroots := hroots)
      p c E rho crossing hE hz hjz hy (hServices.relay
        (healing_head_carrier_demand_phase p c E rho crossing hE hphase hz hjz hhead hev hy))
  have hBW : Block.Preceq B (eraseFG W) := by
    refine Gen.Pure.block_preceq_trans hBK ?_
    have hKe' : eraseFG Kfg = headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho jz z).st
      (SA.voteTime p.toParams i)) i := hKe
    rw [← hKe']
    exact eraseFG_preceq hKW
  have hZK : FGBlock.Preceq (FGSA.controls p ((fgsa p c).clock (rho.stateBefore E jz z)
      (SA.voteTime p.toParams i)).st).Z Kfg :=
    ((KitFG.mem_filteredFromView _ _ _ _).mp hKfull).2.2.1
  have hRz : FGSA.controls p ((fgsa p c).clock (rho.stateBefore E jz z)
      (SA.voteTime p.toParams i)).st = R_at p c E rho jz z := by
    change KitFG.treeStoreControlsView (heightView p) (FGSA.clock p _ _).fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho jz _).fg
    rw [clock_fg]
    rfl
  rw [hRz] at hZK hloW
  have hfz := healing_settled_frame_strict p c E rho crossing u v m J contested hphase jz z
    (healing_support_idxBefore_le p c E rho hS hjz hhead)
    (healing_phase_lt_timeIdx p c E rho hS hjz hvq).le hz
  have hfy := healing_settled_frame_strict p c E rho crossing u v m J contested hphase a y
    ha0 hav hy
  have hWd : W ∈ (storeAt p c E rho
      (V2.D.Run.idxBefore rho (SA.voteTime p.toParams i + p.Δ)) y).fg.TF := by
    have h := hrelay W (KitFG.preceq_refl W)
    change W ∈ (V2.D.Run.stateBefore E rho _ y).st.fg.TF
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    exact h
  have hWy : W ∈ (storeAt p c E rho a y).fg.TF :=
    (fgsa_store_durable p c E rho ha1 y).1 hWd
  have hloy : (R_at p c E rho a y).lo ≤ (heightView p W).h := by
    have e1 : (R_at p c E rho a y).lo = (R_at p c E rho jz z).lo :=
      hfy.2.2.1.trans hfz.2.2.1.symm
    rw [e1]
    exact hloW
  refine ⟨W, hWy, hBW, ?_⟩
  cases J with
  | some J0 =>
    obtain ⟨_, _, hZy, _, _, hFJ⟩ := hfy.2.2.2.1
    obtain ⟨_, _, hZz, _, _, _⟩ := hfz.2.2.2.1
    have hZW : FGBlock.Preceq J0 W := by
      rw [← hZz]
      exact KitFG.preceq_trans hZK hKW
    refine ⟨?_, KitFG.preceq_trans hFJ hZW, hloy⟩
    change FGBlock.Preceq (FGSA.controls p (storeAt p c E rho a y)).Z W
    rw [hZy]
    exact hZW
  | none =>
    obtain ⟨_, hZy, ⟨Kc, hKc, hKcF, hKclt⟩, _⟩ := hfy.2.2.2.1
    have hFW := crossing a a y y Kc W hy le_rfl hKc hKcF ⟨hy, hWy⟩ (lt_of_lt_of_le hKclt hloy)
    refine ⟨?_, hFW, hloy⟩
    change FGBlock.Preceq (FGSA.controls p (storeAt p c E rho a y)).Z W
    rw [hZy]
    exact hFW

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:729–739 (H.2 S3 gate cases); plan H-SUPPORT §4 step 8, G7.
DC: INTENTIONAL one honest gate at a label whose honest HEADs cover B, with finality at
or below B. The raw result h covers B. A passed guard advances to a block above h or
keeps an output above h. A vetoed guard keeps the output: either it already covers B,
or the vetoing live lease is compatible with B, conflicts with h ⪰ B, so it is above B
and below the output. -/
theorem healing_output_gate_step [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    {w : Slot} {B : Block} (hgw : E.t_GST ≤ SA.voteTime p.toParams w)
    (hhor : SA.gateTime p.toParams w ≤ rho.horizon)
    (hcov : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z w = some K → Block.Preceq B K)
    {a : Nat} {y : V} (hy : y ∈ rho.honest)
    (ht : rho.events[a]? = some (.tick y (SA.gateTime p.toParams w)))
    (hScope : SupportGateScope E rho a y w)
    (hFB : Block.Preceq (eraseFG (storeAt p c E rho a y).fg.F) B)
    (hprev : Block.Preceq B (S_at p c E rho a y) ∨
      ∀ row ∈ (storeAt p c E rho a y).base.obligations, Block.Compatible row.1 B) :
    Block.Preceq B (S_at p c E rho (a + 1) y) := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hd := p.deltaPos
  obtain ⟨h, hh, hBh⟩ := healing_support_gate_cover E rho hrec hgw hhor hcov ht hScope
    (by rw [clockPre_fg]; exact hFB)
  let st := storeAt p c E rho a y
  let v := actView (clockPre p st (SA.gateTime p.toParams w))
  have hv : { v with early := st.base.early } = (fgsaAC E rho).gateView a y w :=
    fgsa_clockPre_gateView p st w
  have hraw : (fgsaAC E rho).raw a w y = some h := by
    have he := congrArg (fun u => SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) u w) hv
    rw [clockPre_fg] at hh
    have he' : (fgsaAC E rho).raw a w y =
        SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) v w := he.symm
    exact he'.trans hh
  have hf : (fgsaAC E rho).saved a y w = none := fgsa_gate_fresh E rho hS ht
  rw [S_at_def]
  change Block.Preceq B ((fgsaAC E rho).output (a + 1) y)
  rcases (fgsaAC_gate_write E rho a w y (by
    rw [clockPre_joined]
    exact fgsa_gate_joined_of_enabled E rho hScope.enabled) ht).effects with hskip | hrun
  · obtain ⟨⟨result, hr⟩, _⟩ := hskip
    rw [hf] at hr
    cases hr
  by_cases hg : ∀ lease ∈ ((fgsaAC E rho).gateView a y w).obligations,
      Block.Compatible (Lease.target lease) h
  · obtain ⟨hout, _, _⟩ := hrun.accept h hraw hg
    rw [hout]
    have hX : Block.Preceq B (GridCO.advance ((fgsaAC E rho).output a y) h) := by
      unfold GridCO.advance
      split
      · rename_i hhS
        exact Gen.Pure.block_preceq_trans hBh hhS
      · exact hBh
    rw [normalizeOutput_def]
    have ha : Block.preceq ((fgsaAC E rho).anchor a y)
        (GridCO.advance ((fgsaAC E rho).output a y) h) = true :=
      Gen.Pure.block_preceq_trans hFB hX
    simp only [ha, ↓reduceIte]
    exact hX
  · obtain ⟨lease, hl, hnc⟩ : ∃ lease ∈ ((fgsaAC E rho).gateView a y w).obligations,
        ¬ Block.Compatible (Lease.target lease) h := by
      simpa only [not_forall, exists_prop] using hg
    obtain ⟨hout, _, _⟩ := hrun.veto h hraw ⟨lease, hl, hnc⟩
    rw [hout]
    rcases hprev with hold | hcomp
    · exact hold
    obtain ⟨K, g, d⟩ := lease
    have hl' := List.mem_filter.mp hl
    have hmem : (K, g, d) ∈ (storeAt p c E rho a y).base.obligations := hl'.1
    have hdl : SA.gateTime p.toParams w < d := of_decide_eq_true hl'.2
    have hgpos : 0 < SA.gateTime p.toParams w := by
      change 0 < 4 * p.Δ * (w : Int) + 6 * p.Δ
      positivity
    have hnow : (fgsaAC E rho).now a y < d :=
      (fgsa_preTick_now_lt_joined E rho hS ht hgpos
        (fgsa_gate_joined_of_enabled E rho hScope.enabled)).trans hdl
    have hKS : Block.Preceq K ((fgsaAC E rho).output a y) :=
      fgsaAC_lease_le_output E rho a y hy (K, g, d) hmem hnow
    have hKB : Block.Compatible K B := hcomp (K, g, d) hmem
    change ¬ Block.Compatible K h at hnc
    rcases Bool.or_eq_true_iff.mp hKB with hKB' | hBK
    · exact absurd (Bool.or_eq_true_iff.mpr (Or.inl (Gen.Pure.block_preceq_trans hKB' hBh)))
        hnc
    · exact Gen.Pure.block_preceq_trans hBK hKS

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:721–739 (H.2 S3), 1012–1045 (frame); plan H-SUPPORT §4 step 8, G7,
G8;
ruling B31. DC: INTENTIONAL the guarded S3 output clause from a HEAD clause and the
lease invariant at the gates d_(s+1). From the cut after d_(s+1) to the end of the
interval, every honest output covers B. Finality and B are comparable in the phase
(`healing_support_F_cover`). If B ⪯ F, the output is above F. Otherwise a reconcile keeps
the output, and each gate is `healing_output_gate_step`. -/
theorem healing_output_cover [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams s)
    (hCut : HealingWindow p E 1 s)
    (hguard : SA.gateTime p.toParams s + 4 * p.Δ ≤ v)
    (hheads : ∀ i, s + 1 ≤ i → SA.voteTime p.toParams i ≤ v →
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K → Block.Preceq B K)
    (hGates : ∀ w, s + 1 ≤ w → SA.gateTime p.toParams w ≤ v →
        ∀ j y, y ∈ rho.honest → IsGateTick p c rho j y w →
      enabledGateAt p c E rho j y w → ∀ B,
      GateReceiptGeometry E rho
        (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w)) w B →
      SupportGateScope E rho j y w)
    (hServices : ∀ w, s + 1 ≤ w →
      ∀ iy y t, t ≤ v → HealingCarriersAt E rho w iy y t)
    (hlease : ∀ j y, y ∈ rho.honest → IsGateTick p c rho j y (s + 1) →
      Block.Preceq (eraseFG (storeAt p c E rho j y).fg.F) B →
      ∀ row ∈ (storeAt p c E rho j y).base.obligations, Block.Compatible row.1 B) :
    ∀ i y, y ∈ rho.honest → afterTicksIdx rho (SA.gateTime p.toParams s + 4 * p.Δ) ≤ i →
      i ≤ timeIdx rho v → Block.Preceq B (S_at p c E rho i y) := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  have hG1 : SA.gateTime p.toParams s + 4 * p.Δ = SA.gateTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ + 4 * p.Δ =
      4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    push_cast
    ring
  rw [hG1] at hguard ⊢
  intro i y hy hai hiv
  have hhor : SA.gateTime p.toParams (s + 1) ≤ rho.horizon := hguard.trans hphase.2.1
  have hvs : SA.voteTime p.toParams s ≤ SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hq1 : SA.voteTime p.toParams (s + 1) + p.Δ ≤ SA.gateTime p.toParams (s + 1) := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ + p.Δ ≤
      4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    linarith
  have hq1v : SA.voteTime p.toParams (s + 1) + p.Δ ≤ v := hq1.trans hguard
  have hqv : SA.voteTime p.toParams (s + 1) ≤ v :=
    (le_add_of_nonneg_right hd.le).trans hq1v
  have hgst1 : E.t_GST ≤ SA.voteTime p.toParams (s + 1) := hgst.trans (hhead.trans hvs)
  have hu1 : u ≤ SA.voteTime p.toParams (s + 1) := hhead.trans hvs
  -- The honest gate tick of y at d_(s+1); the cut state is its post-gate state.
  have htime1 : ((4 * (s + 1) + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams (s + 1) := by
    change _ = 4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨j1, hj1, _⟩ := fgsa_tick_total E rho hS hDelta y hy (4 * (s + 1) + 6)
    (htime1 ▸ hhor) (htime1 ▸ hrec.awake y hy _
      (hgst1.trans (by
        change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ ≤
          4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
        linarith)) hhor)
  rw [htime1] at hj1
  have hcut : V2.D.Run.stateBefore E rho (afterTicksIdx rho (SA.gateTime p.toParams (s + 1))) y =
      V2.D.Run.stateBefore E rho (j1 + 1) y := by
    rw [← congrFun (afterTicks_eq_stateBefore E rho hS _) y, afterTicks_node E rho hS hj1,
      V2.D.Run.stateBefore_succ E rho hj1]
    simp only [V2.D.World.step, Function.update_self]
  have hidx1 : V2.D.Run.idxBefore rho (SA.gateTime p.toParams (s + 1)) ≤
      afterTicksIdx rho (SA.gateTime p.toParams (s + 1)) := by
    have h := (preIdx_le_afterTicksIdx E rho hS (SA.gateTime p.toParams (s + 1))).1
    rw [V2.D.Run.idxBefore_def]
    exact h
  have hj1i : V2.D.Run.idxBefore rho (SA.gateTime p.toParams (s + 1)) ≤ j1 :=
    not_lt.mp (fun h => lt_irrefl _
      ((Gen.V2.Duty.index_lt_idxBefore_iff hS hj1 _).mp h))
  have hj1v : j1 < timeIdx rho v := healing_phase_lt_timeIdx p c E rho hS hj1 hguard
  -- The witness of y's own HEAD at s+1, and the finality/B comparison.
  obtain ⟨jz, hjz⟩ := healing_support_vote_tick E rho hS hDelta hy (s + 1)
    (hqv.trans hphase.2.1) (hrec.awake y hy _ hgst1 (hqv.trans hphase.2.1))
  have hhl : headAtLabel p c E rho y (s + 1) = some (headVote p (FGSA.clock p
      (V2.D.Run.stateBefore E rho jz y).st (SA.voteTime p.toParams (s + 1))) (s + 1)) := by
    unfold headAtLabel
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hjz]
    rfl
  have hBK := hheads (s + 1) le_rfl hqv y hy _ hhl
  have hidxmono {t t' : Time} (htt : t ≤ t') :
      V2.D.Run.idxBefore rho t ≤ V2.D.Run.idxBefore rho t' := by
    rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def]
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he => decide_eq_true
      (lt_of_lt_of_le (of_decide_eq_true he) htt))
  have hFc (b : Nat) (hb1 : V2.D.Run.idxBefore rho (SA.gateTime p.toParams (s + 1)) ≤ b)
      (hbv : b ≤ timeIdx rho v) :
      Block.Preceq B (eraseFG (storeAt p c E rho b y).fg.F) ∨
        Block.Preceq (eraseFG (storeAt p c E rho b y).fg.F) B := by
    obtain ⟨W, _, hBW, _, hFW, _⟩ := healing_support_frame_at
      (hroots := hrec.base.receiptIdealization)
      E rho (fun _ => mono) crossing hE hDelta
      hrec.sync hgst hphase hu1 hq1v hy hjz
      y (healing_carriers_window_at p c E rho hrec (hCut.cut_mono (Nat.le_succ s))
        (hServices (s + 1) le_rfl j1 y _ hguard) hy hj1 hq1 jz y hy hjz) hBK hy
      ((hidxmono hq1).trans hb1)
      ((hidxmono (hu1.trans ((le_add_of_nonneg_right hd.le).trans hq1))).trans hb1) hbv
    rcases Gen.Pure.block_preceq_total_of_common (eraseFG_preceq hFW) hBW with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hanchor (b : Nat) (h : Block.Preceq B (eraseFG (storeAt p c E rho b y).fg.F)) :
      Block.Preceq B (S_at p c E rho b y) :=
    Gen.Pure.block_preceq_trans h (fgsaAC_anchor_le_output E rho b y)
  have hFmono {a b : Nat} (hab : a ≤ b)
      (h : Block.Preceq (eraseFG (storeAt p c E rho b y).fg.F) B) :
      Block.Preceq (eraseFG (storeAt p c E rho a y).fg.F) B :=
    Gen.Pure.block_preceq_trans (eraseFG_preceq (mono a b y hy hab).1) h
  -- Base: the gate d_(s+1) of y.
  have hbase : Block.Preceq B (S_at p c E rho (j1 + 1) y) := by
    rcases hFc (j1 + 1) (hj1i.trans (Nat.le_succ _)) hj1v with hBF | hFB
    · exact hanchor _ hBF
    have hFB0 := hFmono (Nat.le_succ _) hFB
    exact healing_output_gate_step E rho hrec hgst1 hhor (hheads (s + 1) le_rfl hqv) hy hj1
      (hGates (s + 1) le_rfl hguard j1 y hy hj1
        (healing_recovery_later_gate E rho hrec (hgst.trans hhead) le_rfl hy hj1) B
        (healing_support_gate_geometry E rho hS (hheads (s + 1) le_rfl hqv)
          (by rw [clockPre_fg]; exact hFB0)))
      hFB0 (Or.inr (hlease j1 y hy hj1 hFB0))
  -- Induction along the events of the interval.
  let a0 := afterTicksIdx rho (SA.gateTime p.toParams (s + 1))
  have h0 : Block.Preceq B (S_at p c E rho a0 y) := by
    rw [S_at_def]
    change Block.Preceq B (V2.D.Run.stateBefore E rho a0 y).st.base.stableRecord
    rw [hcut]
    exact hbase
  suffices hn : ∀ n, a0 + n ≤ timeIdx rho v → Block.Preceq B (S_at p c E rho (a0 + n) y) by
    have h := hn (i - a0) (by omega)
    rwa [Nat.add_sub_cancel' hai] at h
  intro n
  induction n with
  | zero => intro _; exact h0
  | succ n ih =>
    intro hn
    have hIH := ih (by omega)
    let b := a0 + n
    have hb1 : V2.D.Run.idxBefore rho (SA.gateTime p.toParams (s + 1)) ≤ b :=
      hidx1.trans (Nat.le_add_right _ _)
    change Block.Preceq B (S_at p c E rho (b + 1) y)
    rcases hFc (b + 1) (hb1.trans (Nat.le_succ _)) hn with hBF | hFB
    · exact hanchor _ hBF
    have hFb := hFmono (Nat.le_succ _) hFB
    rcases fgsaAC_output_step E rho b y with hsame | ⟨w, hw⟩ | hrc | ⟨t, hr, _⟩
    · rw [S_at_def]
      change Block.Preceq B ((fgsaAC E rho).output (b + 1) y)
      rw [hsame]
      exact hIH
    · -- A gate d_w with s+1 ≤ w and d_w ≤ v.
      have hwv : SA.gateTime p.toParams w ≤ v := output_time_le E rho hS hw (by omega)
      have hw1 : SA.gateTime p.toParams (s + 1) ≤ SA.gateTime p.toParams w :=
        not_lt.mp (fun h => absurd ((Gen.V2.Duty.index_lt_idxBefore_iff hS hw _).mpr h)
          (not_lt.mpr hb1))
      have hwI : (s : Int) + 1 ≤ (w : Int) := by
        have h : (4 * ((s + 1 : Nat) : Int) + 6) * p.Δ ≤ (4 * (w : Int) + 6) * p.Δ := by
          change 4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ ≤ 4 * p.Δ * (w : Int) + 6 * p.Δ
            at hw1
          linarith
        have h2 := le_of_mul_le_mul_right h hd
        push_cast at h2
        omega
      have hvw : SA.voteTime p.toParams w ≤ SA.gateTime p.toParams w := by
        change 4 * p.Δ * (w : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + 6 * p.Δ
        linarith
      have hgw : E.t_GST ≤ SA.voteTime p.toParams w := by
        refine hgst1.trans ?_
        change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + p.Δ
        push_cast
        nlinarith
      exact healing_output_gate_step E rho hrec hgw (hwv.trans hphase.2.1)
        (hheads w (by exact_mod_cast hwI) (hvw.trans hwv)) hy hw
        (hGates w (by exact_mod_cast hwI) hwv b y hy hw
          (healing_recovery_later_gate E rho hrec (hgst.trans hhead)
            (by exact_mod_cast hwI) hy hw) B
          (healing_support_gate_geometry E rho hS
            (hheads w (by exact_mod_cast hwI) (hvw.trans hwv))
            (by rw [clockPre_fg]; exact hFb))) hFb (Or.inl hIH)
    · -- A reconcile keeps an output above B, since the new finality is below B.
      obtain ⟨_, _, _, _, _, _, hout⟩ := hrc
      rw [S_at_def]
      change Block.Preceq B ((fgsaAC E rho).output (b + 1) y)
      rw [hout, normalizeOutput_def]
      have ha : Block.preceq ((fgsaAC E rho).anchor (b + 1) y)
          ((fgsaAC E rho).output b y) = true :=
        Gen.Pure.block_preceq_trans hFB hIH
      simp only [ha, ↓reduceIte]
      exact hIH
    · rw [S_at_def] at hIH ⊢
      change Block.Preceq B (rho.stateBefore E (b + 1) y).st.base.stableRecord
      rw [V2.D.Run.stateBefore_succ E rho hr]
      simp only [V2.D.World.step, Function.update_self]
      change Block.Preceq B (acRestart p (rho.stateBefore E b y).st t).base.stableRecord
      rw [acRestart_stableRecord]
      exact hIH

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:620–739 (H.1 + H.2 S3, fast arm); plan H-SUPPORT §4 steps 1–8; ruling
B31. DC: INTENTIONAL the guarded S3 output clause for a fast PhaseBody arm. -/
theorem healing_fast_output [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v)
    (hguard : SA.gateTime p.toParams s + 4 * p.Δ ≤ v)
    {x : V} (hx : x ∈ rho.honest) {nd : Node p}
    (hnd : postClock E rho x (SA.gateTime p.toParams s) = some nd)
    (hB : B ∈ (fastWriteAt nd.st s).getD [])
    (hScopes : FastSupportScope E rho s v x)
    (hCut : HealingWindow p E 1 s) :
    ∀ i y, y ∈ rho.honest → afterTicksIdx rho (SA.gateTime p.toParams s + 4 * p.Δ) ≤ i →
      i ≤ timeIdx rho v → Block.Preceq B (S_at p c E rho i y) := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  have hheads := healing_fast_heads E rho hrec mono crossing writes hgst hphase hhead hgate hx
    hnd hB hScopes hCut
  refine healing_output_cover E rho hrec mono crossing hgst hphase hhead hCut hguard hheads
    hScopes.gates hScopes.carriers ?_
  intro j y hy ht hFB
  have hq : SA.voteTime p.toParams (s + 1) < SA.gateTime p.toParams (s + 1) := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    linarith
  have hgv : SA.gateTime p.toParams (s + 1) ≤ v := by
    refine le_trans (le_of_eq ?_) hguard
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ = 4 * p.Δ * (s : Int) + 6 * p.Δ + 4 * p.Δ
    push_cast
    ring
  obtain ⟨iq, hiq⟩ := healing_support_vote_tick E rho hS hDelta hy (s + 1)
    ((hq.le.trans hgv).trans hphase.2.1) (hrec.awake y hy _ (by
      refine (hgst.trans hhead).trans ?_
      change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
      push_cast
      nlinarith) ((hq.le.trans hgv).trans hphase.2.1))
  have hqa : iq < j := output_idx_lt E rho hS hiq ht hq
  refine healing_fast_lease_at E rho hrec mono writes (hgst.trans hhead)
    (hgate.trans hphase.2.1) hx hnd hB hphase.2.1 hScopes
    (healing_gate_cut_of_batch_cut E s hCut.2) ?_ hy hiq hqa ?_ hFB
  · intro w hw hwT
    refine hheads w hw (le_trans ?_ hwT)
    change 4 * p.Δ * (w : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + 6 * p.Δ
    linarith
  · intro j' t hj' ht'
    exact ((fgsa_tick_time_strict E rho hS ht' ht hj').le).trans hgv

end AvailableChain.FGSA.Run
end
