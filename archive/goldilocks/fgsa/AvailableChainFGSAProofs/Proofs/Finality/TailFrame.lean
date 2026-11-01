module
public import AvailableChainFGSAProofs.Proofs.Finality.TailOpening
public import AvailableChainFGSAProofs.Proofs.Finality.Rows
public import AvailableChainFGSAProofs.Proofs.Finality.CoreServices
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainGeneric.Proofs.Pure.BlockOrder -- shake: keep (block order)
public import AvailableChainKitFG.ProvenanceCore

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG

/-! ### Read-index bridges -/

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [DecidableEq V] in
/-- Paper 22:1702–1706 (Q0 cuts). A tick strictly later than a cut time is at or after
the post-gate cut. DC: INTENTIONAL: event phases order same-time ticks first. -/
theorem ktail_afterTicksIdx_le (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {v : V} {t u : Time} (hi : rho.events[i]? = some (.tick v u)) (ht : t < u) :
    afterTicksIdx rho t ≤ i := by
  by_contra hn
  have hf := V2.D.Engine.filter_eq_take hs (cutPred t) (fun e f hk hf =>
    decide_eq_true (hk.trans (of_decide_eq_true hf)))
  have hm : (V2.Event.tick v u : V2.Event V (fgsa p c).Object) ∈
      rho.events.filter (cutPred t) := by
    rw [hf]
    apply List.mem_of_getElem? (i := i)
    change (rho.events.take (afterTicksIdx rho t))[i]? = some _
    rw [List.getElem?_take_of_lt (Nat.lt_of_not_le hn)]
    exact hi
  have hkey : toLex (u, (1 : Nat)) ≤ toLex (t, (1 : Nat)) :=
    of_decide_eq_true (List.mem_filter.mp hm).2
  rcases Prod.Lex.toLex_le_toLex.mp hkey with h | ⟨h, _⟩
  · exact absurd (h.trans ht) (lt_irrefl _)
  · have hut : u = t := h
    rw [hut] at ht
    exact absurd ht (lt_irrefl _)

/-- Paper 22:1228–1254 (action read). The post-clock action read is the store after
the action tick: the own-record fold keeps the store.
DC: INTENTIONAL: the run reads the FG source and head at the post-clock state. -/
theorem ktail_action_store (x : V) (t : Time) (nd : Node p)
    (hnd : postClock E rho x t = some nd) :
    ∃ k, rho.events[k]? = some (.tick x t) ∧
      (fgsa p c).clock (V2.D.Run.stateBefore E rho k x) t = nd ∧
      storeAt p c E rho (k + 1) x = nd.st := by
  rw [postClock_def, preTick_def] at hnd
  cases hj : V2.D.Run.tickIdx? rho x t with
  | none => rw [hj] at hnd; cases hnd
  | some k =>
    rw [hj] at hnd
    have hk := V2.D.Run.tickIdx?_spec hj
    have hclock : (fgsa p c).clock (V2.D.Run.stateBefore E rho k x) t = nd :=
      Option.some.inj hnd
    refine ⟨k, hk, hclock, ?_⟩
    have fold : ∀ (l : List (Obj p)) (n : Node p),
        (l.foldl (fgsa p c).recordOwn n).st = n.st := by
      intro l
      induction l with
      | nil => intro n; rfl
      | cons o l ih => intro n; exact (ih _).trans (recordOwn_st (c := c) n o)
    change (V2.D.Run.stateBefore E rho (k + 1) x).st = nd.st
    rw [(V2.D.Run.step_tick_eq E rho hk).1, V2.D.tick_decomp]
    exact (fold _ _).trans (congrArg Node.st hclock)

/-! ### The frame guards from the store controls -/

omit [DecidableEq V] in
/-- Paper 22:1690–1700 (Q0 frame), plan §2 "hD" and "hframe". In a store whose
finality is below Q and whose blocks are capped at Q's height, Q passes all four
frame guards and is in the full filtered tree. The uncontested root J is below Q because
Q is at the frontier height; the band floor is at most the frontier height.
DC: INTENTIONAL: the FG-SA frame filter reads the store controls. -/
theorem ktail_frame_of_store (st : State p.n)
    (hI : KitFG.FGStoreInvariant (heightView p) (finalityView p) st.fg)
    (Q : FGBlock (Fin p.n)) (hQ : Q ∈ st.fg.TF)
    (hcap : ∀ B ∈ st.fg.TF, (heightView p B).h ≤ (heightView p Q).h)
    (hF : FGBlock.Preceq st.fg.F Q) :
    Q ∈ st.fg.TF ∧ FGBlock.Preceq (FGSA.controls p st).F Q ∧
      FGBlock.Preceq (FGSA.controls p st).Z Q ∧
      (FGSA.controls p st).lo ≤ (heightView p Q).h ∧ Q ∈ FGSA.fullTree p st := by
  have hmax : st.fg.h_max = (heightView p Q).h := by
    rw [hI.hmax]
    apply le_antisymm
    · exact sup_le (Finset.sup_le hcap) ((fgCertificateLaws p).height.one_le_h Q)
    · exact le_sup_of_le_left (Finset.le_sup (f := fun B => (heightView p B).h) hQ)
  have hc : FGSA.controls p st = ⟨st.fg.F, st.fg.h_max, st.fg.h_j, st.fg.J,
      decide (st.fg.h_max = st.fg.h_j + 1) &&
        decide (∃ W ∈ st.fg.TF, FGBlock.Preceq st.fg.F W ∧
          (heightView p W).h = st.fg.h_max ∧
          ¬ FGBlock.Preceq st.fg.J W)⟩ := by
    unfold FGSA.controls
    rw [KitFG.treeStoreControlsView_def]
  have hZ : FGBlock.Preceq (FGSA.controls p st).Z Q := by
    rw [hc]
    unfold Controls.Z Controls.rootIsJ
    dsimp only
    split_ifs with hr
    · rw [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hr
      obtain ⟨htop, hcon⟩ := hr
      by_contra hn
      have hex : decide (∃ W ∈ st.fg.TF, FGBlock.Preceq st.fg.F W ∧
          (heightView p W).h = st.fg.h_max ∧
          ¬ FGBlock.Preceq st.fg.J W) = true :=
        decide_eq_true ⟨Q, hQ, hF, hmax.symm, hn⟩
      rw [hex, htop] at hcon
      simp at hcon
    · exact hF
  have hlo : (FGSA.controls p st).lo ≤ (heightView p Q).h := by
    rw [hc]
    unfold Controls.lo
    dsimp only
    split_ifs
    · exact hmax.le
    · exact (Nat.sub_le _ _).trans hmax.le
  have hFc : FGBlock.Preceq (FGSA.controls p st).F Q := by rw [hc]; exact hF
  refine ⟨hQ, hFc, hZ, hlo, ?_⟩
  change Q ∈ KitFG.filteredFromView (heightView p) (FGSA.controls p st) st.fg.TF
  exact (KitFG.mem_filteredFromView (heightView p) _ _ Q).mpr
    ⟨hQ, hFc, hZ, Q, hQ, KitFG.preceq_refl Q, hlo⟩

/-! ### Q0 at the Tail witness -/

variable [Fintype V] {p c E rho}

/-- Paper 22:1702–1706 (Q0 criterion), plan §2 "hFgate". At an honest read inside the
healed suffix and before the next action's read cut, if Q is below the stable output,
the local finality is below Q. H4 makes F and Q compatible; a finalized proper descendant
of Q would be an entry of height ≥ e+1, but held finality is below e.
DC: INTENTIONAL: certificate height and block height stay distinct. -/
theorem ktail_F_below_witness {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) (ow : TailOpeningWitness_W p c E rho ΔF pt)
    (i : Nat) (x : V) (hx : x ∈ rho.honest)
    (hsuf : HealSuffix p c rho (tstar p pt.w) i)
    (hcut : i ≤ afterTicksIdx rho (p.actionTime (pt.r + 1)))
    (hS : Block.Preceq (eraseFG ow.Q) (S_at p c E rho i x)) :
    FGBlock.Preceq (storeAt p c E rho i x).fg.F ow.Q := by
  have laws := (fgCertificateLaws p).height
  have hI := (cstoreInv_stateBefore E rho i x).fg
  have hFS : Block.Preceq (F_at p c E rho i x) (S_at p c E rho i x) :=
    hT.input.healed.2.2.1 i x x hsuf hx
      (ktail_suffix_confirmed hT hx hsuf (ktail_start_horizon hT))
  rcases Gen.Pure.block_preceq_total_of_common hFS hS with h | h
  · exact kmid_lift_preceq p h
  · exfalso
    have hQF : FGBlock.Preceq ow.Q (V2.D.Run.stateBefore E rho i x).st.fg.F :=
      kmid_lift_preceq p h
    obtain ⟨D, hD, hDF⟩ := hI.Fcar
    have hFh : (finalityView p D).h_F < ow.e := ow.finalityThroughAction i x D hcut ⟨hx, hD⟩
    have hQne : ow.Q ≠ .genesis := by
      intro hg
      have hs := ow.slotQ
      rw [hg] at hs
      have h0 : (0 : Nat) = pt.carrier := hs
      have := hT.carrier.1
      have := (ktail_bounds hT).2.1
      omega
    by_cases hz : (finalityView p D).h_F = 0
    · have hg := (fgCertificateLaws p).finalized_zero D hz
      rw [hDF] at hg
      rw [hg] at hQF
      exact hQne (preceq_genesis.mp hQF)
    · obtain ⟨C, -, hCJ, hCj⟩ := KitFG.provenance_finality_of_certificate p.E
        (heightView p) (finalityView p) (fgCertificateLaws p) D hz
      have hJh := (fgJustificationLaws p).J_height C (by rw [hCj]; exact hz)
      rw [hCJ, hCj, hDF] at hJh
      have hm := laws.h_mono hQF
      rw [hJh, ow.heightQ] at hm
      simp only [Height] at *
      omega

/-- Paper 22:1690–1700 (Q0 suffix). The healed suffix starts at the post-gate cut of t*.
DC: INTENTIONAL: index form of the H-time cut. -/
theorem ktail_healStart {G ΔF : Time} {pt : TailKernelPt p}
    (_hT : TailKernelPrem_W p c G ΔF E rho pt) :
    healStart p c rho (tstar p pt.w) = afterTicksIdx rho (tstar p pt.w) := by
  have hgate : isGateTime p (tstar p pt.w) = true :=
    (isGateTime_iff p _).mpr ⟨pt.w.u, rfl⟩
  unfold healStart
  rw [hgate, ite_eq_left rfl]

/-- Paper 22:1690–1700 (Q0 suffix). The action read is inside the healed suffix and
before the next action's read cut. DC: INTENTIONAL: index forms of the H-time cuts. -/
theorem ktail_action_suffix {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) {k : Nat} {x : V}
    (hk : rho.events[k]? = some (.tick x (p.actionTime (pt.r + 1)))) :
    HealSuffix p c rho (tstar p pt.w) k ∧ HealSuffix p c rho (tstar p pt.w) (k + 1) ∧
      k + 1 ≤ afterTicksIdx rho (p.actionTime (pt.r + 1)) := by
  have hs := hT.set.base.valid.toScheduleWellFormed
  have hstart : tstar p pt.w ≤ (pt.r : Time) * P p := hT.start
  rw [kmid_period_eq] at hstart
  have hlt : tstar p pt.w < p.actionTime (pt.r + 1) := by
    have h1 := kmid_proposal_le_action p (r := pt.r) (s := pt.r * p.R) le_rfl
    have h2 := kmid_action_strictMono p (Nat.lt_succ_self pt.r)
    change tstar p pt.w ≤ SA.proposalTime p.toParams (pt.r * p.R) at hstart
    exact lt_of_le_of_lt hstart (lt_of_le_of_lt h1 h2)
  have hle := ktail_afterTicksIdx_le p c E rho hs hk hlt
  have hlen : k < rho.events.length := (List.getElem?_eq_some_iff.mp hk).1
  have hhs := ktail_healStart hT
  refine ⟨⟨by rw [hhs]; exact hle, hlen.le⟩, ⟨by rw [hhs]; omega, hlen⟩,
    kmid_tick_lt_afterTicks p c E rho hs hk le_rfl⟩

/-- Paper 22:1988–1990 (H3 exact gate value of the witness, then H4 monotonicity).
From the witness gate cut on, inside the healed suffix, every honest stable output
extends Q. DC: INTENTIONAL: index form of the H3/H4 reads. -/
theorem ktail_S_cover_after {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) (ow : TailOpeningWitness_W p c E rho ΔF pt)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hi : afterTicksIdx rho (SA.gateTime p.toParams pt.carrier) ≤ i)
    (hsuf : HealSuffix p c rho (tstar p pt.w) i) :
    Block.Preceq (eraseFG ow.Q) (S_at p c E rho i x) := by
  have hs := hT.set.base.valid.toScheduleWellFormed
  obtain ⟨hκ2, -⟩ := (ktail_bounds hT).2
  have hc2 : (pt.carrier : Nat) ≤ (pt.r + 1) * p.R := hT.carrier.2.1
  have hhorG : SA.gateTime p.toParams pt.carrier ≤ rho.horizon :=
    (ktail_slot_horizon hT (s := pt.carrier) (le_trans hc2 (Nat.le_add_right _ _))).2.2
      (Nat.add_le_add hc2 hκ2)
  have hstable := ((ow.serviceQ.2 hhorG x hx
      (ktail_window_confirmed hT (by have hc := hT.carrier.1; omega) hhorG hx)).2.2.2).1
  rw [afterTicks_eq_stateBefore E rho hs] at hstable
  have hsuf₀ : HealSuffix p c rho (tstar p pt.w)
      (afterTicksIdx rho (SA.gateTime p.toParams pt.carrier)) := by
    refine ⟨?_, le_trans hi hsuf.2⟩
    rw [ktail_healStart hT]
    apply afterTicksIdx_mono
    have hstart : tstar p pt.w ≤ (pt.r : Time) * P p := hT.start
    rw [kmid_period_eq] at hstart
    have h1 := kmid_slot_scale_le p (show pt.r * p.R ≤ (pt.carrier : Nat) by
      have := hT.carrier.1; omega)
    have := p.deltaPos
    change tstar p pt.w ≤ 4 * p.Δ * (pt.carrier : Time) + 6 * p.Δ
    linarith
  have hmono := hT.input.ac.h4.2.2.1
    (afterTicksIdx rho (SA.gateTime p.toParams pt.carrier)) i x hsuf₀ hsuf hi
    (ktail_suffix_confirmed hT hx hsuf₀ (ktail_start_horizon hT))
    (ktail_suffix_confirmed hT hx hsuf (ktail_start_horizon hT))
  have hS₀ : S_at p c E rho (afterTicksIdx rho (SA.gateTime p.toParams pt.carrier)) x =
      eraseFG ow.Q := hstable
  rw [← hS₀]
  exact hmono

/-- Paper 22:1988–1996 (H3 at c = z, or H2′ plus H4 at c < z). At the action read of
round r+1, the stable output of every honest node extends Q.
DC: INTENTIONAL: the post-tick store of the action read. -/
theorem ktail_action_S_cover {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) (ow : TailOpeningWitness_W p c E rho ΔF pt)
    {k : Nat} {x : V} (hx : x ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick x (p.actionTime (pt.r + 1)))) :
    Block.Preceq (eraseFG ow.Q) (S_at p c E rho (k + 1) x) := by
  have hs := hT.set.base.valid.toScheduleWellFormed
  obtain ⟨hκ2, -⟩ := (ktail_bounds hT).2
  have hc2 : (pt.carrier : Nat) ≤ (pt.r + 1) * p.R := hT.carrier.2.1
  obtain ⟨-, hsuf1, -⟩ := ktail_action_suffix hT hk
  rcases Nat.lt_or_ge (pt.carrier : Nat) ((pt.r + 1) * p.R) with hlt | hge
  · have hlt' : SA.gateTime p.toParams pt.carrier < p.actionTime (pt.r + 1) := by
      rw [kmid_actionTime_eq]
      have := kmid_slot_scale_lt p hlt
      change 4 * p.Δ * (pt.carrier : Time) + 6 * p.Δ < _
      linarith
    exact ktail_S_cover_after hT ow hx
      ((ktail_afterTicksIdx_le p c E rho hs hk hlt').trans (Nat.le_succ k)) hsuf1
  · have hhorG : SA.gateTime p.toParams pt.carrier ≤ rho.horizon :=
      (ktail_slot_horizon hT (s := pt.carrier) (le_trans hc2 (Nat.le_add_right _ _))).2.2
        (Nat.add_le_add hc2 hκ2)
    have hstable := ((ow.serviceQ.2 hhorG x hx
      (ktail_window_confirmed hT (by have hc := hT.carrier.1; omega) hhorG hx)).2.2.2).1
    have heq : (pt.carrier : Nat) = (pt.r + 1) * p.R := le_antisymm hc2 hge
    have hk' : rho.events[k]? = some (.tick x (SA.gateTime p.toParams pt.carrier)) := by
      rw [heq]
      exact hk
    rw [afterTicks_node E rho hs hk', ← (V2.D.Run.step_tick_eq E rho hk').1] at hstable
    have hS : S_at p c E rho (k + 1) x = eraseFG ow.Q := hstable
    rw [hS]
    exact Gen.Pure.block_preceq_refl _

/-! ### The K-ROWS premises for D = Q at the action of round r+1 -/

/-- Paper 22:1690–1700, 1988–1996; plan §2 "hD", "hframe", "hcompat". At every honest
action read of round r+1, Q is held, passes the four frame guards, is in the full
filtered tree, is compatible with the live start, and caps the held heights. The read is
the store after the action tick. T-START, H3 and H4 make every live start compatible with Q.
DC: INTENTIONAL: the FG-SA frame filter and T-START; no future gate is assumed. -/
theorem ktail_action_frame {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) (ow : TailOpeningWitness_W p c E rho ΔF pt)
    {x : V} (hx : x ∈ rho.honest) (nd : Node p)
    (hnd : postClock E rho x (p.actionTime (pt.r + 1)) = some nd) :
    ∃ k, rho.events[k]? = some (.tick x (p.actionTime (pt.r + 1))) ∧
      storeAt p c E rho (k + 1) x = nd.st ∧
      ow.Q ∈ nd.st.fg.TF ∧ FGBlock.Preceq (FGSA.controls p nd.st).F ow.Q ∧
      FGBlock.Preceq (FGSA.controls p nd.st).Z ow.Q ∧
      (FGSA.controls p nd.st).lo ≤ (heightView p ow.Q).h ∧
      ow.Q ∈ FGSA.fullTree p nd.st ∧
      Block.Compatible (FGSA.liveRoot p nd.st) (eraseFG ow.Q) ∧
      (∀ B ∈ nd.st.fg.TF, (heightView p B).h ≤ ow.e + 1) := by
  have hs := hT.set.base.valid.toScheduleWellFormed
  obtain ⟨k, hk, -, hread⟩ := ktail_action_store p c E rho x _ nd hnd
  obtain ⟨-, hsuf1, hcut1⟩ := ktail_action_suffix hT hk
  have hS := ktail_action_S_cover hT ow hx hk
  have hF := ktail_F_below_witness hT ow (k + 1) x hx hsuf1 hcut1 hS
  have hcap : ∀ B ∈ (storeAt p c E rho (k + 1) x).fg.TF, (heightView p B).h ≤ ow.e + 1 :=
    fun B hB => ow.capThroughAction (k + 1) x B hcut1 ⟨hx, hB⟩
  have hc2 : (pt.carrier : Nat) ≤ (pt.r + 1) * p.R := hT.carrier.2.1
  have hvote := ktail_afterTicksIdx_le p c E rho hs hk (kmid_vote_lt_action p hc2)
  have hQ : ow.Q ∈ (storeAt p c E rho (k + 1) x).fg.TF :=
    ow.heldQFrom x hx (k + 1) _ le_rfl (hvote.trans (Nat.le_succ k))
  have hI := (cstoreInv_stateBefore E rho (k + 1) x).fg
  obtain ⟨-, hFc, hZ, hlo, hfull⟩ := ktail_frame_of_store p (storeAt p c E rho (k + 1) x) hI
    ow.Q hQ (fun B hB => by rw [ow.heightQ]; exact hcap B hB) hF
  have hcompat : Block.Compatible (FGSA.liveRoot p (storeAt p c E rho (k + 1) x))
      (eraseFG ow.Q) := by
    rcases (fgsa_tStart (p := p) (c := c) E rho).2 (k + 1) x hx with
      h | ⟨row, -, -, hrow, -, hout⟩
    · rw [h]
      exact Gen.Pure.block_compatible_of_common (eraseFG_preceq hZ) (Gen.Pure.block_preceq_refl _)
    · rw [← hrow]
      exact Gen.Pure.block_compatible_of_common hout hS
  rw [← hread]
  exact ⟨k, hk, rfl, hQ, hFc, hZ, hlo, hfull, hcompat, hcap⟩

/-- Paper 22:1702–1706 (Q0 criterion), plan §2 "hFgate". When the witness is before
the next opening, every honest gate read of slot (r+1)R has finality below Q. The gate
read is the pre-tick store; H4 and the strict row cap give the bound.
DC: INTENTIONAL: certificate height and block height stay distinct. -/
theorem ktail_gate_finality {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) (ow : TailOpeningWitness_W p c E rho ΔF pt)
    (hlt : (pt.carrier : Nat) < (pt.r + 1) * p.R) :
    ∀ x st, x ∈ rho.honest → gateIn p c E rho x ((pt.r + 1) * p.R) = some st →
      Block.Preceq (eraseFG st.fg.F) (eraseFG ow.Q) := by
  intro x st hx hst
  have hs := hT.set.base.valid.toScheduleWellFormed
  rw [gateIn_def, preTick_def] at hst
  cases hj : V2.D.Run.tickIdx? rho x (SA.gateTime p.toParams ((pt.r + 1) * p.R)) with
  | none => rw [hj] at hst; cases hst
  | some k =>
    rw [hj] at hst
    have hk : rho.events[k]? = some (.tick x (p.actionTime (pt.r + 1))) :=
      V2.D.Run.tickIdx?_spec hj
    have hst' : FGSA.clockPre p (V2.D.Run.stateBefore E rho k x).st
        (SA.gateTime p.toParams ((pt.r + 1) * p.R)) = st := Option.some.inj hst
    obtain ⟨hsufk, -, hcut1⟩ := ktail_action_suffix hT hk
    have hlt' : SA.gateTime p.toParams pt.carrier < p.actionTime (pt.r + 1) := by
      rw [kmid_actionTime_eq]
      have := kmid_slot_scale_lt p hlt
      change 4 * p.Δ * (pt.carrier : Time) + 6 * p.Δ < _
      linarith
    have hS := ktail_S_cover_after hT ow hx (ktail_afterTicksIdx_le p c E rho hs hk hlt') hsufk
    have hF := ktail_F_below_witness hT ow k x hx hsufk ((Nat.le_succ k).trans hcut1) hS
    rw [← hst', clockPre_fg]
    exact eraseFG_preceq hF

/-- Paper 22:1988–1996 (FT-Tail-W: "at the next opening z, H3 if c = z, or H2′ and
Q0 if c < z, give sources at fresh height e+1"), plan §1 step 4. Every honest action
source of round r+1 covers Q, has height e+1 and Q's entry.
DC: INTENTIONAL: deepest fresh FG-SA selector; height plateau fixes the same entry. -/
theorem ktail_action_source {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) (ow : TailOpeningWitness_W p c E rho ΔF pt) :
    ∀ x ∈ rho.honest, ∃ nd C, postClock E rho x (p.actionTime (pt.r + 1)) = some nd ∧
      FGSA.fgSource p nd.st = some C ∧ FGBlock.Preceq ow.Q C ∧
      (heightView p C).h = ow.e + 1 ∧ (heightView p C).T_h = (heightView p ow.Q).T_h := by
  intro x hx
  have hs := hT.set.base.valid.toScheduleWellFormed
  obtain ⟨_hF0, hκ2, _hκR, _hR2, hs2, _hGST, _hhorT⟩ := ktail_bounds hT
  have hc1 : pt.r * p.R + kappaF p ΔF ≤ (pt.carrier : Nat) := hT.carrier.1
  have hc2 : (pt.carrier : Nat) ≤ (pt.r + 1) * p.R := hT.carrier.2.1
  rcases Nat.lt_or_ge (pt.carrier : Nat) ((pt.r + 1) * p.R) with hlt | hge
  · have hZT : (pt.r + 1) * p.R ≤ (pt.r + 1) * p.R + kappaF p ΔF := Nat.le_add_right _ _
    have hhorZ := ktail_slot_horizon hT hZT
    have hGST : E.t_GST ≤ SA.voteTime p.toParams ((pt.r + 1) * p.R) := by
      have h1 := ktail_slot_gst hT (s := (pt.r + 1) * p.R) (by
        rw [Nat.succ_mul]; exact Nat.le_add_right _ _)
      have := p.deltaPos
      change E.t_GST ≤ 4 * p.Δ * (((pt.r + 1) * p.R : Nat) : Time) at h1
      change E.t_GST ≤ 4 * p.Δ * (((pt.r + 1) * p.R : Nat) : Time) + p.Δ
      linarith
    have hheads : ∀ y ∈ rho.honest, ∃ H,
        headAtLabel p c E rho y ((pt.r + 1) * p.R) = some H := by
      intro y hy
      have hmul : SA.voteTime p.toParams ((pt.r + 1) * p.R) =
          ((4 * ((pt.r + 1) * p.R) + 1 : Nat) : Time) * p.Δ := by
        change 4 * p.Δ * (((pt.r + 1) * p.R : Nat) : Time) + p.Δ = _
        push_cast
        ring
      obtain ⟨i, hi, -⟩ := fgsa_tick_total E rho hs hT.set.base.delta y hy
        (4 * ((pt.r + 1) * p.R) + 1) (hmul ▸ hhorZ.2.1)
        (hmul ▸ hT.set.awake y hy _ hGST hhorZ.2.1)
      rw [← hmul] at hi
      have ht := fgsa_tickIdx_of_event p c E rho hs hi
      refine ⟨FGSA.headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i y)
        (SA.voteTime p.toParams ((pt.r + 1) * p.R))).st ((pt.r + 1) * p.R), ?_⟩
      change (postClock E rho y (SA.voteTime p.toParams ((pt.r + 1) * p.R))).map
        (fun nd => FGSA.headVote p nd.st ((pt.r + 1) * p.R)) = _
      rw [postClock_def, preTick_def, ht]
      rfl
    have hne : eraseFG ow.Q ≠ .genesis := by
      intro hg
      have hQg : ow.Q = .genesis := eraseFG_eq_genesis.mp hg
      have hsl := ow.slotQ
      rw [hQg] at hsl
      have h0 : (0 : Nat) = pt.carrier := hsl
      omega
    exact finality_action_source p c E rho pt.w (pt.r + 1) ow.e pt.carrier ow.Q x hx
      hc2 (hs2.trans (le_trans (Nat.le_add_right _ _) hc1)) ow.honestQ
      hT.input.ac.h2' hT.input.ac.h3 hT.input.ac.h6
      (by
        apply finality_recoveryStart_le_vote p E ((pt.r + 1) * p.R) (by
          have hR2 := (ktail_bounds hT).2.2.2.1
          have hle : p.R ≤ (pt.r + 1) * p.R := by rw [Nat.add_mul]; omega
          exact hR2.trans hle)
        have hsync := hT.input.wit.synchronous
        have hstart := hT.start
        rw [kmid_period_eq] at hstart
        have hlow : (pt.w.sStar : Int) + 2 ≤ (pt.w.u : Int) := by
          exact_mod_cast hT.input.wit.proposal_lower
        have hR : 2 ≤ p.R := (ktail_bounds hT).2.2.2.1
        have hle := kmid_slot_scale_le p (show pt.r * p.R + 2 ≤ (pt.r + 1) * p.R by
          rw [Nat.succ_mul]; omega)
        change E.t_GST ≤ 4 * p.Δ * (pt.w.sStar : Int) + p.Δ at hsync
        change 4 * p.Δ * (pt.w.u : Int) + 6 * p.Δ ≤ _ at hstart
        change E.t_GST ≤ 4 * p.Δ * (_ - 2)
        push_cast at hle hstart ⊢
        nlinarith [p.deltaPos]) ow.actionInRun hne hheads
      (fun y hy => ktail_window_joined hT (by rw [Nat.succ_mul]; omega) hZT hy)
      (ktail_window_confirmed hT (by omega) (by
        have hle := kmid_slot_scale_le p hc2
        have hh := ow.actionInRun
        rw [kmid_actionTime_eq] at hh
        change 4 * p.Δ * (pt.carrier : Int) + 6 * p.Δ ≤ rho.horizon
        linarith) hx)
      (ktail_gate_finality hT ow hlt)
      (fun nd hnd => by
        obtain ⟨-, -, -, hQ, hFc, hZ, hlo, -, -, -⟩ := ktail_action_frame hT ow hx nd hnd
        exact ⟨hQ, hFc, hZ, hlo⟩)
      ow.heightQ
      (fun nd hnd => by
        obtain ⟨-, -, -, -, -, -, -, -, -, hcap⟩ := ktail_action_frame hT ow hx nd hnd
        exact hcap)
  · have heq : (pt.carrier : Nat) = (pt.r + 1) * p.R := le_antisymm hc2 hge
    have hsrc := ow.sourceQAtOpening heq x hx
    rw [actionSourceFG_def] at hsrc
    obtain ⟨nd, hnd, hsource⟩ := Option.map_eq_some_iff.mp hsrc
    exact ⟨nd, ow.Q, hnd, hsource, KitFG.preceq_refl _, ow.heightQ, rfl⟩

end AvailableChain.FGSA.Run
end
