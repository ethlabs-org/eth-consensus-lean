module
public import AvailableChainFGSAProofs.Proofs.Healing.FrameRelay
public import AvailableChainFGSAProofs.Proofs.Healing.FrameZero
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseRelay
public import AvailableChainFGSAProofs.Proofs.Shared.HeldReceipt
public import AvailableChainFGSAProofs.Proofs.Healing.SupportRecovery

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Blueprint 21:749–783, 1153–1162; plan H-SUPPORT S0 (H-FRAME review F1); ruling B25.
DC: INTENTIONAL the settled frame is read at the strict PhaseInterval cut idxBefore u.
A HEAD tick at u = v_s reads a state inside this cut. No GST premise is used. -/
theorem healing_settled_frame_strict (crossing : RXing p c E rho)
    (u v : Time) (m : Nat) (J : Option (FGBlock (Fin p.n))) (contested : Bool)
    (hp : PhaseInterval p c E rho u v m J contested)
    (i : Nat) (x : V) (hui : V2.D.Run.idxBefore rho u ≤ i) (hiv : i ≤ timeIdx rho v)
    (hx : x ∈ rho.honest) :
    SettledPhaseFrame p (storeAt p c E rho i x) m J contested := by
  obtain ⟨hH, hc, hr⟩ := hp.2.2.2 i x hui hiv hx
  exact healing_phase_frame p c E rho crossing hx hp.2.2.1 hH hc hr

omit [DecidableEq V] in
/-- Blueprint 21:749–783, 1153–1162; plan H-SUPPORT S0; ruling B25.
DC: SAME an event at or after u is not before the strict cut at u. -/
theorem healing_support_idxBefore_le (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {e : V2.Event V (Obj p)} (hi : rho.events[i]? = some e) {u : Time}
    (hu : u ≤ e.time) : V2.D.Run.idxBefore rho u ≤ i := by
  by_contra hn
  have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hs hi u).mp (Nat.lt_of_not_ge hn)
  exact (not_lt.mpr hu) hlt

/-- ROOT-DIGEST W2b. Blueprint 21:749–783, 1148–1252; plan H-SUPPORT S0 (H-FRAME review F1); B25,
B26.
DC: INTENTIONAL the source frame comes from the phase at the strict cut, so the
hsrc premise of healing_witness_relay_phase is derived. The HEAD may be at u = v_s.
The finite horizon follows from the phase end. -/
theorem healing_witness_relay_settled (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (u v : Time) (m : Nat) (J : Option (FGBlock (Fin p.n))) (contested : Bool)
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hhead : u ≤ SA.voteTime p.toParams s)
    (hreceipt : SA.voteTime p.toParams s + p.Δ ≤ v)
    (W : FGBlock (Fin p.n)) (hW : W ∈ (storeAt p c E rho i x).fg.TF)
    (hZW : FGBlock.Preceq (R_at p c E rho i x).Z W)
    (hlo : (R_at p c E rho i x).lo ≤ (heightView p W).h)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams s + p.Δ) = true →
          Gen.V2.Duty.HoldsBefore E rho
      (fun nd => ∀ B, FGBlock.Preceq B W → B ∈ nd.st.fg.TF)
      (SA.voteTime p.toParams s + p.Δ) y := by
  have hs := hvalid.toScheduleWellFormed
  have hui := healing_support_idxBefore_le p c E rho hs hi hhead
  have hiv : i ≤ timeIdx rho v := (healing_phase_lt_timeIdx p c E rho hs hi
    ((le_add_of_nonneg_right p.deltaPos.le).trans hreceipt)).le
  exact healing_witness_relay_phase (hroots := hroots)
    p c E rho mono crossing hvalid hnr hdelta hsync
    u v m J contested hgst hphase hx hi hhead hreceipt (hreceipt.trans hphase.2.1) W hW
    (healing_settled_frame_strict p c E rho crossing u v m J contested hphase i x hui hiv hx)
    hZW hlo

/-- ROOT-DIGEST W2b. Blueprint 21:749–783, 1148–1252; plan H-SUPPORT S0 and §4 step 3 (F1 + F2).
DC: INTENTIONAL the HEAD of an honest node in the phase has a full-domain witness K
and a height witness W above K; all ancestors of W reach every honest store
strictly before v_s + Δ. The HEAD itself need not be in its frozen domain. -/
theorem healing_head_witness_relay (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (u v : Time) (m : Nat) (J : Option (FGBlock (Fin p.n))) (contested : Bool)
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hhead : u ≤ SA.voteTime p.toParams s)
    (hreceipt : SA.voteTime p.toParams s + p.Δ ≤ v)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let st := ((fgsa p c).clock (rho.stateBefore E i x) (SA.voteTime p.toParams s)).st
    ∃ K ∈ fullTree p st, eraseFG K = headVote p st s ∧
      ∃ W ∈ st.fg.TF, FGBlock.Preceq K W ∧ (controls p st).lo ≤ (heightView p W).h ∧
        ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams s + p.Δ) = true →
          Gen.V2.Duty.HoldsBefore E rho
          (fun nd => ∀ B, FGBlock.Preceq B W → B ∈ nd.st.fg.TF)
          (SA.voteTime p.toParams s + p.Δ) y := by
  intro st
  have hs := hvalid.toScheduleWellFormed
  obtain ⟨K, hK, hk, W, hW, hKW, hlo⟩ :=
    healing_full_witness_all p c E rho hs crossing hx hi
  have hfg : st.fg = (storeAt p c E rho i x).fg := clock_fg p _ _
  have hZK : FGBlock.Preceq (controls p st).Z K :=
    ((KitFG.mem_filteredFromView _ _ _ _).mp hK).2.2.1
  have hR : controls p st = R_at p c E rho i x := by
    change KitFG.treeStoreControlsView (heightView p) st.fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho i x).fg
    rw [hfg]
  refine ⟨K, hK, hk, W, hW, hKW, hlo, ?_⟩
  apply healing_witness_relay_settled (hroots := hroots)
    p c E rho mono crossing hvalid hnr hdelta hsync
    u v m J contested hgst hphase hx hi hhead hreceipt W (hfg ▸ hW)
  · exact hR ▸ KitFG.preceq_trans hZK hKW
  · exact hR ▸ hlo

/-- A selected witness is admissible at this receiver before service is requested. -/
structure HeadCarrierDemand {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (i : Nat) (x : V) (s : Slot)
    (y : V) : Prop where
  witness :
    let st := clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)
    ∃ K ∈ fullTree p st, eraseFG K = headVote p st s ∧
      ∃ W ∈ st.fg.TF, FGBlock.Preceq K W ∧ (controls p st).lo ≤ (heightView p W).h ∧
        Block.Compatible (eraseFG W)
          (eraseFG (rho.stateBeforeTime E (SA.voteTime p.toParams s + p.Δ) y).st.fg.F)

/-- Phase geometry constructs an admissible witness without assuming receipt. -/
theorem healing_head_carrier_demand_phase (crossing : RXing p c E rho)
    (hE : V2.D.ExecutionValid E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hphase : PhaseInterval p c E rho u v m J contested)
    {i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hu : u ≤ SA.voteTime p.toParams s) (hv : SA.voteTime p.toParams s + p.Δ ≤ v)
    {y : V} (hy : y ∈ rho.honest) : HeadCarrierDemand E rho i x s y := by
  have hS := hE.toScheduleWellFormed
  let d := V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + p.Δ)
  have hid : i ≤ d := ((Gen.V2.Duty.index_lt_idxBefore_iff hS hi _).mpr
    (lt_add_of_pos_right _ p.deltaPos)).le
  have hdu : V2.D.Run.idxBefore rho u ≤ d := fgsa_idxBefore_mono rho
    (hu.trans (le_add_of_nonneg_right p.deltaPos.le))
  have hdv : d ≤ timeIdx rho v := healing_phase_idx_le_time p c rho hv
  obtain ⟨K, hK, he, W, hW, hKW, hlo⟩ :=
    healing_full_witness_all p c E rho hS crossing hx hi
  have hf := healing_settled_frame_strict p c E rho crossing u v m J contested hphase
    i x (healing_support_idxBefore_le p c E rho hS hi hu) (hid.trans hdv) hx
  have hfY := healing_settled_frame_strict p c E rho crossing u v m J contested hphase
    d y hdu hdv hy
  have hW0 : W ∈ (storeAt p c E rho i x).fg.TF := by
    have hw := hW
    change W ∈ (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)).fg.TF at hw
    rwa [clock_fg] at hw
  have hR : controls p (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)) =
      R_at p c E rho i x := by
    change KitFG.treeStoreControlsView (heightView p) (clock p _ _).fg = _
    rw [clock_fg]; rfl
  have hZW : FGBlock.Preceq (R_at p c E rho i x).Z W := by
    rw [← hR]
    exact KitFG.preceq_trans ((KitFG.mem_filteredFromView _ _ _ _).mp hK).2.2.1 hKW
  have hFW : FGBlock.Preceq (storeAt p c E rho d y).fg.F W := by
    cases J with
    | some J0 =>
      obtain ⟨_, _, hZ, _, _, _⟩ := hf.2.2.2.1
      obtain ⟨_, _, _, _, _, hFJ⟩ := hfY.2.2.2.1
      exact KitFG.preceq_trans hFJ (hZ ▸ hZW)
    | none =>
      obtain ⟨_, _, ⟨Kc, hKc, hKcF, hLow⟩, _⟩ := hfY.2.2.2.1
      have hLo : (R_at p c E rho d y).lo ≤ (heightView p W).h := by
        change (controls p (storeAt p c E rho d y)).lo ≤ (heightView p W).h
        rw [hfY.2.2.1, ← hf.2.2.1]
        change (R_at p c E rho i x).lo ≤ (heightView p W).h
        rw [← hR]
        exact hlo
      exact crossing d d y x Kc W hy le_rfl hKc hKcF
        ⟨hx, (fgsa_store_durable p c E rho hid x).1 hW0⟩ (hLow.trans_le hLo)
  constructor
  refine ⟨K, hK, he, W, hW, hKW, hlo, ?_⟩
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
  exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl (eraseFG W))
    (eraseFG_preceq hFW)

/-- One selected HEAD witness, with its source frame and this receiver's floor.
Old durable blocks outside this witness create no receipt obligation. -/
structure HeadCarrierScope {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (i : Nat) (x : V) (s : Slot)
    (y : V) : Prop where
  carrier :
    let st := clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)
    ∃ K ∈ fullTree p st, eraseFG K = headVote p st s ∧
      ∃ W ∈ st.fg.TF, FGBlock.Preceq K W ∧ (controls p st).lo ≤ (heightView p W).h ∧
        Block.Compatible (eraseFG W)
          (eraseFG (rho.stateBeforeTime E (SA.voteTime p.toParams s + p.Δ) y).st.fg.F) ∧
        TargetReceiptService E rho (eraseFG W) (SA.voteTime p.toParams s + p.Δ) y

/-- Only the selected admissible witness or actual HEAD target is served. -/
structure HeadCarrierServices {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (i : Nat) (x : V) (s : Slot)
    (y : V) : Prop where
  relay : HeadCarrierDemand E rho i x s y → HeadCarrierScope E rho i x s y
  direct : ∀ K ∈ (storeAt p c E rho i x).fg.TF,
    eraseFG K = headVote p (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)) s →
    Block.Preceq (eraseFG (rho.stateBeforeTime E (SA.voteTime p.toParams s + p.Δ) y).st.fg.F)
      (eraseFG K) → TargetReceiptService E rho (eraseFG K) (SA.voteTime p.toParams s + p.Δ) y

/-- The carrier reader is an honest actor at its actual joined tick. -/
@[expose] def HealingJoinedTick {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) (t : Time) : Prop :=
  x ∈ rho.honest ∧ rho.events[i]? = some (.tick x t) ∧
    joinedAt p E rho x (slotAt p t) t

/-- Carrier transport serves one joined reader, with its bounded deadline. -/
@[expose] def HealingCarriersAt {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) (iy : Nat) (y : V) (t : Time) : Prop :=
  E.t_GST ≤ SA.voteTime p.toParams s → HealingJoinedTick E rho iy y t →
  SA.voteTime p.toParams s + p.Δ ≤ t → t ≤ rho.horizon →
  ∀ j z, z ∈ rho.honest →
    rho.events[j]? = some (.tick z (SA.voteTime p.toParams s)) →
    joinedAt p E rho z s (SA.voteTime p.toParams s) →
    HeadCarrierServices E rho j z s y

/-- The stored join test at an actual tick supplies the environmental read guard. -/
theorem healing_joined_tick_of_guard (hV : V2.D.ExecutionValid E rho)
    {i : Nat} {x : V} {t : Time} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x t))
    (hguard : joinedAtTime p (storeAt p c E rho i x).restartTime t = true) :
    HealingJoinedTick E rho i x t := by
  have bound (w : Time) (_hw : 0 ≤ w) (hwt : w ≤ t)
      (hr : V2.Event.restart x w ∈ rho.events) :
      w ≤ slotStartZ p ((slotAt p t : Int) - 1) := by
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
    have hji := V2.D.Engine.restart_index_lt_event hV.toScheduleWellFormed hj hi hwt
      (by change 0 < (1 : Nat); decide)
    obtain ⟨u, hu, hwu⟩ := fgsa_restartTime_ge E rho hV.toScheduleWellFormed hj hji
    have hg := hguard
    change joinedAtTime p (rho.stateBefore E i x).st.restartTime t = true at hg
    unfold joinedAtTime at hg
    rw [hu] at hg
    exact hwu.trans (of_decide_eq_true hg)
  refine ⟨hx, hi, hV.tick_awake x t (List.mem_of_getElem? hi), ?_, bound⟩
  intro w hw hwt hwake
  exact bound w hw.le hwt (hV.wake_restart x hx w hw
    (hwt.trans (hV.in_horizon _ (List.mem_of_getElem? hi)).2) hwake)

/-- The batch window supplies a joined reader at each later actual tick. -/
theorem healing_joined_tick_of_window [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot} (hCut : HealingWindow p E 1 s)
    {i : Nat} {x : V} {t : Time} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x t)) (ht : SA.voteTime p.toParams s ≤ t) :
    HealingJoinedTick E rho i x t := by
  have hh := (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hi)).2
  have hs : slotAt p (SA.voteTime p.toParams s) = s := by
    exact (fgsa_postClock_slot (c := c) (rho.stateBefore E i x) _).2.symm.trans
      (fgsa_vote_slot (c := c) _ s)
  have hst : s ≤ slotAt p t := by
    rw [← hs]
    exact Internal.slotOf_mono (p := p) ht
  refine ⟨hx, hi, healing_recovery_joined E rho hrec hx ?_ (hCut.sync.trans ht) hh⟩
  exact (hCut.cut_mono hst).2

/-- A real bounded tick after recoveryStart gives the carrier reader's join. -/
theorem healing_joined_tick_of_ready [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {i : Nat} {x : V} {t : Time}
    (hx : x ∈ rho.honest) (hi : rho.events[i]? = some (.tick x t))
    (hready : recoveryStart p E ≤ t) (hhor : t ≤ rho.horizon) :
    HealingJoinedTick E rho i x t :=
  ⟨hx, hi, healing_joined_at_or_after_start E rho hrec hx hready hhor⟩

/-- Use the guarded carrier at its fixed actual reader in a batch window. -/
theorem healing_carriers_window_at [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot} (hCut : HealingWindow p E 1 s)
    {iy : Nat} {y : V} {t : Time} (h : HealingCarriersAt E rho s iy y t)
    (hy : y ∈ rho.honest) (hi : rho.events[iy]? = some (.tick y t))
    (ht : SA.voteTime p.toParams s + p.Δ ≤ t) :
    ∀ j z, z ∈ rho.honest →
      rho.events[j]? = some (.tick z (SA.voteTime p.toParams s)) →
      HeadCarrierServices E rho j z s y := by
  have hvt := (le_add_of_nonneg_right p.deltaPos.le).trans ht
  have hh := (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hi)).2
  intro j z hz hj
  exact h hCut.sync (healing_joined_tick_of_window p c E rho hrec hCut hy hi hvt)
    ht hh j z hz hj (healing_recovery_joined_window E rho hrec hCut hz (hvt.trans hh))

/-- The integer cutoff supplies joined readers without asserting a predecessor label. -/
theorem healing_carriers_cut_at [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot}
    (hCut : E.t_GST ≤ slotStartZ p ((s : Int) - 1))
    {iy : Nat} {y : V} {t : Time} (h : HealingCarriersAt E rho s iy y t)
    (hy : y ∈ rho.honest) (hi : rho.events[iy]? = some (.tick y t))
    (ht : SA.voteTime p.toParams s + p.Δ ≤ t) :
    ∀ j z, z ∈ rho.honest →
      rho.events[j]? = some (.tick z (SA.voteTime p.toParams s)) →
      HeadCarrierServices E rho j z s y := by
  have hh := (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hi)).2
  have hs : slotAt p (SA.voteTime p.toParams s) = s := by
    exact (fgsa_postClock_slot (c := c) (rho.stateBefore E iy y) _).2.symm.trans
      (fgsa_vote_slot (c := c) _ s)
  have hvt := (le_add_of_nonneg_right p.deltaPos.le).trans ht
  have hst : s ≤ slotAt p t := by
    rw [← hs]
    exact Internal.slotOf_mono (p := p) hvt
  have hSync : E.t_GST ≤ SA.voteTime p.toParams s := by
    refine hCut.trans ?_
    change 4 * p.Δ * ((s : Int) - 1) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hRead : HealingJoinedTick E rho iy y t := by
    refine ⟨hy, hi, healing_recovery_joined E rho hrec hy ?_ (hSync.trans hvt) hh⟩
    refine hCut.trans ?_
    have hstI : (s : Int) ≤ (slotAt p t : Int) := by exact_mod_cast hst
    unfold slotStartZ
    nlinarith [p.deltaPos]
  intro j z hz hj
  exact h hSync hRead ht hh j z hz hj
    (healing_recovery_joined E rho hrec hz hCut hSync (hvt.trans hh))

/-- The selected ancestor, rather than every cached block, reaches the receiver. -/
theorem healing_head_carrier_receipt (hvalid : V2.D.ExecutionValid E rho)
    {i : Nat} {x y : V} {s : Slot} (hy : y ∈ rho.honest)
    (hServices : HeadCarrierScope E rho i x s y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    headVote p (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)) s ∈
      (rho.stateBeforeTime E (SA.voteTime p.toParams s + p.Δ) y).st.base.blocks := by
  obtain ⟨K, _, he, W, _, hKW, _, _, hs⟩ := hServices.carrier
  have hW := healing_held_block_receipt_on p c E rho hvalid hroots W
    (SA.voteTime p.toParams s + p.Δ) y hy hs
  have hK := KitFG.ancestor_closed_of_parent_closed _
    (storeBundle_stateBeforeTime E rho (SA.voteTime p.toParams s + p.Δ) y).cstore.fg.closed
    W hW K hKW
  rw [← he]
  exact ((storeBundle_stateBeforeTime E rho _ y).cstore.baseTree _).mpr ⟨K, hK, rfl⟩

/-- The selected carrier supplies its ancestors at this receiver's deadline. -/
theorem healing_head_witness_relay_on (_crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho)
    {i : Nat} {x : V} {s : Slot} (_hx : x ∈ rho.honest)
    (_hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    {y : V} (hy : y ∈ rho.honest) (hServices : HeadCarrierScope E rho i x s y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let st := ((fgsa p c).clock (rho.stateBefore E i x) (SA.voteTime p.toParams s)).st
    ∃ K ∈ fullTree p st, eraseFG K = headVote p st s ∧
      ∃ W ∈ st.fg.TF, FGBlock.Preceq K W ∧ (controls p st).lo ≤ (heightView p W).h ∧
        Gen.V2.Duty.HoldsBefore E rho
          (fun nd => ∀ B, FGBlock.Preceq B W → B ∈ nd.st.fg.TF)
          (SA.voteTime p.toParams s + p.Δ) y := by
  intro st
  obtain ⟨K, hK, hk, W, hW, hKW, hlo, _, hs⟩ := hServices.carrier
  refine ⟨K, hK, hk, W, hW, hKW, hlo, ?_⟩
  have hheld := healing_held_block_receipt_on p c E rho hvalid hroots W
    (SA.voteTime p.toParams s + p.Δ) y hy hs
  change W ∈ (rho.stateBeforeTime E (SA.voteTime p.toParams s + p.Δ) y).st.fg.TF at hheld
  intro B hBW
  exact KitFG.ancestor_closed_of_parent_closed _
    (storeBundle_stateBeforeTime E rho (SA.voteTime p.toParams s + p.Δ) y).cstore.fg.closed
    W hheld B hBW

end AvailableChain.FGSA.Run
end
