module
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseOrder
public import AvailableChainFGSAProofs.Proofs.Shared.CatchUp
public import AvailableChainFGSAProofs.Proofs.Healing.Base

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1142–1171; plan S20, H-PHASE/P2. DC: SAME decoded block identity. -/
private theorem phase_block_decode {o : Obj p} {b : Block} (h : blockOf? p o = some b) :
    ∃ s N, (toWire p o).decode = some (.block s N) ∧ N.erase = b := by
  dsimp only [blockOf?] at h
  cases hd : (toWire p o).decode with
  | none => simp only [hd, reduceCtorEq] at h
  | some msg =>
    cases msg <;> simp only [hd, reduceCtorEq, Option.some.injEq] at h
    subst b
    exact ⟨_, _, rfl, rfl⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:1142–1171; plan S20, H-PHASE/P2.
DC: INTENTIONAL a processed FG wire identifies the same cumulative block. -/
private theorem phase_processed_mem (hnr : V2.D.NoRestart rho) {k j : Nat} {x : V} {o : Obj p}
    {B : FGBlock (Fin p.n)} (hb : blockOf? p o = some (eraseFG B))
    (hp : (fgsa p c).processed (V2.D.Run.stateBefore E rho j x) o = true)
    (hjk : j ≤ k) (hB : B ∈ (storeAt p c E rho k x).fg.TF) :
    B ∈ (storeAt p c E rho j x).fg.TF := by
  obtain ⟨s, N, hd, heN⟩ := phase_block_decode p hb
  change processedS p (storeAt p c E rho j x) o = true at hp
  dsimp only [processedS] at hp
  rw [hd] at hp
  obtain ⟨Y, hY, he⟩ := of_decide_eq_true hp
  have heq : Y = B := (cstoreInv_stateBefore E rho k x).rootInj Y
    ((fgsa_store_cumulative p c E rho hnr hjk x).1 hY) B hB
    (by rw [← named_erase_root, heN] at he; exact he.trans (eraseFG_root B))
  exact heq ▸ hY

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:1142–1171; plan S20, H-PHASE/P2.
DC: INTENTIONAL new cumulative membership supplies the exact acceptance event. -/
private theorem phase_new_accept (hnr : V2.D.NoRestart rho)
    {i : Nat} {ev : V2.Event V (Obj p)} {x : V} {W : FGBlock (Fin p.n)}
    (hi : rho.events[i]? = some ev)
    (hbefore : W ∉ (storeAt p c E rho i x).fg.TF)
    (hafter : W ∈ (storeAt p c E rho (i + 1) x).fg.TF) :
    ∃ o, blockOf? p o = some (eraseFG W) ∧ V2.D.Run.acceptsAt E rho i x o ev.time := by
  have hgen : W ≠ .genesis := fun he =>
    hbefore (he ▸ (storeBundle_stateBefore E rho i x).cstore.fg.gen)
  have hbase := (storeBundle_stateBefore E rho (i + 1) x).cstore.baseTree (eraseFG W)
  have hm := hbase.mpr ⟨W, hafter, rfl⟩
  rw [← (metaInv_stateBefore E rho (i + 1) x).stampKeys] at hm
  obtain ⟨⟨b, stamp⟩, hm, he⟩ := List.mem_map.mp hm
  dsimp only at he
  subst b
  rcases fgsa_block_stamp_source E rho hnr (i + 1) x (eraseFG W) stamp hm with
    hg | ⟨j, hj, t, o, hb, ha, _⟩
  · exact (hgen (eraseFG_eq_genesis.mp hg.1)).elim
  · have hji : j = i := by
      by_contra hn
      have hlt : j + 1 ≤ i := by omega
      exact hbefore ((fgsa_store_cumulative p c E rho hnr hlt x).1
        (phase_processed_mem p c E rho hnr hb ha.2.2
          (Nat.succ_le_succ (Nat.le_of_lt_succ hj)) hafter))
    subst j
    obtain ⟨parent, hd, _⟩ := ha.1
    have hevent := Option.some.inj (hi.symm.trans hd)
    have htime : ev.time = t := congrArg V2.Event.time hevent
    exact ⟨o, hb, htime ▸ ha⟩

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1142–1171; plan S20, H-PHASE/P2.
DC: SAME an inclusive time cut contains every strict earlier receipt. -/
theorem healing_phase_idx_le_time {d t : Time} (hdt : d ≤ t) :
    V2.D.Run.idxBefore rho d ≤ timeIdx rho t := by
  change (rho.events.filter (fun e => decide (e.time < d))).length ≤
    (rho.events.filter (fun e => decide (e.time ≤ t))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true ((of_decide_eq_true he).le.trans hdt))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:1142–1171; plan S20, H-PHASE/P2.
DC: INTENTIONAL block relay uses Δ; the frontier-rise alternative ends the task.
Assembly supplies RXing. The accepted W certificate bounds the receiver's F. -/
theorem healing_phase_block_receipt (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {i : Nat} {ev : V2.Event V (Obj p)} {x : V} {W : FGBlock (Fin p.n)} {m : Nat}
    (hi : rho.events[i]? = some ev) (hx : x ∈ rho.honest) (hgst : E.t_GST ≤ ev.time)
    (hbefore : W ∉ (storeAt p c E rho i x).fg.TF)
    (hafter : W ∈ (storeAt p c E rho (i + 1) x).fg.TF)
    (hheight : (heightView p W).h = m) (hhor : ev.time + p.Δ ≤ rho.horizon)
    {y : V} (hy : y ∈ rho.honest)
    (hAwake : E.awake y (ev.time + p.Δ) = true)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let j := V2.D.Run.idxBefore rho (ev.time + p.Δ)
    i < j ∧ j ≤ rho.events.length ∧
      (∀ l e, l < j → rho.events[l]? = some e → e.time < ev.time + p.Δ) ∧
      (W ∈ (storeAt p c E rho j y).fg.TF ∨ m < frontierAtIdx p c E rho j) := by
  let j := V2.D.Run.idxBefore rho (ev.time + p.Δ)
  have hs := hvalid.toScheduleWellFormed
  have hij : i < j := (Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mpr
    (lt_add_of_pos_right _ p.deltaPos)
  refine ⟨hij, List.length_filter_le .., ?_, ?_⟩
  · intro l e hl he
    exact (Gen.V2.Duty.index_lt_idxBefore_iff hs he _).mp hl
  · by_cases hrise : m < frontierAtIdx p c E rho j
    · exact Or.inr hrise
    left
    obtain ⟨o, hb, ha⟩ := phase_new_accept p c E rho hnr hi hbefore hafter
    obtain ⟨s, N, hd, heN⟩ := phase_block_decode p hb
    have ho : o = ofWire p ⟨.proposer s, .proposal N⟩ := by
      apply toWire_injective
      rw [toWire_ofWire]
      exact decode_eq_block.mp hd
    have hWj := (fgsa_store_cumulative p c E rho hnr (Nat.succ_le_of_lt hij) x).1 hafter
    obtain ⟨K, hK, hKF⟩ := (storeBundle_stateBefore E rho j y).cstore.fg.Fcar
    have hfj := (healing_phase_finality_le p c E rho hK hKF).trans_lt
      (healing_phase_justified_lt p c E rho j y)
    have hcap := healing_phase_local_le_frontier p c E rho (i := j) hy
    have hFW := crossing j j y x K W hy le_rfl hK hKF ⟨hx, hWj⟩
      (by simp only [Height] at *; omega)
    have hcompat : Block.Compatible (eraseFG W)
        (eraseFG (V2.D.Run.stateBeforeTime E rho (ev.time + p.Δ) y).st.fg.F) := by
      rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
      exact Bool.or_eq_true_iff.mpr (Or.inr (eraseFG_preceq hFW))
    have delay (o : Obj p) (hn : ¬ isRowObject o) : fgsaDelay E.Δ ΔF o = p.Δ := by
      cases he : o.payload <;> simp only [fgsaDelay_def, he, hdelta]
      exact (hn (by change (match o.payload with | .row _ => True | _ => False)
                    rw [he]; trivial)).elim
    have hD := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hsync
      (fun o => ¬ isRowObject o) p.Δ delay
    have hT : Gen.V2.Duty.Trigger E rho
        (ofWire p ⟨.proposer s, .proposal N⟩) ev.time :=
      Or.inr ⟨x, hx, i, ho ▸ ha⟩
    have hdline : max ev.time E.t_GST + p.Δ = ev.time + p.Δ :=
      congrArg (· + p.Δ) (max_eq_left hgst)
    obtain ⟨Y, hY, he⟩ := fgsa_proposal_receipt (hRoots := hroots) E rho hdelta hvalid hnr
      (fun t => max t E.t_GST + p.Δ) rho.horizon s N ev.time y
      hD hT hy (hdline ▸ hhor) (hdline ▸ (lt_add_of_pos_right _ p.deltaPos))
      (by simpa only [heN, hdline] using hcompat) (hdline ▸ hhor)
      (by
        rw [hdline]
        intro u hu hud
        exact fgsa_awake_before_noRestart E rho hvalid hnr y hy _ hhor hAwake u
          ((hvalid.in_horizon _ (List.mem_of_getElem? hi)).1.trans hu) hud.le)
    have heq : Y = W := eraseFG_injective (he.trans heN)
    rw [hdline, ← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs, heq] at hY
    exact hY

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1155–1163; plan S20, H-PHASE/P2.
DC: INTENTIONAL strict receipt stamps enter the frozen HEAD arm at equality. -/
private theorem phase_frozen_mem_of_crossing (crossing : RXing p c E rho)
    (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) {y : V} {W : FGBlock (Fin p.n)} {d : Time}
    (hdpos : 0 < d) {s : Slot} {nd : Node p}
    (hy : y ∈ rho.honest)
    (hcap : frontierAtIdx p c E rho (timeIdx rho (SA.voteTime p.toParams s)) ≤
      (heightView p W).h)
    (hdt : d ≤ SA.voteTime p.toParams s) (hdf : d ≤ SA.freezeTime p.toParams (s - 1))
    (hW : W ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho d) y).fg.TF)
    (hpost : postClock E rho y (SA.voteTime p.toParams s) = some nd) :
    W ∈ FGSA.voterBlocks p nd.st s := by
  rw [postClock_def, preTick_def] at hpost
  cases hk : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams s) with
  | none => simp only [hk, Option.map_none, reduceCtorEq] at hpost
  | some k =>
    rw [hk] at hpost
    have hnd := Option.some.inj hpost
    subst nd
    have htick := V2.D.Run.tickIdx?_spec hk
    have hjk : V2.D.Run.idxBefore rho d ≤ k := by
      by_contra hn
      have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hs htick d).mp (by omega)
      exact (not_lt.mpr hdt) hlt
    let st := storeAt p c E rho (V2.D.Run.idxBefore rho d) y
    let st' := storeAt p c E rho k y
    have hc := fgsa_store_cumulative p c E rho hnr hjk y
    have hb : eraseFG W ∈ st.base.blocks :=
      (storeBundle_stateBefore E rho _ y).cstore.baseTree _ |>.mpr ⟨W, hW, rfl⟩
    have hkeys := (storeBundle_stateBefore E rho (V2.D.Run.idxBefore rho d) y).«meta».stampKeys
    have hfind : ∃ stamp, st.base.blockStamp.find? (fun row => row.1 == eraseFG W) =
        some (eraseFG W, stamp) := by
      have hm : eraseFG W ∈ st.base.blockStamp.map Prod.fst := hkeys ▸ hb
      cases hf : st.base.blockStamp.find? (fun row => row.1 == eraseFG W) with
      | none =>
        obtain ⟨row, hr, he⟩ := List.mem_map.mp hm
        have hn := List.find?_eq_none.mp hf row hr
        rw [he, beq_self_eq_true] at hn
        contradiction
      | some row =>
        have he : row.1 = eraseFG W := by simpa only [beq_iff_eq] using List.find?_some hf
        exact ⟨row.2, by simp only [← he]⟩
    obtain ⟨stamp, hf⟩ := hfind
    have hstamp : stamp < d := by
      rcases fgsa_block_stamp_source E rho hnr _ y (eraseFG W) stamp
          (List.mem_of_find?_eq_some hf) with hg | ⟨l, hl, t, o, _, ha, hstamp⟩
      · exact hg.2 ▸ hdpos
      · obtain ⟨parent, he, _⟩ := ha.1
        have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hs he d).mp hl
        have hn := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
          (fgsaRestoreTimeLaw p c) E rho hs he y
        rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho l y)] at hn
        exact hstamp ▸ hn.trans_lt ht
    have hkept : st'.base.blockStamp.find? (fun row => row.1 == eraseFG W) =
        some (eraseFG W, stamp) := by
      obtain ⟨tail, htail⟩ := hc.2.2.1
      change (storeAt p c E rho k y).base.blockStamp.find? _ = _
      rw [← htail, List.find?_append, hf]
      rfl
    change W ∈ FGSA.voterBlocks p (clock p st' (SA.voteTime p.toParams s)) s
    apply Finset.mem_filter.mpr
    refine ⟨?_, Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true ?_))⟩
    · change W ∈ (clock p st' (SA.voteTime p.toParams s)).fg.TF.filter _
      apply Finset.mem_filter.mpr
      rw [clock_fg]
      refine ⟨hc.1 hW, ?_⟩
      have hktime : k ≤ timeIdx rho (SA.voteTime p.toParams s) := by
        have hklt := (Gen.V2.Duty.index_lt_idxBefore_iff hs htick
          (SA.voteTime p.toParams s + 1)).mpr (Int.lt_add_one_iff.mpr le_rfl)
        have hcut : V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + 1) =
            timeIdx rho (SA.voteTime p.toParams s) := by
          dsimp only [timeIdx]
          simp only [V2.D.Run.idxBefore_def, Int.lt_add_one_iff]
        exact (hcut ▸ hklt).le
      obtain ⟨K, hK, hKF⟩ := (storeBundle_stateBefore E rho k y).cstore.fg.Fcar
      have hlt := (healing_phase_finality_le p c E rho hK hKF).trans_lt
        (healing_phase_justified_lt p c E rho k y)
      obtain ⟨Q, hQ, hhQ⟩ := healing_phase_frontier_witness p c E rho k y
      have hQ' := (fgsa_store_cumulative p c E rho hnr hktime y).1 hQ
      have hb := (hhQ ▸ healing_phase_height_le p c E rho hQ').trans
        ((healing_phase_local_le_frontier p c E rho hy).trans hcap)
      exact crossing k k y y K W hy le_rfl hK hKF ⟨hy, hc.1 hW⟩ (hlt.trans_le hb)
    · have he : GridCO.stampBlock (clock p st' (SA.voteTime p.toParams s)).base (eraseFG W) =
          stamp := by
        unfold GridCO.stampBlock
        rw [(clock_cumulative p _ _).2.2.1, hkept]
        rfl
      rw [he]
      exact hstamp.trans_le hdf

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:1142–1171, 1270–1274; plan S20, H-PHASE/P2.
DC: INTENTIONAL strict Δ relay and the live-store/frozen-HEAD split.
This is the second frozen RPhase clause. Standalone row spread is separate at ΔF. -/
theorem healing_evidence_spread (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (i : Nat) (ev : V2.Event V (Obj p)) (x : V) (W : FGBlock (Fin p.n)) (m : Nat)
    (hi : rho.events[i]? = some ev) (hx : x ∈ rho.honest) (hgst : E.t_GST ≤ ev.time)
    (_hm : 1 ≤ m) (_hfront : frontierAtIdx p c E rho (i + 1) = m)
    (hbefore : W ∉ (storeAt p c E rho i x).fg.TF)
    (hafter : W ∈ (storeAt p c E rho (i + 1) x).fg.TF) (hh : (heightView p W).h = m)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    (ev.time + p.Δ ≤ rho.horizon → ∀ y ∈ rho.honest,
      E.awake y (ev.time + p.Δ) = true → ∃ j, i < j ∧ j ≤ rho.events.length ∧
        (∀ l e, l < j → rho.events[l]? = some e → e.time < ev.time + p.Δ) ∧
        (W ∈ (storeAt p c E rho j y).fg.TF ∨ m < frontierAtIdx p c E rho j)) ∧
    (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
      SA.voteTime p.toParams s ≤ rho.horizon →
      postClock E rho y (SA.voteTime p.toParams s) = some nd →
      (∃ j, i < j ∧ j ≤ timeIdx rho (SA.voteTime p.toParams s) ∧
        m < frontierAtIdx p c E rho j) ∨ W ∈ FGSA.voterBlocks p nd.st s) := by
  have receipt (y : V) := healing_phase_block_receipt (hroots := hroots) (y := y)
    p c E rho crossing hvalid hnr hdelta hsync
    hi hx hgst hbefore hafter hh
  constructor
  · intro hhor y hy hAwake
    exact ⟨_, receipt y hhor hy hAwake⟩
  · intro y s nd hy htime hhor hpost
    have hdt : ev.time + p.Δ ≤ SA.voteTime p.toParams s := by
      have := p.deltaPos
      simp only [Time] at *
      omega
    have hAwake : E.awake y (ev.time + p.Δ) = true := by
      have hpost' := hpost
      rw [postClock_def, preTick_def] at hpost'
      cases hk : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams s) with
      | none => simp only [hk, Option.map_none, reduceCtorEq] at hpost'
      | some k =>
        have htick := V2.D.Run.tickIdx?_spec hk
        exact fgsa_awake_before_noRestart E rho hvalid hnr y hy _ hhor
          (hvalid.tick_awake y _ (List.mem_of_getElem? htick)) _
          ((hvalid.in_horizon _ (List.mem_of_getElem? hi)).1.trans
            (le_add_of_nonneg_right p.deltaPos.le)) hdt
    obtain ⟨hij, _, _, hw⟩ := receipt y (hdt.trans hhor) hy hAwake
    rcases hw with hw | hrise
    · by_cases hrise : m < frontierAtIdx p c E rho (timeIdx rho (SA.voteTime p.toParams s))
      · exact Or.inl ⟨_, hij.trans_le (healing_phase_idx_le_time p c rho hdt),
          le_rfl, hrise⟩
      right
      apply phase_frozen_mem_of_crossing p c E rho crossing
        hvalid.toScheduleWellFormed hnr
        (lt_add_of_le_of_pos (hvalid.in_horizon _ (List.mem_of_getElem? hi)).1 p.deltaPos)
        hy (hh ▸ Nat.le_of_not_gt hrise) hdt ?_ hw hpost
      cases s with
      | zero =>
        change ev.time + 3 * p.Δ ≤ 4 * p.Δ * (0 : Int) + p.Δ at htime
        have hzero : (0 : Int) ≤ ev.time :=
          (hvalid.in_horizon _ (List.mem_of_getElem? hi)).1
        have hpos : (0 : Int) < p.Δ := p.deltaPos
        have htime' : (ev.time : Int) + 3 * (p.Δ : Int) ≤ p.Δ := by
          simpa only [mul_zero, zero_add] using htime
        linarith only [htime', hzero, hpos]
      | succ s =>
        change ev.time + p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
        change ev.time + 3 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ at htime
        push_cast at htime
        simp only [Time] at *
        linarith
    · exact Or.inl ⟨_, hij, healing_phase_idx_le_time p c rho hdt, hrise⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1125–1132; plan S20, H-PHASE/P2, using H-BASE/HB4.
DC: INTENTIONAL standalone phase rows use the independent ΔF deadline.
All selected rows reach every honest node, including rows sent before GST. -/
theorem healing_phase_rows_spread (ΔF : Time)
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    (receipt : TRowsReceipt p c E rho ΔF) (t : Time)
    (hgst : E.t_GST ≤ t) (hhor : t + ΔF ≤ rho.horizon)
    (rows : Finset (RowWire p.n))
    (hsent : ∀ a ∈ rows, ∃ j y r, HonestRowAt p c E rho j y r a ∧ p.actionTime r ≤ t) :
    ∀ x ∈ rho.honest, ∀ a ∈ rows, HeldBefore p c E rho x a (t + ΔF) := by
  intro x hx a ha
  obtain ⟨j, y, r, hrow, ht⟩ := hsent a ha
  exact healing_phase_receipt p c E rho ΔF hs hnr receipt hrow ht hgst hhor hx


omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1142–1171; plan S20, H-PHASE r2/P3.
DC: SAME a later strict cut contains every earlier strict receipt. -/
theorem healing_phase_idxBefore_mono {d d' : Time} (hdd : d ≤ d') :
    V2.D.Run.idxBefore rho d ≤ V2.D.Run.idxBefore rho d' := by
  change (rho.events.filter (fun e => decide (e.time < d))).length ≤
    (rho.events.filter (fun e => decide (e.time < d'))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true ((of_decide_eq_true he).trans_le hdd))

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1155–1163; plan S20, H-PHASE r2/P3.
DC: SAME an event at or before t lies before the inclusive cut at t. -/
theorem healing_phase_lt_timeIdx (hs : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {e : V2.Event V (Obj p)} (hk : rho.events[k]? = some e) {t : Time}
    (ht : e.time ≤ t) : k < timeIdx rho t := by
  have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hs hk (t + 1)).mpr (Int.lt_add_one_iff.mpr ht)
  refine hlt.trans_le ?_
  change (rho.events.filter (fun e => decide (e.time < t + 1))).length ≤
    (rho.events.filter (fun e => decide (e.time ≤ t))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true (Int.lt_add_one_iff.mp (of_decide_eq_true he)))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1193–1209; plan S20, H-PHASE r2/P3. DC: SAME cumulative cache bound. -/
private theorem phase_hmax_mono (hnr : V2.D.NoRestart rho) {i j : Nat} (hij : i ≤ j) (x : V) :
    (storeAt p c E rho i x).fg.h_max ≤ (storeAt p c E rho j x).fg.h_max := by
  have hi : KitFG.FGStoreInvariant (heightView p) (finalityView p)
      (storeAt p c E rho i x).fg := (storeBundle_stateBefore E rho i x).cstore.fg
  have hj : KitFG.FGStoreInvariant (heightView p) (finalityView p)
      (storeAt p c E rho j x).fg := (storeBundle_stateBefore E rho j x).cstore.fg
  rw [hi.hmax, hj.hmax]
  exact sup_le_sup_right (Finset.sup_mono (fgsa_store_cumulative p c E rho hnr hij x).1) 1

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1193–1209; plan S20, H-PHASE r2/P3.
DC: SAME the global frontier does not fall in a restart-free run. -/
theorem healing_frontier_mono (hnr : V2.D.NoRestart rho) {i j : Nat} (hij : i ≤ j) :
    frontierAtIdx p c E rho i ≤ frontierAtIdx p c E rho j :=
  Finset.sup_mono_fun (fun x _ => phase_hmax_mono p c E rho hnr hij x)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:1142–1171; plan S20, H-PHASE r2/P3.
DC: INTENTIONAL a held carrier is relayed by max(t, GST) + Δ.
The carrier can be accepted before GST. Assembly supplies RXing.
The frontier cap at the deadline gives the receiver's F compatibility. -/
theorem healing_phase_held_receipt (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {i : Nat} {ev : V2.Event V (Obj p)} {x : V} {W : FGBlock (Fin p.n)}
    (hi : rho.events[i]? = some ev) (hx : x ∈ rho.honest) (hgst : E.t_GST ≤ ev.time)
    (hW : W ∈ (storeAt p c E rho (i + 1) x).fg.TF) (hhor : ev.time + p.Δ ≤ rho.horizon)
    (hcap : frontierAtIdx p c E rho (V2.D.Run.idxBefore rho (ev.time + p.Δ)) ≤
      (heightView p W).h)
    {y : V} (hy : y ∈ rho.honest)
    (hAwake : E.awake y (ev.time + p.Δ) = true)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    W ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho (ev.time + p.Δ)) y).fg.TF := by
  let j := V2.D.Run.idxBefore rho (ev.time + p.Δ)
  have hs := hvalid.toScheduleWellFormed
  by_cases hgen : W = .genesis
  · exact hgen ▸ (storeBundle_stateBefore E rho j y).cstore.fg.gen
  have hbase := (storeBundle_stateBefore E rho (i + 1) x).cstore.baseTree (eraseFG W)
  have hm := hbase.mpr ⟨W, hW, rfl⟩
  rw [← (metaInv_stateBefore E rho (i + 1) x).stampKeys] at hm
  obtain ⟨⟨b, stamp⟩, hm, he⟩ := List.mem_map.mp hm
  dsimp only at he
  subst b
  rcases fgsa_block_stamp_source E rho hnr (i + 1) x (eraseFG W) stamp hm with
    hg | ⟨l, hl, t, o, hb, ha, _⟩
  · exact (hgen (eraseFG_eq_genesis.mp hg.1)).elim
  obtain ⟨o', hd, _⟩ := ha.1
  have htl : t ≤ ev.time := by
    have hil : l < V2.D.Run.idxBefore rho (ev.time + 1) :=
      lt_of_le_of_lt (Nat.lt_succ_iff.mp hl)
        ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mpr (Int.lt_add_one_iff.mpr le_rfl))
    exact Int.lt_add_one_iff.mp ((Gen.V2.Duty.index_lt_idxBefore_iff hs hd _).mp hil)
  obtain ⟨s, N, hdec, heN⟩ := phase_block_decode p hb
  have ho : o = ofWire p ⟨.proposer s, .proposal N⟩ := by
    apply toWire_injective
    rw [toWire_ofWire]
    exact decode_eq_block.mp hdec
  have hdl : max t E.t_GST + p.Δ ≤ ev.time + p.Δ := Int.add_le_add_right (max_le htl hgst) _
  let j' := V2.D.Run.idxBefore rho (max t E.t_GST + p.Δ)
  have hj' : j' ≤ j := healing_phase_idxBefore_mono p c rho hdl
  obtain ⟨K, hK, hKF⟩ := (storeBundle_stateBefore E rho j' y).cstore.fg.Fcar
  have hfj := (healing_phase_finality_le p c E rho hK hKF).trans_lt
    (healing_phase_justified_lt p c E rho j' y)
  have hmax := ((phase_hmax_mono p c E rho hnr hj' y).trans
    (healing_phase_local_le_frontier p c E rho (i := j) hy)).trans hcap
  have hxW : HeldAt p c E rho (max j' (i + 1)) x W :=
    ⟨hx, (fgsa_store_cumulative p c E rho hnr (le_max_right j' (i + 1)) x).1 hW⟩
  have hFW := crossing j' (max j' (i + 1)) y x K W hy (le_max_left _ _) hK hKF hxW
    (by simp only [Height] at *; omega)
  have hcompat : Block.Compatible (eraseFG W)
      (eraseFG (V2.D.Run.stateBeforeTime E rho (max t E.t_GST + p.Δ) y).st.fg.F) := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
    exact Bool.or_eq_true_iff.mpr (Or.inr (eraseFG_preceq hFW))
  have delay (o : Obj p) (hn : ¬ isRowObject o) : fgsaDelay E.Δ ΔF o = p.Δ := by
    cases he : o.payload <;> simp only [fgsaDelay_def, he, hdelta]
    exact (hn (by change (match o.payload with | .row _ => True | _ => False)
                  rw [he]; trivial)).elim
  have hD := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hsync
    (fun o => ¬ isRowObject o) p.Δ delay
  have hT : Gen.V2.Duty.Trigger E rho
      (ofWire p ⟨.proposer s, .proposal N⟩) t :=
    Or.inr ⟨x, hx, l, ho ▸ ha⟩
  have hlt : t < max t E.t_GST + p.Δ :=
    lt_add_of_le_of_pos (le_max_left _ _) p.deltaPos
  obtain ⟨Y, hY, he⟩ := fgsa_proposal_receipt (hRoots := hroots) E rho hdelta hvalid hnr
    (fun t => max t E.t_GST + p.Δ) rho.horizon s N t y
    hD hT hy (hdl.trans hhor) hlt (by simpa only [heN] using hcompat)
    (hdl.trans hhor) (by
      intro u hu hud
      exact fgsa_awake_before_noRestart E rho hvalid hnr y hy _ hhor hAwake u
        ((fgsa_trigger_nonneg E rho hs hT).trans hu) (hud.le.trans hdl))
  have heq : Y = W := eraseFG_injective (he.trans heN)
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs, heq] at hY
  exact (fgsa_store_cumulative p c E rho hnr hj' y).1 hY

/-- The global frontier is monotone through restarts under RMonoAll. -/
theorem healing_frontier_mono_all (mono : RMonoAll p c E rho)
    {i j : Nat} (hij : i ≤ j) :
    frontierAtIdx p c E rho i ≤ frontierAtIdx p c E rho j :=
  Finset.sup_mono_fun (fun x hx => (mono i j x hx hij).2.2)

end AvailableChain.FGSA.Run
end
