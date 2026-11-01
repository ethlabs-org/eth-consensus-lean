module
public import AvailableChainFGSAProofs.Statements.WeakContinuation
public import AvailableChainFGSAProofs.Proofs.Shared.Reads -- shake: keep (B3 ownSeats)

public section

/-! WC J1: exact finite replay. DC: PrefixAgreement; blueprint 23 §3.
The source execution supplies its time bound. Agreement supplies every input
read by a tick. No property of a later continuation event is assumed. -/

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} {E E' : Generic.Env V}
    {source rho : V2.D.Run V (fgsa p c)} {ΔF : Time}

omit [DecidableEq V] in
/-- WC J1; DC PrefixAgreement: the agreed event list is a prefix. -/
theorem wc_eventsReplay (ha : AgreesThrough₂ p c E source E' rho ΔF) :
    rho.events = source.events ++ rho.events.drop source.events.length := by
  conv_lhs => rw [← List.take_append_drop source.events.length rho.events, ha.events]

omit [DecidableEq V] in
/-- WC J1; DC PrefixAgreement: replay each actual source event. -/
theorem wc_eventReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    {i : Nat} (hi : i < source.events.length) :
    rho.events[i]? = source.events[i]? := by
  rw [← ha.events, List.getElem?_take_of_lt hi]

/-- WC J1; DC PrefixAgreement: replay the world at each source prefix. -/
theorem wc_prefixReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {i : Nat} (hi : i ≤ source.events.length) :
    rho.stateBefore E' i = source.stateBefore E i := by
  unfold V2.D.Run.stateBefore
  have htake : rho.events.take i = source.events.take i := by
    rw [← ha.events, List.take_take, Nat.min_eq_left hi]
  rw [htake]
  apply List.foldl_ext
  intro world event he
  have ht := (hv.in_horizon event (List.mem_of_mem_take he)).2
  cases event with
  | restart v t => rfl
  | deliver v o t => rfl
  | tick v t =>
    simp only [V2.D.World.step, V2.D.tick, V2.D.Run.ownSeats, ha.seats,
      ha.inputs v t ht, ha.awake v t ht]

/-- WC J1; DC PrefixAgreement: the complete tick and its emissions agree. -/
theorem wc_tickReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {i : Nat} {x : V} {t : Time}
    (he : source.events[i]? = some (.tick x t)) :
    V2.D.tick E' rho (rho.stateBefore E' i x) x t =
      V2.D.tick E source (source.stateBefore E i x) x t := by
  have hi := List.getElem?_eq_some_iff.mp he
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).2
  rw [wc_prefixReplay ha hv (Nat.le_of_lt hi.1)]
  simp only [V2.D.tick, V2.D.Run.ownSeats, ha.seats, ha.inputs x t ht, ha.awake x t ht]

/-- WC J1; DC PrefixAgreement: replay actual emitted objects, with their indices. -/
theorem wc_emitsReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {i : Nat} (hi : i < source.events.length) :
    rho.emitsAt E' i = source.emitsAt E i := by
  unfold V2.D.Run.emitsAt
  rw [wc_eventReplay ha hi]
  cases he : source.events[i]? with
  | none => rfl
  | some e =>
    cases e with
    | restart x t => rfl
    | deliver x o t => rfl
    | tick x t => exact congrArg Prod.snd (wc_tickReplay ha hv he)

/-- WC J1; DC PrefixAgreement: replay each receipt stamp and store field. -/
theorem wc_storeReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {i : Nat} (hi : i ≤ source.events.length)
    (x : V) : storeAt p c E' rho i x = storeAt p c E source i x := by
  exact congrArg (fun world => (world x).st) (wc_prefixReplay ha hv hi)

/-- WC J1; DC PrefixAgreement: suffix events cannot enter an old cut. -/
theorem wc_cutReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {t : Time} (ht : t ≤ source.horizon) :
    afterTicksIdx rho t = afterTicksIdx source t := by
  have _ := hv
  have hnil : (rho.events.drop source.events.length).filter (cutPred t) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he hc
    have he' := ha.suffixTime e he
    have hle : e.time ≤ t := by
      rcases Prod.Lex.toLex_le_toLex.mp (of_decide_eq_true hc) with h | ⟨h, _⟩
      · exact le_of_lt h
      · exact le_of_eq h
    exact (not_lt_of_ge (hle.trans ht)) he'
  change (rho.events.filter (cutPred t)).length = _
  rw [wc_eventsReplay ha, List.filter_append, hnil, List.append_nil]
  rfl

/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private def replayTickPred (x : V) (t : Time) (e : V2.Event V (fgsa p c).Object) : Bool :=
  match e with
  | .tick y u => decide (y = x ∧ u = t)
  | _ => false

/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem replayTickPred_eq (run : V2.D.Run V (fgsa p c)) (x : V) (t : Time) :
    run.tickIdx? x t = run.events.findIdx? (replayTickPred x t) := by
  unfold V2.D.Run.tickIdx?
  congr 1
  funext e
  cases e <;> rfl

/-- WC J1; DC PrefixAgreement: an old tick lookup cannot select a suffix event. -/
theorem wc_tickIdxReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (x : V) {t : Time} (ht : t ≤ source.horizon) :
    rho.tickIdx? x t = source.tickIdx? x t := by
  rw [replayTickPred_eq, replayTickPred_eq]
  rw [wc_eventsReplay ha, List.findIdx?_append]
  have hn : (rho.events.drop source.events.length).findIdx? (replayTickPred x t) = none := by
    apply List.findIdx?_eq_none_iff.mpr
    intro e he
    have hb := ha.suffixTime e he
    cases e with
    | restart y u => rfl
    | deliver y o u => rfl
    | tick y u =>
      change decide (y = x ∧ u = t) = false
      simp only [decide_eq_false_iff_not]
      rintro ⟨_, rfl⟩
      exact (not_lt_of_ge ht) hb
  rw [hn]
  simp only [Option.map_none, Option.or_none]

/-- WC J1; DC PrefixAgreement: replay the exact pre-clock input through the endpoint. -/
theorem wc_preTickReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) (x : V) {t : Time}
    (ht : t ≤ source.horizon) : preTick E' rho x t = preTick E source x t := by
  rw [preTick_def, preTick_def, wc_tickIdxReplay ha x ht]
  cases he : source.tickIdx? x t with
  | none => rfl
  | some i =>
    have hi := List.getElem?_eq_some_iff.mp (V2.D.Run.tickIdx?_spec he)
    simp only [Option.map_some]
    rw [wc_prefixReplay ha hv (Nat.le_of_lt hi.1)]

/-- WC J1; DC PrefixAgreement: replay the post-clock duty input, including sleepers. -/
theorem wc_postClockReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) (x : V) {t : Time}
    (ht : t ≤ source.horizon) : postClock E' rho x t = postClock E source x t := by
  rw [postClock_def, postClock_def, wc_preTickReplay ha hv x ht]

/-- WC J1; DC PrefixAgreement: replay a deterministic HEAD at its original read. -/
theorem wc_headReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) (x : V) {s : Slot}
    (ht : SA.voteTime p.toParams s ≤ source.horizon) :
    headAtLabel p c E' rho x s = headAtLabel p c E source x s := by
  unfold headAtLabel
  rw [wc_postClockReplay ha hv x ht]

/-- WC J1; DC PrefixAgreement: replay an action source at the original action time. -/
theorem wc_sourceReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) (x : V) {r : Nat}
    (ht : p.actionTime r ≤ source.horizon) :
    actionSourceFG p c E' rho x r = actionSourceFG p c E source x r := by
  rw [actionSourceFG_def, actionSourceFG_def, wc_postClockReplay ha hv x ht]

/-- WC J1; DC PrefixAgreement: signed rows retain the original action index. -/
theorem wc_rowReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {i : Nat} (hi : i < source.events.length)
    (x : V) (r : Nat) (a : RowWire p.n) :
    HonestRowAt p c E' rho i x r a ↔ HonestRowAt p c E source i x r a := by
  rw [HonestRowAt_def, HonestRowAt_def, ha.honest, wc_eventReplay ha hi,
    wc_emitsReplay ha hv hi]

/-- WC J1; DC PrefixAgreement: preserve acceptance triggers with their event index. -/
theorem wc_acceptsReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {i : Nat} (hi : i < source.events.length)
    (x : V) (o : Obj p) (t : Time) :
    rho.acceptsAt E' i x o t ↔ source.acceptsAt E i x o t := by
  unfold V2.D.Run.acceptsAt V2.D.Run.handlesAt
  rw [wc_prefixReplay ha hv (Nat.le_of_lt hi),
    wc_prefixReplay ha hv (Nat.succ_le_of_lt hi), wc_eventReplay ha hi]

/-- WC J1; DC PrefixAgreement: replay the completed actual step. -/
theorem wc_stepReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {i : Nat} (hi : i < source.events.length) :
    rho.stateBefore E' (i + 1) = source.stateBefore E (i + 1) :=
  wc_prefixReplay ha hv (Nat.succ_le_of_lt hi)

/-- WC J1; DC PrefixAgreement: replay each exact intermediate duty input. -/
theorem wc_dutyReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {i : Nat} (hi : i < source.events.length)
    (x : V) (phase : WCDutyPhase) (st : State p.n) :
    WCDutyInput p c E' rho i x phase st ↔ WCDutyInput p c E source i x phase st := by
  have he := wc_eventReplay ha hi
  have hs := wc_storeReplay ha hv (Nat.le_of_lt hi) x
  constructor
  · intro h
    exact ⟨hi, h.joined, by simpa only [he, hs] using h.input⟩
  · intro h
    refine ⟨?_, h.joined, by simpa only [he, hs] using h.input⟩
    obtain ⟨t, ht, _⟩ := h.input
    exact (List.getElem?_eq_some_iff.mp (he.trans ht)).1

/-- WC J1; DC PrefixAgreement: replay gate inputs at covered times. -/
theorem wc_gateInReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) (x : V) {s : Slot}
    (ht : SA.gateTime p.toParams s ≤ source.horizon) :
    gateIn p c E' rho x s = gateIn p c E source x s := by
  rw [gateIn_def, gateIn_def, wc_preTickReplay ha hv x ht]

/-- WC J1; DC PrefixAgreement: a raw result keeps its original value. -/
theorem wc_gateReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) (x : V) {s : Slot}
    (ht : SA.gateTime p.toParams s ≤ source.horizon) :
    gateResult p c E' rho x s = gateResult p c E source x s := by
  rw [gateResult_def, gateResult_def, wc_gateInReplay ha hv x ht]

/-- WC J1; DC PrefixAgreement: fast-write support is read at the original gate. -/
theorem wc_fastReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) (x : V) {s : Slot} (B : Block)
    (ht : SA.gateTime p.toParams s ≤ source.horizon) :
    fastAt p c E' rho x s B ↔ fastAt p c E source x s B := by
  unfold fastAt
  rw [wc_gateInReplay ha hv x ht]

/-- WC J1; DC PrefixAgreement: replay a result at its actual event index. -/
theorem wc_gateAtReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {i : Nat} (hi : i < source.events.length) :
    gateResultAt p c E' rho i = gateResultAt p c E source i := by
  unfold gateResultAt
  rw [wc_eventReplay ha hi, wc_prefixReplay ha hv (Nat.le_of_lt hi)]

omit [DecidableEq V] in
/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_isGateReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    {i : Nat} (hi : i < source.events.length) (x : V) (s : Slot) :
    IsGateTick p c rho i x s ↔ IsGateTick p c source i x s := by
  unfold IsGateTick
  rw [wc_eventReplay ha hi]


/-- The enabled guard replays with its tick and stored restart marker. -/
private theorem wc_enabledReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {i : Nat} (hi : i < source.events.length)
    (x : V) (s : Slot) :
    enabledGateAt p c E' rho i x s ↔ enabledGateAt p c E source i x s := by
  constructor
  · intro h
    refine ⟨(wc_isGateReplay ha hi x s).mp h.1, ?_⟩
    have hb := h.2
    change (match (storeAt p c E' rho i x).restartTime with
      | none => True | some w => w ≤ slotStartZ p (s : Int)) at hb
    rw [wc_storeReplay ha hv hi.le] at hb
    exact hb
  · intro h
    refine ⟨(wc_isGateReplay ha hi x s).mpr h.1, ?_⟩
    change (match (storeAt p c E' rho i x).restartTime with
      | none => True | some w => w ≤ slotStartZ p (s : Int))
    rw [wc_storeReplay ha hv hi.le]
    exact h.2


/-- WC J1; DC PrefixAgreement: the original guard and write input are unchanged. -/
theorem wc_passedReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {i : Nat} (hi : i < source.events.length) :
    gatePassedAt p c E' rho i ↔ gatePassedAt p c E source i := by
  constructor
  · rintro ⟨x, s, hG, hfresh, B, hB, hguard⟩
    refine ⟨x, s, (wc_enabledReplay ha hv hi x s).mp hG, ?_, B, ?_, ?_⟩
    · simpa only [wc_storeReplay ha hv hi.le] using hfresh
    · simpa only [wc_storeReplay ha hv hi.le] using hB
    · simpa only [wc_storeReplay ha hv hi.le] using hguard
  · rintro ⟨x, s, hG, hfresh, B, hB, hguard⟩
    refine ⟨x, s, (wc_enabledReplay ha hv hi x s).mpr hG, ?_, B, ?_, ?_⟩
    · simpa only [wc_storeReplay ha hv hi.le] using hfresh
    · simpa only [wc_storeReplay ha hv hi.le] using hB
    · simpa only [wc_storeReplay ha hv hi.le] using hguard

/-- WC J1; DC PrefixAgreement: the post-clock HEAD retains all original pools. -/
theorem wc_headAtReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {i : Nat} (hi : i < source.events.length) (s : Slot) :
    headAtIdx p c E' rho i s = headAtIdx p c E source i s := by
  unfold headAtIdx
  rw [wc_eventReplay ha hi, wc_prefixReplay ha hv (Nat.le_of_lt hi)]

/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_action_gate (r : Nat) :
    p.actionTime r = SA.gateTime p.toParams (r * p.R) := rfl

omit [DecidableEq V] in
/-- Local event epochs replay exactly through the source prefix. -/
private theorem wc_restartFreeReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    {a b : Nat} (hb : b ≤ source.events.length) (x : V) :
    V2.D.restartFree rho x a b ↔ V2.D.restartFree source x a b := by
  constructor <;> intro h j t haj hjb hj
  · exact h j t haj hjb ((wc_eventReplay ha (hjb.trans_le hb)).trans hj)
  · exact h j t haj hjb ((wc_eventReplay ha (hjb.trans_le hb)).symm.trans hj)


/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_receiptsReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {i : Nat} (hi : i ≤ source.events.length)
    {x : V} {st : State p.n} (h : WCReceiptOrigins p c E source i x st) :
    WCReceiptOrigins p c E' rho i x st := by
  constructor
  · intro B stamp hm
    rcases h.blocks B stamp hm with hz | hacc | ⟨hn, j, hj, w, he, hm, hs, hrf⟩
    · exact Or.inl hz
    · obtain ⟨j, hj, t, o, ho, ha', he⟩ := hacc
      refine Or.inr (Or.inl ⟨j, hj, t, o, ho,
        (wc_acceptsReplay ha hv (hj.trans_le hi) x o t).mpr ha', ?_⟩)
      rw [wc_storeReplay ha hv (hj.le.trans hi)]
      exact he
    · refine Or.inr (Or.inr ⟨hn, j, hj, w,
        (wc_eventReplay ha (hj.trans_le hi)).trans he, ?_, hs,
        (wc_restartFreeReplay ha hi x).mpr hrf⟩)
      rw [wc_storeReplay ha hv ((Nat.succ_le_of_lt hj).trans hi)]
      exact hm
  · intro s k b stamp hm
    rcases h.votes s k b stamp hm with ⟨j, hj, t, ha', he⟩ | ⟨j, hj, w, he, hm, hs, hrf⟩
    · refine Or.inl ⟨j, hj, t,
        (wc_acceptsReplay ha hv (hj.trans_le hi) _ _ _).mpr ha', ?_⟩
      rw [wc_storeReplay ha hv (hj.le.trans hi)]
      exact he
    · refine Or.inr ⟨j, hj, w, (wc_eventReplay ha (hj.trans_le hi)).trans he,
        ?_, hs, (wc_restartFreeReplay ha hi x).mpr hrf⟩
      rw [wc_storeReplay ha hv ((Nat.succ_le_of_lt hj).trans hi)]
      exact hm

/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_headReadReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {i : Nat} (hi : i < source.events.length)
    {x : V} {s : Slot} {B : Block} (h : WCHeadRead p c E source i x s B) :
    WCHeadRead p c E' rho i x s B := by
  refine ⟨(wc_eventReplay ha hi).trans h.event, ?_, ?_, ?_⟩
  · rw [wc_headAtReplay ha hv hi]
    exact h.covers
  · rw [wc_storeReplay ha hv hi.le]
    exact h.path
  · rw [wc_storeReplay ha hv hi.le]
    exact wc_receiptsReplay ha hv hi.le h.receipts

/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_scopeReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {B : Block}
    (h : RootBlockInRun p c E source B) : RootBlockInRun p c E' rho B := by
  obtain ⟨N, ⟨M, hm, hNM⟩, he⟩ := h
  refine ⟨N, ⟨M, ?_, hNM⟩, he⟩
  rcases hm with hd | ⟨x, hx, i, hi⟩
  · left
    obtain ⟨x, o, t, hm, ho⟩ := hd
    refine ⟨x, o, t, ?_, ho⟩
    rw [wc_eventsReplay ha]
    exact List.mem_append_left _ hm
  · right
    refine ⟨x, ha.honest ▸ hx, min i source.events.length, ?_⟩
    rw [wc_prefixReplay ha hv (Nat.min_le_right _ _)]
    have heq : source.stateBefore E (min i source.events.length) = source.stateBefore E i := by
      unfold V2.D.Run.stateBefore
      rw [← List.take_take, List.take_length]
    rw [heq]
    exact hi


/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_leaseReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {i : Nat} (hi : i ≤ source.events.length)
    {x : V} {row : Block × Nat × Time} (h : WCLeaseOrigin p c E source i x row) :
    WCLeaseOrigin p c E' rho i x row := by
  obtain ⟨j, hj, s, B, ht, hp, hb, hr, hk, hd, hrel, hlast⟩ := h.origin
  have hjL := hj.trans_le hi
  refine ⟨j, hj, s, B, (wc_enabledReplay ha hv hjL x s).mpr ht,
    (wc_passedReplay ha hv hjL).mpr hp, ?_, hr, ?_, hd, hrel, ?_⟩
  · rw [wc_gateAtReplay ha hv hjL]
    exact hb
  · rw [wc_storeReplay ha hv hjL.le]
    exact hk
  · intro k v C hjk hki htk
    dsimp only
    rw [wc_storeReplay ha hv (hki.le.trans hi)]
    exact hlast k v C hjk hki ((wc_enabledReplay ha hv (hki.trans_le hi) x v).mp htk)

/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_targetReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {i : Nat} (hi : i ≤ source.events.length)
    {X : SimplexFG.FGBlock (Fin p.n)} {h : SimplexFG.Height}
    (ho : WCTargetOrigin p c E source i X h) : WCTargetOrigin p c E' rho i X h := by
  obtain ⟨j, y, r, wire, K, B, hj, hr, hn, hK, hXK, hB, hKB⟩ := ho.origin
  have ht := (hv.in_horizon _ (List.mem_of_getElem? hr.2.1)).2
  have hg : SA.gateTime p.toParams (r * p.R) ≤ source.horizon := ht
  refine ⟨j, y, r, wire, K, B, hj, (wc_rowReplay ha hv (hj.trans_le hi) y r wire).mpr hr,
    hn, ?_, hXK, ?_, hKB⟩
  · rw [wc_sourceReplay ha hv y ht]
    exact hK
  · rw [wc_gateReplay ha hv y hg]
    exact hB

/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_finiteReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {i : Nat} (hi : i ≤ source.events.length)
    (h : WCFiniteFacts p c E source i) : WCFiniteFacts p c E' rho i := by
  have honest (x : V) (hx : x ∈ rho.honest) : x ∈ source.honest := ha.honest ▸ hx
  constructor
  · intro x hx
    rw [wc_storeReplay ha hv hi]
    exact h.store x (honest x hx)
  · intro x hx
    rw [wc_storeReplay ha hv hi]
    exact h.nesting x (honest x hx)
  · intro x hx
    rw [wc_storeReplay ha hv hi]
    exact h.metadata x (honest x hx)
  · intro x hx
    rw [wc_storeReplay ha hv hi]
    exact wc_receiptsReplay ha hv hi (h.receipts x (honest x hx))
  · intro x hx row hr
    rw [wc_storeReplay ha hv hi] at hr
    exact wc_leaseReplay ha hv hi (h.leases x (honest x hx) row hr)
  · intro x hx K g deadline hr B hB hBK
    rw [wc_storeReplay ha hv hi] at hr ⊢
    exact h.deadlines x (honest x hx) K g deadline hr B hB hBK
  · intro x hx s X hX
    rw [wc_storeReplay ha hv hi] at hX
    obtain ⟨j, hj, hrf, ht, hp, B, hb, hXB, hf⟩ := h.fastWrites x (honest x hx) s X hX
    have hjL := hj.trans_le hi
    refine ⟨j, hj, (wc_restartFreeReplay ha hi x).mpr hrf,
      (wc_enabledReplay ha hv hjL x s).mpr ht,
      (wc_passedReplay ha hv hjL).mpr hp, B, ?_, hXB, ?_⟩
    · rw [wc_gateAtReplay ha hv hjL]
      exact hb
    · exact (wc_fastReplay ha hv x X (hv.in_horizon _ (List.mem_of_getElem? ht.1)).2).mpr hf
  · intro x hx s C hc
    rw [wc_storeReplay ha hv hi] at hc
    obtain ⟨j, hj, hrf, ht, hb⟩ := h.saved x (honest x hx) s C hc
    refine ⟨j, hj, (wc_restartFreeReplay ha hi x).mpr hrf,
      (wc_enabledReplay ha hv (hj.trans_le hi) x s).mpr ht, ?_⟩
    rw [wc_gateAtReplay ha hv (hj.trans_le hi)]
    exact hb
  · intro x hx W hW X hX hne
    rw [wc_storeReplay ha hv hi] at hW
    exact wc_targetReplay ha hv hi (h.certified x (honest x hx) W hW X hX hne)
  · intro j k x r r' a b u v hj hk ha' hb hu hv'
    exact h.client j k x r r' a b u v hj hk
      ((wc_rowReplay ha hv (hj.trans_le hi) x r a).mp ha')
      ((wc_rowReplay ha hv (hk.trans_le hi) x r' b).mp hb) hu hv'

/-- WC J1; DC prefix seed transfer: only finite evidence is replayed.
Continuation foundations and later relay service remain separate inputs. -/
theorem wc_seedReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {w : HealingWitness} {iStar : Nat}
    (hs : WCSeed p c E source w iStar)
    (hend : SA.gateTime p.toParams w.u < source.horizon) : WCSeed p c E' rho w iStar := by
  have honest (x : V) (hx : x ∈ rho.honest) : x ∈ source.honest := ha.honest ▸ hx
  have hi := hs.within
  have hcut : iStar = afterTicksIdx rho (SA.gateTime p.toParams w.u) :=
    hs.cut.trans (wc_cutReplay ha hv hend.le).symm
  refine ⟨hcut, ?_, ?_, ?_, ?_, hs.sourcePrefix, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    wc_finiteReplay ha hv hi hs.finite⟩
  · rw [hcut]
    exact List.length_filter_le _ _
  · rw [ha.gst]
    exact hs.afterGST
  · rw [ha.gst]
    exact hs.firstVoteAfterGST
  · obtain ⟨WStar, he, hh, hscope, hstored⟩ := hs.carrier
    refine ⟨WStar, he, hh, wc_scopeReplay ha hv hscope, ?_⟩
    intro x hx
    rw [wc_storeReplay ha hv hi]
    exact hstored x (honest x hx)
  · intro x hx
    obtain ⟨j, hj, ht, hb, hp⟩ := hs.gates x (honest x hx)
    refine ⟨j, hj, (wc_isGateReplay ha (hj.trans_le hi) x w.u).mpr ht, ?_,
      (wc_passedReplay ha hv (hj.trans_le hi)).mpr hp⟩
    rw [wc_gateAtReplay ha hv (hj.trans_le hi)]
    exact hb
  · intro x hx
    rw [S_at_def, wc_storeReplay ha hv hi]
    exact hs.refreshed x (honest x hx)
  · intro x hx
    obtain ⟨k, hk, hhead⟩ := hs.nextHeads x (honest x hx)
    exact ⟨k, hk, wc_headReadReplay ha hv (hk.trans_le hi) hhead⟩
  · intro j x r a e hj hr he hh
    have hrow := (wc_rowReplay ha hv (hj.trans_le hi) x r a).mp hr
    have ht := (hv.in_horizon _ (List.mem_of_getElem? hrow.2.1)).2
    have hg : SA.gateTime p.toParams (r * p.R) ≤ source.horizon := ht
    obtain ⟨K, B, hK, hp, heK, hB, hKB, hKQ⟩ := hs.highSources j x r a e hj hrow he hh
    refine ⟨K, B, ?_, hp, heK, ?_, hKB, hKQ⟩
    · rw [wc_sourceReplay ha hv x ht]
      exact hK
    · rw [wc_gateReplay ha hv x hg]
      exact hB
  · intro x hx
    rw [wc_storeReplay ha hv hi]
    exact hs.height x (honest x hx)
  · intro x hx
    change Block.Preceq (eraseFG (storeAt p c E' rho iStar x).fg.F) w.QStar
    rw [wc_storeReplay ha hv hi]
    exact hs.finalBelow x (honest x hx)
  · intro x hx row hr htime
    rw [wc_storeReplay ha hv hi] at hr htime
    exact hs.liveTargets x (honest x hx) row hr htime

omit [DecidableEq V] in
/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_filterReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (test : V2.Event V (fgsa p c).Object → Bool)
    (htest : ∀ e, test e = true → e.time ≤ source.horizon) :
    rho.events.filter test = source.events.filter test := by
  have hn : (rho.events.drop source.events.length).filter test = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he ht
    exact (not_lt_of_ge (htest e ht)) (ha.suffixTime e he)
  rw [wc_eventsReplay ha, List.filter_append, hn, List.append_nil]

/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_filteredWorldReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source)
    (test : V2.Event V (fgsa p c).Object → Bool)
    (htest : ∀ e, test e = true → e.time ≤ source.horizon) :
    (rho.events.filter test).foldl (V2.D.World.step E' rho) V2.D.World.init =
      (source.events.filter test).foldl (V2.D.World.step E source) V2.D.World.init := by
  rw [wc_filterReplay ha test htest]
  apply List.foldl_ext
  intro world event he
  have ht := (hv.in_horizon event (List.mem_filter.mp he).1).2
  cases event with
  | restart x t => rfl
  | deliver x o t => rfl
  | tick x t =>
    simp only [V2.D.World.step, V2.D.tick, V2.D.Run.ownSeats, ha.seats,
      ha.inputs x t ht, ha.awake x t ht]

/-- WC J1; DC inclusive endpoint: replay public reads through the source horizon. -/
theorem wc_readReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {t : Time} (ht : t ≤ source.horizon) :
    rho.readAt E' t = source.readAt E t :=
  wc_filteredWorldReplay ha hv _ (fun _ he => (of_decide_eq_true he).trans ht)

/-- WC J1; DC strict read: retain the strict receipt cutoff through the source horizon. -/
theorem wc_beforeReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {t : Time} (ht : t ≤ source.horizon) :
    rho.stateBeforeTime E' t = source.stateBeforeTime E t :=
  wc_filteredWorldReplay ha hv _ (fun _ he => (le_of_lt (of_decide_eq_true he)).trans ht)

omit [DecidableEq V] in
/-- WC J1; DC inclusive endpoint: replay the public-read index. -/
theorem wc_timeIdxReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    {t : Time} (ht : t ≤ source.horizon) : timeIdx rho t = timeIdx source t :=
  congrArg List.length (wc_filterReplay ha _ (fun _ he => (of_decide_eq_true he).trans ht))

/-- WC J1; DC selected gate: replay the complete post-tick world. -/
theorem wc_afterTicksReplay (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) {t : Time} (ht : t ≤ source.horizon) :
    afterTicks E' rho t = afterTicks E source t := by
  apply wc_filteredWorldReplay ha hv
  intro e he
  rcases Prod.Lex.toLex_le_toLex.mp (of_decide_eq_true he) with h | ⟨h, _⟩
  · exact h.le.trans ht
  · exact h.le.trans ht

end AvailableChain.FGSA.Run
end
