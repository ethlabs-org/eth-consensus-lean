module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Replay
public import AvailableChainFGSAProofs.Proofs.Shared.Reads -- shake: keep (duty execution import route)

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E E' : Generic.Env V} {source rho : V2.D.Run V (fgsa p c)}

/-- Local signed event membership transfers in both directions. -/
theorem wcg_eventReplay (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (e : V2.Event V (fgsa p c).Object) (hx : e.node ∈ rho.honest)
    (ht : e.time ≤ source.horizon) : e ∈ rho.events ↔ e ∈ source.events := by
  have he := ha.events e.node hx
  have hm := congrArg (fun es => e ∈ es) he
  simpa only [List.mem_filter, decide_eq_true_eq, true_and, and_true,
    ht, and_self, eq_self_iff_true] using (Iff.of_eq hm)

/-- Strict reads agree, so matched local ticks have the same input state. -/
theorem wcg_beforeReplay (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (x : V) (hx : x ∈ rho.honest) {t : Time} (ht : t ≤ source.horizon) :
    rho.stateBeforeTime E' t x = source.stateBeforeTime E t x :=
  wcg_filtered_replay ha x hx _ (fun _ he => (le_of_lt (of_decide_eq_true he)).trans ht)

/-- A retained source tick has a continuation tick at its own global index.
The input states agree even when unrelated nodes change the global ordering. -/
theorem wcg_tickEventReplay (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    {j : Nat} {x : V} {t : Time} (hx : x ∈ rho.honest) (ht : t ≤ source.horizon)
    (hj : source.events[j]? = some (.tick x t)) :
    ∃ k, rho.events[k]? = some (.tick x t) ∧
      rho.stateBefore E' k x = source.stateBefore E j x := by
  have hm := (wcg_eventReplay ha (.tick x t) hx ht).mpr (List.mem_of_getElem? hj)
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
  refine ⟨k, hk, ?_⟩
  rw [V2.D.Engine.stateBefore_tick_eq_stateAfterRestartsAt hr hk,
    V2.D.Engine.stateBefore_tick_eq_stateAfterRestartsAt hs hj]
  let test := fun e : V2.Event V (fgsa p c).Object =>
    decide (e.time < t ∨ (e.time = t ∧ e.phase = 0))
  have down : ∀ e f, e.key ≤ f.key → test f = true → test e = true := by
    intro e f hk hf
    apply decide_eq_true
    have hf' : f.time < t ∨ (f.time = t ∧ f.phase = 0) := of_decide_eq_true hf
    have hk' := Prod.Lex.toLex_le_toLex.mp hk
    dsimp only [V2.Event.key] at hk'
    dsimp [Time] at *
    rcases hk' with h | ⟨h, hp⟩ <;> rcases hf' with ht | ⟨ht, hf⟩ <;> omega
  change ((rho.events.take (rho.events.filter test).length).foldl
    (V2.D.World.step E' rho) V2.D.World.init) x =
    ((source.events.take (source.events.filter test).length).foldl
      (V2.D.World.step E source) V2.D.World.init) x
  rw [← V2.D.Engine.filter_eq_take hr test down,
    ← V2.D.Engine.filter_eq_take hs test down]
  apply wcg_filtered_replay ha x hx test
  intro e he
  rcases of_decide_eq_true he with h | ⟨h, _⟩
  · exact h.le.trans ht
  · exact h.le.trans ht

/-- A retained tick in the continuation has its own source occurrence. -/
theorem wcg_tickSourceReplay (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    {k : Nat} {x : V} {t : Time} (hx : x ∈ rho.honest) (ht : t ≤ source.horizon)
    (hk : rho.events[k]? = some (.tick x t)) :
    ∃ j, source.events[j]? = some (.tick x t) ∧
      rho.stateBefore E' k x = source.stateBefore E j x := by
  have hm := (wcg_eventReplay ha (.tick x t) hx ht).mp (List.mem_of_getElem? hk)
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
  obtain ⟨l, hl, he⟩ := wcg_tickEventReplay ha hs hr hx ht hj
  have hlk := fgsa_tick_unique E' rho hr hl hk
  exact ⟨j, hj, hlk ▸ he⟩

/-- A confirmed public reader replays its current gate and local restart interval. -/
theorem wcg_confirmedReaderSourceReplay
    (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    {x : V} {t : Time} (ht : t ≤ source.horizon)
    (hx : confirmedReader p c E' rho x t) : confirmedReader p c E source x t := by
  have hst : storeAt p c E' rho (timeIdx rho t) x =
      storeAt p c E source (timeIdx source t) x := by
    have he := wcg_readReplay ha x hx.1 ht
    rw [V2.D.Engine.readAt_eq_stateBefore hr t,
      V2.D.Engine.readAt_eq_stateBefore hs t] at he
    exact congrArg (fun nd => nd.st) he
  refine ⟨ha.honest hx.1, ?_⟩
  obtain ⟨hAw, hC⟩ := hx.2
  refine ⟨(ha.awake x hx.1 t ht).symm.trans hAw, ?_⟩
  rw [hst] at hC
  cases hw : (storeAt p c E source (timeIdx source t) x).restartTime with
  | none => trivial
  | some w =>
    rw [hw] at hC
    obtain ⟨s, k, hw, hgt, _hki, hG, hA, hR⟩ := hC
    obtain ⟨j, hj, he⟩ := wcg_tickSourceReplay ha hs hr hx.1 (hgt.trans ht) hG.1
    refine ⟨s, j, hw, hgt,
      (V2.D.Engine.index_lt_read_length_iff hs t hj).mpr hgt, ⟨hj, ?_⟩, ?_, ?_⟩
    · change (match (storeAt p c E source j x).restartTime with
        | none => True | some w => w ≤ slotStartZ p (s : Int))
      have hg := hG.2
      change (match (storeAt p c E' rho k x).restartTime with
        | none => True | some w => w ≤ slotStartZ p (s : Int)) at hg
      have heSt := congrArg (fun nd => nd.st) he.symm
      change storeAt p c E source j x = storeAt p c E' rho k x at heSt
      rwa [heSt]
    · intro u hu hau hut
      exact (ha.awake x hx.1 u (hut.trans ht)).symm.trans (hA u hu hau hut)
    · intro u hau hut hm
      exact hR u hau hut
        ((wcg_eventReplay ha (.restart x u) hx.1 (hut.trans ht)).mpr hm)

/-- Every public getter replays through the inclusive source endpoint. -/
theorem wcg_outputReplay (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (g : V2.D.Output (fgsa p c)) (x : V) (hx : x ∈ rho.honest)
    {t : Time} (ht : t ≤ source.horizon) :
    V2.D.outputAt E' rho g x t = V2.D.outputAt E source g x t :=
  congrArg g (wcg_readReplay ha x hx ht)

/-- Empty-suffix public output safety needs no participation or half cap.
This transfers compatibility and monotonicity at all covered public reads.
The event-index safety fields require a separate occurrence-index argument. -/
theorem wcg_empty_outputs
    (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hsch : V2.D.ScheduleWellFormed E source)
    (hrho : V2.D.ScheduleWellFormed E' rho)
    (hend : rho.horizon = source.horizon)
    {u : Slot} {Q : Block} {iSource : Nat} {ΔF : Time}
    (hcut : iSource = afterTicksIdx source (SA.gateTime p.toParams u))
    (hsafe : SSafeFromCut₂ p c E source iSource Q ΔF) :
    ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      ScopedCompat (confirmedReader p c E' rho) (fun t x => V2.D.outputAt E' rho g x t)
        (fun t => SA.gateTime p.toParams u ≤ t ∧ t ≤ rho.horizon) ∧
      ScopedMono (confirmedReader p c E' rho) (fun t x => V2.D.outputAt E' rho g x t)
        (fun t => SA.gateTime p.toParams u ≤ t ∧ t ≤ rho.horizon) := by
  have hidx : ∀ t, SA.gateTime p.toParams u ≤ t → iSource ≤ timeIdx source t := by
    intro t ht
    rw [hcut]
    exact (preIdx_le_afterTicksIdx E source hsch _).2.trans
      (V2.D.Engine.read_length_mono (rho := source) _ t ht)
  intro g hg
  obtain ⟨hc, hm⟩ := hsafe.outputs g hg
  constructor
  · intro t r x y ht hr hx hy
    change Block.Compatible (V2.D.outputAt E' rho g x t) (V2.D.outputAt E' rho g y r)
    rw [wcg_outputReplay ha g x hx.1 (ht.2.trans_eq hend),
      wcg_outputReplay ha g y hy.1 (hr.2.trans_eq hend)]
    exact hc t r x y (hidx t ht.1) (hidx r hr.1)
      (wcg_confirmedReaderSourceReplay ha hsch hrho (ht.2.trans_eq hend) hx)
      (wcg_confirmedReaderSourceReplay ha hsch hrho (hr.2.trans_eq hend) hy)
  · intro t r x ht hr htr hx hxR
    change Block.Preceq (V2.D.outputAt E' rho g x t) (V2.D.outputAt E' rho g x r)
    rw [wcg_outputReplay ha g x hx.1 (ht.2.trans_eq hend),
      wcg_outputReplay ha g x hx.1 (hr.2.trans_eq hend)]
    exact hm t r x (hidx t ht.1) (hidx r hr.1) htr
      (wcg_confirmedReaderSourceReplay ha hsch hrho (ht.2.trans_eq hend) hx)
      (wcg_confirmedReaderSourceReplay ha hsch hrho (hr.2.trans_eq hend) hxR)

end AvailableChain.FGSA.Run
end
