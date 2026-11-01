module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Seed
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Epoch
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthReads
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthProposal
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthCausal

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E E' : Generic.Env V} {source rho : V2.D.Run V (fgsa p c)}

/-- Public reads after the horizon equal the endpoint read. -/
theorem wcg_readAt_clamp (hs : V2.D.ScheduleWellFormed E rho) (t : Time) :
    rho.readAt E t = rho.readAt E (min t rho.horizon) := by
  change (rho.events.filter _).foldl _ _ = (rho.events.filter _).foldl _ _
  congr 1
  apply List.filter_congr
  intro e he
  have ht := (hs.in_horizon e he).2
  simp only [le_min_iff, ht, and_true]

/-- Empty-suffix getter replay covers every public time, including times
past the horizon. -/
theorem wcg_empty_outputReplay (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    (hend : rho.horizon = source.horizon)
    (g : V2.D.Output (fgsa p c)) (x : V) (hx : x ∈ rho.honest) (t : Time) :
    V2.D.outputAt E' rho g x t = V2.D.outputAt E source g x t := by
  change g (rho.readAt E' t x) = g (source.readAt E t x)
  rw [wcg_readAt_clamp hr t, wcg_readAt_clamp hs t, hend]
  exact congrArg g (wcg_readReplay ha x hx (min_le_right _ _))

omit [DecidableEq V] in
/-- A cut containing a tick cannot precede a public read before that tick. -/
theorem wcg_cut_read_time (hr : V2.D.ScheduleWellFormed E' rho)
    {k : Nat} {x : V} {d t : Time} (hk : rho.events[k]? = some (.tick x d))
    (hi : afterTicksIdx rho d ≤ timeIdx rho t) : d ≤ t := by
  have hki := (wcg_tick_before_cut hr hk le_rfl).trans_le hi
  have hm : (.tick x d : V2.Event V (fgsa p c).Object) ∈
      rho.events.filter (fun e => decide (e.time ≤ t)) := by
    rw [V2.D.Engine.filter_eq_take hr _ (by
      intro e f hkey hf
      exact decide_eq_true ((V2.D.Engine.time_le_of_key_le e f hkey).trans
        (of_decide_eq_true hf)))]
    apply List.mem_of_getElem? (i := k)
    change (rho.events.take (timeIdx rho t))[k]? = _
    rw [List.getElem?_take_of_lt hki]
    exact hk
  exact of_decide_eq_true (List.mem_filter.mp hm).2

/-- Compatibility and monotonicity transfer on the exact public output domain.
A retained seed tick supplies the lower time bound for each honest reader. -/
theorem wcg_empty_outputDomain
    (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    (hend : rho.horizon = source.horizon)
    {w : HealingWitness} {iSource : Nat}
    (hseed : WCSeed p c E source w iSource)
    (hgate : SA.gateTime p.toParams w.u ≤ source.horizon)
    (hsafe : WCCachedSafety p c E source iSource w.QStar) :
    ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      Gen.Pure.CompatOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E' rho g x t)
        (fun t => afterTicksIdx rho (SA.gateTime p.toParams w.u) ≤ timeIdx rho t) ∧
      Gen.Pure.MonoOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E' rho g x t)
        (fun t => afterTicksIdx rho (SA.gateTime p.toParams w.u) ≤ timeIdx rho t) := by
  have hidx : ∀ x ∈ rho.honest, ∀ t,
      afterTicksIdx rho (SA.gateTime p.toParams w.u) ≤ timeIdx rho t →
      iSource ≤ timeIdx source t := by
    intro x hx t ht
    obtain ⟨j, _, hj, _⟩ := hseed.gates x (ha.honest hx)
    obtain ⟨k, hk, _⟩ := wcg_tickEventReplay ha hs hr hx hgate hj
    have hdt := wcg_cut_read_time hr hk ht
    rw [hseed.cut]
    exact (preIdx_le_afterTicksIdx E source hs _).2.trans
      (V2.D.Engine.read_length_mono _ _ hdt)
  intro g hg
  obtain ⟨hc, hm⟩ := hsafe.outputs g hg
  constructor
  · intro t r x y ht hrt hx hy
    change Block.Compatible (V2.D.outputAt E' rho g x t) (V2.D.outputAt E' rho g y r)
    rw [wcg_empty_outputReplay ha hs hr hend g x hx,
      wcg_empty_outputReplay ha hs hr hend g y hy]
    exact hc t r x y (hidx x hx t ht) (hidx y hy r hrt) (ha.honest hx) (ha.honest hy)
  · intro t r x ht hrt htr hx
    change Block.Preceq (V2.D.outputAt E' rho g x t) (V2.D.outputAt E' rho g x r)
    rw [wcg_empty_outputReplay ha hs hr hend g x hx,
      wcg_empty_outputReplay ha hs hr hend g x hx]
    exact hm t r x (hidx x hx t ht) (hidx x hx r hrt) htr (ha.honest hx)

/-- A retained honest proposal has the same proposer, wire, and block in source. -/
theorem wcg_proposalSourceReplay
    (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    {s : Slot} {B : Block}
    (hp : HonestProposal E' rho (fgsaInterface p c) s B)
    (ht : V2.D.proposalTime (fgsaInterface p c) s ≤ source.horizon) :
    HonestProposal E source (fgsaInterface p c) s B := by
  have hproposer : V2.D.proposerOf rho (fgsaInterface p c) s =
      V2.D.proposerOf source (fgsaInterface p c) s := by
    change rho.seatOf _ _ = source.seatOf _ _
    rw [ha.seats]
  obtain ⟨hh, o, ⟨k, hk, ho⟩, hb⟩ := hp
  have hx : V2.D.proposerOf rho (fgsaInterface p c) s ∈ rho.honest := hh.2
  obtain ⟨j, hj, he⟩ := wcg_tickSourceReplay ha hs hr hx ht hk
  refine ⟨?_, o, ?_, hb⟩
  · rw [Gen.V2.Duty.HonestSlot_def]
    exact ⟨hh.1, hproposer ▸ ha.honest hx⟩
  · rw [(V2.D.Run.step_tick_eq E' rho hk).2, he,
      wcg_tick_retained ha _ hx _ _ ht] at ho
    have hem : o ∈ source.emitsAt E j := by
      rwa [(V2.D.Run.step_tick_eq E source hj).2]
    exact ⟨j, hproposer ▸ hj, hem⟩

/-- Empty-suffix proposal inclusion transfers through the inclusive endpoint. -/
theorem wcg_empty_inclusion
    (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    (hend : rho.horizon = source.horizon)
    {u : Slot} {Q : Block} {iSource : Nat} {ΔF : Time}
    (hgate : SA.gateTime p.toParams u ≤ source.horizon)
    (hlive : WeakContinuationLiveAt₂ p c E source u Q iSource ΔF) :
    ∀ pt : PtSP, u + 2 ≤ pt.s →
      HonestProposal E' rho (fgsaInterface p c) pt.s pt.P →
      SA.gateTime p.toParams pt.s ≤ rho.horizon → ServedFromGateAt p c E' rho pt := by
  intro pt hslot hprop hcovered
  have htime : V2.D.proposalTime (fgsaInterface p c) pt.s ≤ source.horizon := by
    have hcovered' := hcovered.trans_eq hend
    change 4 * p.Δ * (pt.s : Time) ≤ source.horizon
    change 4 * p.Δ * (pt.s : Time) + 6 * p.Δ ≤ source.horizon at hcovered'
    nlinarith [p.deltaPos]
  have hi := hlive.inclusion hgate pt hslot
    (wcg_proposalSourceReplay ha hs hr hprop htime) (hcovered.trans_eq hend)
  intro g hg t x ht hx
  change Block.Preceq pt.P (V2.D.outputAt E' rho g x t)
  rw [wcg_empty_outputReplay ha hs hr hend g x hx.1]
  exact hi g hg t x ⟨ht.1, ht.2.trans_eq hend⟩
    (wcg_confirmedReaderSourceReplay ha hs hr (ht.2.trans_eq hend) hx)

/-- Conditional growth uses only public output order and proposal inclusion.
It does not require event-index finalBelow or a continuation fault cap. -/
theorem wcg_growthOfOutputs (hb : Base₂ p c E' rho) (u : Slot)
    (_hout : ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      Gen.Pure.CompatOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E' rho g x t)
        (fun t => SA.gateTime p.toParams u ≤ t) ∧
      Gen.Pure.MonoOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E' rho g x t)
        (fun t => SA.gateTime p.toParams u ≤ t))
    (hincl : ∀ pt : PtSP, u + 2 ≤ pt.s →
      HonestProposal E' rho (fgsaInterface p c) pt.s pt.P →
      SA.gateTime p.toParams pt.s ≤ rho.horizon → ServedFromGateAt p c E' rho pt)
    (hproposals : ∀ pt : PtSP, u + 2 ≤ pt.s →
      HonestProposal E' rho (fgsaInterface p c) pt.s pt.P →
      SA.gateTime p.toParams pt.s ≤ rho.horizon →
      ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed], ∀ t x,
      SA.gateTime p.toParams u ≤ t → t ≤ rho.horizon →
      confirmedReader p c E' rho x t →
      Block.Compatible (V2.D.outputAt E' rho g x t) pt.P)
    (G' : Time) (hG' : 4 * p.Δ ≤ G')
    (hrecurrence : AwakeProposerRecurrenceFrom p c E' rho (SA.gateTime p.toParams u) G')
    (t : Time) (ht : SA.gateTime p.toParams u ≤ t)
    (hdeadline : t + G' + 6 * p.Δ ≤ rho.horizon) :
    JointGrowthAt p c E' rho t (t + G' + 6 * p.Δ) := by
  have hd := p.deltaPos
  have h6 : 0 ≤ 6 * p.Δ := mul_nonneg (by decide) hd.le
  have hgap : 0 ≤ G' := (mul_nonneg (by decide : (0 : Time) ≤ 4) hd.le).trans hG'
  have hwindow : t + G' ≤ rho.horizon :=
    (le_add_of_nonneg_right h6).trans hdeadline
  have htD : t ≤ t + G' + 6 * p.Δ :=
    (le_add_of_nonneg_right hgap).trans (le_add_of_nonneg_right h6)
  obtain ⟨s, hfuture, hupper, hh, ha⟩ := hrecurrence t ht hwindow
  have hs := hb.valid.toScheduleWellFormed
  obtain ⟨B, hprop, hslot⟩ := fgsa_honestProposal_exists_of_awake_slot E' rho hs
    hb.delta hh ha.1 ha.2.2 (hupper.trans hwindow)
  have hstart : u + 2 ≤ s := by
    by_contra h
    have hsu : s ≤ u + 1 := by
      simp only [Slot] at h ⊢
      omega
    have hcast : (s : Time) ≤ (u : Time) + 1 := by exact_mod_cast hsu
    have hscaled := mul_le_mul_of_nonneg_left hcast
      (mul_nonneg (by decide : (0 : Time) ≤ 4) hd.le)
    change 4 * p.Δ * (u : Time) + 6 * p.Δ ≤ t at ht
    change t < 4 * p.Δ * (s : Time) at hfuture
    nlinarith
  have hgate : SA.gateTime p.toParams s ≤ t + G' + 6 * p.Δ := by
    change 4 * p.Δ * (s : Time) + 6 * p.Δ ≤ t + G' + 6 * p.Δ
    change 4 * p.Δ * (s : Time) ≤ t + G' at hupper
    simpa only [add_comm] using add_le_add_left hupper (6 * p.Δ)
  have htzero : 0 ≤ t := by
    change 4 * p.Δ * (u : Time) + 6 * p.Δ ≤ t at ht
    exact (add_nonneg
      (mul_nonneg (mul_nonneg (by decide) hd.le) (Nat.cast_nonneg u)) h6).trans ht
  have hserved := hincl ⟨s, B⟩ hstart hprop (hgate.trans hdeadline)
  refine ⟨s, B, hfuture, hprop, ?_⟩
  intro g hg
  refine ⟨?_, fun x hx => hserved g hg _ x ⟨hgate, hdeadline⟩ hx⟩
  intro x hx
  have hc := hproposals ⟨s, B⟩ hstart hprop (hgate.trans hdeadline) g hg t x ht
    (htD.trans hdeadline) hx
  have hn := fgsa_output_noFuture_of_slot E' rho hs htzero hfuture hslot.ge g hg x
  have hb : Block.Preceq (V2.D.outputAt E' rho g x t) B :=
    (Bool.or_eq_true_iff.mp hc).resolve_right hn
  have hne : V2.D.outputAt E' rho g x t ≠ B := by
    intro he; exact hn (he ▸ Gen.Pure.block_preceq_refl B)
  change (!decide (_ = B) && Block.preceq _ B) = true
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  exact ⟨hne, hb⟩

end AvailableChain.FGSA.Run

namespace AvailableChain.FGSA.Run
open SimplexFG KitFG
variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E E' : Generic.Env V} {source rho : V2.D.Run V (fgsa p c)}
private def localStep (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (st : (fgsa p c).State) : V2.Event V (fgsa p c).Object → (fgsa p c).State
  | .restart v t => if v = x then (fgsa p c).restore ((fgsa p c).durable st) t else st
  | .tick v t => if v = x then (V2.D.tick E rho st v t).1 else st
  | .deliver v o _ => if v = x then (fgsa p c).process st o else st

private theorem step_local (world : V2.D.World V (fgsa p c)) (x : V)
    (e : V2.Event V (fgsa p c).Object) :
    V2.D.World.step E rho world e x = localStep E rho x (world x) e := by
  cases e with
  | restart v t =>
    change Function.update world v _ x = if v = x then _ else _
    by_cases h : v = x
    · subst v; simp
    · rw [ite_eq_right h, Function.update_of_ne (Ne.symm h)]
  | tick v t =>
    change Function.update world v _ x = if v = x then _ else _
    by_cases h : v = x
    · subst v; simp
    · rw [ite_eq_right h, Function.update_of_ne (Ne.symm h)]
  | deliver v o t =>
    change Function.update world v _ x = if v = x then _ else _
    by_cases h : v = x
    · subst v; simp
    · rw [ite_eq_right h, Function.update_of_ne (Ne.symm h)]

private theorem fold_local (events : List (V2.Event V (fgsa p c).Object))
    (world : V2.D.World V (fgsa p c)) (x : V) :
    (events.foldl (V2.D.World.step E rho) world) x =
      events.foldl (localStep E rho x) (world x) := by
  induction events generalizing world with
  | nil => rfl
  | cons e es ih =>
    change (es.foldl _ (V2.D.World.step E rho world e)) x = es.foldl _ _
    rw [ih, step_local]

private theorem localStep_other (x : V) (st : (fgsa p c).State)
    (e : V2.Event V (fgsa p c).Object) (h : e.node ≠ x) :
    localStep E rho x st e = st := by
  cases e with
  | restart v t => exact ite_eq_right h
  | tick v t => exact ite_eq_right h
  | deliver v o t => exact ite_eq_right h

private theorem fold_filter_local (events : List (V2.Event V (fgsa p c).Object))
    (st : (fgsa p c).State) (x : V) :
    events.foldl (localStep E rho x) st =
      (events.filter (fun e => decide (e.node = x))).foldl (localStep E rho x) st := by
  induction events generalizing st with
  | nil => rfl
  | cons e es ih =>
    by_cases h : e.node = x
    · simp only [List.foldl_cons, List.filter_cons, h, decide_true,
        ite_true]
      exact ih _
    · simp only [List.foldl_cons, List.filter_cons, h, decide_false, Bool.false_eq_true,
        ite_false]
      rw [localStep_other x st e h]
      exact ih _


private theorem filter_prefix_extend {α : Type} (q : α → Bool) {xs ys : List α}
    {a b i : Nat} (hfull : xs.filter q = ys.filter q)
    (hbase : (xs.take a).filter q = (ys.take b).filter q)
    (hai : a ≤ i) (hb : b ≤ ys.length) :
    ∃ j, b ≤ j ∧ j ≤ ys.length ∧ (xs.take i).filter q = (ys.take j).filter q := by
  have hp : (xs.take i).filter q <+: ys.filter q := by
    rw [← hfull]
    exact (List.take_prefix i xs).filter q
  obtain ⟨ls, hl, he⟩ := List.prefix_filter_iff.mp hp
  have hls := List.prefix_iff_eq_take.mp hl
  rw [hls] at he
  by_cases hbj : b ≤ ls.length
  · exact ⟨ls.length, hbj, hl.length_le, he⟩
  · refine ⟨b, le_rfl, hb, ?_⟩
    have hleft : (ys.take b).filter q <+: (xs.take i).filter q := by
      rw [← hbase]
      exact (List.take_prefix_take_left hai).filter q
    have hright : (xs.take i).filter q <+: (ys.take b).filter q := by
      rw [he]
      exact (List.take_prefix_take_left (Nat.le_of_not_ge hbj)).filter q
    exact hright.eq_of_length_le hleft.length_le

/-- Replay arbitrary local event prefixes, with no equality of global indices. -/
theorem wcg_localPrefixReplay (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hr : V2.D.ScheduleWellFormed E' rho) (hend : rho.horizon ≤ source.horizon)
    {i j : Nat} (x : V) (hx : x ∈ rho.honest)
    (he : (rho.events.take i).filter (fun e => decide (e.node = x)) =
      (source.events.take j).filter (fun e => decide (e.node = x))) :
    rho.stateBefore E' i x = source.stateBefore E j x := by
  change ((rho.events.take i).foldl (V2.D.World.step E' rho) V2.D.World.init) x =
    ((source.events.take j).foldl (V2.D.World.step E source) V2.D.World.init) x
  simp only [fold_local]
  rw [fold_filter_local (E := E') (rho := rho), fold_filter_local (E := E) (rho := source)]
  rw [← he]
  apply List.foldl_ext
  intro st e hm
  have hx' := of_decide_eq_true (List.mem_filter.mp hm).2
  have ht := ((hr.in_horizon e (List.mem_of_mem_take (List.mem_filter.mp hm).1)).2).trans hend
  cases e with
  | restart v t => rfl
  | deliver v o t => rfl
  | tick v t =>
    change v = x at hx'
    subst v
    change (if x = x then (V2.D.tick E' rho st x t).1 else st) =
      (if x = x then (V2.D.tick E source st x t).1 else st)
    rw [ite_eq_left rfl, ite_eq_left rfl, wcg_tick_retained ha x hx st t ht]

private theorem full_local (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    (hend : rho.horizon = source.horizon) (x : V) (hx : x ∈ rho.honest) :
    rho.events.filter (fun e => decide (e.node = x)) =
      source.events.filter (fun e => decide (e.node = x)) := by
  have he := ha.events x hx
  have norm (es : List (V2.Event V (fgsa p c).Object))
      (ht : ∀ e ∈ es, e.time ≤ source.horizon) :
      es.filter (fun e => decide (e.node = x ∧ e.time ≤ source.horizon)) =
        es.filter (fun e => decide (e.node = x)) := by
    apply List.filter_congr
    intro e hm
    simp only [ht e hm, and_true]
  rw [norm rho.events (fun e hm => (hr.in_horizon e hm).2.trans_eq hend),
    norm source.events (fun e hm => (hs.in_horizon e hm).2)] at he
  exact he

private theorem cut_local (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    (hend : rho.horizon = source.horizon) (x : V) (hx : x ∈ rho.honest) (d : Time) :
    (rho.events.take (afterTicksIdx rho d)).filter (fun e => decide (e.node = x)) =
      (source.events.take (afterTicksIdx source d)).filter (fun e => decide (e.node = x)) := by
  have hdown : ∀ e f : V2.Event V (fgsa p c).Object, e.key ≤ f.key →
      cutPred d f = true → cutPred d e = true := by
    intro e f h hf
    exact decide_eq_true (h.trans (of_decide_eq_true hf))
  have er : rho.events.filter (cutPred d) = rho.events.take (afterTicksIdx rho d) :=
    V2.D.Engine.filter_eq_take hr _ hdown
  have es : source.events.filter (cutPred d) = source.events.take (afterTicksIdx source d) :=
    V2.D.Engine.filter_eq_take hs _ hdown
  rw [← er, ← es]
  have he := congrArg (List.filter (cutPred d)) (full_local ha hs hr hend x hx)
  simpa only [List.filter_filter, Bool.and_comm] using he

/-- A later continuation state has a later matching source state at each reader. -/
theorem wcg_empty_stateMap (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    (hend : rho.horizon = source.horizon) (x : V) (hx : x ∈ rho.honest)
    {a b i : Nat} (hbase : (rho.events.take a).filter (fun e => decide (e.node = x)) =
      (source.events.take b).filter (fun e => decide (e.node = x)))
    (hai : a ≤ i) (hb : b ≤ source.events.length) :
    ∃ j, b ≤ j ∧ j ≤ source.events.length ∧
      (rho.events.take i).filter (fun e => decide (e.node = x)) =
        (source.events.take j).filter (fun e => decide (e.node = x)) ∧
      rho.stateBefore E' i x = source.stateBefore E j x := by
  obtain ⟨j, hj, hjlen, he⟩ := filter_prefix_extend _
    (full_local ha hs hr hend x hx) hbase hai hb
  exact ⟨j, hj, hjlen, he, wcg_localPrefixReplay ha hr hend.le x hx he⟩


/-- The least matching source prefix bounds every earlier source event time
by a retained event in the continuation prefix. -/
theorem wcg_empty_stateMap_timed (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    (hend : rho.horizon = source.horizon) (x : V) (hx : x ∈ rho.honest)
    {d : Time} {i : Nat} (hi : afterTicksIdx rho d ≤ i) :
    ∃ j, afterTicksIdx source d ≤ j ∧ j ≤ source.events.length ∧
      rho.stateBefore E' i x = source.stateBefore E j x ∧
      (rho.events.take i).filter (fun e => decide (e.node = x)) =
        (source.events.take j).filter (fun e => decide (e.node = x)) ∧
      ∀ k e, k < j → source.events[k]? = some e → d < e.time →
        ∃ f ∈ rho.events.take i, e.time ≤ f.time := by
  classical
  let q := fun e : V2.Event V (fgsa p c).Object => decide (e.node = x)
  let P := fun j => afterTicksIdx source d ≤ j ∧ j ≤ source.events.length ∧
    (rho.events.take i).filter q = (source.events.take j).filter q
  have hex : ∃ j, P j := by
    obtain ⟨j, hj, hlen, he, _⟩ := wcg_empty_stateMap ha hs hr hend x hx
      (cut_local ha hs hr hend x hx d) hi (List.length_filter_le _ _)
    exact ⟨j, hj, hlen, he⟩
  let j := Nat.find hex
  have hj : P j := Nat.find_spec hex
  refine ⟨j, hj.1, hj.2.1, wcg_localPrefixReplay ha hr hend.le x hx hj.2.2, hj.2.2, ?_⟩
  intro k e hk he htime
  have hjgt : afterTicksIdx source d < j := by
    by_contra hn
    have hkj : k < afterTicksIdx source d := by omega
    exact (not_lt.mpr (wcg_time_before_cut hs he hkj)) htime
  have hjpos : 0 < j := lt_of_le_of_lt (Nat.zero_le _) hjgt
  have hlastlen : j - 1 < source.events.length := by omega
  let f := source.events[j - 1]
  have hf : source.events[j - 1]? = some f := List.getElem?_eq_getElem hlastlen
  have htake : source.events.take j = source.events.take (j - 1) ++ [f] := by
    have h := List.take_add_one (l := source.events) (i := j - 1)
    rw [hf] at h
    simpa only [Nat.sub_add_cancel hjpos, Option.toList_some] using h
  have hnode : f.node = x := by
    by_contra hn
    have hP : P (j - 1) := by
      refine ⟨by omega, by omega, ?_⟩
      have heq := hj.2.2
      rw [htake, List.filter_append] at heq
      simpa only [q, List.filter_cons, hn, decide_false, Bool.false_eq_true,
        ite_false, List.filter_nil, List.append_nil] using heq
    have hmin : j ≤ j - 1 := Nat.find_min' hex hP
    omega
  have hmem : f ∈ (source.events.take j).filter q := by
    apply List.mem_filter.mpr
    refine ⟨?_, decide_eq_true hnode⟩
    rw [htake]
    exact List.mem_append_right _ (List.mem_singleton_self f)
  rw [← hj.2.2] at hmem
  refine ⟨f, (List.mem_filter.mp hmem).1, ?_⟩
  by_cases hke : k = j - 1
  · have heq := he.symm.trans (hke ▸ hf)
    exact (congrArg V2.Event.time (Option.some.inj heq)).le
  · obtain ⟨hklen, hkeq⟩ := List.getElem?_eq_some_iff.mp he
    have hkey := (List.pairwise_iff_getElem.mp hs.sorted) k (j - 1) hklen hlastlen (by omega)
    rw [hkeq] at hkey
    exact V2.D.Engine.time_le_of_key_le _ _ hkey

omit [DecidableEq V] in
/-- A covered prefix event strictly after D puts the completed D cut before
that prefix index. -/
theorem wcg_cut_before_prefix_event (hr : V2.D.ScheduleWellFormed E' rho)
    {i : Nat} {f : V2.Event V (fgsa p c).Object} {D : Time}
    (hf : f ∈ rho.events.take i) (ht : D < f.time) : afterTicksIdx rho D ≤ i := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hf
  have hki : k < i := lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hk).1 (List.length_take_le _ _)
  have he : rho.events[k]? = some f := by rwa [List.getElem?_take_of_lt hki] at hk
  by_contra hn
  have hkc : k < afterTicksIdx rho D := hki.trans (Nat.lt_of_not_ge hn)
  exact (not_lt.mpr (wcg_time_before_cut hr he hkc)) ht

/-- A local prefix match preserves a confirmed reader at the earlier source time. -/
theorem wcg_empty_readerReplay
    (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    (hend : rho.horizon = source.horizon) {i j : Nat} {x : V}
    (_hi : i ≤ rho.events.length) (hj : j ≤ source.events.length)
    (hx : confirmedReaderIdx p c E' rho x i)
    (hl : (rho.events.take i).filter (fun e => decide (e.node = x)) =
      (source.events.take j).filter (fun e => decide (e.node = x)))
    (he : rho.stateBefore E' i x = source.stateBefore E j x)
    (ht : prefixTime source j ≤ prefixTime rho i) :
    confirmedReaderIdx p c E source x j := by
  have bounds (r : V2.D.Run V (fgsa p c)) (F : Generic.Env V)
      (h : V2.D.ScheduleWellFormed F r) (k : Nat) :
      0 ≤ prefixTime r k ∧ prefixTime r k ≤ r.horizon := by
    unfold prefixTime
    cases hf : (r.events.take k).getLast? with
    | none => simpa only [Option.map_none, Option.getD_none] using ⟨le_rfl, h.horizon_nonneg⟩
    | some e =>
      have hm := List.mem_of_getLast? hf
      simpa only [Option.map_some, Option.getD_some] using
        h.in_horizon e ((List.take_sublist _ _).subset hm)
  have htr := (bounds rho E' hr i).2
  have hts := bounds source E hs j
  have local_before (e : V2.Event V (fgsa p c).Object) (hn : e.node = x)
      (hm : e ∈ rho.events.take i) : ∃ k < j, source.events[k]? = some e := by
    have hf : e ∈ (source.events.take j).filter (fun e => decide (e.node = x)) := by
      rw [← hl]
      exact List.mem_filter.mpr ⟨hm, decide_eq_true hn⟩
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp (List.mem_filter.mp hf).1
    have hkj := lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hk).1
      (List.length_take_le _ _)
    exact ⟨k, hkj, by rwa [List.getElem?_take_of_lt hkj] at hk⟩
  have hW : WakesAppliedAtIdx E source x j (prefixTime source j) := by
    intro u hu0 hut hu
    have hwr : V2.D.Wakes E' x u := by
      exact ⟨(ha.awake x hx.1.1 u (hut.trans hts.2)).trans hu.1,
        (ha.awake x hx.1.1 (u - 1) (by
          have hh := hut.trans hts.2
          simp only [Time] at hh ⊢
          omega)).trans hu.2⟩
    obtain ⟨k, hki, hk⟩ := hx.2 u hu0 (hut.trans ht) hwr
    exact local_before (.restart x u) rfl
      (List.mem_of_getElem? (by rwa [List.getElem?_take_of_lt hki]))
  have hst : (storeAt p c E' rho i x).restartTime =
      (storeAt p c E source j x).restartTime :=
    congrArg (fun nd : Node p => nd.st.restartTime) he
  have hcatch := hx.1.2.2
  change (match (storeAt p c E' rho i x).restartTime with
    | none => True | some w => _) at hcatch
  rw [hst] at hcatch
  have hreader : confirmedReaderAtIdx p c E source x j (prefixTime source j) := by
    refine ⟨ha.honest hx.1.1, ?_⟩
    cases hw : (storeAt p c E source j x).restartTime with
    | none =>
      refine ⟨?_, by rw [hw]; trivial⟩
      by_contra hn
      have hn' : E'.awake x (prefixTime source j) = false := by
        rw [ha.awake x hx.1.1 _ hts.2]
        exact Bool.eq_false_iff.mpr hn
      obtain ⟨u, hju, hui, hu⟩ := V2.D.Engine.wake_between ht hn' hx.1.2.1
      obtain ⟨k, hki, hk⟩ := hx.2 u (hts.1.trans_lt hju) hui hu
      obtain ⟨l, hlj, hl⟩ := local_before (.restart x u) rfl
        (List.mem_of_getElem? (by rwa [List.getElem?_take_of_lt hki]))
      obtain ⟨w, hw', _⟩ := fgsa_restartTime_ge E source hs hl hlj
      change (storeAt p c E source j x).restartTime = some w at hw'
      rw [hw] at hw'
      cases hw'
    | some w =>
      rw [hw] at hcatch
      obtain ⟨s, k, hws, hgt, hki, hG, hA, hR⟩ := hcatch
      obtain ⟨l, hlj, hle⟩ := local_before (.tick x (SA.gateTime p.toParams s)) rfl
        (List.mem_of_getElem? (by
          rw [List.getElem?_take_of_lt hki]
          exact hG.1))
      have hgl := wcg_event_before_prefixTime hs hj hlj hle
      obtain ⟨q, hq, heq⟩ := wcg_tickSourceReplay ha hs hr hx.1.1
        (hgt.trans htr |>.trans_eq hend) hG.1
      have hql : q = l := fgsa_tick_unique E source hs hq hle
      subst q
      have hGs : enabledGateAt p c E source l x s := by
        refine ⟨hle, ?_⟩
        have hh : (storeAt p c E' rho k x).restartTime =
            (storeAt p c E source l x).restartTime :=
          congrArg (fun nd : Node p => nd.st.restartTime) heq
        change (match (storeAt p c E source l x).restartTime with
          | none => True | some w => w ≤ slotStartZ p (s : Int))
        rw [← hh]
        exact hG.2
      have hAw : E.awake x (prefixTime source j) = true :=
        (ha.awake x hx.1.1 _ hts.2).symm.trans (hA _ hts.1
          (by exact (show slotStartZ p (s : Int) ≤ SA.gateTime p.toParams s by
            change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
            linarith [p.deltaPos]).trans hgl) ht)
      refine ⟨hAw, ?_⟩
      rw [hw]
      refine ⟨s, l, hws, hgl, hlj, hGs, ?_, ?_⟩
      · intro u hu0 hsu huj
        exact (ha.awake x hx.1.1 u (huj.trans hts.2)).symm.trans
          (hA u hu0 hsu (huj.trans ht))
      · intro u hsu huj hm
        exact hR u hsu (huj.trans ht)
          ((wcg_eventReplay ha (.restart x u) hx.1.1 (huj.trans hts.2)).mpr hm)
  exact ⟨hreader, hW⟩

/-- Event-index S compatibility, monotonicity, and seed preservation transfer.
Finality service at two different local source indices is a separate fact. -/
theorem wcg_empty_stateSafety
    (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    (hend : rho.horizon = source.horizon)
    {d : Time} {Q : Block}
    (hsafe : WCCachedSafety p c E source (afterTicksIdx source d) Q) :
    Gen.Pure.CompatOn (· ∈ rho.honest) (S_at p c E' rho)
      (fun i => afterTicksIdx rho d ≤ i ∧ i ≤ rho.events.length) ∧
    Gen.Pure.MonoOn (· ∈ rho.honest) (S_at p c E' rho)
      (fun i => afterTicksIdx rho d ≤ i ∧ i ≤ rho.events.length) ∧
    Gen.Pure.ServedOn (· ∈ rho.honest) (S_at p c E' rho) Q
      (fun i => afterTicksIdx rho d ≤ i ∧ i ≤ rho.events.length) := by
  have hmap : ∀ x ∈ rho.honest, ∀ i, afterTicksIdx rho d ≤ i →
      ∃ j, afterTicksIdx source d ≤ j ∧ j ≤ source.events.length ∧
        (rho.events.take i).filter (fun e => decide (e.node = x)) =
          (source.events.take j).filter (fun e => decide (e.node = x)) ∧
        rho.stateBefore E' i x = source.stateBefore E j x := by
    intro x hx i hi
    exact wcg_empty_stateMap ha hs hr hend x hx (cut_local ha hs hr hend x hx d)
      hi (List.length_filter_le _ _)
  refine ⟨?_, ?_, ?_⟩
  · intro i k x y hi hk hx hy
    obtain ⟨j, hj, hjlen, _, he⟩ := hmap x hx i hi.1
    obtain ⟨l, hl, hllen, _, hf⟩ := hmap y hy k hk.1
    change Block.Compatible (rho.stateBefore E' i x).st.base.stableRecord
      (rho.stateBefore E' k y).st.base.stableRecord
    rw [he, hf]
    exact hsafe.compatible j l x y ⟨hj, hjlen⟩ ⟨hl, hllen⟩ (ha.honest hx) (ha.honest hy)
  · intro i k x hi _ hik hx
    obtain ⟨j, hj, hjlen, hjlocal, he⟩ := hmap x hx i hi.1
    obtain ⟨l, hl, hllen, _, hf⟩ := wcg_empty_stateMap ha hs hr hend x hx hjlocal hik hjlen
    change Block.Preceq (rho.stateBefore E' i x).st.base.stableRecord
      (rho.stateBefore E' k x).st.base.stableRecord
    rw [he, hf]
    exact hsafe.monotone j l x ⟨hj, hjlen⟩ ⟨hj.trans hl, hllen⟩ hl (ha.honest hx)
  · intro i x hi hx
    obtain ⟨j, hj, hjlen, _, he⟩ := hmap x hx i hi.1
    change Block.Preceq Q (rho.stateBefore E' i x).st.base.stableRecord
    rw [he]
    exact hsafe.seed j x ⟨hj, hjlen⟩ (ha.honest hx)
/-- All empty-suffix fields follow once the cross-validator finality-service
bridge is supplied. The bridge is a proof obligation, not a public premise. -/
theorem wcg_empty_live_of_finalBelow
    (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hb : Base₂ p c E' rho) (hs : V2.D.ScheduleWellFormed E source)
    (hend : rho.horizon = source.horizon)
    {w : HealingWitness} {iSource : Nat} {ΔF : Time}
    (hseed : WCSeed p c E source w iSource)
    (hgate : SA.gateTime p.toParams w.u ≤ source.horizon)
    (hlive : WeakContinuationLiveAt₂ p c E source w.u w.QStar iSource ΔF)
    (hcache : WCCachedSafety p c E source iSource w.QStar)
    (hcover : ∀ pt : PtSP, w.u + 2 ≤ pt.s →
      HonestProposal E source (fgsaInterface p c) pt.s pt.P →
      SA.gateTime p.toParams pt.s ≤ source.horizon →
      ∃ x ∈ source.honest, Block.Preceq pt.P
        (V2.D.outputAt E source (fgsaInterface p c).stable x source.horizon))
    (hfinal : ∀ i x y, afterTicksIdx rho (SA.gateTime p.toParams w.u) ≤ i →
      i ≤ rho.events.length → x ∈ rho.honest → confirmedReaderIdx p c E' rho y i →
      Block.Preceq (F_at p c E' rho i x) (S_at p c E' rho i y)) :
    WeakContinuationLiveAt₂ p c E' rho w.u w.QStar
      (afterTicksIdx rho (SA.gateTime p.toParams w.u)) ΔF := by
  have hr := hb.valid.toScheduleWellFormed
  have hsafety := hcache
  have hout := wcg_empty_outputDomain ha hs hr hend hseed hgate hsafety
  have hincl := wcg_empty_inclusion ha hs hr hend hgate hlive
  have hsafety' := hsafety
  rw [hseed.cut] at hsafety'
  obtain ⟨hc, hm, hserved⟩ := wcg_empty_stateSafety ha hs hr hend hsafety'
  have htime : ∀ t, SA.gateTime p.toParams w.u ≤ t →
      afterTicksIdx rho (SA.gateTime p.toParams w.u) ≤ timeIdx rho t := by
    intro t ht
    exact (preIdx_le_afterTicksIdx E' rho hr _).2.trans
      (V2.D.Engine.read_length_mono _ _ ht)
  refine ⟨fun _ => ⟨fun i j x y hii hjj hx hy => hc i j x y hii hjj hx.1.1 hy.1.1,
    fun i j x hii hjj hij hx _ => hm i j x hii hjj hij hx.1.1,
    fun i x hii hx => hserved i x hii hx.1.1, hfinal, fun g hg =>
      ⟨fun t r x y ht hr hx hy => (hout g hg).1 t r x y ht hr hx.1 hy.1,
        fun t r x ht hr htr hx _ => (hout g hg).2 t r x ht hr htr hx.1⟩⟩, fun _ => hincl, ?_⟩
  intro _ G' hG hrec t ht hdeadline
  apply wcg_growthOfOutputs hb w.u _ hincl _ G' hG hrec t ht hdeadline
  · intro g hg
    refine ⟨?_, ?_⟩
    · intro t r x y ht hr hx hy
      exact (hout g hg).1 t r x y (htime t ht) (htime r hr) hx hy
    · intro t r x ht hr htr hx
      exact (hout g hg).2 t r x (htime t ht) (htime r hr) htr hx
  · intro pt hslot hprop hcovered g hg t x ht hth hx
    have htime : SA.proposalTime p.toParams pt.s ≤ source.horizon := by
      change 4 * p.Δ * (pt.s : Int) ≤ source.horizon
      have hh := hcovered.trans_eq hend
      change 4 * p.Δ * (pt.s : Int) + 6 * p.Δ ≤ source.horizon at hh
      nlinarith [p.deltaPos]
    obtain ⟨y, hy, hP⟩ := hcover pt hslot
      (wcg_proposalSourceReplay ha hs hr hprop htime) (hcovered.trans_eq hend)
    have hidx (t : Time) (ht : SA.gateTime p.toParams w.u ≤ t) :
        afterTicksIdx source (SA.gateTime p.toParams w.u) ≤ timeIdx source t :=
      (preIdx_le_afterTicksIdx E source hs _).2.trans
        (V2.D.Engine.read_length_mono (rho := source) _ t ht)
    have hc := (hcache.outputs (fgsaInterface p c).stable (by simp)).1
      t source.horizon x y (hseed.cut ▸ hidx t ht)
      (hseed.cut ▸ hidx source.horizon hgate) (ha.honest hx.1) hy
    change Block.Compatible (V2.D.outputAt E source (fgsaInterface p c).stable x t)
      (V2.D.outputAt E source (fgsaInterface p c).stable y source.horizon) at hc
    rw [fgsa_outputAt_eq_S_at E source hs (fgsaInterface p c).stable (by simp) x t] at hc
    rw [wcg_empty_outputReplay ha hs hr hend g x hx.1 t,
      fgsa_outputAt_eq_S_at E source hs g hg x t]
    change Block.compatible _ pt.P = true
    rw [Gen.Pure.block_compatible_comm]
    exact Gen.Pure.block_compatible_of_preceq_compatible hP (by
      simpa only [Block.Compatible, Gen.Pure.block_compatible_comm
        (V2.D.outputAt E source (fgsaInterface p c).stable y source.horizon)] using hc)

/-- Empty-suffix finality is below every retained output. The source's strict
finality causality puts service before the matched continuation prefix. -/
theorem wcg_empty_finalBelow
    (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hsch : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    (hend : rho.horizon = source.horizon)
    {w : HealingWitness} {iSource : Nat} (hs : WCSeed p c E source w iSource)
    (hinv : ∀ i, iSource ≤ i ∧ i ≤ source.events.length → WCInv p c E source w iSource i)
    (hcache : WCCachedSafety p c E source iSource w.QStar)
    (hcausal : ∀ i x D X h, HeldAt p c E source i x D → 0 < h →
      (finalityView p D).F = X → (finalityView p D).h_F = h →
      WCFinalityTargetEarlier p c E source i D X h)
    (hservice : ∀ j v s B, v ∈ source.honest → iSource ≤ j → IsGateTick p c source j v s →
      w.u < s → gateResultAt p c E source j = some (some B) →
      SA.gateTime p.toParams s + 4 * p.Δ ≤ source.horizon →
      ∀ k y, afterTicksIdx source (SA.gateTime p.toParams s + 4 * p.Δ) ≤ k →
        k ≤ source.events.length → confirmedReaderIdx p c E source y k →
        Block.Preceq B (S_at p c E source k y)) :
    ∀ i x y, afterTicksIdx rho (SA.gateTime p.toParams w.u) ≤ i →
      i ≤ rho.events.length →
      x ∈ rho.honest → confirmedReaderIdx p c E' rho y i →
      Block.Preceq (F_at p c E' rho i x) (S_at p c E' rho i y) := by
  intro i x y hi hilen hx hy
  obtain ⟨j, hj, hjlen, hex, _hlocal, htimed⟩ := wcg_empty_stateMap_timed ha hsch hr hend x hx hi
  have hj' : iSource ≤ j := hs.cut ▸ hj
  have inv := hinv j ⟨hj', hjlen⟩
  have hservedY : Block.Preceq w.QStar (S_at p c E' rho i y) := by
    obtain ⟨k, hk, hklen, hey, _, _⟩ :=
      wcg_empty_stateMap_timed ha hsch hr hend y hy.1.1 hi
    have hk' : iSource ≤ k := hs.cut ▸ hk
    change Block.Preceq w.QStar (rho.stateBefore E' i y).st.base.stableRecord
    rw [hey]
    exact hcache.seed k y ⟨hk', hklen⟩ (ha.honest hy.1.1)
  have hmatch : F_at p c E' rho i x = F_at p c E source j x :=
    congrArg (fun st : Node p => eraseFG st.st.fg.F) hex
  rw [hmatch]
  obtain ⟨D, hD, hF⟩ := ((inv.finite j hj' le_rfl).store x (ha.honest hx)).fg.Fcar
  by_cases hlo : (finalityView p D).h_F ≤ w.M
  · exact Gen.Pure.block_preceq_trans
      (inv.lowFinalized j x D _ _ hj' le_rfl ⟨ha.honest hx, hD⟩ hF rfl hlo)
      (Gen.Pure.block_preceq_trans hs.sourcePrefix hservedY)
  have hpos : 0 < (finalityView p D).h_F := by simp only [Height] at *; omega
  have hhigh : w.M + 1 ≤ (finalityView p D).h_F := by simp only [Height] at *; omega
  obtain ⟨jf, z, rf, af, uf, H, jt, v, rt, aT, ut, K, B, hjf, haf, _, _, _, _,
      _, _, _, _, hjt, haT, hdecode, _, htarget, hK, hXK, hgate, hKB, hgap⟩ :=
    (hcausal j x D _ _ ⟨ha.honest hx, hD⟩ hpos hF rfl).finalityRow
  have hfields : aT.payload.height_pair = ut.height_pair := by
    rcases aT with ⟨auth, body⟩
    cases auth with
    | none => cases hdecode
    | proposer s => cases hdecode
    | seat label k =>
      cases label with
      | head s => cases hdecode
      | fg => exact congrArg SimplexFG.Row.height_pair (Option.some.inj hdecode)
  have hname : namedEntry aT.payload.height_pair =
      some ((finalityView p D).h_F, (storeAt p c E source j x).fg.F.root) := by
    rw [hfields, htarget]
    rfl
  by_cases hbefore : jt < iSource
  · obtain ⟨K', B', hK', _, _, _, _, hbelow⟩ :=
      hs.highSources jt v rt aT _ hbefore haT hname hhigh
    have heq : K = K' := Option.some.inj (Option.some.inj (hK.symm.trans hK'))
    exact Gen.Pure.block_preceq_trans (eraseFG_preceq hXK)
      (Gen.Pure.block_preceq_trans (heq ▸ hbelow) hservedY)
  have hafter : iSource ≤ jt := Nat.le_of_not_gt hbefore
  have ht : IsGateTick p c source jt v (rt * p.R) := haT.2.1
  have hlabel : w.u < rt * p.R := by
    by_contra hn
    have hle : rt * p.R ≤ w.u := Nat.le_of_not_gt hn
    have htime : SA.gateTime p.toParams (rt * p.R) ≤ SA.gateTime p.toParams w.u := by
      have hcast : ((rt * p.R : Nat) : Time) ≤ w.u := Int.ofNat_le.mpr hle
      change 4 * p.Δ * (rt * p.R : Nat) + 6 * p.Δ ≤ 4 * p.Δ * (w.u : Time) + 6 * p.Δ
      nlinarith [p.deltaPos]
    have hlt := wcg_tick_before_cut hsch ht htime
    rw [← hs.cut] at hlt
    omega
  have hhor : SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ ≤ source.horizon :=
    hgap.le.trans (hsch.in_horizon _ (List.mem_of_getElem? haf.2.1)).2
  have hdeadline : SA.gateTime p.toParams w.u ≤ SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ := by
    have hcast : (w.u : Time) ≤ ((rt * p.R : Nat) : Time) := Int.ofNat_le.mpr hlabel.le
    change 4 * p.Δ * (w.u : Time) + 6 * p.Δ ≤ 4 * p.Δ * (rt * p.R : Nat) + 6 * p.Δ + 4 * p.Δ
    nlinarith [p.deltaPos]
  obtain ⟨f, hf, hftime⟩ := htimed jf (.tick z (p.actionTime rf)) hjf haf.2.1
    (hdeadline.trans_lt hgap)
  have hcut := wcg_cut_before_prefix_event hr hf (hgap.trans_le hftime)
  obtain ⟨k, hk, hklen, hey, hlocal, htimedY⟩ :=
    wcg_empty_stateMap_timed ha hsch hr hend y hy.1.1 hcut
  have hraw := (gateResultAt_eq_gateResult p c E source hsch ht).trans hgate
  have hprefix : prefixTime source k ≤ prefixTime rho i := by
    unfold prefixTime
    cases he : (source.events.take k).getLast? with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      have hnonneg : 0 ≤ f.time := (hr.in_horizon _ ((List.take_sublist _ _).subset hf)).1
      obtain ⟨l, hl⟩ := List.mem_iff_getElem?.mp hf
      have hli := lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hl).1
        (List.length_take_le _ _)
      have he := hl
      rw [List.getElem?_take_of_lt hli] at he
      exact hnonneg.trans (wcg_event_before_prefixTime hr hilen hli he)
    | some e =>
      simp only [Option.map_some, Option.getD_some]
      obtain ⟨l, hl⟩ := List.mem_iff_getElem?.mp (List.mem_of_getLast? he)
      have hlk := lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hl).1
        (List.length_take_le _ _)
      rw [List.getElem?_take_of_lt hlk] at hl
      by_cases hd : e.time ≤ SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ
      · obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hf
        have hmi := lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hm).1
          (List.length_take_le _ _)
        rw [List.getElem?_take_of_lt hmi] at hm
        exact hd.trans (hgap.le.trans (hftime.trans
          (wcg_event_before_prefixTime hr hilen hmi hm)))
      · obtain ⟨g, hg, heg⟩ := htimedY l e hlk hl (lt_of_not_ge hd)
        obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hg
        have hmi := lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hm).1
          (List.length_take_le _ _)
        rw [List.getElem?_take_of_lt hmi] at hm
        exact heg.trans (wcg_event_before_prefixTime hr hilen hmi hm)
  have hreader := wcg_empty_readerReplay ha hsch hr hend hilen hklen hy hlocal hey hprefix
  have hserved := hservice jt v (rt * p.R) B haT.1 hafter ht hlabel hraw hhor
    k y hk hklen hreader
  have heS : S_at p c E' rho i y = S_at p c E source k y :=
    congrArg (fun st => st.st.base.stableRecord) hey
  rw [heS]
  exact Gen.Pure.block_preceq_trans (eraseFG_preceq hXK)
    (Gen.Pure.block_preceq_trans hKB hserved)

end AvailableChain.FGSA.Run

end
