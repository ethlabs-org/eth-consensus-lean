module
public import AvailableChainContractProofs.Canonical

@[expose] public section
namespace AvailableChain.Contract
open AvailableChain.Generic

namespace Run
variable {V : Type} [Fintype V] [DecidableEq V] {F : Family} {E : Env V}

theorem not_hashCollision_of_injective {rho : Run F E}
    (hi : rho.InjectiveHash) : ¬ rho.HashCollision := by
  rintro ⟨a, b, hab, he, _, _⟩
  cases a with
  | none =>
    cases b with
    | none => exact hab rfl
    | some b => exact hi.2 b he.symm
  | some a =>
    cases b with
    | none => exact hi.2 a he
    | some b => exact hab (congrArg some (hi.1 he))

/-- Headers whose own-key proposals occur in the honest observation set. -/
def signedHeaders (rho : Run F E) : Set Header :=
  {h | rho.ObservedItem (some h)}

/-- A finite list covering every root seen in the execution. -/
def roots (rho : Run F E) : List (protoOf F E).Object :=
  (List.range rho.events.length).flatMap fun i =>
    rho.releasesAt i ++ (match rho.events[i]? with
      | some (.deliver _ o _) => [o]
      | _ => [])

theorem observed_mem_roots {rho : Run F E} {o : (protoOf F E).Object}
    (ho : o ∈ rho.Observed) : o ∈ closure rho.roots := by
  obtain ⟨v, hv, k, r, hk, he, hc⟩ := ho
  apply mem_closure_iff _ _ |>.mpr
  refine ⟨r, ?_, hc⟩
  apply List.mem_flatMap.mpr
  refine ⟨k, List.mem_range.mpr hk, ?_⟩
  rcases he with ⟨t, ht, hr⟩ | ⟨t, ht⟩
  · exact List.mem_append_left _ hr
  · exact List.mem_append_right _ (by simp [ht])

theorem signedHeaders_finite (rho : Run F E) : rho.signedHeaders.Finite := by
  classical
  apply Set.Finite.subset (s := ↑((closure rho.roots).filterMap Obj.signedProp).toFinset)
    (Finset.finite_toSet _)
  intro h hh
  obtain ⟨cs, hc⟩ := hh
  simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filterMap]
  exact ⟨.mk (.proposer h.slot) (.prop h) cs, observed_mem_roots hc,
    by simp [Obj.signedProp]⟩

def headerCode (h : Header) : Nat :=
  Nat.pair (Nat.pair h.parent h.slot) (Nat.pair h.input h.aux)

theorem headerCode_injective : Function.Injective headerCode := by
  intro a b he
  obtain ⟨hp, hi⟩ := Nat.pair_eq_pair.mp he
  obtain ⟨hp, hs⟩ := Nat.pair_eq_pair.mp hp
  obtain ⟨hi, ha⟩ := Nat.pair_eq_pair.mp hi
  cases a; cases b; simp_all

/-- Extend the collision-free observed hash to a globally injective nonzero hash. -/
theorem extend_hash (rho : Run F E) (hn : ¬ rho.HashCollision) :
    ∃ hash' : Header → Nat, (Function.Injective hash' ∧ ∀ h, hash' h ≠ 0) ∧
      ∀ h ∈ rho.signedHeaders, hash' h = rho.hash h := by
  classical
  let S := rho.signedHeaders_finite.toFinset
  let M := S.sup rho.hash
  have bound : ∀ h ∈ rho.signedHeaders, rho.hash h ≤ M := by
    intro h hh
    exact Finset.le_sup (f := rho.hash) (by simpa [S] using hh)
  have nz : ∀ h ∈ rho.signedHeaders, rho.hash h ≠ 0 := by
    intro h hh hz
    exact hn ⟨some h, none, by simp, hz, hh, trivial⟩
  have inj : ∀ a ∈ rho.signedHeaders, ∀ b ∈ rho.signedHeaders,
      rho.hash a = rho.hash b → a = b := by
    intro a ha b hb he
    by_contra hab
    exact hn ⟨some a, some b, by simpa using hab, he, ha, hb⟩
  let f := fun h => if h ∈ rho.signedHeaders then rho.hash h else M + 1 + headerCode h
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · intro a b he
    by_cases ha : a ∈ rho.signedHeaders <;> by_cases hb : b ∈ rho.signedHeaders
    · exact inj a ha b hb (by simpa [f, ha, hb] using he)
    · have := bound a ha
      simp only [f, ite_eq_left ha, ite_eq_right hb] at he
      omega
    · have := bound b hb
      simp only [f, ite_eq_right ha, ite_eq_left hb] at he
      omega
    · apply headerCode_injective
      simpa [f, ha, hb] using he
  · intro h
    by_cases hh : h ∈ rho.signedHeaders
    · simpa [f, hh] using nz h hh
    · simp only [f, ite_eq_right hh]; omega
  · intro h hh; simp [f, hh]

/-- Hash agreement on an observed root fixes every digest passed with it. -/
theorem digests_eq_of_observed (rho : Run F E) (hash' : Header → Nat)
    (ha : ∀ h ∈ rho.signedHeaders, hash' h = rho.hash h)
    {o : (protoOf F E).Object} (ho : o ∈ rho.Observed) :
    digests hash' o = digests rho.hash o := by
  unfold digests
  apply List.map_congr_left
  intro h hh
  obtain ⟨d, hd, he⟩ := List.mem_filterMap.mp hh
  have obs : d ∈ rho.Observed := by
    obtain ⟨v, hv, k, r, hk, hr, hc⟩ := ho
    exact ⟨v, hv, k, r, hk, hr, hc.trans ((Obj.mem_parts_iff _ _).mp hd)⟩
  have hh : h ∈ rho.signedHeaders := by
    cases d with
    | mk a m cs =>
      cases a <;> cases m <;> simp [Obj.signedProp] at he
      obtain ⟨hs, rfl⟩ := he
      subst hs
      exact ⟨cs, obs⟩
  exact Prod.ext rfl (ha h hh)

end Run

/-- A release batch consults only the digests of the roots it releases. -/
theorem releaseAll_eq_of_digests {pub : Public} {P : Protocol pub}
    (hash hash' : Header → Nat) (nd : Node P) (cs : List P.Object)
    (ha : ∀ o ∈ (releaseAll hash nd cs).2, digests hash' o = digests hash o) :
    releaseAll hash' nd cs = releaseAll hash nd cs := by
  induction cs generalizing nd with
  | nil => rfl
  | cons c cs ih =>
    unfold releaseAll at ha ⊢
    split at ha
    next hf =>
      simp only [hf, ↓reduceIte]
      have hc := ha c List.mem_cons_self
      rw [hc]
      rw [ih _ (fun o ho => ha o (List.mem_cons_of_mem c ho))]
    next hf =>
      simp only [hf]
      exact ih nd ha

namespace Run
variable {V : Type} [Fintype V] [DecidableEq V] {F : Family} {E : Env V}

/-- Replacing the hash while preserving observed digests preserves the trace. -/
theorem rehash_trace (rho : Run F E) (hv : rho.ExecutionValid) (hash' : Header → Nat)
    (ha : ∀ h ∈ rho.signedHeaders, hash' h = rho.hash h) :
    let r := {rho with hash := hash'}
    (∀ i, r.stateBefore i = rho.stateBefore i) ∧
      (∀ i, r.releasesAt i = rho.releasesAt i) := by
  let r := {rho with hash := hash'}
  have tick_eq : ∀ i v t, rho.events[i]? = some (.tick v t) →
      r.tick (rho.stateBefore i v) v t = rho.tick (rho.stateBefore i v) v t := by
    intro i v t he
    unfold tick
    change (if E.awake v t then releaseAll hash' _ _ else _) = _
    split
    · apply releaseAll_eq_of_digests
      intro o ho
      apply rho.digests_eq_of_observed hash' ha
      refine ⟨v, hv.honest_only _ (List.mem_of_getElem? he), i, o,
        (List.getElem?_eq_some_iff.mp he).1, Or.inl ⟨t, he, ?_⟩, .refl _⟩
      simpa only [releasesAt, he, tick, ‹E.awake v t = true›, ↓reduceIte, r, candidates] using ho
    · rfl
  have states : ∀ i, r.stateBefore i = rho.stateBefore i := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      cases he : rho.events[i]? with
      | none => simpa [stateBefore, List.take_add_one, r, he] using ih
      | some e =>
        rw [r.stateBefore_succ he, rho.stateBefore_succ he, ih]
        cases e with
        | tick v t => simp only [step, tick_eq i v t he]
        | restart v t => rfl
        | deliver v o t =>
          have ho : o ∈ rho.Observed :=
            ⟨v, hv.honest_only _ (List.mem_of_getElem? he), i, o,
              (List.getElem?_eq_some_iff.mp he).1, Or.inr ⟨t, he⟩, .refl _⟩
          simp only [step]
          simp only [show r.hash = hash' from rfl, rho.digests_eq_of_observed hash' ha ho]
  refine ⟨states, ?_⟩
  intro i
  change r.releasesAt i = rho.releasesAt i
  unfold releasesAt
  change (match rho.events[i]? with | some (.tick v t) => _ | _ => _) = _
  cases he : rho.events[i]? with
  | none => rfl
  | some e =>
    cases e with
    | tick v t =>
      change (r.tick (r.stateBefore i v) v t).2 = _
      rw [states i]
      exact congrArg Prod.snd (tick_eq i v t he)
    | deliver => rfl
    | restart => rfl

omit [DecidableEq V] in
private theorem filter_time_prefix (xs : List (Event V (protoOf F E).Object))
    (hs : xs.Pairwise Event.keyLe) (t : Time) :
    xs.filter (fun e => decide (e.time ≤ t)) =
      xs.take (xs.filter (fun e => decide (e.time ≤ t))).length := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨hh, ht⟩ := List.pairwise_cons.mp hs
    by_cases he : e.time ≤ t
    · simp only [List.filter_cons, he, decide_true, ite_true,
        List.length_cons, List.take_succ_cons]
      exact congrArg (e :: ·) (ih ht)
    · have hn : es.filter (fun e => decide (e.time ≤ t)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro f hf
        have h := hh f hf
        change Event.keyLe e f at h
        unfold Event.keyLe at h
        have hef : e.time ≤ f.time := by
          rcases h with h | ⟨h, _⟩
          · exact h.le
          · exact le_of_eq h
        change ¬ decide (f.time ≤ t) = true
        simp only [decide_eq_true_eq]
        exact fun hf => he (hef.trans hf)
      simp [he, hn]

def rehash (rho : Run F E) (hash' : Header → Nat) : Run F E := {rho with hash := hash'}

/-- All execution observations needed by the escaped claims. -/
structure SameTrace (rho r : Run F E) : Prop where
  honest : r.honest = rho.honest
  horizon : r.horizon = rho.horizon
  events : r.events = rho.events
  seat : r.seat = rho.seat
  proposer : r.proposer = rho.proposer
  input : r.input = rho.input
  states : r.stateBefore = rho.stateBefore
  reads : r.readAt = rho.readAt
  releases : r.releasesAt = rho.releasesAt

theorem rehash_sameTrace (rho : Run F E) (hv : rho.ExecutionValid)
    (hash' : Header → Nat) (ha : ∀ h ∈ rho.signedHeaders, hash' h = rho.hash h) :
    rho.SameTrace (rho.rehash hash') := by
  obtain ⟨hs, hr⟩ := rho.rehash_trace hv hash' ha
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, funext hs, ?_, funext hr⟩
  funext t
  have hf := filter_time_prefix rho.events hv.sorted t
  change (rho.events.filter _).foldl _ _ = (rho.events.filter _).foldl _ _
  rw [hf]
  exact hs _

namespace SameTrace
variable {rho r : Run F E} (h : SameTrace rho r)
include h

theorem releases_eq : r.releases = rho.releases := by
  repeat' (apply funext; intro)
  simp only [Run.releases, h.events, h.releases]

theorem receives_eq : r.receives = rho.receives := by
  repeat' (apply funext; intro)
  simp only [Run.receives, h.events]

theorem view_eq : r.View = rho.View := by
  repeat' (apply funext; intro)
  simp only [Run.View, h.releases_eq, h.receives_eq]

theorem viewIdx_eq : r.ViewIdx = rho.ViewIdx := by
  repeat' (apply funext; intro)
  simp only [Run.ViewIdx, h.events, h.releases]

theorem observed_eq : r.Observed = rho.Observed := by
  repeat' (apply funext; intro)
  simp only [Run.Observed, h.honest, h.events, h.viewIdx_eq]

theorem cutAt_eq : r.cutAt = rho.cutAt := by
  repeat' (apply funext; intro)
  simp only [Run.cutAt, h.events]

theorem cutTime_eq : r.cutTime = rho.cutTime := by
  repeat' (apply funext; intro)
  simp only [Run.cutTime, h.events]

theorem holder_eq : r.holder = rho.holder := by
  repeat' (apply funext; intro)
  simp only [Run.holder, h.seat, h.proposer]

theorem readOut_eq : r.readOut = rho.readOut := by
  repeat' (apply funext; intro)
  simp only [Run.readOut, h.reads]

theorem readIdx_eq : r.readIdx = rho.readIdx := by
  repeat' (apply funext; intro)
  simp only [Run.readIdx, h.states]

theorem honestProposal_eq : r.HonestProposal = rho.HonestProposal := by
  repeat' (apply funext; intro)
  simp only [Run.HonestProposal, h.proposer, h.honest, h.releases_eq]

theorem unforgeable_eq : r.Unforgeable = rho.Unforgeable := by
  simp only [Run.Unforgeable, h.events, h.honest, h.holder_eq, h.releases]

theorem served_eq : r.Served = rho.Served := by
  repeat' (apply funext; intro)
  simp only [Run.Served, h.releases_eq, h.receives_eq, h.events]

theorem delivers_eq : r.Delivers = rho.Delivers := by
  repeat' (apply funext; intro)
  simp only [Run.Delivers, h.honest, h.releases_eq, h.horizon, h.served_eq]

theorem partialSynchrony_eq : r.PartialSynchrony = rho.PartialSynchrony := by
  simp only [Run.PartialSynchrony, h.delivers_eq, h.horizon]

theorem healthyPrefixDelivery_eq : r.HealthyPrefixDelivery = rho.HealthyPrefixDelivery := by
  repeat' (apply funext; intro)
  simp only [Run.HealthyPrefixDelivery, h.delivers_eq]

theorem faulty_eq : r.faulty = rho.faulty := by
  simp only [Run.faulty, h.honest]

theorem awakeAt_eq : r.awakeAt = rho.awakeAt := by
  repeat' (apply funext; intro)
  simp only [Run.awakeAt, h.honest]

theorem awakeIn_eq : r.awakeIn = rho.awakeIn := by
  repeat' (apply funext; intro)
  simp only [Run.awakeIn, h.honest]

theorem ready_eq : r.Ready = rho.Ready := by
  repeat' (apply funext; intro)
  simp only [Run.Ready, h.honest]

theorem readyAt_eq : r.readyAt = rho.readyAt := by
  funext C t
  apply Finset.ext
  intro v
  simp only [Run.readyAt, Finset.mem_filter, h.honest, h.ready_eq]

theorem readyMajority_eq : r.ReadyMajority = rho.ReadyMajority := by
  repeat' (apply funext; intro)
  simp only [Run.ReadyMajority, h.faulty_eq, h.readyAt_eq]

theorem etaSleepy_eq : r.EtaSleepy = rho.EtaSleepy := by
  repeat' (apply funext; intro)
  simp only [Run.EtaSleepy, h.awakeIn_eq, h.faulty_eq, h.readyAt_eq]

theorem fullParticipation_eq : r.FullParticipation = rho.FullParticipation := by
  repeat' (apply funext; intro)
  simp only [Run.FullParticipation, h.honest, h.horizon]

theorem belowQuarter_eq : r.BelowQuarter = rho.BelowQuarter := by
  simp only [Run.BelowQuarter, h.faulty_eq]

theorem belowOneThird_eq : r.BelowOneThird = rho.BelowOneThird := by
  simp only [Run.BelowOneThird, h.faulty_eq]

theorem readyProposer_eq : r.ReadyProposer = rho.ReadyProposer := by
  repeat' (apply funext; intro)
  simp only [Run.ReadyProposer, h.ready_eq, h.proposer]

theorem recurrence_eq : r.Recurrence = rho.Recurrence := by
  repeat' (apply funext; intro)
  simp only [Run.Recurrence, h.horizon, h.readyProposer_eq]

theorem inCuts_eq : r.InCuts = rho.InCuts := by
  repeat' (apply funext; intro)
  simp only [Run.InCuts, h.cutAt_eq, h.events]

theorem consistentFrom_eq : r.ConsistentFrom = rho.ConsistentFrom := by
  repeat' (apply funext; intro)
  simp only [Run.ConsistentFrom, h.honest, h.inCuts_eq, h.readIdx_eq]

theorem agreeFrom_eq : r.AgreeFrom = rho.AgreeFrom := by
  repeat' (apply funext; intro)
  simp only [Run.AgreeFrom, h.consistentFrom_eq]

theorem monotoneFrom_eq : r.MonotoneFrom = rho.MonotoneFrom := by
  repeat' (apply funext; intro)
  simp only [Run.MonotoneFrom, h.honest, h.inCuts_eq, h.readIdx_eq]

theorem below_eq : r.Below = rho.Below := by
  repeat' (apply funext; intro)
  simp only [Run.Below, h.honest, h.events, h.readIdx_eq]

theorem inBy_eq : r.InBy = rho.InBy := by
  repeat' (apply funext; intro)
  simp only [Run.InBy, h.ready_eq, h.readOut_eq]

theorem includedFrom_eq : r.IncludedFrom = rho.IncludedFrom := by
  repeat' (apply funext; intro)
  simp only [Run.IncludedFrom, h.readyProposer_eq, h.horizon, h.honestProposal_eq, h.inBy_eq]

theorem liveFrom_eq : r.LiveFrom = rho.LiveFrom := by
  repeat' (apply funext; intro)
  simp only [Run.LiveFrom, h.horizon, h.readyProposer_eq, h.honestProposal_eq, h.inBy_eq,
    h.ready_eq, h.readOut_eq]

theorem persistsThrough_eq : r.PersistsThrough = rho.PersistsThrough := by
  repeat' (apply funext; intro)
  simp only [Run.PersistsThrough, h.honest, h.readOut_eq]

theorem slashable_eq : r.Slashable = rho.Slashable := by
  repeat' (apply funext; intro)
  simp only [Run.Slashable, h.holder_eq]

theorem slashedBy_eq : r.slashedBy = rho.slashedBy := by
  funext A
  apply Finset.ext
  intro v
  simp only [Run.slashedBy, Finset.mem_filter, h.slashable_eq]

theorem accountablySafeFrom_eq : r.AccountablySafeFrom = rho.AccountablySafeFrom := by
  repeat' (apply funext; intro)
  simp only [Run.AccountablySafeFrom, h.honest, h.inCuts_eq, h.readIdx_eq, h.slashedBy_eq,
    h.viewIdx_eq]

theorem scheduleWellFormed_iff : r.ScheduleWellFormed ↔ rho.ScheduleWellFormed := by
  constructor <;> intro hx <;> cases hx <;> constructor <;>
    simp_all [h.honest, h.horizon, h.events] <;> assumption

theorem sleepWellFormed_iff : r.SleepWellFormed ↔ rho.SleepWellFormed := by
  constructor <;> intro hx
  all_goals
    constructor
    · simpa only [h.events] using hx.tick_awake
    · simpa only [h.events] using hx.deliver_awake
    · simpa only [h.events] using hx.restart_at_wake
    · simpa only [h.events, h.honest, h.horizon] using hx.wake_restart

theorem executionValid_iff : r.ExecutionValid  ↔ rho.ExecutionValid  := by
  constructor <;> intro hx <;> cases hx <;> constructor <;>
    simp_all [h.scheduleWellFormed_iff, h.sleepWellFormed_iff, h.unforgeable_eq]

theorem safeFrom_iff (g : Output F E) (t : Time) : r.SafeFrom g t ↔ rho.SafeFrom g t := by
  constructor <;> intro hx <;> cases hx <;> constructor <;>
    simp_all [h.agreeFrom_eq, h.monotoneFrom_eq]

theorem readySafeFrom_iff (C : Constants) (g : Output F E) (t : Time) :
    r.ReadySafeFrom C g t ↔ rho.ReadySafeFrom C g t := by
  constructor <;> intro hx <;> cases hx <;> constructor <;>
    simp_all [h.inCuts_eq, h.ready_eq, h.cutTime_eq, h.readIdx_eq]

theorem sleepy_iff (C : Constants) (t : Time) : r.Sleepy C t ↔ rho.Sleepy C t := by
  constructor <;> intro hx <;> cases hx <;> constructor <;>
    simp_all [h.executionValid_iff, h.partialSynchrony_eq, h.horizon, h.readyMajority_eq]

theorem stableSleepy_iff (C : Constants) (t : Time) :
    r.StableSleepy C t ↔ rho.StableSleepy C t := by
  constructor <;> intro hx <;> cases hx <;> constructor <;>
    simp_all [h.sleepy_iff, h.horizon, h.etaSleepy_eq]

theorem fast_iff (C : Constants) (t : Time) : r.Fast C t ↔ rho.Fast C t := by
  constructor <;> intro hx <;> cases hx <;> constructor <;>
    simp_all [h.sleepy_iff, h.fullParticipation_eq, h.belowQuarter_eq]

theorem liveSleepy_iff (C : Constants) (t : Time) (k : Nat) :
    r.LiveSleepy C t k ↔ rho.LiveSleepy C t k := by
  constructor <;> intro hx <;> cases hx <;> constructor <;>
    simp_all [h.sleepy_iff, h.recurrence_eq]

theorem outageWith_iff (C : Constants) (lag : Nat) (T a b : Time) :
    r.OutageWith C lag T a b ↔ rho.OutageWith C lag T a b := by
  constructor <;> intro hx <;> cases hx <;> constructor <;>
    simp_all [h.executionValid_iff, h.healthyPrefixDelivery_eq, h.horizon, h.readyMajority_eq,
      h.etaSleepy_eq]

theorem fastOutage_iff (C : Constants) (T a b : Time) :
    r.FastOutage C T a b ↔ rho.FastOutage C T a b := by
  constructor <;> intro hx <;> cases hx <;> constructor <;>
    simp_all [h.outageWith_iff, h.readyAt_eq]

theorem recovery_iff (C : Constants) (k : Nat) : r.Recovery C k ↔ rho.Recovery C k := by
  constructor <;> intro hx <;> cases hx <;> constructor <;>
    simp_all [h.executionValid_iff, h.partialSynchrony_eq, h.readyAt_eq, h.faulty_eq,
      h.fullParticipation_eq, h.honest, h.horizon, h.recurrence_eq]

theorem finality_iff (C : Constants) (k : Nat) : r.Finality C k ↔ rho.Finality C k := by
  constructor <;> intro hx <;> cases hx <;> constructor <;>
    simp_all [h.recovery_iff, h.belowOneThird_eq, h.horizon, h.readyAt_eq]

theorem recoveredAt_iff (C : Constants) (t : Time) : r.RecoveredAt C t ↔ rho.RecoveredAt C t := by
  constructor <;> intro hx <;> cases hx <;> constructor <;>
    simp_all [h.readySafeFrom_iff, h.includedFrom_eq]

end SameTrace

/-- One transfer argument for every escaped field: the premise and conclusion
must depend only on the execution trace. -/
theorem lift_escaped (rho : Run F E) (A X : Run F E → Prop)
    (valid : A rho → rho.ExecutionValid)
    (premise : ∀ r, rho.SameTrace r → (A r ↔ A rho))
    (conclusion : ∀ r, rho.SameTrace r → (X r ↔ X rho))
    (hi : ∀ r, A r → r.InjectiveHash → X r) :
    A rho → X rho ∨ rho.HashCollision := by
  intro ha
  by_cases hc : rho.HashCollision
  · exact Or.inr hc
  · obtain ⟨hash', hinj, hagree⟩ := rho.extend_hash hc
    let r := rho.rehash hash'
    have hs : rho.SameTrace r := rho.rehash_sameTrace (valid ha) hash' hagree
    exact Or.inl ((conclusion r hs).mp (hi r ((premise r hs).mpr ha) hinj))

end Run

/-- Claims for globally injective nonzero hashes imply the collision-escaped
contract for arbitrary hashes. The unconditional fields are reused directly. -/
theorem claims_of_claimsInj {F : Family} {C : Constants}
    (claims : ClaimsInj F C) : Claims F C := by
  refine {
    constants := claims.constants
    slotTicks := claims.slotTicks
    outputValid := claims.outputValid
    outputOrder := claims.outputOrder
    finalizedMonotone := claims.finalizedMonotone
    honestNeverSlashed := claims.honestNeverSlashed
    confirmedSafe := ?_
    stableSafe := ?_
    confirmedIncluded := ?_
    stableIncluded := ?_
    stableIncludedFast := ?_
    confirmedLive := ?_
    stableLive := ?_
    stableResilient := ?_
    stableResilientFast := ?_
    recovered := ?_
    finalizedAccountable := ?_
    finalizedIncluded := ?_
    finalizedLive := ?_ }
  · intro V _ _ _ E rho t₀
    apply rho.lift_escaped (fun r => r.Sleepy C t₀)
      (fun r => r.SafeFrom (protoOf F E).confirmed t₀) (fun h => h.valid)
    · intro r hs; exact hs.sleepy_iff C t₀
    · intro r hs; exact hs.safeFrom_iff _ t₀
    · intro r; exact claims.confirmedSafe V E r t₀
  · intro V _ _ _ E rho t₀
    apply rho.lift_escaped (fun r => r.Sleepy C t₀)
      (fun r => r.SafeFrom (protoOf F E).stable t₀) (fun h => h.valid)
    · intro r hs; exact hs.sleepy_iff C t₀
    · intro r hs; exact hs.safeFrom_iff _ t₀
    · intro r; exact claims.stableSafe V E r t₀
  · intro V _ _ _ E rho t₀
    apply rho.lift_escaped (fun r => r.Sleepy C t₀)
      (fun r => r.IncludedFrom C (protoOf F E).confirmed t₀ C.D_c) (fun h => h.valid)
    · intro r hs; exact hs.sleepy_iff C t₀
    · intro r hs; simp only [hs.includedFrom_eq]
    · intro r; exact claims.confirmedIncluded V E r t₀
  · intro V _ _ _ E rho t₀
    apply rho.lift_escaped (fun r => r.StableSleepy C t₀)
      (fun r => r.IncludedFrom C (protoOf F E).stable t₀ C.D_s) (fun h => h.valid)
    · intro r hs; exact hs.stableSleepy_iff C t₀
    · intro r hs; simp only [hs.includedFrom_eq]
    · intro r; exact claims.stableIncluded V E r t₀
  · intro V _ _ _ E rho t₀
    apply rho.lift_escaped (fun r => r.Fast C t₀)
      (fun r => r.IncludedFrom C (protoOf F E).stable t₀ C.D_f) (fun h => h.valid)
    · intro r hs; exact hs.fast_iff C t₀
    · intro r hs; simp only [hs.includedFrom_eq]
    · intro r; exact claims.stableIncludedFast V E r t₀
  · intro V _ _ _ E rho t₀ k
    apply rho.lift_escaped (fun r => r.LiveSleepy C t₀ k)
      (fun r => r.LiveFrom C (protoOf F E).confirmed t₀ (C.growth.eval k)) (fun h => h.valid)
    · intro r hs; exact hs.liveSleepy_iff C t₀ k
    · intro r hs; simp only [hs.liveFrom_eq]
    · intro r; exact claims.confirmedLive V E r t₀ k
  · intro V _ _ _ E rho t₀ k
    apply rho.lift_escaped (fun r => r.LiveSleepy C t₀ k)
      (fun r => r.LiveFrom C (protoOf F E).stable t₀ (C.stableGrowth.eval k)) (fun h => h.valid)
    · intro r hs; exact hs.liveSleepy_iff C t₀ k
    · intro r hs; simp only [hs.liveFrom_eq]
    · intro r; exact claims.stableLive V E r t₀ k
  · intro V _ _ _ E rho T a b
    apply rho.lift_escaped (fun r => r.Outage C T a b)
      (fun r => r.PersistsThrough C (protoOf F E).stable T a b) (fun h => h.valid)
    · intro r hs; exact hs.outageWith_iff C C.armingLag T a b
    · intro r hs; simp only [hs.persistsThrough_eq]
    · intro r; exact claims.stableResilient V E r T a b
  · intro V _ _ _ E rho T a b
    apply rho.lift_escaped (fun r => r.FastOutage C T a b)
      (fun r => r.PersistsThrough C (protoOf F E).stable T a b) (fun h => h.valid)
    · intro r hs; exact hs.fastOutage_iff C T a b
    · intro r hs; simp only [hs.persistsThrough_eq]
    · intro r; exact claims.stableResilientFast V E r T a b
  · intro V _ _ _ E rho k
    apply rho.lift_escaped (fun r => r.Recovery C k)
      (fun r => r.RecoveredAt C
        (E.t_GST + ((C.recovery.eval k : Nat) : Time) * E.Δ)) (fun h => h.valid)
    · intro r hs; exact hs.recovery_iff C k
    · intro r hs; exact hs.recoveredAt_iff C _
    · intro r; exact claims.recovered V E r k
  · intro V _ _ _ E rho
    apply rho.lift_escaped (fun r => r.ExecutionValid)
      (fun r => r.AccountablySafeFrom (protoOf F E).finalized 0) (fun h => h)
    · intro r hs; exact hs.executionValid_iff
    · intro r hs; simp only [hs.accountablySafeFrom_eq]
    · intro r; exact claims.finalizedAccountable V E r
  · intro V _ _ _ E rho k
    apply rho.lift_escaped (fun r => r.Finality C k)
      (fun r => r.IncludedFrom C (protoOf F E).finalized
        (E.t_GST + ((C.finStart.eval k : Nat) : Time) * E.Δ) (C.finDelay.eval k)) (fun h => h.valid)
    · intro r hs; exact hs.finality_iff C k
    · intro r hs; simp only [hs.includedFrom_eq]
    · intro r; exact claims.finalizedIncluded V E r k
  · intro V _ _ _ E rho k
    apply rho.lift_escaped (fun r => r.Finality C k)
      (fun r => r.LiveFrom C (protoOf F E).finalized
        (E.t_GST + ((C.finStart.eval k : Nat) : Time) * E.Δ) (C.finDelay.eval k)) (fun h => h.valid)
    · intro r hs; exact hs.finality_iff C k
    · intro r hs; simp only [hs.liveFrom_eq]
    · intro r; exact claims.finalizedLive V E r k

/-- An escaped claim gives the injective-hash claim: an injective, nonzero
hash has no collision. -/
theorem ifInjective_of_orCollision {F : Family} {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} {rho : Run F E} {X : Prop} (h : orCollision F rho X) :
    ifInjective F rho X :=
  fun hi => h.resolve_right (Run.not_hashCollision_of_injective hi)

/-- The converse of `claims_of_claimsInj`. -/
theorem claimsInj_of_claims {F : Family} {C : Constants} (hC : Claims F C) :
    ClaimsInj F C where
  constants := hC.constants
  slotTicks := hC.slotTicks
  outputValid := hC.outputValid
  outputOrder := hC.outputOrder
  confirmedSafe := fun V _ _ _ E rho t₀ h =>
    ifInjective_of_orCollision (hC.confirmedSafe V E rho t₀ h)
  stableSafe := fun V _ _ _ E rho t₀ h =>
    ifInjective_of_orCollision (hC.stableSafe V E rho t₀ h)
  confirmedIncluded := fun V _ _ _ E rho t₀ h =>
    ifInjective_of_orCollision (hC.confirmedIncluded V E rho t₀ h)
  stableIncluded := fun V _ _ _ E rho t₀ h =>
    ifInjective_of_orCollision (hC.stableIncluded V E rho t₀ h)
  stableIncludedFast := fun V _ _ _ E rho t₀ h =>
    ifInjective_of_orCollision (hC.stableIncludedFast V E rho t₀ h)
  confirmedLive := fun V _ _ _ E rho t₀ k h =>
    ifInjective_of_orCollision (hC.confirmedLive V E rho t₀ k h)
  stableLive := fun V _ _ _ E rho t₀ k h =>
    ifInjective_of_orCollision (hC.stableLive V E rho t₀ k h)
  stableResilient := fun V _ _ _ E rho T b₀ b₁ h =>
    ifInjective_of_orCollision (hC.stableResilient V E rho T b₀ b₁ h)
  stableResilientFast := fun V _ _ _ E rho T b₀ b₁ h =>
    ifInjective_of_orCollision (hC.stableResilientFast V E rho T b₀ b₁ h)
  recovered := fun V _ _ _ E rho k h =>
    ifInjective_of_orCollision (hC.recovered V E rho k h)
  finalizedMonotone := hC.finalizedMonotone
  finalizedAccountable := fun V _ _ _ E rho h =>
    ifInjective_of_orCollision (hC.finalizedAccountable V E rho h)
  honestNeverSlashed := hC.honestNeverSlashed
  finalizedIncluded := fun V _ _ _ E rho k h =>
    ifInjective_of_orCollision (hC.finalizedIncluded V E rho k h)
  finalizedLive := fun V _ _ _ E rho k h =>
    ifInjective_of_orCollision (hC.finalizedLive V E rho k h)

/-- The two forms of the contract are equivalent: stating the escaped claims
"or a hash collision was observed" for every hash says exactly as much as
stating them outright for injective hashes. The escape adds nothing beyond
genuine collisions among observed headers. -/
theorem claims_iff_claimsInj {F : Family} {C : Constants} :
    Claims F C ↔ ClaimsInj F C :=
  ⟨claimsInj_of_claims, claims_of_claimsInj⟩

end AvailableChain.Contract
end
