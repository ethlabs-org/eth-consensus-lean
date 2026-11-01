module
public import AvailableChainRegistry.CounterRun

@[expose] public section

namespace AvailableChain.Registry.Counter

open AvailableChain AvailableChain.Generic AvailableChain.Framework
open AvailableChain.Statements.Generic AvailableChain.Framework.Catalog

/-- `process` accepts exactly the next height. -/
theorem process_of_eq {a : Nat} {o : counter.Object} (h : o.payload = a + 1) :
    counter.process a o = a + 1 := by
  simp [counter, h]

theorem process_of_ne {a : Nat} {o : counter.Object} (h : ¬ o.payload = a + 1) :
    counter.process a o = a := by
  simpa [counter] using h

/-! ### Schedule order in every valid run -/

section Schedule

variable {V : Type} [DecidableEq V] {E : Env V} {rho : Run V counter}

omit [DecidableEq V] in
/-- In a sorted schedule, a smaller index has a smaller or equal key. -/
theorem key_le_of_index_le (hs : ScheduleWellFormed E rho) {q j : Nat}
    {e f : Event V counter.Object} (hq : rho.events[q]? = some e)
    (hj : rho.events[j]? = some f) (h : q ≤ j) : e.key ≤ f.key := by
  obtain ⟨hql, rfl⟩ := List.getElem?_eq_some_iff.mp hq
  obtain ⟨hjl, rfl⟩ := List.getElem?_eq_some_iff.mp hj
  rcases Nat.lt_or_eq_of_le h with hlt | rfl
  · exact (List.pairwise_iff_getElem.mp hs.sorted) q j hql hjl hlt
  · exact le_refl _

omit [DecidableEq V] in
theorem time_le_of_key_le {e f : Event V counter.Object} (h : e.key ≤ f.key) :
    e.time ≤ f.time := by
  rcases Prod.Lex.toLex_le_toLex.mp h with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h

omit [DecidableEq V] in
/-- A strictly earlier time has a strictly smaller index. -/
theorem index_lt_of_time_lt (hs : ScheduleWellFormed E rho) {q j : Nat}
    {e f : Event V counter.Object} (hq : rho.events[q]? = some e)
    (hj : rho.events[j]? = some f) (ht : e.time < f.time) : q < j := by
  by_contra hn
  exact absurd (time_le_of_key_le (key_le_of_index_le hs hj hq (by omega))) (not_le.mpr ht)

omit [DecidableEq V] in
/-- A delivery before a tick has a strictly earlier time: at one time, ticks
come first. -/
theorem deliver_time_lt_tick (hs : ScheduleWellFormed E rho) {q i : Nat} {v u : V}
    {o : counter.Object} {t s : Time} (hq : rho.events[q]? = some (.deliver v o t))
    (hi : rho.events[i]? = some (.tick u s)) (h : q < i) : t < s := by
  rcases Prod.Lex.toLex_le_toLex.mp (key_le_of_index_le hs hq hi h.le) with h | ⟨_, h⟩
  · exact h
  · exact (Nat.not_succ_le_zero 0 h).elim

/-- The read at `T` includes every event up to an event at a time `≤ T`. -/
theorem stateBefore_le_readAt (hs : ScheduleWellFormed E rho) {j : Nat}
    {f : Event V counter.Object} (hj : rho.events[j]? = some f) {T : Time}
    (hT : f.time ≤ T) (v : V) :
    height (Run.stateBefore counter rho (j + 1)) v ≤ height (Run.readAt counter rho T) v := by
  have hself : (rho.events.take (j + 1)).filter (fun e => decide (e.time ≤ T)) =
      rho.events.take (j + 1) := by
    apply List.filter_eq_self.mpr
    intro x hx
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp hx
    rw [List.getElem?_take] at hq
    split_ifs at hq with hqj
    exact decide_eq_true
      (le_trans (time_le_of_key_le (key_le_of_index_le hs hq hj (by omega))) hT)
  have hsub : (rho.events.take (j + 1)).Sublist
      (rho.events.filter (fun e => decide (e.time ≤ T))) := by
    rw [← hself]
    exact (List.take_sublist _ _).filter _
  exact foldl_sublist hsub _ _ (fun _ => le_refl _) v

/-- If node `p` has height `a > 0` before index `i`, an earlier delivery to `p`
made `p` accept height `a`. -/
theorem accept_source (rho : Run V counter) (p : V) :
    ∀ i, 0 < height (Run.stateBefore counter rho i) p →
      ∃ i' < i, ∃ o t, rho.events[i']? = some (.deliver p o t) ∧
        o.payload = height (Run.stateBefore counter rho i) p ∧
        height (Run.stateBefore counter rho i') p < height (Run.stateBefore counter rho i) p ∧
        height (Run.stateBefore counter rho i) p ≤ height (Run.stateBefore counter rho (i' + 1)) p
  | 0, h => by
    set_option backward.isDefEq.respectTransparency false in
    simp [Run.stateBefore, World.init, height, counter] at h
  | i + 1, h => by
    set_option backward.isDefEq.respectTransparency false in
    have hsame : height (Run.stateBefore counter rho (i + 1)) p =
        height (Run.stateBefore counter rho i) p →
        ∃ i' < i + 1, ∃ o t, rho.events[i']? = some (.deliver p o t) ∧
          o.payload = height (Run.stateBefore counter rho (i + 1)) p ∧
          height (Run.stateBefore counter rho i') p <
            height (Run.stateBefore counter rho (i + 1)) p ∧
          height (Run.stateBefore counter rho (i + 1)) p ≤
            height (Run.stateBefore counter rho (i' + 1)) p := by
      intro heq
      obtain ⟨i', hi', o, t, h1, h2, h3, h4⟩ :=
        accept_source rho p i (by rw [heq] at h; exact h)
      rw [heq]
      exact ⟨i', by omega, o, t, h1, h2, h3, h4⟩
    cases he : rho.events[i]? with
    | none =>
      apply hsame
      unfold height Run.stateBefore
      rw [List.take_add_one, he]
      simp
    | some e =>
      have hstep := stateBefore_succ he
      by_cases heq : height (Run.stateBefore counter rho (i + 1)) p =
          height (Run.stateBefore counter rho i) p
      · exact hsame heq
      · cases e with
        | tick v t =>
          exact absurd (by unfold height; rw [hstep, step_tick]) heq
        | deliver v o t =>
          by_cases hv : p = v
          · subst hv
            have hval : height (Run.stateBefore counter rho (i + 1)) p =
                counter.process (height (Run.stateBefore counter rho i) p) o := by
              unfold height
              rw [hstep, step_deliver_self]
            by_cases hpay : o.payload = height (Run.stateBefore counter rho i) p + 1
            · have hval' := hval.trans (process_of_eq hpay)
              refine ⟨i, by omega, o, t, he, hpay.trans hval'.symm, ?_, le_refl _⟩
              omega
            · exact absurd (hval.trans (process_of_ne hpay)) heq
          · exact absurd (by unfold height; rw [hstep, step_deliver_ne _ hv]) heq

end Schedule

/-! ### Inclusion at `D = 1` -/

/-- In the Sleepy regime with `Δ = 1`, the proposal of an honest awake
proposer at `s` is in every honest `confirmed` read at `s + 1`. The proposer
proposes its height plus one. Every honest node has that height before the
proposal arrives, by checked receipt relay, so it accepts the proposal. -/
theorem counter_included (W : Validators) (E : Env W.V) (hΔ : E.Δ = 1)
    (rho : Run W.V counter) (t₀ : Time)
    (hs : SleepyRegime counter E counterIface rho t₀) :
    IncludedFrom counter E counterIface rho counterIface.confirmed t₀ 1 := by
  set_option backward.isDefEq.respectTransparency false in
  classical
  intro s _ hprop hsh
  obtain ⟨hph, hpa⟩ := hprop
  have hsched := hs.execution.toScheduleWellFormed
  have hs0 : (0 : Time) ≤ s := Int.natCast_nonneg s
  change (s : Time) + 1 ≤ rho.horizon at hsh
  have hsH : (s : Time) ≤ rho.horizon := by linarith
  have htick : Event.tick (rho.proposerOf s) (s : Time) ∈ rho.events :=
    hsched.tick_total _ hph s ⟨s, by rw [hΔ, mul_one]⟩ hs0 hsH
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp htick
  obtain ⟨a, ha⟩ : ∃ a, a = height (Run.stateBefore counter rho i) (rho.proposerOf s) :=
    ⟨_, rfl⟩
  obtain ⟨o, ho⟩ : ∃ o : counter.Object, o = ⟨.proposer s, a + 1⟩ := ⟨_, rfl⟩
  have hemit : Run.emits counter E rho (rho.proposerOf s) o s := by
    refine ⟨i, hi, ?_⟩
    change E.awake (rho.proposerOf s) (s : Time) = true at hpa
    rw [ho, ha]
    simp [Run.emittedAt, hpa, counter, height]
  refine ⟨chain (a + 1), ⟨hph, a + 1, rfl, ho ▸ hemit⟩, ?_⟩
  intro w hw
  have hdl : max (s : Time) E.t_GST + E.Δ = (s : Time) + 1 := by
    rw [hs.gst_zero, hΔ, max_eq_left hs0]
  obtain ⟨t', ht1, ht2, j, o', hj, ho'⟩ :=
    hs.partialSynchrony.broadcast _ hph o s hemit w hw (by rw [hdl]; exact hsh) rfl
  have ho'o : o' = o := ho'
  subst ho'o
  rw [hdl] at ht2
  -- `w` has height at least `a` before the delivery at `j`.
  have hge : a ≤ height (Run.stateBefore counter rho j) w := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · omega
    · rw [ha] at hpos
      obtain ⟨i', hi'i, o₁, t'', hi', hpay, hlt, hle⟩ := accept_source rho _ i hpos
      rw [← ha] at hpay hlt hle
      have ht''s : t'' < s := deliver_time_lt_tick hsched hi' hi hi'i
      have hi'j : i' < j :=
        index_lt_of_time_lt hsched hi' hj (show t'' < t' from lt_of_lt_of_le ht''s ht1)
      by_cases hproc : counter.processed (Run.stateBefore counter rho (i' + 1) w) o₁ = true
      · have h1 := of_decide_eq_true hproc
        rw [hpay] at h1
        exact le_trans h1 (stateBefore_mono rho hi'j w)
      · have hacc : Run.acceptsAt counter rho i' (rho.proposerOf s) o₁ t'' :=
          ⟨⟨o₁, hi', rfl⟩, decide_eq_false (by rw [hpay]; exact not_le.mpr hlt),
            decide_eq_true (by rw [hpay]; exact hle)⟩
        have ht''0 : 0 ≤ t'' := (hsched.in_horizon _ (List.mem_of_getElem? hi')).1
        have hdl' : max t'' E.t_GST + E.Δ = t'' + 1 := by
          rw [hs.gst_zero, hΔ, max_eq_left ht''0]
        obtain ⟨t₃, _, h32, j', hacc'⟩ :=
          hs.partialSynchrony.relay _ hph i' o₁ t'' hacc w hw (by simpa using hproc)
            (by rw [hdl']; linarith) rfl
        rw [hdl'] at h32
        obtain ⟨o₂, hj', ho₂⟩ := hacc'
        have ho₂' : o₂ = o₁ := ho₂
        subst ho₂'
        have hj'j : j' < j :=
          index_lt_of_time_lt hsched hj' hj
            (show t₃ < t' by have := Int.add_one_le_iff.mpr ht''s; linarith)
        have hd : a ≤ height (Run.stateBefore counter rho j') w + 1 := by
          have hdep := hs.execution.deps j' w o₂ t₃ hj'
          simp only [counter, decide_eq_true_eq] at hdep
          rw [hpay] at hdep
          exact hdep
        have h1 : a ≤ height (Run.stateBefore counter rho (j' + 1)) w := by
          have hval : height (Run.stateBefore counter rho (j' + 1)) w =
              counter.process (height (Run.stateBefore counter rho j') w) o₂ := by
            unfold height
            rw [stateBefore_succ hj', step_deliver_self]
          by_cases he : o₂.payload = height (Run.stateBefore counter rho j') w + 1
          · rw [hval, process_of_eq he]
            exact hd
          · rw [hval, process_of_ne he]
            rw [hpay] at he
            exact Nat.lt_succ_iff.mp (lt_of_le_of_ne hd he)
        exact le_trans h1 (stateBefore_mono rho hj'j w)
  -- The delivery at `j` moves `w` to at least `a + 1`.
  have hafter : a + 1 ≤ height (Run.stateBefore counter rho (j + 1)) w := by
    have hpay : o'.payload = a + 1 := by rw [ho]
    have hval : height (Run.stateBefore counter rho (j + 1)) w =
        counter.process (height (Run.stateBefore counter rho j) w) o' := by
      unfold height
      rw [stateBefore_succ hj, step_deliver_self]
    rw [hval]
    rcases Nat.eq_or_lt_of_le hge with heq | hlt
    · rw [← heq, process_of_eq hpay]
    · exact le_trans hlt (process_ge _ o')
  have hread := stateBefore_le_readAt hsched hj (show t' ≤ (s : Time) + 1 by linarith) w
  exact chain_preceq (le_trans hafter hread)

/-- The trigger slot `s = (max H 2).toNat` is at least `H` and positive, and
its deadline `s + 1` is the horizon `N = s + 1` of the run (I2: the trigger
is late, not at slot 1). -/
private theorem slot_late (H : Time) :
    H ≤ ((max H 2).toNat : Time) ∧ (0 : Time) < ((max H 2).toNat : Time) ∧
      ((max H 2).toNat : Time) + 1 ≤ (((max H 2).toNat + 1 : Nat) : Time) := by
  refine ⟨le_trans (le_max_left _ _) (Int.self_le_toNat _), ?_, by push_cast; exact le_rfl⟩
  exact lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) (Int.self_le_toNat _))

def certIncluded : Cert includedConfirmed counterInst where
  const := (1 : Time)
  valid := zero_le_one
  inhabited := by
    intro H
    obtain ⟨hH, hpos, hdl⟩ := slot_late H
    refine ⟨⟨Fin (Nat.succ 0), inferInstance, inferInstance⟩,
      ⟨counterEnv 0, canonical 0 ((max H 2).toNat + 1)⟩, (0 : Time), rfl, ?_,
      canonical_sleepy 0 ((max H 2).toNat + 1), (max H 2).toNat, hpos, hH,
      ⟨Finset.mem_univ _, rfl⟩, hdl⟩
    change H ≤ (((max H 2).toNat + 1 : Nat) : Time)
    push_cast
    linarith
  proof := by
    intro W x hΔ t₀ hs
    exact counter_included W x.E hΔ x.rho t₀ hs

/-- Counter passes the core floor at the shared delay `D = 1`: it is the
first candidate. -/
noncomputable def candidate : Candidate counterInst where
  shared := (1 : Time)
  valid := zero_le_one
  certs := by
    classical
    intro e he
    exact if h1 : e = ⟨safeConfirmed, fun _ => ()⟩ then
        (by subst h1; exact ⟨certSafeConfirmed, rfl⟩)
      else if h2 : e = ⟨safeStable, fun _ => ()⟩ then
        (by subst h2; exact ⟨certSafeStable, rfl⟩)
      else if h3 : e = ⟨prefixOrder, fun _ => ()⟩ then
        (by subst h3; exact ⟨certPrefix, rfl⟩)
      else (by
        have h4 : e = ⟨includedConfirmed, fun D => D⟩ := by
          rcases List.mem_cons.1 he with h | he; · exact absurd h h1
          rcases List.mem_cons.1 he with h | he; · exact absurd h h2
          rcases List.mem_cons.1 he with h | he; · exact absurd h h3
          exact List.mem_singleton.1 he
        subst h4; exact ⟨certIncluded, rfl⟩)

/-- Review Focus 3: every certificate of Counter's candidate is at the
projection of the one shared delay. -/
example (e : Profile.Entry ClaimDomain.v1 Time) (he : e ∈ core.entries) :
    (candidate.certs e he).1.const = e.share candidate.shared :=
  (candidate.certs e he).2

end AvailableChain.Registry.Counter

end
