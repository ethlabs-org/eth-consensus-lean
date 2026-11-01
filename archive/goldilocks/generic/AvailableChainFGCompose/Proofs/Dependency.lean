module
public import AvailableChainFGCompose.Statements.DependencyTrace

public section

namespace AvailableChain.FGCompose

section Retention
variable {State Body Origin Latest V : Type}
variable {H : FGHistoricalReads State Body}
variable {D : FGDependencyReads State Body Origin Latest}
variable {L : FGDependencyLeaf State Body Origin}
variable {Step : FGDependencyStepKind → V → State → State → Prop}
variable {restore : State → Time → State} {signs : State → State → Prop}

theorem dependency_effect_step (laws : FGDependencyStepLaws H D L Step restore signs)
    {kind x st st' b o} (step : Step kind x st st') (h : Effect H D st b o) :
    Effect H D st' b o := by
  rcases h with ⟨origin, pending | accepted | refused⟩
  · exact laws.pending_effect _ _ _ _ _ _ step pending
  · exact ⟨laws.origin_keep _ _ _ _ _ _ step origin,
      Or.inr (Or.inl (laws.accepted_keep _ _ _ _ _ step accepted))⟩
  · exact ⟨laws.origin_keep _ _ _ _ _ _ step origin,
      Or.inr (Or.inr (laws.refused_keep _ _ _ _ _ _ _ step refused))⟩

theorem dependency_effect_prefix (laws : FGDependencyStepLaws H D L Step restore signs)
    {x st st' b o} (steps : FGDependencySteps Step x st st') (h : Effect H D st b o) :
    Effect H D st' b o := by
  induction steps with
  | refl => exact h
  | tail _ _ step ih => exact dependency_effect_step laws step ih

private theorem dependency_accepted_prefix
    (laws : FGDependencyStepLaws H D L Step restore signs) {x a z b}
    (steps : FGDependencySteps Step x a z) (held : D.accepted a b) : D.accepted z b := by
  induction steps with
  | refl => exact held
  | tail _ _ step ih => exact laws.accepted_keep _ _ _ _ _ step ih

private theorem dependency_closed_child {st b o}
    (closed : dependencyClosed H D st) (effect : Effect H D st b o)
    (valid : D.validBody b)
    (checks : D.pending st b o → D.accepted st (H.parent b) →
      D.priorChecks st b ∧ D.timely st b)
    (parent : dependencyResolved H D st (H.parent b)) : dependencyResolved H D st b := by
  classical
  by_contra unresolved
  have pending := effect.2.resolve_right unresolved
  rcases parent with held | refused
  · exact closed (.retry b o pending valid (checks pending held).1
      (checks pending held).2 held unresolved)
  · exact closed (.inherit b o pending refused unresolved)

theorem dependency_refusal_descendants
    (stateLaws : FGDependencyStateLaws H D L) {st base target path}
    (chain : FGDependencyPath H base target path) (base_refused : dependencyRefused H D st base)
    (closed : dependencyClosed H D st)
    (parent_closed : ∀ b, D.accepted st b → D.accepted st (H.parent b))
    (valid : ∀ b ∈ base :: path, D.validBody b)
    (effects : ∀ b ∈ path, ∃ o, Effect H D st b o) : dependencyRefused H D st target := by
  induction chain with
  | root => exact base_refused
  | @snoc parent b path chain hp ih =>
    have pr := ih (fun c hc => valid c (by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ hc)))
      (fun c hc => effects c (List.mem_append_left _ hc))
    obtain ⟨o, eff⟩ := effects b (by simp)
    have parentMember : parent = base ∨ parent ∈ path := by
      induction chain with
      | root => exact Or.inl rfl
      | snoc => exact Or.inr (by simp)
    have notAccepted : ¬ D.accepted st b := by
      intro hb
      have hpv := valid parent (by simp only [List.mem_cons, List.mem_append]; tauto)
      exact stateLaws.accepted_refused_disjoint st parent hpv
        (hp ▸ parent_closed b hb) pr
    rcases eff.2 with pending | accepted | refused
    · by_contra noRefusal
      exact closed (.inherit b o pending (hp ▸ pr)
        (fun h => h.elim notAccepted noRefusal))
    · exact (notAccepted accepted).elim
    · exact refused

/-- Arrival inheritance and retained-child closure give the same durable refusal. -/
theorem dependency_arrival_order
    {Arrival : State → Body → Origin → State → Prop} {Notify : State → Body → State → Prop}
    (arrivalLaws : FGDependencyArrivalLeafLaws H D L Arrival Notify)
    {a z b o} (arrival : Arrival a b o z) (valid : D.validBody b)
    (parentFirst : dependencyRefused H D a (H.parent b)) : dependencyRefused H D z b :=
  (arrivalLaws.arrival_inherits a z b o arrival valid parentFirst).1

end Retention

section Trace
variable {In LeafIn V Body Row Latest : Type} [DecidableEq V]
variable {P : V2.ProtocolSpecD In} {Leaf : V2.ProtocolSpecD LeafIn}
variable {E : Generic.Env V} {rho : V2.D.Run V P} {x : V}
variable {H : FGHistoricalReads P.State Body} {W : FGDependencyWireReads P Body Row}
variable {D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest}
variable {L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object)}
variable {Step : FGDependencyStepKind → V → P.State → P.State → Prop}
variable {T : FGDependencyTrace P.State}
variable {F : FGDependencyDriver V Body P}
variable {Op : Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object}
variable {Arrival : P.State → Body → FGReceiptToken V P.Object → P.State → Prop}
variable {Notify : P.State → Body → P.State → Prop}
variable {leafState : P.State → Leaf.State} {leafWire : P.Object → Leaf.Object}
variable {Read : V → Nat → P.State → Prop}
variable (traceLaws : FGDependencyTraceLaws E rho x H W D L Step T
  F Op Arrival Notify leafState leafWire Read)
variable {restore : P.State → Time → P.State} {signs : P.State → P.State → Prop}
variable (stepLaws : FGDependencyStepLaws H D L Step restore signs)

include traceLaws stepLaws in
/-- Reconstruction is an ordinary metadata step and emits no signing duty. -/
theorem dependency_reconstruct_metadata {k t} (bound : k < T.length)
    (operation : Op k = .reconstruct t) :
    Step .ordinary x (T.state k) (T.state (k + 1)) ∧
    H.acceptedBlocks (T.state (k + 1)) = H.acceptedBlocks (T.state k) ∧
    ¬ signs (T.state k) (T.state (k + 1)) := by
  have step := traceLaws.step_kind k bound
  rw [operation] at step
  change Step .ordinary x (T.state k) (T.state (k + 1)) at step
  exact ⟨step, stepLaws.metadata_fg_eq _ _ _ _ step (by decide) (by decide),
    stepLaws.no_signing _ _ _ _ step⟩

theorem dependency_origin_same_receiver {b o} (origin : FGReceiptOrigin E rho H W x b o) :
    o.receiver = x ∧ rho.events[o.eventIndex]? = some (.deliver x o.wire o.receiptTime) :=
  ⟨origin.receiver_eq, origin.delivered⟩

include traceLaws in
private theorem dependency_trace_steps {i j : Nat} (hij : i ≤ j) (hj : j ≤ T.length) :
    FGDependencySteps Step x (T.state i) (T.state j) := by
  induction j, hij using Nat.le_induction with
  | base => exact .refl _
  | succ j hij ih =>
    obtain ⟨kind, step⟩ := traceLaws.micro_step j (by omega)
    exact .tail kind (ih (by omega)) step

include traceLaws stepLaws in
private theorem dependency_effect_between {i j b o} (hij : i ≤ j) (hj : j ≤ T.length)
    (effect : Effect H D (T.state i) b o) : Effect H D (T.state j) b o :=
  dependency_effect_prefix stepLaws (dependency_trace_steps traceLaws hij hj) effect

include traceLaws in
theorem dependency_origin_at_read {i st b o} (read : Read x i st)
    (origin : D.originAvailable st b o) :
    FGReceiptOrigin E rho H W x b o ∧ T.start o.eventIndex < T.readCut i := by
  obtain ⟨bound, eq, _⟩ := traceLaws.read_correspondence i st read
  exact traceLaws.origin_valid _ b o bound (eq ▸ origin)

include traceLaws in
/-- Completion starts at the actual entry boundary of the event which consumes the read. -/
theorem dependency_read_completion {i st} (read : Read x i st) :
    ∃ j e kind, rho.events[j]? = some e ∧
      dependencyReadRequired E F x (dependencyStateBefore E rho F x j) e kind ∧
      i = 4 * j + dependencyReadCode kind ∧
      T.entryCut j ≤ T.readCut i ∧ T.readCut i ≤ T.done j ∧
      FGDependencySteps Step x (T.state (T.entryCut j)) st ∧ dependencyClosed H D st := by
  obtain ⟨j, e, kind, event, required, index, _⟩ := (traceLaws.actual_read i st).mp read
  obtain ⟨lo, hi, _, steps⟩ := traceLaws.read_order j e kind event required
  obtain ⟨_, state_eq, closed⟩ := traceLaws.read_correspondence i st read
  subst i
  exact ⟨j, e, kind, event, required, rfl, lo, hi, state_eq ▸ steps, closed⟩

include traceLaws in
/-- A hook read consumes its executed command's cut, after the actual entry segment. -/
theorem dependency_hook_read_completion {j e index kind cut st}
    (event : rho.events[j]? = some e) (read : T.hookRead j index kind cut st) :
    T.entryCut j ≤ cut ∧ cut ≤ T.done j ∧ T.state cut = st ∧
    FGDependencySteps Step x (T.state (T.entryCut j)) st ∧ dependencyClosed H D st := by
  obtain ⟨r, member, _, rfl, rfl⟩ :=
    (traceLaws.hook_correspondence j e index kind cut st event).mp read
  have completed := traceLaws.hook_reads j e r event (List.mem_of_getElem? member)
  exact ⟨Nat.le_add_right _ _, completed⟩

include traceLaws in
private theorem dependency_accepted_origin_at_cut {cut b} (bound : cut ≤ T.length)
    (accepted : D.accepted (T.state cut) b) (nonGenesis : b ≠ L.genesis) : ∃ o,
    FGReceiptOrigin E rho H W x b o ∧
    W.proposalErase o.wire = some (H.erase b) ∧ W.decodedRows o.wire = W.bodyRows b := by
  have go : ∀ k, k ≤ T.length → D.accepted (T.state k) b → ∃ o,
      FGReceiptOrigin E rho H W x b o := by
    intro k
    induction k with
    | zero =>
      intro _ hb
      rw [traceLaws.initial] at hb
      exact (nonGenesis (traceLaws.initial_accepted b hb)).elim
    | succ k ih =>
      intro hk hb
      classical
      by_cases old : D.accepted (T.state k) b
      · exact ih (by omega) old
      · obtain ⟨o, leaf, _, _⟩ := traceLaws.origin_attribution k b (by omega) hb old
        exact ⟨o, (traceLaws.leaf_step k b o _ (by omega) leaf rfl).1⟩
  obtain ⟨o, ho⟩ := go _ bound accepted
  exact ⟨o, ho, ho.geometry, ho.rows⟩

include traceLaws in
theorem dependency_accepted_origin_bridge {i st b} (read : Read x i st)
    (accepted : D.accepted st b) (nonGenesis : b ≠ L.genesis) : ∃ o,
    FGReceiptOrigin E rho H W x b o ∧
    W.proposalErase o.wire = some (H.erase b) ∧ W.decodedRows o.wire = W.bodyRows b := by
  obtain ⟨bound, eq, _⟩ := traceLaws.read_correspondence i st read
  exact dependency_accepted_origin_at_cut traceLaws bound (eq ▸ accepted) nonGenesis

include traceLaws in
theorem dependency_hook_origin_at_read {j e index kind cut st b o}
    (event : rho.events[j]? = some e) (read : T.hookRead j index kind cut st)
    (origin : D.originAvailable st b o) :
    FGReceiptOrigin E rho H W x b o ∧ T.start o.eventIndex < cut := by
  obtain ⟨_, upper, eq, _⟩ := dependency_hook_read_completion traceLaws event read
  exact traceLaws.origin_valid cut b o
    (Nat.le_trans upper (traceLaws.finite_segment j e event).2) (eq ▸ origin)

include traceLaws in
theorem dependency_hook_accepted_origin_bridge {j e index kind cut st b}
    (event : rho.events[j]? = some e) (read : T.hookRead j index kind cut st)
    (accepted : D.accepted st b) (nonGenesis : b ≠ L.genesis) : ∃ o,
    FGReceiptOrigin E rho H W x b o ∧
    W.proposalErase o.wire = some (H.erase b) ∧ W.decodedRows o.wire = W.bodyRows b := by
  obtain ⟨_, upper, eq, _⟩ := dependency_hook_read_completion traceLaws event read
  exact dependency_accepted_origin_at_cut traceLaws
    (Nat.le_trans upper (traceLaws.finite_segment j e event).2) (eq ▸ accepted) nonGenesis

include traceLaws in
theorem dependency_drain_before_deadline {j wire t deadline}
    (receipt : rho.events[j]? = some (.deliver x wire t)) (strict : t < deadline) :
    dependencyClosed H D (T.state (T.done j)) ∧
    T.time (T.done j) = t ∧ dependencyStrictPrefix rho T deadline (T.done j) := by
  have segment := traceLaws.finite_segment j _ receipt
  exact ⟨traceLaws.event_drain j x wire t receipt,
    traceLaws.segment_time j _ _ receipt segment.1 (Nat.le_refl _),
    traceLaws.completion_cut j _ deadline receipt strict⟩

include traceLaws in
private theorem dependency_done_mono {i j : Nat} {ei ej : V2.Event V P.Object}
    (hi : rho.events[i]? = some ei) (hj : rho.events[j]? = some ej) (hij : i ≤ j) :
    T.done i ≤ T.done j := by
  rcases Nat.eq_or_lt_of_le hij with rfl | lt
  · exact Nat.le_refl _
  · exact Nat.le_trans (Nat.le_of_lt (traceLaws.event_order i j ei ej hi hj lt))
      (traceLaws.finite_segment j ej hj).1

include traceLaws stepLaws in
/-- Finite maxima use event indices. Equal timestamps do not identify event cuts. -/
private theorem dependency_latest_inputs (path : List Body) {entry deadline}
    {event : V2.Event V P.Object} (entry_event : rho.events[entry]? = some event)
    (entry_strict : event.time < deadline)
    (inputs : ∀ b ∈ path, ∃ j e o, rho.events[j]? = some e ∧ e.time < deadline ∧
      Effect H D (T.state (T.done j)) b o) :
    ∃ j e, rho.events[j]? = some e ∧ e.time < deadline ∧ entry ≤ j ∧
      ∀ b ∈ path, ∃ o, Effect H D (T.state (T.done j)) b o := by
  induction path with
  | nil => exact ⟨entry, event, entry_event, entry_strict, Nat.le_refl _, by simp⟩
  | cons b bs ih =>
    obtain ⟨j, e, hj, tj, ej, all⟩ := ih (fun c hc => inputs c (List.mem_cons_of_mem _ hc))
    obtain ⟨i, ei, o, hi, ti, effect⟩ := inputs b (by simp)
    by_cases le : i ≤ j
    · refine ⟨j, e, hj, tj, ej, ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨o, dependency_effect_between traceLaws stepLaws
          (dependency_done_mono traceLaws hi hj le)
          (traceLaws.finite_segment j e hj).2 effect⟩
      · exact all c hc
    · have ji : j ≤ i := by omega
      refine ⟨i, ei, hi, ti, Nat.le_trans ej ji, ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨o, effect⟩
      · obtain ⟨oc, ec⟩ := all c hc
        exact ⟨oc, dependency_effect_between traceLaws stepLaws
          (dependency_done_mono traceLaws hj hi ji)
          (traceLaws.finite_segment i ei hi).2 ec⟩

omit [DecidableEq V] in
private theorem dependency_path_closed {st target path}
    (chain : FGDependencyPath H L.genesis target path)
    (genesis : D.accepted st L.genesis) (closed : dependencyClosed H D st)
    (inputs : ∀ b ∈ path, (∃ o, Effect H D st b o) ∧ D.validBody b ∧
      ∀ o, D.pending st b o → D.accepted st (H.parent b) →
        D.priorChecks st b ∧ D.timely st b) : dependencyResolved H D st target := by
  induction chain with
  | root => exact Or.inl genesis
  | @snoc parent b path chain hp ih =>
    have parentDone := ih (fun c hc => inputs c (List.mem_append_left _ hc))
    obtain ⟨⟨o, effect⟩, valid, checks⟩ := inputs b (by simp)
    exact dependency_closed_child closed effect valid (checks o) (hp ▸ parentDone)

include traceLaws stepLaws in
/-- Strict completion uses the last required event, including the retained-only entry event.
No actual read before the deadline is a premise. Network production remains conditional. -/
theorem dependency_finite_path_resolved_before
    {Outstanding : P.Object → Time → Time → Prop}
    (delivery : FGDependencyDeliveryLaws E rho x H W D T F Outstanding)
    {target path entry tau wake} {event : V2.Event V P.Object}
    (chain : FGDependencyPath H L.genesis target path)
    (entry_event : rho.events[entry]? = some event) (entry_time : event.time = tau)
    (genesis : D.accepted (T.state 0) L.genesis)
    (gst : E.t_GST ≤ tau) (wake_le : wake ≤ tau)
    (awake : ∀ t, wake ≤ t → t ≤ tau + E.Δ → E.awake x t = true)
    (noRestart : ∀ (j : Nat) (t : Time), rho.events[j]? = some (.restart x t) →
      wake < t → tau + E.Δ < t)
    (horizon : tau + E.Δ ≤ rho.horizon)
    (checks : ∀ b ∈ path, D.validBody b ∧ ∀ k, k ≤ T.length →
      ∀ o, D.pending (T.state k) b o → D.accepted (T.state k) (H.parent b) →
        D.priorChecks (T.state k) b ∧ D.timely (T.state k) b)
    (inputs : ∀ b ∈ path,
      (∃ o, Effect H D (T.state (T.start entry)) b o) ∨
      (∃ sender wire sent, sender ∈ rho.honest ∧ dependencyEmits E rho F sender wire sent ∧
        W.decodeBody wire = some b ∧ sent < tau ∧ Outstanding wire sent wake)) :
    ∃ j k, k = T.done j ∧ entry ≤ j ∧ dependencyStrictPrefix rho T (tau + E.Δ) k ∧
      dependencyResolved H D (T.state k) target ∧ D.notified (T.state k) target ∧
      (D.accepted (T.state k) target → D.matching (D.latest (T.state k)) target →
        D.companionHeld (D.latest (T.state k)) target) := by
  have tau_strict : tau < tau + E.Δ := lt_add_of_pos_right tau E.Δ_pos
  have entry_strict : event.time < tau + E.Δ := entry_time ▸ tau_strict
  have gathered : ∀ b ∈ path, ∃ j e o, rho.events[j]? = some e ∧
      e.time < tau + E.Δ ∧ Effect H D (T.state (T.done j)) b o := by
    intro b hb
    rcases inputs b hb with ⟨o, retained⟩ | ⟨sender, wire, sent, honest, emit, decode, old, out⟩
    · have segment := traceLaws.finite_segment entry event entry_event
      exact ⟨entry, event, o, entry_event, entry_strict,
        dependency_effect_between traceLaws stepLaws segment.1 segment.2 retained⟩
    · have deadline : max (max sent E.t_GST) wake + E.Δ ≤ tau + E.Δ :=
        Int.add_le_add (max_le (max_le (le_of_lt old) gst) wake_le) (Int.le_refl E.Δ)
      obtain ⟨j, o, origin, index, strict, effect⟩ := delivery.old_send
        sender wire sent wake (tau + E.Δ) b honest emit decode (checks b hb).1 out
        (lt_trans old tau_strict) (le_trans wake_le (le_of_lt tau_strict))
        awake noRestart horizon deadline
      exact ⟨j, .deliver x o.wire o.receiptTime, o, index ▸ origin.delivered,
        lt_of_lt_of_le strict deadline, effect⟩
  obtain ⟨j, e, hj, tj, ej, effects⟩ := dependency_latest_inputs traceLaws stepLaws
    path entry_event entry_strict gathered
  have bound := (traceLaws.finite_segment j e hj).2
  have closed := traceLaws.entry_drain j e hj
  have base := dependency_accepted_prefix stepLaws
    (dependency_trace_steps traceLaws (Nat.zero_le (T.done j)) bound) genesis
  have resolved := dependency_path_closed chain base closed (fun b hb =>
    ⟨effects b hb, (checks b hb).1, (checks b hb).2 _ bound⟩)
  refine ⟨j, T.done j, rfl, ej, traceLaws.completion_cut j e _ hj tj, resolved, ?_, ?_⟩
  · by_contra missing
    exact closed (.notify target resolved missing)
  · intro accepted matching
    by_contra missing
    exact closed (.companion target accepted matching missing)

end Trace
end AvailableChain.FGCompose
end
