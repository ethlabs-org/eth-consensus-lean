module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.RunBlocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Accountable

public section

/-! # Goldilocks Refinement: the engine agrees with the simulating trace

The engine's events are the trace's groups, its node states agree with the trace's states,
and it releases and relays what the trace signs, emits and admits. `Simulation` assembles
these correspondence facts into `EngineSimulatesNode`. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload blockVotes)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-! ## `Simulates`: the engine agrees with the trace -/

/-- Every labelled node cut lies in the range of some engine event. -/
theorem simTrace_covered :
    ∀ k, (simTrace S rho hn).label k ≠ none →
      ∃ i < rho.events.length, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) := by
  intro k hk
  rw [simTrace_label] at hk
  have hlt : k < (allCuts S rho hn).length := by
    by_contra h
    rw [List.getElem?_eq_none_iff.mpr (by omega)] at hk
    exact hk rfl
  obtain ⟨i, hi, h1, h2, -⟩ := allCuts_getElem? S rho hn k hlt
  exact ⟨i, hi, h1, h2⟩

/-- The node state inside the shape's state is the trace's state at the mapped cut (by induction
on the events, from `node_of_tick_public`, `node_of_tick_other`, `node_of_deliver`,
`node_of_restart` and `state_of_other`). -/
theorem simTrace_state (hv : rho.ExecutionValid) :
    ∀ v ∈ rho.honest, ∀ i ≤ rho.events.length,
      (stateAt S rho hn v i).node =
        (simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i) := by
  intro v hv' i
  induction i with
  | zero =>
    intro _
    rw [cutMap_zero]
    exact (congrArg (·.node) (stateAt_zero S rho hn v)).trans
      (simTrace_init_eq S rho hn (rho.ownKey v)).symm
  | succ i ih =>
    intro hi
    have hi' : i < rho.events.length := by omega
    have ih := ih (by omega)
    have he : rho.events[i]? = some rho.events[i] := List.getElem?_eq_getElem hi'
    rw [cutMap_succ]
    by_cases hne : rho.events[i].node ≠ v
    · rw [state_of_other S rho hn v i _ he hne]
      refine ih.trans (state_of_block_ne S rho hn _ (fun k hk r hr => ?_)).symm
      rw [allCuts_getElem?_add S rho hn i k hi' hk] at hr
      obtain ⟨hnode, -, -⟩ := mem_eventCuts S rho hn he (List.mem_of_getElem? hr)
      rw [hnode]
      exact fun h => hne (rho.key.symm.injective h)
    rw [not_not] at hne
    have hcut : ∀ k < (eventCuts S rho hn i).length,
        (allCuts S rho hn)[cutMap S rho hn i + k]? = (eventCuts S rho hn i)[k]? :=
      fun k hk => allCuts_getElem?_add S rho hn i k hi' hk
    cases hev : rho.events[i] with
    | tick w t =>
      rw [hev] at he hne
      simp only [Model.Event.node] at hne
      subst hne
      by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
      · rw [eventCuts_tick_public S rho hn i w t he hp] at hcut ⊢
        rw [node_of_tick_public S rho hn hv w hv' i t he hp]
        exact (state_of_group S rho hn _ _ hcut ih.symm).symm
      · rw [eventCuts_tick_other S rho hn i w t he hp, List.length_nil, Nat.add_zero,
          node_of_tick_other S rho hn hv w hv' i t he hp]
        exact ih
    | deliver w o t =>
      rw [hev] at he hne
      simp only [Model.Event.node] at hne
      subst hne
      rw [eventCuts_deliver S rho hn i w o t he] at hcut ⊢
      rw [node_of_deliver S rho hn hv w hv' i o t he]
      exact (state_of_deliverRecs S rho hn _ _ _ _ _ _ _ hcut ih.symm).symm
    | restart w t =>
      rw [hev] at he hne
      simp only [Model.Event.node] at hne
      subst hne
      rw [eventCuts_restart S rho hn i w t he] at hcut ⊢
      rw [node_of_restart S rho hn hv w hv' i t he]
      exact (state_of_group S rho hn _ _ hcut ih.symm).symm

/-- An engine tick of an honest node at a public time is the node's tick with the engine's input,
one group. -/
theorem simTrace_tick_public_group (hv : rho.ExecutionValid) :
    ∀ v ∈ rho.honest, ∀ i t, rho.events[i]? = some (.tick v t) →
      (S.params (pubOf E) hn).toParams.IsPublic t →
        (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho)
            (rho.ownKey v) (cutMap S rho hn i) t
            (.tick (encodeTxs (Model.mempool rho.inbox v t))) ∧
          cutMap S rho hn (i + 1) = cutMap S rho hn i +
            (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
            ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t
            (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2.length := by
  intro v hv' i t he hp
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  rw [cutMap_succ, eventCuts_tick_public S rho hn i v t he hp]
  have h0 := (simTrace_state S rho hn hv v hv' i hi.le).symm
  have hne := exec_tick_ne_nil (runProposer S rho hn) (digestOf S rho)
    (rho.ownKey v) (stateAt S rho hn v i).node t
    (encodeTxs (Model.mempool rho.inbox v t))
  have hcut : ∀ k < (groupRecs (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node t
      (Nat.pair i 0) (.tick (encodeTxs (Model.mempool rho.inbox v t)))).length,
      (allCuts S rho hn)[cutMap S rho hn i + k]? =
        (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t))))[k]? := fun k hk => by
    rw [← eventCuts_tick_public S rho hn i v t he hp] at hk ⊢
    exact allCuts_getElem?_add S rho hn i k hi hk
  have huniq : ∀ k, (simTrace S rho hn).event k = Nat.pair i 0 → cutMap S rho hn i ≤ k ∧
      k < cutMap S rho hn i + (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t)))).length := fun k hk => by
    have := range_of_event S rho hn hi hk
    rwa [cutMap_succ, eventCuts_tick_public S rho hn i v t he hp] at this
  obtain ⟨hG, hlen⟩ :=
    groupAt_of_group S rho hn (runProposer S rho hn) (digestOf S rho) hcut h0 hne huniq
  exact ⟨hG, congrArg (cutMap S rho hn i + ·) hlen⟩

/-- An honest node awake at a public time (from `0` on) ticks there. -/
theorem simTrace_tick_of_awake (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ t, 0 ≤ t → (S.params (pubOf E) hn).toParams.IsPublic t →
      (simTrace S rho hn).awake y t →
      ∃ j, (simTrace S rho hn).TickAt (runProposer S rho hn) (digestOf S rho) y j t := by
  intro y hy t ht0 hp hw
  obtain ⟨hwE, -, hth⟩ := (awake_iff' S rho hn y t).mp hw
  obtain ⟨i, he⟩ := List.mem_iff_getElem?.mp (hv.tick_total _ hy t ht0 hth hwE)
  obtain ⟨hg, -⟩ := simTrace_tick_public_group S rho hn hv _ hy i t he hp
  rw [ownKey_key] at hg
  exact ⟨_, _, hg⟩

/-- An engine tick at a non-public time has no cut. -/
theorem simTrace_tick_other (_hv : rho.ExecutionValid) :
    ∀ v ∈ rho.honest, ∀ i t, rho.events[i]? = some (.tick v t) →
      ¬ (S.params (pubOf E) hn).toParams.IsPublic t →
        cutMap S rho hn (i + 1) = cutMap S rho hn i := by
  intro v _ i t he hp
  rw [cutMap_succ, eventCuts_tick_other S rho hn i v t he hp, List.length_nil, Nat.add_zero]

/-- An engine delivery to an honest node is the groups of the canonical objects it delivers. -/
theorem simTrace_deliver (hv : rho.ExecutionValid) :
    ∀ v ∈ rho.honest, ∀ i o t, rho.events[i]? = some (.deliver v o t) →
      DeliverSeq (runProposer S rho hn) (simTrace S rho hn) (digestOf S rho)
        (Model.digests rho.hash o) (rho.ownKey v) t
        (delivered (S.params (pubOf E) hn) o) (cutMap S rho hn i) (cutMap S rho hn (i + 1)) := by
  intro v hv' i o t he
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  rw [cutMap_succ, eventCuts_deliver S rho hn i v o t he]
  refine deliverSeq_of_recs S rho hn (runProposer S rho hn) (digestOf S rho)
    _ _ _ 0 _ (fun k hk => ?_)
    (simTrace_state S rho hn hv v hv' i hi.le).symm (fun k s hk _ => ?_)
  · rw [← eventCuts_deliver S rho hn i v o t he] at hk ⊢
    exact allCuts_getElem?_add S rho hn i k hi hk
  · have := range_of_event S rho hn hi hk
    rwa [cutMap_succ, eventCuts_deliver S rho hn i v o t he] at this

/-- An engine restart of an honest node is the node's restart group. -/
theorem simTrace_restart (hv : rho.ExecutionValid) :
    ∀ v ∈ rho.honest, ∀ i t, rho.events[i]? = some (.restart v t) →
      (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho)
        (rho.ownKey v) (cutMap S rho hn i) t .restart ∧
        cutMap S rho hn (i + 1) = cutMap S rho hn i +
          (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
          ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t .restart).2.length := by
  intro v hv' i t he
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  rw [cutMap_succ, eventCuts_restart S rho hn i v t he]
  have h0 := (simTrace_state S rho hn hv v hv' i hi.le).symm
  have hne := exec_restart_ne_nil (runProposer S rho hn) (digestOf S rho)
    (rho.ownKey v) (stateAt S rho hn v i).node t
  have hcut : ∀ k < (groupRecs (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node t
      (Nat.pair i 0) .restart).length,
      (allCuts S rho hn)[cutMap S rho hn i + k]? =
        (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0) .restart)[k]? := fun k hk => by
    rw [← eventCuts_restart S rho hn i v t he] at hk ⊢
    exact allCuts_getElem?_add S rho hn i k hi hk
  have huniq : ∀ k, (simTrace S rho hn).event k = Nat.pair i 0 → cutMap S rho hn i ≤ k ∧
      k < cutMap S rho hn i + (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0) .restart).length := fun k hk => by
    have := range_of_event S rho hn hi hk
    rwa [cutMap_succ, eventCuts_restart S rho hn i v t he] at this
  obtain ⟨hG, hlen⟩ :=
    groupAt_of_group S rho hn (runProposer S rho hn) (digestOf S rho) hcut h0 hne huniq
  exact ⟨hG, congrArg (cutMap S rho hn i + ·) hlen⟩

/-- An honest node awake in the trace is awake in the environment, within `[0, horizon]`,
by the canonical observation clamp; unlabelled filler lies beyond that interval. -/
theorem simTrace_awake_of (_hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ t, (simTrace S rho hn).awake y t →
      E.awake (rho.key y) t = true ∧ 0 ≤ t ∧ t ≤ rho.horizon := by
  intro y _ t hw
  exact (awake_iff' S rho hn y t).mp hw

/-- An honest node's signings in the simulating trace are pairwise not slashable (`non_framing`
over the trace, a Goldilocks run). -/
private theorem simTrace_nonFraming
    (hrun : GoldilocksRun (runProposer S rho hn)
      (digestOf S rho) (honestKeys S rho) (simTrace S rho hn))
    {v : V} (hv' : v ∈ rho.honest) :
    ∀ k k' a b, (simTrace S rho hn).SignAt (rho.ownKey v) k a →
      (simTrace S rho hn).SignAt (rho.ownKey v) k' b → ¬ FG.slashable a b :=
  Regimes.non_framing _ _ _ _ _ _ hrun (rho.ownKey v)
    (by change rho.key (rho.ownKey v) ∈ rho.honest; rw [ownKey_key']; exact hv')

/-- The engine's Goldilocks state at a delivery: at the delivery's time, with the own key. -/
private theorem deliver_state (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {o : (Model.protoOf (compiled (family S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) :
    (stateAt S rho hn v i).now = t ∧ (stateAt S rho hn v i).self = rho.ownKey v :=
  ⟨(now_eq_lastClock S rho hn hv v i).trans (lastClock_deliver S rho hv he),
    stateAt_self S rho hn v i⟩

/-- A cut of a delivery to an honest node: its delivered object is queued by the delivery's
`process` (`process_relay`) and relayed by the delivery's gossip at its own time
(`deliver_relays`), as a carried object of a released relay wrapper. -/
theorem relays_of_cut (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)} {k : Nat}
    (hnode : (simTrace S rho hn).node k = y) (hl : (simTrace S rho hn).label k ≠ none)
    (hdel : ∀ r : CutRec (S.params (pubOf E) hn) (S.ro _), (allCuts S rho hn)[k]? = some r →
      (r.pos = 0 ∧ ∃ ℓ, r.label = .fg ℓ) ∨ ∃ ℓ m, r.label = .ac ℓ ∧ ℓ.call = .message m) :
    ∃ r : CutRec (S.params (pubOf E) hn) (S.ro _),
      (simTrace S rho hn).label k = some r.label ∧ (simTrace S rho hn).post k = r.post ∧
      ∀ x, ((∃ B, r.label = .fg (.block B true) ∧ x = blockObj (S.params (pubOf E) hn) B) ∨
          (∃ a, r.label = .fg (.attestation a) ∧ x = attObj a)) →
        ∃ cs, x ∈ cs ∧ rho.releases (rho.key y) (.mk .none (.data .relay) cs)
          ((simTrace S rho hn).time k) := by
  obtain ⟨r, i, ev, hr, he, -, -, hidx, hn', ht, -, hlab⟩ := simTrace_cut S rho hn hl
  have hmem := List.mem_of_getElem? hidx
  obtain ⟨v, o, t, rfl⟩ := eq_deliver_of_cut S rho hn he hmem (hdel r hr)
  simp only [Model.Event.node, Model.Event.time] at hn' ht
  have hkey : v = rho.key y := key_of_ownKey S rho (hn'.symm.trans hnode)
  subst hkey
  refine ⟨r, hlab, by rw [simTrace_post, hr]; rfl, fun x hx => ?_⟩
  rw [ht]
  rw [eventCuts_deliver S rho hn i _ o t he] at hmem
  obtain ⟨hnow, hself⟩ := deliver_state S rho hn hv he
  obtain ⟨h1, -, h3⟩ := (process_relay (runProposer S rho hn)
    (digestOf S rho) (Model.digests rho.hash o) t i
    (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn _ i) 0 hnow).2.2.2 r
    (by rw [hself]; exact hmem)
  have hq : x ∈
      (process (stateAt S rho hn (rho.key y) i) o (Model.digests rho.hash o)).relayBuf := by
    rcases hx with ⟨B, hB, rfl⟩ | ⟨a, ha, rfl⟩
    · exact h1 B hB
    · exact h3 a ha
  obtain ⟨cs, hxcs, hrel⟩ := deliver_relays S rho hn he hq
  exact ⟨cs, hxcs, i, Or.inr ⟨o, he⟩, hrel⟩

/-- The engine releases an honest node's own block at the tick that proposes it (the proposal
duty's candidate is `blockObj` of the block, `releasable` by `proposal_releasable`). -/
theorem simTrace_block_released (hv : rho.ExecutionValid)
    (hrun : GoldilocksRun (runProposer S rho hn)
      (digestOf S rho) (honestKeys S rho) (simTrace S rho hn)) :
    ∀ y ∈ honestKeys S rho, ∀ k B, (simTrace S rho hn).OwnBlockAt y k B →
      rho.releases (rho.key y) (blockObj (S.params (pubOf E) hn) B)
        ((simTrace S rho hn).time k) := by
  rintro y _ k B ⟨⟨acc, hnode, hlab⟩, hpos⟩
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, -, he, -, -, hidx, hn', ht, hp', hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .fg (.block B acc) := Option.some.inj (hlab'.symm.trans hlab)
  have hpos' : r.pos ≠ 0 := hp' ▸ hpos
  have hmem := List.mem_of_getElem? hidx
  have hkey : ev.node = rho.key y := key_of_ownKey S rho (hn'.symm.trans hnode)
  rw [ht, ← hkey]
  cases ev with
  | tick v t =>
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn i v t he hp] at hmem
      simp at hmem
    exact ⟨i, Or.inl he, (tick_releases S rho hn hv
      (hv.honest_only _ (List.mem_of_getElem? he)) he hp
      (simTrace_nonFraming S rho hn hrun (hv.honest_only _ (List.mem_of_getElem? he)))
      r hmem).1 B acc hrl hpos'⟩
  | deliver v o t =>
    exfalso
    rw [eventCuts_deliver S rho hn i v o t he] at hmem
    obtain ⟨o', e, st', _, hce, kk, hk, hlabk, hposk⟩ :=
      mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hmem
    exact hpos' (hposk.trans
      (pos_of_block_cut _ _ _ _ _ (canonEvent_ne_tick hce) hk (hlabk.symm.trans hrl)))
  | restart v t =>
    exfalso
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨kk, hk, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨-, -, -, hposk, hlabk⟩ := getElem_groupRecs _ _ _ _ _ _ _ kk hk
    have hk' := lt_of_lt_of_eq hk (length_groupRecs _ _ _ _ _ _ _)
    exact hpos' (hposk.trans (pos_of_block_cut _ _ _ _ _ (e := .restart) (fun x h => by cases h)
      hk' (hlabk.symm.trans hrl)))

/-- The engine releases an honest node's vote at its emission time: the tick's trailing polls
or the delivery's poll. A restart at its own time emits no vote. -/
theorem simTrace_vote_released (hv : rho.ExecutionValid)
    (hrun : GoldilocksRun (runProposer S rho hn)
      (digestOf S rho) (honestKeys S rho) (simTrace S rho hn)) :
    ∀ y ∈ honestKeys S rho, ∀ k m, (simTrace S rho hn).EmitAt y k m →
      ReleasedFrom S rho (rho.key y) (voteObj m) ((simTrace S rho hn).time k) := by
  rintro y _ k m ⟨ℓ, ⟨hnode, hlab⟩, em, hem, rfl⟩
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, -, he, -, -, hidx, hn', ht, -, hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .ac ℓ := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  have hkey : ev.node = rho.key y := key_of_ownKey S rho (hn'.symm.trans hnode)
  rw [ht, ← hkey]
  cases ev with
  | tick v t =>
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn i v t he hp] at hmem
      simp at hmem
    exact ⟨i, Or.inl he, (tick_releases S rho hn hv
      (hv.honest_only _ (List.mem_of_getElem? he)) he hp
      (simTrace_nonFraming S rho hn hrun (hv.honest_only _ (List.mem_of_getElem? he)))
      r hmem).2.1 ℓ hrl em hem⟩
  | deliver v o t =>
    have hm := List.mem_of_getElem? he
    have ht0 := (hv.in_horizon _ hm).1
    have hnow : (stateAt S rho hn v i).now = t :=
      (now_eq_lastClock S rho hn hv v i).trans (lastClock_of_deliver S rho hv v he)
    rw [eventCuts_deliver S rho hn i v o t he] at hmem
    have hmem' := hmem
    rw [← stateAt_self S rho hn v i] at hmem'
    obtain ⟨hb, hval⟩ := (process_outbox (runProposer S rho hn) (digestOf S rho)
      (Model.digests rho.hash o) t i _ (stateAt S rho hn v i) 0 hnow).2
      r hmem' ℓ hrl em hem
    have hpre : OneVote t (stateAt S rho hn v i) := by
      rcases (outbox_inv S rho hn hv v (hv.honest_only _ hm) i).2 with h | h
      · exact absurd h (not_lastRestart_deliver S rho hv he)
      · rwa [hnow] at h
    have hproc := process_oneVote (digestOf S rho) (Model.digests rho.hash o) ht0
      (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v i) hnow hpre
    have hone : (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox =
        [Body.vote (encodeVote em.msg)] := by
      have hlen := ((atMostOneVote_iff _).mp hproc.atMost).2
      match hq : (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox with
      | [] => change _ ∈ (process _ _ _).outbox at hb; rw [hq] at hb; cases hb
      | [b] =>
        change _ ∈ (process _ _ _).outbox at hb
        rw [hq, List.mem_singleton] at hb
        rw [hb]
      | _ :: _ :: _ =>
        change (process _ _ _).outbox.length ≤ 1 at hlen
        rw [hq] at hlen
        simp at hlen
    have hobj : voteObj em.msg = pollObj S rho v (Body.vote (encodeVote em.msg)) := by
      unfold voteObj pollObj
      rw [hval, stateAt_self]
      rfl
    rw [hobj]
    refine ⟨i, Or.inr ⟨o, he⟩, ?_⟩
    simp only [Model.Run.releasesAt, he]
    unfold Model.Run.deliver
    rw [deliverDuties_eq S t ht0]
    refine List.mem_append_left _ ?_
    erw [Model.Run.runDuties_cons]
    refine List.mem_append_left _ ?_
    apply dutyStep_poll_rel S rho hn v _ _ (poll_selected S rho hv v)
    · change (pollPre (process (stateAt S rho hn v i) o
        (Model.digests rho.hash o))).outbox.head? = some _
      rw [pollPre_eq]
      have hf : (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).fgDue = false :=
        (process_fgDue _ _ _).trans (fgDue_eq_false S rho hn v i)
      rw [hf]
      simp only [Bool.false_eq_true, ite_false, hone]
      rfl
    · exact protects_of_not_att S _ _ _ (fun k w h => by cases h)
  | restart v t =>
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨kk, hk, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨-, -, -, -, hlabk⟩ := getElem_groupRecs _ _ _ _ _ _ _ kk hk
    have hk' := lt_of_lt_of_eq hk (length_groupRecs _ _ _ _ _ _ _)
    have hcut := List.getElem_mem hk'
    rw [← hlabk, hrl] at hcut
    have hval := emits_val_of_mem_exec _ _ _ _ _ _ hcut em hem
    have hb : Body.vote (encodeVote em.msg) ∈ (stateAt S rho hn v (i + 1)).outbox := by
      rw [stateAt_succ_restart S rho hn he]
      exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨_, hcut, by simpa using ⟨em, hem, rfl⟩⟩)
    have hobj : @voteObj (pubOf E).n em.msg = Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (Body.vote (encodeVote em.msg))) [] := by
      unfold voteObj
      rw [show em.msg.val = rho.ownKey v from hval]
    rw [hobj]
    exact releasedFrom_of_pending S rho hn hv he hb

/-- The engine releases an honest node's attestation at its signing time (queued by `fgUpdate`,
released by the tick's last poll steps; `tick_releases`, `Release`). -/
theorem simTrace_att_released (hv : rho.ExecutionValid)
    (hrun : GoldilocksRun (runProposer S rho hn)
      (digestOf S rho) (honestKeys S rho) (simTrace S rho hn)) :
    ∀ y ∈ honestKeys S rho, ∀ k a, (simTrace S rho hn).SignAt y k a →
      ReleasedFrom S rho (rho.key y) (attObj a) ((simTrace S rho hn).time k) := by
  rintro y _ k a ⟨src, hnode, hlab⟩
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, -, he, -, -, hidx, hn', ht, -, hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .fg (.attest src (some a)) := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  have hkey : ev.node = rho.key y := key_of_ownKey S rho (hn'.symm.trans hnode)
  rw [ht, ← hkey]
  cases ev with
  | tick v t =>
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn i v t he hp] at hmem
      simp at hmem
    exact ⟨i, Or.inl he, (tick_releases S rho hn hv
      (hv.honest_only _ (List.mem_of_getElem? he)) he hp
      (simTrace_nonFraming S rho hn hrun (hv.honest_only _ (List.mem_of_getElem? he)))
      r hmem).2.2 src a hrl⟩
  | deliver v o t =>
    exfalso
    rw [eventCuts_deliver S rho hn i v o t he] at hmem
    obtain ⟨o', e, st', _, hce, kk, hk, hlabk, -⟩ := mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hmem
    have hcut := List.getElem_mem hk
    rw [← hlabk, hrl] at hcut
    obtain ⟨x, rfl⟩ := Compose.signed_only_in_ticks _ _ _ st' t e src a hcut
    exact canonEvent_ne_tick hce x rfl
  | restart v t =>
    exfalso
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨kk, hk, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨-, -, -, -, hlabk⟩ := getElem_groupRecs _ _ _ _ _ _ _ kk hk
    have hk' := lt_of_lt_of_eq hk (length_groupRecs _ _ _ _ _ _ _)
    have hcut := List.getElem_mem hk'
    rw [← hlabk, hrl] at hcut
    obtain ⟨x, hx⟩ := Compose.signed_only_in_ticks _ _ _ _ t .restart src a hcut
    cases hx

/-- An honest node relays a block it accepts from the wire, at the delivery's own time
(`relays_of_cut`). -/
theorem simTrace_block_relayed (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ k B, (simTrace S rho hn).AcceptAt y k B →
      (simTrace S rho hn).pos k = 0 →
        RelayedFrom S rho (rho.key y) (blockObj (S.params (pubOf E) hn) B)
          ((simTrace S rho hn).time k) := by
  rintro y _ k B ⟨hnode, hlab⟩ hpos
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, hrl, -, hrel⟩ := relays_of_cut S rho hn hv hnode hl fun r hr => Or.inl
    ⟨by rw [simTrace_pos, hr] at hpos; exact hpos, _,
      Option.some.inj ((by rw [simTrace_label, hr]; rfl : _ = some r.label).symm.trans hlab)⟩
  obtain ⟨cs, hx, hcs⟩ := hrel _ (Or.inl ⟨B, Option.some.inj (hrl.symm.trans hlab), rfl⟩)
  exact ⟨cs, hx, hcs⟩

/-- An honest node relays an attestation it receives from the wire. -/
theorem simTrace_att_relayed (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ k a, (simTrace S rho hn).AttCallAt y k a →
      (simTrace S rho hn).pos k = 0 →
        RelayedFrom S rho (rho.key y) (attObj a) ((simTrace S rho hn).time k) := by
  rintro y _ k a ⟨hnode, hlab⟩ hpos
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, hrl, -, hrel⟩ := relays_of_cut S rho hn hv hnode hl fun r hr => Or.inl
    ⟨by rw [simTrace_pos, hr] at hpos; exact hpos, _,
      Option.some.inj ((by rw [simTrace_label, hr]; rfl : _ = some r.label).symm.trans hlab)⟩
  obtain ⟨cs, hx, hcs⟩ := hrel _ (Or.inr ⟨a, Option.some.inj (hrl.symm.trans hlab), rfl⟩)
  exact ⟨cs, hx, hcs⟩

end Consensus.Goldilocks.Refinement

end
