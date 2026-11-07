module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.EngineSteps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Provenance
import ConsensusLean.Lemmas.Model.Candidates
import ConsensusLean.Lemmas.Model.Protection

public section

/-! # Inverting actual attestation releases

The ordinary poll's signing provenance is node-local and already holds for growing faults.
Locate a released attestation's actual duty prefix, then reuse that provenance instead of
reconstructing a static global honest-origin invariant.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
private theorem duties_append_at (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (ds ds') :
    rho.runDuties v nd (ds ++ ds') =
      let r := rho.runDuties v nd ds
      let r' := rho.runDuties v r.1 ds'
      (r'.1, r.2 ++ r'.2) := by
  unfold Model.Run.runDuties
  rw [List.foldl_append]
  generalize ds.foldl _ _ = acc
  induction ds' generalizing acc with
  | nil => simp
  | cons d ds' ih =>
    dsimp only
    rw [List.foldl_cons, List.foldl_cons, ih]
    conv_rhs => rw [ih]
    simp only [List.append_assoc, List.nil_append]

omit [DecidableEq V] in
/-- A duty release comes from one actual prefix, not a replayed node handler. -/
private theorem release_duty_at (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (ds)
    {o} (ho : o ∈ (rho.runDuties v nd ds).2) :
    ∃ p d, ds[p]? = some d ∧
      o ∈ (rho.dutyStep v (rho.runDuties v nd (ds.take p)).1 d).2 := by
  induction ds using List.reverseRecOn with
  | nil => cases ho
  | append_singleton ds d ih =>
    rw [duties_append_at] at ho
    rcases List.mem_append.mp ho with ho | ho
    · obtain ⟨p, d', hp, ho⟩ := ih ho
      have hlt := (List.getElem?_eq_some_iff.mp hp).1
      refine ⟨p, d', ?_, ?_⟩
      · simpa [List.getElem?_append, hlt] using hp
      · simpa only [List.take_append_of_le_length (Nat.le_of_lt hlt)] using ho
    · exact ⟨ds.length, d, by simp,
        by simpa only [List.take_left, rho.runDuties_cons, rho.runDuties_nil,
          List.append_nil] using ho⟩

private theorem released_poll_at {v : V} {i p : Nat} {nd}
    (hc : EngineDutyCut S rho v i p nd) {d} {a : FG.Att (Fintype.card V)}
    (hd : (∃ t, rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
        ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some d) ∨
      ∃ t o, rho.events[i]? = some (.deliver v o t) ∧
        ((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t)[p]? = some d)
    (hr : attObj a ∈ (rho.dutyStep v nd d).2) :
    a.val = rho.ownKey v ∧ ∃ j q, EngineSignsAt S rho hn v j q a := by
  unfold Model.Run.dutyStep at hr
  split at hr
  · rename_i hsel
    obtain ⟨m, cs, hm, _, he⟩ := rho.mem_signedCandidate.mp
      (Model.releaseAll_subset _ _ _ _ _ hr)
    have he' := he
    change (Model.Obj.mk (.signed a.val (ShapeRole.poll : ShapeRole Empty))
      (.data (Body.att (encodeAtt a))) [] : Wire (Fintype.card V)) = _ at he'
    injection he' with hauth hmsg hcs
    subst m cs
    cases d with
    | act s k => exact k.elim
    | propose s hs =>
      have hh : (ShapeRole.poll : ShapeRole Empty) = .proposer s := by injection hauth
      cases hh
    | pollPropose t =>
      change _ ∈ (Option.map _ ((goldilocks S (pubOf E)).pollPropose nd.st.1 t).2).toList at hm
      simp only [goldilocks, dite_eq_left hn] at hm
      cases hm
    | poll t =>
      have hp : (poll (nd.st.1 hn) t).2 = some (.att (encodeAtt a), []) := by
        change _ ∈ (((goldilocks S (pubOf E)).pollBatch nd.st.1 t).2.map
          (fun (b, cs) => (Model.Msg.data b, cs))) at hm
        simp only [goldilocks, dite_eq_left hn] at hm
        change _ ∈ ((pollBatch (nd.st.1 hn) t).2.map
          (fun (b, cs) => (Model.Msg.data b, cs))) at hm
        obtain ⟨⟨b, cs⟩, hb, heq⟩ := List.mem_map.mp hm
        have hp := Prod.mk.inj heq
        have hb' := Model.Msg.data.inj hp.1
        have hcs' := hp.2
        subst b cs
        simp only [pollBatch, List.mem_append] at hb
        rcases hb with (hb | hb) | hb
        · exact Option.mem_toList.mp hb
        · obtain ⟨p, _, heq⟩ := List.mem_map.mp hb
          cases heq
        · obtain ⟨p, _, heq⟩ := List.mem_map.mp hb
          cases heq
      obtain ⟨b, j, q, heq, hval, hs⟩ := engine_poll_att_signed S rho hn hc hd hsel hp
      have hab : a = b := by
        have hh := congrArg (decodeAtt (Fintype.card V)) heq
        simpa only [decodeAtt_encodeAtt, Option.some.injEq] using hh
      subst b
      exact ⟨hval.trans (cut_self S rho hn hc), j, q, hs⟩
  · cases hr

omit [DecidableEq V] in
private theorem gossip_not_att_at (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (k : Fin (Fintype.card V)) (t : Time) (a : FG.Att (Fintype.card V)) :
    attObj a ∉ (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) rho.hash k nd
      (Model.gossipCandidates (Model.protoOf (compiled (goldilocks S)) E) nd.st t)).2 := by
  intro ha
  obtain ⟨mc, _, he⟩ := Model.mem_gossipCandidates.mp
    (Model.releaseAll_subset _ _ _ _ _ ha)
  have hh := congrArg Model.Obj.auth he
  cases hh

/-- Any actual attestation release has an actual engine signing. This is purely
node-local: it needs neither constant faults nor honesty after the sending event. -/
theorem released_att_signed_at {v : V} {i : Nat} {t : Time}
    (hs : rho.SendsAt v i t) {a : FG.Att (Fintype.card V)}
    (ha : attObj a ∈ rho.releasesAt i) :
    ∃ j q, EngineSignsAt S rho hn v j q a := by
  rcases hs with he | ⟨o, he⟩
  · simp only [Model.Run.releasesAt, he] at ha
    unfold Model.Run.tick at ha
    split at ha
    · rename_i hw
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨p, d, hd, hr⟩ := release_duty_at S rho v _ _ ha
        exact (released_poll_at S rho hn
          (.tick he hw (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hd).1))
          (Or.inl ⟨t, he, hw, hd⟩) hr).2
      · exact False.elim (gossip_not_att_at S rho _ _ t a ha)
    · cases ha
  · simp only [Model.Run.releasesAt, he, Model.Run.deliver] at ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨p, d, hd, hr⟩ := release_duty_at S rho v _ _ ha
      exact (released_poll_at S rho hn
        (.deliver he (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hd).1))
        (Or.inr ⟨t, o, he, hd⟩) hr).2
    · exact False.elim (gossip_not_att_at S rho _ _ t a ha)

omit [DecidableEq V] in
private theorem duties_closure_at (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (ds)
    (a : FG.Att (Fintype.card V))
    (ha : attObj a ∈ Model.closure (rho.runDuties v nd ds).1.seen) :
    attObj a ∈ Model.closure nd.seen ∨ attObj a ∈ (rho.runDuties v nd ds).2 := by
  induction ds using List.reverseRecOn with
  | nil => exact Or.inl ha
  | append_singleton ds d ih =>
    rw [duties_append_at] at ha ⊢
    change _ ∨ attObj a ∈ _ ++ (rho.dutyStep v (rho.runDuties v nd ds).1 d).2
    change attObj a ∈ Model.closure (rho.dutyStep v (rho.runDuties v nd ds).1 d).1.seen at ha
    unfold Model.Run.dutyStep at ha ⊢
    split at ha
    · rename_i hsel
      simp only [hsel, ↓reduceIte]
      let Q := fun o => o = attObj a →
        attObj a ∈ Model.closure (rho.runDuties v nd ds).1.seen ∨
          attObj a ∈ (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
            rho.hash (rho.ownKey v)
            ⟨((Model.protoOf (compiled (goldilocks S)) E).act (rho.runDuties v nd ds).1.st d).1,
              (rho.runDuties v nd ds).1.seen⟩
            (rho.signedCandidate v d
              ((Model.protoOf (compiled (goldilocks S)) E).act (rho.runDuties v nd ds).1.st d).2)).2
      have hp := Model.releaseAll_preserves rho.hash (rho.ownKey v) Q
        ⟨((Model.protoOf (compiled (goldilocks S)) E).act (rho.runDuties v nd ds).1.st d).1,
          (rho.runDuties v nd ds).1.seen⟩
        (rho.signedCandidate v d
          ((Model.protoOf (compiled (goldilocks S)) E).act (rho.runDuties v nd ds).1.st d).2)
        (fun o ho b hb he => Or.inl (he ▸ (Model.mem_closure_iff _ _).mpr ⟨o, ho, hb⟩))
        (fun o ho he => Or.inr (he ▸ ho))
      obtain ⟨o, ho, hc⟩ := (Model.mem_closure_iff _ _).mp ha
      rcases hp.1 o ho _ hc rfl with hh | hh
      · rcases ih hh with hh | hh
        · exact Or.inl hh
        · exact Or.inr (List.mem_append_left _ hh)
      · exact Or.inr (List.mem_append_right _ hh)
    · rename_i hsel
      simp only [hsel, ↓reduceIte, List.append_nil]
      exact ih ha

/-- A seen attestation has a genuine signing if its signer is still honest at the
current event, not merely at the preceding engine cut. The latter would allow a forgery
delivered after a compromise between the two cuts. No order bound is needed for guard safety. -/
theorem engine_seen_att_signed_at (hv : rho.ExecutionValid) {v u : V}
    {i p : Nat} {nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)}
    (hc : EngineDutyCut S rho v i p nd) (hu : u ∉ rho.faultyAt (rho.cutTime (i + 1)))
    {a : FG.Att (Fintype.card V)} (ha : a.val = rho.ownKey u)
    (hm : attObj a ∈ Model.closure nd.seen) :
    ∃ j q, EngineSignsAt S rho hn u j q a := by
  have hsigner : rho.signerOf (attObj a) = some u := by
    change Option.map rho.key (some a.val) = some u
    simp [ha, Model.Run.ownKey]
  have hbefore (hi : i < rho.events.length)
      (hm : attObj a ∈ Model.closure (rho.stateBefore i v).seen) :
      ∃ j q, EngineSignsAt S rho hn u j q a := by
    have hlaws := (Model.sysOf_laws schema (compiled (goldilocks S)) V).trace ⟨E, rho⟩ hv
    have ht := hlaws.cutTime_mono i (i + 1) (by omega)
      (by change i + 1 ≤ rho.events.length; omega)
    obtain ⟨j, _, t, hs, hr⟩ := rho.signed_seen_released hv (Nat.le_of_lt hi) hm
      (fun hf => hu (rho.faultyAt_mono ht hf)) hsigner
    exact released_att_signed_at S rho hn hs hr
  cases hc with
  | tick he hw hp =>
    rename_i t
    rcases duties_closure_at S rho v _ _ a hm with hm | hm
    · exact hbefore (List.getElem?_eq_some_iff.mp he).1 hm
    · obtain ⟨q, d, hd, hr⟩ := release_duty_at S rho v _ _ hm
      have hq : q < p := lt_of_lt_of_le
        (List.getElem?_eq_some_iff.mp hd).1 (List.length_take_le _ _)
      rw [List.getElem?_take_of_lt hq] at hd
      simp only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hq)] at hr
      obtain ⟨hval, j, r, hs⟩ := released_poll_at S rho hn
        (.tick he hw (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hd).1))
        (Or.inl ⟨t, he, hw, hd⟩) hr
      have huv := rho.key.symm.injective (ha.symm.trans hval)
      exact huv ▸ ⟨j, r, hs⟩
  | deliver he hp =>
    rename_i t o
    rcases duties_closure_at S rho v _ _ a hm with hm | hm
    · rw [Model.closure_append] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hbefore (List.getElem?_eq_some_iff.mp he).1 hm
      · have hcontains : Model.Obj.Contains o (attObj a) := by
          simp only [Model.closure, List.flatMap_singleton] at hm
          exact hm
        have hut : u ∉ rho.faultyAt t := by
          simpa only [Model.Run.cutTime, he, Model.Event.time] using hu
        obtain ⟨j, t', _, hs, hr⟩ := hv.unforgeable i v o t he _ hcontains u hsigner hut
        exact released_att_signed_at S rho hn hs hr
    · obtain ⟨q, d, hd, hr⟩ := release_duty_at S rho v _ _ hm
      have hq : q < p := lt_of_lt_of_le
        (List.getElem?_eq_some_iff.mp hd).1 (List.length_take_le _ _)
      rw [List.getElem?_take_of_lt hq] at hd
      simp only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hq)] at hr
      obtain ⟨hval, j, r, hs⟩ := released_poll_at S rho hn
        (.deliver he (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hd).1))
        (Or.inr ⟨t, o, he, hd⟩) hr
      have huv := rho.key.symm.injective (ha.symm.trans hval)
      exact huv ▸ ⟨j, r, hs⟩

/-- Actual event nodes remain honest through all duties of that event. -/
theorem duty_honest_at (hv : rho.ExecutionValid) {v : V} {i p : Nat} {nd}
    (hc : EngineDutyCut S rho v i p nd) : v ∉ rho.faultyAt (rho.cutTime (i + 1)) := by
  cases hc with
  | tick he _ _ =>
    simpa only [Model.Run.cutTime, he, Model.Event.time, Model.Event.node] using
      hv.honest_only _ (List.mem_of_getElem? he)
  | deliver he _ =>
    simpa only [Model.Run.cutTime, he, Model.Event.time, Model.Event.node] using
      hv.honest_only _ (List.mem_of_getElem? he)

/-- The own-object guard admits a genuine attestation at an actual event's duty prefix.
Only the event node's current honesty is used, not a constant-fault assumption. -/
theorem engine_att_protected_at (hv : rho.ExecutionValid)
    {v : V} {i p : Nat} {nd}
    (hc : EngineDutyCut S rho v i p nd) {j q : Nat} {a : FG.Att (Fintype.card V)}
    (ha : EngineSignsAt S rho hn v j q a) :
    Model.protects (Model.protoOf (compiled (goldilocks S)) E) (rho.ownKey v) nd.seen
      (attObj a) = true := by
  have hv0 : v ∉ rho.faultyAt 0 := by
    cases hc with
    | tick he _ _ => exact event_honest_zero S rho hv he
    | deliver he _ => exact event_honest_zero S rho hv he
  have hinj {a b : FG.Att (Fintype.card V)} (h : attObj a = attObj b) : a = b := by
    injection h with _ h₂
    injection h₂ with h₃
    injection h₃ with h₄
    have hd := congrArg (decodeAtt (Fintype.card V)) h₄
    simpa only [decodeAtt_encodeAtt, Option.some.injEq] using hd
  have hself : conflicts (attObj a) (attObj a) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨b, c, hb, hc', hbc⟩ := (conflictsIff_iff.mp conflicts_iff _ _ _).mp h
    obtain rfl := hinj hb
    obtain rfl := hinj hc'
    exact engine_signings_nonFraming S rho hn hv hv0 ha ha hbc
  unfold Model.protects
  split
  · simp only [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨hself, ?_⟩
    rw [List.all_eq_true]
    intro o ho
    by_cases hk : o.signer? = some (rho.ownKey v)
    · have hconf : conflicts (attObj a) o = false ∧ conflicts o (attObj a) = false := by
        constructor <;> apply Bool.eq_false_iff.mpr <;> intro h
        · obtain ⟨b, c, hb, rfl, hbc⟩ := (conflictsIff_iff.mp conflicts_iff _ _ _).mp h
          obtain rfl := hinj hb
          have hcval : c.val = rho.ownKey v := Option.some.inj hk
          obtain ⟨j', q', hc'⟩ := engine_seen_att_signed_at S rho hn hv hc
            (duty_honest_at S rho hv hc) hcval ho
          exact engine_signings_nonFraming S rho hn hv hv0 ha hc' hbc
        · obtain ⟨b, c, rfl, hc', hbc⟩ := (conflictsIff_iff.mp conflicts_iff _ _ _).mp h
          obtain rfl := hinj hc'
          have hbval : b.val = rho.ownKey v := Option.some.inj hk
          obtain ⟨j', q', hb⟩ := engine_seen_att_signed_at S rho hn hv hc
            (duty_honest_at S rho hv hc) hbval ho
          exact engine_signings_nonFraming S rho hn hv hv0 hb ha hbc
      change (_ != _ || !(conflicts (attObj a) o || conflicts o (attObj a))) = true
      simp [hconf.1, hconf.2]
    · simp [hk]
  · rfl

/-- An actual scheduled poll's ordinary attestation passes the own-signature guard. -/
theorem engine_poll_att_protected_at (hv : rho.ExecutionValid) {v : V}
    {i p : Nat} {nd} {k : Nat} (hc : EngineDutyCut S rho v i p nd)
    (hd : (∃ t, rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
        ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some (.poll k)) ∨
      ∃ t o, rho.events[i]? = some (.deliver v o t) ∧
        ((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t)[p]? = some (.poll k))
    (hsel : rho.ownKey v ∈ rho.sel .poll) {w cs}
    (hm : (poll (nd.st.1 hn) k).2 = some (.att w, cs)) :
    Model.protects (Model.protoOf (compiled (goldilocks S)) E) (rho.ownKey v) nd.seen
      (.mk (.signed (rho.ownKey v) .poll) (.data (.att w)) []) = true := by
  obtain ⟨a, j, q, rfl, hval, ha⟩ := engine_poll_att_signed S rho hn hc hd hsel hm
  have hp := engine_att_protected_at S rho hn hv hc ha
  have he := hval.trans (cut_self S rho hn hc)
  have ho : attObj a = (.mk (.signed (rho.ownKey v) .poll)
      (.data (.att (encodeAtt a))) [] : Wire (Fintype.card V)) := by
    unfold attObj
    rw [he]
  rw [ho] at hp
  exact hp

end Consensus.Goldilocks.Simulation
