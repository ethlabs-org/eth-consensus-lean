module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.HeldRefusal
import ConsensusLean.Lemmas.Model.Candidates
import ConsensusLean.Lemmas.Model.DutyFold

public section

/-! # Goldilocks Simulation: held attestations leave at the first allowed awake tick

The engine-level flush of `HeldQueue`. An attestation in a node's held queue stays there until a
poll at a time the release schedule allows releases it (`dutyStep_held`, `runDuties_held`,
`event_held`, `held_until`); the first poll of an awake tick at such a time does
(`tick_flush`). So an attestation held after its signing tick at `s` is released at the first
time `t ≥ s` at which the node is awake, honest and allowed to release, unless it was released
earlier (`held_flush`): the `hflush` premise of `released_by_of_release_liveness`
(`Lemmas/Growing/Simulation/HeldRelease`). The released object is the held attestation signed by
the node in the `.poll` role (`heldObj`), the attestation's canonical object when the node signed
it (`heldObj_eq_attObj`).

Every step is proved. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The object a poll of `v` releases for a flushed held attestation `a`. -/
noncomputable abbrev heldObj (v : V) (a : FG.Att (Fintype.card V)) :
    (Model.protoOf (compiled (goldilocks S)) E).Object :=
  .mk (.signed (rho.ownKey v) .poll) (.data (.att (encodeAtt a))) []

omit [DecidableEq V] in
/-- An attestation of the node itself is released as its canonical object. -/
theorem heldObj_eq_attObj {v : V} {a : FG.Att (Fintype.card V)} (h : a.val = rho.ownKey v) :
    heldObj S rho v a = attObj (binding := S.vote) a := by
  unfold heldObj attObj
  rw [h]
  rfl

omit [DecidableEq V] in
/-- `releaseAll` releases every candidate that passes both guards at every prefix. -/
private theorem mem_releaseAll_of_ready (k : Fin (Fintype.card V))
    (c : (Model.protoOf (compiled (goldilocks S)) E).Object)
    (hrel : ∀ seen, Model.releasable seen c = true)
    (hdep : ∀ held, (Model.protoOf (compiled (goldilocks S)) E).dependencies.ready held c = true) :
    ∀ (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (cs),
      c ∈ cs → c ∈ (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) rho.hash k nd
        cs).2
  | _, [], h => absurd h List.not_mem_nil
  | nd, c' :: cs, h => by
    unfold Model.releaseAll
    split
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_releaseAll_of_ready k c hrel hdep _ cs h)
    · rename_i hg
      rcases List.mem_cons.mp h with rfl | h
      · exact absurd (by rw [hrel, hdep]; rfl) hg
      · exact mem_releaseAll_of_ready k c hrel hdep nd cs h

omit [DecidableEq V] in
/-- A flushed held attestation carries nothing. -/
theorem heldObj_releasable (v : V) (a : FG.Att (Fintype.card V)) seen :
    Model.releasable seen (heldObj S rho v a) = true := by
  simp [Model.releasable, Model.Obj.carried]

omit [DecidableEq V] in
/-- A flushed held attestation depends on nothing. -/
private theorem heldObj_ready (v : V) (a : FG.Att (Fintype.card V)) held :
    (Model.protoOf (compiled (goldilocks S)) E).dependencies.ready held (heldObj S rho v a) =
      true := by
  have h := pollObj_ready S rho v held (.att (encodeAtt a))
  simp only [pollObj, pollRole_of_not_vote _ _ (b := .att (encodeAtt a))
    (fun _ _ h => by cases h)] at h
  exact h

omit [DecidableEq V] in
/-- `releaseAll` releases every flushed held attestation, in order. -/
theorem releaseAll_heldObj (v : V) (k : Fin (Fintype.card V)) :
    ∀ (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
      (as : List (FG.Att (Fintype.card V))),
      (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) rho.hash k nd
        (as.map (heldObj S rho v))).2 = as.map (heldObj S rho v)
  | _, [] => rfl
  | nd, a :: as => by
    rw [List.map_cons]
    unfold Model.releaseAll
    simp only [heldObj_releasable, heldObj_ready, Bool.and_self, ↓reduceIte]
    exact congrArg (heldObj S rho v a :: ·) (releaseAll_heldObj v k _ as)

omit [DecidableEq V] in
/-- After the tick step, at a time the release schedule allows, a selected poll releases every
held attestation. -/
private theorem dutyStep_poll_flush (v : V) (hsel : rho.ownKey v ∈ rho.sel .poll)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (t : Nat)
    (hr : (S.release (pubOf E) (shapeOf S hn nd).self (shapeOf S hn nd).now &&
      (shapeOf S hn nd).ticked) = true)
    {a : FG.Att (Fintype.card V)} (ha : a ∈ (shapeOf S hn nd).held) :
    heldObj S rho v a ∈ (rho.dutyStep v nd (.poll t)).2 := by
  unfold Model.Run.dutyStep
  simp only [show (Model.protoOf (compiled (goldilocks S)) E).role (.poll t) = .poll from rfl,
    hsel, ↓reduceIte]
  rw [signedCandidate_poll S rho hn v nd t hsel]
  refine mem_releaseAll_of_ready S rho _ (heldObj S rho v a)
    (fun _ => by simp [Model.releasable, Model.Obj.carried]) (fun held => ?_) _ _ ?_
  · have h := pollObj_ready S rho v held (.att (encodeAtt a))
    simp only [pollObj, pollRole_of_not_vote _ _ (b := .att (encodeAtt a))
      (fun _ _ h => by cases h)] at h
    exact h
  apply List.mem_append_right
  rw [pollFlush_eq, ite_eq_left_iff.mpr (fun h => absurd hr h)]
  exact List.mem_map_of_mem ha

omit [DecidableEq V] in
/-- A selected duty keeps a held attestation, or releases it. -/
private theorem dutyStep_held (v : V) (hsel : rho.ownKey v ∈ rho.sel .poll)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (d : (Model.protoOf (compiled (goldilocks S)) E).Duty) {a : FG.Att (Fintype.card V)}
    (ha : a ∈ (shapeOf S hn nd).held) :
    a ∈ (shapeOf S hn (rho.dutyStep v nd d).1).held ∨
      heldObj S rho v a ∈ (rho.dutyStep v nd d).2 := by
  cases d with
  | propose s hs =>
    exact Or.inl (dutyStep_propose_pres S rho hn (fun st => a ∈ st.held)
      (fun st o hs h => (recordOwn_held st o hs).symm ▸ h)
      (fun st s h => (propose_held st s).symm ▸ h) v nd s hs ha)
  | act s k =>
    have h : rho.dutyStep v nd (.act s k) = (nd, []) := dutyStep_act S rho v nd s k
    rw [h]
    exact Or.inl ha
  | pollPropose t =>
    left
    rw [dutyStep_pollPropose S rho hn v nd t hsel, nodeTick_held]
    exact ha
  | poll t =>
    by_cases hr : (S.release (pubOf E) (shapeOf S hn nd).self (shapeOf S hn nd).now &&
        (shapeOf S hn nd).ticked) = true
    · exact Or.inr (dutyStep_poll_flush S rho hn v hsel nd t hr ha)
    · left
      rw [dutyStep_poll S rho hn v nd t hsel, pollBatch_held, ite_eq_right_iff.mpr
        (fun h => absurd h hr)]
      exact List.mem_append_left _ ha

omit [DecidableEq V] in
/-- Selected duties keep a held attestation, or release it. -/
private theorem runDuties_held (v : V) (hsel : rho.ownKey v ∈ rho.sel .poll) :
    ∀ (ds : List (Model.protoOf (compiled (goldilocks S)) E).Duty)
      (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) {a : FG.Att (Fintype.card V)},
      a ∈ (shapeOf S hn nd).held →
      a ∈ (shapeOf S hn (rho.runDuties v nd ds).1).held ∨
        heldObj S rho v a ∈ (rho.runDuties v nd ds).2
  | [], nd, _, ha => by rw [rho.runDuties_nil]; exact Or.inl ha
  | d :: ds, nd, a, ha => by
    rw [rho.runDuties_cons]
    rcases dutyStep_held S rho hn v hsel nd d ha with h | h
    · rcases runDuties_held v hsel ds _ h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (List.mem_append_right _ h')
    · exact Or.inr (List.mem_append_left _ h)

/-- An engine event keeps a held attestation of its node, or releases it. -/
private theorem event_held (hv : rho.ExecutionValid) (v : V) {i : Nat} {a : FG.Att (Fintype.card V)}
    (ha : a ∈ (stateAt S rho hn v i).held) :
    a ∈ (stateAt S rho hn v (i + 1)).held ∨
      ∃ t, rho.SendsAt v i t ∧ heldObj S rho v a ∈ rho.releasesAt i := by
  have hsel := poll_selected S rho hv v
  have hkeep : ∀ (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) cs,
      a ∈ (shapeOf S hn nd).held →
      a ∈ (shapeOf S hn (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) rho.hash
        (rho.ownKey v) nd cs).1).held := fun nd cs h =>
    releaseAll_pres S rho hn (fun st => a ∈ st.held)
      (fun st o hs h => (recordOwn_held st o hs).symm ▸ h) _ nd cs h
  match he : rho.events[i]? with
  | none => rw [stateAt_succ_none S rho hn v he]; exact Or.inl ha
  | some e =>
    by_cases hne : e.node = v
    · cases e with
      | tick w t =>
        simp only [Model.Event.node] at hne
        subst hne
        have hw := hv.tick_awake w t (List.mem_of_getElem? he)
        have hr : rho.releasesAt i = (rho.tick (rho.stateBefore i w) w t).2 := by
          simp only [Model.Run.releasesAt, he]
        rw [stateAt_tick S rho hn w he, hr]
        unfold Model.Run.tick
        simp only [hw, ite_true]
        have h0 : a ∈ (shapeOf S hn ⟨(Model.protoOf (compiled (goldilocks S)) E).clock
            (rho.stateBefore i w).st t (Model.mempool rho.inbox w t),
            (rho.stateBefore i w).seen⟩).held := by
          rw [stateAt_eq] at ha
          exact ha
        rcases runDuties_held S rho hn w hsel _ _ h0 with h | h
        · exact Or.inl (hkeep _ _ h)
        · exact Or.inr ⟨t, Or.inl he, List.mem_append_left _ h⟩
      | deliver w o t =>
        simp only [Model.Event.node] at hne
        subst hne
        have hr : rho.releasesAt i = (rho.deliver (rho.stateBefore i w) w o t).2 := by
          simp only [Model.Run.releasesAt, he]
        rw [stateAt_deliver S rho hn w he, hr]
        unfold Model.Run.deliver
        simp only
        have h0 : a ∈ (shapeOf S hn ⟨(Model.protoOf (compiled (goldilocks S)) E).process
            (rho.stateBefore i w).st o (Model.digests rho.hash o),
            (rho.stateBefore i w).seen ++ [o]⟩).held := by
          have hp := process_held ((rho.stateBefore i w).st.1 hn) o (Model.digests rho.hash o)
          rw [stateAt_eq] at ha
          exact (congrArg (a ∈ ·) hp).mpr ha
        rcases runDuties_held S rho hn w hsel _ _ h0 with h | h
        · exact Or.inl (hkeep _ _ h)
        · exact Or.inr ⟨t, Or.inr ⟨o, he⟩, List.mem_append_left _ h⟩
      | restart w t =>
        simp only [Model.Event.node] at hne
        subst hne
        rw [stateAt_restart S rho hn w he, restore_held]
        exact Or.inl ha
    · rw [state_of_other S rho hn v i e he hne]
      exact Or.inl ha

/-- A held attestation stays held until a sending event of its node releases it. -/
private theorem held_until (hv : rho.ExecutionValid) (v : V) {i : Nat} {a : FG.Att (Fintype.card V)}
    (ha : a ∈ (stateAt S rho hn v i).held) :
    ∀ j, i ≤ j → a ∈ (stateAt S rho hn v j).held ∨
      ∃ k t, i ≤ k ∧ k < j ∧ rho.SendsAt v k t ∧ heldObj S rho v a ∈ rho.releasesAt k := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base => exact Or.inl ha
  | succ j hij ih =>
    rcases ih with h | ⟨k, t, hik, hkj, hs, hk⟩
    · rcases event_held S rho hn hv v h with h | ⟨t, hs, hk⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, t, hij, Nat.lt_succ_self j, hs, hk⟩
    · exact Or.inr ⟨k, t, hik, Nat.lt_succ_of_lt hkj, hs, hk⟩

/-- **The flush.** The first poll of a tick of `v` at a time `t` the release schedule allows
releases every attestation `v` holds before the tick. -/
private theorem tick_flush (hv : rho.ExecutionValid) {j : Nat} {v : V} {t : Time}
    (he : rho.events[j]? = some (.tick v t)) {a : FG.Att (Fintype.card V)}
    (ha : a ∈ (stateAt S rho hn v j).held)
    (hr : S.release (pubOf E) (rho.ownKey v) t = true) :
    heldObj S rho v a ∈ rho.releasesAt j := by
  have hm := List.mem_of_getElem? he
  have hw := hv.tick_awake v t hm
  have ht := (hv.in_horizon _ hm).1
  have hsel := poll_selected S rho hv v
  simp only [Model.Run.releasesAt, he]
  unfold Model.Run.tick
  simp only [hw, ite_true]
  apply List.mem_append_left
  set nd := rho.stateBefore j v
  set nd₀ : Model.Node (Model.protoOf (compiled (goldilocks S)) E) :=
    ⟨(Model.protoOf (compiled (goldilocks S)) E).clock nd.st t (Model.mempool rho.inbox v t),
      nd.seen⟩
  set L : List (Model.protoOf (compiled (goldilocks S)) E).Duty :=
    [.poll t.toNat, .poll t.toNat, .pollPropose t.toNat]
  set Pr : List (Model.protoOf (compiled (goldilocks S)) E).Duty :=
    (skeleton (pubOf E) S.vote).proposeAt t
  have hds : (Model.protoOf (compiled (goldilocks S)) E).duties t =
      (L ++ Pr) ++ (([.poll t.toNat] : List (Model.protoOf (compiled (goldilocks S)) E).Duty) ++
        [.poll t.toNat]) := by
    rw [duties_eq S t ht]
    exact List.append_assoc _ _ _
  rw [hds, rho.runDuties_append]
  apply List.mem_append_right
  rw [rho.runDuties_append]
  apply List.mem_append_left
  refine (congrArg (fun r => heldObj S rho v a ∈ r.2)
    (rho.runDuties_cons v _ (.poll t.toNat) [])).mpr ?_
  apply List.mem_append_left
  -- the node before the first trailing poll: after the proposal step
  have hN : (rho.runDuties v nd₀ (L ++ Pr)).1 =
      (rho.runDuties v (atProposal S rho v nd t) Pr).1 :=
    (runDuties_fst_append S rho v nd₀ L Pr).trans (by rw [← atProposal_eq])
  rw [hN]
  have hk := self_eq_ownKey S rho hn v j
  rw [stateAt_eq] at hk ha
  have hA : (shapeOf S hn (atProposal S rho v nd t)).self = rho.ownKey v ∧
      (shapeOf S hn (atProposal S rho v nd t)).now = t ∧
      (shapeOf S hn (atProposal S rho v nd t)).ticked = true ∧
      a ∈ (shapeOf S hn (atProposal S rho v nd t)).held := by
    refine ⟨(atProposal_self S rho hn v nd t hsel).trans hk, atProposal_now S rho hn v nd t hsel,
      by rw [atProposal_shape S rho hn v nd t hsel], ?_⟩
    rw [atProposal_shape S rho hn v nd t hsel]
    simp only [nodeTick_held, pollBatch_held, pollBatch_ticked, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte]
    exact List.mem_append_left _ (List.mem_append_left _ ha)
  have hP : ∀ (Q : State (S.params (pubOf E) hn) S.vote → Prop),
      (∀ st o hs, Q st → Q (recordOwn st o hs)) → (∀ st s, Q st → Q (propose st s).1) →
      Q (shapeOf S hn (atProposal S rho v nd t)) →
      Q (shapeOf S hn (rho.runDuties v (atProposal S rho v nd t) Pr).1) := by
    intro Q h1 h2 h
    rcases Skeleton.proposeAt_cases (skeleton (pubOf E) S.vote) t with ⟨hnil, -⟩ | ⟨s, hs, hone, -⟩
    · rw [show Pr = [] from hnil]
      exact h
    · rw [show Pr = [.propose s hs] from hone]
      refine (congrArg (fun n => Q (shapeOf S hn n))
        (runDuties_fst_cons S rho v _ (.propose s hs) [])).mpr ?_
      exact dutyStep_propose_pres S rho hn Q h1 h2 v _ s hs h
  obtain ⟨hs₁, hn₁, ht₁, ha₁⟩ := hA
  refine dutyStep_poll_flush S rho hn v hsel _ _ ?_ ?_
  · rw [hP (fun st => st.self = rho.ownKey v) (fun st o hs h => (recordOwn_self st o hs).trans h)
      (fun st s h => (propose_self st s).trans h) hs₁,
      hP (fun st => st.now = t) (fun st o hs h => (recordOwn_now st o hs).trans h)
      (fun st s h => (propose_now st s).trans h) hn₁,
      hP (fun st => st.ticked = true) (fun st o hs h => (recordOwn_ticked st o hs).trans h)
      (fun st s h => (propose_ticked st s).trans h) ht₁, hr]
    rfl
  · exact hP (fun st => a ∈ st.held) (fun st o hs h => (recordOwn_held st o hs).symm ▸ h)
      (fun st s h => (propose_held st s).symm ▸ h) ha₁

/-- **`hflush`.** An attestation `v` holds after its tick at `s` is released at every time
`t ≥ s` at which `v` is awake, honest and allowed to release, unless it was released at a time in
`[s, t)`. -/
theorem held_flush (hv : rho.ExecutionValid) {i : Nat} {v : V} {s : Time}
    (he : rho.events[i]? = some (.tick v s)) {a : FG.Att (Fintype.card V)}
    (ha : a ∈ (stateAt S rho hn v (i + 1)).held) {t : Time} (hst : s ≤ t)
    (hth : t ≤ rho.horizon) (hhon : v ∉ rho.faultyAt t) (hw : E.awake v t = true)
    (hr : S.release (pubOf E) (rho.ownKey v) t = true)
    (hnot : ∀ r, s ≤ r → r < t → ¬ rho.releases v (heldObj S rho v a) r) :
    rho.releases v (heldObj S rho v a) t := by
  have hm := List.mem_of_getElem? he
  have hs0 := (hv.in_horizon _ hm).1
  rcases hst.lt_or_eq with hlt | rfl
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp
      (hv.tick_total v t (hs0.trans hlt.le) hth hhon hw)
    have hij : i + 1 ≤ j := by
      by_contra! h
      rcases (Nat.lt_succ_iff.mp h).lt_or_eq with h | rfl
      · rcases keyLe_of_lt S rho hv hj he h with h' | h' <;>
          simp only [Model.Event.time] at h' <;> [exact absurd h' (not_lt.mpr hlt.le);
            exact absurd h'.1 hlt.ne']
      · rw [he] at hj
        cases hj
        exact lt_irrefl _ hlt
    rcases held_until S rho hn hv v ha j hij with h | ⟨k, τ, hik, hkj, hsk, hk⟩
    · exact ⟨j, Or.inl hj, tick_flush S rho hn hv hj h hr⟩
    · have hτ : ∀ ev, rho.events[k]? = some ev → ev.time = τ := by
        intro ev hev
        rcases hsk with h | ⟨o, h⟩ <;> rw [h] at hev <;> cases hev <;> rfl
      obtain ⟨ev, hev⟩ : ∃ ev, rho.events[k]? = some ev := by
        rcases hsk with h | ⟨o, h⟩
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
      have hsτ : s ≤ τ := by
        have h := keyLe_of_lt S rho hv he hev (by omega)
        rw [← hτ ev hev]
        rcases h with h | h
        · exact h.le
        · exact h.1.le
      have hτt : τ ≤ t := by
        have h := keyLe_of_lt S rho hv hev hj hkj
        rw [← hτ ev hev]
        rcases h with h | h
        · exact h.le
        · exact h.1.le
      rcases hτt.lt_or_eq with hτt | rfl
      · exact absurd ⟨k, hsk, hk⟩ (hnot τ hsτ hτt)
      · exact ⟨k, hsk, hk⟩
  · exfalso
    have hne : a ∈ (stateAt S rho hn v (i + 1)).held := ha
    rcases heldRefused_inv S rho hn hv v (i + 1) with h | h
    · rw [lastRestart_eq, NodeAsChainShape.CanonicalTrace.lastRestart_iff] at h
      obtain ⟨r, hr', τ, hrr, hno⟩ := h
      rcases (Nat.lt_succ_iff.mp hr').lt_or_eq with h | rfl
      · exact hno i h (Nat.lt_succ_self i) _ he rfl
      · rw [he] at hrr
        cases hrr
    · have h' := (heldRefused_iff _).1 h (List.ne_nil_of_mem hne)
      rw [self_eq_ownKey, now_eq_lastClock S rho hn hv, lastClock_succ, he] at h'
      simp only [↓reduceIte] at h'
      rw [hr] at h'
      cases h'

end Consensus.Goldilocks.Simulation

end
