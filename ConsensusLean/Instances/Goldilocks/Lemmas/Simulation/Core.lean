module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.VoteForwardQueue
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Forwarding
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationQueue
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationProvenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ForwardingInvariant
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PoolInsertionRelease
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Goldilocks Simulation: the engine simulates the node

`EngineSimulatesNode` (`Statements/Obligations`) assembled from its steps: the trace `simTrace`
with the cut map `cutMap` (`Trace`), a Goldilocks run by `simTrace_goldilocksRun` and agreeing
with the engine by the `Simulates` steps (`Run`). Signed fresh-admission publication follows
from event-local pool insertion and global first-release provenance. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Shape Blocks
open Consensus.Model (pubOf)

variable {binding : VoteBinding}

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- Envelopes queued before the tick's trailing polls are released by that tick. -/
theorem tick_voteForward_released (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {v : V} (hv' : v ∉ rho.faultyAt 0) {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) :
    let pre : List (Model.protoOf (compiled (goldilocksWith S)) E).Duty :=
      [.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] ++ (skeleton
          (pubOf E) S.vote).proposeAt t
    let nd := (rho.runDuties v
      ⟨(Model.protoOf (compiled (goldilocksWith S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ pre).1
    ∀ q ∈ (shapeOf S hn nd).voteForwards,
      Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward q.1 (encodeVote q.2))) [voteObj q.2] ∈ rho.releasesAt i := by
  intro pre nd q hq
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  have hrel := tick_trailing_voteForward_poll S rho hn hconst hv hv' he q hq
  simp only [Model.Run.releasesAt, he]
  rw [rho.tick_of_awake _ _ _ (hv.tick_awake v t (List.mem_of_getElem? he))]
  apply List.mem_append_left
  have hd : (Model.protoOf (compiled (goldilocksWith S)) E).duties t =
      pre ++ .poll t.toNat :: [.poll t.toNat] := by
    rw [duties_eq S t ht]
    exact List.append_assoc _ _ _
  rw [hd]
  exact duty_release_in_runDuties S rho v _ pre _ _ _ hrel

/-- A tick's aggregate pool difference is queued before its trailing polls and released. -/
theorem tick_pool_insertion_released (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {v : V} (hv' : v ∉ rho.faultyAt 0) {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) (m : SA.Vote (Fintype.card V))
    (hold : m ∉ (stateAt S rho hn v i).node.ac.pool m.slot)
    (hnew : m ∈ (stateAt S rho hn v (i + 1)).node.ac.pool m.slot) :
    Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∈ rho.releasesAt i :=
  tick_voteForward_released S rho hn hconst hv hv' he (t, m)
    (tick_pool_insertion_queued S rho hn hv he m hold hnew)

/-- Every envelope actually queued during delivery is released in that same engine event.
Canonical dependencies are derived from reachable inventory and the actual ordinary prefix. -/
theorem delivery_voteForward_released (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid) {v : V}
    {i : Nat} {o : (Model.protoOf (compiled (goldilocksWith S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (tv : Time × SA.Vote (Fintype.card V))
    (htv : tv ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).voteForwards) :
    Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward tv.1 (encodeVote tv.2))) [voteObj tv.2] ∈ rho.releasesAt i :=
  delivery_voteForward_released_of S rho hn hv
    ((rho.point.honestAt_iff_zero hconst v t).mp (hv.honest_only _ (List.mem_of_getElem? he))) he
    (delivery_voteForward_held_or_head S rho hn hconst hv he) tv htv

/-- A delivery's aggregate pool difference suffices for same-event forwarding,
without identifying which nested message or block handler made the insertion. -/
theorem delivery_pool_insertion_released (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid) {v : V}
    {i : Nat} {o : (Model.protoOf (compiled (goldilocksWith S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) (m : SA.Vote (Fintype.card V))
    (hold : m ∉ (stateAt S rho hn v i).node.ac.pool m.slot)
    (hnew : m ∈ (stateAt S rho hn v (i + 1)).node.ac.pool m.slot) :
    Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∈ rho.releasesAt i :=
  delivery_voteForward_released S rho hn hconst hv he (t, m)
    (delivery_pool_insertion_queued S rho hn hv
      ((rho.point.honestAt_iff_zero hconst v t).mp (hv.honest_only _ (List.mem_of_getElem? he)))
      he m hold hnew)

/-- An honest emission cut cannot be a restart, even though `EmitAt` permits that call
syntactically. This uses the actual cut law and the run's nonnegative clock. -/
theorem simTrace_emission_not_restart (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {k : Nat}
    {ℓ : ACLabel (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    (hc : (simTrace S rho hn).CallAt y k (.ac ℓ))
    {e : SA.Em (S.params (pubOf E) hn) (List (FG.Att (Fintype.card V)))}
    (he : e ∈ ℓ.emits) : ℓ.call ≠ .restart := by
  intro hr
  have hstep := (simTrace_cutLaw S rho hn hconst hv y hy k _ hc).2.1
  rw [hr] at hstep
  have hnil := restart_emits_nil (S.ro _) y (simTrace S rho hn |>.state y k).ac
    ℓ.frame ((simTrace S rho hn).time k) (simTrace_time_nonneg S rho hn hv k)
  have hemits := congrArg Prod.snd hstep
  rw [hnil] at hemits
  have hempty : ℓ.emits = [] := hemits.symm
  rw [hempty] at he
  exact List.not_mem_nil he

/-- The first trace cut of a public tick is its actual AC-tick call. -/
theorem tick_boundary_call (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∉ rho.faultyAt 0) {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) :
    (simTrace S rho hn).CallAt (rho.ownKey v) (cutMap S rho hn i)
      (Node.acCall (rho.ownKey v) (stateAt S rho hn v i).node t .tick).2 ∧
      (simTrace S rho hn).time (cutMap S rho hn i) = t := by
  have hg := (simTrace_tick_public_group S rho hn hconst hv v hv' i t he hp).1
  have hstate := simTrace_state S rho hn hconst hv v hv' i
    (Nat.le_of_lt (List.getElem?_eq_some_iff.mp he).1)
  have hlen : 0 < (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2.length := by
    exact List.length_pos_iff.mpr hg.1
  obtain ⟨hnode, htime, -, -, hlabel⟩ := hg.2.1 0 hlen
  have hget : (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2[0]'hlen =
      (Node.acCall (rho.ownKey v) (stateAt S rho hn v i).node t .tick).2 := by
    change (Node.acCall (rho.ownKey v)
      ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t .tick).2 = _
    rw [hstate]
  rw [hget] at hlabel
  exact ⟨⟨by simpa only [Nat.add_zero] using hnode,
    by simpa only [Nat.add_zero] using hlabel⟩, by simpa only [Nat.add_zero] using htime⟩

/-- A trace restart is produced by an actual engine restart, never by tick or
recursive delivery processing. The interval identifies its exact engine event. -/
theorem simTrace_restart_event {y : Fin (Fintype.card V)} {k : Nat}
    (hr : (simTrace S rho hn).RestartAt y k) :
    ∃ i, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      rho.events[i]? = some (.restart (rho.key y) ((simTrace S rho hn).time k)) := by
  obtain ⟨ℓ, ⟨hnode, hlab⟩, hcall⟩ := hr
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, -, he, hlo, hhi, hidx, hn', ht, -, hlab'⟩ :=
    simTrace_cut S rho hn hl
  have hrl : r.label = .ac ℓ := Option.some.inj (hlab'.symm.trans hlab)
  obtain ⟨v, t, rfl⟩ :=
    restart_of_mem_eventCuts S rho hn he (List.mem_of_getElem? hidx) hrl hcall
  have hkey : v = rho.key y := by
    have hk := congrArg rho.key (hn'.symm.trans hnode)
    exact (rho.key.apply_symm_apply v).symm.trans hk
  exact ⟨i, hlo, hhi, by simpa only [hkey, ht, Model.Event.time] using he⟩

/-- An engine interval without this node's restarts contains no restart cuts for
that node. This supplies the cut-level premise needed for pool monotonicity. -/
theorem simTrace_noRestart_between {y : Fin (Fintype.card V)} {a b k : Nat}
    (hnr : ∀ i, a ≤ i → i < b → ∀ t,
      rho.events[i]? ≠ some (.restart (rho.key y) t))
    (ha : cutMap S rho hn a ≤ k) (hb : k < cutMap S rho hn b) :
    ¬ (simTrace S rho hn).RestartAt y k := by
  intro hr
  obtain ⟨i, hlo, hhi, he⟩ := simTrace_restart_event S rho hn hr
  have hai : a ≤ i := by
    by_contra h
    have hm := cutMap_mono S rho hn (show i + 1 ≤ a by omega)
    omega
  have hib : i < b := by
    by_contra h
    have hm := cutMap_mono S rho hn (show b ≤ i by omega)
    omega
  exact hnr i hai hib _ he

/-- Restarts precede all sending events at a fixed time, so none can intervene
between two such events, even for a different node. -/
theorem noRestart_between_same_time_sends (hv : rho.ExecutionValid)
    {v : V} {a b : Nat} {t : Time} (ha : rho.SendsAt v a t) (hb : rho.SendsAt v b t)
    {j : Nat} (haj : a ≤ j) (hjb : j < b) (w : V) (u : Time) :
    rho.events[j]? ≠ some (.restart w u) := by
  intro hr
  have haj' : a < j := by
    rcases haj.lt_or_eq with h | rfl
    · exact h
    · rcases ha with ha | ⟨o, ha⟩ <;> rw [hr] at ha <;> cases ha
  have hle : u ≤ t := by
    rcases hb with hb | ⟨o, hb⟩ <;>
      rcases keyLe_of_lt S rho hv hr hb hjb with h | h
    all_goals first | exact h.le | exact h.1.le
  rcases ha with ha | ⟨o, ha⟩ <;>
    rcases keyLe_of_lt S rho hv ha hr haj' with h | h
  all_goals first
    | exact (not_lt_of_ge hle) h
    | simpa only [Model.Event.phase, Nat.reduceLeDiff] using h.2

/-- Retention also covers the later sending event's own cuts: its event cannot
be a restart. This is the interval needed for a fresh admission inside that event. -/
theorem pool_mono_through_same_time_send {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys ⟨S, stock⟩ rho)
    {a b : Nat} {t : Time} (ha : rho.SendsAt (rho.key y) a t)
    (hb : rho.SendsAt (rho.key y) b t) {k l : Nat}
    (hak : cutMap ⟨S, stock⟩ rho hn a ≤ k) (hkl : k ≤ l)
    (hlb : l ≤ cutMap ⟨S, stock⟩ rho hn (b + 1)) (σ : Nat) :
    ((simTrace ⟨S, stock⟩ rho hn).state y k).ac.pool σ ⊆
      ((simTrace ⟨S, stock⟩ rho hn).state y l).ac.pool σ := by
  have hr := simTrace_goldilocksRun S rho hn hconst hv
  have hnr : ∀ i, a ≤ i → i < b + 1 → ∀ u,
      rho.events[i]? ≠ some (.restart (rho.key y) u) := by
    intro i hai hib u he
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hib) with hib | rfl
    · exact noRestart_between_same_time_sends ⟨S, stock⟩ rho hv ha hb hai hib _ u he
    · rcases hb with hb | ⟨o, hb⟩ <;> rw [he] at hb <;> cases hb
  have hm := Compose.pool_mono hr hy hkl (fun j hkj hjl =>
    simTrace_noRestart_between ⟨S, stock⟩ rho hn hnr (hak.trans hkj) (hjl.trans_le hlb)) σ
  simpa only [Compose.projAC_state hr.toLocalRun hy] using hm

/-- Freshness at any sending-event cut gives an aggregate boundary pool insertion.
Non-restart retention covers both sides of the source cut. -/
theorem sending_event_pool_insertion {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys ⟨S, stock⟩ rho)
    {i k : Nat} {t : Time} {m : SA.Vote (Fintype.card V)}
    (hs : rho.SendsAt (rho.key y) i t)
    (hlo : cutMap ⟨S, stock⟩ rho hn i ≤ k) (hhi : k < cutMap ⟨S, stock⟩ rho hn (i + 1))
    (hc : (simTrace ⟨S, stock⟩ rho hn).IsCall y k)
    (hold : m ∉ ((simTrace ⟨S, stock⟩ rho hn).state y k).ac.pool m.slot)
    (hnew : m ∈ ((simTrace ⟨S, stock⟩ rho hn).post k).ac.pool m.slot) :
    m ∉ (stateAt ⟨S, stock⟩ rho hn (rho.key y) i).node.ac.pool m.slot ∧
      m ∈ (stateAt ⟨S, stock⟩ rho hn (rho.key y) (i + 1)).node.ac.pool m.slot := by
  have hi : i < rho.events.length := by
    rcases hs with h | ⟨o, h⟩ <;> exact (List.getElem?_eq_some_iff.mp h).1
  have hstate (j : Nat) (hj : j ≤ rho.events.length) :
      (stateAt ⟨S, stock⟩ rho hn (rho.key y) j).node =
        (simTrace ⟨S, stock⟩ rho hn).state y (cutMap ⟨S, stock⟩ rho hn j) := by
    simpa only [Model.Run.ownKey, Equiv.symm_apply_apply] using
      simTrace_state ⟨S, stock⟩ rho hn hconst hv (rho.key y)
          ((mem_honestKeys_iff ⟨S, stock⟩ rho y).mp hy) j hj
  constructor
  · rw [hstate i hi.le]
    intro hm
    exact hold (pool_mono_through_same_time_send S rho hn hconst hv hy hs hs le_rfl hlo hhi.le _ hm)
  · rw [hstate (i + 1) (by omega)]
    apply pool_mono_through_same_time_send S rho hn hconst hv hy hs hs
      (hlo.trans (Nat.le_succ k)) (by omega) le_rfl m.slot
    obtain ⟨c, hc⟩ := hc
    rwa [(simTrace ⟨S, stock⟩ rho hn).state_succ_of_call hc]

/-- Fresh admission rules out an earlier exact envelope once every earlier release
is backed by a pool cut in its event. Only that release-to-pool supplier remains
explicit; stamp authentication and restart-free retention are proved here. -/
theorem admission_voteForward_first_of_release_pool {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys ⟨S, stock⟩ rho)
    {i k : Nat} {t : Time} {m : SA.Vote (Fintype.card V)}
    (hs : rho.SendsAt (rho.key y) i t)
    (hlo : cutMap ⟨S, stock⟩ rho hn i ≤ k) (hhi : k < cutMap ⟨S, stock⟩ rho hn (i + 1))
    (hf : m ∉ ((simTrace ⟨S, stock⟩ rho hn).state y k).ac.pool m.slot)
    (hpool : ∀ j < i, Model.Obj.mk (.signed y .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∈ rho.releasesAt j →
      ∃ c, cutMap ⟨S, stock⟩ rho hn j ≤ c ∧ c ≤ cutMap ⟨S, stock⟩ rho hn (j + 1) ∧
        m ∈ ((simTrace ⟨S, stock⟩ rho hn).state y c).ac.pool m.slot) :
    ∀ j < i, Model.Obj.mk (.signed y .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∉ rho.releasesAt j := by
  intro j hji hj
  obtain ⟨u, hsend⟩ := voteForward_release_sender ⟨S, stock⟩ rho hj
  have hkey : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply y
  have ht : t = u := released_voteForward_stamp ⟨S, stock⟩ rho hn hv hsend m
      (by erw [hkey]; exact hj)
  subst u
  obtain ⟨c, hjc, hcj, hm⟩ := hpool j hji hj
  have hck := hcj.trans ((cutMap_mono ⟨S, stock⟩ rho hn (Nat.succ_le_of_lt hji)).trans hlo)
  exact hf (pool_mono_through_same_time_send S rho hn hconst hv hy hsend hs
    hjc hck hhi.le m.slot hm)

/-- A fresh admission's exact signed envelope has no earlier release, even when
the original vote signer is faulty. Event pool provenance discharges the supplier. -/
theorem admission_voteForward_first {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys ⟨S, stock⟩ rho)
    {i k : Nat} {t : Time} {m : SA.Vote (Fintype.card V)}
    (hs : rho.SendsAt (rho.key y) i t)
    (hlo : cutMap ⟨S, stock⟩ rho hn i ≤ k) (hhi : k < cutMap ⟨S, stock⟩ rho hn (i + 1))
    (hf : m ∉ ((simTrace ⟨S, stock⟩ rho hn).state y k).ac.pool m.slot) :
    ∀ j < i, Model.Obj.mk (.signed y .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∉ rho.releasesAt j := by
  apply admission_voteForward_first_of_release_pool S rho hn hconst hv hy hs hlo hhi hf
  intro j _ hj
  obtain ⟨u, hsend⟩ := voteForward_release_sender ⟨S, stock⟩ rho hj
  have hkey : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply y
  have hm := released_voteForward_pool ⟨S, stock⟩ rho hn hv hsend m (by erw [hkey]; exact hj)
  have hjlen : j + 1 ≤ rho.events.length := by
    rcases hsend with he | ⟨o, he⟩ <;>
      exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp he).1
  rw [simTrace_state ⟨S, stock⟩ rho hn hconst hv (rho.key y)
      ((mem_honestKeys_iff ⟨S, stock⟩ rho y).mp hy)
    (j + 1) hjlen] at hm
  erw [hkey] at hm
  exact ⟨cutMap ⟨S, stock⟩ rho hn (j + 1), cutMap_mono ⟨S, stock⟩ rho hn (Nat.le_succ j),
      le_rfl, hm⟩

/-- Every non-restart AC cut lies in a sending engine event of the same node and time.
This is interval transport only; it does not assume the publication supplier. -/
theorem simTrace_call_sending_event {y : Fin (Fintype.card V)} {k : Nat}
    {ℓ : ACLabel (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    (hc : (simTrace S rho hn).CallAt y k (.ac ℓ)) (hnr : ℓ.call ≠ .restart) :
    ∃ i, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      rho.SendsAt (rho.key y) i ((simTrace S rho hn).time k) := by
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hc.2]; simp
  obtain ⟨r, i, ev, -, he, hlo, hhi, hidx, hnode, ht, -, hlabel⟩ :=
    simTrace_cut S rho hn hl
  have hkey : rho.key y = ev.node := by
    rw [← hc.1, hnode]
    exact rho.key.apply_symm_apply ev.node
  refine ⟨i, hlo, hhi, ?_⟩
  rw [hkey, ht]
  cases ev with
  | tick v t => exact Or.inl he
  | deliver v o t => exact Or.inr ⟨o, he⟩
  | restart v t =>
    have hr := List.mem_of_getElem? hidx
    rw [eventCuts_restart S rho hn i v t he] at hr
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
    have hj' := hj
    rw [length_groupRecs] at hj'
    have hj0 : j = 0 := by
      simpa only [Node.exec, Node.restart, List.length_singleton, Nat.lt_one_iff] using hj'
    subst j
    have hrl := (getElem_groupRecs _ _ _ _ _ _ _ 0 hj).2.2.2.2
    have heq := Option.some.inj (hlabel.symm.trans hc.2)
    rw [hrl] at heq
    have hcall := congrArg (fun c => match c with | .ac l => l.call | _ => .restart) heq
    exact False.elim (hnr hcall.symm)

/-- A vote carried by an actual receipt is processed at a cut of that same event.
No fresh insertion, honest signer, or pool-cap premise is required. -/
theorem received_vote_processAt {i : Nat} {v : V}
    {receipt : Wire (Fintype.card V) S.vote} {u : Time} {m : SA.Vote (Fintype.card V)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    (hc : Model.Obj.Contains receipt (voteObj m)) :
    ∃ k, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      (simTrace S rho hn).projAC.ProcessAt (rho.ownKey v) k m ∧
      (simTrace S rho hn).time k = u := by
  obtain ⟨r, hr, ℓ, hl, hm⟩ := deliverRecs_message_call (runProposer S rho hn)
    (digestOf S rho) (Model.digests rho.hash receipt) (rho.ownKey v) u i m
    (delivered _ receipt) (stateAt S rho hn v i).node 0
    ⟨voteObj m, by simpa only [delivered, Model.Obj.Contains] using hc,
      canonEvent_voteObj (sp := S.params (pubOf E) hn) (ro := S.ro _)
        (Model.digests rho.hash receipt) m⟩
  obtain ⟨hn', ht', _⟩ := mem_deliverRecs (sp := S.params (pubOf E) hn)
    (ro := S.ro _) (runProposer S rho hn) (digestOf S rho)
    (rho.ownKey v) (Model.digests rho.hash receipt) u i hr
  have hr' : r ∈ eventCuts S rho hn i := by
    rw [eventCuts_deliver S rho hn i v receipt u he]
    exact hr
  obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hr'
  have hk : (allCuts S rho hn)[cutMap S rho hn i + j]? = some r := by
    rw [allCuts_getElem?_add S rho hn i j (List.getElem?_eq_some_iff.mp he).1 hj,
      List.getElem?_eq_getElem hj, heq]
  refine ⟨cutMap S rho hn i + j, Nat.le_add_right _ _, ?_, ?_, ?_⟩
  · rw [cutMap_succ]
    omega
  · refine ⟨ℓ, Compose.projAC_callAt.mpr ⟨?_, ?_⟩, Or.inl hm⟩
    · simpa only [simTrace_node, hk, Option.elim_some] using hn'
    · simp [simTrace_label, hk, hl]
  · simpa only [simTrace_time, hk, Option.elim_some] using ht'

/-- An AC block cut in an actual delivery comes from that receipt's canonical block.
Consequently its payload votes also receive explicit message processing in that event. -/
theorem delivery_block_payload_processAt {i : Nat} {v : V}
    {receipt : Wire (Fintype.card V) S.vote} {u : Time}
    {r : CutRec (S.params (pubOf E) hn) (S.ro _)}
    {ℓ : ACLabel (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    {B : Blk (S.params (pubOf E) hn)} {m : SA.Vote (Fintype.card V)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    (hr : r ∈ eventCuts S rho hn i) (hl : r.label = .ac ℓ)
    (hb : ℓ.call = .block B) (hm : m ∈ SA.blockVotes B) :
    ∃ k, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      (simTrace S rho hn).projAC.ProcessAt (rho.ownKey v) k m ∧
      (simTrace S rho hn).time k = u := by
  rw [eventCuts_deliver S rho hn i v receipt u he] at hr
  obtain ⟨o, e, st, ho, hce, q, hq, hlabel, _⟩ :=
    mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hr
  have hcut := List.getElem_mem hq
  rw [← hlabel, hl] at hcut
  have heq : e = .block B := by
    cases e with
    | tick x => exact False.elim (canonEvent_ne_tick hce x rfl)
    | block B' =>
      simp only [Node.exec, Node.onBlock] at hcut
      split_ifs at hcut
      · simp at hcut
      · split at hcut <;> simp [Node.acCall] at hcut
        subst ℓ
        cases hb
        rfl
    | message m' =>
      simp only [Node.exec, Node.onMessage, Node.acCall, List.mem_singleton,
        Cut.ac.injEq] at hcut
      subst ℓ
      cases hb
    | attestation => simp [Node.exec, Node.onAttestation] at hcut
    | restart =>
      simp only [Node.exec, Node.restart, Node.acCall, List.mem_singleton,
        Cut.ac.injEq] at hcut
      subst ℓ
      cases hb
  subst e
  obtain rfl := eq_blockObj_of_decodeBlock (decodeBlock_of_canonEvent hce)
  have hp : voteObj (binding := S.vote) m ∈ payloadObjs B.fgPayload B.acPayload :=
    List.mem_append_right _ (List.mem_map.mpr ⟨m, List.mem_append_left _ hm, rfl⟩)
  exact received_vote_processAt S rho hn he
    ((contains_of_mem_delivered ho).trans (Model.Obj.Contains.step hp (.refl _)))

/-- An authenticated vote envelope received after its globally first release yields
processing no earlier than that release. The first-release premise is essential:
the wire timestamp alone does not authenticate a fresh source occurrence. -/
theorem received_voteForward_processAt (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {source i : Nat} {x : Fin (Fintype.card V)} {v : V} {τ u : Time}
    {receipt : Wire (Fintype.card V) S.vote} {m : SA.Vote (Fintype.card V)}
    (hx : rho.key x ∉ rho.faultyAt 0) (hs : rho.SendsAt (rho.key x) source τ)
    (hfirst : ∀ j < source,
      Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m] ∉
        rho.releasesAt j)
    (he : rho.events[i]? = some (.deliver v receipt u))
    (hc : Model.Obj.Contains receipt
      (.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m])) :
    ∃ k, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      (simTrace S rho hn).projAC.ProcessAt (rho.ownKey v) k m ∧
      (simTrace S rho hn).time k = u ∧ τ ≤ u := by
  obtain ⟨j, s, hji, hsend, hrel⟩ := hv.unforgeable i v receipt u he _ hc
    (rho.key x) rfl (by simpa only [rho.faultyAt_eq_zero hconst] using hx)
  have hsj : source ≤ j := by
    by_contra h
    exact hfirst j (Nat.lt_of_not_ge h) hrel
  have hsi : source < i := hsj.trans_lt hji
  have htime : τ ≤ u := by
    rcases hs with hs | ⟨o, hs⟩ <;>
      rcases keyLe_of_lt S rho hv hs he hsi with h | ⟨h, _⟩
    · exact h.le
    · exact h.le
    · exact h.le
    · exact h.le
  obtain ⟨k, hlo, hhi, hp, ht⟩ := received_vote_processAt S rho hn he
    (hc.trans (Model.Obj.Contains.step (List.mem_singleton_self _) (.refl _)))
  exact ⟨k, hlo, hhi, hp, ht, htime⟩

/-- Holdings of a first-release vote envelope either belong to its source or give
an actual recipient processing cut between source time and the holding time.
The source alternative is not itself a fresh-processing claim. -/
theorem held_voteForward_source_or_process (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid)
    {source : Nat} {x y : Fin (Fintype.card V)} {τ d : Time}
    {m : SA.Vote (Fintype.card V)}
    (hx : rho.key x ∉ rho.faultyAt 0) (hs : rho.SendsAt (rho.key x) source τ)
    (hfirst : ∀ j < source,
      Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m] ∉
        rho.releasesAt j)
    (hh : rho.log.Held rho.point (rho.key y)
      (.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m]) d) :
    y = x ∨ ∃ k, (simTrace S rho hn).projAC.ProcessAt y k m ∧
      τ ≤ (simTrace S rho hn).time k ∧ (simTrace S rho hn).time k ≤ d := by
  obtain ⟨u, hud, hsend | hrecv, _⟩ := hh
  · obtain ⟨i, hi, hrel⟩ := hsend
    have hxy : x = rho.ownKey (rho.key y) := by
      rcases hi with he | ⟨o, he⟩
      · simp only [Model.Run.releasesAt, he] at hrel
        rcases rho.tick_auth _ _ _ hrel with h | ⟨r, h, _⟩
        · cases h
        · exact (Model.Auth.signed.inj h).1
      · simp only [Model.Run.releasesAt, he] at hrel
        rcases rho.deliver_auth _ _ _ _ hrel with h | ⟨r, h, _⟩
        · cases h
        · exact (Model.Auth.signed.inj h).1
    exact Or.inl (hxy.trans (rho.key.symm_apply_apply y)).symm
  · obtain ⟨i, hi⟩ := hrecv
    obtain ⟨k, _, _, hp, ht, hτ⟩ := received_voteForward_processAt S rho hn hconst hv hx hs
      hfirst hi (.refl _)
    have hkey : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply y
    rw [hkey] at hp
    exact Or.inr ⟨k, hp, ht ▸ hτ, ht ▸ hud⟩

/-- Option C's publication supplier: actual same-event release and first release,
not merely candidate construction or pool membership. -/
theorem simTrace_vote_forwarded {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    :
    ∀ y ∈ honestKeys ⟨S, stock⟩ rho, ∀ k (m : SA.Vote (Fintype.card V)),
    let tr := simTrace ⟨S, stock⟩ rho hn
    (tr.EmitAt y k m ∨
      ((tr.MsgCallAt y k m ∨ ∃ ℓ B, tr.CallAt y k (.ac ℓ) ∧ ℓ.call = .block B ∧
          m ∈ SA.blockVotes B) ∧
        m ∉ (tr.state y k).ac.pool m.slot ∧ m ∈ (tr.post k).ac.pool m.slot)) →
    let envelope : (Model.protoOf (compiled (goldilocksWith ⟨S, stock⟩)) E).Object :=
      .mk (.signed y .poll) (.data (.voteForward (tr.time k) (encodeVote m))) [voteObj m]
    ∃ i, cutMap ⟨S, stock⟩ rho hn i ≤ k ∧ k < cutMap ⟨S, stock⟩ rho hn (i + 1) ∧
      rho.SendsAt (rho.key y) i (tr.time k) ∧ envelope ∈ rho.releasesAt i ∧
      ∀ j < i, envelope ∉ rho.releasesAt j := by
  intro y hy k m
  dsimp only
  intro hsource
  have hevent : ∃ i, cutMap ⟨S, stock⟩ rho hn i ≤ k ∧ k < cutMap ⟨S, stock⟩ rho hn (i + 1) ∧
      rho.SendsAt (rho.key y) i ((simTrace ⟨S, stock⟩ rho hn).time k) := by
    rcases hsource with ⟨ℓ, hc, e, he, -⟩ | ⟨hc, -, -⟩
    · exact simTrace_call_sending_event ⟨S, stock⟩ rho hn hc
        (simTrace_emission_not_restart ⟨S, stock⟩ rho hn hconst hv hy hc he)
    · rcases hc with ⟨ℓ, hc, hm⟩ | ⟨ℓ, B, hc, hb, -⟩
      · exact simTrace_call_sending_event ⟨S, stock⟩ rho hn hc (by rw [hm]; simp)
      · exact simTrace_call_sending_event ⟨S, stock⟩ rho hn hc (by rw [hb]; simp)
  obtain ⟨i, hlo, hhi, hs⟩ := hevent
  have hfresh : m ∉ ((simTrace ⟨S, stock⟩ rho hn).state y k).ac.pool m.slot := by
    rcases hsource with hem | ⟨-, hf, -⟩
    · have hr := simTrace_goldilocksRun S rho hn hconst hv
      obtain ⟨ℓ, hc, e, he, hev⟩ := hem
      have hΦ : FrameOK ℓ.frame :=
        (hr.cutLaw y hy k _ hc).1 ▸
          (Store.frame_realization _ _ _ _ (Compose.fg_reachable hr.toLocalRun hy k)).1
      have hsign := SA.step_emission_signer y _ ℓ.frame _ ℓ.call
        hΦ
        (hr.time_nonneg k) (by
          rw [(hr.cutLaw y hy k _ hc).2.1]
          exact he)
      have hm : m.val = y := hev ▸ hsign
      have hf := Compose.emitted_slot_not_pooled hr hy hy
        (Nat.le_refl k) ⟨ℓ, hc, e, he, hev⟩ hm rfl m.slot
      simpa only [Compose.projAC_state hr.toLocalRun hy] using hf
    · exact hf
  have hcall : (simTrace ⟨S, stock⟩ rho hn).IsCall y k := by
    rcases hsource with ⟨ℓ, hc, -⟩ | ⟨hc, -⟩
    · exact ⟨_, hc⟩
    · rcases hc with ⟨ℓ, hc, -⟩ | ⟨ℓ, B, hc, -⟩ <;> exact ⟨_, hc⟩
  have hpost : m ∈ ((simTrace ⟨S, stock⟩ rho hn).post k).ac.pool m.slot := by
    rcases hsource with hem | ⟨-, -, hpost⟩
    · exact Compose.emitted_vote_mem_post (simTrace_goldilocksRun S rho hn hconst hv) hy hem
    · exact hpost
  obtain ⟨hold, hnew⟩ := sending_event_pool_insertion S rho hn hconst hv hy hs hlo hhi
    hcall hfresh hpost
  refine ⟨i, hlo, hhi, hs, ?_, admission_voteForward_first S rho hn hconst hv hy hs hlo hhi hfresh⟩
  rcases hs with he | ⟨o, he⟩
  · have hr := tick_pool_insertion_released ⟨S, stock⟩ rho hn hconst hv
      ((mem_honestKeys_iff ⟨S, stock⟩ rho y).mp hy) he m hold hnew
    simp only [Model.Run.ownKey, Equiv.symm_apply_apply] at hr
    exact hr
  · have hr := delivery_pool_insertion_released ⟨S, stock⟩ rho hn hconst hv he m hold hnew
    simp only [Model.Run.ownKey, Equiv.symm_apply_apply] at hr
    exact hr

/-- The simulating trace and cut map of a valid engine run simulate it. -/
theorem simTrace_simulates {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    :
    Simulates ⟨S, stock⟩ rho hn (simTrace ⟨S, stock⟩ rho hn) (cutMap ⟨S, stock⟩ rho hn) where
  run := simTrace_goldilocksRun S rho hn hf hv
  ι_zero := cutMap_zero ⟨S, stock⟩ rho hn
  ι_mono := cutMap_mono ⟨S, stock⟩ rho hn
  covered := simTrace_covered ⟨S, stock⟩ rho hn
  state := simTrace_state ⟨S, stock⟩ rho hn hf hv
  now := now_eq_lastClock ⟨S, stock⟩ rho hn hv
  tick_public := simTrace_tick_public_group ⟨S, stock⟩ rho hn hf hv
  tick_other := simTrace_tick_other ⟨S, stock⟩ rho hn hv
  deliver := simTrace_deliver ⟨S, stock⟩ rho hn hf hv
  restart := simTrace_restart ⟨S, stock⟩ rho hn hf hv
  awake_of := simTrace_awake_of ⟨S, stock⟩ rho hn hv
  awake_to := simTrace_awake_to ⟨S, stock⟩ rho hn hv
  block_released := simTrace_block_released ⟨S, stock⟩ rho hn hf hv
      (simTrace_goldilocksRun S rho hn hf hv)
  vote_released := simTrace_vote_released ⟨S, stock⟩ rho hn hf hv
      (simTrace_goldilocksRun S rho hn hf hv)
  att_released := simTrace_att_released ⟨S, stock⟩ rho hn hf hv
      (simTrace_goldilocksRun S rho hn hf hv)
  block_relayed := simTrace_block_relayed ⟨S, stock⟩ rho hn hv
  vote_forwarded := simTrace_vote_forwarded S rho hn hf hv
  att_relayed := simTrace_att_relayed ⟨S, stock⟩ rho hn hv

/-- **The engine simulates the node** (`EngineSimulatesNode`): every valid engine run of the
family is simulated by `simTrace` with `cutMap`. -/
theorem engineSimulatesNode (V : Type) [Fintype V] [DecidableEq V] (S : Setup)
    : EngineSimulatesNode V ⟨S, stock⟩ :=
  (engineSimulatesNode_iff V ⟨S, stock⟩).mpr
    fun _ rho hn hf hv =>
        ⟨simTrace ⟨S, stock⟩ rho hn, cutMap ⟨S, stock⟩ rho hn, simTrace_simulates S rho hn hf hv⟩

end Consensus.Goldilocks.Simulation

end
