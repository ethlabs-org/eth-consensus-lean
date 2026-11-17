module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunBlocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Accountable
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EmitRelease
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EventGroups
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Goldilocks Simulation: the engine agrees with the simulating trace

The engine's events are the trace's groups, its node states agree with the trace's states,
and it releases and relays what the trace signs, emits and admits. The growing-fault simulation
`simTraceAt_simulates` (`Growing/Simulation/Simulates`) reads these correspondence facts. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload blockVotes)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-! ## The engine agrees with the trace -/

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

/-- The node state inside the shape's state is the trace's state at the mapped cut
(`simTrace_state_of`, with `node_of_tick_public` at the public ticks). -/
theorem simTrace_state (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid) :
    ∀ v, v ∉ rho.faultyAt 0 → ∀ i ≤ rho.events.length,
      (stateAt S rho hn v i).node =
        (simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i) := by
  intro v hv'
  exact simTrace_state_of S rho hn hv (fun _ _ => hv')
    (fun he hp => node_of_tick_public S rho hn hf hv v hv' _ _ he hp)

/-- An engine tick of an honest node at a public time is the node's tick with the engine's input,
one group. -/
theorem simTrace_tick_public_group (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid) :
    ∀ v, v ∉ rho.faultyAt 0 → ∀ i t, rho.events[i]? = some (.tick v t) →
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
  exact tick_public_group_of_state S rho hn he hp (simTrace_state S rho hn hf hv v hv' i hi.le)

/-- An honest node awake at a public time (from `0` on) ticks there. -/
theorem simTrace_tick_of_awake (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ t, 0 ≤ t → (S.params (pubOf E) hn).toParams.IsPublic t →
      (simTrace S rho hn).awake y t →
      ∃ j, (simTrace S rho hn).TickAt (runProposer S rho hn) (digestOf S rho) y j t := by
  intro y hy t ht0 hp hw
  rw [mem_honestKeys_iff] at hy
  obtain ⟨hwE, -, hth⟩ := (awake_iff' S rho hn y t).mp hw
  obtain ⟨i, he⟩ := List.mem_iff_getElem?.mp (hv.tick_total _ t ht0 hth
    (by simpa only [rho.faultyAt_eq_zero hf] using hy) hwE)
  obtain ⟨hg, -⟩ := simTrace_tick_public_group S rho hn hf hv _ hy i t he hp
  rw [ownKey_key] at hg
  exact ⟨_, _, hg⟩

/-- An engine tick at a non-public time has no cut. -/
theorem simTrace_tick_other (_hv : rho.ExecutionValid) :
    ∀ v, v ∉ rho.faultyAt 0 → ∀ i t, rho.events[i]? = some (.tick v t) →
      ¬ (S.params (pubOf E) hn).toParams.IsPublic t →
        cutMap S rho hn (i + 1) = cutMap S rho hn i := by
  intro v _ i t he hp
  rw [cutMap_succ, eventCuts_tick_other S rho hn i v t he hp, List.length_nil, Nat.add_zero]

/-- An engine delivery to an honest node is the groups of the canonical objects it delivers. -/
theorem simTrace_deliver (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid) :
    ∀ v, v ∉ rho.faultyAt 0 → ∀ i o t, rho.events[i]? = some (.deliver v o t) →
      DeliverSeq (runProposer S rho hn) (simTrace S rho hn) (digestOf S rho)
        (Model.digests rho.hash o) (rho.ownKey v) t
        (delivered (S.params (pubOf E) hn) o) (cutMap S rho hn i) (cutMap S rho hn (i + 1)) := by
  intro v hv' i o t he
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  exact deliver_seq_of_state S rho hn he (simTrace_state S rho hn hf hv v hv' i hi.le)

/-- An engine restart of an honest node is the node's restart group. -/
theorem simTrace_restart (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid) :
    ∀ v, v ∉ rho.faultyAt 0 → ∀ i t, rho.events[i]? = some (.restart v t) →
      (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho)
        (rho.ownKey v) (cutMap S rho hn i) t .restart ∧
        cutMap S rho hn (i + 1) = cutMap S rho hn i +
          (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
          ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t .restart).2.length := by
  intro v hv' i t he
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  exact restart_group_of_state S rho hn he (simTrace_state S rho hn hf hv v hv' i hi.le)

/-- The engine's Goldilocks state at a delivery: at the delivery's time, with the own key. -/
private theorem deliver_state (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {o : (Model.protoOf (compiled (goldilocks S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) :
    (stateAt S rho hn v i).now = t ∧ (stateAt S rho hn v i).self = rho.ownKey v :=
  ⟨(now_eq_lastClock S rho hn hv v i).trans (lastClock_deliver S rho hv he),
    self_eq_ownKey S rho hn v i⟩

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

end Consensus.Goldilocks.Simulation

end
