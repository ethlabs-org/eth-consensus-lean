module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunBlocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Accountable
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EmitRelease
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EventGroups
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Goldilocks Simulation: the engine agrees with the simulating trace

Every labelled cut lies in an engine event's range, the engine's node states agree with the
trace's states, and a delivery relays what the trace admits. The growing-fault simulation
`simTraceAt_simulates` (`Growing/Simulation/Simulates`) reads these correspondence facts. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open AC (ACParams ReplayOrder Vote Payload declaredHeadVotes)

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
(`simTrace_state_of`). -/
theorem simTrace_state (_hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid) :
    ∀ v, v ∉ rho.faultyAt 0 → ∀ i ≤ rho.events.length,
      (stateAt S rho hn v i).node =
        (simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i) := by
  intro v hv'
  exact simTrace_state_of S rho hn hv (fun _ _ => hv')

/-- The engine's Goldilocks state at a delivery: at the delivery's time, with the own key. -/
private theorem deliver_state (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {o : (Model.protoOf (compiled (goldilocks S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) :
    (stateAt S rho hn v i).now = t ∧ (stateAt S rho hn v i).self = rho.ownKey v :=
  ⟨(now_eq_lastClock S rho hn hv v i).trans (lastClock_deliver S rho hv he),
    self_eq_ownKey S rho hn v i⟩

/-- A cut of a delivery to an honest node, not an own admission: its delivered object is queued
by the delivery's `process` (`process_relay`) and relayed by the delivery's gossip at its own time
(`deliver_relays`), as a carried object of a released relay wrapper. -/
theorem relays_of_cut (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)} {k : Nat}
    (hnode : (simTrace S rho hn).node k = y) (hl : (simTrace S rho hn).label k ≠ none)
    (hdel : ∀ r : CutRec (S.params (pubOf E) hn) (S.ro _), (allCuts S rho hn)[k]? = some r →
      (r.pos = 0 ∧ ∃ ℓ, r.label = .fg ℓ) ∨ ∃ ℓ m, r.label = .ac ℓ ∧ ℓ.call = .message m)
    (hown : ∀ r : CutRec (S.params (pubOf E) hn) (S.ro _), (allCuts S rho hn)[k]? = some r →
      ∀ a, r.label = .fg (.attestation a) → ∀ v i t, r ∉ tickTail S rho hn v i t) :
    ∃ r : CutRec (S.params (pubOf E) hn) (S.ro _),
      (simTrace S rho hn).label k = some r.label ∧ (simTrace S rho hn).post k = r.post ∧
      ∀ x, ((∃ B, r.label = .fg (.block B true) ∧ x = blockObj (S.params (pubOf E) hn) B) ∨
          (∃ a, r.label = .fg (.attestation a) ∧ x = attObj a)) →
        ∃ cs, x ∈ cs ∧ rho.releases (rho.key y) (.mk .none (.data .relay) cs)
          ((simTrace S rho hn).time k) := by
  obtain ⟨r, i, ev, hr, he, -, -, hidx, hn', ht, -, hlab⟩ := simTrace_cut_origin S rho hn hl
  have hmem := List.mem_of_getElem? hidx
  obtain ⟨v, o, t, rfl⟩ | ⟨w, τ, rfl, htl⟩ := eq_deliver_of_cut S rho hn he hmem (hdel r hr)
  swap
  · -- an own admission carries an attestation label, which `hown` excludes
    refine ⟨r, hlab, by rw [simTrace_post, hr]; rfl, fun x hx => absurd htl ?_⟩
    obtain ⟨-, a, ha⟩ := tickTail_label S rho hn htl
    rcases hx with ⟨B, hB, -⟩ | ⟨a', ha', -⟩
    · rw [ha] at hB; cases hB
    · exact hown r hr a' ha' w i τ
  change (simTrace S rho hn).node k = rho.ownKey v at hn'
  simp only [Model.Event.time] at ht
  have hkey : v = rho.key y := key_of_ownKey S rho (hn'.symm.trans hnode)
  subst hkey
  refine ⟨r, hlab, by rw [simTrace_post, hr]; rfl, fun x hx => ?_⟩
  rw [ht]
  rw [eventCuts_deliver S rho hn i _ o t he] at hmem
  obtain ⟨hnow, hself⟩ := deliver_state S rho hn hv he
  obtain ⟨h1, -, h3⟩ := (process_relay (runProposer S rho hn)
    (digestOf S rho) (stateAt S rho hn (rho.key y) i).voteIO (Model.digests rho.hash o) t i
    (delivered (stateAt S rho hn (rho.key y) i).voteIO
      (Model.digests rho.hash o) (stateAt S rho hn _ i) o)
      (stateAt S rho hn _ i) 0 hnow).2.2.2 r
    (by rw [hself, stateAt_voteIO]; exact hmem)
  have hq : x ∈
      (process (stateAt S rho hn (rho.key y) i) o (Model.digests rho.hash o)).relayBuf := by
    rcases hx with ⟨B, hB, rfl⟩ | ⟨a, ha, rfl⟩
    · exact h1 B hB
    · exact h3 a ha
  obtain ⟨cs, hxcs, hrel⟩ := deliver_relays S rho hn he hq
  exact ⟨cs, hxcs, i, Or.inr ⟨o, he⟩, hrel⟩

end Consensus.Goldilocks.Simulation

end
