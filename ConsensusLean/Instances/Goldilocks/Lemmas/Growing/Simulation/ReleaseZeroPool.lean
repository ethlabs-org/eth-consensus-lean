module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ReleaseZero
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.SignCut
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ReleaseTick
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.PrefixSteps

public section

/-! # Goldilocks Simulation: own attestations in the pool, and the exact stock admission

An own attestation in a node's pool was signed by the node before (`pool_own_signAt`): the pool
holds only processed attestations (own ones admitted at their release, others delivered or carried
by an accepted block), and an attestation of a signer honest at its processing was signed by it at
an earlier cut. A node signs an attestation once (`Healing.sign_unique`), so on a valid run the
attestation that a tick's FG update actually signs is not yet in the node's pool
(`fgSigned_not_mem_pool`). At the stock schedule (`release ≡ true`), where the own admission at
release is at the signing tick, a tick therefore admits exactly the attestation its FG update
signs, with no filter on the pool (`admitsAt_tick_of_release_signed`).

The argument reads the prefix of the canonical trace through the event's time, a static run
for the keys honest then (`prefix_reader_at`); the event's node is one of them, since an engine
event is at a node honest at its time.

Every step is proved. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The prefix of the canonical trace through the time of engine event `i` of `v` is a static run
for the keys honest then, `v`'s key among them, and it reads `v`'s state at `cutMap i` as the
trace does. -/
private theorem event_prefix (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {ev : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object}
    (he : rho.events[i]? = some ev) (hnode : ev.node = v) :
    GoldilocksRun (runProposer S rho hn) (digestOf S rho)
        (honestKeysAt S rho (rho.cutTime (i + 1)))
        ((simTraceAt S rho hn).upTo (rho.cutTime (i + 1))) (simIni S rho hn) ∧
      rho.ownKey v ∈ honestKeysAt S rho (rho.cutTime (i + 1)) ∧
      ((simTraceAt S rho hn).upTo (rho.cutTime (i + 1))).state (rho.ownKey v)
          (cutMap S rho hn i) = (simTraceAt S rho hn).state (rho.ownKey v) (cutMap S rho hn i) ∧
      ∀ k < cutMap S rho hn (i + 1), (simTraceAt S rho hn).time k ≤ rho.cutTime (i + 1) := by
  have hi : i + 1 ≤ rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  have hct : rho.cutTime (i + 1) = ev.time := by simp only [Model.Run.cutTime, he]
  have hh : v ∉ rho.faultyAt (rho.cutTime (i + 1)) := by
    rw [hct, ← hnode]
    exact hv.honest_only ev (List.mem_of_getElem? he)
  obtain ⟨hrun, hy, -⟩ := prefix_reader_at S rho hn hv hi hh
  exact ⟨hrun, hy, upTo_state_cutMap S rho hn hv (Nat.le_succ i) hi _,
    cutMap_time_le S rho hn hv hi⟩

/-- **An own attestation in a node's pool was signed by the node before.** Before an engine event
of `v`, every attestation of `v`'s key in `v`'s pool was signed by `v` at a cut of the canonical
trace before the event's cuts: an attestation enters the pool only by its processing (the own
admission at release, a delivery, or an accepted block's payload), and an attestation of a signer
honest at its processing was signed by it at an earlier cut. -/
theorem pool_own_signAt (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {ev : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object}
    (he : rho.events[i]? = some ev) (hnode : ev.node = v) {a : FG.Att (Fintype.card V)}
    (ha : a ∈ (stateAt S rho hn v i).node.fg.atts) (hval : a.val = rho.ownKey v) :
    ∃ j < cutMap S rho hn i, (simTrace S rho hn).SignAt (rho.ownKey v) j a := by
  have hi : i ≤ rho.events.length := (List.getElem?_eq_some_iff.mp he).1.le
  obtain ⟨hrun, hy, hstate, -⟩ := event_prefix S rho hn hv he hnode
  rw [simTraceAt_state_all S rho hn hv v i hi, ← hstate] at ha
  obtain ⟨k, hk, hp⟩ := Healing.pool_processed hrun.toLocalRun hy ha
  obtain ⟨j, hj, hs⟩ := hrun.att_unforgeable _ hy k a
    (hp.imp id fun ⟨B, hB, hB'⟩ => ⟨B, ⟨true, hB⟩, hB'⟩) (hval ▸ hy)
  rw [hval, RunTrace.upTo_signAt, simTraceAt_eq] at hs
  exact ⟨j, hj.trans hk, hs.2⟩

/-- **The attestation a tick actually signs is not yet in the node's pool.** On a valid run, when
the FG update of a tick's first trailing poll is due and signs `a`, `a` is not in the pool before
the tick: an own attestation there was signed at an earlier cut, and a node signs an attestation
once. -/
theorem fgSigned_not_mem_pool (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t))
    (hdue : (shapeOf S hn (beforeTrailing S rho v i t)).fgDue = true)
    {a : FG.Att (Fintype.card V)}
    (ha : fgSigned (shapeOf S hn (beforeTrailing S rho v i t)) = some a) :
    a ∉ (stateAt S rho hn v i).node.fg.atts := by
  intro hmem
  obtain ⟨p, hcut, hw, hpoll⟩ := beforeTrailing_dutyCut S rho hv he
  have hs := engineSignsAt_of_fgSigned S rho hn hv he hcut hw hpoll hdue ha
  obtain ⟨t', he', hp, C, hc⟩ := engineSignsAt_tick_cut S rho hn hv hs
  obtain rfl : t' = t := (Model.Event.tick.inj (Option.some.inj (he'.symm.trans he))).2
  obtain ⟨k, hik, hki, hsk⟩ := signAt_in_tick S rho hn he hp hc
  obtain ⟨j, hj, hsj⟩ := pool_own_signAt S rho hn hv he rfl hmem
    (attest_val_of_mem_exec _ _ _ _ _ _ hc)
  obtain ⟨hrun, hy, -, htime⟩ := event_prefix S rho hn hv he rfl
  have hk : ((simTraceAt S rho hn).upTo (rho.cutTime (i + 1))).SignAt (rho.ownKey v) k a := by
    rw [RunTrace.upTo_signAt, simTraceAt_eq]
    exact ⟨by simpa only [simTraceAt_eq] using htime k hki, hsk⟩
  have hj' : ((simTraceAt S rho hn).upTo (rho.cutTime (i + 1))).SignAt (rho.ownKey v) j a := by
    rw [RunTrace.upTo_signAt, simTraceAt_eq]
    exact ⟨by simpa only [simTraceAt_eq] using htime j (by omega), hsj⟩
  have := Healing.sign_unique hrun hy hj' hk
  omega

/-- **At the stock schedule a tick admits exactly the attestation its FG update signs**: the
plain form of `admitsAt_tick_of_release_eq`, whose filter on the pool removes nothing
(`fgSigned_not_mem_pool`). -/
theorem admitsAt_tick_of_release_signed (hR : S.release (pubOf E) = fun _ _ => true)
    (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) :
    admitsAt S rho hn v i =
      (if (shapeOf S hn (beforeTrailing S rho v i t)).fgDue then
        fgSigned (shapeOf S hn (beforeTrailing S rho v i t)) else none).toList := by
  rw [admitsAt_tick_of_release_eq S rho hn hR hv he, List.filter_eq_self]
  intro a ha
  split at ha
  · rename_i hdue
    have hs : fgSigned (shapeOf S hn (beforeTrailing S rho v i t)) = some a := by
      simpa only [Option.mem_toList, Option.mem_def] using ha
    simpa only [decide_eq_true_eq] using fgSigned_not_mem_pool S rho hn hv he hdue hs
  · cases ha

end Consensus.Goldilocks.Simulation
