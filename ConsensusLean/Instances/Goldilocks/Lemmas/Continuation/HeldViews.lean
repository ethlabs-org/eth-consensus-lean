module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Cuts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run

public section

/-! # Held attestations in an honest engine view, at any trace cut

`held_att_in_view_at` puts the attestations of a reader's tree in its engine view when the
reader is read at a mapped cut `cutMap i`. The continuation's conviction bridge reads trees at
arbitrary trace cuts: a node honest at `t ≥ 0`, before a cut `i` whose earlier cuts are at or
before `t`.

* `held_atts_in_view_at`: such a tree's attestations are in the node's engine view `ViewIdx`
  at an engine cut `q` at which the node is still honest. `q` is the first engine cut whose
  mapped cut covers every labelled trace cut before `i`; the last event before `q` has a trace
  cut before `i`, so `cutTime q ≤ t`. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- A labelled trace cut is before the end of the mapped cuts. -/
private theorem lt_cutMap_length {k : Nat} (hk : (simTrace S rho hn).label k ≠ none) :
    k < cutMap S rho hn rho.events.length := by
  obtain ⟨_, i, _, _, he, _, hki, -⟩ := simTrace_cut S rho hn hk
  exact hki.trans_le (cutMap_mono S rho hn (List.getElem?_eq_some_iff.mp he).1)

/-- The engine cut after an event with a trace cut is at that cut's time. -/
private theorem cutTime_succ_eq {q : Nat}
    (hq : cutMap S rho hn q < cutMap S rho hn (q + 1))
    (hlen : cutMap S rho hn q < cutMap S rho hn rho.events.length) :
    rho.cutTime (q + 1) = (simTraceAt S rho hn).time (cutMap S rho hn q) := by
  have hl : (simTrace S rho hn).label (cutMap S rho hn q) ≠ none := by
    rw [simTrace_label, List.getElem?_eq_getElem (by rw [length_allCuts]; exact hlen)]
    simp
  obtain ⟨_, i, ev, _, he, hlo, hhi, -, -, ht, -⟩ := simTrace_cut S rho hn hl
  obtain rfl : i = q := by
    rcases lt_trichotomy i q with h | rfl | h
    · have := cutMap_mono S rho hn (show i + 1 ≤ q by omega)
      omega
    · rfl
    · have := cutMap_mono S rho hn (show q + 1 ≤ i by omega)
      omega
  rw [simTraceAt_eq, ht]
  simp [Model.Run.cutTime, he]

/-- **The held attestations of a node honest at `t` are in its view at an honest engine cut.**
For a node honest at `t ≥ 0`, before a trace cut `i` whose earlier cuts are at or before `t`,
there is an engine cut `q` at which the node is honest whose view holds every attestation on a
block of the node's tree. -/
theorem held_atts_in_view_at (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)} {i : Nat}
    {t : Time} (ht : 0 ≤ t) (hi : ∀ k < i, (simTraceAt S rho hn).time k ≤ t)
    (hy : y ∈ honestKeysAt S rho t) :
    ∃ q ≤ rho.events.length, rho.key y ∉ rho.faultyAt (rho.cutTime q) ∧
      ∀ B ∈ ((simTraceAt S rho hn).state y i).fg.tree, ∀ a ∈ B.fgPayload,
        attObj a ∈ rho.ViewIdx (rho.key y) q := by
  classical
  set m := min i (cutMap S rho hn rho.events.length)
  have hex : ∃ q, q ≤ rho.events.length ∧ m ≤ cutMap S rho hn q :=
    ⟨_, le_rfl, min_le_right _ _⟩
  obtain ⟨hql, hqm⟩ := Nat.find_spec hex
  set q := Nat.find hex
  have hown : rho.ownKey (rho.key y) = y := by
    simp [Model.Run.ownKey]
  refine ⟨q, hql, ?_, fun B hB a ha => ?_⟩
  · have hle : rho.cutTime q ≤ min t rho.horizon := by
      refine le_min ?_ (cutTime_bounds S rho hv hql).2
      by_cases h0 : q = 0
      · rw [h0]
        simpa [Model.Run.cutTime] using ht
      · obtain ⟨q', hq'⟩ := Nat.exists_eq_succ_of_ne_zero h0
        have hmin := Nat.find_min hex (show q' < q by omega)
        have hq'l : q' ≤ rho.events.length := by omega
        have hlt : cutMap S rho hn q' < m := by
          by_contra h
          exact hmin ⟨hq'l, not_lt.mp h⟩
        rw [hq'] at hqm ⊢
        rw [cutTime_succ_eq S rho hn (lt_of_lt_of_le hlt hqm)
          (lt_of_lt_of_le hlt (min_le_right _ _))]
        exact hi _ (lt_of_lt_of_le hlt (min_le_left _ _))
    exact fun hf => (mem_honestKeysAt_iff S rho t y).mp hy (rho.faultyAt_mono hle hf)
  · have hrun := (simTraceAt_goldilocksRun S rho hn hv).upTo ht
    rw [← Trace.upTo_state _ y hi] at hB
    rcases Compose.tree_cases hrun.toLocalRun hy hB with hgen | ⟨k, hk, hacc⟩
    · subst B
      simp [Params.genesisBlock] at ha
    · have hacc' := ((RunTrace.upTo_acceptAt _).mp hacc).2
      have hl : (simTrace S rho hn).label k ≠ none := by
        rw [simTraceAt_eq] at hacc'
        rw [hacc'.2]
        simp
      have hkq : k < cutMap S rho hn q :=
        lt_of_lt_of_le (lt_min hk (lt_cutMap_length S rho hn hl)) hqm
      rw [← hown] at hacc'
      have hb := accepted_in_view_at S rho hn hv hacc' hkq
      obtain ⟨j, o, hj, ho, hc⟩ := rho.mem_viewIdx_iff.mp hb
      refine rho.mem_viewIdx_iff.mpr ⟨j, o, hj, ho, hc.trans (.step ?_ (.refl _))⟩
      change attObj a ∈ payloadObjs B.fgPayload B.acPayload
      exact List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩)

end Consensus.Goldilocks.Simulation

end
