module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.PublishedVotes

public section

/-! # Attestation publication through an honest tick -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- A tick's signed attestation is released at that tick. -/
theorem tick_att_releases_at (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) :
    ∀ r ∈ eventCuts S rho hn i, ∀ C a,
      r.label = .fg (.attest C (some a)) → attObj a ∈ rho.releasesAt i := by
  intro r hr C a ha
  have hEC := eventCuts_tick_public S rho hn i v t he hp
  have hlab : r.label ∈ (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      (stateAt S rho hn v i).node t
      (.tick (encodeTxs (Model.mempool rho.inbox v t)) (S.sign (pubOf E) (rho.ownKey v) t))).2 := by
    rw [hEC] at hr
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hr
    obtain ⟨-, -, -, -, hl⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
    rw [hl]; exact List.getElem_mem _
  have hv' : v ∉ rho.faultyAt 0 := event_honest_zero S rho hv he
  obtain ⟨N4, N5, Q, R4, F, G, heq, -, -, -, -, hQlen, hQ, -, -, -⟩ :=
    tick_public_analysis S rho hn hv hv' he hp (preNode_releasable_at S rho hn hv he)
  have hval := attest_val_of_mem_exec _ _ _ _ _ _ (ha ▸ hlab)
  have hq : Body.att (encodeAtt a) ∈ Q := by
    rw [hQ]
    apply List.mem_append_right
    rw [attBodies_eq]
    exact List.mem_flatMap.mpr ⟨_, ha ▸ hlab, List.mem_singleton_self _⟩
  have hobj : (attObj a : (Model.protoOf (compiled (goldilocks S)) E).Object) =
      pollObj S rho v (.att (encodeAtt a)) := attObj_eq_pollObj_of_val S rho hval
  have hpos : ∀ q ∈ Q, Q.head? = some q ∨ Q.tail.head? = some q := by
    intro q hq
    match Q, hQlen, hq with
    | [a], _, hq => rw [List.mem_singleton] at hq; subst hq; exact Or.inl rfl
    | [a, b], _, hq =>
      rcases List.mem_pair.mp hq with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    | _ :: _ :: _ :: _, h, _ => simp at h
  rw [hobj, heq]
  have hk := pollRole_selected_of_not_vote S rho (poll_selected S rho hv v)
    (b := .att (encodeAtt a)) (fun _ _ h => by cases h)
  rcases hpos _ hq with h | h
  · refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
    apply List.mem_append_left
    rw [h]
    simp only [relHead_eq, Option.elim_some, hk, ↓reduceIte]
    exact List.mem_singleton_self _
  · refine List.mem_append_left _ (List.mem_append_right _ ?_)
    rw [h]
    simp only [relHead_eq, Option.elim_some, hk, ↓reduceIte]
    exact List.mem_singleton_self _

/-- A trace signing is released at its actual engine tick, under growing faults. -/
theorem simTraceAt_att_released (hv : rho.ExecutionValid) :
    ∀ y k a, y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time k) →
      (simTraceAt S rho hn).SignAt y k a →
      ReleasedFrom S rho (rho.key y) (attObj a) ((simTraceAt S rho hn).time k) := by
  rw [simTraceAt_eq]
  rintro y k a _ ⟨src, hnode, hlab⟩
  erw [releasedFrom_iff]
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
    exact ⟨i, Or.inl he, tick_att_releases_at S rho hn hv he hp r hmem src a hrl⟩
  | deliver v o t =>
    exfalso
    rw [eventCuts_deliver S rho hn i v o t he] at hmem
    obtain ⟨o', e, st', _, hce, kk, hk, hlabk, -⟩ :=
      mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ _ hmem
    have hcut := List.getElem_mem hk
    rw [← hlabk, hrl] at hcut
    obtain ⟨x, rfl⟩ := Compose.signed_only_in_ticks _ _ _ st' t e src a hcut
    exact canonEvent_ne_tick hce x true rfl
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

end Consensus.Goldilocks.Simulation
