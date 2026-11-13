module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Release

public section

/-! # Publication at an engine tick with growing faults

Blocks and votes do not pass through the attestation conflict guard. Their publication
therefore needs only the local proposal inventory, not a static honest-origin invariant.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- Every block and vote emitted by a public tick is released at that engine event. -/
theorem tick_block_vote_releases_at (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {t : Time} (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) :
    ∀ r ∈ eventCuts S rho hn i,
      (∀ B acc, r.label = .fg (.block B acc) → r.pos ≠ 0 →
        blockObj (S.params (pubOf E) hn) B ∈ rho.releasesAt i) ∧
      (∀ ℓ, r.label = .ac ℓ → ∀ m ∈ ℓ.emits, voteObj m.msg ∈ rho.releasesAt i) := by
  intro r hr
  have hEC := eventCuts_tick_public S rho hn i v t he hp
  have hlab : r.label ∈ (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      (stateAt S rho hn v i).node t
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2 := by
    rw [hEC] at hr
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hr
    obtain ⟨-, -, -, -, hl⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
    rw [hl]; exact List.getElem_mem _
  have hv' : v ∉ rho.faultyAt 0 := event_honest_zero S rho hv he
  obtain ⟨N4, N5, Q, R4, F, G, heq, -, -, -, -, hQlen, hQ, hR4, -⟩ :=
    tick_public_analysis S rho hn hv hv' he hp (preNode_releasable_at S rho hn hv he)
  have hpos : ∀ q ∈ Q, Q.head? = some q ∨ Q.tail.head? = some q := by
    intro q hq
    match Q, hQlen, hq with
    | [a], _, hq => rw [List.mem_singleton] at hq; subst hq; exact Or.inl rfl
    | [a, b], _, hq =>
      rcases List.mem_pair.mp hq with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    | _ :: _ :: _ :: _, h, _ => simp at h
  have hrelQ : ∀ q ∈ Q,
      Model.protects (Model.protoOf (compiled (goldilocks S)) E) (rho.ownKey v) N4.seen
        (pollObj S rho v q) = true →
      Model.protects (Model.protoOf (compiled (goldilocks S)) E) (rho.ownKey v) N5.seen
        (pollObj S rho v q) = true →
      pollObj S rho v q ∈ rho.releasesAt i := by
    intro q hq h4 h5
    have hd (seen) : (Model.protoOf (compiled (goldilocks S)) E).dependencies.ready
        (Model.closure seen) (pollObj S rho v q) = true := by
      change (dependencies _).ready _ (.mk (.signed _ .poll) (.data q) []) = true
      cases q <;> rfl
    rw [heq]
    rcases hpos q hq with h | h
    · refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      apply List.mem_append_left
      rw [h, ← release_head S rho v N4 (some q)]
      simp [Model.releaseAll, Model.releasable, Model.Obj.carried, h4, hd]
    · refine List.mem_append_left _ (List.mem_append_right _ ?_)
      rw [h, ← release_head S rho v N5 (some q)]
      simp [Model.releaseAll, Model.releasable, Model.Obj.carried, h5, hd]
  refine ⟨fun B acc hB _ => ?_, fun ℓ hℓ m hm => ?_⟩
  · rw [heq]
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ ?_)))
    rw [hR4, mem_blockObjs]
    exact ⟨B, acc, hB ▸ hlab, rfl⟩
  · have hval := emits_val_of_mem_exec _ _ _ _ _ _ (hℓ ▸ hlab) m hm
    have hq : Body.vote (encodeVote m.msg) ∈ Q := by
      rw [hQ]
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, hℓ ▸ hlab,
        List.mem_map.mpr ⟨m, hm, rfl⟩⟩)
    have hobj : @voteObj stock (pubOf E).n m.msg = pollObj S rho v (.vote (encodeVote m.msg)) := by
      unfold voteObj; rw [show m.msg.val = rho.ownKey v from hval]; rfl
    exact (congrArg (· ∈ rho.releasesAt i) hobj).mpr (hrelQ _ hq
      (protects_of_not_att S _ _ _ (fun k w h => by cases h))
      (protects_of_not_att S _ _ _ (fun k w h => by cases h)))

end Consensus.Goldilocks.Simulation
