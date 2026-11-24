module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Release
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.GoldilocksStateAgreement
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeOpLawsInstance

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
      (∀ ℓ, r.label = .ac ℓ → ∀ m ∈ ℓ.emits, ∃ z, voteObj m.msg z ∈ rho.releasesAt i) := by
  intro r hr
  have hEC := eventCuts_tick_public S rho hn i v t he hp
  have hlab : r.label ∈ (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      (stateAt S rho hn v i).node t
      (.tick (encodeTxs (Model.mempool rho.inbox v t)) (S.sign (pubOf E) (rho.ownKey v) t))).2 := by
    rw [hEC] at hr
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hr
    obtain ⟨-, -, -, -, hl⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
    rw [hl]; exact List.getElem_mem _
  have hv' : v ∉ rho.faultyAt 0 := event_honest_zero S rho hv he
  obtain ⟨N4, N5, Q, R4, F, G, heq, -, -, -, -, hQlen, hQ, -, -⟩ :=
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
  have hrelQ : ∀ q ∈ Q, rho.ownKey v ∈ rho.sel (pollRole S.vote (pubOf E).n q) →
      pollObj S rho v q ∈ rho.releasesAt i := by
    intro q hq hk
    rw [heq]
    rcases hpos q hq with h | h
    · refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      apply List.mem_append_left
      rw [h]; simp [relHead_eq, hk]
    · refine List.mem_append_left _ (List.mem_append_right _ ?_)
      rw [h]; simp [relHead_eq, hk]
  refine ⟨fun B acc hB hpos => ?_, fun ℓ hℓ m hm => ?_⟩
  · obtain ⟨q, hq, hqp, hql, _⟩ := eventCuts_source S rho hn i hr
    have h := NodeAsChainShape.CanonicalTrace.tick_block_released (traceEncoding S hn) rho
      (traceEncoding_opLaws S hn) (goldilocks_ready S hn) hv he hp q hq B acc
      (hql.symm.trans hB) (hqp ▸ hpos)
    have hobj : NodeAsChainShape.CanonicalTrace.engineObj (traceEncoding S hn)
        (NodeAsChainShape.blockObj (traceEncoding S hn).codec.encode
          (traceEncoding S hn).codec.carried B) = blockObj (S.params (pubOf E) hn) B := by
      apply traceEncoding_induction S hn (fun e _ _ =>
        NodeAsChainShape.CanonicalTrace.engineObj e
          (NodeAsChainShape.blockObj e.codec.encode e.codec.carried B) = blockObj _ B)
      intro _ _
      rw (config := { transparency := .default }) [NodeAsChainShape.CanonicalTrace.engineObj_eq,
        cast_eq]
      rfl
    rwa [hobj] at h
  · have hcut := hℓ ▸ hlab
    have hval := emits_val_of_mem_exec _ _ _ _ _ _ hcut m hm
    have hk := exec_emit_selected S rho hn hv hcut m hm
    obtain ⟨z, hz⟩ := stateAt_ownToken_exists S rho hn hv v i m.msg
      (emits_mayVote_of_mem_exec _ _ _ _ _ _ hcut m hm)
    have hq : Body.vote (encodeVote m.msg) z ∈ Q := by
      rw [hQ]
      exact List.mem_append_left _ (mem_emitted.mpr ⟨⟨ℓ, hcut, m, hm, rfl⟩, hz⟩)
    refine ⟨z, ?_⟩
    rw [voteObj_eq_pollObj S rho z (show m.msg.val = rho.ownKey v from hval)]
    exact hrelQ _ hq (by rw [pollRole_vote]; exact hk)

end Consensus.Goldilocks.Simulation
