module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Interface
import ConsensusLean.Lemmas.Model.Objects
import ConsensusLean.Lemmas.Model.DutyFold
import ConsensusLean.Lemmas.Model.Protection
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape

public section

/-! # Attestations released by engine duties

Node-local facts about the attestations an engine node's duties release: they come from a
selected poll's ordinary attestation candidate, gossip releases none, and an attestation seen
after duties was seen before them or released by them. Constant faults (`Provenance`) and
growing faults (`Growing/Simulation/Signing`) invert attestation releases with them. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)

variable {binding : VoteBinding}

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- Running the duties `ds ++ ds'` runs `ds`, then `ds'` from the node `ds` reach. -/
theorem runDuties_append (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (ds ds') :
    rho.runDuties v nd (ds ++ ds') =
      let r := rho.runDuties v nd ds
      let r' := rho.runDuties v r.1 ds'
      (r'.1, r.2 ++ r'.2) :=
  rho.runDuties_append v nd ds ds'

omit [DecidableEq V] in
/-- An attestation that a duty releases is a selected poll's: its ordinary attestation
candidate, or a held attestation the batch poll flushes at a time the release schedule allows. -/
theorem dutyStep_att_poll {v : V} (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (d : (Model.protoOf (compiled (goldilocks S)) E).Duty) {a : FG.Att (Fintype.card V)}
    (ha : attObj a ∈ (rho.dutyStep v nd d).2) :
    ∃ t, d = .poll t ∧ rho.ownKey v ∈ rho.sel .poll ∧
      ((poll (nd.st.1 hn) t (S.release (pubOf E))).2 = some (.att (encodeAtt a), []) ∨
        S.release (pubOf E) (nd.st.1 hn).self (nd.st.1 hn).now = true ∧
          a ∈ (nd.st.1 hn).held) := by
  unfold Model.Run.dutyStep at ha
  split at ha
  · rename_i hsel
    have hc := Model.releaseAll_subset _ _ _ _ _ ha
    obtain ⟨m, cs, hm, _, _, he⟩ := rho.mem_signedCandidate.mp hc
    have he' := he
    change (Model.Obj.mk (.signed a.val (ShapeRole.poll : ShapeRole S.vote.Kind))
      (.data (Body.att (encodeAtt a))) [] : Wire (Fintype.card V) S.vote) = _ at he'
    injection he' with hauth hmsg hcs
    subst m cs
    cases d with
    | act s k => exact absurd hm List.not_mem_nil
    | propose s hs =>
      have hr : (Model.protoOf (compiled (goldilocks S)) E).candidateRole (.propose s hs)
          (.data (.att (encodeAtt a))) = .proposer s := by
        change (S.vote.candidateRole _ (.propose s hs) (.data (.att (encodeAtt a)))).getD
          (.proposer s) = .proposer s
        rw [candidateRole_of_not_vote _ _ _ _ fun _ _ h => by cases h]
        rfl
      have hh : (ShapeRole.poll : ShapeRole S.vote.Kind) = .proposer s := by
        injection hauth with _ h
        exact h.trans hr
      cases hh
    | pollPropose t =>
      change _ ∈ (Option.map _ ((goldilocks S (pubOf E)).pollPropose nd.st.1 t).2).toList at hm
      rw [goldilocks_pollPropose_eq S _ nd.st.1 t, dite_eq_left hn] at hm
      cases hm
    | poll t =>
      refine ⟨t, rfl, hsel, ?_⟩
      change _ ∈ (((goldilocks S (pubOf E)).pollBatch nd.st.1 t).2.map
        (fun (b, cs) => (Model.Msg.data b, cs))) at hm
      rw [goldilocks_pollBatch_eq S _ nd.st.1 t, dite_eq_left hn] at hm
      change _ ∈ ((pollBatch (nd.st.1 hn) t (S.release (pubOf E))).2.map
        (fun (b, cs) => (Model.Msg.data b, cs))) at hm
      obtain ⟨⟨b, cs⟩, hb, heq⟩ := List.mem_map.mp hm
      have hp := Prod.mk.inj heq
      have hb' := Model.Msg.data.inj hp.1
      have hcs' := hp.2
      subst b cs
      rw [pollBatch_snd] at hb
      simp only [List.mem_append] at hb
      rcases hb with ((hb | hb) | hb) | hb
      · left
        split at hb
        · rw [poll_snd_heldDrain] at hb
          exact Option.mem_toList.mp hb
        · exact Option.mem_toList.mp hb
      · obtain ⟨p, _, heq⟩ := List.mem_map.mp hb
        cases heq
      · obtain ⟨p, _, heq⟩ := List.mem_map.mp hb
        cases heq
      · right
        split at hb
        · rename_i hr
          obtain ⟨b, hb, heq⟩ := List.mem_map.mp hb
          have hab : b = a := by
            have hh := congrArg (decodeAtt (Fintype.card V))
              (Body.att.inj (Prod.mk.inj heq).1)
            simpa only [decodeAtt_encodeAtt, Option.some.injEq] using hh
          exact ⟨(Bool.and_eq_true _ _).mp hr |>.1, hab ▸ hb⟩
        · cases hb
  · cases ha

omit [DecidableEq V] in
/-- Gossip releases no attestation. -/
theorem attObj_not_mem_gossip (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (k : Fin (Fintype.card V)) (t : Time) (a : FG.Att (Fintype.card V)) :
    attObj a ∉ (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) rho.hash k nd
      (Model.gossipCandidates (Model.protoOf (compiled (goldilocks S)) E) nd.st t)).2 := by
  intro ha
  obtain ⟨mc, _, he⟩ := Model.mem_gossipCandidates.mp
    (Model.releaseAll_subset _ _ _ _ _ ha)
  have hh := congrArg Model.Obj.auth he
  cases hh

omit [DecidableEq V] in
/-- An attestation in the closure of what a node has seen after duties was seen before them
or released by them. -/
theorem attObj_mem_closure_runDuties (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (ds)
    (a : FG.Att (Fintype.card V))
    (ha : attObj a ∈ Model.closure (rho.runDuties v nd ds).1.seen) :
    attObj a ∈ Model.closure nd.seen ∨ attObj a ∈ (rho.runDuties v nd ds).2 := by
  induction ds using List.reverseRecOn with
  | nil => exact Or.inl ha
  | append_singleton ds d ih =>
    rw [runDuties_append] at ha ⊢
    change _ ∨ attObj a ∈ _ ++ (rho.dutyStep v (rho.runDuties v nd ds).1 d).2
    change attObj a ∈ Model.closure (rho.dutyStep v (rho.runDuties v nd ds).1 d).1.seen at ha
    unfold Model.Run.dutyStep at ha ⊢
    split at ha
    · rename_i hsel
      simp only [hsel, ↓reduceIte]
      let Q := fun o => o = attObj (binding := S.vote) a →
        attObj a ∈ Model.closure (rho.runDuties v nd ds).1.seen ∨
          attObj a ∈ (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
            rho.hash (rho.ownKey v)
            ⟨((Model.protoOf (compiled (goldilocks S)) E).act (rho.runDuties v nd ds).1.st d).1,
              (rho.runDuties v nd ds).1.seen⟩
            (rho.signedCandidate v d
              ((Model.protoOf (compiled (goldilocks S)) E).act
                  (rho.runDuties v nd ds).1.st d).2)).2
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

end Consensus.Goldilocks.Simulation
