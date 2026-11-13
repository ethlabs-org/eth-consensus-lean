module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Interface
import ConsensusLean.Lemmas.Model.Objects
import ConsensusLean.Lemmas.Model.Candidates
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

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- Running the duties `ds ++ ds'` runs `ds`, then `ds'` from the node `ds` reach. -/
theorem runDuties_append (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (ds ds') :
    rho.runDuties v nd (ds ++ ds') =
      let r := rho.runDuties v nd ds
      let r' := rho.runDuties v r.1 ds'
      (r'.1, r.2 ++ r'.2) := by
  unfold Model.Run.runDuties
  rw [List.foldl_append]
  generalize ds.foldl _ _ = acc
  induction ds' generalizing acc with
  | nil => simp
  | cons d ds' ih =>
    dsimp only
    rw [List.foldl_cons, List.foldl_cons, ih]
    conv_rhs => rw [ih]
    simp only [List.append_assoc, List.nil_append]

omit [DecidableEq V] in
/-- An attestation that a duty releases is the ordinary attestation candidate of a selected
poll. -/
theorem dutyStep_att_poll {v : V} (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (d : (Model.protoOf (compiled (goldilocks S)) E).Duty) {a : FG.Att (Fintype.card V)}
    (ha : attObj a ∈ (rho.dutyStep v nd d).2) :
    ∃ t, d = .poll t ∧ rho.ownKey v ∈ rho.sel .poll ∧
      (poll (nd.st.1 hn) t).2 = some (.att (encodeAtt a), []) := by
  unfold Model.Run.dutyStep at ha
  split at ha
  · rename_i hsel
    have hc := Model.releaseAll_subset _ _ _ _ _ ha
    obtain ⟨m, cs, hm, _, _, he⟩ := rho.mem_signedCandidate.mp hc
    have he' := he
    change (Model.Obj.mk (.signed a.val (ShapeRole.poll : ShapeRole Empty))
      (.data (Body.att (encodeAtt a))) [] : Wire (Fintype.card V)) = _ at he'
    injection he' with hauth hmsg hcs
    subst m cs
    cases d with
    | act s k => exact k.elim
    | propose s hs =>
      have hh : (ShapeRole.poll : ShapeRole Empty) = .proposer s := by
        injection hauth
      cases hh
    | pollPropose t =>
      change _ ∈ (Option.map _ ((goldilocks S (pubOf E)).pollPropose nd.st.1 t).2).toList at hm
      simp only [goldilocks, goldilocksWith, dite_eq_left hn] at hm
      cases hm
    | poll t =>
      have hp : (poll (nd.st.1 hn) t).2 = some (.att (encodeAtt a), []) := by
        change _ ∈ (((goldilocks S (pubOf E)).pollBatch nd.st.1 t).2.map
          (fun (b, cs) => (Model.Msg.data b, cs))) at hm
        simp only [goldilocks, goldilocksWith, dite_eq_left hn] at hm
        change _ ∈ ((pollBatch (nd.st.1 hn) t).2.map
          (fun (b, cs) => (Model.Msg.data b, cs))) at hm
        obtain ⟨⟨b, cs⟩, hb, heq⟩ := List.mem_map.mp hm
        have hp := Prod.mk.inj heq
        have hb' := Model.Msg.data.inj hp.1
        have hcs' := hp.2
        subst b cs
        simp only [pollBatch, List.mem_append] at hb
        rcases hb with (hb | hb) | hb
        · exact Option.mem_toList.mp hb
        · obtain ⟨p, _, heq⟩ := List.mem_map.mp hb
          cases heq
        · obtain ⟨p, _, heq⟩ := List.mem_map.mp hb
          cases heq
      exact ⟨t, rfl, hsel, hp⟩
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
      let Q := fun o => o = attObj (binding := stock) a →
        attObj a ∈ Model.closure (rho.runDuties v nd ds).1.seen ∨
          attObj a ∈ (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
            rho.hash (rho.ownKey v)
            ⟨((Model.protoOf (compiled (goldilocks S)) E).act (rho.runDuties v nd ds).1.st d).1,
              (rho.runDuties v nd ds).1.seen⟩
            (rho.signedCandidate v d
              ((Model.protoOf (compiled (goldilocks S)) E).act (rho.runDuties v nd ds).1.st d).2)).2
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
