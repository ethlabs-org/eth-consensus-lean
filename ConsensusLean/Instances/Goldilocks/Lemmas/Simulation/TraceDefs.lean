module
public import ConsensusLean.Spec.Shape.Run
public import ConsensusLean.Instances.Goldilocks.AsChainShape
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Results.Spec.CanonicalTrace

public section

/-! # Canonical engine-to-node trace construction: derived facts

The definitions of the canonical trace (`simTrace`, its cuts and cut map, the honest keys, the
node digest and the run's proposer) and the lemmas characterising their bodies are untrusted
statement vocabulary in `Results/Spec/CanonicalTrace`, re-exported here. This module derives
further facts from those lemmas: the cuts of each kind of engine event, the receipt of a canonical
or a dropped object, and the committee size of a bound setup. Further proofs are in
`Lemmas/Simulation/Trace`. -/

namespace Consensus.Goldilocks

open Blocks

namespace Node

variable {P : Params} {A : NodeAC P}

end Node

namespace Simulation
open AsChainShape

open Shape Node
open Consensus.Model (pubOf)
open AC (ACParams ReplayOrder Vote Payload)

/-- A bound setup's committee is nonempty at every population with a validator: the population
binding's committee is the population, a committee binding's by `VoteBinding.committeeSize_pos`. -/
theorem _root_.Consensus.Goldilocks.AsChainShape.Setup.committeeSize_pos (S : Setup)
    (pub : Model.Public) (hn : 1 ≤ pub.n) : 0 < (S.params pub hn).committeeSize := by
  change 0 < S.vote.committeeSize pub
  unfold VoteBinding.committeeSize
  split
  · exact hn
  · rename_i k _
    have h := S.vote.committeeSize_pos pub k hn
    split
    · rename_i m hm
      rw [hm] at h
      exact lt_min h hn
    · rename_i keys hk
      rw [hk] at h
      exact Finset.card_pos.mpr h

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {binding : VoteBinding}

/-- A canonical object contributes its group, then the rest from the handler's state. -/
theorem deliverRecs_cons_some (io : VoteAuth sp.n binding) (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat) (o : Wire sp.n binding)
    (os : List (Wire sp.n binding)) (st : NodeState (goldilocksNode sp ro)) (sub : Nat)
    (e : Event (goldilocksNode sp ro)) (he : canonEvent sp ro io hs o = some e) :
    deliverRecs io proposer dg hs self t i (o :: os) st sub =
      groupRecs proposer dg self st t (Nat.pair i sub) e ++
        deliverRecs io proposer dg hs self t i os (exec proposer dg self st t e).1 (sub + 1) := by
  rw [deliverRecs_cons, he]

/-- A dropped object contributes no group. -/
theorem deliverRecs_cons_none (io : VoteAuth sp.n binding) (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat) (o : Wire sp.n binding)
    (os : List (Wire sp.n binding)) (st : NodeState (goldilocksNode sp ro)) (sub : Nat)
    (he : canonEvent sp ro io hs o = none) :
    deliverRecs io proposer dg hs self t i (o :: os) st sub =
      deliverRecs io proposer dg hs self t i os st (sub + 1) := by
  rw [deliverRecs_cons, he]

/-- A cut of the own-admission groups is a cut of the `.attestation` group of one of the admitted
attestations, under an event id `Nat.pair i s` with `sub ≤ s`. -/
theorem mem_admitRecs {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (t : Time) (i : Nat) :
    ∀ (as : List (FG.Att sp.n)) (st : NodeState (goldilocksNode sp ro)) (sub : Nat)
      (r : CutRec sp ro), r ∈ admitRecs proposer dg self t i as st sub →
      ∃ a ∈ as, ∃ (st' : NodeState (goldilocksNode sp ro)) (s : Nat), sub ≤ s ∧
        r ∈ groupRecs proposer dg self st' t (Nat.pair i s) (.attestation a)
  | [], _, _, _, h => by rw [admitRecs_nil] at h; exact absurd h List.not_mem_nil
  | a :: as, st, sub, r, h => by
    rw [admitRecs_cons] at h
    rcases List.mem_append.mp h with h | h
    · exact ⟨a, List.mem_cons_self, st, sub, le_rfl, h⟩
    · obtain ⟨b, hb, st', s, hs, hr⟩ := mem_admitRecs proposer dg self t i as _ (sub + 1) r h
      exact ⟨b, List.mem_cons_of_mem _ hb, st', s, by omega, hr⟩

/-- The cuts after the tick group of engine tick `i` of `v` at `t`: the node's own admissions
during the tick, one `.attestation` group each from its node after the tick (`postTick`), under
the event ids `Nat.pair i 1`, `Nat.pair i 2`, …. -/
noncomputable def tickTail (v : V) (i : Nat) (t : Time) :
    List (CutRec (S.params (pubOf E) hn) (S.ro _)) :=
  admitRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) t i (admitsAt S rho hn v i)
    (postTick S rho hn v i t) 1

/-- `tickTail` unfolded. -/
theorem tickTail_eq (v : V) (i : Nat) (t : Time) : tickTail S rho hn v i t =
    admitRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) t i (admitsAt S rho hn v i)
      (postTick S rho hn v i t) 1 := by rfl

/-- A cut of a tick tail is a cut of the `.attestation` group of an attestation the engine admits
to the node's pool during the tick, under the event id `Nat.pair i s`, `1 ≤ s`. -/
theorem mem_tickTail (v : V) (i : Nat) (t : Time) {r : CutRec (S.params (pubOf E) hn) (S.ro _)}
    (h : r ∈ tickTail S rho hn v i t) :
    ∃ a ∈ admitsAt S rho hn v i,
      ∃ (st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _))) (s : Nat), 1 ≤ s ∧
        r ∈ groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) st t (Nat.pair i s)
          (.attestation a) := by
  rw [tickTail_eq] at h
  exact mem_admitRecs _ _ _ _ _ _ _ _ _ h

/-- The cuts of an engine tick at a public time: the node's tick group, then the tick tail. -/
theorem eventCuts_tick_public (i : Nat) (v : V) (t : Time)
    (he : rho.events[i]? = some (.tick v t)) (hp : (S.params (pubOf E) hn).toParams.IsPublic t) :
    eventCuts S rho hn i =
      groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t)) (S.sign (pubOf E) (rho.ownKey v) t)) ++
        tickTail S rho hn v i t := by
  simp only [eventCuts_eq, he, hp, reduceIte, tickTail_eq]

/-- An engine tick at a non-public time has only its tick tail. -/
theorem eventCuts_tick_other (i : Nat) (v : V) (t : Time)
    (he : rho.events[i]? = some (.tick v t))
    (hp : ¬ (S.params (pubOf E) hn).toParams.IsPublic t) :
    eventCuts S rho hn i = tickTail S rho hn v i t := by
  simp only [eventCuts_eq, he, hp, reduceIte, tickTail_eq, List.nil_append]

/-- The cuts of an engine delivery. -/
theorem eventCuts_deliver (i : Nat) (v : V)
    (o : (Model.protoOf (compiled (goldilocks S)) E).Object)
    (t : Time) (he : rho.events[i]? = some (.deliver v o t)) :
    eventCuts S rho hn i =
      deliverRecs (sp := S.params (pubOf E) hn) (binding := S.vote)
        (rho.voteIO v) (runProposer S rho hn) (digestOf S rho)
        (Model.digests rho.hash o) (rho.ownKey v) t i
        (delivered (sp := S.params (pubOf E) hn) (binding := S.vote)
          (rho.voteIO v) (Model.digests rho.hash o) (stateAt S rho hn v i) o)
        (stateAt S rho hn v i).node 0 := by
  simp only [eventCuts_eq, he]

/-- The cuts of an engine restart. -/
theorem eventCuts_restart (i : Nat) (v : V) (t : Time)
    (he : rho.events[i]? = some (.restart v t)) :
    eventCuts S rho hn i =
      groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0) .restart := by
  simp only [eventCuts_eq, he]

end Simulation

end Consensus.Goldilocks
