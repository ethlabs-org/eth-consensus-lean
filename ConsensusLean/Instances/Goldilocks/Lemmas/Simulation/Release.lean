module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outbox
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Steps
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Goldilocks Simulation: the cuts of a tick and the proposal duty

What the cuts of a tick queue and release: their attestation bodies (`attBodies`) and the
canonical objects of their blocks (`blockObjs`), with their characterising lemmas; the FG update's
outbox and the cuts of the node's tick (`onTick_cuts`, `fgUpdate_outbox_eq`); and the proposal duty
release by release (`dutyStep_propose_full`): at the start of slot `s`, with the proposal carrying
only seen objects, the engine's `propose` duty releases the canonical objects of the blocks of the
node's proposal step and queues that step's emissions. `ReleaseTick` unrolls the whole tick from
them. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload SAState)

/-! ## The bodies and the block of a tick's cuts -/

section TickCuts

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- The attestation bodies a list of cuts queues: one per signing `fg_attest` cut. -/
def attBodies (cs : List (Cut (goldilocksNode sp ro))) : List Body :=
  cs.flatMap fun
    | .fg (.attest _ (some a)) => [.att (encodeAtt a)]
    | _ => []

/-- The canonical objects of the blocks of a list of cuts' `fg_on_block` cuts. -/
def blockObjs (cs : List (Cut (goldilocksNode sp ro))) : List (Wire sp.n) :=
  cs.flatMap fun
    | .fg (.block B _) => [blockObj sp B]
    | _ => []

/-- The flat-map interface of attestation bodies, without generated match equations. -/
theorem attBodies_eq (cs : List (Cut (goldilocksNode sp ro))) :
    attBodies cs = cs.flatMap (fun
      | .fg (.attest _ (some a)) => [.att (encodeAtt a)]
      | _ => []) := by rfl

theorem attBodies_nil : attBodies (sp := sp) (ro := ro) [] = [] := by rfl

theorem attBodies_cons (c : Cut (goldilocksNode sp ro)) (cs : List (Cut (goldilocksNode sp ro))) :
    attBodies (c :: cs) = (match c with
      | .fg (.attest _ (some a)) => [.att (encodeAtt a)]
      | _ => []) ++ attBodies cs := by rfl

/-- The flat-map interface of block objects, without generated match equations. -/
theorem blockObjs_eq (cs : List (Cut (goldilocksNode sp ro))) :
    blockObjs cs = cs.flatMap (fun
      | .fg (.block B _) => [blockObj sp B]
      | _ => []) := by rfl

theorem blockObjs_nil : blockObjs (sp := sp) (ro := ro) [] = [] := by rfl

theorem blockObjs_cons (c : Cut (goldilocksNode sp ro)) (cs : List (Cut (goldilocksNode sp ro))) :
    blockObjs (c :: cs) = (match c with
      | .fg (.block B _) => [blockObj sp B]
      | _ => []) ++ blockObjs cs := by rfl

theorem mem_blockObjs {cs : List (Cut (goldilocksNode sp ro))} {o : Wire sp.n} :
    o ∈ blockObjs cs ↔ ∃ B acc, Cut.fg (.block B acc) ∈ cs ∧ o = blockObj sp B := by
  simp only [blockObjs_eq, List.mem_flatMap]
  constructor
  · rintro ⟨c, hc, ho⟩
    cases c with
    | ac => simp at ho
    | fg l =>
      cases l with
      | block B acc => exact ⟨B, acc, hc, List.mem_singleton.mp ho⟩
      | attestation => simp at ho
      | attest => simp at ho
  · rintro ⟨B, acc, hc, rfl⟩
    exact ⟨_, hc, List.mem_singleton_self _⟩

theorem emitted_append (cs cs' : List (Cut (goldilocksNode sp ro))) :
    emitted (cs ++ cs') = emitted cs ++ emitted cs' := by simp [emitted]

theorem mem_emitted {cs : List (Cut (goldilocksNode sp ro))} {v : Vote sp.n} :
    Body.vote (encodeVote v) ∈ emitted cs ↔
      ∃ ℓ, Cut.ac ℓ ∈ cs ∧ ∃ em ∈ ℓ.emits, em.msg = v := by
  simp only [emitted, List.mem_flatMap]
  constructor
  · rintro ⟨c, hc, hv⟩
    cases c with
    | fg => simp at hv
    | ac ℓ =>
      obtain ⟨em, hem, heq⟩ := List.mem_map.mp hv
      have h := congrArg (decodeVote sp.n) (Body.vote.inj heq)
      rw [decodeVote_encodeVote, decodeVote_encodeVote] at h
      exact ⟨ℓ, hc, em, hem, Option.some.inj h⟩
  · rintro ⟨ℓ, hc, em, hem, heq⟩
    exact ⟨_, hc, List.mem_map.mpr ⟨em, hem, by rw [heq]⟩⟩

theorem attBodies_append (cs cs' : List (Cut (goldilocksNode sp ro))) :
    attBodies (cs ++ cs') = attBodies cs ++ attBodies cs' := by
  simp only [attBodies_eq, List.flatMap_append]

theorem vote_not_mem_attBodies (cs : List (Cut (goldilocksNode sp ro))) (w : WireVote) :
    Body.vote w ∉ attBodies cs := by
  simp only [attBodies_eq, List.mem_flatMap, not_exists, not_and]
  intro c _
  cases c with
  | ac => simp
  | fg l => cases l <;> simp; split <;> simp

theorem blockObjs_append (cs cs' : List (Cut (goldilocksNode sp ro))) :
    blockObjs (cs ++ cs') = blockObjs cs ++ blockObjs cs' := by
  simp only [blockObjs_eq, List.flatMap_append]

theorem attBodies_ac (ℓ : ACLabel (goldilocksNode sp ro)) : attBodies [Cut.ac ℓ] = [] := by
  simp only [attBodies_cons, attBodies_nil, List.append_nil]

theorem blockObjs_ac (ℓ : ACLabel (goldilocksNode sp ro)) : blockObjs [Cut.ac ℓ] = [] := by
  simp only [blockObjs_cons, blockObjs_nil, List.append_nil]

/-- The cuts of the node's tick: the AC's tick, the proposal step, the FG update. -/
theorem onTick_cuts (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat) :
    (Node.onTick proposer dg self st t x).2 =
      (Node.tickStep proposer dg self st t x .acTick).2 ++
        (Node.tickStep proposer dg self
          (Node.tickStep proposer dg self st t x .acTick).1 t x .proposal).2 ++
          (Node.tickStep proposer dg self (Node.tickStep proposer dg self
            (Node.tickStep proposer dg self st t x .acTick).1
            t x .proposal).1 t x .fgUpdate).2 := by
  simp [Node.onTick, Node.runSteps, Node.tickSteps]

/-- The FG update queues the attestation of the node's FG-update step's signing cut, and that
step emits no vote and processes no block. -/
theorem fgUpdate_outbox_eq (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (x : Nat)
    (st : State sp ro) :
    (fgUpdate st).outbox =
        st.outbox ++ attBodies (Node.tickStep proposer dg st.self st.node st.now x .fgUpdate).2 ∧
      emitted (Node.tickStep proposer dg st.self st.node st.now x .fgUpdate).2 = [] ∧
      blockObjs (Node.tickStep proposer dg st.self st.node st.now x .fgUpdate).2 = [] ∧
      ∀ C a, Cut.fg (.attest C (some a)) ∈ (Node.tickStep proposer dg st.self st.node st.now x
        .fgUpdate).2 → a.val = st.self := by
  unfold fgUpdate Node.tickStep
  simp only
  rcases h : (Node.acToFG st.node st.now).2.2 with _ | C
  · simp only [attBodies_cons, attBodies_nil, acToFG, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, emitted, List.map_nil, blockObjs_cons, blockObjs_nil,
      List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self,
      IsEmpty.forall_iff, implies_true, and_self]
  · unfold Node.attest
    rcases h' : (Node.acToFG st.node st.now).1.fg.attest (Node.acToFG st.node st.now).1.record
      st.self C with _ | ⟨a, Λ'⟩
    · simp only [Node.acToFG] at h'
      simp only [acToFG, h', attBodies_cons, attBodies_nil, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, emitted, List.map_nil, blockObjs_cons, blockObjs_nil,
        List.mem_cons, reduceCtorEq, Cut.fg.injEq,
        FGLabel.attest.injEq, and_false, List.not_mem_nil, or_self, IsEmpty.forall_iff,
        implies_true, and_self]
    · simp only [Node.acToFG] at h'
      simp only [h', Node.onAttestation, attBodies_cons, attBodies_nil, emitted,
        blockObjs_cons, blockObjs_nil, Node.acToFG,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
        reduceCtorEq, Cut.fg.injEq, FGLabel.attest.injEq, Option.some.injEq, false_or,
        List.nil_append, true_and]
      refine ⟨rfl, ?_⟩
      intro C' a' hm
      rcases hm with ⟨-, rfl⟩ | hm
      · exact createAtt_val h'
      · simp at hm

/-- The proposal step signs nothing. -/
theorem tickStep_proposal_attBodies (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (self : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat) :
    attBodies (Node.tickStep proposer dg self st t x .proposal).2 = [] := by
  simp only [Node.tickStep]
  split_ifs
  · split
    · rfl
    · simp only [Node.proposeBlock, Node.onBlock]
      split_ifs
      · rfl
      · split <;> rfl
  · rfl

end TickCuts

/-! ## The proposal duty, release by release -/

section ProposeDuty

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- **The proposal duty is the node's proposal step, release by release.** At the start of slot
`s` with the proposal carrying only seen objects, the engine's `propose` duty releases the canonical
objects of the blocks of the node's proposal step and queues that step's emissions. -/
theorem dutyStep_propose_full (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (s : Slot) (hs : 0 < s)
    (hsel : rho.sel (.proposer s) = {runProposer S rho hn s})
    (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (hslot : (S.params (pubOf E) hn).toParams.slotOf (shapeOf S hn nd).now = s)
    (hst : (shapeOf S hn nd).now = (S.params (pubOf E) hn).toParams.slotTime s)
    (hrel : rho.ownKey v ∈ rho.sel (.proposer s) →
      ∀ par info cs, (propose (shapeOf S hn nd) s).2 = some (par, info, cs) →
      ∀ o ∈ cs, o ∈ Model.closure nd.seen) :
    (rho.dutyStep v nd (.propose s hs)).2 =
        blockObjs (Node.tickStep (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
          (shapeOf S hn nd).node
          (shapeOf S hn nd).now (encodeTxs nd.st.2) .proposal).2 ∧
      (shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1).outbox =
        (shapeOf S hn nd).outbox ++ emitted (Node.tickStep (runProposer S rho hn)
          (digestOf S rho) (rho.ownKey v)
          (shapeOf S hn nd).node (shapeOf S hn nd).now (encodeTxs nd.st.2) .proposal).2 := by
  have hact2 := act_propose_snd S hn nd s hs
  have hact1 := shapeOf_act_propose S hn nd.st s hs
  unfold Model.Run.dutyStep
  generalize (Model.protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs) =
      a at hact1 hact2
  have hP : Proposes (P := (S.params (pubOf E) hn).toParams) (runProposer S rho hn) (rho.ownKey v)
        (shapeOf S hn nd).now ↔
      runProposer S rho hn s = (shapeOf S hn nd).self := by
    rw [hst, proposes_iff S hn (runProposer S rho hn) _ s hs, hself]
  by_cases hp : runProposer S rho hn s = (shapeOf S hn nd).self
  · have hmem : rho.ownKey v ∈ rho.sel (.proposer s) := by
      rw [hsel]
      exact Finset.mem_singleton.2 (hp.trans hself).symm
    have hrel := hrel hmem
    simp only [show (Model.protoOf (compiled (goldilocks S)) E).role (.propose s hs) =
      .proposer s from rfl, hmem, ↓reduceIte]
    simp only [propose] at hact1 hact2 hrel
    simp only [Node.tickStep, hP.2 hp, ite_true]
    rcases hr : (acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now).2.2 with _ | ⟨d, p⟩
    · simp only [hr] at hact1 hact2
      rw [hact2]
      simp only [Option.map_none, Option.toList_none, Model.Run.signedCandidate]
      erw [List.map_nil]
      simp only [ite_self, Model.releaseAll]
      refine ⟨by
        simp only [blockObjs_cons, blockObjs_nil, acProposal, List.append_nil]
        rfl, ?_⟩
      change (a.1.1 hn).outbox = _
      rw [hact1]
      simp only [emitted, acProposal, List.flatMap_cons, List.map_nil, List.flatMap_nil,
        List.append_nil]
    · simp only [hr] at hact1 hact2 hrel
      rw [hact2]
      have hrole : (Model.protoOf (compiled (goldilocks S)) E).role (.propose s hs) =
          .proposer s := rfl
      simp only [Option.map, Option.toList_some, Model.Run.signedCandidate, hrole]
      erw [List.map_cons, List.map_nil]
      have hmem : rho.ownKey v ∈ rho.sel (.proposer s) := by
        rw [hsel]
        exact Finset.mem_singleton.2 (hp.trans hself).symm
      rw [ite_eq_left hmem]
      have hc : (Model.releasable nd.seen (Model.Obj.mk (.signed (rho.ownKey v) (.proposer s))
          (.item ⟨parentRef (S.params (pubOf E) hn).genesisRoot (some d.head.root), s,
            encodeTxs nd.st.2, encodeInfo ((acProposal (shapeOf S hn nd).node
              (shapeOf S hn nd).now).1.fg.proposalAttestations d.head) p⟩)
          (payloadObjs ((acProposal (shapeOf S hn nd).node
              (shapeOf S hn nd).now).1.fg.proposalAttestations d.head) p)) &&
          Model.protects (Model.protoOf (compiled (goldilocks S)) E) (rho.ownKey v) nd.seen
            (Model.Obj.mk (.signed (rho.ownKey v) (.proposer s))
              (.item ⟨parentRef (S.params (pubOf E) hn).genesisRoot (some d.head.root), s,
                encodeTxs nd.st.2, encodeInfo ((acProposal (shapeOf S hn nd).node
                  (shapeOf S hn nd).now).1.fg.proposalAttestations d.head) p⟩)
              (payloadObjs ((acProposal (shapeOf S hn nd).node
                  (shapeOf S hn nd).now).1.fg.proposalAttestations d.head) p))) = true := by
        refine Bool.and_eq_true_iff.2 ⟨?_, ?_⟩
        · unfold Model.releasable
          exact List.all_eq_true.2 fun o ho => decide_eq_true (hrel _ _ _ rfl o ho)
        · exact protects_of_not_att S _ _ _ (fun k w h => by cases h)
      have hB := blockOf_eq_mkBlock S rho hn (rho.ownKey v)
        (acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now).1.fg (shapeOf S hn nd).now
        (encodeTxs nd.st.2) d.head p s hslot
      have hfut : ¬ (S.params (pubOf E) hn).toParams.slotOf (shapeOf S hn nd).now <
          (mkBlock (A := goldilocksNode (S.params (pubOf E) hn) (S.ro _)) (digestOf S rho)
            (rho.ownKey v) (acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now).1.fg
            (shapeOf S hn nd).now (encodeTxs nd.st.2) d.head p).slot := lt_irrefl _
      have hobj : blockObj (S.params (pubOf E) hn)
          (mkBlock (A := goldilocksNode (S.params (pubOf E) hn) (S.ro _)) (digestOf S rho)
            (rho.ownKey v) (acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now).1.fg
            (shapeOf S hn nd).now (encodeTxs nd.st.2) d.head p) =
          Model.Obj.mk (.signed (rho.ownKey v) (.proposer s))
            (.item ⟨parentRef (S.params (pubOf E) hn).genesisRoot (some d.head.root), s,
              encodeTxs nd.st.2, encodeInfo ((acProposal (shapeOf S hn nd).node
                (shapeOf S hn nd).now).1.fg.proposalAttestations d.head) p⟩)
            (payloadObjs ((acProposal (shapeOf S hn nd).node
                (shapeOf S hn nd).now).1.fg.proposalAttestations d.head) p) := by
        simp only [blockObj, mkBlock, headerOf, hslot]
      have hb : blockObjs ((acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now).2.1 ::
          (Node.proposeBlock (digestOf S rho) (rho.ownKey v)
            (acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now).1 (shapeOf S hn nd).now
            (encodeTxs nd.st.2) d.head p).2) =
          [Model.Obj.mk (.signed (rho.ownKey v) (.proposer s))
            (.item ⟨parentRef (S.params (pubOf E) hn).genesisRoot (some d.head.root), s,
              encodeTxs nd.st.2, encodeInfo ((acProposal (shapeOf S hn nd).node
                (shapeOf S hn nd).now).1.fg.proposalAttestations d.head) p⟩)
            (payloadObjs ((acProposal (shapeOf S hn nd).node
                (shapeOf S hn nd).now).1.fg.proposalAttestations d.head) p)] := by
        simp only [Node.proposeBlock, Node.onBlock, hfut, ite_false]
        simp only [Node.acProposal] at hobj ⊢
        split <;> simp only [blockObjs_cons, blockObjs_nil, List.append_nil,
          Node.acCall, List.nil_append] <;> exact congrArg (fun x => [x]) hobj
      unfold Model.releaseAll
      split
      · refine ⟨?_, ?_⟩
        · rw [hb]; rfl
        · change (recordOwn (a.1.1 hn) _ _).outbox = _
          rw [hact1]
          simp only [recordOwn, decodeInfo_encodeInfo]
          erw [rootOf_digests_item]
          simp only [apply]
          erw [hB]
          simp only [Node.proposeBlock, hself, emitted, List.flatMap_cons, Node.acProposal]
          rfl
      · rename_i h
        exact False.elim (h (Bool.and_eq_true_iff.2 ⟨hc, dependencies_item _ _ _ _ _⟩))
  · simp only [Node.tickStep, hP.not.2 hp, ite_false]
    have hmem : rho.ownKey v ∉ rho.sel (.proposer s) := by
      rw [hsel, Finset.mem_singleton]
      intro heq
      exact hp (heq.symm.trans hself.symm)
    simp only [show (Model.protoOf (compiled (goldilocks S)) E).role (.propose s hs) =
      .proposer s from rfl, hmem, ↓reduceIte]
    simp only [blockObjs_nil, emitted, List.flatMap_nil, List.append_nil, and_true]
    rfl

end ProposeDuty

end Consensus.Goldilocks.Simulation

end
