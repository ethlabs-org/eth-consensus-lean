module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Outbox
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Steps

public section

/-! # Goldilocks Refinement: what the engine releases at a tick

The engine's tick of an honest node against the node's `on_tick`, release by release
(`tick_public_analysis`): at a public time it releases the queued body, the canonical objects of
the blocks of the tick's cuts, and the votes and the attestation the tick's cuts emit and sign
(`Q`, at most two bodies, drained by the two trailing polls), then unsigned gossip. From it:

* `att_released_inv`: an honest node releases an attestation object only at a public tick, and
  only one that a cut of that tick signs;
* `tick_releases`: the own block, the tick's votes and its attestation are released at the tick.
  The attestation passes the own-object guard: every own attestation the node has seen, or
  released earlier in the tick, is one it signed in the simulating trace (`signAt_of_tick_cut`),
  and its signings there are pairwise not slashable (the hypothesis `hnf`, `non_framing` over the
  trace in `Run`);
* `atProposal_outbox_nil`: at the proposal duty of a slot start nothing is queued. -/

namespace Consensus.Goldilocks.Refinement

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

theorem mem_blockObjs {cs : List (Cut (goldilocksNode sp ro))} {o : Wire sp.n} :
    o ∈ blockObjs cs ↔ ∃ B acc, Cut.fg (.block B acc) ∈ cs ∧ o = blockObj sp B := by
  simp only [blockObjs, List.mem_flatMap]
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
    attBodies (cs ++ cs') = attBodies cs ++ attBodies cs' := by simp [attBodies]

theorem vote_not_mem_attBodies (cs : List (Cut (goldilocksNode sp ro))) (w : WireVote) :
    Body.vote w ∉ attBodies cs := by
  simp only [attBodies, List.mem_flatMap, not_exists, not_and]
  intro c _
  cases c with
  | ac => simp
  | fg l => cases l <;> simp; split <;> simp

theorem blockObjs_append (cs cs' : List (Cut (goldilocksNode sp ro))) :
    blockObjs (cs ++ cs') = blockObjs cs ++ blockObjs cs' := by simp [blockObjs]

theorem attBodies_ac (ℓ : ACLabel (goldilocksNode sp ro)) : attBodies [Cut.ac ℓ] = [] := by
  simp [attBodies]

theorem blockObjs_ac (ℓ : ACLabel (goldilocksNode sp ro)) : blockObjs [Cut.ac ℓ] = [] := by
  simp [blockObjs]

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

private theorem createAtt_val {n : Nat} {Λ Λ' : FG.Record} {v : Fin n} {σe : FG.ChainState n}
    {a : FG.Att n} (h : Λ.createAtt v σe = some (a, Λ')) : a.val = v := by
  unfold FG.Record.createAtt at h
  split at h
  · cases h
  · split_ifs at h
    cases h
    rfl

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
  rcases h : (Node.acToFG st.node st.now).2.2.1 with _ | C
  · simp [attBodies, emitted, blockObjs, Node.acToFG]
  · unfold Node.attest
    rcases h' : (Node.acToFG st.node st.now).1.fg.attest (Node.acToFG st.node st.now).1.record
      st.self C with _ | ⟨a, Λ'⟩
    · simp only [Node.acToFG] at h'
      simp [h', attBodies, emitted, blockObjs, Node.acToFG]
    · simp only [Node.acToFG] at h'
      simp only [h', Node.onAttestation, attBodies, emitted, blockObjs, Node.acToFG,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
        reduceCtorEq, Cut.fg.injEq, FGLabel.attest.injEq, Option.some.injEq, false_or,
        List.nil_append, true_and]
      refine ⟨rfl, ?_⟩
      intro C' a' hm
      rcases hm with ⟨-, rfl⟩ | hm
      · exact createAtt_val h'
      · simp at hm

/-- The AC-tick step signs nothing and processes no block. -/
theorem tickStep_acTick_cuts (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat) :
    (Node.tickStep proposer dg self st t x .acTick).2 = [(Node.acCall self st t .tick).2] ∧
      attBodies (Node.tickStep proposer dg self st t x .acTick).2 = [] ∧
      blockObjs (Node.tickStep proposer dg self st t x .acTick).2 = [] := by
  refine ⟨rfl, ?_, ?_⟩ <;> simp [Node.tickStep, Node.acCall, attBodies, blockObjs]

/-- The proposal step signs nothing. -/
theorem tickStep_proposal_attBodies (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (self : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat) :
    attBodies (Node.tickStep proposer dg self st t x .proposal).2 = [] := by
  simp only [Node.tickStep]
  split_ifs
  · split
    · simp [attBodies, Node.acProposal]
    · simp only [Node.proposeBlock, Node.onBlock]
      split_ifs
      · simp [attBodies, Node.acProposal]
      · split <;> simp [attBodies, Node.acCall, Node.acProposal]
  · simp [attBodies]

end TickCuts

/-! ## The proposal duty, release by release -/

section ProposeDuty

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- **The proposal duty is the node's proposal step, release by release.** At the start of slot
`s` with the proposal carrying only seen objects, the engine's `propose` duty releases the canonical
objects of the blocks of the node's proposal step and queues that step's emissions. -/
theorem dutyStep_propose_full (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
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
  generalize (Model.protoOf (compiled (family S)) E).act nd.st (.propose s hs) = a at hact1 hact2
  have hP : Proposes (P := (S.params (pubOf E) hn).toParams) (runProposer S rho hn) (rho.ownKey v)
        (shapeOf S hn nd).now ↔
      runProposer S rho hn s = (shapeOf S hn nd).self := by
    rw [hst, proposes_iff S hn (runProposer S rho hn) _ s hs, hself]
  by_cases hp : runProposer S rho hn s = (shapeOf S hn nd).self
  · have hmem : rho.ownKey v ∈ rho.sel (.proposer s) := by
      rw [hsel]
      exact Finset.mem_singleton.2 (hp.trans hself).symm
    have hrel := hrel hmem
    simp only [show (Model.protoOf (compiled (family S)) E).role (.propose s hs) =
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
        simp [blockObjs, Node.acProposal]; rfl, ?_⟩
      change (a.1.1 hn).outbox = _
      rw [hact1]
      simp [emitted, Node.acProposal]
    · simp only [hr] at hact1 hact2 hrel
      rw [hact2]
      have hrole : (Model.protoOf (compiled (family S)) E).role (.propose s hs) = .proposer s := rfl
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
          Model.protects (Model.protoOf (compiled (family S)) E) (rho.ownKey v) nd.seen
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
        split <;> simp only [blockObjs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
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
    simp only [show (Model.protoOf (compiled (family S)) E).role (.propose s hs) =
      .proposer s from rfl, hmem, ↓reduceIte]
    simp [blockObjs, emitted]
    rfl

end ProposeDuty


/-! ## A tick, duty by duty -/

section Unroll

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- What a poll step releases for the head `ob` of the outbox it pops from, against `seen`: the
poll object of the head, when the own-object guard passes. -/
noncomputable def relHead (v : V) (seen : List (Model.protoOf (compiled (family S)) E).Object)
    (ob : Option Body) : List (Model.protoOf (compiled (family S)) E).Object :=
  ob.elim [] fun b =>
    if Model.protects (Model.protoOf (compiled (family S)) E) (rho.ownKey v) seen
      (pollObj S rho v b) = true then [pollObj S rho v b] else []

omit [DecidableEq V] in
/-- A poll step of a node selected in the poll role releases `relHead` of the head of
`pollPre`'s outbox. -/
theorem dutyStep_poll_eq (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (k : Nat) (hsel : rho.ownKey v ∈ rho.sel .poll)
    (hempty : (shapeOf S hn nd).forwards = []) :
    (rho.dutyStep v nd (.poll k)).2 =
      relHead S rho v nd.seen (pollPre (shapeOf S hn nd)).outbox.head? := by
  unfold Model.Run.dutyStep
  simp only [show (Model.protoOf (compiled (family S)) E).role (.poll k) = .poll from rfl,
    hsel, ↓reduceIte]
  rw [act_poll_snd S hn, (poll_outbox _ _).2]
  erw [hempty, List.map_nil, List.append_nil]
  cases hh : (pollPre (shapeOf S hn nd)).outbox.head? with
  | none =>
    simp only [Option.map_none, Option.toList_none, Model.Run.signedCandidate]
    erw [List.map_nil]
    simp [Model.releaseAll, relHead]
  | some b =>
    have hrole : (Model.protoOf (compiled (family S)) E).role (.poll k) = .poll := rfl
    simp only [Option.map_some, Option.toList_some, Model.Run.signedCandidate, hrole]
    rw [ite_eq_left hsel]
    erw [List.map_cons, List.map_nil]
    unfold relHead
    simp only [Option.elim_some]
    by_cases hp : Model.protects (Model.protoOf (compiled (family S)) E) (rho.ownKey v) nd.seen
        (pollObj S rho v b) = true
    · rw [ite_eq_left hp]
      have hc : (Model.releasable nd.seen (pollObj S rho v b) &&
          Model.protects (Model.protoOf (compiled (family S)) E) (rho.ownKey v) nd.seen
            (pollObj S rho v b)) = true :=
        Bool.and_eq_true_iff.2 ⟨by simp [Model.releasable, Model.Obj.carried], hp⟩
      unfold Model.releaseAll
      split
      · rfl
      · rename_i h
        apply False.elim
        apply h
        refine Bool.and_eq_true_iff.2 ⟨hc, ?_⟩
        change (dependencies _).ready _ (.mk (.signed _ .poll) (.data b) []) = true
        cases b <;> rfl
    · rw [ite_eq_right hp]
      have hc : ¬ (Model.releasable nd.seen (pollObj S rho v b) &&
          Model.protects (Model.protoOf (compiled (family S)) E) (rho.ownKey v) nd.seen
            (pollObj S rho v b)) = true := fun h => hp (Bool.and_eq_true_iff.1 h).2
      unfold Model.releaseAll
      split
      · rename_i h; exact False.elim (hc (Bool.and_eq_true_iff.mp h).1)
      · rfl

omit [DecidableEq V] in
/-- Exact poll release decomposition at the actual candidate prefix. The suffix is run on
the state and holdings left by the ordinary head, not the pre-poll holdings. -/
theorem dutyStep_poll_batch (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (k : Nat) (hsel : rho.ownKey v ∈ rho.sel .poll) :
    let P := Model.protoOf (compiled (family S)) E
    let start : Model.Node P := ⟨(P.act nd.st (.poll k)).1, nd.seen⟩
    let ordinary := ((poll (shapeOf S hn nd) k).2.toList).map
      (fun bc => Model.Obj.mk (.signed (rho.ownKey v) .poll) (.data bc.1) bc.2)
    let headRelease := Model.releaseAll P rho.hash (rho.ownKey v) start ordinary
    let forwards := (shapeOf S hn nd).forwards.map
      (fun p => Model.Obj.mk (.signed (rho.ownKey v) .poll) (.data (.forward p.1)) p.2)
    (rho.dutyStep v nd (.poll k)).2 = headRelease.2 ++
      (Model.releaseAll P rho.hash (rho.ownKey v) headRelease.1 forwards).2 := by
  dsimp only
  unfold Model.Run.dutyStep
  simp only [show (Model.protoOf (compiled (family S)) E).role (.poll k) = .poll from rfl,
    hsel, ↓reduceIte]
  rw [act_poll_snd S hn]
  unfold Model.Run.signedCandidate
  simp only [show (Model.protoOf (compiled (family S)) E).role (.poll k) = .poll from rfl,
    hsel, ↓reduceIte]
  erw [List.map_append, List.map_map, Option.toList_map, List.map_map]
  exact congrArg Prod.snd (Model.releaseAll_append _ _ _ _ _)

omit [DecidableEq V] in
/-- Releasing the ordinary head alone gives `relHead`, from any runtime state. -/
theorem release_head (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (ob : Option Body) :
    (Model.releaseAll (Model.protoOf (compiled (family S)) E) rho.hash (rho.ownKey v) nd
      (ob.toList.map (pollObj S rho v))).2 = relHead S rho v nd.seen ob := by
  cases ob with
  | none => rfl
  | some b =>
    have hr : Model.releasable nd.seen (pollObj S rho v b) = true := by
      simp [Model.releasable, Model.Obj.carried]
    have hd : (Model.protoOf (compiled (family S)) E).dependencies.ready
        (Model.closure nd.seen) (pollObj S rho v b) = true := by
      change (dependencies _).ready _ (.mk (.signed _ .poll) (.data b) []) = true
      cases b <;> rfl
    simp only [Option.toList_some, List.map_cons, List.map_nil, Model.releaseAll, hr, hd,
      Bool.true_and, Bool.and_true, relHead, Option.elim_some]
    split <;> rfl

omit [DecidableEq V] in
/-- An awake tick at `t ≥ 0`, duty by duty, when no slot proposal is due. -/
theorem tick_unroll_nil (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (t : Time) (ht : 0 ≤ t) (hw : E.awake v t = true)
    (hnil : (skeleton (pubOf E)).proposeAt t = []) :
    ∃ N1 N3 N5 N6 : Model.Node (Model.protoOf (compiled (family S)) E),
      N1 = (rho.dutyStep v ⟨(Model.protoOf (compiled (family S)) E).clock nd.st t
          (Model.mempool rho.inbox v t), nd.seen⟩ (.poll t.toNat)).1 ∧
      N3 = (rho.dutyStep v (rho.dutyStep v N1 (.poll t.toNat)).1 (.pollPropose t.toNat)).1 ∧
      N5 = (rho.dutyStep v N3 (.poll t.toNat)).1 ∧
      N6 = (rho.dutyStep v N5 (.poll t.toNat)).1 ∧
      (rho.tick nd v t).2 =
        (rho.dutyStep v ⟨(Model.protoOf (compiled (family S)) E).clock nd.st t
          (Model.mempool rho.inbox v t), nd.seen⟩ (.poll t.toNat)).2 ++
        (rho.dutyStep v N1 (.poll t.toNat)).2 ++
        (rho.dutyStep v (rho.dutyStep v N1 (.poll t.toNat)).1 (.pollPropose t.toNat)).2 ++
        (rho.dutyStep v N3 (.poll t.toNat)).2 ++ (rho.dutyStep v N5 (.poll t.toNat)).2 ++
        (Model.releaseAll (Model.protoOf (compiled (family S)) E) rho.hash (rho.ownKey v) N6
          (Model.gossipCandidates (Model.protoOf (compiled (family S)) E) N6.st t)).2 := by
  refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, ?_⟩
  rw [rho.tick_of_awake nd v t hw]
  dsimp only
  rw [duties_eq S t ht]
  unfold dutiesInit
  rw [hnil]
  rfl

omit [DecidableEq V] in
/-- An awake tick at the start of slot `s > 0`, duty by duty. -/
theorem tick_unroll_propose (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (t : Time) (ht : 0 ≤ t) (hw : E.awake v t = true) (s : Slot) (hs : 0 < s)
    (hone : (skeleton (pubOf E)).proposeAt t = [.propose s hs]) :
    ∃ N1 N3 N4 N5 N6 : Model.Node (Model.protoOf (compiled (family S)) E),
      N1 = (rho.dutyStep v ⟨(Model.protoOf (compiled (family S)) E).clock nd.st t
          (Model.mempool rho.inbox v t), nd.seen⟩ (.poll t.toNat)).1 ∧
      N3 = (rho.dutyStep v (rho.dutyStep v N1 (.poll t.toNat)).1 (.pollPropose t.toNat)).1 ∧
      N4 = (rho.dutyStep v N3 (.propose s hs)).1 ∧
      N5 = (rho.dutyStep v N4 (.poll t.toNat)).1 ∧
      N6 = (rho.dutyStep v N5 (.poll t.toNat)).1 ∧
      (rho.tick nd v t).2 =
        (rho.dutyStep v ⟨(Model.protoOf (compiled (family S)) E).clock nd.st t
          (Model.mempool rho.inbox v t), nd.seen⟩ (.poll t.toNat)).2 ++
        (rho.dutyStep v N1 (.poll t.toNat)).2 ++
        (rho.dutyStep v (rho.dutyStep v N1 (.poll t.toNat)).1 (.pollPropose t.toNat)).2 ++
        (rho.dutyStep v N3 (.propose s hs)).2 ++
        (rho.dutyStep v N4 (.poll t.toNat)).2 ++ (rho.dutyStep v N5 (.poll t.toNat)).2 ++
        (Model.releaseAll (Model.protoOf (compiled (family S)) E) rho.hash (rho.ownKey v) N6
          (Model.gossipCandidates (Model.protoOf (compiled (family S)) E) N6.st t)).2 := by
  refine ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, ?_⟩
  rw [rho.tick_of_awake nd v t hw]
  dsimp only
  rw [duties_eq S t ht]
  unfold dutiesInit
  rw [hone]
  rfl

end Unroll

/-! ## The releases of a public tick -/

section TickPublic

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- The tick's first three duties from a node with no FG update due and at most one body queued:
the first poll releases the queued body, the second and the node's tick release nothing; after
them nothing is queued, the node state and the own index are the node's, the clock is the tick's. -/
theorem leading_polls (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (t : Time) (hsel : rho.ownKey v ∈ rho.sel .poll) (hf : (shapeOf S hn nd).fgDue = false)
    (hb : (shapeOf S hn nd).outbox.length ≤ 1)
    (hempty : (shapeOf S hn nd).forwards = []) :
    let N0 : Model.Node (Model.protoOf (compiled (family S)) E) :=
      ⟨(Model.protoOf (compiled (family S)) E).clock nd.st t (Model.mempool rho.inbox v t),
        nd.seen⟩
    let N1 := (rho.dutyStep v N0 (.poll t.toNat)).1
    let N2 := (rho.dutyStep v N1 (.poll t.toNat)).1
    (rho.dutyStep v N0 (.poll t.toNat)).2 =
        relHead S rho v nd.seen (shapeOf S hn nd).outbox.head? ∧
      (rho.dutyStep v N1 (.poll t.toNat)).2 = [] ∧
      (rho.dutyStep v N2 (.pollPropose t.toNat)).2 = [] ∧
      (rho.dutyStep v N2 (.pollPropose t.toNat)).1.seen =
        nd.seen ++ relHead S rho v nd.seen (shapeOf S hn nd).outbox.head? ∧
      shapeOf S hn (rho.dutyStep v N2 (.pollPropose t.toNat)).1 = nodeTick (shapeOf S hn N2) ∧
      (shapeOf S hn N2).outbox = [] ∧ (shapeOf S hn N2).node = (shapeOf S hn nd).node ∧
      (shapeOf S hn N2).self = (shapeOf S hn nd).self ∧ (shapeOf S hn N2).now = t ∧
      (shapeOf S hn N2).fgDue = false := by
  intro N0 N1 N2
  have hS0 : shapeOf S hn N0 = { shapeOf S hn nd with now := t } := rfl
  have hpre0 : pollPre (shapeOf S hn N0) = shapeOf S hn N0 := by
    rw [pollPre_eq]; rw [hS0]; simp [hf]
  have hS1 : shapeOf S hn N1 = (poll (shapeOf S hn N0) t.toNat).1 :=
    dutyStep_poll S rho hn v N0 _ hsel
  have hpre1 : pollPre (shapeOf S hn N1) = shapeOf S hn N1 := by
    rw [pollPre_eq]; rw [hS1, poll_fgDue]; rfl
  have hout1 : (shapeOf S hn N1).outbox = [] := by
    rw [hS1, (poll_outbox _ _).1, hpre0, hS0]
    change (shapeOf S hn nd).outbox.tail = []
    match hq : (shapeOf S hn nd).outbox with
    | [] => rfl
    | [_] => rfl
    | _ :: _ :: _ => rw [hq] at hb; simp at hb
  have hS2 : shapeOf S hn N2 = (poll (shapeOf S hn N1) t.toNat).1 :=
    dutyStep_poll S rho hn v N1 _ hsel
  have hR1 := dutyStep_poll_eq S rho hn v N0 t.toNat hsel hempty
  rw [hpre0, hS0] at hR1
  have hR2 := dutyStep_poll_eq S rho hn v N1 t.toNat hsel (by rw [hS1]; exact poll_forwards _ _)
  rw [hpre1, hout1] at hR2
  have hR3 := dutyStep_pollPropose_snd S rho hn v N2 t.toNat
  refine ⟨hR1, hR2, hR3, ?_, dutyStep_pollPropose S rho hn v N2 _ hsel, ?_, ?_, ?_, ?_, ?_⟩
  · have e3 := dutyStep_seen S rho v N2 (.pollPropose t.toNat)
    have e2 := dutyStep_seen S rho v N1 (.poll t.toNat)
    have e1 := dutyStep_seen S rho v N0 (.poll t.toNat)
    rw [hR3] at e3
    rw [hR2] at e2
    rw [hR1] at e1
    rw [e3, e2, e1]
    simp only [List.append_nil, relHead, List.head?_nil, Option.elim_none]
    rfl
  · rw [hS2, (poll_outbox _ _).1, hpre1, hout1]; rfl
  · rw [hS2, poll_node_of_fgDue _ _ (by rw [hS1]; exact poll_fgDue _ _), hS1,
      poll_node_of_fgDue _ _ (by rw [hS0]; exact hf), hS0]
  · rw [hS2, poll_self, hS1, poll_self, hS0]
  · rw [hS2, poll_now, hS1, poll_now, hS0]
  · rw [hS2]; exact poll_fgDue _ _

omit [DecidableEq V] in
/-- The node's tick at a public time from a state with nothing queued: the AC's tick, its
emissions queued, the FG update due. -/
theorem nodeTick_public (st : State (S.params (pubOf E) hn) (S.ro _))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic st.now) (h0 : st.outbox = []) :
    (nodeTick st).node = (Node.acCall st.self st.node st.now .tick).1 ∧
      (nodeTick st).outbox = emitted [(Node.acCall st.self st.node st.now .tick).2] ∧
      (nodeTick st).fgDue = true ∧ (nodeTick st).self = st.self ∧ (nodeTick st).now = st.now := by
  unfold nodeTick
  rw [ite_eq_left hp]
  simp [apply, h0]

omit [DecidableEq V] in
/-- The tick's two trailing polls from a node whose FG update is due: they release the head and
the second body of the outbox after the FG update. -/
theorem trailing_polls (v : V) (N4 : Model.Node (Model.protoOf (compiled (family S)) E))
    (k : Nat) (hsel : rho.ownKey v ∈ rho.sel .poll) (hf : (shapeOf S hn N4).fgDue = true) :
    let N5 := (rho.dutyStep v N4 (.poll k)).1
    ∃ F : List (Model.protoOf (compiled (family S)) E).Object,
    (rho.dutyStep v N4 (.poll k)).2 =
        relHead S rho v N4.seen (fgUpdate (shapeOf S hn N4)).outbox.head? ++ F ∧
      N5.seen = N4.seen ++
        (relHead S rho v N4.seen (fgUpdate (shapeOf S hn N4)).outbox.head? ++ F) ∧
      (rho.dutyStep v N5 (.poll k)).2 =
        relHead S rho v N5.seen (fgUpdate (shapeOf S hn N4)).outbox.tail.head? ∧
      (shapeOf S hn (rho.dutyStep v N5 (.poll k)).1).outbox =
        (fgUpdate (shapeOf S hn N4)).outbox.tail.tail ∧
      (∀ o ∈ F, ∃ τ cs, o = .mk (.signed (rho.ownKey v) .poll) (.data (.forward τ)) cs) := by
  intro N5
  have hpre4 : pollPre (shapeOf S hn N4) = fgUpdate (shapeOf S hn N4) := by
    rw [pollPre_eq]; rw [ite_eq_left hf]
  have hS5 : shapeOf S hn N5 = (poll (shapeOf S hn N4) k).1 := dutyStep_poll S rho hn v N4 _ hsel
  have hpre5 : pollPre (shapeOf S hn N5) = shapeOf S hn N5 := by
    rw [pollPre_eq]; rw [hS5, poll_fgDue]; rfl
  have hout5 : (shapeOf S hn N5).outbox = (fgUpdate (shapeOf S hn N4)).outbox.tail := by
    rw [hS5, (poll_outbox _ _).1, hpre4]
  have hR5 := dutyStep_poll_batch S rho hn v N4 k hsel
  dsimp only at hR5
  rw [(poll_outbox _ _).2, Option.toList_map, List.map_map] at hR5
  change (rho.dutyStep v N4 (.poll k)).2 =
    (Model.releaseAll _ _ _ _ ((pollPre (shapeOf S hn N4)).outbox.head?.toList.map
      (pollObj S rho v))).2 ++ _ at hR5
  rw [release_head, hpre4] at hR5
  generalize hF : (Model.releaseAll _ _ _ _ _).2 = F at hR5
  have hR6 := dutyStep_poll_eq S rho hn v N5 k hsel (by rw [hS5]; exact poll_forwards _ _)
  rw [hpre5, hout5] at hR6
  have e5 := dutyStep_seen S rho v N4 (.poll k)
  rw [hR5] at e5
  refine ⟨F, hR5, e5, hR6, ?_, ?_⟩
  · have e6 := dutyStep_poll S rho hn v N5 k hsel
    rw [e6, (poll_outbox _ _).1, hpre5, hout5]
  · intro o ho
    rw [← hF] at ho
    obtain ⟨⟨τ, cs⟩, _, rfl⟩ := List.mem_map.mp (Model.releaseAll_subset _ _ _ _ o ho)
    exact ⟨τ, cs, rfl⟩

/-- The proposal step of a key that does not propose at `t` makes no cut. -/
theorem tickStep_proposal_not' {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat)
    (h : ¬ Proposes (P := sp.toParams) proposer self t) :
    Node.tickStep proposer dg self st t x .proposal = (st, []) := by
  simp [Node.tickStep, h]

/-- The node of `v` after the first three duties of its tick at `t` from `nd`. -/
noncomputable def preNode (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (t : Time) : Model.Node (Model.protoOf (compiled (family S)) E) :=
  (rho.dutyStep v (rho.dutyStep v (rho.dutyStep v
    ⟨(Model.protoOf (compiled (family S)) E).clock nd.st t (Model.mempool rho.inbox v t),
      nd.seen⟩ (.poll t.toNat)).1 (.poll t.toNat)).1 (.pollPropose t.toNat)).1

/-- **The releases of a public tick.** At an honest node's tick at a public time (when its slot
proposal carries only seen objects), the engine releases, in order: the queued body (at most one)
against the node's `seen`, the canonical objects of the blocks of the node's tick cuts, the first
and the second body of `Q` against the `seen` before each, and unsigned gossip; `Q` is the votes
the tick's cuts emit followed by the attestation they sign, at most two bodies. -/
theorem tick_public_analysis (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (hv' : v ∈ rho.honest) (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t)
    (hrel : ∀ s (hs : 0 < s), (skeleton (pubOf E)).proposeAt t = [.propose s hs] →
      rho.ownKey v ∈ rho.sel (.proposer s) → ∀ par info cs,
      (propose (shapeOf S hn (preNode S rho v (rho.stateBefore i v) t)) s).2 =
        some (par, info, cs) →
      ∀ o ∈ cs, o ∈ Model.closure (preNode S rho v (rho.stateBefore i v) t).seen) :
    ∃ (N4 N5 : Model.Node (Model.protoOf (compiled (family S)) E)) (Q : List Body)
      (R4 F G : List (Model.protoOf (compiled (family S)) E).Object),
      rho.releasesAt i =
        relHead S rho v (rho.stateBefore i v).seen (stateAt S rho hn v i).outbox.head? ++ R4 ++
          (relHead S rho v N4.seen Q.head? ++ F) ++ relHead S rho v N5.seen Q.tail.head? ++ G ∧
      N4.seen = (rho.stateBefore i v).seen ++
        relHead S rho v (rho.stateBefore i v).seen (stateAt S rho hn v i).outbox.head? ++ R4 ∧
      N5.seen = N4.seen ++ (relHead S rho v N4.seen Q.head? ++ F) ∧
      (∀ o ∈ F, ∃ τ cs, o = .mk (.signed (rho.ownKey v) .poll) (.data (.forward τ)) cs) ∧
      (∀ o ∈ G, o.auth = .none) ∧ Q.length ≤ 2 ∧
      Q = emitted (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
          (stateAt S rho hn v i).node t
          (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2 ++
        attBodies (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
          (stateAt S rho hn v i).node t
          (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2 ∧
      R4 = blockObjs (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
          (stateAt S rho hn v i).node t
          (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2 ∧
      (∀ c ∈ R4, ∀ x ∈ c.carried, x ∈ Model.closure ((rho.stateBefore i v).seen ++
        relHead S rho v (rho.stateBefore i v).seen (stateAt S rho hn v i).outbox.head?)) ∧
      N5 = (rho.dutyStep v N4 (.poll t.toNat)).1 := by
  have hm := List.mem_of_getElem? he
  have ht : 0 ≤ t := (hv.in_horizon _ hm).1
  have hw := hv.tick_awake v t hm
  have hsel : rho.ownKey v ∈ rho.sel .poll := by
    rw [selValid_poll S rho hv.selValid]; exact Finset.mem_univ _
  obtain ⟨hamo, -⟩ := outbox_inv S rho hn hv v hv' i
  obtain ⟨-, hlen⟩ := (atMostOneVote_iff _).1 hamo
  have hf := fgDue_eq_false S rho hn v i
  have hself0 := self_eq_ownKey S rho hn v i
  set nd := rho.stateBefore i v with hnd
  have hσ : stateAt S rho hn v i = shapeOf S hn nd := rfl
  rw [hσ] at hlen hf hself0 ⊢
  obtain ⟨hR1, hR2, hR3, hseen3, hS3, hout2, hnode2, hself2, hnow2, hfg2⟩ :=
    leading_polls S rho hn v nd t hsel hf hlen (forwards_empty S rho hn hv v i)
  set X := encodeTxs (Model.mempool rho.inbox v t)
  set dg := digestOf S rho
  set n1 := (Node.acCall (rho.ownKey v) (shapeOf S hn nd).node t .tick).1
  have hp2 : (S.params (pubOf E) hn).toParams.IsPublic
      (shapeOf S hn (rho.dutyStep v (rho.dutyStep v
        ⟨(Model.protoOf (compiled (family S)) E).clock nd.st t (Model.mempool rho.inbox v t),
          nd.seen⟩ (.poll t.toNat)).1 (.poll t.toNat)).1).now :=
    by rw [hnow2]; exact hp
  obtain ⟨hn3, ho3, hf3, hs3, hw3⟩ := nodeTick_public S hn _ hp2 hout2
  rw [hnode2, hself2, hnow2, hself0] at hn3 ho3
  rw [hself2, hself0] at hs3
  rw [hnow2] at hw3
  -- the cuts of the node's tick
  have hcuts : (exec (runProposer S rho hn) dg (rho.ownKey v)
      (shapeOf S hn nd).node t (.tick X)).2 =
      [(Node.acCall (rho.ownKey v) (shapeOf S hn nd).node t .tick).2] ++
        (Node.tickStep (runProposer S rho hn) dg (rho.ownKey v) n1 t X .proposal).2 ++
        (Node.tickStep (runProposer S rho hn) dg (rho.ownKey v)
          (Node.tickStep (runProposer S rho hn) dg (rho.ownKey v) n1 t X .proposal).1 t X
          .fgUpdate).2 :=
    onTick_cuts (sp := S.params (pubOf E) hn) (ro := S.ro _)
      (runProposer S rho hn) dg (rho.ownKey v) _ t X
  -- the third and fourth duties
  have hpre : preNode S rho v nd t = (rho.dutyStep v (rho.dutyStep v (rho.dutyStep v
      ⟨(Model.protoOf (compiled (family S)) E).clock nd.st t (Model.mempool rho.inbox v t),
        nd.seen⟩ (.poll t.toNat)).1 (.poll t.toNat)).1 (.pollPropose t.toNat)).1 := rfl
  have hpre_shape : shapeOf S hn (preNode S rho v nd t) =
      nodeTick (poll (poll { nd.st.1 hn with now := t } t.toNat).1 t.toNat).1 :=
    pre_shape S rho hn v nd t hsel
  -- the final step, common to both cases
  have finish : ∀ (N4 : Model.Node (Model.protoOf (compiled (family S)) E))
      (R4 : List (Model.protoOf (compiled (family S)) E).Object) (c2 : List (Cut _)),
      (shapeOf S hn N4).fgDue = true → (shapeOf S hn N4).self = rho.ownKey v →
      (shapeOf S hn N4).now = t →
      (shapeOf S hn N4).node =
        (Node.tickStep (runProposer S rho hn) dg (rho.ownKey v) n1 t X .proposal).1 →
      (shapeOf S hn N4).outbox = emitted [(Node.acCall (rho.ownKey v) (shapeOf S hn nd).node t
        .tick).2] ++ emitted c2 →
      c2 = (Node.tickStep (runProposer S rho hn) dg (rho.ownKey v) n1 t X .proposal).2 →
      R4 = blockObjs c2 →
      N4.seen = nd.seen ++ relHead S rho v nd.seen (shapeOf S hn nd).outbox.head? ++ R4 →
      (shapeOf S hn N4).outbox.length ≤ 1 →
      (∀ c ∈ R4, ∀ x ∈ c.carried, x ∈ Model.closure (nd.seen ++
        relHead S rho v nd.seen (shapeOf S hn nd).outbox.head?)) →
      (rho.tick nd v t).2 = relHead S rho v nd.seen (shapeOf S hn nd).outbox.head? ++ R4 ++
        (rho.dutyStep v N4 (.poll t.toNat)).2 ++
        (rho.dutyStep v (rho.dutyStep v N4 (.poll t.toNat)).1 (.poll t.toNat)).2 ++
        (Model.releaseAll (Model.protoOf (compiled (family S)) E) rho.hash (rho.ownKey v)
          (rho.dutyStep v (rho.dutyStep v N4 (.poll t.toNat)).1 (.poll t.toNat)).1
          (Model.gossipCandidates (Model.protoOf (compiled (family S)) E)
            (rho.dutyStep v (rho.dutyStep v N4 (.poll t.toNat)).1 (.poll t.toNat)).1.st t)).2 →
      ∃ (N4 N5 : Model.Node (Model.protoOf (compiled (family S)) E)) (Q : List Body)
        (R4 F G : List (Model.protoOf (compiled (family S)) E).Object),
        (rho.tick nd v t).2 =
          relHead S rho v nd.seen (shapeOf S hn nd).outbox.head? ++ R4 ++
            (relHead S rho v N4.seen Q.head? ++ F) ++ relHead S rho v N5.seen Q.tail.head? ++ G ∧
        N4.seen = nd.seen ++ relHead S rho v nd.seen (shapeOf S hn nd).outbox.head? ++ R4 ∧
        N5.seen = N4.seen ++ (relHead S rho v N4.seen Q.head? ++ F) ∧
        (∀ o ∈ F, ∃ τ cs, o = .mk (.signed (rho.ownKey v) .poll) (.data (.forward τ)) cs) ∧
        (∀ o ∈ G, o.auth = .none) ∧ Q.length ≤ 2 ∧
        Q = emitted (exec (runProposer S rho hn) dg (rho.ownKey v)
            (shapeOf S hn nd).node t (.tick X)).2 ++
          attBodies (exec (runProposer S rho hn) dg (rho.ownKey v)
            (shapeOf S hn nd).node t (.tick X)).2 ∧
        R4 = blockObjs (exec (runProposer S rho hn) dg (rho.ownKey v)
            (shapeOf S hn nd).node t (.tick X)).2 ∧
        (∀ c ∈ R4, ∀ x ∈ c.carried, x ∈ Model.closure (nd.seen ++
          relHead S rho v nd.seen (shapeOf S hn nd).outbox.head?)) ∧
        N5 = (rho.dutyStep v N4 (.poll t.toNat)).1 := by
    intro N4 R4 c2 hf4 hs4 hw4 hn4 ho4 hc2 hR4 hseen4 hb4 hcar htick
    obtain ⟨F, hR5, hseen5, hR6, -, hF⟩ := trailing_polls S rho hn v N4 t.toNat hsel hf4
    obtain ⟨hQ, hem3, hbl3, -⟩ := fgUpdate_outbox_eq (runProposer S rho hn) dg X (shapeOf S hn N4)
    rw [hs4, hn4, hw4] at hQ hem3 hbl3
    refine ⟨N4, (rho.dutyStep v N4 (.poll t.toNat)).1, (fgUpdate (shapeOf S hn N4)).outbox, R4, F,
      (Model.releaseAll (Model.protoOf (compiled (family S)) E) rho.hash (rho.ownKey v)
        (rho.dutyStep v (rho.dutyStep v N4 (.poll t.toNat)).1 (.poll t.toNat)).1
        (Model.gossipCandidates (Model.protoOf (compiled (family S)) E)
          (rho.dutyStep v (rho.dutyStep v N4 (.poll t.toNat)).1 (.poll t.toNat)).1.st t)).2,
      ?_, hseen4, hseen5, hF, gossip_unsigned S rho _ _ _, ?_, ?_, ?_, hcar, rfl⟩
    · rw [htick, hR5, hR6]
    · rcases fgUpdate_outbox (shapeOf S hn N4) with h | ⟨a, h⟩
      · rw [h]; omega
      · rw [h, List.length_append, List.length_singleton]; omega
    · rw [hQ, ho4, hcuts, hc2, emitted_append, emitted_append, attBodies_append, attBodies_append,
        hem3, tickStep_proposal_attBodies (sp := S.params (pubOf E) hn) (ro := S.ro _)
          (runProposer S rho hn) dg (rho.ownKey v) n1 t X,
        show attBodies [(Node.acCall (rho.ownKey v) (shapeOf S hn nd).node t .tick).2] = [] from
          attBodies_ac _]
      simp only [List.append_nil, List.nil_append, List.append_assoc]
    · rw [hR4, hcuts, hc2, blockObjs_append, blockObjs_append, hbl3,
        show blockObjs [(Node.acCall (rho.ownKey v) (shapeOf S hn nd).node t .tick).2] = [] from
          blockObjs_ac _]
      simp only [List.append_nil, List.nil_append]
      rfl
  simp only [Model.Run.releasesAt, he]
  rcases Skeleton.proposeAt_cases (skeleton (pubOf E)) t with
    ⟨hnil, hno⟩ | ⟨s, hs, hone, hts⟩
  · -- no slot proposal at `t`
    obtain ⟨N1, N3, N5, N6, rfl, rfl, rfl, rfl, heq⟩ := tick_unroll_nil S rho v nd t ht hw hnil
    have hnp : ¬ Proposes (P := (S.params (pubOf E) hn).toParams)
        (runProposer S rho hn) (rho.ownKey v) t :=
      not_proposes S hn (runProposer S rho hn) _ t
        (fun s hs h => hno s hs (h.trans (slotTime_eq S hn s)))
    have hc2 := tickStep_proposal_not' (runProposer S rho hn) dg (rho.ownKey v) n1 t X hnp
    have hb3 := outbox_after_pre S rho hn v (shapeOf S hn nd) t ht hf hlen
      (preNode S rho v nd t) hpre_shape
    rw [hnil] at hb3
    have hb3' : (shapeOf S hn (rho.dutyStep v (rho.dutyStep v (rho.dutyStep v
        ⟨(Model.protoOf (compiled (family S)) E).clock nd.st t (Model.mempool rho.inbox v t),
          nd.seen⟩ (.poll t.toNat)).1 (.poll t.toNat)).1 (.pollPropose t.toNat)).1).outbox.length
        ≤ 1 := hb3
    refine finish _ [] [] (by rw [hS3]; exact hf3) (by rw [hS3]; exact hs3)
      (by rw [hS3]; exact hw3) (by rw [hS3, hn3, hc2]) (by rw [hS3, ho3]; simp [emitted])
      (by rw [hc2]) rfl (by rw [hseen3]; simp) hb3' (fun c hc => absurd hc List.not_mem_nil) ?_
    rw [heq, hR1, hR2, hR3]
    simp
  · -- the slot proposal of `s`
    obtain ⟨N1, N3, N4, N5, N6, rfl, rfl, rfl, rfl, rfl, heq⟩ :=
      tick_unroll_propose S rho v nd t ht hw s hs hone
    have hts' : t = (S.params (pubOf E) hn).toParams.slotTime s :=
      hts.trans (slotTime_eq S hn s).symm
    set N3 := (rho.dutyStep v (rho.dutyStep v (rho.dutyStep v
        ⟨(Model.protoOf (compiled (family S)) E).clock nd.st t (Model.mempool rho.inbox v t),
          nd.seen⟩ (.poll t.toNat)).1 (.poll t.toNat)).1 (.pollPropose t.toNat)).1 with hN3
    have hselfN3 : (shapeOf S hn N3).self = rho.ownKey v := by rw [hS3]; exact hs3
    have hnowN3 : (shapeOf S hn N3).now = t := by rw [hS3]; exact hw3
    have hnodeN3 : (shapeOf S hn N3).node = n1 := by rw [hS3]; exact hn3
    have hfgN3 : (shapeOf S hn N3).fgDue = true := by rw [hS3]; exact hf3
    have houtN3 : (shapeOf S hn N3).outbox =
        emitted [(Node.acCall (rho.ownKey v) (shapeOf S hn nd).node t .tick).2] := by
      rw [hS3]; exact ho3
    have hmem : N3.st.2 = Model.mempool rho.inbox v t :=
      runDuties_mempool S rho v [.poll t.toNat, .poll t.toNat, .pollPropose t.toNat]
        ⟨(Model.protoOf (compiled (family S)) E).clock nd.st t (Model.mempool rho.inbox v t),
          nd.seen⟩
    have hsp := selValid_proposer S rho hn hv.selValid s
    have hslot : (S.params (pubOf E) hn).toParams.slotOf (shapeOf S hn N3).now = s := by
      rw [hnowN3, hts']; exact slotOf_slotTime _ s
    have hst : (shapeOf S hn N3).now = (S.params (pubOf E) hn).toParams.slotTime s :=
      hnowN3.trans hts'
    have hrel' : rho.ownKey v ∈ rho.sel (.proposer s) →
        ∀ par info cs, (propose (shapeOf S hn N3) s).2 = some (par, info, cs) →
        ∀ o ∈ cs, o ∈ Model.closure N3.seen := hrel s hs hone
    obtain ⟨hR4, ho4⟩ := dutyStep_propose_full S rho hn v N3 s hs hsp hselfN3 hslot hst hrel'
    have hn4 := dutyStep_propose_node S rho hn v N3 s hs hsp hselfN3 hslot hst hrel'
    rw [hnodeN3, hnowN3, hmem] at hR4 ho4 hn4
    rw [houtN3] at ho4
    have hf4 := dutyStep_propose_pres S rho hn (fun st => st.fgDue = true)
      (fun st o hs h => (recordOwn_fgDue st o hs).trans h)
      (fun st s h => (propose_fgDue st s).trans h) v N3 s hs hfgN3
    have hs4 := dutyStep_propose_pres S rho hn (fun st => st.self = rho.ownKey v)
      (fun st o hs h => (recordOwn_self st o hs).trans h)
      (fun st s h => (propose_self st s).trans h) v N3 s hs hselfN3
    have hw4 := dutyStep_propose_pres S rho hn (fun st => st.now = t)
      (fun st o hs h => (recordOwn_now st o hs).trans h)
      (fun st s h => (propose_now st s).trans h) v N3 s hs hnowN3
    have hb3 := outbox_after_pre S rho hn v (shapeOf S hn nd) t ht hf hlen
      (preNode S rho v nd t) hpre_shape
    rw [hone] at hb3
    have hb4 : (shapeOf S hn (rho.dutyStep v N3 (.propose s hs)).1).outbox.length ≤ 1 := hb3
    have hseen4 := dutyStep_seen S rho v N3 (.propose s hs)
    rw [hseen3] at hseen4
    have hcar : ∀ c ∈ (rho.dutyStep v N3 (.propose s hs)).2, ∀ x ∈ c.carried,
        x ∈ Model.closure (nd.seen ++ relHead S rho v nd.seen (shapeOf S hn nd).outbox.head?) := by
      intro c hc x hx
      have := dutyStep_carried S rho v N3 (.propose s hs) (fun _ h => by cases h) c hc x hx
      rwa [hseen3] at this
    refine finish _ _ _ hf4 hs4 hw4 hn4 ho4 rfl hR4 hseen4 hb4 hcar ?_
    rw [heq, hR1, hR2, hR3]
    simp

end TickPublic

/-! ## Which attestations a tick releases -/

section Inventory

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- An attestation's canonical object is the poll object of its attestation body, signed by its
validator. -/
theorem attObj_eq_pollObj {v : V} {b : FG.Att (Fintype.card V)} {q : Body}
    (h : (attObj b : (Model.protoOf (compiled (family S)) E).Object) = pollObj S rho v q) :
    q = .att (encodeAtt b) ∧ b.val = rho.ownKey v := by
  injection h with h1 h2 h3
  injection h1 with h4 h5
  injection h2 with h6
  exact ⟨h6.symm, h4⟩

omit [DecidableEq V] in
/-- The attestation body encoding is injective. -/
theorem encodeAtt_inj {n : Nat} {a b : FG.Att n} (h : encodeAtt a = encodeAtt b) : a = b := by
  have h1 := decodeAtt_encodeAtt a
  rw [h, decodeAtt_encodeAtt] at h1
  exact (Option.some.inj h1).symm

omit [DecidableEq V] in
/-- A member of `relHead` is the poll object of the head. -/
theorem mem_relHead {v : V} {seen} {ob : Option Body} {o}
    (h : o ∈ relHead S rho v seen ob) : ∃ b, ob = some b ∧ o = pollObj S rho v b := by
  cases ob with
  | none => simp [relHead] at h
  | some b =>
    simp only [relHead, Option.elim_some] at h
    split_ifs at h
    · exact ⟨b, rfl, List.mem_singleton.mp h⟩
    · simp at h

omit [DecidableEq V] in
/-- No attestation object among the canonical block objects. -/
theorem attObj_not_mem_blockObjs (b : FG.Att (Fintype.card V))
    (cs : List (Cut (goldilocksNode (S.params (pubOf E) hn) (S.ro _)))) :
    (attObj b : (Model.protoOf (compiled (family S)) E).Object) ∉
      blockObjs (sp := S.params (pubOf E) hn) cs := by
  intro h
  obtain ⟨c, -, hc⟩ := List.mem_flatMap.mp h
  match c with
  | .fg (.block B _) =>
    have := List.mem_singleton.mp hc
    injection this with h1 h2 h3
    cases h2
  | .fg (.attestation _) => exact absurd hc List.not_mem_nil
  | .fg (.attest _ _) => exact absurd hc List.not_mem_nil
  | .ac _ => exact absurd hc List.not_mem_nil

omit [DecidableEq V] in
/-- An attestation body among `emitted ++ attBodies` comes from a signing cut. -/
theorem att_mem_bodies {cs : List (Cut (goldilocksNode (S.params (pubOf E) hn) (S.ro _)))}
    {w : WireAtt} (h : Body.att w ∈ emitted cs ++ attBodies cs) :
    ∃ C a, Cut.fg (.attest C (some a)) ∈ cs ∧ w = encodeAtt a := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨c, -, hc⟩ := List.mem_flatMap.mp h
    match c with
    | .ac ℓ =>
      obtain ⟨e, -, he⟩ := List.mem_map.mp hc
      cases he
    | .fg _ => exact absurd hc List.not_mem_nil
  · obtain ⟨c, hc, hb⟩ := List.mem_flatMap.mp h
    match c, hc, hb with
    | .fg (.attest C (some a)), hc, hb =>
      have := List.mem_singleton.mp hb
      injection this with h1
      exact ⟨C, a, hc, h1⟩
    | .fg (.attest _ none), _, hb => exact absurd hb List.not_mem_nil
    | .fg (.block _ _), _, hb => exact absurd hb List.not_mem_nil
    | .fg (.attestation _), _, hb => exact absurd hb List.not_mem_nil
    | .ac _, _, hb => exact absurd hb List.not_mem_nil

end Inventory

section Inventory2

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- `preNode` is the engine's node at the proposal duty (`atProposal`, Steps). -/
theorem preNode_eq_atProposal (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (t : Time) : preNode S rho v nd t = atProposal S rho v nd t := by
  rw [atProposal_eq]; rfl

/-- The proposal of an honest node's tick carries only objects the node has seen
(`proposal_releasable`, Steps). -/
theorem preNode_releasable (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (hv' : v ∈ rho.honest) (he : rho.events[i]? = some (.tick v t)) :
    ∀ s (hs : 0 < s), (skeleton (pubOf E)).proposeAt t = [.propose s hs] →
      rho.ownKey v ∈ rho.sel (.proposer s) → ∀ par info cs,
      (propose (shapeOf S hn (preNode S rho v (rho.stateBefore i v) t)) s).2 =
        some (par, info, cs) →
      ∀ o ∈ cs, o ∈ Model.closure (preNode S rho v (rho.stateBefore i v) t).seen := by
  rw [preNode_eq_atProposal]
  exact fun s hs hone hsel par info cs h =>
    proposal_releasable S rho hn hv v hv' i t he s par info cs hs hone hsel h

/-- At a tick at a non-public time an honest node releases only its queued body and unsigned
gossip. -/
theorem tick_other_releases (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (hv' : v ∈ rho.honest) (he : rho.events[i]? = some (.tick v t))
    (hnp : ¬ (S.params (pubOf E) hn).toParams.IsPublic t) :
    ∀ o ∈ rho.releasesAt i, o ∈ relHead S rho v (rho.stateBefore i v).seen
      (stateAt S rho hn v i).outbox.head? ∨ o.auth = .none := by
  have hm := List.mem_of_getElem? he
  have ht : 0 ≤ t := (hv.in_horizon _ hm).1
  have hw := hv.tick_awake v t hm
  have hsel : rho.ownKey v ∈ rho.sel .poll := by
    rw [selValid_poll S rho hv.selValid]; exact Finset.mem_univ _
  obtain ⟨hamo, -⟩ := outbox_inv S rho hn hv v hv' i
  obtain ⟨-, hlen⟩ := (atMostOneVote_iff _).1 hamo
  have hf := fgDue_eq_false S rho hn v i
  set nd := rho.stateBefore i v
  have hσ : stateAt S rho hn v i = shapeOf S hn nd := rfl
  rw [hσ] at hlen hf ⊢
  obtain ⟨hR1, hR2, hR3, -, hS3, hout2, -, -, hnow2, hfg2⟩ :=
    leading_polls S rho hn v nd t hsel hf hlen (forwards_empty S rho hn hv v i)
  have hnil : (skeleton (pubOf E)).proposeAt t = [] := by
    rcases Skeleton.proposeAt_cases (skeleton (pubOf E)) t with
      ⟨h, -⟩ | ⟨s, hs, -, hts⟩
    · exact h
    · exfalso; apply hnp
      rw [hts, ← slotTime_eq S hn s]
      exact (S.params (pubOf E) hn).toParams.slotTime_public s
  obtain ⟨N1, N3, N5, N6, h1, rfl, rfl, rfl, heq⟩ := tick_unroll_nil S rho v nd t ht hw hnil
  rw [← h1] at hR2 hR3 hS3 hout2 hnow2 hfg2
  have hS3' : shapeOf S hn (rho.dutyStep v (rho.dutyStep v N1 (.poll t.toNat)).1
      (.pollPropose t.toNat)).1 = shapeOf S hn (rho.dutyStep v N1 (.poll t.toNat)).1 := by
    rw [hS3]; unfold nodeTick; rw [ite_eq_right (by rw [hnow2]; exact hnp)]
  have hpre3 : pollPre (shapeOf S hn (rho.dutyStep v (rho.dutyStep v N1 (.poll t.toNat)).1
      (.pollPropose t.toNat)).1) = shapeOf S hn (rho.dutyStep v N1 (.poll t.toNat)).1 := by
    rw [pollPre_eq]; rw [hS3', hfg2]; rfl
  have hR5 := dutyStep_poll_eq S rho hn v (rho.dutyStep v (rho.dutyStep v N1 (.poll t.toNat)).1
    (.pollPropose t.toNat)).1 t.toNat hsel (by
      rw [hS3', dutyStep_poll S rho hn _ _ _ hsel]
      exact poll_forwards _ _)
  rw [hpre3, hout2] at hR5
  have hS5 := dutyStep_poll S rho hn v (rho.dutyStep v (rho.dutyStep v N1 (.poll t.toNat)).1
    (.pollPropose t.toNat)).1 t.toNat hsel
  have hpre5 : pollPre (shapeOf S hn (rho.dutyStep v (rho.dutyStep v
      (rho.dutyStep v N1 (.poll t.toNat)).1 (.pollPropose t.toNat)).1 (.poll t.toNat)).1) =
      shapeOf S hn (rho.dutyStep v (rho.dutyStep v
        (rho.dutyStep v N1 (.poll t.toNat)).1 (.pollPropose t.toNat)).1 (.poll t.toNat)).1 := by
    rw [pollPre_eq]; rw [hS5, poll_fgDue]; rfl
  have hout5 : (shapeOf S hn (rho.dutyStep v (rho.dutyStep v
      (rho.dutyStep v N1 (.poll t.toNat)).1 (.pollPropose t.toNat)).1 (.poll t.toNat)).1).outbox =
      [] := by
    rw [hS5, (poll_outbox _ _).1, hpre3, hout2]; rfl
  have hR6 := dutyStep_poll_eq S rho hn v (rho.dutyStep v (rho.dutyStep v
    (rho.dutyStep v N1 (.poll t.toNat)).1 (.pollPropose t.toNat)).1 (.poll t.toNat)).1
    t.toNat hsel (by rw [hS5]; exact poll_forwards _ _)
  rw [hpre5, hout5] at hR6
  intro o ho
  simp only [Model.Run.releasesAt, he] at ho
  rw [heq, hR1, hR2, hR3, hR5, hR6] at ho
  simp only [relHead, List.head?_nil, Option.elim_none, List.append_nil] at ho
  rcases List.mem_append.mp ho with ho | ho
  · exact Or.inl ho
  · exact Or.inr (gossip_unsigned S rho _ _ _ o ho)

/-- **Which attestations a tick releases.** An honest node releases an attestation object only
at a tick at a public time, and only the attestation one of its tick's cuts signs. -/
theorem att_released_inv (hv : rho.ExecutionValid) {j : Nat} {v : V} {t : Time}
    (hv' : v ∈ rho.honest) (he : rho.events[j]? = some (.tick v t)) {b : FG.Att (Fintype.card V)}
    (hb : (attObj b : (Model.protoOf (compiled (family S)) E).Object) ∈ rho.releasesAt j) :
    (S.params (pubOf E) hn).toParams.IsPublic t ∧ ∃ C,
      Cut.fg (.attest C (some b)) ∈ (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v j).node t (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2 := by
  obtain ⟨hamo, -⟩ := outbox_inv S rho hn hv v hv' j
  obtain ⟨hvote, -⟩ := (atMostOneVote_iff _).1 hamo
  have hnotpend : ∀ seen, (attObj b : (Model.protoOf (compiled (family S)) E).Object) ∉
      relHead S rho v seen (stateAt S rho hn v j).outbox.head? := by
    intro seen h
    obtain ⟨q, hq, hqo⟩ := mem_relHead S rho h
    obtain ⟨w, rfl⟩ := hvote q (List.mem_of_mem_head? hq)
    exact absurd (attObj_eq_pollObj S rho hqo).1 (by simp)
  by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
  · refine ⟨hp, ?_⟩
    obtain ⟨N4, N5, Q, R4, F, G, heq, -, -, hF, hG, -, hQ, hR4, -⟩ :=
      tick_public_analysis S rho hn hv hv' he hp (preNode_releasable S rho hn hv hv' he)
    rw [heq] at hb
    have hQmem : ∀ seen ob, ob ∈ [Q.head?, Q.tail.head?] →
        (attObj b : (Model.protoOf (compiled (family S)) E).Object) ∈ relHead S rho v seen ob →
        ∃ C, Cut.fg (.attest C (some b)) ∈ (exec (runProposer S rho hn)
          (digestOf S rho) (rho.ownKey v)
          (stateAt S rho hn v j).node t (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2 := by
      intro seen ob hob h
      obtain ⟨q, rfl, hqo⟩ := mem_relHead S rho h
      obtain ⟨hq, -⟩ := attObj_eq_pollObj S rho hqo
      have hqQ : q ∈ Q := by
        rcases List.mem_pair.mp hob with h' | h'
        · exact List.mem_of_mem_head? h'.symm
        · exact List.mem_of_mem_tail (List.mem_of_mem_head? h'.symm)
      rw [hQ, hq] at hqQ
      obtain ⟨C, a, hc, hw⟩ := att_mem_bodies S hn hqQ
      have hab := encodeAtt_inj hw
      subst hab
      exact ⟨C, hc⟩
    rcases List.mem_append.mp hb with hb | h
    swap
    · exact absurd (hG _ h) (by simp [attObj, Model.Obj.auth])
    rcases List.mem_append.mp hb with hb | h
    swap
    · exact hQmem _ _ (by simp) h
    rcases List.mem_append.mp hb with hb | h
    swap
    · rcases List.mem_append.mp h with h | h
      · exact hQmem _ _ (by simp) h
      · obtain ⟨τ, cs, heq⟩ := hF _ h
        have hm := congrArg Model.Obj.msg heq
        change Model.Msg.data (Body.att (encodeAtt b)) = Model.Msg.data (Body.forward τ) at hm
        cases hm
    rcases List.mem_append.mp hb with h | h
    · exact absurd h (hnotpend _)
    · rw [hR4] at h; exact absurd h (attObj_not_mem_blockObjs S hn b _)
  · exfalso
    rcases tick_other_releases S rho hn hv hv' he hp _ hb with h | h
    · exact hnotpend _ h
    · exact absurd h (by simp [attObj, Model.Obj.auth])

end Inventory2

/-! ## The releases of a tick -/

section TickReleases

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- A signing cut of a handler of `self` signs an attestation of `self`. -/
theorem attest_val_of_mem_exec {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp ro)) (t : Time) (e : Event (goldilocksNode sp ro))
    {C : (goldilocksNode sp ro).Blk} {a : FG.Att sp.n}
    (h : Cut.fg (.attest C (some a)) ∈ (exec proposer dg self st t e).2) : a.val = self := by
  have key : ∀ {st st' : NodeState (goldilocksNode sp ro)} {cs},
      CutChain self t st cs st' → Cut.fg (.attest C (some a)) ∈ cs → a.val = self := by
    intro st st' cs hc
    induction hc with
    | nil => simp
    | @cons st₀ st₁ _ c cs hstep _ ih =>
      intro hm
      rcases List.mem_cons.mp hm with hm | hm
      · subst hm
        obtain ⟨he, -, -⟩ := hstep
        exact createAtt_val he
      · exact ih hm
  exact key (Compose.exec_is_cut_chain (P := sp.toParams) (A := goldilocksNode sp ro)
    proposer dg self st t e) h

omit [DecidableEq V] in
/-- An object carrying nothing contains only itself. -/
theorem contains_atomic {a : Model.Auth (Fintype.card V) (ShapeRole Empty)}
    {m : Model.Msg (Header Info) Body} {y : (Model.protoOf (compiled (family S)) E).Object}
    (h : Model.Obj.Contains (Model.Obj.mk a m []) y) : y = Model.Obj.mk a m [] := by
  rcases h.cases with h | ⟨c, hc, -⟩
  · exact h
  · exact absurd hc List.not_mem_nil

omit [DecidableEq V] in
/-- The closure is closed under containment. -/
theorem mem_closure_of_contains {l : List (Model.protoOf (compiled (family S)) E).Object}
    {x y : (Model.protoOf (compiled (family S)) E).Object} (hx : x ∈ Model.closure l)
    (h : Model.Obj.Contains x y) : y ∈ Model.closure l := by
  obtain ⟨r, hr, hc⟩ := (Model.mem_closure_iff _ _).mp hx
  exact (Model.mem_closure_iff _ _).mpr ⟨r, hr, hc.trans h⟩

/-- A signing cut of an honest node's tick at a public time is a signing of the simulating
trace. -/
theorem signAt_of_tick_cut {j : Nat} {v : V} {t : Time}
    (he : rho.events[j]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) {C} {b : FG.Att (Fintype.card V)}
    (hc : Cut.fg (.attest C (some b)) ∈ (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      (stateAt S rho hn v j).node t (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2) :
    ∃ k, (simTrace S rho hn).SignAt (rho.ownKey v) k b := by
  have hj : j < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  have hEC := eventCuts_tick_public S rho hn j v t he hp
  obtain ⟨m, hm, hcm⟩ := List.getElem_of_mem hc
  have hm' : m < (eventCuts S rho hn j).length := by
    rw [hEC]; exact lt_of_lt_of_eq hm
      (length_groupRecs (sp := S.params (pubOf E) hn) (ro := S.ro _) _ _ _ _ _ _ _).symm
  have hk := allCuts_getElem?_add S rho hn j m hj hm'
  rw [List.getElem?_eq_getElem hm'] at hk
  have hm'' : m < (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      (stateAt S rho hn v j).node t
      (Nat.pair j 0) (.tick (encodeTxs (Model.mempool rho.inbox v t)))).length :=
    lt_of_lt_of_eq hm
      (length_groupRecs (sp := S.params (pubOf E) hn) (ro := S.ro _) _ _ _ _ _ _ _).symm
  obtain ⟨hnode, -, -, -, hlab⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm''
  refine ⟨cutMap S rho hn j + m, C, ?_, ?_⟩
  · rw [simTrace_node, hk]
    simp only [Option.elim_some]
    rw [show (eventCuts S rho hn j)[m] = (groupRecs (runProposer S rho hn)
      (digestOf S rho) (rho.ownKey v)
      (stateAt S rho hn v j).node t (Nat.pair j 0)
      (.tick (encodeTxs (Model.mempool rho.inbox v t))))[m] from by simp only [hEC]]
    exact hnode
  · rw [simTrace_label, hk]
    simp only [Option.map_some]
    rw [show (eventCuts S rho hn j)[m] = (groupRecs (runProposer S rho hn)
      (digestOf S rho) (rho.ownKey v)
      (stateAt S rho hn v j).node t (Nat.pair j 0)
      (.tick (encodeTxs (Model.mempool rho.inbox v t))))[m] from by simp only [hEC], hlab, hcm]

/-- The canonical attestation object is injective. -/
theorem attObj_inj {n : Nat} {a b : FG.Att n} (h : (attObj a : Wire n) = attObj b) : a = b := by
  injection h with h1 h2 h3
  injection h2 with h4
  injection h4 with h5
  exact encodeAtt_inj h5

omit [DecidableEq V] in
/-- A release batch cannot introduce a nested object that was neither already held nor a
top-level candidate: the carried-object guard checks the preceding holdings. -/
private theorem releaseAll_closure_source
    (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (cs : List (Model.protoOf (compiled (family S)) E).Object) :
    ∀ o ∈ Model.closure (Model.releaseAll (Model.protoOf (compiled (family S)) E)
      rho.hash (rho.ownKey v) nd cs).1.seen, o ∈ Model.closure nd.seen ∨
        o ∈ (Model.releaseAll (Model.protoOf (compiled (family S)) E)
          rho.hash (rho.ownKey v) nd cs).2 := by
  induction cs generalizing nd with
  | nil => intro o ho; exact Or.inl ho
  | cons c cs ih =>
    unfold Model.releaseAll
    split
    next hg =>
      intro o ho
      rcases ih _ o ho with ho | ho
      · change o ∈ Model.closure (nd.seen ++ [c]) at ho
        rw [Model.closure_append] at ho
        rcases List.mem_append.mp ho with ho | ho
        · exact Or.inl ho
        · obtain ⟨c', hc', hcon⟩ := (Model.mem_closure_iff _ _).mp ho
          have he : c' = c := List.mem_singleton.mp hc'
          subst c'
          rcases hcon.cases with rfl | ⟨x, hx, hxo⟩
          · exact Or.inr List.mem_cons_self
          · have hr := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hg).1).1
            have hxheld : x ∈ Model.closure nd.seen :=
              of_decide_eq_true (List.all_eq_true.mp hr x hx)
            exact Or.inl (mem_closure_of_contains S hxheld hxo)
      · exact Or.inr (List.mem_cons_of_mem _ ho)
    next hg =>
      intro o ho
      rcases ih nd o ho with ho | ho
      · exact Or.inl ho
      · exact Or.inr ho

/-- **The releases of a tick.** At an honest node's tick at a public time the engine releases
the canonical object of the block of every block cut of the tick, the vote of every emission of
the tick's AC cuts and the attestation of every signing cut. The attestation passes the own-object
guard: every own attestation the node has seen, or released earlier in the tick, is one it signed
in the simulating trace, and its signings there are pairwise not slashable (`hnf`). -/
theorem tick_releases (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (hv' : v ∈ rho.honest) (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t)
    (hnf : ∀ k k' a b, (simTrace S rho hn).SignAt (rho.ownKey v) k a →
      (simTrace S rho hn).SignAt (rho.ownKey v) k' b → ¬ FG.slashable a b) :
    ∀ r ∈ eventCuts S rho hn i,
      (∀ B acc, r.label = .fg (.block B acc) → r.pos ≠ 0 →
        blockObj (S.params (pubOf E) hn) B ∈ rho.releasesAt i) ∧
      (∀ ℓ, r.label = .ac ℓ → ∀ m ∈ ℓ.emits, voteObj m.msg ∈ rho.releasesAt i) ∧
      (∀ C a, r.label = .fg (.attest C (some a)) → attObj a ∈ rho.releasesAt i) := by
  intro r hr
  have hEC := eventCuts_tick_public S rho hn i v t he hp
  have hlab : r.label ∈ (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      (stateAt S rho hn v i).node t
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2 := by
    rw [hEC] at hr
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hr
    obtain ⟨-, -, -, -, hl⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
    rw [hl]; exact List.getElem_mem _
  obtain ⟨hamo, -⟩ := outbox_inv S rho hn hv v hv' i
  obtain ⟨hvote, -⟩ := (atMostOneVote_iff _).1 hamo
  obtain ⟨N4, N5, Q, R4, F, G, heq, hseen4, hseen5, hF, -, hQlen, hQ, hR4, hcar, hN5⟩ :=
    tick_public_analysis S rho hn hv hv' he hp (preNode_releasable S rho hn hv hv' he)
  set nd := rho.stateBefore i v
  set R1 := relHead S rho v nd.seen (stateAt S rho hn v i).outbox.head?
  have hpos : ∀ q ∈ Q, Q.head? = some q ∨ Q.tail.head? = some q := by
    intro q hq
    match Q, hQlen, hq with
    | [a], _, hq => rw [List.mem_singleton] at hq; subst hq; exact Or.inl rfl
    | [a, b], _, hq =>
      rcases List.mem_pair.mp hq with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    | _ :: _ :: _ :: _, h, _ => simp at h
  have hsigner : ∀ b' : FG.Att (Fintype.card V), b'.val = rho.ownKey v →
      rho.signerOf (attObj b') = some v := by
    intro b' hb'
    simp [Model.Run.signerOf, Model.Obj.signer?, attObj, Model.Obj.auth, hb', Model.Run.ownKey]
  -- own attestations seen before the tick, or released in it before the attestation
  have hbase : ∀ b' : FG.Att (Fintype.card V), b'.val = rho.ownKey v →
      (attObj b' : (Model.protoOf (compiled (family S)) E).Object) ∈ Model.closure (nd.seen ++ R1) →
      ∃ k, (simTrace S rho hn).SignAt (rho.ownKey v) k b' := by
    intro b' hb' ho
    rw [Model.closure_append] at ho
    rcases List.mem_append.mp ho with ho | ho
    · obtain ⟨j, -, t', hej, hrj⟩ := rho.signed_seen_released hv ho hv' (hsigner b' hb')
      rcases hej with hej | ⟨o, hej⟩
      · obtain ⟨hp', C, hc⟩ := att_released_inv S rho hn hv hv' hej hrj
        exact signAt_of_tick_cut S rho hn hej hp' hc
      · exact absurd hrj (deliver_not_att S rho hn hv hej b')
    · exfalso
      obtain ⟨x, hx, hc⟩ := (Model.mem_closure_iff _ _).mp ho
      obtain ⟨q, hq, rfl⟩ := mem_relHead S rho hx
      obtain ⟨w, rfl⟩ := hvote q (List.mem_of_mem_head? hq)
      have := contains_atomic S hc
      exact absurd (attObj_eq_pollObj S rho this).1 (by simp)
  have hsig4 : ∀ b' : FG.Att (Fintype.card V), b'.val = rho.ownKey v →
      (attObj b' : (Model.protoOf (compiled (family S)) E).Object) ∈ Model.closure N4.seen →
      ∃ k, (simTrace S rho hn).SignAt (rho.ownKey v) k b' := by
    intro b' hb' ho
    rw [hseen4, Model.closure_append] at ho
    rcases List.mem_append.mp ho with ho | ho
    · exact hbase b' hb' ho
    · obtain ⟨c, hc, hcon⟩ := (Model.mem_closure_iff _ _).mp ho
      rcases hcon.cases with h | ⟨x, hx, hcx⟩
      · rw [← h, hR4] at hc
        exact absurd hc (attObj_not_mem_blockObjs S hn b' _)
      · exact hbase b' hb' (mem_closure_of_contains S (hcar c hc x hx) hcx)
  have hsig5 : ∀ b' : FG.Att (Fintype.card V), b'.val = rho.ownKey v →
      (attObj b' : (Model.protoOf (compiled (family S)) E).Object) ∈ Model.closure N5.seen →
      ∃ k, (simTrace S rho hn).SignAt (rho.ownKey v) k b' := by
    intro b' hb' ho
    have hsource : (attObj b' : (Model.protoOf (compiled (family S)) E).Object) ∈
        Model.closure N4.seen ∨ attObj b' ∈ (rho.dutyStep v N4 (.poll t.toNat)).2 := by
      rw [hN5] at ho
      unfold Model.Run.dutyStep at ho ⊢
      split at ho
      · rename_i hsel
        rw [ite_eq_left hsel]
        exact releaseAll_closure_source S rho v _ _ _ ho
      · exact Or.inl ho
    rcases hsource with ho | ho
    · exact hsig4 b' hb' ho
    · have hrel : (rho.dutyStep v N4 (.poll t.toNat)).2 = relHead S rho v N4.seen Q.head? ++ F := by
        have hs := dutyStep_seen S rho v N4 (.poll t.toNat)
        rw [← hN5, hseen5] at hs
        exact List.append_cancel_left hs.symm
      rw [hrel] at ho
      rcases List.mem_append.mp ho with hx | hx
      swap
      · obtain ⟨τ, cs, heq⟩ := hF _ hx
        have hm := congrArg Model.Obj.msg heq
        change Model.Msg.data (Body.att (encodeAtt b')) = Model.Msg.data (Body.forward τ) at hm
        cases hm
      obtain ⟨q, hq, hobj⟩ := mem_relHead S rho hx
      have hq' := (attObj_eq_pollObj S rho hobj).1
      have hqQ : q ∈ Q := List.mem_of_mem_head? hq
      rw [hQ, hq'] at hqQ
      obtain ⟨C, a, hca, hw⟩ := att_mem_bodies S hn hqQ
      have hab := encodeAtt_inj hw
      subst hab
      exact signAt_of_tick_cut S rho hn he hp hca
  -- the own-object guard for an attestation signed at this tick
  have hprot : ∀ (a : FG.Att (Fintype.card V))
      (seen : List (Model.protoOf (compiled (family S)) E).Object),
      (∃ k, (simTrace S rho hn).SignAt (rho.ownKey v) k a) →
      (∀ b' : FG.Att (Fintype.card V), b'.val = rho.ownKey v →
        (attObj b' : (Model.protoOf (compiled (family S)) E).Object) ∈ Model.closure seen →
        ∃ k, (simTrace S rho hn).SignAt (rho.ownKey v) k b') →
      Model.protects (Model.protoOf (compiled (family S)) E) (rho.ownKey v) seen
        (attObj a) = true := by
    intro a seen ⟨ka, hka⟩ hs
    refine Model.protects_iff.mpr ?_
    intro _
    refine ⟨Bool.eq_false_iff.mpr fun h => ?_, fun o ho hos => ⟨Bool.eq_false_iff.mpr fun h => ?_,
      Bool.eq_false_iff.mpr fun h => ?_⟩⟩
    · obtain ⟨a1, b1, h1, h2, hsl⟩ := (conflicts_iff (Fintype.card V) (attObj a) (attObj a)).mp h
      rw [← attObj_inj h1, ← attObj_inj h2] at hsl
      exact hnf ka ka a a hka hka hsl
    · obtain ⟨a1, b1, h1, rfl, hsl⟩ := (conflicts_iff (Fintype.card V) (attObj a) o).mp h
      rw [← attObj_inj h1] at hsl
      have hb1 : b1.val = rho.ownKey v := by
        simpa [Model.Obj.signer?, attObj, Model.Obj.auth] using hos
      obtain ⟨kb, hkb⟩ := hs b1 hb1 ho
      exact hnf ka kb a b1 hka hkb hsl
    · obtain ⟨a1, b1, rfl, h2, hsl⟩ := (conflicts_iff (Fintype.card V) o (attObj a)).mp h
      rw [← attObj_inj h2] at hsl
      have ha1 : a1.val = rho.ownKey v := by
        simpa [Model.Obj.signer?, attObj, Model.Obj.auth] using hos
      obtain ⟨kb, hkb⟩ := hs a1 ha1 ho
      exact hnf kb ka a1 a hkb hka hsl
  -- a body of `Q` whose guard passes is released
  have hrelQ : ∀ q ∈ Q,
      Model.protects (Model.protoOf (compiled (family S)) E) (rho.ownKey v) N4.seen
        (pollObj S rho v q) = true →
      Model.protects (Model.protoOf (compiled (family S)) E) (rho.ownKey v) N5.seen
        (pollObj S rho v q) = true →
      pollObj S rho v q ∈ rho.releasesAt i := by
    intro q hq h4 h5
    rw [heq]
    rcases hpos q hq with h | h
    · refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      apply List.mem_append_left
      rw [h]; simp [relHead, h4]
    · refine List.mem_append_left _ (List.mem_append_right _ ?_)
      rw [h]; simp [relHead, h5]
  refine ⟨fun B acc hB _ => ?_, fun ℓ hℓ m hm => ?_, fun C a ha => ?_⟩
  · rw [heq]
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ ?_)))
    rw [hR4]
    exact List.mem_flatMap.mpr ⟨_, hB ▸ hlab, List.mem_singleton_self _⟩
  · have hval := emits_val_of_mem_exec _ _ _ _ _ _ (hℓ ▸ hlab) m hm
    have hq : Body.vote (encodeVote m.msg) ∈ Q := by
      rw [hQ]
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, hℓ ▸ hlab,
        List.mem_map.mpr ⟨m, hm, rfl⟩⟩)
    have hobj : @voteObj (pubOf E).n m.msg = pollObj S rho v (.vote (encodeVote m.msg)) := by
      unfold voteObj; rw [show m.msg.val = rho.ownKey v from hval]; rfl
    exact (congrArg (· ∈ rho.releasesAt i) hobj).mpr (hrelQ _ hq
      (protects_of_not_att S _ _ _ (fun k w h => by cases h))
      (protects_of_not_att S _ _ _ (fun k w h => by cases h)))
  · have hval := attest_val_of_mem_exec _ _ _ _ _ _ (ha ▸ hlab)
    have hq : Body.att (encodeAtt a) ∈ Q := by
      rw [hQ]
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, ha ▸ hlab,
        List.mem_singleton_self _⟩)
    have hobj : (attObj a : (Model.protoOf (compiled (family S)) E).Object) =
        pollObj S rho v (.att (encodeAtt a)) := by
      unfold attObj; rw [show a.val = rho.ownKey v from hval]; rfl
    have hsa := signAt_of_tick_cut S rho hn he hp (ha ▸ hlab)
    have h4 := hprot a N4.seen hsa hsig4
    have h5 := hprot a N5.seen hsa hsig5
    rw [hobj] at h4 h5
    exact (congrArg (· ∈ rho.releasesAt i) hobj).mpr (hrelQ _ hq h4 h5)

end TickReleases

end Consensus.Goldilocks.Refinement

end
