module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Cuts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.EngineSteps
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries
public import ConsensusLean.Lemmas.Model.Objects
public import ConsensusLean.Lemmas.Model.Candidates
public import ConsensusLean.Lemmas.Model.View
public import ConsensusLean.Lemmas.Model.Protection

public section

/-! # Goldilocks Refinement: the engine's Goldilocks state and the relay obligations

The engine runs the Goldilocks shape (`Refinement/Defs`) on its own state; this file relates that
state to the simulating trace's cuts where the relay obligations of `Simulates` need it.

* **Canonical objects.** An object a delivery's canonical event stands for is that event's
  canonical object (`canonEvent_eq_some`: `blockObj`, `voteObj`, `attObj`).
* **Wire checks and groups.** A decoded block passes the checks `decodeBlock` makes
  (`decodeBlock_wire`), a decoded attestation is well-formed (`wellFormed_of_canonEvent`), a
  `DeliverSeq` covers its cuts by groups of canonical objects (`deliverSeq_cover`), a handler's
  first FG cut names its event (`exec_head_fg`), and a cut chain steps by the cut law at every cut
  (`cutStep_of_cutChain`).
* **A delivery's relay queue** (`process_relay`). The shape's `process` of a delivery, from a
  state at the delivery's time, keeps the clock and the own index, only grows the relay queue,
  and queues the canonical object of every accepted block, every vote the pool holds after its
  `ac_on_message` call, and every attestation among the delivery's cuts (`deliverRecs`).
* **The engine's state across an event** (`stateAt_succ_deliver`: the shape of
  `Model.Run.deliver`; `_restart`, `_tick`, `stateBefore_succ_of_ne`), what the shape's steps
  keep (`propose_keeps`, `nodeTick_keeps`, `poll_keeps`, `recordOwn_keeps`), the compiled
  duties (`act_preserves`, `tick_preserves`), and two invariants: the own index is the own key
  (`stateAt_self`) and the relay queue is seen (`stateAt_relay_seen`).
* **Relaying.** The gossip of a tick or a delivery releases the unsigned relay wrapper of the
  relay queue (`deliver_relays`): what a delivery queues leaves at the delivery's
  own time.
* **Releasing.** Every emission is a vote of the emitting node (`emits_val`); a delivery or a
  restart queues the votes it emits (`process_outbox`), which wait in the outbox
  between the node's ticks and deliveries, whose poll steps release them.
  The outbox bookkeeping and tick releases are proved in `Outbox` and `Release`.
-/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload)

/-! ## Canonical objects -/

section

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

private theorem encodeVote_of_decodeVote {n : Nat} {w : WireVote} {v : Vote n}
    (h : decodeVote n w = some v) : encodeVote v = w := by
  unfold decodeVote at h
  split at h
  · cases h; rfl
  · cases h

private theorem map_of_mapM {α β : Type} {f : α → Option β} {g : β → α}
    (hfg : ∀ a b, f a = some b → g b = a) :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l'.map g = l
  | [], l', h => by simp at h; subst h; rfl
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    simp [hfg a b hb, map_of_mapM hfg hbs]

private theorem encodeInfo_of_decodeInfo {n : Nat} {i : Info} {atts : List (FG.Att n)}
    {p : Payload n} (h : decodeInfo n i = some (atts, p)) : encodeInfo atts p = i := by
  obtain ⟨i1, i2, i3⟩ := i
  simp only [decodeInfo, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨a, ha, b, hb, c, hc, rfl, rfl⟩ := h
  simp only [encodeInfo, map_of_mapM (fun _ _ => Refinement.decodeAtt_eq_some) ha,
    map_of_mapM (fun _ _ => encodeVote_of_decodeVote) hb,
    map_of_mapM (fun _ _ => encodeVote_of_decodeVote) hc]

/-- A received object that decodes to a block is that block's canonical object. -/
theorem eq_blockObj_of_decodeBlock {hs : List (Header Info × Nat)} {o : Wire sp.n}
    {B : Blk sp} (h : decodeBlock sp hs o = some B) : o = blockObj sp B := by
  unfold decodeBlock at h
  split at h
  · rename_i k s hd cs
    split at h
    · rename_i atts p d hdec hroot
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
      obtain ⟨⟨hpos, rfl, -, -⟩, rfl⟩ := h
      obtain ⟨par, pos, input, info⟩ := hd
      simp only at hpos hdec
      subst hpos
      have hinfo := encodeInfo_of_decodeInfo hdec
      simp only [blockObj, headerOf, blockOf, hinfo]
      congr
      cases par with
      | root => simp [parentRoot, parentRef]
      | digest r =>
        simp [parentRoot, parentRef, taggedRoot_ne, rawRoot_taggedRoot]
    · cases h
  · cases h

/-- A received object that decodes to a vote is that vote's canonical object. -/
theorem eq_voteObj_of_decodeVoteObj {o : Wire sp.n} {v : Vote sp.n}
    (h : decodeVoteObj sp o = some v) : o = voteObj v := by
  unfold decodeVoteObj at h
  split at h
  · rename_i k w
    cases hw : decodeVote sp.n w with
    | none => simp [hw] at h
    | some v' =>
      simp only [hw, Option.filter_some, decide_eq_true_eq] at h
      split_ifs at h with hk
      cases h
      simp only [voteObj, encodeVote_of_decodeVote hw, hk]
  · cases h

/-- A received object that decodes to an attestation is that attestation's canonical object. -/
theorem eq_attObj_of_decodeAttObj {o : Wire sp.n} {a : FG.Att sp.n}
    (h : decodeAttObj sp o = some a) : o = attObj a := by
  unfold decodeAttObj at h
  split at h
  · rename_i k w
    cases hw : decodeAtt sp.n w with
    | none => simp [hw] at h
    | some a' =>
      simp only [hw, Option.filter_some, decide_eq_true_eq] at h
      split_ifs at h with hk
      cases h
      simp only [attObj, Refinement.decodeAtt_eq_some hw, hk.1]
  · cases h

/-- The object a canonical event stands for is its canonical object. -/
theorem canonEvent_eq_some {hs : List (Header Info × Nat)} {o : Wire sp.n}
    {e : Event (goldilocksNode sp ro)} (h : canonEvent sp ro hs o = some e) :
    (∃ B, e = .block B ∧ o = blockObj sp B) ∨ (∃ v, e = .message v ∧ o = voteObj v) ∨
      ∃ a, e = .attestation a ∧ o = attObj a := by
  unfold canonEvent at h
  cases hB : decodeBlock sp hs o with
  | some B =>
    simp only [hB, Option.some.injEq] at h
    exact Or.inl ⟨B, h.symm, eq_blockObj_of_decodeBlock hB⟩
  | none =>
    cases hv : decodeVoteObj sp o with
    | some v =>
      simp only [hB, hv, Option.some.injEq] at h
      exact Or.inr (Or.inl ⟨v, h.symm, eq_voteObj_of_decodeVoteObj hv⟩)
    | none =>
      cases ha : decodeAttObj sp o with
      | some a =>
        simp only [hB, hv, ha, Option.some.injEq] at h
        exact Or.inr (Or.inr ⟨a, h.symm, eq_attObj_of_decodeAttObj ha⟩)
      | none => simp [hB, hv, ha] at h

/-! ## Wire checks, deliveries and handlers' first cuts -/

/-- A delivery sequence covers its range of cuts by groups of canonical objects it delivers. -/
theorem deliverSeq_cover {proposer : Nat → Fin sp.n} {tr : GoldilocksTrace sp ro}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {hs : List (Header Info × Nat)}
    {y : Fin sp.n} {t : Time} {os : List (Wire sp.n)} {j j' : Nat}
    (h : DeliverSeq proposer tr dg hs y t os j j') :
    j ≤ j' ∧ ∀ k, j ≤ k → k < j' → ∃ j0 e o, o ∈ os ∧ canonEvent sp ro hs o = some e ∧
      tr.GroupAt proposer dg y j0 t e ∧ j0 ≤ k ∧
        k < j0 + (Node.exec proposer dg y (tr.state y j0) t e).2.length := by
  induction h with
  | nil j => exact ⟨le_rfl, fun k h1 h2 => absurd h2 (by omega)⟩
  | @event o os j j' e he hg _ ih =>
    refine ⟨by omega, fun k h1 h2 => ?_⟩
    by_cases hk : k < j + (Node.exec proposer dg y (tr.state y j) t e).2.length
    · exact ⟨j, e, o, List.mem_cons_self .., he, hg, h1, hk⟩
    · obtain ⟨j0, e', o', ho, he', hg', h3, h4⟩ := ih.2 k (by omega) h2
      exact ⟨j0, e', o', List.mem_cons_of_mem _ ho, he', hg', h3, h4⟩
  | drop _ _ ih =>
    refine ⟨ih.1, fun k h1 h2 => ?_⟩
    obtain ⟨j0, e', o', ho, he', hg', h3, h4⟩ := ih.2 k h1 h2
    exact ⟨j0, e', o', List.mem_cons_of_mem _ ho, he', hg', h3, h4⟩
  | noCut _ _ _ _ ih =>
    refine ⟨ih.1, fun k h1 h2 => ?_⟩
    obtain ⟨j0, e', o', ho, he', hg', h3, h4⟩ := ih.2 k h1 h2
    exact ⟨j0, e', o', List.mem_cons_of_mem _ ho, he', hg', h3, h4⟩

/-- A delivered object belongs to the received object's recursive closure. -/
theorem mem_delivered {o x : Wire sp.n} (h : x ∈ delivered sp o) :
    x ∈ o.parts := h

/-- A decoded block passes the checks `decodeBlock` makes: the digests map its header to its root,
it has a parent, its attestations are well-formed and its AC payload is valid. -/
theorem decodeBlock_wire {hs : List (Header Info × Nat)} {o : Wire sp.n} {B : Blk sp}
    (h : decodeBlock sp hs o = some B) :
    (rootOf hs (headerOf sp B)).map (taggedRoot sp.genesisRoot) = some B.root ∧ B.parent ≠ none ∧
      (∀ a ∈ B.fgPayload, a.WellFormed) ∧ SA.validPayload B := by
  obtain rfl := eq_blockObj_of_decodeBlock h
  simp only [decodeBlock, blockObj] at h
  split at h
  · rename_i atts p d hdec hroot
    simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨⟨-, -, hwf, hval⟩, hB⟩ := h
    have hr : B.root = taggedRoot sp.genesisRoot d := by rw [← hB]; rfl
    refine ⟨by rw [hroot, Option.map_some, hr], ?_, ?_, ?_⟩
    · rw [← hB]
      simp only [blockOf]
      cases (headerOf sp B).parent <;> simp [parentRoot]
    · rw [← hB]; exact hwf
    · rw [← hB]; exact hval
  · simp at h

/-- A received object standing for a block event decodes to that block. -/
theorem decodeBlock_of_canonEvent {hs : List (Header Info × Nat)} {o : Wire sp.n} {B : Blk sp}
    (h : canonEvent sp ro hs o = some (.block B)) : decodeBlock sp hs o = some B := by
  cases hb : decodeBlock sp hs o with
  | some B' => simp only [canonEvent, hb, Option.some.injEq, Event.block.injEq] at h; rw [h]
  | none =>
    cases hv : decodeVoteObj sp o <;> cases ha : decodeAttObj sp o <;>
      simp [canonEvent, hb, hv, ha] at h

/-- A received object standing for an attestation event decodes to a well-formed attestation. -/
theorem wellFormed_of_canonEvent {hs : List (Header Info × Nat)} {o : Wire sp.n}
    {a : FG.Att sp.n} (h : canonEvent sp ro hs o = some (.attestation a)) : a.WellFormed := by
  have hd : decodeAttObj sp o = some a := by
    cases hb : decodeBlock sp hs o with
    | some B' => simp [canonEvent, hb] at h
    | none =>
      cases hv : decodeVoteObj sp o with
      | some v => simp [canonEvent, hb, hv] at h
      | none =>
        cases ha : decodeAttObj sp o with
        | some a' =>
          simp only [canonEvent, hb, hv, ha, Option.some.injEq, Event.attestation.injEq] at h
          rw [h]
        | none => simp [canonEvent, hb, hv, ha] at h
  unfold decodeAttObj at hd
  split at hd
  · rename_i k w
    cases hw : decodeAtt sp.n w with
    | none => simp [hw] at hd
    | some a' =>
      simp only [hw, Option.filter_some, decide_eq_true_eq] at hd
      split_ifs at hd with hk
      cases hd
      exact hk.2
  · cases hd

section

variable {P : Params} {A : NodeAC P}

/-- Cut `m` of a cut chain steps by the cut law from the fold of the cuts before it. -/
theorem cutStep_of_cutChain {self : Fin P.n} {t : Time} {st st' : NodeState A}
    {cs : List (Cut A)} (h : CutChain self t st cs st') (m : Nat) (hm : m < cs.length) :
    CutStep self t ((cs.take m).foldl (cutPost self t) st) cs[m]
      ((cs.take (m + 1)).foldl (cutPost self t) st) := by
  induction h generalizing m with
  | nil => simp at hm
  | cons hc _ ih =>
    cases m with
    | zero => simpa [cutPost_of_cutStep hc] using hc
    | succ m =>
      simp only [List.take_succ_cons, List.foldl_cons, List.getElem_cons_succ,
        cutPost_of_cutStep hc]
      exact ih m (by simpa using hm)

/-- An FG first cut of a handler is a block's or an attestation's, of the handler's event. -/
theorem exec_head_fg (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) (e : Event A) {ℓ : FGLabel P A.Payload} {cs : List (Cut A)}
    (h : (exec proposer dg self st t e).2 = .fg ℓ :: cs) :
    (∃ B acc, e = .block B ∧ ℓ = .block B acc) ∨ ∃ a, e = .attestation a ∧ ℓ = .attestation a := by
  cases e with
  | tick x => simp [Node.exec, onTick, runSteps, tickSteps, Node.tickStep, acCall] at h
  | block B =>
    simp only [Node.exec, onBlock] at h
    split_ifs at h
    cases hfg : st.fg.onBlock B <;> simp only [hfg, List.cons.injEq, Cut.fg.injEq] at h
    · exact Or.inl ⟨B, false, rfl, h.1.symm⟩
    · exact Or.inl ⟨B, true, rfl, h.1.symm⟩
  | message m => simp [Node.exec, onMessage, acCall] at h
  | attestation a => cases h; exact Or.inr ⟨a, rfl, rfl⟩
  | restart => simp [Node.exec, Node.restart, acCall] at h

/-- The first cut of a block's handler is the FG's call on the block. -/
theorem exec_block_head (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) (B : A.Blk) {c : Cut A} {cs : List (Cut A)}
    (h : (exec proposer dg self st t (.block B)).2 = c :: cs) :
    ∃ acc, c = .fg (.block B acc) := by
  simp only [Node.exec, onBlock] at h
  split_ifs at h
  cases hfg : st.fg.onBlock B <;> simp only [hfg, List.cons.injEq] at h
  · exact ⟨false, h.1.symm⟩
  · exact ⟨true, h.1.symm⟩

end

/-! ## Processing a delivery -/

/-- A cut of a group: the handler's cut `k` and its post-state. -/
private theorem mem_groupRecs_label {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {self : Fin sp.n} {st : NodeState (goldilocksNode sp ro)} {t : Time} {id : Nat}
    {e : Event (goldilocksNode sp ro)} {r : CutRec sp ro}
    (hr : r ∈ groupRecs proposer dg self st t id e) :
    ∃ k, ∃ hk : k < (exec proposer dg self st t e).2.length,
      r.label = (exec proposer dg self st t e).2[k] ∧
      r.post = (cutPosts self t (exec proposer dg self st t e).2 st)[k]'(by
        rw [length_cutPosts]; exact hk) := by
  rw [groupRecs_eq] at hr
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
  simp only [List.length_mapIdx, List.length_zip] at hk
  refine ⟨k, by omega, ?_, ?_⟩ <;> simp

private theorem relayIf_eq (st : State sp ro) (c : Prop) [Decidable c] (o : Wire sp.n) :
    relayIf st c o = { st with relayBuf := st.relayBuf ++ if c then [o] else [] } := by
  unfold relayIf
  split_ifs <;> simp

/-- The block of an accepted block cut is held after the store's step. -/
private theorem blocks_of_onBlock {st st' : Store sp.toParams (Payload sp.n)}
    {B : Blk sp} (h : st.onBlock B = some st') : st'.blocks B.root = some B := by
  obtain ⟨pr, σ', -, -, -, -, -, rfl⟩ := Store.onBlock_eq_some h
  rw [(Store.addAtts_fields _ _).1, (Store.updateFinality_spec _ _).1]
  simp

/-- One delivered object: the node state its handler leaves (at the clock), its own index and
clock kept, the relay queue extended by at most the object. -/
theorem processOne_eq (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (σ : State sp ro) (o : Wire sp.n) :
    ∃ L, (processOne hs σ o).relayBuf = σ.relayBuf ++ L ∧ (∀ x ∈ L, x = o) ∧
      (processOne hs σ o).now = σ.now ∧ (processOne hs σ o).self = σ.self ∧
      (processOne hs σ o).node =
        ((canonEvent sp ro hs o).elim σ.node fun e =>
          (exec proposer dg σ.self σ.node σ.now e).1) := by
  unfold processOne
  cases he : canonEvent sp ro hs o with
  | none => exact ⟨[], by simp, by simp, rfl, rfl, rfl⟩
  | some e =>
    rcases canonEvent_eq_some he with ⟨B, rfl, -⟩ | ⟨v, rfl, -⟩ | ⟨a, rfl, -⟩
    case inr.inl => exact ⟨[], by simp [apply], by simp, rfl, rfl, rfl⟩
    all_goals
      dsimp only
      refine ⟨_, by rw [relayIf_eq]; rfl, fun x hx => ?_, by rw [relayIf_eq]; rfl,
        by rw [relayIf_eq]; rfl, by rw [relayIf_eq]; rfl⟩
      split_ifs at hx <;> simp_all


private theorem processOne_block {hs : List (Header Info × Nat)} {σ : State sp ro}
    {o : Wire sp.n} {B : Blk sp} (he : canonEvent sp ro hs o = some (.block B))
    (h : (Node.onBlock σ.self σ.node σ.now B).1.fg.blocks B.root = some B) :
    o ∈ (processOne hs σ o).relayBuf := by
  unfold processOne
  rw [he]
  dsimp only
  rw [relayIf_eq]
  simp [h]

private theorem processOne_attestation {hs : List (Header Info × Nat)} {σ : State sp ro}
    {o : Wire sp.n} {a : FG.Att sp.n} (he : canonEvent sp ro hs o = some (.attestation a)) :
    o ∈ (processOne hs σ o).relayBuf := by
  unfold processOne
  rw [he]
  dsimp only
  rw [relayIf_eq]
  simp

/-- The relay obligations of one group of a delivery: the canonical object `o` of the group's
event is queued by `processOne` when the group has an accepted block cut, an AC message cut
after which the pool holds the vote, or an attestation cut. -/
private theorem group_relay (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    {hs : List (Header Info × Nat)} {σ : State sp ro} {t : Time} (ht : σ.now = t) {id : Nat}
    {o : Wire sp.n} {e : Event (goldilocksNode sp ro)} (he : canonEvent sp ro hs o = some e)
    {r : CutRec sp ro} (hr : r ∈ groupRecs proposer dg σ.self σ.node t id e) :
    (∀ B, r.label = .fg (.block B true) → blockObj sp B = o ∧ o ∈ (processOne hs σ o).relayBuf) ∧
    (∀ ℓ m, r.label = .ac ℓ → ℓ.call = .message m → m ∈ r.post.ac.pool m.slot →
      voteObj m = o) ∧
    (∀ a, r.label = .fg (.attestation a) → attObj a = o ∧ o ∈ (processOne hs σ o).relayBuf) := by
  obtain ⟨k, hk, hlab, hpost⟩ := mem_groupRecs_label hr
  subst ht
  rcases canonEvent_eq_some he with ⟨B, rfl, rfl⟩ | ⟨v, rfl, rfl⟩ | ⟨a, rfl, rfl⟩
  · -- a block: `[fg_on_block(B) refused]` or `[fg_on_block(B) accepted, ac_on_block(B)]`
    have hmem : r.label ∈ (exec proposer dg σ.self σ.node σ.now (.block B)).2 :=
      hlab ▸ List.getElem_mem hk
    simp only [exec, onBlock, acCall] at hmem
    split_ifs at hmem with hf
    · simp at hmem
    · cases hfg : σ.node.fg.onBlock B with
      | none =>
        simp only [hfg, List.mem_singleton] at hmem
        refine ⟨fun B' h => ?_, fun ℓ m h => ?_, fun a h => ?_⟩ <;> rw [hmem] at h <;> cases h
      | some fg' =>
        simp only [hfg, List.mem_cons, List.not_mem_nil, or_false] at hmem
        refine ⟨fun B' h => ?_, fun ℓ m h hc => ?_, fun a h => ?_⟩
        · rcases hmem with hmem | hmem <;> rw [hmem] at h <;> cases h
          refine ⟨rfl, processOne_block he ?_⟩
          simp only [onBlock, acCall, hf, ↓reduceIte, hfg]
          exact blocks_of_onBlock hfg
        · rcases hmem with hmem | hmem <;> rw [hmem] at h <;> cases h
          simp at hc
        · rcases hmem with hmem | hmem <;> rw [hmem] at h <;> cases h
  · -- a vote: `[ac_on_message(v)]`
    have hk0 : k = 0 := by simp [exec, onMessage] at hk; omega
    subst hk0
    refine ⟨fun B h => ?_, fun ℓ m h hc _ => ?_, fun a h => ?_⟩
    · simp [hlab, exec, onMessage, acCall] at h
    · simp only [hlab, exec, onMessage, acCall, List.getElem_cons_zero, Cut.ac.injEq] at h
      subst h
      cases hc
      rfl
    · simp [hlab, exec, onMessage, acCall] at h
  · -- an attestation: `[fg_on_attestation(a)]`
    have hk0 : k = 0 := by simp [exec, onAttestation] at hk; omega
    subst hk0
    refine ⟨fun B h => ?_, fun ℓ m h => ?_, fun a' h => ?_⟩
    · simp [hlab, exec, onAttestation] at h
    · simp [hlab, exec, onAttestation] at h
    · simp only [hlab, exec, onAttestation, List.getElem_cons_zero, Cut.fg.injEq,
        FGLabel.attestation.injEq] at h
      subst h
      exact ⟨rfl, processOne_attestation he⟩


/-- **A delivery's relay queue.** Processing the objects `os` from a shape state at clock `t`
keeps the clock and the own index; the relay queue only grows, by objects of `os`; and every
accepted block, every vote the pool holds after its `ac_on_message` call, and every attestation
among the delivery's cuts (`deliverRecs` from the state's node) is queued as its canonical
object. -/
theorem process_relay (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (t : Time) (i : Nat) :
    ∀ (os : List (Wire sp.n)) (σ : State sp ro) (sub : Nat), σ.now = t →
      (∃ L, (os.foldl (processOne hs) σ).relayBuf = σ.relayBuf ++ L ∧ ∀ x ∈ L, x ∈ os) ∧
      (os.foldl (processOne hs) σ).now = t ∧ (os.foldl (processOne hs) σ).self = σ.self ∧
      ∀ r ∈ deliverRecs proposer dg hs σ.self t i os σ.node sub,
        (∀ B, r.label = .fg (.block B true) →
          blockObj sp B ∈ (os.foldl (processOne hs) σ).relayBuf) ∧
        (∀ ℓ m, r.label = .ac ℓ → ℓ.call = .message m → m ∈ r.post.ac.pool m.slot →
          voteObj m ∈ os) ∧
        (∀ a, r.label = .fg (.attestation a) →
          attObj a ∈ (os.foldl (processOne hs) σ).relayBuf)
  | [], σ, sub, ht => ⟨⟨[], by simp, by simp⟩, ht, rfl, by simp [deliverRecs_nil]⟩
  | o :: os, σ, sub, ht => by
    obtain ⟨L₁, hL₁, hL₁o, hnow₁, hself₁, hnode₁⟩ := processOne_eq proposer dg hs σ o
    obtain ⟨⟨L, hL, hLos⟩, hnow, hself, hrec⟩ :=
      process_relay proposer dg hs t i os (processOne hs σ o) (sub + 1) (hnow₁.trans ht)
    rw [List.foldl_cons]
    have hkeep : ∀ x ∈ (processOne hs σ o).relayBuf,
        x ∈ (os.foldl (processOne hs) (processOne hs σ o)).relayBuf := fun x hx => by
      rw [hL]; exact List.mem_append_left _ hx
    refine ⟨⟨L₁ ++ L, by rw [hL, hL₁, List.append_assoc], fun x hx => ?_⟩, hnow,
      hself.trans hself₁, fun r hr => ?_⟩
    · rcases List.mem_append.mp hx with hx | hx
      · rw [hL₁o x hx]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hLos x hx)
    rw [hself₁, hnode₁] at hrec
    cases he : canonEvent sp ro hs o with
    | none =>
      rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ he] at hr
      rw [he] at hrec
      obtain ⟨h1, h2, h3⟩ := hrec r hr
      exact ⟨h1, fun ℓ m h hc hp => List.mem_cons_of_mem _ (h2 ℓ m h hc hp), h3⟩
    | some e =>
      rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ e he] at hr
      rw [he, Option.elim_some, ht] at hrec
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨h1, h2, h3⟩ := group_relay proposer dg ht he hr
        refine ⟨fun B h => ?_, fun ℓ m h hc hp => ?_, fun a h => ?_⟩
        · obtain ⟨rfl, ho⟩ := h1 B h; exact hkeep _ ho
        · rw [h2 ℓ m h hc hp]; exact List.mem_cons_self
        · obtain ⟨rfl, ho⟩ := h3 a h; exact hkeep _ ho
      · obtain ⟨h1, h2, h3⟩ := hrec r hr
        exact ⟨h1, fun ℓ m h hc hp => List.mem_cons_of_mem _ (h2 ℓ m h hc hp), h3⟩


end

/-! ## The engine's node state across an event -/

section

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- An engine delivery: the node after it is the engine's `deliver` (`process`, the delivery's
poll step, the gossip; `deliver_pres`). -/
theorem stateBefore_succ_deliver {i : Nat} {v : V}
    {o : (Model.protoOf (compiled (family S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) :
    rho.stateBefore (i + 1) v = (rho.deliver (rho.stateBefore i v) v o t).1 := by
  simp only [rho.stateBefore_succ he, Model.Run.step, Function.update_self]

/-- An engine delivery: the Goldilocks state after it is the shape of the engine's `deliver`. -/
theorem stateAt_succ_deliver {i : Nat} {v : V}
    {o : (Model.protoOf (compiled (family S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) :
    stateAt S rho hn v (i + 1) = (rho.deliver (rho.stateBefore i v) v o t).1.st.1 hn :=
  stateAt_deliver S rho hn v he

/-- An engine restart runs the shape's `restore` with the own key. -/
theorem stateAt_succ_restart {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.restart v t)) :
    stateAt S rho hn v (i + 1) = restore (rho.ownKey v) (stateAt S rho hn v i) t := by
  simp only [stateAt_eq, rho.stateBefore_succ he, Model.Run.step, Function.update_self]
  rfl

/-- An event of another node leaves the node's engine state unchanged. -/
theorem stateBefore_succ_of_ne {i : Nat}
    {e : Model.Event V (Model.protoOf (compiled (family S)) E).Object}
    (he : rho.events[i]? = some e) {v : V} (hne : e.node ≠ v) :
    rho.stateBefore (i + 1) v = rho.stateBefore i v := by
  rw [rho.stateBefore_succ he]
  cases e <;> simp only [Model.Event.node] at hne <;>
    simp only [Model.Run.step, Function.update_of_ne (Ne.symm hne)]

/-- Past the last event the world stays. -/
theorem stateBefore_succ_none {i : Nat} (he : rho.events[i]? = none) :
    rho.stateBefore (i + 1) = rho.stateBefore i := by
  simp [Model.Run.stateBefore, List.take_add_one, he]

end



/-! ## What the shape's steps keep -/

section

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- A delivered object is the delivery's object or carried by it. -/
theorem contains_of_mem_delivered {o x : Wire sp.n} (h : x ∈ delivered sp o) :
    Model.Obj.Contains o x := h

/-- The slot proposal keeps the relay queue and the own index. -/
theorem propose_keeps (st : State sp ro) (s : Slot) :
    (propose st s).1.relayBuf = st.relayBuf ∧ (propose st s).1.self = st.self := by
  unfold propose
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

/-- The node's tick keeps the relay queue and the own index. -/
theorem nodeTick_keeps (st : State sp ro) :
    (nodeTick st).relayBuf = st.relayBuf ∧ (nodeTick st).self = st.self := by
  unfold nodeTick
  split_ifs <;> exact ⟨rfl, rfl⟩

/-- The FG update keeps the relay queue and the own index. -/
theorem fgUpdate_keeps (st : State sp ro) :
    (fgUpdate st).relayBuf = st.relayBuf ∧ (fgUpdate st).self = st.self := by
  unfold fgUpdate
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

/-- A poll step keeps the relay queue and the own index. -/
theorem poll_keeps (st : State sp ro) (t : Time) :
    (poll st t).1.relayBuf = st.relayBuf ∧ (poll st t).1.self = st.self := by
  have h₁ : (if st.fgDue then fgUpdate st else st).relayBuf = st.relayBuf ∧
      (if st.fgDue then fgUpdate st else st).self = st.self := by
    split_ifs
    · exact fgUpdate_keeps st
    · exact ⟨rfl, rfl⟩
  unfold poll
  dsimp only
  split
  · exact h₁
  · exact h₁

/-- `recordOwn` keeps the own index; it keeps the relay queue unless the object is a relay
wrapper, which empties it. -/
theorem recordOwn_keeps (st : State sp ro) (o : Wire sp.n) (hs : List (Header Info × Nat)) :
    ((recordOwn st o hs).relayBuf = st.relayBuf ∨ (recordOwn st o hs).relayBuf = []) ∧
      (recordOwn st o hs).self = st.self := by
  unfold recordOwn
  split
  · exact ⟨Or.inr rfl, rfl⟩
  · split
    · exact ⟨Or.inl rfl, rfl⟩
    · exact ⟨Or.inl rfl, rfl⟩
  · exact ⟨Or.inl rfl, rfl⟩

/-- `recordOwn` of a signed object keeps the relay queue. -/
theorem recordOwn_relayBuf_signed (st : State sp ro) {k : Fin sp.n} {r : ShapeRole Empty}
    {m : Model.Msg (Header Info) Body} {cs : List (Wire sp.n)} (hs : List (Header Info × Nat)) :
    (recordOwn st (.mk (.signed k r) m cs) hs).relayBuf = st.relayBuf := by
  unfold recordOwn
  split
  · rename_i h; cases h
  · split <;> rfl
  · rfl

end

/-! ## The engine's duties on the Goldilocks state -/

section

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- A property of Goldilocks states kept by the slot proposal, the node's tick and a poll step
is kept by every duty of the compiled family. -/
theorem act_preserves (Q : State (S.params (pubOf E) hn) (S.ro _) → Prop)
    (hprop : ∀ st s, Q st → Q (propose st s).1) (hnt : ∀ st, Q st → Q (nodeTick st))
    (hpoll : ∀ st t, Q st → Q (poll st t).1)
    (st : (Model.protoOf (compiled (family S)) E).State)
    (d : (Model.protoOf (compiled (family S)) E).Duty) (h : Q (st.1 hn)) :
    Q (((Model.protoOf (compiled (family S)) E).act st d).1.1 hn) := by
  cases d with
  | propose s h' =>
    simp only [Model.protoOf, compiled, compile, withMempool, family, hn, ↓reduceDIte]
    exact hprop _ (s : Nat) h
  | act s k => exact k.elim
  | pollPropose t =>
    simp only [Model.protoOf, compiled, compile, withMempool, family, hn, ↓reduceDIte]
    exact hnt _ h
  | poll t =>
    simp only [Model.protoOf, compiled, compile, withMempool, family, hn, ↓reduceDIte]
    exact hpoll _ (t : Time) h

omit [DecidableEq V] in
/-- The compiled `recordOwn` is the shape's. -/
theorem recordOwn_eq (st : (Model.protoOf (compiled (family S)) E).State)
    (o : (Model.protoOf (compiled (family S)) E).Object) (hs) :
    ((Model.protoOf (compiled (family S)) E).recordOwn st o hs).1 hn =
      recordOwn (st.1 hn) o hs :=
  rfl


omit [DecidableEq V] in
/-- The digests the engine passes with a block object map the block's header to the engine's hash of
it. -/
theorem rootOf_digests_blockObj (B : Blk (S.params (pubOf E) hn)) :
    rootOf (Model.digests rho.hash (blockObj (S.params (pubOf E) hn) B))
        (headerOf (S.params (pubOf E) hn) B) =
      some (rho.hash (headerOf (S.params (pubOf E) hn) B)) :=
  rootOf_digests_item S rho _ _ _

end


/-! ## Invariants of the engine's Goldilocks state -/

section

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- An engine tick of the node: the Goldilocks state after the tick. -/
theorem stateAt_succ_tick {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) :
    stateAt S rho hn v (i + 1) = (rho.tick (rho.stateBefore i v) v t).1.st.1 hn := by
  simp only [stateAt_eq, rho.stateBefore_succ he, Model.Run.step, Function.update_self]

omit [DecidableEq V] in
/-- A property of Goldilocks states kept by the clock, every duty step and every `recordOwn`
is kept by a tick. -/
theorem tick_preserves (Q : State (S.params (pubOf E) hn) (S.ro _) → Prop)
    (hclock : ∀ st t, Q st → Q { st with now := t })
    (hprop : ∀ st s, Q st → Q (propose st s).1) (hnt : ∀ st, Q st → Q (nodeTick st))
    (hpoll : ∀ st t, Q st → Q (poll st t).1) (hrec : ∀ st o hs, Q st → Q (recordOwn st o hs))
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (v : V) (t : Time)
    (h : Q (nd.st.1 hn)) : Q ((rho.tick nd v t).1.st.1 hn) :=
  rho.tick_invariant (fun s => Q (s.1 hn)) nd v t
    (fun s d _ hs => act_preserves S hn Q hprop hnt hpoll s d hs)
    (fun s o hs _ hq => (recordOwn_eq S hn s o hs).symm ▸ hrec _ o hs hq)
    (hclock _ t h)

/-- **The own index.** The Goldilocks state of node `v` holds `v`'s own key. -/
theorem stateAt_self (v : V) : ∀ i, (stateAt S rho hn v i).self = rho.ownKey v
  | 0 => by rw [stateAt_zero]; rfl
  | i + 1 => by
    have ih := stateAt_self v i
    cases he : rho.events[i]? with
    | none =>
      simp only [stateAt_eq, stateBefore_succ_none S rho he] at ih ⊢
      exact ih
    | some e =>
      by_cases hne : e.node = v
      · cases e with
        | tick w t =>
          simp only [Model.Event.node] at hne
          subst hne
          rw [stateAt_succ_tick S rho hn he]
          exact tick_preserves S rho hn (fun st => st.self = rho.ownKey w) (fun _ _ h => h)
            (fun st s h => (propose_keeps st s).2.trans h)
            (fun st h => (nodeTick_keeps st).2.trans h)
            (fun st t h => (poll_keeps st t).2.trans h)
            (fun st o hs h => (recordOwn_keeps st o hs).2.trans h) _ w t
            (by simpa only [stateAt_eq] using ih)
        | deliver w o t =>
          simp only [Model.Event.node] at hne
          subst hne
          rw [stateAt_succ_deliver S rho hn he]
          exact deliver_pres S rho hn (fun st => st.self = rho.ownKey w)
            (fun st t h => (poll_keeps st t).2.trans h)
            (fun st _ _ hs h => (recordOwn_keeps st _ hs).2.trans h) w _ o t
            ((process_relay (runProposer S rho hn) (digestOf S rho) _ _ i _ _ 0 rfl).2.2.1.trans
              (by simpa only [stateAt_eq] using ih))
        | restart w t =>
          simp only [Model.Event.node] at hne
          subst hne
          rw [stateAt_succ_restart S rho hn he]
          rfl
      · simp only [stateAt_eq, stateBefore_succ_of_ne S rho he hne] at ih ⊢
        exact ih


/-- The relay queue after a delivery's `process` is in the closure of what the node has seen with
the delivered object, if the queue before it was. -/
theorem process_relay_seen {i : Nat} {v : V} (o : (Model.protoOf (compiled (family S)) E).Object)
    (ih : ∀ x ∈ (stateAt S rho hn v i).relayBuf, x ∈ Model.closure (rho.stateBefore i v).seen) :
    ∀ x ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).relayBuf,
      x ∈ Model.closure ((rho.stateBefore i v).seen ++ [o]) := by
  obtain ⟨⟨L, hL, hLos⟩, -⟩ := process_relay (runProposer S rho hn)
    (digestOf S rho) (Model.digests rho.hash o)
    _ i (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v i) 0 rfl
  intro x hx
  unfold process at hx
  rw [hL] at hx
  rw [Model.closure_append]
  rcases List.mem_append.mp hx with hx | hx
  · exact List.mem_append_left _ (ih x hx)
  · exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨o, List.mem_singleton_self _, contains_of_mem_delivered (hLos x hx)⟩)

/-- **The relay queue is seen.** Every object queued for relay by node `v` is in the closure of
what `v` has seen. -/
theorem stateAt_relay_seen (v : V) : ∀ i, ∀ x ∈ (stateAt S rho hn v i).relayBuf,
    x ∈ Model.closure (rho.stateBefore i v).seen
  | 0 => by rw [stateAt_zero]; exact fun x hx => absurd hx List.not_mem_nil
  | i + 1 => by
    have ih := stateAt_relay_seen v i
    cases he : rho.events[i]? with
    | none =>
      simp only [stateAt_eq, stateBefore_succ_none S rho he] at ih ⊢
      exact ih
    | some e =>
      by_cases hne : e.node = v
      · cases e with
        | tick w t =>
          simp only [Model.Event.node] at hne
          subst hne
          intro x hx
          rw [stateAt_succ_tick S rho hn he] at hx
          have hQ := tick_preserves S rho hn
            (fun st => ∀ x ∈ st.relayBuf, x ∈ Model.closure (rho.stateBefore i w).seen)
            (fun _ _ h => h)
            (fun st s h => by rw [(propose_keeps st s).1]; exact h)
            (fun st h => by rw [(nodeTick_keeps st).1]; exact h)
            (fun st t h => by rw [(poll_keeps st t).1]; exact h)
            (fun st o hs h => by
              rcases (recordOwn_keeps st o hs).1 with h' | h' <;> rw [h']
              · exact h
              · simp)
            _ w t (by simpa only [stateAt_eq] using ih) x hx
          rw [rho.stateBefore_succ he]
          simp only [Model.Run.step, Function.update_self, Model.Run.tick_seen,
            Model.closure_append]
          exact List.mem_append_left _ hQ
        | deliver w o t =>
          simp only [Model.Event.node] at hne
          subst hne
          intro x hx
          rw [stateAt_succ_deliver S rho hn he] at hx
          have hQ := deliver_pres S rho hn
            (fun st => ∀ x ∈ st.relayBuf, x ∈ Model.closure ((rho.stateBefore i w).seen ++ [o]))
            (fun st t h => by rw [(poll_keeps st t).1]; exact h)
            (fun st _ _ hs h => by
              rcases (recordOwn_keeps st _ hs).1 with h' | h' <;> rw [h']
              · exact h
              · simp) w _ o t
                (by simpa only [stateAt_eq] using process_relay_seen S rho hn o ih) x hx
          rw [stateBefore_succ_deliver S rho he, rho.deliver_seen, Model.closure_append]
          exact List.mem_append_left _ hQ
        | restart w t =>
          simp only [Model.Event.node] at hne
          subst hne
          rw [stateAt_succ_restart S rho hn he]
          rw [rho.stateBefore_succ he]
          simp only [Model.Run.step, Function.update_self]
          exact ih
      · simp only [stateAt_eq, stateBefore_succ_of_ne S rho he hne] at ih ⊢
        exact ih

end


/-! ## The engine's schedule -/

section

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E)

/-- Two events of a valid run in index order are in time-and-phase order. -/
theorem keyLe_of_index_lt (hv : rho.ExecutionValid) {i i' : Nat}
    {ev ev' : Model.Event V (Model.protoOf (compiled (family S)) E).Object}
    (he : rho.events[i]? = some ev) (he' : rho.events[i']? = some ev') (h : i < i') :
    ev.keyLe ev' := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp he
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp he'
  exact List.pairwise_iff_getElem.mp hv.sorted i i' hi hi' h

/-- An event occurs at one index of a valid run. -/
theorem index_eq_of_events (hv : rho.ExecutionValid) {i i' : Nat}
    {ev : Model.Event V (Model.protoOf (compiled (family S)) E).Object}
    (he : rho.events[i]? = some ev) (he' : rho.events[i']? = some ev) : i = i' := by
  obtain ⟨hi, h1⟩ := List.getElem?_eq_some_iff.mp he
  obtain ⟨hi', h2⟩ := List.getElem?_eq_some_iff.mp he'
  exact (hv.nodup.getElem_inj_iff).mp (h1.trans h2.symm)

/-- At a delivery the node's last tick or restart is at the delivery's time: an awake honest
node ticks at every time of the horizon, before the deliveries of that time. -/
theorem lastClock_deliver (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {o : (Model.protoOf (compiled (family S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) : lastClock S rho v i = t := by
  have hm := List.mem_of_getElem? he
  have hb := hv.in_horizon _ hm
  obtain ⟨it, hit⟩ := List.mem_iff_getElem?.mp
    (hv.tick_total v (hv.honest_only _ hm) t hb.1 hb.2 (hv.deliver_awake v o t hm))
  have hlt : it < i := by
    rcases lt_trichotomy it i with h | rfl | h
    · exact h
    · rw [he] at hit; cases hit
    · rcases keyLe_of_index_lt S rho hv he hit h with h' | h'
      · exact absurd h' (lt_irrefl _)
      · exact absurd h'.2 (by simp [Model.Event.phase])
  have key : ∀ m, it + 1 ≤ m → m ≤ i → lastClock S rho v m = t := by
    intro m hm1
    induction m, hm1 using Nat.le_induction with
    | base => intro _; simp [lastClock_succ, hit]
    | succ m hm1 ih =>
      intro hmi
      have ihm := ih (by omega)
      cases hem : rho.events[m]? with
      | none => simpa [lastClock_succ, hem] using ihm
      | some e =>
        have h1 := keyLe_of_index_lt S rho hv hit hem (by omega)
        have h2 := keyLe_of_index_lt S rho hv hem he (by omega)
        cases e with
        | tick v' t' =>
          simp only [lastClock_succ, hem]
          split_ifs with hvv
          · subst hvv
            exfalso
            have htt : t' = t := by
              rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
                simp only [Model.Event.time] at h1 h2 <;> first | linarith [h1.1, h2.1] | linarith
            subst htt
            exact absurd (index_eq_of_events S rho hv hit hem) (by omega)
          · exact ihm
        | restart v' t' =>
          simp only [lastClock_succ, hem]
          split_ifs with hvv
          · exfalso
            rcases h1 with h1 | h1
            · rcases h2 with h2 | h2
              · simp only [Model.Event.time] at h1 h2; linarith
              · simp only [Model.Event.time] at h1 h2; linarith [h2.1]
            · exact absurd h1.2 (by simp [Model.Event.phase])
          · exact ihm
        | deliver v' o' t' => simpa [lastClock_succ, hem] using ihm
  exact key i hlt le_rfl

end

/-! ## Relaying -/

section

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- The duties of a tick release only signed objects. -/
theorem runDuties_signed (v : V) :
    ∀ (ds : List (Model.protoOf (compiled (family S)) E).Duty)
      (nd : Model.Node (Model.protoOf (compiled (family S)) E)),
      ∀ o ∈ (rho.runDuties v nd ds).2, ∃ k r m cs, o = Model.Obj.mk (.signed k r) m cs
  | [], nd => by simp [rho.runDuties_nil]
  | d :: ds, nd => by
    intro o ho
    rw [rho.runDuties_cons] at ho
    rcases List.mem_append.mp ho with ho | ho
    · rw [rho.dutyStep_eq] at ho
      split at ho
      case isFalse => simp at ho
      obtain ⟨m, cs, -, -, rfl⟩ :=
        (rho.mem_signedCandidate).mp (Model.releaseAll_subset _ _ _ _ o ho)
      exact ⟨_, _, m, cs, rfl⟩
    · exact runDuties_signed v ds _ o ho

omit [DecidableEq V] in
/-- The duties of a tick append what they release to `seen`. -/
theorem runDuties_seen (v : V) :
    ∀ (ds : List (Model.protoOf (compiled (family S)) E).Duty)
      (nd : Model.Node (Model.protoOf (compiled (family S)) E)),
      (rho.runDuties v nd ds).1.seen = nd.seen ++ (rho.runDuties v nd ds).2
  | [], nd => by simp [rho.runDuties_nil]
  | d :: ds, nd => by
    rw [rho.runDuties_cons, runDuties_seen v ds, rho.dutyStep_eq]
    split
    · rw [Model.releaseAll_seen]; simp
    · simp

/-- **A delivery relays what it queued.** The gossip of a delivery to node `v` releases the
unsigned relay wrapper of its relay queue, which carries everything the delivery's `process`
queued (`process_relay`), at the delivery's own time. -/
theorem deliver_relays {j : Nat} {v : V} {o : (Model.protoOf (compiled (family S)) E).Object}
    {t : Time} (he : rho.events[j]? = some (.deliver v o t)) {x : Wire (S.params (pubOf E) hn).n}
    (hx : x ∈ (process (stateAt S rho hn v j) o (Model.digests rho.hash o)).relayBuf) :
    ∃ cs, x ∈ cs ∧ Model.Obj.mk .none (.data .relay) cs ∈ rho.releasesAt j := by
  simp only [Model.Run.releasesAt, he]
  rw [rho.deliver_eq]
  set nd := rho.stateBefore j v
  set R := rho.runDuties v ⟨(Model.protoOf (compiled (family S)) E).process nd.st o
    (Model.digests rho.hash o), nd.seen ++ [o]⟩
    ((Model.protoOf (compiled (family S)) E).deliverDuties t)
  -- the queue after the delivery's duties keeps `x` and holds only seen objects
  have hkeep : x ∈ (R.1.st.1 hn).relayBuf :=
    rho.runDuties_invariant (fun s => x ∈ (s.1 hn).relayBuf) v _ _
      (fun s d _ hs => act_preserves S hn (fun st => x ∈ st.relayBuf)
        (fun st s h => by rw [(propose_keeps st s).1]; exact h)
        (fun st h => by rw [(nodeTick_keeps st).1]; exact h)
        (fun st t h => by rw [(poll_keeps st t).1]; exact h) s d hs)
      (fun s o hs ho hq => by
        obtain ⟨k, r, m, cs, rfl⟩ := runDuties_signed S rho v _ _ o ho
        have h := recordOwn_relayBuf_signed (s.1 hn) (k := k) (r := r) (m := m) (cs := cs) hs
        rw [← h] at hq
        exact hq)
      (by rw [stateAt_eq] at hx; exact hx)
  have hseen : ∀ y ∈ (R.1.st.1 hn).relayBuf, y ∈ Model.closure R.1.seen := by
    have hQ : ∀ y ∈ (R.1.st.1 hn).relayBuf, y ∈ Model.closure (nd.seen ++ [o]) :=
      rho.runDuties_invariant
        (fun s => ∀ y ∈ (s.1 hn).relayBuf, y ∈ Model.closure (nd.seen ++ [o])) v _ _
        (fun s d _ hs => act_preserves S hn
          (fun st => ∀ y ∈ st.relayBuf, y ∈ Model.closure (nd.seen ++ [o]))
          (fun st s h => by rw [(propose_keeps st s).1]; exact h)
          (fun st h => by rw [(nodeTick_keeps st).1]; exact h)
          (fun st t h => by rw [(poll_keeps st t).1]; exact h) s d hs)
        (fun s o hs _ hq => by
          change ∀ y ∈ (recordOwn (s.1 hn) o hs).relayBuf, _
          rcases (recordOwn_keeps (s.1 hn) o hs).1 with h' | h' <;> rw [h']
          · exact hq
          · simp)
        (by
          have h := process_relay_seen S rho hn o (stateAt_relay_seen S rho hn v j)
          rw [stateAt_eq] at h
          exact h)
    intro y hy
    rw [runDuties_seen S rho v, Model.closure_append]
    exact List.mem_append_left _ (hQ y hy)
  generalize hcs : (R.1.st.1 hn).relayBuf = cs at hkeep hseen
  have hgo : Model.gossipCandidates (Model.protoOf (compiled (family S)) E) R.1.st t =
      [Model.Obj.mk .none (.data .relay) cs] := by
    obtain ⟨c, cs₀, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hkeep)
    have hcs' : ∀ h', (R.1.st.1 h').relayBuf = c :: cs₀ := fun _ => hcs
    simp only [Model.gossipCandidates, Model.protoOf, compiled, compile, family, hn,
      ↓reduceDIte, goldilocksShape, hcs']
    rfl
  refine ⟨cs, hkeep, List.mem_append_right _ ?_⟩
  have hc : (Model.releasable R.1.seen (Model.Obj.mk .none (.data .relay) cs) &&
      Model.protects (Model.protoOf (compiled (family S)) E) (rho.ownKey v) R.1.seen
        (Model.Obj.mk .none (.data .relay) cs)) = true := by
    simp only [Model.releasable, Model.protects, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq]
    refine ⟨fun y hy => hseen y hy, ?_⟩
    simp [Model.Obj.signer?, Model.Obj.auth]
  rw [hgo]
  simp only [Model.releaseAll]
  split
  · exact List.mem_cons_self
  · rename_i h
    exact False.elim (h (Bool.and_eq_true_iff.2 ⟨hc, dependencies_relay _ _ hseen⟩))

/-- A cut of an engine event that is an FG cut at position `0`, or an `ac_on_message` cut, is a
cut of a delivery. -/
theorem eq_deliver_of_cut {i : Nat}
    {ev : Model.Event V (Model.protoOf (compiled (family S)) E).Object}
    (he : rho.events[i]? = some ev) {r : CutRec (S.params (pubOf E) hn) (S.ro _)}
    (hr : r ∈ eventCuts S rho hn i)
    (h : (r.pos = 0 ∧ ∃ ℓ, r.label = .fg ℓ) ∨
      ∃ ℓ m, r.label = .ac ℓ ∧ ℓ.call = .message m) :
    ∃ v o t, ev = .deliver v o t := by
  cases ev with
  | deliver v o t => exact ⟨v, o, t, rfl⟩
  | tick v t =>
    exfalso
    by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
    · rw [eventCuts_tick_public S rho hn i v t he hp] at hr
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
      obtain ⟨-, -, -, hpos, hlab⟩ := getElem_groupRecs _ _ _ _ _ _ _ k hk
      obtain ⟨ℓ₀, pc, uc, hℓ₀, hcs, hpc, ⟨ℓ₁, hℓ₁, huc⟩⟩ :=
        Compose.tick_order (runProposer S rho hn) (digestOf S rho)
          (rho.ownKey v) (stateAt S rho hn v i).node t
          (encodeTxs (Model.mempool rho.inbox v t))
      have hcs' : (exec (runProposer S rho hn) (digestOf S rho)
          (rho.ownKey v) (stateAt S rho hn v i).node t
          (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2 = .ac ℓ₀ :: (pc ++ uc) := hcs
      rw [List.getElem_of_eq hcs'] at hlab
      rcases h with ⟨h0, ℓ, hl⟩ | ⟨ℓ, m, hl, hc⟩
      · rw [hpos] at h0
        subst h0
        rw [hlab] at hl
        cases hl
      · have hmem : Cut.ac ℓ ∈ Cut.ac ℓ₀ :: (pc ++ uc) := by
          rw [← hl, hlab]; exact List.getElem_mem _
        rcases List.mem_cons.mp hmem with h | h
        · cases h; rw [hc] at hℓ₀; cases hℓ₀
        rcases List.mem_append.mp h with h | h
        · rcases hpc with ⟨-, rfl⟩ | ⟨-, ℓ₂, hℓ₂, hpc⟩
          · simp at h
          rcases hpc with rfl | ⟨B, -, -, rfl | ⟨ℓ₃, hℓ₃, rfl⟩⟩
          · simp only [List.mem_singleton, Cut.ac.injEq] at h
            subst h; rw [hc] at hℓ₂; cases hℓ₂
          · simp only [List.mem_cons, Cut.ac.injEq, reduceCtorEq, List.not_mem_nil,
              or_false] at h
            subst h; rw [hc] at hℓ₂; cases hℓ₂
          · simp only [List.mem_cons, Cut.ac.injEq, reduceCtorEq, List.not_mem_nil, or_false,
              false_or] at h
            rcases h with rfl | rfl
            · rw [hc] at hℓ₂; cases hℓ₂
            · rw [hc] at hℓ₃; cases hℓ₃
        · rcases huc with rfl | ⟨C, rfl⟩ | ⟨C, a, rfl⟩ <;>
            simp only [List.mem_cons, Cut.ac.injEq, reduceCtorEq, List.not_mem_nil,
              or_false] at h <;>
            (subst h; rw [hc] at hℓ₁; cases hℓ₁)
    · rw [eventCuts_tick_other S rho hn i v t he hp] at hr
      simp at hr
  | restart v t =>
    exfalso
    rw [eventCuts_restart S rho hn i v t he] at hr
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
    obtain ⟨-, -, -, hpos, hlab⟩ := getElem_groupRecs _ _ _ _ _ _ _ k hk
    have hk1 : k = 0 :=
      Nat.lt_one_iff.mp (lt_of_lt_of_eq hk ((length_groupRecs _ _ _ _ _ _ _).trans rfl))
    subst hk1
    simp only [exec, Node.restart, acCall, List.getElem_cons_zero] at hlab
    rcases h with ⟨-, ℓ, hl⟩ | ⟨ℓ, m, hl, hc⟩
    · rw [hlab] at hl; cases hl
    · rw [hlab] at hl; cases hl; cases hc

end


/-! ## Releasing -/

section

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

private theorem tryVote_val {FGP : Type} (self : Fin sp.n) (A : SA.SAState sp.n) (Φ)
    (t : Time) : ∀ e ∈ (SA.tryVote (FGP := FGP) sp self A Φ t).2, e.msg.val = self := by
  unfold SA.tryVote
  dsimp only
  split_ifs <;> simp

private theorem foldl_emits_val {α σ ε : Type} (P : ε → Prop) (f : σ → α → σ × List ε)
    (hf : ∀ s a, ∀ e ∈ (f s a).2, P e) :
    ∀ (l : List α) (acc : σ × List ε), (∀ e ∈ acc.2, P e) →
      ∀ e ∈ (l.foldl (fun acc a => ((f acc.1 a).1, acc.2 ++ (f acc.1 a).2)) acc).2, P e
  | [], _, h => h
  | a :: l, acc, h => foldl_emits_val P f hf l _ fun e he => by
      rcases List.mem_append.mp he with he | he
      · exact h e he
      · exact hf _ _ e he

/-- Every emission of the node's AC is a vote of its own validator. -/
theorem emits_val (self : Fin sp.n) (s : (goldilocksNode sp ro).State)
    (Φ : (goldilocksNode sp ro).Frm) (t : Time) (c : (goldilocksNode sp ro).Call) :
    ∀ e ∈ ((goldilocksNode sp ro).step self s Φ t c).2, e.msg.val = self := by
  cases c with
  | tick =>
    change ∀ e ∈ (SA.acOnTick sp self s Φ t).2, _
    unfold SA.acOnTick
    dsimp only
    split_ifs <;> first | exact tryVote_val _ _ _ _ | simp
  | proposal => simp [ACInterface.step]
  | toFG => simp [ACInterface.step]
  | message m => exact tryVote_val _ _ _ _
  | block B => exact tryVote_val _ _ _ _
  | restart =>
    change ∀ e ∈ (SA.acRestart sp ro self s Φ t).2, _
    unfold SA.acRestart
    exact foldl_emits_val _ (fun A B => SA.acOnBlock sp self A Φ t B)
      (fun _ _ => tryVote_val _ _ _ _) _ _ (by simp)

/-- Every emission of an AC cut of a handler of `self` is a vote of `self`. -/
theorem emits_val_of_mem_exec (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (self : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time)
    (e : Event (goldilocksNode sp ro)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (h : Cut.ac ℓ ∈ (exec proposer dg self st t e).2) : ∀ m ∈ ℓ.emits, m.msg.val = self := by
  have key : ∀ {st st' : NodeState (goldilocksNode sp ro)} {cs},
      CutChain self t st cs st' → Cut.ac ℓ ∈ cs → ∀ m ∈ ℓ.emits, m.msg.val = self := by
    intro st st' cs hc
    induction hc with
    | nil => simp
    | @cons st₀ st₁ _ c cs hstep _ ih =>
      intro hm
      rcases List.mem_cons.mp hm with hm | hm
      · subst hm
        obtain ⟨-, he, -, -⟩ := hstep
        intro m hm'
        have hm'' : m ∈ ((goldilocksNode sp ro).step self st₀.ac ℓ.frame t ℓ.call).2 := by
          rw [he]; exact hm'
        exact emits_val (ro := ro) self st₀.ac ℓ.frame t ℓ.call m hm''
      · exact ih hm
  exact key (Compose.exec_is_cut_chain (P := sp.toParams) (A := goldilocksNode sp ro)
    proposer dg self st t e) h

/-- An FG block cut of a handler other than a tick's is its first cut. -/
theorem pos_of_block_cut (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp ro)) (t : Time) {e : Event (goldilocksNode sp ro)}
    (hne : ∀ x, e ≠ .tick x) {k : Nat} (hk : k < (exec proposer dg self st t e).2.length) {B acc}
    (h : (exec proposer dg self st t e).2[k] = .fg (.block B acc)) : k = 0 := by
  cases e with
  | tick x => exact absurd rfl (hne x)
  | block B' =>
    by_cases hf : sp.toParams.slotOf t < B'.slot
    · simp [exec, onBlock, hf] at hk
    · cases hfg : st.fg.onBlock B' with
      | none =>
        simp only [exec, onBlock, hf, hfg, ↓reduceIte, List.length_cons,
          List.length_nil] at hk
        omega
      | some fg' =>
        simp only [exec, onBlock, acCall, hf, hfg, ↓reduceIte, List.length_cons,
          List.length_nil] at hk h
        rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
        · rfl
        · simp at h
  | message m =>
    simp only [exec, onMessage, acCall] at hk h
    simp at hk; subst hk; simp at h
  | attestation a =>
    simp only [exec, onAttestation] at hk h
    simp at hk; subst hk; simp at h
  | restart =>
    simp only [exec, Node.restart, acCall] at hk h
    simp at hk; subst hk; simp at h

/-- A cut of a delivery is a cut of the handler of a canonical event, at its position. -/
theorem mem_deliverRecs_exec (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat) :
    ∀ (os : List (Wire sp.n)) (st : NodeState (goldilocksNode sp ro)) (sub : Nat)
      {r : CutRec sp ro}, r ∈ deliverRecs proposer dg hs self t i os st sub →
      ∃ o e st', o ∈ os ∧ canonEvent sp ro hs o = some e ∧
        ∃ k, ∃ hk : k < (exec proposer dg self st' t e).2.length,
          r.label = (exec proposer dg self st' t e).2[k] ∧ r.pos = k
  | [], _, _, _, hr => by simp [deliverRecs_nil] at hr
  | o :: os, st, sub, r, hr => by
    cases he : canonEvent sp ro hs o with
    | none =>
      rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ he] at hr
      obtain ⟨o', e, st', ho, h⟩ := mem_deliverRecs_exec proposer dg hs self t i os st _ hr
      exact ⟨o', e, st', List.mem_cons_of_mem _ ho, h⟩
    | some e =>
      rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ e he] at hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
        obtain ⟨-, -, -, hpos, hlab⟩ := getElem_groupRecs proposer dg self st t _ e k hk
        exact ⟨o, e, st, List.mem_cons_self, he, k,
          by rwa [length_groupRecs] at hk, hlab, hpos⟩
      · obtain ⟨o', e', st', ho, h⟩ := mem_deliverRecs_exec proposer dg hs self t i os _ _ hr
        exact ⟨o', e', st', List.mem_cons_of_mem _ ho, h⟩

/-- A canonical event is not a tick. -/
theorem canonEvent_ne_tick {hs : List (Header Info × Nat)} {o : Wire sp.n}
    {e : Event (goldilocksNode sp ro)} (he : canonEvent sp ro hs o = some e) :
    ∀ x, e ≠ .tick x := by
  rintro x rfl
  rcases canonEvent_eq_some he with ⟨_, h, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩ <;> cases h

/-- The outbox after one received object: its handler's emissions queued. -/
theorem processOne_outbox_eq (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (σ : State sp ro) (o : Wire sp.n) :
    (processOne hs σ o).outbox = σ.outbox ++
      (canonEvent sp ro hs o).elim [] fun e =>
        emitted (exec proposer dg σ.self σ.node σ.now e).2 := by
  unfold processOne
  cases he : canonEvent sp ro hs o with
  | none => simp
  | some e =>
    rcases canonEvent_eq_some he with ⟨B, rfl, -⟩ | ⟨v, rfl, -⟩ | ⟨a, rfl, -⟩
    all_goals
      dsimp only
      try rw [relayIf_eq]
      rfl

/-- Every body pending after delivery was already queued or emitted by one of its cuts. -/
theorem process_outbox_source (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (t : Time) (i : Nat) :
    ∀ (os : List (Wire sp.n)) (σ : State sp ro) (sub : Nat), σ.now = t →
      ∀ b ∈ (os.foldl (processOne hs) σ).outbox,
        b ∈ σ.outbox ∨ ∃ r ∈ deliverRecs proposer dg hs σ.self t i os σ.node sub,
          ∃ ℓ, r.label = .ac ℓ ∧ ∃ em ∈ ℓ.emits, b = .vote (encodeVote em.msg)
  | [], σ, _, _, b, hb => Or.inl hb
  | o :: os, σ, sub, ht, b, hb => by
    obtain ⟨_, _, _, hnow, hself, hnode⟩ := processOne_eq proposer dg hs σ o
    rcases process_outbox_source proposer dg hs t i os (processOne hs σ o) (sub + 1)
      (hnow.trans ht) b hb with hb | ⟨r, hr, ℓ, hl, em, hem, hb⟩
    · rw [processOne_outbox_eq proposer dg] at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact Or.inl hb
      · cases he : canonEvent sp ro hs o with
        | none => simp [he] at hb
        | some e =>
          simp only [he, Option.elim_some, emitted] at hb
          obtain ⟨c, hc, hb⟩ := List.mem_flatMap.mp hb
          cases c with
          | fg => simp at hb
          | ac ℓ =>
            obtain ⟨em, hem, rfl⟩ := List.mem_map.mp hb
            rw [ht] at hc
            obtain ⟨k, hk, hck⟩ := List.getElem_of_mem hc
            have hk' : k < (groupRecs proposer dg σ.self σ.node t (Nat.pair i sub) e).length :=
              by rwa [length_groupRecs]
            refine Or.inr ⟨(groupRecs proposer dg σ.self σ.node t (Nat.pair i sub) e)[k],
              ?_, ℓ, ?_, em, hem, rfl⟩
            · rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ e he]
              exact List.mem_append_left _ (List.getElem_mem hk')
            · exact (getElem_groupRecs _ _ _ _ _ _ _ k hk').2.2.2.2.trans hck
    · refine Or.inr ⟨r, ?_, ℓ, hl, em, hem, hb⟩
      rw [hself, hnode] at hr
      cases he : canonEvent sp ro hs o with
      | none =>
        rw [he] at hr
        rwa [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ he]
      | some e =>
        rw [he, Option.elim_some, ht] at hr
        rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ e he]
        exact List.mem_append_right _ hr

/-- A delivery queues each emission, preserving previously pending bodies. -/
theorem process_outbox (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (t : Time) (i : Nat) :
    ∀ (os : List (Wire sp.n)) (σ : State sp ro) (sub : Nat), σ.now = t →
      (∃ L, (os.foldl (processOne hs) σ).outbox = σ.outbox ++ L) ∧
      ∀ r ∈ deliverRecs proposer dg hs σ.self t i os σ.node sub, ∀ ℓ, r.label = .ac ℓ →
        ∀ m ∈ ℓ.emits, Body.vote (encodeVote m.msg) ∈ (os.foldl (processOne hs) σ).outbox ∧
          m.msg.val = σ.self
  | [], σ, sub, ht => ⟨⟨[], by simp⟩, by simp [deliverRecs_nil]⟩
  | o :: os, σ, sub, ht => by
    obtain ⟨-, -, -, hnow₁, hself₁, hnode₁⟩ := processOne_eq proposer dg hs σ o
    obtain ⟨⟨L, hL⟩, hrec⟩ :=
      process_outbox proposer dg hs t i os (processOne hs σ o) (sub + 1) (hnow₁.trans ht)
    rw [List.foldl_cons]
    have hkeep : ∀ x ∈ (processOne hs σ o).outbox,
        x ∈ (os.foldl (processOne hs) (processOne hs σ o)).outbox := fun x hx => by
      rw [hL]; exact List.mem_append_left _ hx
    refine ⟨⟨_, by rw [hL, processOne_outbox_eq proposer dg, List.append_assoc]⟩,
      fun r hr ℓ hl m hm => ?_⟩
    rw [hself₁, hnode₁] at hrec
    cases he : canonEvent sp ro hs o with
    | none =>
      rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ he] at hr
      rw [he] at hrec
      simpa [hself₁] using hrec r hr ℓ hl m hm
    | some e =>
      rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ e he] at hr
      rw [he, Option.elim_some, ht] at hrec
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
        obtain ⟨-, -, -, -, hlab⟩ := getElem_groupRecs proposer dg σ.self σ.node t _ e k hk
        have hmem : Cut.ac ℓ ∈ (exec proposer dg σ.self σ.node t e).2 := by
          rw [← hl, hlab]; exact List.getElem_mem _
        refine ⟨hkeep _ ?_, emits_val_of_mem_exec proposer dg σ.self σ.node t e hmem m hm⟩
        rw [processOne_outbox_eq proposer dg, he, Option.elim_some, ht]
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hmem, by simpa using ⟨m, hm, rfl⟩⟩)
      · simpa [hself₁] using hrec r hr ℓ hl m hm

end

section

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

end

end Consensus.Goldilocks.Refinement

end
