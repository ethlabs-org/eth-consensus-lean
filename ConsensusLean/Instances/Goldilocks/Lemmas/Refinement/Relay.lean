module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Cuts
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
* **A delivery's relay queue** (`process_relay`). The shape's `process` of a delivery, from a
  state at the delivery's time, keeps the clock and the own index, only grows the relay queue,
  and queues the canonical object of every accepted block, every vote the pool holds after its
  `ac_on_message` call, and every attestation among the delivery's cuts (`deliverRecs`).
* **The engine's state across an event** (`stateAt_succ_deliver`, `_restart`, `_tick`,
  `stateBefore_succ_of_ne`), what the shape's steps keep (`propose_keeps`, `nodeTick_keeps`,
  `poll_keeps`, `recordOwn_keeps`), the compiled duties (`act_preserves`, `tick_preserves`), and
  two invariants: the own index is the own key (`stateAt_self`) and the relay queue is seen
  (`stateAt_relay_seen`).
* **Relaying** (`relayedFrom_of_deliver`). An object queued at a delivery stays queued until the
  node's next tick (`relayBuf_persist`), which is at its first awake time after the delivery, and
  whose gossip releases the relay wrapper of the queue (`tick_relays`). -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload)

/-! ## Canonical objects -/

section

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

private theorem encodeAtt_of_decodeAtt {n : Nat} {w : WireAtt} {a : FG.Att n}
    (h : decodeAtt n w = some a) : encodeAtt a = w := by
  unfold decodeAtt at h
  split at h
  · cases h; rfl
  · cases h

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
  simp only [encodeInfo, map_of_mapM (fun _ _ => encodeAtt_of_decodeAtt) ha,
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
      obtain ⟨⟨hpos, hpar, rfl, -, -⟩, rfl⟩ := h
      obtain ⟨par, pos, input, info⟩ := hd
      simp only at hpos hpar hdec
      subst hpos
      have hinfo := encodeInfo_of_decodeInfo hdec
      simp only [blockObj, headerOf, blockOf, hinfo]
      congr
      cases par with
      | root => simp [parentRoot, parentRef]
      | digest r =>
        have : r ≠ sp.genesisRoot := fun e => hpar (by rw [e])
        simp [parentRoot, parentRef, this]
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
      simp only [attObj, encodeAtt_of_decodeAtt hw, hk.1]
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

/-! ## Processing a delivery -/

/-- A cut of a group: the handler's cut `k` and its post-state. -/
private theorem mem_groupRecs_label {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {self : Fin sp.n} {st : NodeState (goldilocksNode sp ro)} {t : Time} {id : Nat}
    {e : Event (goldilocksNode sp ro)} {r : CutRec sp ro}
    (hr : r ∈ groupRecs dg self st t id e) :
    ∃ k, ∃ hk : k < (exec dg self st t e).2.length, r.label = (exec dg self st t e).2[k] ∧
      r.post = (cutPosts self t (exec dg self st t e).2 st)[k]'(by
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
private theorem processOne_eq (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (σ : State sp ro) (o : Wire sp.n) :
    ∃ L, (processOne hs σ o).relayBuf = σ.relayBuf ++ L ∧ (∀ x ∈ L, x = o) ∧
      (processOne hs σ o).now = σ.now ∧ (processOne hs σ o).self = σ.self ∧
      (processOne hs σ o).node =
        ((canonEvent sp ro hs o).elim σ.node fun e => (exec dg σ.self σ.node σ.now e).1) := by
  unfold processOne
  cases he : canonEvent sp ro hs o with
  | none => exact ⟨[], by simp, by simp, rfl, rfl, rfl⟩
  | some e =>
    rcases canonEvent_eq_some he with ⟨B, rfl, -⟩ | ⟨v, rfl, -⟩ | ⟨a, rfl, -⟩
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

private theorem processOne_message {hs : List (Header Info × Nat)} {σ : State sp ro}
    {o : Wire sp.n} {v : Vote sp.n} (he : canonEvent sp ro hs o = some (.message v))
    (h : v ∈ (Node.onMessage σ.self σ.node σ.now v).1.ac.pool v.slot) :
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
private theorem group_relay (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    {hs : List (Header Info × Nat)} {σ : State sp ro} {t : Time} (ht : σ.now = t) {id : Nat}
    {o : Wire sp.n} {e : Event (goldilocksNode sp ro)} (he : canonEvent sp ro hs o = some e)
    {r : CutRec sp ro} (hr : r ∈ groupRecs dg σ.self σ.node t id e) :
    (∀ B, r.label = .fg (.block B true) → blockObj sp B = o ∧ o ∈ (processOne hs σ o).relayBuf) ∧
    (∀ ℓ m, r.label = .ac ℓ → ℓ.call = .message m → m ∈ r.post.ac.pool m.slot →
      voteObj m = o ∧ o ∈ (processOne hs σ o).relayBuf) ∧
    (∀ a, r.label = .fg (.attestation a) → attObj a = o ∧ o ∈ (processOne hs σ o).relayBuf) := by
  obtain ⟨k, hk, hlab, hpost⟩ := mem_groupRecs_label hr
  subst ht
  rcases canonEvent_eq_some he with ⟨B, rfl, rfl⟩ | ⟨v, rfl, rfl⟩ | ⟨a, rfl, rfl⟩
  · -- a block: `[fg_on_block(B) refused]` or `[fg_on_block(B) accepted, ac_on_block(B)]`
    have hmem : r.label ∈ (exec dg σ.self σ.node σ.now (.block B)).2 :=
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
    refine ⟨fun B h => ?_, fun ℓ m h hc hp => ⟨?_, processOne_message he ?_⟩, fun a h => ?_⟩
    · simp [hlab, exec, onMessage, acCall] at h
    · simp only [hlab, exec, onMessage, acCall, List.getElem_cons_zero, Cut.ac.injEq] at h
      subst h
      cases hc
      rfl
    · simp only [hlab, exec, onMessage, acCall, List.getElem_cons_zero, Cut.ac.injEq] at h
      subst h
      cases hc
      simpa [hpost, exec, onMessage, acCall, cutPosts_cons, cutPost_ac] using hp
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
theorem process_relay (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (t : Time) (i : Nat) :
    ∀ (os : List (Wire sp.n)) (σ : State sp ro) (sub : Nat), σ.now = t →
      (∃ L, (os.foldl (processOne hs) σ).relayBuf = σ.relayBuf ++ L ∧ ∀ x ∈ L, x ∈ os) ∧
      (os.foldl (processOne hs) σ).now = t ∧ (os.foldl (processOne hs) σ).self = σ.self ∧
      ∀ r ∈ deliverRecs dg hs σ.self t i os σ.node sub,
        (∀ B, r.label = .fg (.block B true) →
          blockObj sp B ∈ (os.foldl (processOne hs) σ).relayBuf) ∧
        (∀ ℓ m, r.label = .ac ℓ → ℓ.call = .message m → m ∈ r.post.ac.pool m.slot →
          voteObj m ∈ (os.foldl (processOne hs) σ).relayBuf) ∧
        (∀ a, r.label = .fg (.attestation a) →
          attObj a ∈ (os.foldl (processOne hs) σ).relayBuf)
  | [], σ, sub, ht => ⟨⟨[], by simp, by simp⟩, ht, rfl, by simp [deliverRecs_nil]⟩
  | o :: os, σ, sub, ht => by
    obtain ⟨L₁, hL₁, hL₁o, hnow₁, hself₁, hnode₁⟩ := processOne_eq dg hs σ o
    obtain ⟨⟨L, hL, hLos⟩, hnow, hself, hrec⟩ :=
      process_relay dg hs t i os (processOne hs σ o) (sub + 1) (hnow₁.trans ht)
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
      rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ he] at hr
      rw [he] at hrec
      exact hrec r hr
    | some e =>
      rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ e he] at hr
      rw [he, Option.elim_some, ht] at hrec
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨h1, h2, h3⟩ := group_relay dg ht he hr
        refine ⟨fun B h => ?_, fun ℓ m h hc hp => ?_, fun a h => ?_⟩
        · obtain ⟨rfl, ho⟩ := h1 B h; exact hkeep _ ho
        · obtain ⟨rfl, ho⟩ := h2 ℓ m h hc hp; exact hkeep _ ho
        · obtain ⟨rfl, ho⟩ := h3 a h; exact hkeep _ ho
      · exact hrec r hr


end

/-! ## The engine's node state across an event -/

section

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- An engine delivery runs the shape's `process` on the delivered object. -/
theorem stateAt_succ_deliver {i : Nat} {v : V}
    {o : (Model.protoOf (compiled (family S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) :
    stateAt S rho hn v (i + 1) =
      process (stateAt S rho hn v i) o (Model.digests rho.hash o) := by
  simp only [stateAt, rho.stateBefore_succ he, Model.Run.step, Function.update_self]
  rfl

/-- An engine restart runs the shape's `restore` with the own key. -/
theorem stateAt_succ_restart {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.restart v t)) :
    stateAt S rho hn v (i + 1) = restore (rho.ownKey v) (stateAt S rho hn v i) t := by
  simp only [stateAt, rho.stateBefore_succ he, Model.Run.step, Function.update_self]
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
    Model.Obj.Contains o x := by
  unfold delivered at h
  split at h
  · exact .step h (.refl x)
  · rw [List.mem_singleton] at h
    subst h
    exact .refl _

/-- The slot proposal keeps the relay queue and the own index. -/
theorem propose_keeps (st : State sp ro) (s : Slot) :
    (propose st s).1.relayBuf = st.relayBuf ∧ (propose st s).1.self = st.self := by
  unfold propose
  split_ifs
  · dsimp only
    split <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

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
    exact hprop _ _ h
  | act s k => exact k.elim
  | pollPropose t =>
    simp only [Model.protoOf, compiled, compile, withMempool, family, hn, ↓reduceDIte]
    exact hnt _ h
  | poll t =>
    simp only [Model.protoOf, compiled, compile, withMempool, family, hn, ↓reduceDIte]
    exact hpoll _ (t : Time) h

omit [DecidableEq V] in
/-- The compiled clock sets the Goldilocks clock. -/
theorem clock_eq (st : (Model.protoOf (compiled (family S)) E).State) (t : Time)
    (xs : List Tx) :
    ((Model.protoOf (compiled (family S)) E).clock st t xs).1 hn = { st.1 hn with now := t } :=
  rfl

omit [DecidableEq V] in
/-- The compiled `recordOwn` is the shape's. -/
theorem recordOwn_eq (st : (Model.protoOf (compiled (family S)) E).State)
    (o : (Model.protoOf (compiled (family S)) E).Object) (hs) :
    ((Model.protoOf (compiled (family S)) E).recordOwn st o hs).1 hn =
      recordOwn (st.1 hn) o hs :=
  rfl

end


/-! ## Invariants of the engine's Goldilocks state -/

section

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- An engine tick of the node: the Goldilocks state after the tick. -/
theorem stateAt_succ_tick {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) :
    stateAt S rho hn v (i + 1) = (rho.tick (rho.stateBefore i v) v t).1.st.1 hn := by
  simp only [stateAt, rho.stateBefore_succ he, Model.Run.step, Function.update_self]

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
  | 0 => rfl
  | i + 1 => by
    have ih := stateAt_self v i
    cases he : rho.events[i]? with
    | none =>
      simp only [stateAt, stateBefore_succ_none S rho he] at ih ⊢
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
            (fun st o hs h => (recordOwn_keeps st o hs).2.trans h) _ w t ih
        | deliver w o t =>
          simp only [Model.Event.node] at hne
          subst hne
          rw [stateAt_succ_deliver S rho hn he]
          exact (process_relay (digestOf S rho) _ _ i _ _ 0 rfl).2.2.1.trans ih
        | restart w t =>
          simp only [Model.Event.node] at hne
          subst hne
          rw [stateAt_succ_restart S rho hn he]
          rfl
      · simp only [stateAt, stateBefore_succ_of_ne S rho he hne] at ih ⊢
        exact ih


/-- **The relay queue is seen.** Every object queued for relay by node `v` is in the closure of
what `v` has seen. -/
theorem stateAt_relay_seen (v : V) : ∀ i, ∀ x ∈ (stateAt S rho hn v i).relayBuf,
    x ∈ Model.closure (rho.stateBefore i v).seen
  | 0 => fun x hx => absurd hx List.not_mem_nil
  | i + 1 => by
    have ih := stateAt_relay_seen v i
    cases he : rho.events[i]? with
    | none =>
      simp only [stateAt, stateBefore_succ_none S rho he] at ih ⊢
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
            _ w t ih x hx
          rw [rho.stateBefore_succ he]
          simp only [Model.Run.step, Function.update_self, Model.Run.tick_seen,
            Model.closure_append]
          exact List.mem_append_left _ hQ
        | deliver w o t =>
          simp only [Model.Event.node] at hne
          subst hne
          intro x hx
          rw [stateAt_succ_deliver S rho hn he] at hx
          obtain ⟨⟨L, hL, hLos⟩, -⟩ := process_relay (digestOf S rho) (Model.digests rho.hash o)
            _ i (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn w i) 0 rfl
          rw [rho.stateBefore_succ he]
          simp only [Model.Run.step, Function.update_self, Model.closure_append]
          unfold process at hx
          rw [hL] at hx
          rcases List.mem_append.mp hx with hx | hx
          · exact List.mem_append_left _ (ih x hx)
          · refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, List.mem_singleton_self _, ?_⟩)
            exact contains_of_mem_delivered (hLos x hx)
        | restart w t =>
          simp only [Model.Event.node] at hne
          subst hne
          rw [stateAt_succ_restart S rho hn he]
          rw [rho.stateBefore_succ he]
          simp only [Model.Run.step, Function.update_self]
          exact ih
      · simp only [stateAt, stateBefore_succ_of_ne S rho he hne] at ih ⊢
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

/-- A tick of an awake honest node at a time after a delivery to it, within the horizon, comes
after the delivery. -/
theorem tick_after_deliver (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {o : (Model.protoOf (compiled (family S)) E).Object} {t u : Time}
    (he : rho.events[i]? = some (.deliver v o t)) (htu : t < u) (hu : u ≤ rho.horizon)
    (hw : E.awake v u = true) : ∃ j, i < j ∧ rho.events[j]? = some (.tick v u) := by
  have hm := List.mem_of_getElem? he
  have ht0 := (hv.in_horizon _ hm).1
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp
    (hv.tick_total v (hv.honest_only _ hm) u (by simp only [Model.Event.time] at ht0; linarith)
      hu hw)
  refine ⟨j, ?_, hj⟩
  rcases lt_trichotomy j i with h | rfl | h
  · rcases keyLe_of_index_lt S rho hv hj he h with h' | h'
    · have : u < t := h'; linarith
    · have : u = t := h'.1; linarith
  · rw [he] at hj; cases hj
  · exact h

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
    | base => intro _; simp [lastClock, hit]
    | succ m hm1 ih =>
      intro hmi
      have ihm := ih (by omega)
      cases hem : rho.events[m]? with
      | none => simpa [lastClock, hem] using ihm
      | some e =>
        have h1 := keyLe_of_index_lt S rho hv hit hem (by omega)
        have h2 := keyLe_of_index_lt S rho hv hem he (by omega)
        cases e with
        | tick v' t' =>
          simp only [lastClock, hem]
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
          simp only [lastClock, hem]
          split_ifs with hvv
          · exfalso
            rcases h1 with h1 | h1
            · rcases h2 with h2 | h2
              · simp only [Model.Event.time] at h1 h2; linarith
              · simp only [Model.Event.time] at h1 h2; linarith [h2.1]
            · exact absurd h1.2 (by simp [Model.Event.phase])
          · exact ihm
        | deliver v' o' t' => simpa [lastClock, hem] using ihm
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
    rw [rho.runDuties_cons, runDuties_seen v ds, rho.dutyStep_eq, Model.releaseAll_seen]
    simp

/-- **The gossip relays the queue.** An awake tick of node `v` releases the unsigned relay
wrapper of its relay queue, which carries everything queued before the tick. -/
theorem tick_relays {j : Nat} {v : V} {t : Time} (he : rho.events[j]? = some (.tick v t))
    (hw : E.awake v t = true) {x : Wire (S.params (pubOf E) hn).n}
    (hx : x ∈ (stateAt S rho hn v j).relayBuf) :
    ∃ cs, x ∈ cs ∧ Model.Obj.mk .none (.data .relay) cs ∈ rho.releasesAt j := by
  simp only [Model.Run.releasesAt, he]
  rw [rho.tick_of_awake _ v t hw]
  set nd := rho.stateBefore j v
  set R := rho.runDuties v ⟨(Model.protoOf (compiled (family S)) E).clock nd.st t
    (Model.mempool rho.inbox v t), nd.seen⟩ ((Model.protoOf (compiled (family S)) E).duties t)
  -- the queue after the duties keeps `x` and holds only seen objects
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
      hx
  have hseen : ∀ y ∈ (R.1.st.1 hn).relayBuf, y ∈ Model.closure R.1.seen := by
    have hQ : ∀ y ∈ (R.1.st.1 hn).relayBuf, y ∈ Model.closure nd.seen := rho.runDuties_invariant
      (fun s => ∀ y ∈ (s.1 hn).relayBuf, y ∈ Model.closure nd.seen) v _ _
      (fun s d _ hs => act_preserves S hn (fun st => ∀ y ∈ st.relayBuf, y ∈ Model.closure nd.seen)
        (fun st s h => by rw [(propose_keeps st s).1]; exact h)
        (fun st h => by rw [(nodeTick_keeps st).1]; exact h)
        (fun st t h => by rw [(poll_keeps st t).1]; exact h) s d hs)
      (fun s o hs _ hq => by
        change ∀ y ∈ (recordOwn (s.1 hn) o hs).relayBuf, _
        rcases (recordOwn_keeps (s.1 hn) o hs).1 with h' | h' <;> rw [h']
        · exact hq
        · simp)
      (stateAt_relay_seen S rho hn v j)
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
  · rename_i h; exact absurd hc h

/-- Between ticks of the node the relay queue only grows. -/
theorem relayBuf_persist {i : Nat} {v : V} {x : Wire (S.params (pubOf E) hn).n}
    (hx : x ∈ (stateAt S rho hn v i).relayBuf) :
    ∀ m, i ≤ m → (∀ l, i ≤ l → l < m → ∀ t, rho.events[l]? ≠ some (.tick v t)) →
      x ∈ (stateAt S rho hn v m).relayBuf := by
  intro m him
  induction m, him using Nat.le_induction with
  | base => exact fun _ => hx
  | succ m him ih =>
    intro hno
    have hm := ih fun l h1 h2 => hno l h1 (by omega)
    cases he : rho.events[m]? with
    | none =>
      simp only [stateAt, stateBefore_succ_none S rho he] at hm ⊢
      exact hm
    | some e =>
      by_cases hne : e.node = v
      · cases e with
        | tick w t =>
          simp only [Model.Event.node] at hne
          subst hne
          exact absurd he (hno m him (by omega) t)
        | deliver w o t =>
          simp only [Model.Event.node] at hne
          subst hne
          rw [stateAt_succ_deliver S rho hn he]
          obtain ⟨⟨L, hL, -⟩, -⟩ := process_relay (digestOf S rho) (Model.digests rho.hash o)
            _ m (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn w m) 0 rfl
          unfold process
          rw [hL]
          exact List.mem_append_left _ hm
        | restart w t =>
          simp only [Model.Event.node] at hne
          subst hne
          rw [stateAt_succ_restart S rho hn he]
          exact hm
      · simp only [stateAt, stateBefore_succ_of_ne S rho he hne] at hm ⊢
        exact hm

open Classical in
/-- **An object queued at a delivery is relayed** at the node's first awake time after the
delivery, if it has one within the horizon (`RelayedFrom`). -/
theorem relayedFrom_of_deliver (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {o : (Model.protoOf (compiled (family S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) {x : Wire (S.params (pubOf E) hn).n}
    (hx : x ∈ (stateAt S rho hn v (i + 1)).relayBuf) : RelayedFrom S rho v x t := by
  by_cases hex : ∃ j, i < j ∧ ∃ t', rho.events[j]? = some (.tick v t')
  · have hj := Nat.find_spec hex
    obtain ⟨hij, t', he'⟩ := hj
    have hmin := fun l (hl : l < Nat.find hex) => Nat.find_min hex hl
    set j := Nat.find hex
    have hw : E.awake v t' = true := hv.tick_awake v t' (List.mem_of_getElem? he')
    have hxj : x ∈ (stateAt S rho hn v j).relayBuf :=
      relayBuf_persist S rho hn hx j (by omega) fun l h1 h2 t₁ hl =>
        hmin l h2 ⟨by omega, t₁, hl⟩
    obtain ⟨cs, hxcs, hrel⟩ := tick_relays S rho hn he' hw hxj
    have htt' : t < t' := by
      rcases keyLe_of_index_lt S rho hv he he' hij with h | h
      · exact h
      · exact absurd h.2 (by simp [Model.Event.phase])
    have hh' : t' ≤ rho.horizon := (hv.in_horizon _ (List.mem_of_getElem? he')).2
    refine Or.inl ⟨t', cs, htt', hxcs, ⟨j, he', hrel⟩, fun u hu1 hu2 => ?_⟩
    by_contra hwu
    obtain ⟨ju, hiju, heu⟩ := tick_after_deliver S rho hv he hu1 (by linarith)
      (by simpa using hwu)
    rcases lt_trichotomy ju j with h | rfl | h
    · exact hmin ju h ⟨hiju, u, heu⟩
    · rw [he'] at heu; cases heu; exact lt_irrefl _ hu2
    · rcases keyLe_of_index_lt S rho hv he' heu h with h' | h'
      · have : t' < u := h'; linarith
      · have : t' = u := h'.1; linarith
  · refine Or.inr fun u hu1 hu2 => ?_
    by_contra hwu
    obtain ⟨ju, hiju, heu⟩ := tick_after_deliver S rho hv he hu1 hu2 (by simpa using hwu)
    exact hex ⟨ju, hiju, u, heu⟩

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
      obtain ⟨-, -, -, hpos, hlab⟩ := getElem_groupRecs _ _ _ _ _ _ k hk
      obtain ⟨ℓ₀, pc, uc, hℓ₀, hcs, hpc, ⟨ℓ₁, hℓ₁, huc⟩⟩ :=
        Compose.tick_order (digestOf S rho) (rho.ownKey v) (stateAt S rho hn v i).node t
          (encodeTxs (Model.mempool rho.inbox v t))
      have hcs' : (exec (digestOf S rho) (rho.ownKey v) (stateAt S rho hn v i).node t
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
    obtain ⟨-, -, -, hpos, hlab⟩ := getElem_groupRecs _ _ _ _ _ _ k hk
    have hk1 : k = 0 :=
      Nat.lt_one_iff.mp (lt_of_lt_of_eq hk ((length_groupRecs _ _ _ _ _ _).trans rfl))
    subst hk1
    simp only [exec, Node.restart, acCall, List.getElem_cons_zero] at hlab
    rcases h with ⟨-, ℓ, hl⟩ | ⟨ℓ, m, hl, hc⟩
    · rw [hlab] at hl; cases hl
    · rw [hlab] at hl; cases hl; cases hc

end


end Consensus.Goldilocks.Refinement

end
