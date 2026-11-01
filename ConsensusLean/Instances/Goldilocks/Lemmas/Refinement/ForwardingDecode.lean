module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ForwardingInvariant
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.PublicationProvenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Provenance

public section

/-! # Forwarding decoder correspondence

Relate the durable wrapper's decoded child to the actual held block, rather than
identifying blocks by equal roots without a store correspondence proof.
-/

namespace Consensus.Goldilocks.Refinement

open Shape Blocks
open Consensus.Model

/-- Every successfully decoded durable wrapper names the block actually held at its map key.
Existence of a decoding is supplied separately by `WrappersDecoded`. -/
structure WrappersHeld {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (tables : Wire sp.n → List (Header Info × Nat)) (st : State sp ro) : Prop where
  held : ∀ root o t p B, st.wrappers root = some o →
    decodeForward sp (tables o) o = some (st.self, t, p, B) →
      st.node.fg.blocks root = some B

/-- Empty wrapper maps have no correspondence obligations. -/
theorem wrappersHeld_empty {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (tables : Wire sp.n → List (Header Info × Nat)) (st : State sp ro)
    (hm : ∀ root, st.wrappers root = none) : WrappersHeld tables st := by
  constructor
  intro root o t p B ho _
  rw [hm root] at ho
  cases ho

/-- State transitions which leave both maps unchanged preserve their correspondence. -/
theorem WrappersHeld.preserve {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {tables : Wire sp.n → List (Header Info × Nat)} {st st' : State sp ro}
    (h : WrappersHeld tables st) (hs : st'.self = st.self)
    (hw : st'.wrappers = st.wrappers) (hb : st'.node.fg.blocks = st.node.fg.blocks) :
    WrappersHeld tables st' := by
  constructor
  intro root o t p B ho hd
  rw [hw] at ho
  rw [hs] at hd
  rw [hb]
  exact h.held root o t p B ho hd

/-- Synchronized insertion of an accepted block and its decoded wrapper preserves
correspondence, including all other roots. No hash-injectivity assumption is needed. -/
theorem WrappersHeld.insert {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {tables : Wire sp.n → List (Header Info × Nat)} {st st' : State sp ro}
    (h : WrappersHeld tables st) (B : Blk sp) (o : Wire sp.n) (t : Time)
    (p : Option (Wire sp.n)) (hs : st'.self = st.self)
    (hw : st'.wrappers = Function.update st.wrappers B.root (some o))
    (hb : st'.node.fg.blocks = Function.update st.node.fg.blocks B.root (some B))
    (hd : decodeForward sp (tables o) o = some (st.self, t, p, B)) :
    WrappersHeld tables st' := by
  constructor
  intro root q u parent A hq hdec
  rw [hw] at hq
  rw [hs] at hdec
  rw [hb]
  by_cases hr : root = B.root
  · subst root
    simp only [Function.update_self, Option.some.injEq] at hq
    subst q
    have he := Option.some.inj (hd.symm.trans hdec)
    have hBA : B = A := congrArg (fun z => z.2.2.2) he
    simp only [Function.update_self, hBA]
  · rw [Function.update_of_ne hr] at hq ⊢
    exact h.held root q u parent A hq hdec

/-- The selected decoded parent is strictly earlier in slot than an accepted child.
The actual held-block correspondence, not equality of roots alone, supplies this fact. -/
theorem WrappersHeld.parent_slot_lt {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {tables : Wire sp.n → List (Header Info × Nat)} {st : State sp ro}
    (h : WrappersHeld tables st)
    (hreach : st.node.fg.Reachable (goldilocksNode sp ro).genesisPayload)
    (B : Blk sp) (fg' : Store sp.toParams (SA.Payload sp.n))
    (haccept : st.node.fg.onBlock B = some fg')
    (root : Nat) (hr : B.parent = some root)
    (parent : Wire sp.n) (pt : Time) (pp : Option (Wire sp.n)) (A : Blk sp)
    (hp : st.wrappers root = some parent)
    (hd : decodeForward sp (tables parent) parent = some (st.self, pt, pp, A)) :
    A.slot < B.slot := by
  have hheld := h.held root parent pt pp A hp hd
  have hroot := hreach.blocks_root hheld
  have hA : A ∈ st.node.fg.tree := by
    change st.node.fg.blocks A.root = some A
    rwa [hroot]
  have hreach' := hreach.tail (Or.inl ⟨B, haccept⟩)
  have htree := (Store.tree_grows sp.toParams _ _ _ hreach).1 B fg' haccept
  have hA' : A ∈ fg'.tree := by rw [htree]; exact Set.mem_insert_of_mem _ hA
  have hB' : B ∈ fg'.tree := by rw [htree]; exact Set.mem_insert _ _
  exact (Store.accepted_tree sp.toParams _ _ _ hreach').2.1.2 A hA' B hB'
    (hr.trans (congrArg some hroot.symm))

/-- The actual accepting handler updates held blocks and durable wrappers together.
The selected wrapper's decoding is supplied by the decoder preservation proof. -/
theorem WrappersHeld.accept {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {tables : Wire sp.n → List (Header Info × Nat)} {st : State sp ro}
    (h : WrappersHeld tables st) (B : Blk sp) (root : Nat) (p : Option (Wire sp.n))
    (hr : B.parent = some root)
    (hp : (if root = sp.genesisRoot then some none else
      (st.wrappers root).map some) = some p)
    (ha : .fg (.block B true) ∈ (Node.onBlock st.self st.node st.now B).2)
    (hd : decodeForward sp (tables (forwardObj sp st.self st.now p B))
      (forwardObj sp st.self st.now p B) = some (st.self, st.now, p, B)) :
    WrappersHeld tables (apply st (Node.onBlock st.self st.node st.now B)) := by
  unfold Node.onBlock at ha ⊢
  split at ha
  · simp at ha
  · rename_i ht
    simp only [ht, ↓reduceIte]
    split at ha
    · simp at ha
    · rename_i fg' hfg
      rw [hfg]
      have hb : fg'.blocks = Function.update st.node.fg.blocks B.root (some B) := by
        obtain ⟨r, σ, _, _, _, _, _, hstore⟩ := Store.onBlock_eq_some hfg
        rw [hstore]
        obtain ⟨atts, he⟩ := Store.addAtts_eq _ B.fgPayload
        rw [he]
        exact (Store.updateFinality_spec _ σ).1
      apply h.insert B (forwardObj sp st.self st.now p B) st.now p
      · exact apply_self _ _
      · exact (queueAccepted_of_parent st B root p hr hp).1
      · exact hb
      · exact hd

/-- Accepted children cannot be stamped before their slot starts. -/
theorem accepted_slotTime_le {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (B : Blk sp)
    (ht : 0 ≤ st.now)
    (ha : .fg (.block B true) ∈ (Node.onBlock st.self st.node st.now B).2) :
    sp.toParams.slotTime B.slot ≤ st.now := by
  have hs : B.slot ≤ sp.toParams.slotOf st.now := by
    unfold Node.onBlock at ha
    split at ha
    · simp at ha
    · exact Nat.le_of_not_lt ‹¬ _›
  exact (sp.toParams.slotTime_strictMono.monotone hs).trans
    (Nat.findGreatest_spec (P := fun s => sp.toParams.slotTime s ≤ st.now)
      (Nat.zero_le _) (by rw [sp.toParams.slotTime_zero]; exact ht))

/-- An accepting block handler queues a decoded wrapper from the actual held parent.
Only child wire validity and time bounds remain local inputs; parent slot order follows
from the reachable FG store and durable-map correspondence. -/
theorem decoded_acceptance_enqueue {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (st : State (S.params (pubOf E) hn) (S.ro _))
    (hdec : WrappersDecoded (digests (P := protoOf (compiled (family S)) E) rho.hash) st)
    (hheld : WrappersHeld (digests (P := protoOf (compiled (family S)) E) rho.hash) st)
    (hcover : WrappersCover st)
    (hreach : st.node.fg.Reachable (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload)
    (B : Blk (S.params (pubOf E) hn))
    (ha : .fg (.block B true) ∈ (Node.onBlock st.self st.node st.now B).2)
    (hb : decodeBlock (S.params (pubOf E) hn) (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B)
    (ht : 0 ≤ st.now) :
    WrappersDecoded (digests (P := protoOf (compiled (family S)) E) rho.hash)
      (queueAccepted st B) := by
  obtain ⟨root, p, hr, hp, _, _⟩ := onBlock_queues_acceptance_parent st B hcover ha
  have hfg : ∃ fg', st.node.fg.onBlock B = some fg' := by
    unfold Node.onBlock at ha
    split at ha
    · simp at ha
    · split at ha
      · simp at ha
      · exact ⟨_, ‹st.node.fg.onBlock B = some _›⟩
  obtain ⟨fg', hfg⟩ := hfg
  exact hdec.engine_enqueue S rho hn st B root p hr hp hb ht
    (accepted_slotTime_le st B ht ha)
    (fun parent pt pp A hp hd => hheld.parent_slot_lt hreach B fg' hfg root hr
      parent pt pp A hp hd)

/-- Transfer the queue decoder invariant to the full accepting handler state. -/
theorem WrappersDecoded.accept {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {tables : Wire sp.n → List (Header Info × Nat)} (st : State sp ro) (B : Blk sp)
    (h : WrappersDecoded tables (queueAccepted st B))
    (hcover : WrappersCover st)
    (ha : .fg (.block B true) ∈ (Node.onBlock st.self st.node st.now B).2) :
    WrappersDecoded tables (apply st (Node.onBlock st.self st.node st.now B)) := by
  obtain ⟨root, p, hr, hp, hm, hq⟩ := onBlock_queues_acceptance_parent st B hcover ha
  have hs : (queueAccepted st B).self = st.self := by simp [queueAccepted, hr, hp]
  exact h.mono ((apply_self _ _).trans hs.symm)
    (hm.trans (queueAccepted_of_parent st B root p hr hp).1.symm)
    (hq.trans (queueAccepted_of_parent st B root p hr hp).2.symm)
    (by rw [apply_now, queueAccepted_now])

/-- A canonical child decoded during a receipt also decodes under its own digest table.
This discharges child wire validity for delivery acceptances without any payload premise. -/
theorem received_child_decodes {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (receipt o : Wire (Fintype.card V)) (B : Blk (S.params (pubOf E) hn))
    (hc : Obj.Contains receipt o)
    (hd : decodeBlock (S.params (pubOf E) hn) (digests rho.hash receipt) o = some B) :
    decodeBlock (S.params (pubOf E) hn) (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B := by
  obtain rfl := eq_blockObj_of_decodeBlock hd
  apply decodeBlock_transport hd
  rw [rootOf_digests_blockObj,
    rootOf_digests_of_mem S rho _ _ (List.mem_filterMap.mpr ⟨_, hc, rfl⟩)]

/-- Own proposals obtain wire validity from reachable node execution, rather than from
a receipt guard (which own-block recording does not run). -/
theorem own_proposal_decodes {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (proposer : Nat → Fin (Fintype.card V)) (self : Fin (Fintype.card V))
    (cfg cfg' : Node.Config (goldilocksNode (S.params (pubOf E) hn) (S.ro _)))
    (t : Time) (x : Nat)
    (hq : (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).Requirements)
    (hg : ((S.params (pubOf E) hn).toParams.genesisBlock
      (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload).RootOk (digestOf S rho))
    (hr : Node.Reachable proposer (digestOf S rho) self cfg)
    (hs : Node.Step proposer (digestOf S rho) self cfg (.tick x) t cfg')
    (hp : Node.Proposes (P := (S.params (pubOf E) hn).toParams) proposer self t) :
    let r := Node.acProposal
      (Node.tickStep proposer (digestOf S rho) self cfg.st t x .acTick).1 t
    ∀ d p, r.2.2 = some (d, p) →
      let B := Node.mkBlock (digestOf S rho) self r.1.fg t x d.head p
      decodeBlock (S.params (pubOf E) hn) (digests rho.hash (blockObj _ B))
        (blockObj _ B) = some B := by
  dsimp only
  intro d p hdp
  have h := Compose.honest_block_accepted
    (A := goldilocksNode (S.params (pubOf E) hn) (S.ro _)) proposer (digestOf S rho) self
    hq hg cfg cfg' t x hr hs hp d p hdp
  exact canonical_block_decodes S rho hn _ (by simp only [Node.mkBlock, ne_eq,
      reduceCtorEq, not_false_eq_true]) h.2.2.2.2.2.1
    (fun a ha => (h.2.2.2.1 a ha).1) h.2.2.2.2.1

/-- Every honest acceptance in the simulating trace has a valid canonical child wire.
Receipt validity and own-proposal validity are proved by their respective run laws. -/
theorem accepted_child_decodes {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) (y : Fin (Fintype.card V)) (hy : y ∈ honestKeys S rho)
    (i : Nat) (B : Blk (S.params (pubOf E) hn))
    (hc : (simTrace S rho hn).CallAt y i (.fg (.block B true))) :
    decodeBlock (S.params (pubOf E) hn) (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B := by
  have run := simTrace_goldilocksRun S rho hn hv
  rcases Compose.blockCall_cases run.toLocalRun hy hc with hg |
    ⟨j, x, _, hg, hp, d, p, hdp, hB, _, _, _, _⟩
  · have hw := run.wire y hy i _ _ hg
    have ha := (run.cutLaw y hy i _ hc).2.1
    obtain ⟨root, _, hr, _, _, _, _, _⟩ := Store.onBlock_eq_some ha
    exact canonical_block_decodes S rho hn B (by rw [hr]; simp) hw.1 hw.2.1 hw.2.2
  · obtain ⟨cfg, hr, hst, hs⟩ := Compose.group_step run.toLocalRun hy hg
    have req := SA.interface_requirements (S.params (pubOf E) hn)
      (List (FG.Att (Fintype.card V))) (S.ro _)
    have hd := own_proposal_decodes S rho hn (runProposer S rho hn) y cfg _ _ x
      ⟨req.1, req.2.1, req.2.2.1, req.2.2.2, SA.proposal_payload_valid _ _ _⟩
      run.genesis_root_ok hr hs hp d p (by rw [hst]; exact hdp)
    simpa only [hst, Node.acProposal, Node.tickStep, Node.acCall, hB] using hd

/-- A successful decode of a constructed wrapper preserves its explicit stamp and parent
when the canonical child has already been decoded in that table. -/
theorem decoded_forward_fields {sp : SA.SAParams} (hs : List (Header Info × Nat))
    (x : Fin sp.n) (t : Time) (p : Option (Wire sp.n)) (B : Blk sp)
    (hb : decodeBlock sp hs (blockObj sp B) = some B)
    {u : Time} {q : Option (Wire sp.n)} {C : Blk sp}
    (hd : decodeForward sp hs (forwardObj sp x t p B) = some (x, u, q, C)) :
    (u, q, C) = (t, p, B) := by
  cases p with
  | none =>
    simp only [forwardObj, Option.toList_none, List.nil_append, decodeForward, hb,
      Option.bind_eq_bind, Option.bind_some] at hd
    split at hd
    · cases hd; rfl
    · cases hd
  | some parent =>
    simp only [forwardObj, Option.toList_some, List.cons_append, List.nil_append,
      decodeForward, hb, Option.bind_eq_bind, Option.bind_some] at hd
    cases hp : decodeForward sp hs parent with
    | none => simp [hp] at hd
    | some result =>
      obtain ⟨origin, stamp, pp, A⟩ := result
      simp only [hp, Option.bind_some] at hd
      split at hd
      · cases hd; rfl
      · cases hd

/-- Acceptance preserves both decoder inventory and held-block correspondence together. -/
theorem decoded_held_accept {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (st : State (S.params (pubOf E) hn) (S.ro _))
    (hd : WrappersDecoded (digests (P := protoOf (compiled (family S)) E) rho.hash) st)
    (hh : WrappersHeld (digests (P := protoOf (compiled (family S)) E) rho.hash) st)
    (hc : WrappersCover st)
    (hr : st.node.fg.Reachable (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload)
    (B : Blk (S.params (pubOf E) hn))
    (ha : .fg (.block B true) ∈ (Node.onBlock st.self st.node st.now B).2)
    (hb : decodeBlock (S.params (pubOf E) hn) (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B) (ht : 0 ≤ st.now) :
    let st' := apply st (Node.onBlock st.self st.node st.now B)
    WrappersDecoded (digests (P := protoOf (compiled (family S)) E) rho.hash) st' ∧
    WrappersHeld (digests (P := protoOf (compiled (family S)) E) rho.hash) st' := by
  have hq := decoded_acceptance_enqueue S rho hn st hd hh hc hr B ha hb ht
  refine ⟨hq.accept st B hc ha, ?_⟩
  obtain ⟨root, p, hpar, hp, _, _⟩ := onBlock_queues_acceptance_parent st B hc ha
  have hm := (queueAccepted_of_parent st B root p hpar hp).1
  obtain ⟨u, q, C, hdec, _, _⟩ := hq.stored B.root
    (forwardObj _ st.self st.now p B) (by rw [hm]; simp)
  have hs : (queueAccepted st B).self = st.self := by simp [queueAccepted, hpar, hp]
  rw [hs] at hdec
  have contains : Obj.Contains (forwardObj (S.params (pubOf E) hn) st.self st.now p B)
      (blockObj _ B) :=
    Obj.Contains.step (List.mem_append_right _ (List.mem_singleton_self _)) (Obj.Contains.refl _)
  have hb' := decodeBlock_transport hb (show
      rootOf (digests rho.hash (forwardObj (S.params (pubOf E) hn) st.self st.now p B))
        (headerOf _ B) = rootOf (digests rho.hash (blockObj _ B)) (headerOf _ B) by
    rw [rootOf_digests_of_mem S rho _ _ (List.mem_filterMap.mpr ⟨_, contains, rfl⟩),
      rootOf_digests_blockObj])
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (decoded_forward_fields _ _ _ _ _ hb' hdec)
  exact hh.accept B root p hpar hp ha hdec

/-- Block handling preserves the joint invariant even when the block is refused.
Only the accepting branch needs a valid child wire. -/
theorem decoded_held_onBlock {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (st : State (S.params (pubOf E) hn) (S.ro _))
    (hd : WrappersDecoded (digests (P := protoOf (compiled (family S)) E) rho.hash) st)
    (hh : WrappersHeld (digests (P := protoOf (compiled (family S)) E) rho.hash) st)
    (hc : WrappersCover st)
    (hr : st.node.fg.Reachable (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload)
    (B : Blk (S.params (pubOf E) hn))
    (hb : .fg (.block B true) ∈ (Node.onBlock st.self st.node st.now B).2 →
      decodeBlock (S.params (pubOf E) hn) (digests rho.hash (blockObj _ B))
        (blockObj _ B) = some B) (ht : 0 ≤ st.now) :
    let st' := apply st (Node.onBlock st.self st.node st.now B)
    WrappersDecoded (digests (P := protoOf (compiled (family S)) E) rho.hash) st' ∧
    WrappersHeld (digests (P := protoOf (compiled (family S)) E) rho.hash) st' := by
  by_cases ha : .fg (.block B true) ∈ (Node.onBlock st.self st.node st.now B).2
  · exact decoded_held_accept S rho hn st hd hh hc hr B ha (hb ha) ht
  · unfold Node.onBlock at ha ⊢
    split
    · exact ⟨hd.mono rfl rfl rfl le_rfl, hh.preserve rfl rfl rfl⟩
    · split
      · exact ⟨hd.mono rfl rfl rfl le_rfl, hh.preserve rfl rfl rfl⟩
      · simp_all [Node.acCall]

/-- Processing a child carried by a receipt preserves decoding and held correspondence.
The decoder guard supplies the child's wire validity in the block branch. -/
theorem decoded_held_processOne {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (st : State (S.params (pubOf E) hn) (S.ro _))
    (hd : WrappersDecoded (digests (P := protoOf (compiled (family S)) E) rho.hash) st)
    (hh : WrappersHeld (digests (P := protoOf (compiled (family S)) E) rho.hash) st)
    (hc : WrappersCover st)
    (hr : st.node.fg.Reachable (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload)
    (receipt o : Wire (Fintype.card V)) (ho : Obj.Contains receipt o) (ht : 0 ≤ st.now) :
    let st' := processOne (digests rho.hash receipt) st o
    WrappersDecoded (digests (P := protoOf (compiled (family S)) E) rho.hash) st' ∧
    WrappersHeld (digests (P := protoOf (compiled (family S)) E) rho.hash) st' := by
  unfold processOne
  split
  · rename_i B he
    have h := decoded_held_onBlock S rho hn st hd hh hc hr B
      (fun _ => received_child_decodes S rho hn receipt o B ho (decodeBlock_of_canonEvent he)) ht
    unfold relayIf
    dsimp only
    split
    · exact ⟨h.1.mono rfl rfl rfl le_rfl, h.2.preserve rfl rfl rfl⟩
    · exact h
  · exact ⟨hd.mono rfl rfl rfl le_rfl, hh.preserve rfl rfl rfl⟩
  · rename_i a _
    obtain ⟨atts, he⟩ := Store.onAttestation_eq st.node.fg a
    unfold relayIf
    split
    · refine ⟨hd.mono rfl rfl rfl le_rfl, hh.preserve rfl rfl ?_⟩
      simpa only [apply, Node.onAttestation] using congrArg Store.blocks he
    · refine ⟨hd.mono rfl rfl rfl le_rfl, hh.preserve rfl rfl ?_⟩
      simpa only [apply, Node.onAttestation] using congrArg Store.blocks he
  · exact ⟨hd, hh⟩

/-- A complete parent-first receipt traversal preserves both wrapper invariants. -/
theorem decoded_held_process {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (st : State (S.params (pubOf E) hn) (S.ro _))
    (hd : WrappersDecoded (digests (P := protoOf (compiled (family S)) E) rho.hash) st)
    (hh : WrappersHeld (digests (P := protoOf (compiled (family S)) E) rho.hash) st)
    (hc : WrappersCover st)
    (hr : st.node.fg.Reachable (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload)
    (receipt : Wire (Fintype.card V)) (ht : 0 ≤ st.now) :
    let st' := process st receipt (digests rho.hash receipt)
    WrappersDecoded (digests (P := protoOf (compiled (family S)) E) rho.hash) st' ∧
    WrappersHeld (digests (P := protoOf (compiled (family S)) E) rho.hash) st' := by
  have fold : ∀ (os : List (Wire (Fintype.card V))),
      (∀ o ∈ os, Obj.Contains receipt o) → ∀ st,
      WrappersDecoded (digests (P := protoOf (compiled (family S)) E) rho.hash) st →
      WrappersHeld (digests (P := protoOf (compiled (family S)) E) rho.hash) st →
      WrappersCover st → st.node.fg.Reachable
        (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload → 0 ≤ st.now →
      WrappersDecoded (digests (P := protoOf (compiled (family S)) E) rho.hash)
        (os.foldl (processOne (digests rho.hash receipt)) st) ∧
      WrappersHeld (digests (P := protoOf (compiled (family S)) E) rho.hash)
        (os.foldl (processOne (digests rho.hash receipt)) st) := by
    intro os
    induction os with
    | nil => exact fun _ _ hd hh _ _ _ => ⟨hd, hh⟩
    | cons o os ih =>
      intro ho st hd hh hc hr ht
      have h := decoded_held_processOne S rho hn st hd hh hc hr receipt o
        (ho o (List.mem_cons_self)) ht
      exact ih (fun q hq => ho q (List.mem_cons_of_mem _ hq)) _ h.1 h.2
        (wrappersCover_processOne _ _ _ hc) (processOne_reachable _ _ _ hr)
        ((processOne_now (digests rho.hash receipt) st o).symm ▸ ht)
  exact fold _ (fun _ ho => ho) st hd hh hc hr ht

/-- FG attestation work changes neither decoded wrapper inventory nor held blocks. -/
theorem decoded_held_fgUpdate {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {tables : Wire sp.n → List (Header Info × Nat)} (st : State sp ro)
    (hd : WrappersDecoded tables st) (hh : WrappersHeld tables st) :
    WrappersDecoded tables (fgUpdate st) ∧ WrappersHeld tables (fgUpdate st) := by
  unfold fgUpdate
  dsimp only
  split
  · exact ⟨hd.mono rfl rfl rfl le_rfl, hh.preserve rfl rfl rfl⟩
  · split
    · exact ⟨hd.mono rfl rfl rfl le_rfl, hh.preserve rfl rfl rfl⟩
    · rename_i a record _
      obtain ⟨atts, he⟩ := Store.onAttestation_eq st.node.fg a
      refine ⟨hd.mono rfl rfl rfl le_rfl, hh.preserve rfl rfl ?_⟩
      simpa only [Node.acToFG, Node.onAttestation] using congrArg Store.blocks he

/-- Polling drains pending wrappers without losing durable decoding or held correspondence. -/
theorem decoded_held_poll {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {tables : Wire sp.n → List (Header Info × Nat)} (st : State sp ro) (t : Time)
    (hd : WrappersDecoded tables st) (hh : WrappersHeld tables st) :
    WrappersDecoded tables (poll st t).1 ∧ WrappersHeld tables (poll st t).1 := by
  have clear (s : State sp ro) (h : WrappersDecoded tables s) (g : WrappersHeld tables s)
      (outbox : List Body) :
      WrappersDecoded tables { s with outbox := outbox, forwards := [], voteForwards := [] } ∧
      WrappersHeld tables { s with outbox := outbox, forwards := [], voteForwards := [] } :=
    ⟨h.drain rfl rfl (by simp [pendingWrappers_eq]) le_rfl, g.preserve rfl rfl rfl⟩
  unfold poll
  split <;> dsimp only <;> split
  all_goals first
    | exact clear _ hd hh _
    | exact clear _ (decoded_held_fgUpdate st hd hh).1 (decoded_held_fgUpdate st hd hh).2 _

/-- AC tick preparation preserves both wrapper invariants. -/
theorem decoded_held_nodeTick {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {tables : Wire sp.n → List (Header Info × Nat)} (st : State sp ro)
    (hd : WrappersDecoded tables st) (hh : WrappersHeld tables st) :
    WrappersDecoded tables (nodeTick st) ∧ WrappersHeld tables (nodeTick st) := by
  unfold nodeTick
  split
  · exact ⟨hd.mono rfl rfl rfl le_rfl, hh.preserve rfl rfl rfl⟩
  · exact ⟨hd, hh⟩

/-- Proposal preparation changes AC state, not wrapper or held-block correspondence. -/
theorem decoded_held_propose {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {tables : Wire sp.n → List (Header Info × Nat)} (st : State sp ro) (s : Slot)
    (hd : WrappersDecoded tables st) (hh : WrappersHeld tables st) :
    WrappersDecoded tables (propose st s).1 ∧ WrappersHeld tables (propose st s).1 := by
  unfold propose
  dsimp only
  split <;> exact ⟨hd.mono rfl rfl rfl le_rfl, hh.preserve rfl rfl rfl⟩

/-- Restart at a later clock preserves wrappers for the same node identity. -/
theorem decoded_held_restore {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {tables : Wire sp.n → List (Header Info × Nat)} (st : State sp ro) (t : Time)
    (hd : WrappersDecoded tables st) (hh : WrappersHeld tables st) (ht : st.now ≤ t) :
    WrappersDecoded tables (restore st.self st t) ∧
    WrappersHeld tables (restore st.self st t) := by
  exact ⟨hd.mono rfl rfl rfl ht, hh.preserve rfl rfl rfl⟩

/-- The entire engine delivery, including its poll drain and gossip, preserves the joint
wrapper invariant. This does not assume that a refused candidate was published. -/
theorem decoded_held_deliver {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (family S)) E))
    (hd : WrappersDecoded (digests rho.hash) (shapeOf S hn nd))
    (hh : WrappersHeld (digests rho.hash) (shapeOf S hn nd))
    (hc : WrappersCover (shapeOf S hn nd))
    (hr : (shapeOf S hn nd).node.fg.Reachable
      (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload)
    (o : Wire (Fintype.card V)) (t : Time) (ht : 0 ≤ (shapeOf S hn nd).now) :
    let st' := shapeOf S hn (rho.deliver nd v o t).1
    WrappersDecoded (digests rho.hash) st' ∧ WrappersHeld (digests rho.hash) st' := by
  apply deliver_pres S rho hn
    (fun st => WrappersDecoded (digests rho.hash) st ∧ WrappersHeld (digests rho.hash) st)
  · exact fun st t h => decoded_held_poll st t h.1 h.2
  · intro st m cs hs h
    unfold recordOwn
    split
    · exact ⟨h.1.mono rfl rfl rfl le_rfl, h.2.preserve rfl rfl rfl⟩
    · rename_i k s header carried heq
      cases heq
    · exact h
  · exact decoded_held_process S rho hn (shapeOf S hn nd) hd hh hc hr o ht

end Consensus.Goldilocks.Refinement
