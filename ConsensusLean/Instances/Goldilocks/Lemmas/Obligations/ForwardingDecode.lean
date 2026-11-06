module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ForwardingInvariant
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationDecode
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Provenance

public section

/-! # Forwarding decoder correspondence

Relate the durable wrapper's decoded child to the actual held block, rather than
identifying blocks by equal roots without a store correspondence proof.
-/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

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
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (st : State (S.params (pubOf E) hn) (S.ro _))
    (hdec : WrappersDecoded (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st)
    (hheld : WrappersHeld (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st)
    (hcover : WrappersCover st)
    (hreach : st.node.fg.Reachable (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload)
    (B : Blk (S.params (pubOf E) hn))
    (ha : .fg (.block B true) ∈ (Node.onBlock st.self st.node st.now B).2)
    (hb : decodeBlock (S.params (pubOf E) hn) (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B)
    (ht : 0 ≤ st.now) :
    WrappersDecoded (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash)
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
theorem _root_.Consensus.Goldilocks.Simulation.WrappersDecoded.accept {sp : SA.SAParams}
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
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
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
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
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
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
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

/-- Acceptance preserves both decoder inventory and held-block correspondence together. -/
theorem decoded_held_accept {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (st : State (S.params (pubOf E) hn) (S.ro _))
    (hd : WrappersDecoded (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st)
    (hh : WrappersHeld (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st)
    (hc : WrappersCover st)
    (hr : st.node.fg.Reachable (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload)
    (B : Blk (S.params (pubOf E) hn))
    (ha : .fg (.block B true) ∈ (Node.onBlock st.self st.node st.now B).2)
    (hb : decodeBlock (S.params (pubOf E) hn) (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B) (ht : 0 ≤ st.now) :
    let st' := apply st (Node.onBlock st.self st.node st.now B)
    WrappersDecoded (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st' ∧
    WrappersHeld (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st' := by
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
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (st : State (S.params (pubOf E) hn) (S.ro _))
    (hd : WrappersDecoded (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st)
    (hh : WrappersHeld (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st)
    (hc : WrappersCover st)
    (hr : st.node.fg.Reachable (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload)
    (B : Blk (S.params (pubOf E) hn))
    (hb : .fg (.block B true) ∈ (Node.onBlock st.self st.node st.now B).2 →
      decodeBlock (S.params (pubOf E) hn) (digests rho.hash (blockObj _ B))
        (blockObj _ B) = some B) (ht : 0 ≤ st.now) :
    let st' := apply st (Node.onBlock st.self st.node st.now B)
    WrappersDecoded (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st' ∧
    WrappersHeld (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st' := by
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
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (st : State (S.params (pubOf E) hn) (S.ro _))
    (hd : WrappersDecoded (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st)
    (hh : WrappersHeld (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st)
    (hc : WrappersCover st)
    (hr : st.node.fg.Reachable (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload)
    (receipt o : Wire (Fintype.card V)) (ho : Obj.Contains receipt o) (ht : 0 ≤ st.now) :
    let st' := processOne (digests rho.hash receipt) st o
    WrappersDecoded (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st' ∧
    WrappersHeld (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st' := by
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
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (st : State (S.params (pubOf E) hn) (S.ro _))
    (hd : WrappersDecoded (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st)
    (hh : WrappersHeld (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st)
    (hc : WrappersCover st)
    (hr : st.node.fg.Reachable (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload)
    (receipt : Wire (Fintype.card V)) (ht : 0 ≤ st.now) :
    let st' := process st receipt (digests rho.hash receipt)
    WrappersDecoded (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st' ∧
    WrappersHeld (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st' := by
  have fold : ∀ (os : List (Wire (Fintype.card V))),
      (∀ o ∈ os, Obj.Contains receipt o) → ∀ st,
      WrappersDecoded (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st →
      WrappersHeld (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st →
      WrappersCover st → st.node.fg.Reachable
        (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload → 0 ≤ st.now →
      WrappersDecoded (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash)
        (os.foldl (processOne (digests rho.hash receipt)) st) ∧
      WrappersHeld (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash)
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
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (goldilocks S)) E))
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

/-- The actual tick prefix up to proposal preserves the joint wrapper invariant. -/
theorem decoded_held_atProposal {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (goldilocks S)) E)) (t : Time)
    (hd : WrappersDecoded (digests rho.hash) (shapeOf S hn nd))
    (hh : WrappersHeld (digests rho.hash) (shapeOf S hn nd))
    (ht : (shapeOf S hn nd).now ≤ t) (hsel : rho.ownKey v ∈ rho.sel .poll) :
    let st' := shapeOf S hn (atProposal S rho v nd t)
    WrappersDecoded (digests rho.hash) st' ∧ WrappersHeld (digests rho.hash) st' := by
  dsimp only
  rw [atProposal_shape S rho hn v nd t hsel]
  have hc : WrappersDecoded (digests rho.hash) { shapeOf S hn nd with now := t } ∧
      WrappersHeld (digests rho.hash) { shapeOf S hn nd with now := t } :=
    ⟨hd.mono rfl rfl rfl ht, hh.preserve rfl rfl rfl⟩
  have h1 := decoded_held_poll _ t.toNat hc.1 hc.2
  have h2 := decoded_held_poll _ t.toNat h1.1 h1.2
  exact decoded_held_nodeTick _ h2.1 h2.2

/-- Recording a valid canonical own block preserves the joint wrapper invariant. -/
theorem decoded_held_recordOwn_block {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (st : State (S.params (pubOf E) hn) (S.ro _))
    (hd : WrappersDecoded (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st)
    (hh : WrappersHeld (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st)
    (hc : WrappersCover st)
    (hr : st.node.fg.Reachable (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload)
    (B : Blk (S.params (pubOf E) hn)) (hpar : B.parent ≠ none)
    (hroot : B.RootOk (digestOf S rho))
    (hb : decodeBlock (S.params (pubOf E) hn) (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B) (ht : 0 ≤ st.now) :
    let st' := recordOwn st (blockObj (S.params (pubOf E) hn) B)
      (digests rho.hash (blockObj _ B))
    WrappersDecoded (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st' ∧
    WrappersHeld (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st' := by
  dsimp only
  rw [recordOwn_canonical_block S rho hn st B hpar hroot]
  exact decoded_held_onBlock S rho hn st hd hh hc hr B (fun _ => hb) ht

/-- A selected proposal with a canonical singleton candidate preserves both invariants,
whether the engine releases it or rejects it. -/
theorem decoded_held_proposal_candidate {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (goldilocks S)) E)) (s : Slot) (hs : 0 < s)
    (hd : WrappersDecoded (digests rho.hash) (shapeOf S hn nd))
    (hh : WrappersHeld (digests rho.hash) (shapeOf S hn nd))
    (hc : WrappersCover (propose (shapeOf S hn nd) s).1)
    (hr : (propose (shapeOf S hn nd) s).1.node.fg.Reachable
      (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload)
    (B : Blk (S.params (pubOf E) hn)) (hpar : B.parent ≠ none)
    (hroot : B.RootOk (digestOf S rho))
    (hb : decodeBlock (S.params (pubOf E) hn) (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B) (ht : 0 ≤ (shapeOf S hn nd).now)
    (hsel : rho.ownKey v ∈ rho.sel (.proposer s))
    (hcs : rho.signedCandidate v (.propose s hs)
      ((protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).2 = [blockObj _ B]) :
    let st' := shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1
    WrappersDecoded (digests rho.hash) st' ∧ WrappersHeld (digests rho.hash) st' := by
  have hp := decoded_held_propose (shapeOf S hn nd) s hd hh
  dsimp only
  simp only [Model.Run.dutyStep,
    show (protoOf (compiled (goldilocks S)) E).role (.propose s hs) = .proposer s from rfl,
    hsel, ↓reduceIte, hcs]
  erw [Model.releaseAll]
  split
  · change WrappersDecoded (digests rho.hash) (recordOwn
        (((protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).1.1 hn)
        (blockObj _ B) (digests rho.hash (blockObj _ B))) ∧
      WrappersHeld (digests rho.hash) (recordOwn
        (((protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).1.1 hn)
        (blockObj _ B) (digests rho.hash (blockObj _ B)))
    rw [shapeOf_act_propose S hn]
    exact decoded_held_recordOwn_block S rho hn _ hp.1 hp.2 hc hr B hpar hroot hb
      ((propose_now (shapeOf S hn nd) s).symm ▸ ht)
  · change WrappersDecoded (digests rho.hash)
      (((protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).1.1 hn) ∧
      WrappersHeld (digests rho.hash)
      (((protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).1.1 hn)
    rw [shapeOf_act_propose S hn]
    exact hp

/-- The engine's selected proposal candidate is the node's canonical constructed block. -/
theorem proposal_candidate_block {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (goldilocks S)) E)) (s : Slot) (hs : 0 < s)
    (hsel : rho.ownKey v ∈ rho.sel (.proposer s))
    (hslot : (S.params (pubOf E) hn).toParams.slotOf (shapeOf S hn nd).now = s) :
    let r := Node.acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now
    ∀ d p, r.2.2 = some (d, p) →
      rho.signedCandidate v (.propose s hs)
        ((protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).2 =
      [blockObj (S.params (pubOf E) hn) (Node.mkBlock (digestOf S rho) (rho.ownKey v)
        r.1.fg (shapeOf S hn nd).now (encodeTxs nd.st.2) d.head p)] := by
  dsimp only
  intro d p hp
  rw [act_propose_snd S hn nd s hs]
  simp only [propose, hp, Option.map_some, Option.toList_some, Model.Run.signedCandidate,
    show (protoOf (compiled (goldilocks S)) E).role (.propose s hs) = .proposer s from rfl,
    hsel, ↓reduceIte]
  simp only [blockObj, Node.mkBlock, headerOf, hslot]
  rfl

/-- A scheduled honest proposal's actual pre-record state supplies canonical child validity. -/
theorem scheduled_proposal_child_decodes {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) (v : V) (hh : v ∈ rho.honest) (i : Nat) (t : Time)
    (he : rho.events[i]? = some (.tick v t))
    (hp : Node.Proposes (P := (S.params (pubOf E) hn).toParams)
      (runProposer S rho hn) (rho.ownKey v) t) :
    let nd := atProposal S rho v (rho.stateBefore i v) t
    let r := Node.acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now
    ∀ d p, r.2.2 = some (d, p) →
      let B := Node.mkBlock (digestOf S rho) (rho.ownKey v) r.1.fg
        (shapeOf S hn nd).now (encodeTxs nd.st.2) d.head p
      decodeBlock (S.params (pubOf E) hn) (digests rho.hash (blockObj _ B))
        (blockObj _ B) = some B := by
  dsimp only
  intro d p hdp
  have run := simTrace_goldilocksRun S rho hn hv
  have hhon : rho.ownKey v ∈ honestKeys S rho := by
    rw [mem_honestKeys_iff]
    have hk : rho.key (rho.ownKey v) = v := rho.key.apply_symm_apply v
    rwa [hk]
  have hpub := (S.params (pubOf E) hn).toParams.slotTime_public
    ((S.params (pubOf E) hn).toParams.slotOf t)
  rw [← hp.2.1] at hpub
  have hg := (simTrace_tick_public_group S rho hn hv v hh i t he hpub).1
  obtain ⟨cfg, hr, hst, hs⟩ := Compose.group_step run.toLocalRun hhon hg
  have hstate := simTrace_state S rho hn hv v hh i
    (Nat.le_of_lt (List.getElem?_eq_some_iff.mp he).1)
  have hsel := poll_selected S rho hv v
  have hnode := atProposal_node S rho hn v (rho.stateBefore i v) t
    (by simpa only [stateAt_eq] using fgDue_eq_false S rho hn v i) hsel
  rw [nodeTick_node_public { (rho.stateBefore i v).st.1 hn with now := t } hpub] at hnode
  have hself := self_eq_ownKey S rho hn v i
  rw [stateAt_eq] at hself
  have hnow := atProposal_now S rho hn v (rho.stateBefore i v) t hsel
  have req := SA.interface_requirements (S.params (pubOf E) hn)
    (List (FG.Att (Fintype.card V))) (S.ro _)
  have hdecode := own_proposal_decodes S rho hn (runProposer S rho hn) (rho.ownKey v)
    cfg _ t (encodeTxs (mempool rho.inbox v t))
    ⟨req.1, req.2.1, req.2.2.1, req.2.2.2, SA.proposal_payload_valid _ _ _⟩
    run.genesis_root_ok hr hs hp d p (by
      rw [hst, ← hstate]
      simpa only [hnode, hnow, Node.tickStep, stateAt_eq, hself] using hdp)
  simpa only [hnode, hnow, atProposal_mempool, hst, ← hstate, Node.tickStep, stateAt_eq, hself]
    using hdecode

/-- At a scheduled honest tick, the proposal duty preserves the joint invariant without
assuming child decoding: reachable proposal execution supplies it. -/
theorem decoded_held_scheduled_proposal {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) (v : V) (hhon : v ∈ rho.honest) (i : Nat) (t : Time)
    (he : rho.events[i]? = some (.tick v t)) (s : Slot) (hs : 0 < s)
    (ht : t = (S.params (pubOf E) hn).toParams.slotTime s)
    (hd : WrappersDecoded (digests rho.hash)
      (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)))
    (hh : WrappersHeld (digests rho.hash)
      (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t))) :
    let nd := atProposal S rho v (rho.stateBefore i v) t
    let st' := shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1
    WrappersDecoded (digests rho.hash) st' ∧ WrappersHeld (digests rho.hash) st' := by
  let nd := atProposal S rho v (rho.stateBefore i v) t
  have hpoll := poll_selected S rho hv v
  have hnow : (shapeOf S hn nd).now = t := atProposal_now S rho hn v _ t hpoll
  have hslot : (S.params (pubOf E) hn).toParams.slotOf (shapeOf S hn nd).now = s := by
    rw [hnow, ht]; exact slotOf_slotTime _ s
  have hc : WrappersCover (propose (shapeOf S hn nd) s).1 := by
    have h := tick_duty_prefix_wrappersCover S rho hn v i t
      ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] :
        List (protoOf (compiled (goldilocks S)) E).Duty)
    rw [← atProposal_eq S rho v (rho.stateBefore i v) t] at h
    unfold propose
    dsimp only
    split <;> simpa only [wrappersCover_iff, Node.acProposal] using h
  have hr : (propose (shapeOf S hn nd) s).1.node.fg.Reachable
      (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload := by
    have hnode := atProposal_node S rho hn v (rho.stateBefore i v) t
      (by simpa only [stateAt_eq] using fgDue_eq_false S rho hn v i) hpoll
    have hpub : (S.params (pubOf E) hn).toParams.IsPublic t :=
      ht ▸ (S.params (pubOf E) hn).toParams.slotTime_public s
    have hfg : (shapeOf S hn nd).node.fg = (stateAt S rho hn v i).node.fg := by
      rw [hnode, nodeTick_node_public { (rho.stateBefore i v).st.1 hn with now := t } hpub]
      rw [stateAt_eq]
      rfl
    have hr := stateAt_fg_reachable S rho hn v i
    rw [← hfg] at hr
    unfold propose; dsimp only; split <;> exact hr
  by_cases hsel : rho.ownKey v ∈ rho.sel (.proposer s)
  · have hp : Node.Proposes (P := (S.params (pubOf E) hn).toParams)
        (runProposer S rho hn) (rho.ownKey v) t := by
      rw [ht, proposes_iff S hn _ _ s hs]
      rw [selValid_proposer S rho hn hv.selValid s] at hsel
      exact (Finset.mem_singleton.mp hsel).symm
    cases hdp : (Node.acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now).2.2 with
    | none =>
      have hempty : ((protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).2 = [] := by
        rw [act_propose_snd S hn nd s hs]
        simp only [propose, hdp, Option.map_none, Option.toList_none]
        rfl
      have hpre := decoded_held_propose (shapeOf S hn nd) s hd hh
      change WrappersDecoded (digests rho.hash)
          (shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1) ∧
        WrappersHeld (digests rho.hash) (shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1)
      simp only [Model.Run.dutyStep,
        show (protoOf (compiled (goldilocks S)) E).role (.propose s hs) = .proposer s from rfl,
        hsel, ↓reduceIte, hempty, Model.Run.signedCandidate, List.map_nil,
        Model.releaseAll]
      change WrappersDecoded (digests rho.hash)
          (((protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).1.1 hn) ∧
        WrappersHeld (digests rho.hash)
          (((protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).1.1 hn)
      rw [shapeOf_act_propose S hn]
      exact hpre
    | some result =>
      obtain ⟨d, p⟩ := result
      exact decoded_held_proposal_candidate S rho hn v nd s hs hd hh hc hr
        (Node.mkBlock (A := goldilocksNode (S.params (pubOf E) hn) (S.ro _))
          (digestOf S rho) (rho.ownKey v)
          (Node.acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now).1.fg
          (shapeOf S hn nd).now (encodeTxs nd.st.2) d.head p)
        (by simp only [Node.mkBlock, ne_eq, reduceCtorEq, not_false_eq_true]) rfl
        (scheduled_proposal_child_decodes S rho hn hv v hhon i t he hp d p hdp)
        (hnow.symm ▸ (hv.in_horizon _ (List.mem_of_getElem? he)).1) hsel
        (proposal_candidate_block S rho hn v nd s hs hsel hslot d p hdp)
  · simpa only [Model.Run.dutyStep,
      show (protoOf (compiled (goldilocks S)) E).role (.propose s hs) = .proposer s from rfl,
      hsel, ↓reduceIte] using And.intro hd hh

/-- The engine clock is nonnegative and never exceeds the next event's time. -/
theorem stateAt_clock_bounds {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) (v : V) (i : Nat) :
    0 ≤ (stateAt S rho hn v i).now ∧
      ∀ j e, i ≤ j → rho.events[j]? = some e → (stateAt S rho hn v i).now ≤ e.time := by
  rw [now_eq_lastClock S rho hn hv]
  induction i with
  | zero =>
    rw [lastClock_zero]
    exact ⟨le_rfl, fun _ e _ he => (hv.in_horizon e (List.mem_of_getElem? he)).1⟩
  | succ i ih =>
    have old : 0 ≤ lastClock S rho v i ∧
        ∀ j e, i + 1 ≤ j → rho.events[j]? = some e → lastClock S rho v i ≤ e.time :=
      ⟨ih.1, fun j e hij he => ih.2 j e (by omega) he⟩
    cases he : rho.events[i]? with
    | none => rw [lastClock_succ_none S rho v he]; exact old
    | some e =>
      have current : 0 ≤ e.time ∧
          ∀ j f, i + 1 ≤ j → rho.events[j]? = some f → e.time ≤ f.time := by
        refine ⟨(hv.in_horizon e (List.mem_of_getElem? he)).1, ?_⟩
        intro j f hij hf
        rcases keyLe_of_lt S rho hv he hf (by omega) with h | h
        · exact h.le
        · exact h.1.le
      cases e with
      | tick w t =>
        by_cases hw : w = v
        · subst w; rw [lastClock_succ_tick S rho v he]; exact current
        · rw [lastClock_succ_other S rho v he hw]; exact old
      | restart w t =>
        by_cases hw : w = v
        · subst w; rw [lastClock_succ_restart S rho v he]; exact current
        · rw [lastClock_succ_other S rho v he hw]; exact old
      | deliver w o t =>
        by_cases hw : w = v
        · subst w; rw [lastClock_succ_deliver S rho v he]; exact old
        · rw [lastClock_succ_other S rho v he hw]; exact old

/-- Every actual honest tick preserves the joint invariant, including its own proposal. -/
theorem decoded_held_tick {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) (v : V) (hhon : v ∈ rho.honest) (i : Nat) (t : Time)
    (he : rho.events[i]? = some (.tick v t))
    (hd : WrappersDecoded (digests rho.hash) (stateAt S rho hn v i))
    (hh : WrappersHeld (digests rho.hash) (stateAt S rho hn v i)) :
    let st' := shapeOf S hn (rho.tick (rho.stateBefore i v) v t).1
    WrappersDecoded (digests rho.hash) st' ∧ WrappersHeld (digests rho.hash) st' := by
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  have hw := hv.tick_awake v t (List.mem_of_getElem? he)
  have hsel := poll_selected S rho hv v
  have hclock := stateAt_clock_bounds S rho hn hv v i
  rw [stateAt_eq] at hd hh hclock
  have hp := decoded_held_atProposal S rho hn v (rho.stateBefore i v) t hd hh
    (hclock.2 i _ le_rfl he) hsel
  have hprop :
      WrappersDecoded (digests rho.hash) (shapeOf S hn
        (rho.runDuties v (atProposal S rho v (rho.stateBefore i v) t)
          ((skeleton (pubOf E)).proposeAt t)).1) ∧
      WrappersHeld (digests rho.hash) (shapeOf S hn
        (rho.runDuties v (atProposal S rho v (rho.stateBefore i v) t)
          ((skeleton (pubOf E)).proposeAt t)).1) := by
    rcases Skeleton.proposeAt_cases (skeleton (pubOf E)) t with
      ⟨hnil, _⟩ | ⟨s, hs, hone, htime⟩
    · rw [hnil]; erw [runDuties_fst_nil]; exact hp
    · rw [hone]; erw [runDuties_fst_cons, runDuties_fst_nil]
      exact decoded_held_scheduled_proposal S rho hn hv v hhon i t he s hs
        (htime.trans (slotTime_eq S hn s).symm) hp.1 hp.2
  dsimp only
  rw [tick_of_awake S rho v _ t hw]
  apply releaseAll_pres_mem S rho hn
    (fun st => WrappersDecoded (digests rho.hash) st ∧ WrappersHeld (digests rho.hash) st)
  · intro c hc st hs h
    obtain ⟨mc, _, rfl⟩ := Model.mem_gossipCandidates.mp hc
    have unsigned (m : Msg (Header Info) Body) (cs : List (Wire (Fintype.card V))) :
        WrappersDecoded (digests rho.hash) (recordOwn st (.mk .none m cs) hs) ∧
        WrappersHeld (digests rho.hash) (recordOwn st (.mk .none m cs) hs) := by
      unfold recordOwn
      split
      · exact ⟨h.1.mono rfl rfl rfl le_rfl, h.2.preserve rfl rfl rfl⟩
      · rename_i k s header carried heq; cases heq
      · exact h
    exact unsigned mc.1 mc.2
  · -- The duty steps stated on the goal's own `ShapeDuty` lists, so plain `rw` applies (as in
    -- `tick_node_eq`); `erw [← atProposal_eq …]` tried every projection at default transparency.
    have hpoll : ∀ (nd' : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (x : Nat),
        shapeOf S hn (rho.runDuties v nd' [.poll x]).1 = (poll (shapeOf S hn nd') x).1 :=
      fun nd' x => dutyStep_poll S rho hn v nd' x hsel
    have hinit : ∀ nd' : Model.Node (Model.protoOf (compiled (goldilocks S)) E),
        (rho.runDuties v nd' (dutiesInit S t)).1 =
          (rho.runDuties v (rho.runDuties v (rho.runDuties v nd'
            ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] :
              List (Model.protoOf (compiled (goldilocks S)) E).Duty)).1
            ((skeleton (pubOf E)).proposeAt t)).1 [.poll t.toNat]).1 := fun nd' =>
      (runDuties_fst_append S rho v nd' _ _).trans
        (congrArg (fun x => (rho.runDuties v x [.poll t.toNat]).1)
          (runDuties_fst_append S rho v nd' _ _))
    rw [duties_eq S t ht, runDuties_fst_append, hpoll, hinit, hpoll,
      ← atProposal_eq S rho v (rho.stateBefore i v) t]
    exact decoded_held_poll _ _ (decoded_held_poll _ _ hprop.1 hprop.2).1
      (decoded_held_poll _ _ hprop.1 hprop.2).2

/-- Every reachable honest engine state has decoded wrappers corresponding to held blocks.
No decoder, parent-slot, payload-validity or clock premise is assumed. -/
theorem stateAt_decoded_held {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) (v : V) (hh : v ∈ rho.honest) (i : Nat) :
    WrappersDecoded (digests rho.hash) (stateAt S rho hn v i) ∧
    WrappersHeld (digests rho.hash) (stateAt S rho hn v i) := by
  induction i with
  | zero =>
    rw [stateAt_zero]
    exact ⟨wrappersDecoded_empty _ _ (fun _ => rfl) rfl,
      wrappersHeld_empty _ _ (fun _ => rfl)⟩
  | succ i ih =>
    cases he : rho.events[i]? with
    | none => rw [stateAt_succ_none S rho hn v he]; exact ih
    | some ev =>
      by_cases hvn : ev.node = v
      · cases ev with
        | tick w t =>
          simp only [Model.Event.node] at hvn
          subst w
          rw [stateAt_tick S rho hn v he]
          exact decoded_held_tick S rho hn hv v hh i t he ih.1 ih.2
        | deliver w o t =>
          simp only [Model.Event.node] at hvn
          subst w
          rw [stateAt_deliver S rho hn v he]
          have hc := stateAt_wrappersCover S rho hn v i
          have hr := stateAt_fg_reachable S rho hn v i
          have ht := (stateAt_clock_bounds S rho hn hv v i).1
          rw [stateAt_eq] at ih hc hr ht
          exact decoded_held_deliver S rho hn v _ ih.1 ih.2
            hc hr o t ht
        | restart w t =>
          simp only [Model.Event.node] at hvn
          subst w
          rw [stateAt_restart S rho hn v he]
          have h := decoded_held_restore (stateAt S rho hn v i) t ih.1 ih.2
            ((stateAt_clock_bounds S rho hn hv v i).2 i _ le_rfl he)
          rwa [self_eq_ownKey S rho hn v i] at h
      · rw [state_of_other S rho hn v i ev he hvn]; exact ih

/-- A queued canonical wrapper decodes to its exact child, parent and acceptance stamp.
The child decoder fixes identity without any root-injectivity assumption. -/
theorem pending_forward_decodes {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (st : State (S.params (pubOf E) hn) (S.ro _))
    (hd : WrappersDecoded (digests (P := protoOf (compiled (goldilocks S)) E) rho.hash) st)
    (t : Time) (p : Option (Wire (Fintype.card V))) (B : Blk (S.params (pubOf E) hn))
    (hp : forwardObj _ st.self t p B ∈ pendingWrappers st)
    (hb : decodeBlock (S.params (pubOf E) hn) (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B) :
    decodeForward (S.params (pubOf E) hn)
      (digests rho.hash (forwardObj _ st.self t p B)) (forwardObj _ st.self t p B) =
        some (st.self, t, p, B) := by
  obtain ⟨u, q, C, hc, _⟩ := hd.pending _ hp
  have hcontains : Obj.Contains (forwardObj (S.params (pubOf E) hn) st.self t p B)
      (blockObj _ B) :=
    Obj.Contains.step (List.mem_append_right _ (List.mem_singleton_self _)) (Obj.Contains.refl _)
  have hb' := decodeBlock_transport hb (show
      rootOf (digests rho.hash (forwardObj (S.params (pubOf E) hn) st.self t p B))
        (headerOf _ B) = rootOf (digests rho.hash (blockObj _ B)) (headerOf _ B) by
    rw [rootOf_digests_of_mem S rho _ _ (List.mem_filterMap.mpr ⟨_, hcontains, rfl⟩),
      rootOf_digests_blockObj])
  have he := decoded_forward_fields _ st.self t p B hb' hc
  cases he
  exact hc

/-- Receipt acceptances publish a wrapper that decodes, not merely a candidate with the
right syntactic shape. The queue and decoder witnesses use the same processed state. -/
theorem delivery_acceptance_decoded_publication {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) {v : V} (hhon : v ∈ rho.honest)
    {i : Nat} {o : (protoOf (compiled (goldilocks S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (r : CutRec (S.params (pubOf E) hn) (S.ro _)) (B : Blk (S.params (pubOf E) hn))
    (hr : r ∈ eventCuts S rho hn i) (hb : r.label = .fg (.block B true))
    (hchild : decodeBlock (S.params (pubOf E) hn) (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B) :
    ∃ p q, (publisherExecution S rho).actual q ∧ q.event = i ∧
      q.origin = rho.ownKey v ∧
      q.object = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B ∧
      decodeForward (S.params (pubOf E) hn) (digests rho.hash q.object) q.object =
        some (rho.ownKey v, t, p, B) := by
  have ht : (stateAt S rho hn v i).now = t :=
    (now_eq_lastClock S rho hn hv v i).trans (lastClock_deliver S rho hv he)
  rw [eventCuts_deliver S rho hn i v o t he] at hr
  have hr' : r ∈ deliverRecs (runProposer S rho hn) (digestOf S rho)
      (digests rho.hash o) (stateAt S rho hn v i).self (stateAt S rho hn v i).now i
      (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v i).node 0 := by
    simpa only [self_eq_ownKey, ht] using hr
  obtain ⟨p, hp⟩ := deliverRecs_acceptance_pending (runProposer S rho hn) (digestOf S rho)
    (digests rho.hash o) i _ _ 0 (stateAt_wrappersCover S rho hn v i) r B hr' hb
  have hself : (process (stateAt S rho hn v i) o (digests rho.hash o)).self =
      rho.ownKey v := (process_self _ _ _).trans (self_eq_ownKey S rho hn v i)
  have hc : forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B ∈
      pendingWrappers (process (stateAt S rho hn v i) o (digests rho.hash o)) := by
    rw [pendingWrappers_eq]
    refine List.mem_map.mpr ⟨_, hp, ?_⟩
    simp only [ht, forwardObj]
    rw [hself]
  have hstate := stateAt_decoded_held S rho hn hv v hhon i
  have hprocessed := decoded_held_process S rho hn _ hstate.1 hstate.2
    (stateAt_wrappersCover S rho hn v i) (stateAt_fg_reachable S rho hn v i) o
    (stateAt_clock_bounds S rho hn hv v i).1
  have hd := pending_forward_decodes S rho hn _ hprocessed.1 t p B
    (hself.symm ▸ hc) hchild
  rw [hself] at hd
  obtain ⟨q, hq, hi, hx, ho⟩ := delivery_pending_publication S rho hn hv he _ hc
  exact ⟨p, q, hq, hi, hx, ho, ho.symm ▸ hd⟩

/-- Scheduled proposal acceptance publishes its exact decoded wrapper in the same tick. -/
theorem tick_proposal_acceptance_decoded_publication {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) (v : V) (hh : v ∈ rho.honest)
    (i : Nat) (t : Time) (he : rho.events[i]? = some (.tick v t)) (s : Slot) (hs : 0 < s)
    (hone : (skeleton (pubOf E)).proposeAt t = [.propose s hs])
    (ht : t = (S.params (pubOf E) hn).toParams.slotTime s)
    (B : Blk (S.params (pubOf E) hn))
    (ha : .fg (.block B true) ∈ (Node.tickStep (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).node
      t (encodeTxs (mempool rho.inbox v t)) .proposal).2)
    (hchild : decodeBlock (S.params (pubOf E) hn) (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B) :
    ∃ p q, (publisherExecution S rho).actual q ∧ q.event = i ∧
      q.origin = rho.ownKey v ∧
      q.object = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B ∧
      decodeForward (S.params (pubOf E) hn) (digests rho.hash q.object) q.object =
        some (rho.ownKey v, t, p, B) := by
  obtain ⟨p, hp⟩ := tick_proposal_acceptance_queued S rho hn hv v hh i t he s hs hone ht B ha
  have hstate := stateAt_decoded_held S rho hn hv v hh i
  have hclock := (stateAt_clock_bounds S rho hn hv v i).2 i _ le_rfl he
  rw [stateAt_eq] at hstate hclock
  have hprefix := decoded_held_atProposal S rho hn v (rho.stateBefore i v) t
    hstate.1 hstate.2 hclock
    (poll_selected S rho hv v)
  have hprop := decoded_held_scheduled_proposal S rho hn hv v hh i t he s hs ht
    hprefix.1 hprefix.2
  have hself : (shapeOf S hn (rho.dutyStep v
      (atProposal S rho v (rho.stateBefore i v) t) (.propose s hs)).1).self =
      rho.ownKey v := by
    apply dutyStep_pres S rho hn (fun st => st.self = rho.ownKey v)
      (fun st o hs h => (recordOwn_self st o hs).trans h)
      (fun st s h => (propose_self st s).trans h)
      (fun st h => (nodeTick_self st).trans h)
      (fun st t h => (poll_self st t).trans h)
    exact (atProposal_self S rho hn v _ t (poll_selected S rho hv v)).trans
      (by simpa only [stateAt_eq] using self_eq_ownKey S rho hn v i)
  have hd := pending_forward_decodes S rho hn _ hprop.1 t p B
    (hself.symm ▸ hp) hchild
  rw [hself] at hd
  have hpub : ∃ q, (publisherExecution S rho).actual q ∧ q.event = i ∧
      q.origin = rho.ownKey v ∧
      q.object = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B := by
    apply tick_pending_publication S rho hn hv he
      ([ShapeDuty.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] ++ [.propose s hs])
      [ShapeDuty.poll t.toNat]
    · rw [duties_eq S t (hv.in_horizon _ (List.mem_of_getElem? he)).1]
      simp only [dutiesInit, hone]
      rfl
    · erw [runDuties_fst_append, runDuties_fst_cons, runDuties_fst_nil]
      rwa [atProposal_eq] at hp
  obtain ⟨q, hq, hi, hx, ho⟩ := hpub
  exact ⟨p, q, hq, hi, hx, ho, ho.symm ▸ hd⟩

/-- Every accepting cut of an honest tick has a successfully decoded publication. -/
theorem tick_acceptance_decoded_publication {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) (v : V) (hh : v ∈ rho.honest)
    (i : Nat) (t : Time) (he : rho.events[i]? = some (.tick v t))
    (r : CutRec (S.params (pubOf E) hn) (S.ro _)) (B : Blk (S.params (pubOf E) hn))
    (hr : r ∈ eventCuts S rho hn i) (hb : r.label = .fg (.block B true))
    (hchild : decodeBlock (S.params (pubOf E) hn) (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B) :
    ∃ p q, (publisherExecution S rho).actual q ∧ q.event = i ∧
      q.origin = rho.ownKey v ∧
      q.object = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B ∧
      decodeForward (S.params (pubOf E) hn) (digests rho.hash q.object) q.object =
        some (rho.ownKey v, t, p, B) := by
  have hpub : (S.params (pubOf E) hn).toParams.IsPublic t := by
    by_contra h
    rw [eventCuts_tick_other S rho hn i v t he h] at hr
    exact List.not_mem_nil hr
  rw [eventCuts_tick_public S rho hn i v t he hpub] at hr
  obtain ⟨k, hk, hkr⟩ := List.getElem_of_mem hr
  have hl := (getElem_groupRecs (runProposer S rho hn) (digestOf S rho)
    (rho.ownKey v) (stateAt S rho hn v i).node t (Nat.pair i 0)
    (.tick (encodeTxs (mempool rho.inbox v t))) k hk).2.2.2.2
  rw [hkr, hb] at hl
  have ha := tick_acceptance_proposal (runProposer S rho hn) (digestOf S rho)
    (rho.ownKey v) (stateAt S rho hn v i).node t (encodeTxs (mempool rho.inbox v t)) B
    (hl.symm ▸ List.getElem_mem _)
  have hsel := poll_selected S rho hv v
  have hnode : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).node =
      (Node.acCall (rho.ownKey v) (stateAt S rho hn v i).node t .tick).1 := by
    rw [atProposal_node S rho hn v _ t
      (by simpa only [stateAt_eq] using fgDue_eq_false S rho hn v i) hsel,
      nodeTick_node_public _ hpub, ← stateAt_eq S rho hn v i]
    exact congrArg (fun key => (Node.acCall key _ t .tick).1) (self_eq_ownKey S rho hn v i)
  rcases Skeleton.proposeAt_cases (skeleton (pubOf E)) t with
    ⟨hnil, hno⟩ | ⟨s, hs, hone, htime⟩
  · have hnp := not_proposes S hn (runProposer S rho hn) (rho.ownKey v) t
      (fun s hs h => hno s hs (h.trans (slotTime_eq S hn s)))
    simp only [Node.tickStep, hnp, ↓reduceIte, List.not_mem_nil] at ha
  · apply tick_proposal_acceptance_decoded_publication S rho hn hv v hh i t he s hs hone
      (htime.trans (slotTime_eq S hn s).symm) B _ hchild
    rwa [hnode]

/-- Every honest acceptance has an actual, exactly decoded same-event publication.
All decoding premises follow from execution validity and reachable state invariants. -/
theorem forwardAtAcceptance {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) :
    ForwardAtAcceptance S rho hn (simTrace S rho hn) (cutMap S rho hn)
      (publisherExecution S rho) := by
  rw [forwardAtAcceptance_iff]
  intro x hx k B ha
  have hchild := accepted_child_decodes S rho hn hv x hx k B ha
  obtain ⟨hxk, hlab⟩ := ha
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, _, he, hlo, hhi, hidx, hnode, htime, _, hlabel⟩ :=
    simTrace_cut S rho hn hl
  have hb : r.label = .fg (.block B true) := Option.some.inj (hlabel.symm.trans hlab)
  have hr := List.mem_of_getElem? hidx
  have hxev : rho.ownKey ev.node = x := hnode.symm.trans hxk
  have hhon : ev.node ∈ rho.honest := by
    have hi : rho.key (rho.ownKey ev.node) = ev.node := rho.key.apply_symm_apply _
    rw [mem_honestKeys_iff] at hx
    rwa [← hxev, hi] at hx
  have hp : ∃ p q, (publisherExecution S rho).actual q ∧ q.event = i ∧
      q.origin = rho.ownKey ev.node ∧
      q.object = forwardObj (S.params (pubOf E) hn) (rho.ownKey ev.node) ev.time p B ∧
      decodeForward (S.params (pubOf E) hn) (digests rho.hash q.object) q.object =
        some (rho.ownKey ev.node, ev.time, p, B) := by
    cases ev with
    | tick v t =>
      exact tick_acceptance_decoded_publication S rho hn hv v hhon i t he r B hr hb hchild
    | deliver v o t =>
      exact delivery_acceptance_decoded_publication S rho hn hv hhon he r B hr hb hchild
    | restart v t =>
      rw [eventCuts_restart S rho hn i v t he] at hr
      obtain ⟨j, hj, hjr⟩ := List.getElem_of_mem hr
      have hc := (getElem_groupRecs (runProposer S rho hn) (digestOf S rho)
        (rho.ownKey v) (stateAt S rho hn v i).node t (Nat.pair i 0) .restart j hj).2.2.2.2
      rw [hjr, hb] at hc
      have hm := hc.symm ▸ List.getElem_mem (by simpa only [length_groupRecs] using hj)
      simp [Node.exec, Node.restart, Node.acCall] at hm
  obtain ⟨p, q, hq, hqi, hqx, hqo, hd⟩ := hp
  refine ⟨q, p, hq, hqx.trans hxev, hqi ▸ hlo, hqi ▸ hhi, ?_, ?_, ?_⟩
  · rw [hqi, publisherExecution_eventTime_eq, he]
    exact htime.symm
  · simpa only [hxev, ← htime] using hqo
  · simpa only [hxev, ← htime] using hd

end Consensus.Goldilocks.Obligations
