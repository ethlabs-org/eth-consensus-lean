module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ForwardingInvariant
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant

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
    (ht : 0 ≤ st.now) (hs : (S.params (pubOf E) hn).toParams.slotTime B.slot ≤ st.now) :
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
  exact hdec.engine_enqueue S rho hn st B root p hr hp hb ht hs
    (fun parent pt pp A hp hd => hheld.parent_slot_lt hreach B fg' hfg root hr
      parent pt pp A hp hd)

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

end Consensus.Goldilocks.Refinement
