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

end Consensus.Goldilocks.Refinement
