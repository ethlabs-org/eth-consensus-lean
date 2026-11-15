module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Interface
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Tree

public section

/-! # Engine output chains

The parent walk is independent of its fuel above the block's slot. Ancestry in a reachable
store therefore gives structural prefix inclusion of the emitted header chains. `blocksTo` is the
walk as a block list, whose headers are `chainTo` (`blocksTo_map`) and whose blocks are held
non-genesis ancestors of a held tip (`mem_blocksTo`, `blocksTo_nonroot`). These facts
do not assume collision freedom and do not depend on the encoding of roots. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Shape
open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {st : Store sp.toParams (Payload sp.n)}
  {acp₀ : Payload sp.n}

variable (V : Type) [Fintype V] [DecidableEq V] (S : BoundSetup) in
/-- The engine reads the node outputs stored by the family, also at the last cut. -/
theorem readIsOut : ReadIsOut V S := by
  rw [readIsOut_iff]
  intro E rho hn g v i
  simp only [chainTrace, goldilocksWith, goldilocksShape, dite_eq_left hn, stateAt_eq]

/-- Read the embedded node's output in a particular engine run. -/
theorem read_eq_out {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
    (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)
    (g : Out) (v : V) (i : Nat) :
    (chainTrace rho).read g v i =
      outOf (stateAt S rho hn v i).node (stateAt S rho hn v i).now g :=
  (readIsOut_iff V S).mp (readIsOut V S) E rho hn g v i

/-- Fuel beyond the tip's slot cannot change its emitted chain. -/
theorem chainTo_fuel (hr : st.Reachable acp₀) {B : Blk sp} (hB : B ∈ st.tree)
    {f k : Nat} (hf : B.slot < f) (hk : B.slot < k) :
    chainTo st.blocks f B = chainTo st.blocks k B := by
  induction f generalizing B k with
  | zero => omega
  | succ f ih =>
    cases k with
    | zero => omega
    | succ k =>
      simp only [chainTo]
      split_ifs with hg
      · rfl
      · cases hp : B.parent.bind st.blocks with
        | none => rfl
        | some P =>
          obtain ⟨r, hpar, hP⟩ := Option.bind_eq_some_iff.1 hp
          have hPr := hr.blocks_root hP
          have hPt : P ∈ st.tree := by change st.blocks P.root = some P; rwa [hPr]
          have hlt := (Store.accepted_tree _ _ _ _ hr).2.1.2 P hPt B hB
            (hpar.trans (congrArg some hPr.symm))
          exact congrArg (· ++ [headerOf sp B]) (ih hPt (by omega) (by omega))

/-- An ancestor's output chain is a prefix, without a collision-freedom premise. -/
theorem chainTo_prefix (hr : st.Reachable acp₀) {B C : Blk sp} (h : st.Anc B C) :
    (chainTo st.blocks (B.slot + 1) B).IsPrefix (chainTo st.blocks (C.slot + 1) C) := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | @tail P C h e ih =>
    have hCg : C.root ≠ sp.genesisRoot := by
      intro he
      have hgen := (Store.accepted_tree _ _ _ _ hr).2.2.1
      have hEq := (Store.accepted_tree _ _ _ _ hr).2.1.1 e.2.1 hgen he
      have hlt := (Store.accepted_tree _ _ _ _ hr).2.1.2 P e.1 C e.2.1 e.2.2
      rw [hEq] at hlt
      change P.slot < 0 at hlt
      omega
    have hlt := (Store.accepted_tree _ _ _ _ hr).2.1.2 P e.1 C e.2.1 e.2.2
    have hp : C.parent.bind st.blocks = some P := by
      rw [e.2.2, Option.bind_some]
      exact e.1
    conv_rhs => rw [chainTo, ite_eq_right hCg, hp]
    dsimp only
    rw [chainTo_fuel hr e.1 hlt (Nat.lt_succ_self _)]
    exact ih.trans (List.prefix_append _ _)

/-- Growing a store preserves the chain of a block it already held. -/
theorem chainTo_mono {st' : Store sp.toParams (Payload sp.n)} (hr : st.Reachable acp₀)
    (hsub : st.tree ⊆ st'.tree) {B : Blk sp} (hB : B ∈ st.tree) (fuel : Nat) :
    chainTo st.blocks fuel B = chainTo st'.blocks fuel B := by
  induction fuel generalizing B with
  | zero => rfl
  | succ fuel ih =>
    simp only [chainTo]
    split_ifs with hg
    · rfl
    · have hAnc := (Store.accepted_tree _ _ _ _ hr).2.2.2 B hB
      obtain he | ⟨P, _, e⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hAnc
      · exact False.elim (hg (congrArg Block.root he))
      · have hp : B.parent.bind st.blocks = some P := by
          rw [e.2.2, Option.bind_some]; exact e.1
        have hp' : B.parent.bind st'.blocks = some P := by
          rw [e.2.2, Option.bind_some]; exact hsub e.1
        simp only [hp, hp']
        rw [ih e.1]

/-- Coherent stores compute the same chain for a shared held block. -/
theorem chainTo_agree {st' : Store sp.toParams (Payload sp.n)}
    (hr : st.Reachable acp₀) (hr' : st'.Reachable acp₀)
    {U : Set (Blk sp)} (hc : Coherent U) (hs : st.tree ⊆ U) (hs' : st'.tree ⊆ U)
    {B : Blk sp} (hB : B ∈ st.tree) (hB' : B ∈ st'.tree) (fuel : Nat) :
    chainTo st.blocks fuel B = chainTo st'.blocks fuel B := by
  induction fuel generalizing B with
  | zero => rfl
  | succ fuel ih =>
    simp only [chainTo]
    split_ifs with hg
    · rfl
    · obtain he | ⟨P, _, e⟩ :=
        (Relation.ReflTransGen.cases_tail_iff _ _ _).1
          ((Store.accepted_tree _ _ _ _ hr).2.2.2 B hB)
      · exact (hg (congrArg Block.root he)).elim
      obtain he | ⟨P', _, e'⟩ :=
        (Relation.ReflTransGen.cases_tail_iff _ _ _).1
          ((Store.accepted_tree _ _ _ _ hr').2.2.2 B hB')
      · exact (hg (congrArg Block.root he)).elim
      have heq : P = P' := hc.1 (hs e.1) (hs' e'.1)
        (Option.some.inj (e.2.2.symm.trans e'.2.2))
      subst P'
      have hp : B.parent.bind st.blocks = some P := by
        rw [e.2.2, Option.bind_some]; exact e.1
      have hp' : B.parent.bind st'.blocks = some P := by
        rw [e'.2.2, Option.bind_some]; exact e'.1
      simp only [hp, hp']
      rw [ih e.1 e'.1]

/-- Ancestry in a coherent superset restricts to a reachable store below a held tip. -/
theorem anc_in_store (hr : st.Reachable acp₀) {U : Set (Blk sp)}
    (hc : Coherent U) (hs : st.tree ⊆ U) {B C : Blk sp}
    (h : Anc U B C) (hC : C ∈ st.tree) : st.Anc B C := by
  induction h with
  | refl => exact .refl
  | @tail P C _ e ih =>
    obtain he | ⟨Q, _, eq⟩ :=
      (Relation.ReflTransGen.cases_tail_iff _ _ _).1
        ((Store.accepted_tree _ _ _ _ hr).2.2.2 C hC)
    · subst C
      cases e.2.2
    · have hQP : Q = P := hc.1 (hs eq.1) e.1
        (Option.some.inj (eq.2.2.symm.trans e.2.2))
      subst Q
      exact (ih eq.1).tail eq

/-- For two reachable stores whose trees lie in a coherent set `U`, ancestry in `U` from a block
held by the first to a block held by the second makes the first chain a prefix of the second. -/
theorem chainTo_prefix_of_anc {st' : Store sp.toParams (Payload sp.n)}
    (hr : st.Reachable acp₀) (hr' : st'.Reachable acp₀) {U : Set (Blk sp)} (hU : Coherent U)
    (hs : st.tree ⊆ U) (hs' : st'.tree ⊆ U) {B C : Blk sp} (hB : B ∈ st.tree)
    (hC : C ∈ st'.tree) (h : Anc U B C) :
    (chainTo st.blocks (B.slot + 1) B).IsPrefix (chainTo st'.blocks (C.slot + 1) C) := by
  have ha := anc_in_store hr' hU hs' h hC
  have hm : B ∈ st'.tree := by
    by_cases he : B = C
    · exact he ▸ hC
    · exact (Anc.mem ha he).1
  rw [chainTo_agree hr hr' hU hs hs' hB hm]
  exact chainTo_prefix hr' ha

/-- A sufficiently fueled parent walk preserves increasing positions. -/
theorem chainTo_append_pos (hr : st.Reachable acp₀) {B : Blk sp} (hB : B ∈ st.tree)
    {fuel : Nat} (hf : B.slot < fuel) (tail : Blocks.Chain Info)
    (hp : Blocks.Chain.PosFrom B.slot tail) :
    Blocks.Chain.PosIncreasing (chainTo st.blocks fuel B ++ tail) := by
  induction fuel generalizing B tail with
  | zero => omega
  | succ fuel ih =>
    by_cases hg : B.root = sp.genesisRoot
    · have hgen := (Store.accepted_tree _ _ _ _ hr).2.2.1
      have he := (Store.accepted_tree _ _ _ _ hr).2.1.1 hB hgen hg
      have hslot : B.slot = 0 := congrArg Block.slot he
      simpa [chainTo, hg, Blocks.Chain.PosIncreasing, hslot] using hp
    · obtain he | ⟨P, _, e⟩ :=
        (Relation.ReflTransGen.cases_tail_iff _ _ _).1
          ((Store.accepted_tree _ _ _ _ hr).2.2.2 B hB)
      · exact (hg (congrArg Block.root he)).elim
      have hlt := (Store.accepted_tree _ _ _ _ hr).2.1.2 P e.1 B hB e.2.2
      have hpar : B.parent.bind st.blocks = some P := by
        rw [e.2.2, Option.bind_some]; exact e.1
      have hp' : Blocks.Chain.PosFrom P.slot (headerOf sp B :: tail) := ⟨hlt, hp⟩
      simpa only [chainTo, ite_eq_right hg, hpar, List.append_assoc, List.singleton_append] using
        ih e.1 (by omega) (headerOf sp B :: tail) hp'

/-- A sufficiently fueled parent walk links to genesis and preserves increasing positions
(`chainTo_append_pos`). The hash/encoding identity is isolated in `hhash`, so root tagging can
change independently. -/
theorem chainTo_append_valid (hr : st.Reachable acp₀) (hash : Blocks.Header Info → Nat)
    (hhash : ∀ X ∈ st.tree, X.root ≠ sp.genesisRoot →
      parentRef sp.genesisRoot (some X.root) = .digest (hash (headerOf sp X)))
    {B : Blk sp} (hB : B ∈ st.tree) {fuel : Nat} (hf : B.slot < fuel)
    (tail : Blocks.Chain Info)
    (hl : Blocks.Chain.LinkedFrom hash (parentRef sp.genesisRoot (some B.root)) tail)
    (hp : Blocks.Chain.PosFrom B.slot tail) :
    Blocks.Chain.Linked hash (chainTo st.blocks fuel B ++ tail) ∧
      Blocks.Chain.PosIncreasing (chainTo st.blocks fuel B ++ tail) := by
  refine ⟨?_, chainTo_append_pos hr hB hf tail hp⟩
  clear hp
  induction fuel generalizing B tail with
  | zero => omega
  | succ fuel ih =>
    by_cases hg : B.root = sp.genesisRoot
    · simpa [chainTo, hg, parentRef, Blocks.Chain.Linked] using hl
    · obtain he | ⟨P, _, e⟩ :=
        (Relation.ReflTransGen.cases_tail_iff _ _ _).1
          ((Store.accepted_tree _ _ _ _ hr).2.2.2 B hB)
      · exact (hg (congrArg Block.root he)).elim
      have hlt := (Store.accepted_tree _ _ _ _ hr).2.1.2 P e.1 B hB e.2.2
      have hpar : B.parent.bind st.blocks = some P := by
        rw [e.2.2, Option.bind_some]; exact e.1
      have hl' : Blocks.Chain.LinkedFrom hash (parentRef sp.genesisRoot (some P.root))
          (headerOf sp B :: tail) := by
        refine ⟨?_, ?_⟩
        · change parentRef sp.genesisRoot B.parent = _
          rw [e.2.2]
        · rwa [hhash B hB hg] at hl
      simpa only [chainTo, ite_eq_right hg, hpar, List.append_assoc, List.singleton_append] using
        ih e.1 (by omega) (headerOf sp B :: tail) hl'

/-- The blocks from genesis (excluded) to `B`, oldest first: `chainTo` before taking headers. -/
noncomputable def blocksTo (blocks : Nat → Option (Blk sp)) : Nat → Blk sp → List (Blk sp)
  | 0, _ => []
  | fuel + 1, B =>
      if B.root = sp.genesisRoot then []
      else
        (match B.parent.bind blocks with
          | some Bp => blocksTo blocks fuel Bp
          | none => []) ++ [B]

/-- `blocksTo` without fuel is empty. -/
theorem blocksTo_zero (blocks : Nat → Option (Blk sp)) (B : Blk sp) :
    blocksTo blocks 0 B = [] := by rfl

/-- `blocksTo` walks one parent step and appends the block. -/
theorem blocksTo_succ (blocks : Nat → Option (Blk sp)) (fuel : Nat) (B : Blk sp) :
    blocksTo blocks (fuel + 1) B =
      if B.root = sp.genesisRoot then []
      else
        (match B.parent.bind blocks with
          | some Bp => blocksTo blocks fuel Bp
          | none => []) ++ [B] := by rfl

/-- The headers of `blocksTo` are `chainTo`. -/
theorem blocksTo_map (blocks : Nat → Option (Blk sp)) :
    ∀ fuel B, (blocksTo blocks fuel B).map (headerOf sp) = chainTo blocks fuel B
  | 0, B => by rw [blocksTo_zero, chainTo, List.map_nil]
  | fuel + 1, B => by
    rw [blocksTo_succ, chainTo]
    split_ifs
    · rfl
    · rw [List.map_append, List.map_singleton]
      cases B.parent.bind blocks with
      | none => rfl
      | some Bp => rw [blocksTo_map blocks fuel Bp]

/-- No block of a parent walk is genesis, for any block map and tip. -/
theorem blocksTo_nonroot (blocks : Nat → Option (Blk sp)) :
    ∀ fuel (B X : Blk sp), X ∈ blocksTo blocks fuel B → X.root ≠ sp.genesisRoot
  | 0, B, X, h => by simp [blocksTo_zero] at h
  | fuel + 1, B, X, h => by
    rw [blocksTo_succ] at h
    split_ifs at h with hg
    · simp at h
    · rcases List.mem_append.1 h with h | h
      · cases hp : B.parent.bind blocks with
        | none => simp [hp] at h
        | some P => exact blocksTo_nonroot blocks fuel P X (by simpa only [hp] using h)
      · exact List.mem_singleton.1 h ▸ hg

/-- Every block of the parent walk from a held tip of a reachable store is a held ancestor. -/
theorem mem_blocksTo (hr : st.Reachable acp₀) {B : Blk sp} (hB : B ∈ st.tree)
    {fuel : Nat} {X : Blk sp} (hX : X ∈ blocksTo st.blocks fuel B) :
    X ∈ st.tree ∧ st.Anc X B := by
  induction fuel generalizing B with
  | zero => simp [blocksTo_zero] at hX
  | succ fuel ih =>
    rw [blocksTo_succ] at hX
    split_ifs at hX with hg
    · simp at hX
    · rcases List.mem_append.1 hX with hX | hX
      · cases hp : B.parent.bind st.blocks with
        | none => simp [hp] at hX
        | some P =>
          obtain ⟨r, hpar, hP⟩ := Option.bind_eq_some_iff.1 hp
          have hPr := hr.blocks_root hP
          have hPt : P ∈ st.tree := by change st.blocks P.root = some P; rwa [hPr]
          obtain ⟨hXt, hXP⟩ := ih hPt (by simpa only [hp] using hX)
          exact ⟨hXt, hXP.tail ⟨hPt, hB, hpar.trans (congrArg some hPr.symm)⟩⟩
      · obtain rfl := List.mem_singleton.1 hX
        exact ⟨hB, .refl⟩

/-- Every emitted header belongs to a non-genesis ancestor held in the store. -/
theorem mem_chainTo (hr : st.Reachable acp₀) {B : Blk sp} (hB : B ∈ st.tree)
    {fuel : Nat} {h : Blocks.Header Info} (hh : h ∈ chainTo st.blocks fuel B) :
    ∃ X ∈ st.tree, st.Anc X B ∧ X.root ≠ sp.genesisRoot ∧ h = headerOf sp X := by
  rw [← blocksTo_map] at hh
  obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hh
  obtain ⟨hXt, hXB⟩ := mem_blocksTo hr hB hX
  exact ⟨X, hXt, hXB, blocksTo_nonroot _ _ _ _ hX, rfl⟩

end Consensus.Goldilocks.Simulation

end
