module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Interface
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Tree

public section

/-! # Engine output chains

The parent walk is independent of its fuel above the block's slot. Ancestry in a reachable
store therefore gives structural prefix inclusion of the emitted header chains. These facts
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

/-- A sufficiently fueled parent walk links to genesis and preserves increasing positions.
The hash/encoding identity is isolated in `hhash`, so root tagging can change independently. -/
theorem chainTo_append_valid (hr : st.Reachable acp₀) (hash : Blocks.Header Info → Nat)
    (hhash : ∀ X ∈ st.tree, X.root ≠ sp.genesisRoot →
      parentRef sp.genesisRoot (some X.root) = .digest (hash (headerOf sp X)))
    {B : Blk sp} (hB : B ∈ st.tree) {fuel : Nat} (hf : B.slot < fuel)
    (tail : Blocks.Chain Info)
    (hl : Blocks.Chain.LinkedFrom hash (parentRef sp.genesisRoot (some B.root)) tail)
    (hp : Blocks.Chain.PosFrom B.slot tail) :
    Blocks.Chain.Linked hash (chainTo st.blocks fuel B ++ tail) ∧
      Blocks.Chain.PosIncreasing (chainTo st.blocks fuel B ++ tail) := by
  induction fuel generalizing B tail with
  | zero => omega
  | succ fuel ih =>
    by_cases hg : B.root = sp.genesisRoot
    · have hgen := (Store.accepted_tree _ _ _ _ hr).2.2.1
      have he := (Store.accepted_tree _ _ _ _ hr).2.1.1 hB hgen hg
      have hslot : B.slot = 0 := congrArg Block.slot he
      simpa [chainTo, hg, parentRef, Blocks.Chain.Linked, Blocks.Chain.PosIncreasing,
        hslot] using And.intro hl hp
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
      have hp' : Blocks.Chain.PosFrom P.slot (headerOf sp B :: tail) := ⟨hlt, hp⟩
      simpa only [chainTo, ite_eq_right hg, hpar, List.append_assoc, List.singleton_append] using
        ih e.1 (by omega) (headerOf sp B :: tail) hl' hp'

/-- Every emitted header belongs to a non-genesis ancestor held in the store. -/
theorem mem_chainTo (hr : st.Reachable acp₀) {B : Blk sp} (hB : B ∈ st.tree)
    {fuel : Nat} {h : Blocks.Header Info} (hh : h ∈ chainTo st.blocks fuel B) :
    ∃ X ∈ st.tree, st.Anc X B ∧ X.root ≠ sp.genesisRoot ∧ h = headerOf sp X := by
  induction fuel generalizing B with
  | zero => simp [chainTo] at hh
  | succ fuel ih =>
    simp only [chainTo] at hh
    split_ifs at hh with hg
    · simp at hh
    · rcases List.mem_append.1 hh with hh | hh
      · cases hp : B.parent.bind st.blocks with
        | none => simp [hp] at hh
        | some P =>
          obtain ⟨r, hpar, hP⟩ := Option.bind_eq_some_iff.1 hp
          have hPr := hr.blocks_root hP
          have hPt : P ∈ st.tree := by change st.blocks P.root = some P; rwa [hPr]
          obtain ⟨X, hX, hXP, hXg, hx⟩ := ih hPt (by simpa only [hp] using hh)
          exact ⟨X, hX, hXP.tail ⟨hPt, hB, hpar.trans (congrArg some hPr.symm)⟩, hXg, hx⟩
      · exact ⟨B, hB, .refl, hg, List.mem_singleton.1 hh⟩

end Consensus.Goldilocks.Simulation

end
