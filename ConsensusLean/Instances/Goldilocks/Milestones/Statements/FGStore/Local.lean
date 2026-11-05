module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Handlers
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.Duties
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.State
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Frame

@[expose] public section

/-! # Goldilocks milestone FGStore, part 1: one FG store (statements)

Transcribed from `specs/goldilocks/tex/goldilocks-claims.tex`, the
single-store nodes of the FG store level, against `Spec/FG/Store`: G0.1 (store), F.2 at the
store, G0.3 (cache invariants), the FG kernel of the frame step,
G0.4 (height) (the frame realization) and G0.2 (c), (h) at the store (`EntryStateOfSource`).
Every statement is about the FG states that the handlers reach (`Store.Reachable`): one node, no
time, no AC. The multi-node store statements are over FG traces (`Spec/FG/Store/Trace`): G1.4
and the core of G1.10 in part 2 (`FGStore/Trace`), G1.6–G1.8 and G1.9 (a) in part 3
(`FGStore/Service`).

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Store

variable (P : Params) (ACP : Type)

/-- The blocks of `c` (oldest first) are linked from genesis: the first names the genesis root
as its parent, and each later one names the previous block's root. -/
def LinkedFromGenesis (c : List (NodeBlock P ACP)) : Prop :=
  c.map Block.parent = ((P.genesisRoot :: c.map Block.root).take c.length).map some

/-- **G0.1 (store), the chain state of an accepted block is its chain's fold.** In a reachable
FG state, every accepted block `B` has a chain in `Σ.T`: blocks linked from genesis, oldest
first, ending at `B` (empty for genesis); and `Σ.σ[B]` is the fold of `state_transition` over
that chain (`FG.FGParams.chainState`). -/
def ChainStateOfChain : Prop :=
  ∀ (acp₀ : ACP) (st : Store P ACP), st.Reachable acp₀ → ∀ B ∈ st.tree,
    ∃ c : List (NodeBlock P ACP), (∀ X ∈ c, X ∈ st.tree) ∧ LinkedFromGenesis P ACP c ∧
      ((c = [] ∧ B = P.genesisBlock acp₀) ∨ c.getLast? = some B) ∧
      P.fg.chainState (c.map Block.fgView) = some (st.σ B.root)

/-- **F.2 at the store, the accepted tree.** In a reachable FG state, `Σ.T` is finite and
coherent (roots injective, slots strictly increasing along parent edges), contains genesis, and
every block of it extends genesis. -/
def AcceptedTree : Prop :=
  ∀ (acp₀ : ACP) (st : Store P ACP), st.Reachable acp₀ →
    st.tree.Finite ∧ Coherent st.tree ∧ P.genesisBlock acp₀ ∈ st.tree ∧
      ∀ B ∈ st.tree, st.Anc (P.genesisBlock acp₀) B

/-- **F.2 at the store, the tree only grows.** From a reachable FG state, an accepted block is
added and nothing else changes in the tree; a processed attestation leaves the tree unchanged.
-/
def TreeGrows : Prop :=
  ∀ (acp₀ : ACP) (st : Store P ACP), st.Reachable acp₀ →
    (∀ B st', st.onBlock B = some st' → st'.tree = insert B st.tree) ∧
      ∀ a, (st.onAttestation a).tree = st.tree

/-- **G0.3, cache invariants.** In a reachable FG state: `Σ.F` and `Σ.J` are accepted and
`Σ.F ⪯ Σ.J`; `(Σ.J, Σ.h_j)` is the justification of an accepted state; `Σ.h_max` is the greatest
accepted state height; `Σ.F` is the finalization of an accepted state. -/
def CacheInvariants : Prop :=
  ∀ (acp₀ : ACP) (st : Store P ACP), st.Reachable acp₀ →
    st.F ∈ st.tree ∧ st.J ∈ st.tree ∧ st.Anc st.F st.J ∧
      (∃ B ∈ st.tree, (st.σ B.root).J = st.J.root ∧ (st.σ B.root).hj = st.hj) ∧
      (∀ B ∈ st.tree, (st.σ B.root).h ≤ st.hmax) ∧
      (∃ B ∈ st.tree, (st.σ B.root).h = st.hmax) ∧
      ∃ B ∈ st.tree, (st.σ B.root).F = st.F.root

/-- **The FG kernel of the frame step.** From a reachable FG state, accepting `B` is a frame
step `fg_to_ac(Σ) ⊑_B fg_to_ac(Σ')` (G0.3 (frame)), and processing an attestation leaves the
frame unchanged (`fg_on_attestation` writes only the pool). -/
def AcceptIsFrameStep : Prop :=
  ∀ (acp₀ : ACP) (st : Store P ACP), st.Reachable acp₀ →
    (∀ B st', st.onBlock B = some st' → FrameStep st.toFrame B st'.toFrame) ∧
      ∀ a, (st.onAttestation a).toFrame = st.toFrame

/-- **G0.4 (height), frame realization.** In a reachable FG state, `fg_to_ac(Σ)` is a
well-formed frame (G0.4 (frame)), and the head height floor is `h_max` or `h_max − 1` (this
clause holds by the definition of `head_height_floor`; it is kept as the claims state it). -/
def FrameRealization : Prop :=
  ∀ (acp₀ : ACP) (st : Store P ACP), st.Reachable acp₀ →
    FrameOK st.toFrame ∧ (st.headHeightFloor = st.hmax ∨ st.headHeightFloor = st.hmax - 1)

/-- **G0.2 (c) and (h) at the store, the entry state of a source.** In a reachable FG state, for
every accepted `B` the block with root `σ[B].T_h` (the entry of `B`'s height) is accepted, is an
ancestor of `B`, and its state has `B`'s height and entry: `σ[σ[B].T_h].h = σ[B].h` and
`σ[σ[B].T_h].T_h = σ[B].T_h`. So `fg_attest`'s `(h_c, T_c)`, read as `(σ_e.h, σ_e.T_h)` of the
entry state `σ_e` (`Store.attest`), is fg.tex's `(Σ.σ[src].h, Σ.σ[src].T_h)`. Likewise the
finalized and justified roots of `σ[B]` name accepted ancestors of `B`. -/
def EntryStateOfSource : Prop :=
  ∀ (acp₀ : ACP) (st : Store P ACP), st.Reachable acp₀ → ∀ B ∈ st.tree,
    (∃ E ∈ st.tree, E.root = (st.σ B.root).Th ∧ st.Anc E B ∧
      (st.σ E.root).h = (st.σ B.root).h ∧ (st.σ E.root).Th = (st.σ B.root).Th) ∧
    (∃ X ∈ st.tree, X.root = (st.σ B.root).F ∧ st.Anc X B) ∧
    (∃ X ∈ st.tree, X.root = (st.σ B.root).J ∧ st.Anc X B)

/-- The statements of FGStore part 1 at parameters `P` and AC payload type `ACP`. -/
structure FGStoreLocalAt : Prop where
  chainStateOfChain : ChainStateOfChain P ACP
  acceptedTree : AcceptedTree P ACP
  treeGrows : TreeGrows P ACP
  cacheInvariants : CacheInvariants P ACP
  acceptIsFrameStep : AcceptIsFrameStep P ACP
  frameRealization : FrameRealization P ACP
  entryStateOfSource : EntryStateOfSource P ACP

/-- **FGStore, part 1.** The single-store statements hold at every parameter and AC payload
type. Parts 2 and 3 (`FGStoreTrace`, `FGStoreService`) are separate bundles, each a statement
of `Challenge`. -/
def FGStoreLocal : Prop := ∀ (P : Params) (ACP : Type), FGStoreLocalAt P ACP

end Consensus.Goldilocks.Store

end
