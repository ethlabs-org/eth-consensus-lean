module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.State
public import ConsensusLean.Instances.Goldilocks.Spec.Common.Params
public import ConsensusLean.Instances.Goldilocks.Spec.Common.Tree

@[expose] public section

/-! # Goldilocks FG store: the FG state `Σ`

The FG state of a node (fradamt-agent/goldilocks `spec/shared/composition.tex` §"State";
`spec/shared/fg.tex` §"Finality caches and frame"):
`Σ = (T, σ[·], F, J, h_j, h_max, attestations)`. The tree `Σ.T` is kept by root, the way the
store tests it (a block enters only when no held block has its root), so a held root names one
block; `Σ.σ` is kept by root too. `Σ.F` and `Σ.J` are blocks of the tree. The FG reads a block
through `Block.fgView` (root, slot, proposer, attestations) before `state_transition`, and its
parameters `Params.fg` are derived from the shared parameters. -/

namespace Consensus.Goldilocks

/-- The FG parameters derived from the shared parameters: `n`, `δ_t`, and genesis root. -/
def Params.fg (P : Params) : FG.FGParams := ⟨P.n, P.hn, P.δt, P.genesisRoot⟩

/-- A node block: its FG payload is the attestation list. -/
abbrev NodeBlock (P : Params) (ACP : Type) := Block P.n (List (FG.Att P.n)) ACP

/-- What the FG reads of a block: root, slot, proposer and the attestation list (order and
repeats kept). -/
def Block.fgView {n : Nat} {ACP : Type} (B : Block n (List (FG.Att n)) ACP) : FG.FGBlock n :=
  ⟨B.root, B.slot, B.proposer, B.fgPayload⟩

/-- Genesis: the genesis root, no parent, slot `0`, input `0`, no attestations, the AC payload
`acp₀`. Its proposer is the fixed index zero, independent of leader selection.
(Its proposer, input and AC payload are never read by the transition.) -/
def Params.genesisBlock (P : Params) {ACP : Type} (acp₀ : ACP) : NodeBlock P ACP :=
  ⟨P.genesisRoot, none, 0, ⟨0, P.hn⟩, 0, [], acp₀⟩

/-- The FG state `Σ`. -/
structure Store (P : Params) (ACP : Type) where
  /-- `Σ.T` by root: the accepted block with each root, if any. -/
  blocks : Nat → Option (NodeBlock P ACP)
  /-- `Σ.σ` by root: the chain state of the accepted block with each root (read only for
  held roots). -/
  σ : Nat → FG.ChainState P.n
  /-- `Σ.F`, the accepted finalization. -/
  F : NodeBlock P ACP
  /-- `Σ.J`, the justification cache (fg.tex: the lex-greatest accepted justification that
  extends `Σ.F`). -/
  J : NodeBlock P ACP
  /-- `Σ.h_j`, the height of `Σ.J`. -/
  hj : Nat
  /-- `Σ.h_max`, the greatest accepted state height. -/
  hmax : Nat
  /-- `Σ.attestations`: the processed attestations, one copy of each, in the order of first
  acceptance. -/
  atts : List (FG.Att P.n)

namespace Store

variable {P : Params} {ACP : Type} (st : Store P ACP)

/-- The tree `Σ.T` as a set of blocks. -/
def tree : Set (NodeBlock P ACP) := {B | st.blocks B.root = some B}

/-- Ancestry inside `Σ.T`. -/
abbrev Anc : NodeBlock P ACP → NodeBlock P ACP → Prop := Goldilocks.Anc st.tree

/-- The initial FG state: genesis alone, `F = J = genesis`, `h_j = 0`, `h_max = 1`, the
initial chain state, an empty pool. -/
def init (acp₀ : ACP) : Store P ACP where
  blocks r := if r = P.genesisRoot then some (P.genesisBlock acp₀) else none
  σ _ := FG.ChainState.init P.fg
  F := P.genesisBlock acp₀
  J := P.genesisBlock acp₀
  hj := 0
  hmax := 1
  atts := []

end Store

end Consensus.Goldilocks

end
