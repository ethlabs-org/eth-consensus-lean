module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.Sigma

@[expose] public section

/-! # Goldilocks FG store: the labels of FG calls

An FG call of a node with what it observes (decomposition §1.5: the component calls are the
cuts of a run; claims C0.4, C0.5). `Spec/Node` records every FG call of a handler by its label;
the FG traces of `Spec/FG/Store` (FGStore part 2) use the same labels, so neither depends on
the other. -/

namespace Consensus.Goldilocks

/-- An FG call of the node, with what it observes: `fg_on_block(Σ, B)` and whether the FG
accepted `B`; `fg_on_attestation(Σ, a)`; `fg_attest(Σ, Λ, src)` and the attestation it signed,
`none` when the record refused. A refused `fg_on_block` is a call with no write, so it is a
label (`accepted := false`). -/
inductive FGLabel (P : Params) (ACP : Type) where
  /-- `fg_on_block(Σ, B)`: accepted, or refused with no write. -/
  | block (B : NodeBlock P ACP) (accepted : Bool)
  /-- `fg_on_attestation(Σ, a)`. -/
  | attestation (a : FG.Att P.n)
  /-- `fg_attest(Σ, Λ, src)` with the attestation it signed, if any. -/
  | attest (src : NodeBlock P ACP) (signed : Option (FG.Att P.n))

end Consensus.Goldilocks

end
