module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.Sigma
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Client

@[expose] public section

/-! # Goldilocks FG store: the duties

fg.tex Figure "FG: handlers, finality caches and frame": `fg_attest` (the only FG function that
reads the client record) and `proposal_attestations`. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} (st : Store P ACP)

/-- `fg_attest(Σ, Λ, fg_confirmed)` for validator `v`: the height pair comes from the source's
state `Σ.σ[fg_confirmed]` and the finality pair from its entry state `σ_e = Σ.σ[T_c]`, with
`T_c` the source state's `T_h`; returns the attestation and the new record, or `none`. (The
client reads `(h_c, T_c)` as `(σ_e.h, σ_e.T_h)`, which equal the source state's height and
entry at a held source.) -/
def attest (Λ : FG.Record) (v : Fin P.n) (src : NodeBlock P ACP) :
    Option (FG.Att P.n × FG.Record) :=
  Λ.createAtt v (st.σ (st.σ src.root).Th)

/-- An attestation is on the chain of `H`: some accepted block at or below `H` carries it. -/
def OnChain (H : NodeBlock P ACP) (a : FG.Att P.n) : Prop :=
  ∃ X ∈ st.tree, st.Anc X H ∧ a ∈ X.fgPayload

open Classical in
/-- `proposal_attestations(Σ, H)`: the attestations of the pool that are valid against
`Σ.σ[H]` and not on `H`'s chain, in the order of the pool. -/
noncomputable def proposalAttestations (H : NodeBlock P ACP) : List (FG.Att P.n) :=
  st.atts.filter (fun a => (st.σ H.root).validAtt a ∧ ¬ st.OnChain H a)

end Consensus.Goldilocks.Store

end
