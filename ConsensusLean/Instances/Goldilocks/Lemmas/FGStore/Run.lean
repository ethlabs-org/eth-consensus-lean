module
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Trace
public import ConsensusLean.Instances.Goldilocks.Statements.FGSafety
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame

public section

/-! # Goldilocks FG store: what an FG trace gives at one honest node

Over an FG trace with its contract (`FGLocalRun`), at an honest node: the store before every
cut is reachable (`store_reachable`), so part 1 applies to it; a block of its tree other than
genesis was accepted by the node at an earlier cut (`tree_accepted`); and the attestations that
an honest validator signs before a cut are the output of one client run from the empty record
over entry states of chains (`signed_run`), so client safety (G0.5) applies to them. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

/-- The store of an honest node before every cut is reachable. -/
theorem store_reachable (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) (i : Nat) :
    (tr.store y i).Reachable acp₀ := by
  sorry

/-- A block of an honest node's tree before cut `i` is genesis or was accepted by the node at
an earlier cut. -/
theorem tree_accepted (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {B : NodeBlock P ACP} (hB : B ∈ (tr.store y i).tree) :
    B = P.genesisBlock acp₀ ∨ ∃ k < i, tr.AcceptAt y k B := by
  sorry

/-- The attestations that an honest validator signs before cut `i` are among the output of one
client run from the empty record over entry states of chains. -/
theorem signed_run (hr : FGLocalRun acp₀ H U tr) {v : Fin P.n} (hv : v ∈ H) (i : Nat) :
    ∃ inputs, FG.EntryInputs P.fg inputs ∧
      ∀ j < i, ∀ a, tr.SignAt v j a → a ∈ (FG.Record.run v FG.Record.empty inputs).2 := by
  sorry

end Consensus.Goldilocks.Store

end
