module
public import AvailableChainFGSA.Proofs.Port.Carry -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.Port.LocalReads -- shake: keep (axioms)

public section

namespace AvailableChain.FGSA.Next.HelperTests

private def ancestor : Block := .node .genesis 1 ⟨1⟩ 0
private def floor : Block := .node ancestor 2 ⟨2⟩ 0
private def head : Block := .node floor 3 ⟨3⟩ 0
private def rival : Block := .node .genesis 1 ⟨4⟩ 0
private def vote (i : Fin 3) (B : Block) : GridCO.Wire 3 .root := ⟨.seat 3 i, .head B.root⟩
private def v : GridCO.State 3 .root :=
  { GridCO.initial 3 .root with
    now := 0
    blocks := [.genesis, ancestor, floor, head, rival]
    votes := [vote 0 ancestor, vote 1 floor, vote 2 head] }
private def kept : List (GridCO.Wire 3 .root) :=
  v.votes.filter (fun o => (GridCO.resolvedHead? v o).any (Block.preceq floor))

/-- Regression for `port_clean_filter_score`: equality starts at F. -/
example : kept = [vote 1 floor, vote 2 head] ∧
    GridCO.goldfishScore v.blocks kept kept floor =
      GridCO.goldfishScore v.blocks v.votes v.votes floor ∧
    GridCO.goldfishScore v.blocks kept kept ancestor = 2 ∧
    GridCO.goldfishScore v.blocks v.votes v.votes ancestor = 3 := by decide +kernel

/-- Regression for `port_confirmation_filter`: non-equivocation is necessary
when the projected support pool also supplies the raw argument. -/
example :
    let raw := [vote 0 ancestor, vote 0 floor]
    let sup := raw.filter (fun o => (GridCO.resolvedHead? v o).any (Block.preceq floor))
    GridCO.goldfishScore v.blocks raw raw head = 1 ∧
    GridCO.goldfishScore v.blocks sup sup head = 0 := by decide +kernel

/-- Regression for `port_ghost_congr`: equal score/root ties remain ambiguous. -/
example :
    let twin := Block.node floor 3 head.root 9
    GridCO.ghost floor [head, twin] (fun _ => 1) (fun _ => true) = floor := by
  decide +kernel

private def collision : Block := .node floor 3 ancestor.root 9
private def ambiguous : GridCO.State 3 .root :=
  { v with blocks := v.blocks ++ [collision] }

/-- Regression for `port_resolvedHead_filter`: the cumulative collision stays
unresolved even though only one candidate survives the prefix projection. -/
example : GridCO.resolvedHead? { ambiguous with
    blocks := ambiguous.blocks.filter (Block.preceq floor)
    headDomain := some (GridCO.resolutionTree ambiguous) } (vote 0 ancestor) = none ∧
    Block.findByRoot? (ambiguous.blocks.filter (Block.preceq floor)) ancestor.root =
      some collision := by decide +kernel

private abbrev p : Params :=
  { Δ := 1, n := 3, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun _ => ⟨99⟩ }
private def projected : GridCO.State 3 .root :=
  { v with
    blocks := v.blocks.filter (Block.preceq floor)
    headDomain := some (GridCO.resolutionTree v) }

/-- Regression for `port_releaseCount_eq`: release counts can differ for an
incompatible target, while the compatible retained target has equal counts. -/
example : GridCO.releaseCount p.toParams.engine v 3 rival = 3 ∧
    GridCO.releaseCount p.toParams.engine projected 3 rival = 2 ∧
    GridCO.releaseCount p.toParams.engine v 3 head =
      GridCO.releaseCount p.toParams.engine projected 3 head := by decide +kernel

/-- Regression for `port_confirmation_filter`: both gate reads confirm F,
although the strict-ancestor vote is absent from the projected clean pool. -/
example : GridCO.confirmationFrom p.toParams.engine floor v 3 = some floor ∧
    GridCO.confirmationFrom p.toParams.engine floor projected 3 = some floor := by
  decide +kernel

private def fgProposal : SimplexFG.FGBlock (Fin 3) := .node .genesis 4 ⟨8⟩ 0 []
private def fgOther : SimplexFG.FGBlock (Fin 3) := .node .genesis 2 ⟨9⟩ 0 []
private def carried : HeadWire 3 := ⟨.seat (.head 3) 0, fgOther.root⟩
private def named : NamedProposal 3 :=
  .node .genesis 4 fgProposal.root (eraseFG fgProposal).body [carried] [carried] []
private def retained : State 3 :=
  { base := { v with votes := [], blocks := v.blocks ++ [eraseFG fgOther, eraseFG fgProposal] }
    fg := { SimplexFG.Store.init with TF := {.genesis, fgProposal, fgOther} }
    proposals := [⟨.proposer 4, .proposal named⟩] }
private def lost : State 3 := { retained with fg := { retained.fg with F := fgOther } }

/-- Regression for `port_retained_raw_carry`: held metadata alone is not a
retention proof. Removing the proposal also removes its raw vote. -/
example : headVotesNext p retained 4 = [baseVote carried] ∧
    headVotesNext p lost 4 = [] ∧ headVotes p lost 4 = [] ∧
    Legacy.headVotes p lost 4 = [baseVote carried] ∧
    headSupportNext p retained 4 = [baseVote carried] ∧
    headSupportNext p lost 4 = [] := by decide +kernel

/-- Regression for `port_lease_projection`: the ancestor row can be removed
without changing the retained target's deadline. -/
example :
    let st : State 3 := { base := { v with obligations := [(ancestor, 1, 10), (head, 1, 20)] } }
    leaseOf { st with base := { st.base with
      obligations := st.base.obligations.filter (fun row => Block.preceq floor row.1) } } head =
      some 20 := by decide +kernel

/-- Instantiates `port_support_filter_score` at genesis; unresolved votes
can be removed from support without changing any score for the fixed raw pool. -/
theorem port_helpers_genesis_projection {n : Nat} (v : GridCO.State n .root)
    (raw support : List (GridCO.Wire n .root)) (B : Block) :
    GridCO.goldfishScoreOn (GridCO.resolutionTree v) v.blocks raw
      (support.filter (fun o => (GridCO.resolvedHead? v o).any (Block.preceq .genesis))) B =
    GridCO.goldfishScoreOn (GridCO.resolutionTree v) v.blocks raw support B :=
  port_support_filter_score v raw support .genesis B (block_genesis_preceq B)

#print axioms port_helpers_genesis_projection

end AvailableChain.FGSA.Next.HelperTests
end
