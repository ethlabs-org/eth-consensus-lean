module
public import AvailableChainFGSA.Proofs.Port.Resolution -- shake: keep (examples)

public section

namespace AvailableChain.FGSA.Next.ResolutionTests

open AvailableChain.SimplexFG

/-- [pinned spec 1120–1150] The initial store has no proposer support, also at slot 0. -/
theorem initial_empty : proposerSupportNext (initial 4) 0 = [] := by decide

private def first : FGBlock (Fin 4) := .node .genesis 1 ⟨100⟩ 0 []
private def final : FGBlock (Fin 4) := .node first 2 ⟨101⟩ 0 []
private def above : FGBlock (Fin 4) := .node final 3 ⟨102⟩ 0 []
private def future : FGBlock (Fin 4) := .node above 4 ⟨103⟩ 0 []
private def fork : FGBlock (Fin 4) := .node .genesis 3 ⟨104⟩ 0 []
private def collision : FGBlock (Fin 4) := .node final 3 ⟨100⟩ 0 []
private def vote (i : Fin 4) (r : Slot) (B : FGBlock (Fin 4)) : GridCO.Wire 4 .root :=
  ⟨.seat r i, .head B.root⟩
private def ancestorVote := vote 0 3 first
private def aboveVote := vote 1 3 above
private def finalVote := vote 2 3 final
private def futureVote := vote 3 3 future
private def forkVote := vote 0 3 fork
private def otherSlotVote := vote 1 2 above
private def st : State 4 :=
  { base := { GridCO.initial 4 .root with
      now := 20
      blocks := [.genesis, eraseFG first, eraseFG final, eraseFG above,
        eraseFG future, eraseFG fork]
      votes := [ancestorVote, aboveVote, finalVote, futureVote, forkVote, otherSlotVote]
      voteStamp := [(aboveVote, 17)]
      blockStamp := [(eraseFG above, 17)] }
    fg := { Store.init with TF := {.genesis, first, final, above, future, fork}, F := final } }

/-- [pinned spec 975–1015, 1120–1150] The ancestor is held and resolved, but
is omitted. F and the slot-boundary head are kept in raw-pool order. -/
example : GridCO.resolvedHead? (actView st) ancestorVote = some (eraseFG first) ∧
    proposerSupport st 4 = [aboveVote, finalVote] ∧
    proposerSupportNext st 4 = [aboveVote, finalVote] := by decide

/-- [pinned spec 975–1015] A head one slot above the vote bound is omitted;
a conflicting head and a vote of a different label are also omitted. -/
example : GridCO.resolvedHead? (actView st) futureVote = some (eraseFG future) ∧
    futureVote ∉ proposerSupportNext st 4 ∧
    GridCO.resolvedHead? (actView st) forkVote = none ∧
    forkVote ∉ proposerSupportNext st 4 ∧ otherSlotVote ∉ proposerSupportNext st 4 := by decide

private def ambiguous : State 4 :=
  { st with
    base := { st.base with
      blocks := [.genesis, eraseFG first, eraseFG final, eraseFG collision]
      votes := [ancestorVote] }
    fg := { st.fg with TF := {.genesis, first, final, collision} } }

/-- [pinned spec 975–1015] Cumulative ambiguity survives active and prefix
filtering. A tree-only domain would wrongly resolve the same root. -/
example : GridCO.resolvedHead? ambiguous.base ancestorVote = none ∧
    GridCO.resolvedHead? (actView ambiguous) ancestorVote = none ∧
    proposerSupport ambiguous 4 = [] ∧ proposerSupportNext ambiguous 4 = [] ∧
    Block.findByRoot? (ambiguous.base.blocks.filter
      (Block.preceq (eraseFG ambiguous.fg.F))) first.root = some (eraseFG collision) := by
  decide

private def voteAtCut : State 4 :=
  { st with base := { st.base with voteStamp := [(aboveVote, 18)] } }
private def headAtCut : State 4 :=
  { st with base := { st.base with blockStamp := [(eraseFG above, 18)] } }

/-- [pinned spec 975–1015] A cutoff uses strict stamps for both vote and head.
Proposal support has no cutoff: a stamp at the cutoff still permits support. -/
example : GridCO.resolvedBefore (actView st) aboveVote 18 = true ∧
    GridCO.resolvedBefore (actView voteAtCut) aboveVote 18 = false ∧
    GridCO.resolvedBefore (actView headAtCut) aboveVote 18 = false ∧
    aboveVote ∈ proposerSupportNext voteAtCut 4 ∧
    aboveVote ∈ proposerSupportNext headAtCut 4 := by decide

private def minimal : State 4 :=
  { st with base := { st.base with
      votes := [ancestorVote]
      voteStamp := [(ancestorVote, 1)]
      blockStamp := [(eraseFG first, 1)] } }

/-- [minimal (h) example; pinned spec 975–1015, 1120–1150] Canonical and Next
support are empty. Early receipts do not imply that the head extends F. -/
example : GridCO.resolvedBefore (actView minimal) ancestorVote 18 = true ∧
    proposerSupport minimal 4 = [] ∧ proposerSupportNext minimal 4 = [] := by
  decide

/-- [minimal (h) correspondence] Canonical and Next scores agree, including
at the omitted ancestor. The raw participant set stays fixed. -/
example : GridCO.goldfishScore minimal.base.blocks (proposerVotes minimal 4)
      (proposerSupport minimal 4) (eraseFG first) = 0 ∧
    GridCO.goldfishScore minimal.base.blocks (proposerVotes minimal 4)
      (proposerSupportNext minimal 4) (eraseFG first) = 0 ∧
    GridCO.goldfishScore minimal.base.blocks (proposerVotes minimal 4)
      (proposerSupport minimal 4) (eraseFG final) = 0 ∧
    GridCO.goldfishScore minimal.base.blocks (proposerVotes minimal 4)
      (proposerSupportNext minimal 4) (eraseFG final) = 0 := by decide

end AvailableChain.FGSA.Next.ResolutionTests
end
