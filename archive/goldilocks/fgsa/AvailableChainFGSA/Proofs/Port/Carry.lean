module
public import AvailableChainFGSA.Proofs.Port.Support -- shake: keep (re-export)
public import AvailableChainFGSA.Proofs.Head.Score

public section

namespace AvailableChain.FGSA.Next

/-- Replaces the proposal-row step of `fgsa_scoreRun_carried_raw_subset`.
Stored metadata and proposal retention are separate premises. -/
theorem port_retained_proposal_row (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n)
    (hw : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ st.proposals)
    (hs : N.slot = s) (hN : ∃ B ∈ tree p st, eraseFG B = N.erase) :
    (N.raw, N.support) ∈ proposalsAtNext p st s := by
  apply List.mem_filterMap.mpr
  refine ⟨⟨.proposer s, .proposal N⟩, hw, ?_⟩
  change (if N.slot = s ∧ ∃ B ∈ tree p st, eraseFG B = N.erase then
    some (N.raw, N.support) else none) = some (N.raw, N.support)
  simp [hs, hN]

/-- Replaces `fgsa_scoreRun_carried_raw_subset`. A retained proposal supplies
its raw votes even when the destination did not admit each vote separately. -/
theorem port_retained_raw_carry (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n)
    (hw : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ st.proposals)
    (hs : N.slot = s) (hN : ∃ B ∈ tree p st, eraseFG B = N.erase)
    (hl : ∀ o ∈ N.raw.map baseVote, GridCO.headLabel? o = some (s - 1)) :
    N.raw.map baseVote ⊆ headVotesNext p st s := by
  intro o ho
  apply List.mem_eraseDups.mpr
  apply List.mem_append.mpr
  right
  apply List.mem_filter.mpr
  exact ⟨List.mem_flatMap.mpr
    ⟨(N.raw, N.support), port_retained_proposal_row p st s N hw hs hN, ho⟩,
    by simpa using hl o ho⟩

/-- Replaces `scoreRun_carried_support`. Both the proposal and the resolved
head must be retained. The cumulative resolver preserves ambiguity. -/
theorem port_retained_support_carry (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n)
    (hw : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ st.proposals)
    (hs : N.slot = s) (hN : ∃ B ∈ tree p st, eraseFG B = N.erase)
    (o : GridCO.Wire p.n .root) (ho : o ∈ N.support.map baseVote)
    (hl : GridCO.headLabel? o = some (s - 1)) (H : Block)
    (hr : GridCO.resolvedHead? st.base o = some H)
    (hH : ∃ B ∈ tree p st, eraseFG B = H) (hv : H.slot ≤ s - 1) :
    o ∈ headSupportNext p st s := by
  apply List.mem_eraseDups.mpr
  apply List.mem_append.mpr
  right
  apply List.mem_filter.mpr
  exact ⟨List.mem_flatMap.mpr
    ⟨(N.raw, N.support), port_retained_proposal_row p st s N hw hs hN, ho⟩,
    by simp [hl, hr, hH, hv]⟩

/-- Feeds the repaired `fgsa_score_eq_on_run`. `F_dst ⪯ N` retains the proposal;
the candidate floor is separate. Admission, labels, and the store erasure law
are supplied independently. Extra raw votes must be from capped source seats. -/
theorem port_retained_carry_score (p : Params) (src dst : State p.n) (s : Slot)
    (N : NamedProposal p.n) (D : Block)
    (hw : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ dst.proposals)
    (hs : N.slot = s) (hheld : N.erase ∈ dst.base.blocks)
    (hFN : Block.Preceq (eraseFG dst.fg.F) N.erase)
    (hT : ∀ H ∈ dst.base.blocks, Block.Preceq (eraseFG dst.fg.F) H →
      ∃ B ∈ tree p dst, eraseFG B = H)
    (hl : ∀ o ∈ N.raw.map baseVote, GridCO.headLabel? o = some (s - 1))
    (hextra : ∀ o ∈ headVotesNext p dst s, ∀ i, GridCO.headSeat? o = some i →
      o ∉ N.raw.map baseVote → GridCO.equivocates (N.raw.map baseVote) i = true)
    (hinc : ∀ B, Block.Preceq D B → ∀ i,
      GridCO.equivocates (N.raw.map baseVote) i = false →
      Gen.AC.Root.poolSupports src.base.blocks (N.support.map baseVote) i B =
        Gen.AC.Root.poolSupports dst.base.blocks (headSupportNext p dst s) i B) :
    GridCO.voterCount (N.raw.map baseVote) = GridCO.voterCount (headVotesNext p dst s) ∧
    ∀ B, Block.Preceq D B →
      GridCO.goldfishScore src.base.blocks (N.raw.map baseVote) (N.support.map baseVote) B =
        GridCO.goldfishScore dst.base.blocks (headVotesNext p dst s)
          (headSupportNext p dst s) B := by
  have hraw := port_retained_raw_carry p dst s N hw hs (hT _ hheld hFN) hl
  have h := fgsa_score_eq_on_retained_suffix p src dst D _ _ _ _ hraw hextra hinc
  exact ⟨h.2.2.1, h.2.2.2⟩

end AvailableChain.FGSA.Next
end
