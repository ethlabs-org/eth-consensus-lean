module
public import AvailableChainFGSA.Proofs.Head.Walk

public section

namespace AvailableChain.FGSA
open AvailableChain.SimplexFG
open Gen.Pure

/-- P3 F2.3, F1b.4; bp02 §4.2. Class (iii), FG-SA store instance.
DC: Goldfish/Adoption.lean:415–435,441–461. INTENTIONAL: liveRoot and
FJ eligibility replace the SG anchor and eligibility (spec:2519–2525,
2557–2565). Only the stored suffix is required; strict sibling dominance
and majority instantiate the generic walk without a run premise. -/
theorem fgsa_headVote_covers_of_transfer
    (p : Params) (st : State p.n) (s : Slot) (B : Block)
    (hanchor : Block.Compatible (liveRoot p st) B)
    (hpath : ∀ C, Block.Prec (liveRoot p st) C → Block.Preceq C B →
      C ∈ erasedList st (storeFrame p.E p.cfg st.fg (voterBlocks p st (s + 1))))
    (hmajority : GridCO.voterCount (headVotes p st (s + 1)) <
      2 * GridCO.goldfishScore st.base.blocks
        (headVotes p st (s + 1)) (headSupport p st (s + 1)) B)
    (hdominance : ∀ D, Block.compatible B D = false →
      GridCO.goldfishScore st.base.blocks
        (headVotes p st (s + 1)) (headSupport p st (s + 1)) D <
      GridCO.goldfishScore st.base.blocks
        (headVotes p st (s + 1)) (headSupport p st (s + 1)) B) :
    Block.Preceq B (headVote p st (s + 1)) := by
  rw [fgsa_headVote_eq_filtered]
  rw [ite_eq_right (Nat.succ_ne_zero s)]
  apply fgsa_headInTree_covers_of_transfer p st _ _ _ B
    hanchor _ hmajority hdominance
  intro C hac hcb
  exact fgsa_storeFrame_mem_above_liveRoot p st _ C (hpath C hac hcb)
    (Bool.and_eq_true_iff.mp hac).2

end AvailableChain.FGSA
end
