module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.HealAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Steps
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace

public section

/-! # Goldilocks comparison instances at Tier A (Slice 0)

* `healProfileAC0_free`: the free static instance `acFree0` at every width-`k` write mode and
  every unlock oracle, from the mode-generic tight H.1 (`ac_healing_standalone_of_parent_tightU`).
* `signingRateAC0`: one vote per slot at every mode, from A0.8 with the unlock given
  (`one_vote_per_slotU`). -/

namespace Consensus.Goldilocks.Comparison

open SA Consensus.Comparison

theorem healProfileAC0_free : HealProfileAC0Free := by
  intro sp
  refine ⟨fun q q' ⟨_, hf, _⟩ => ?_, ?_⟩
  · unfold acFree0
    by_cases h' : 2 * q'.fcap < sp.n
    · simp [h', lt_of_le_of_lt (by omega : 2 * q.fcap ≤ 2 * q'.fcap) h']
    · simp [h']
  · intro m hw u FGP ro H U tr proposer q c b₀ g hc hI p P hpH hP hp
    unfold acFree0 at hc
    split_ifs at hc
    · obtain rfl : c = 8 * sp.k + 4 := (WithTop.coe_injective hc).symm
      refine ac_healing_standalone_of_parent_tightU hI.1 hw hpH hP ?_
      push_cast at hp
      exact hp
    · exact absurd hc WithTop.top_ne_coe

theorem signingRateAC0 : SigningRateAC0 := fun sp _ _ FGP ro H U tr h =>
  one_vote_per_slotU sp FGP ro H U tr h

end Consensus.Goldilocks.Comparison

end
