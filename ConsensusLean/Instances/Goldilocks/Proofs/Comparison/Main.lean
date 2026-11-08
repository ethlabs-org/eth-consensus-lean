module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.Defaults
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.HealAC
public import ConsensusLean.Proofs.Comparison.Main
public import ConsensusLean.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.Obligations.Main
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace

public section

/-! # Goldilocks comparison instances (Slice 0)

* `goldilocks_heal_default0`, `goldilocks_txLatency_default0`: the composite defaults, from the
  endpoint (`Growing.meets_obligations`, whose shape obligations give the L0 `Behaviour`) and the
  generic defaults `healDefault0`, `txLatencyDefault0`.
* `healProfileAC0_free`: the free static Tier A instance, from tight H.1 with the unlock given
  (`ac_healing_standalone_of_parent_tightU`).
* `signingRateAC0`: from A0.8 with the unlock given (`one_vote_per_slotU`). -/

namespace Consensus.Goldilocks.Comparison

open AsChainShape Blocks Shape SA Consensus.Comparison

theorem goldilocks_heal_default0 : GoldilocksHealDefault0 := fun S A V _ _ cap X =>
  healDefault0 V _ _ _ _ ((Growing.meets_obligations S A).2.behaviour V) cap X

theorem goldilocks_txLatency_default0 : GoldilocksTxLatencyDefault0 := fun S A V _ _ cap X =>
  txLatencyDefault0 V _ _ _ _ ((Growing.meets_obligations S A).2.behaviour V) cap X

theorem healProfileAC0_free : HealProfileAC0Free := by
  intro sp
  refine ⟨fun q q' ⟨_, hf, _⟩ => ?_, ?_⟩
  · unfold acFree0
    by_cases h' : 3 * q'.fcap ≤ sp.n - 1
    · simp [h', le_trans (by omega : 3 * q.fcap ≤ 3 * q'.fcap) h']
    · simp [h']
  · intro u FGP ro H U tr proposer q c b₀ g hc hI p P hpH hP hp
    unfold acFree0 at hc
    split_ifs at hc
    · obtain rfl : c = 8 * sp.k + 4 := (WithTop.coe_injective hc).symm
      refine ac_healing_standalone_of_parent_tightU hI.1 hpH hP ?_
      push_cast at hp
      exact hp
    · exact absurd hc WithTop.top_ne_coe

theorem signingRateAC0 : SigningRateAC0 := fun sp _ FGP ro H U tr _ _ hS =>
  one_vote_per_slotU sp FGP ro H U tr hS.run.localRun

end Consensus.Goldilocks.Comparison

end
