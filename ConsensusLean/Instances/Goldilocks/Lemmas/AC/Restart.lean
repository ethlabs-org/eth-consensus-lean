module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.RestartStamp

public section

/-! # Goldilocks AC: the restart (A0.7)

What `ac_restart` keeps, resets and writes follows from its bulk-stamp characterization.
-/

namespace Consensus.Goldilocks.AC

variable (sp : ACParams)

/-- **A0.7, restart.** -/
theorem restart_state : RestartState sp := by
  intro FGP self A Φ t hΦ ht
  rw [acRestart_eq_stamp sp self A Φ t hΦ ht, restartStamp_eq]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl,
    not_joined_of_restartTime sp ht rfl, fun _ => rfl, fun _ => Or.inl rfl, ?_⟩
  intro q
  classical
  by_cases hg : q = sp.genesisRoot
  · subst q
    exact Or.inl (by simp [ACState.initial])
  · by_cases hq : InTree Φ q
    · exact Or.inr ⟨by simp [hg, hq], hg, hq⟩
    · exact Or.inl (by simp [ACState.initial, hg, hq])

end Consensus.Goldilocks.AC

end
