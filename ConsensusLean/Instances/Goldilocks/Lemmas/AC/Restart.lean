module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.RestartStamp

public section

/-! # Goldilocks AC: the restart (A0.7)

What `ac_restart` keeps, resets and writes follows from its bulk-stamp characterization.
-/

namespace Consensus.Goldilocks.AC

variable (sp : ACParams)

/-- Parent order at the genesis root of these protocol parameters. -/
abbrev ParentOrder {FGP : Type} (Φ : Frm sp.n FGP) (l : List (Blk sp.n FGP)) : Prop :=
  ParentOrderAt sp.genesisRoot Φ l

open Classical in
/-- One replay order: a chosen parent-order enumeration (`[]` if there is none). -/
noncomputable def ReplayOrder.choice {FGP : Type} : ReplayOrder sp FGP where
  order := fun _ Φ => if h : ∃ l, ParentOrder sp Φ l then h.choose else []
  parentOrder := fun _ Φ h => by simp only [h, ↓reduceDIte]; exact h.choose_spec

/-- **A0.7, restart.** -/
theorem restart_state : RestartState sp := by
  intro FGP ro self A Φ t hΦ ht
  rw [acRestart_eq_stamp sp ro self A Φ t hΦ ht, restartStamp_eq]
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
