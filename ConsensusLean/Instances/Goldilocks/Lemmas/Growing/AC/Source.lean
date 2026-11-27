module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Base
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Compatible
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Source age at an honest call

The source's lock history is local to the caller, so retention at the call preserves it.
-/

namespace Consensus.Goldilocks.AC.Growing

theorem source_age (sp : ACParams) : SourceAge sp := by
  intro FGP ro H U tr hr τ x i ℓ C hx hto hslot
  rcases AC.source_age sp FGP ro (H (tr.time i)) U (tr.upTo (tr.time i))
      (hr.upTo (hr.time_nonneg i)) τ x i ℓ C hx
      ((upTo_toFGAt hr.time_mono).mpr ⟨le_rfl, hto⟩) hslot with
    ⟨j, hji, s, B, CV, hfl, ht, hs, hanc⟩ | ⟨D, a, hD, hnf, ha, hdeep⟩
  · exact Or.inl ⟨j, hji, s, B, CV, (upTo_fastLockAt hr.time_mono).mp hfl |>.2, ht, hs, hanc⟩
  · have hst : (tr.upTo (tr.time i)).state x i = tr.state x i :=
      Trace.upTo_state tr x fun k hk => hr.time_mono hk.le
    rw [hst, Trace.upTo_time] at hnf ha hdeep
    exact Or.inr ⟨D, a, hD, hnf, ha, hdeep⟩

end Consensus.Goldilocks.AC.Growing

end
