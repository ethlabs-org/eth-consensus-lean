module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Base
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes

public section

/-! # Source age at an honest call

The source's lock history is local to the caller, so retention at the call preserves it.
-/

namespace Consensus.Goldilocks.SA.Growing

theorem source_age (sp : SAParams) : SourceAge sp := by
  intro FGP ro H U tr hr τ x i ℓ C hx hto hslot
  obtain ⟨j, hji, s, B, CV, hfl, ht, hs, hanc⟩ :=
    SA.source_age sp FGP ro (H (tr.time i)) U (tr.upTo (tr.time i))
      (hr.upTo (hr.time_nonneg i)) τ x i ℓ C hx
      ((upTo_toFGAt hr.time_mono).mpr ⟨le_rfl, hto⟩) hslot
  exact ⟨j, hji, s, B, CV, (upTo_fastLockAt hr.time_mono).mp hfl |>.2, ht, hs, hanc⟩

end Consensus.Goldilocks.SA.Growing

end
