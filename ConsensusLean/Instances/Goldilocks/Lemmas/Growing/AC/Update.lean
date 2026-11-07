module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Base
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Update

public section

/-! # Confirmation at an honest update

All counts are charged at the updater's cut. Its retained pool is unchanged.
-/

namespace Consensus.Goldilocks.SA.Growing

theorem optimistic_next_update (sp : SAParams) : OptimisticNextUpdate sp := by
  intro FGP ro H U tr proposer hrun s z k B ℓ hf hext hz hup hh hres
  have hm := hrun.localRun.time_mono
  have hr := hrun.upTo (hrun.localRun.time_nonneg k)
  have hs : (tr.upTo (tr.time k)).state z k = tr.state z k :=
    Trace.upTo_state tr z fun _ hi => hm hi.le
  rw [← hs]
  apply SA.optimistic_next_update sp FGP ro (H (tr.time k)) U (tr.upTo (tr.time k))
    proposer hr s z k B ℓ hf
  · intro x hx j e hv hslot
    obtain ⟨hjt, hv⟩ := upTo_voteAt.mp hv
    exact hext x j e (hrun.localRun.antitone hjt hx) hv hslot
  · exact hz
  · exact (upTo_updateAt hm).mpr ⟨le_rfl, hup⟩
  · simpa only [hs] using hh
  · simpa only [hs] using hres

end Consensus.Goldilocks.SA.Growing

end
