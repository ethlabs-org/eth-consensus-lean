module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.AcceptedFinality
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements

public section

/-! # Goldilocks Healing under growing faults: replay finality enters the cache (G1.9 (b))

`Healing.Growing.cache_acceptance`: the growing form of HR.5. The prefix through the acceptance's
time is a static run for the validators honest then (`GoldilocksRun.upTo`, `NoCollRun.upTo`), on
which `accepted_finality_cached` applies with the faults counted at the cut. -/

namespace Consensus.Goldilocks.Healing.Growing

/-- **G1.9 (b) under growing faults:** every acceptance by a node honest at its cut caches its
replay-finalized target, when fewer than a third of the validators are compromised by the cut. -/
theorem cache_acceptance : CacheAcceptance := by
  intro sp proposer dg H tr ini hrun hnc y k B hy hf3 hB Fs hFs hroot
  set d := tr.time k
  have hd : 0 ≤ d := hrun.time_nonneg k
  have hrd := hrun.upTo hd
  have hBd : (tr.upTo d).AcceptAt y k B := (Trace.upTo_callAt tr).mpr ⟨le_rfl, hB⟩
  have hpost : (tr.upTo d).post k = tr.post k := rfl
  have hfg := Compose.fg_projection_from
    (fun y _ => Compose.requirements_from sp (hrd.vstart y)) hrd.genesis_root_ok
    hrd.toLocalRun (hnc.upTo d)
  have hst : ∀ i, (tr.upTo d).projFG.store y i = ((tr.upTo d).state y i).fg :=
    fun i => by simp only [FGTrace.store, Compose.projFG_state hrd.toLocalRun hy i]
  have hpk : (tr.upTo d).projFG.store y (k + 1) = (tr.post k).fg := by
    rw [hst, (tr.upTo d).state_succ_of_call hBd, hpost]
  have hf : (H d)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.toParams.n := by
    have hn := sp.toParams.hn
    change 3 * (H d)ᶜ.ncard ≤ sp.toParams.n - 1 at hf3
    change (H d)ᶜ.ncard < 2 * ((2 * sp.toParams.n + 2) / 3) - sp.toParams.n
    omega
  have h := accepted_finality_cached hfg hf hy (Compose.projFG_callAt.mpr hBd)
    (hpk.symm ▸ hFs) (hpk.symm ▸ hroot)
  simpa only [hpk] using h

end Consensus.Goldilocks.Healing.Growing

end
