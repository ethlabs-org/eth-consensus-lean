module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record

public section

/-! # Goldilocks milestone Service: A1.7, inclusion

From the inclusion facts (`included_facts`, open: workbench#12): the record's block extends the
honest proposal and has `HeadSupport`, so it is the confirmed tip (`head_confirmed_of_support`);
or the record has left the frame, the confirmed tip is `Σ.F` (`SA.acConfirmed_eq_F`), and `Σ.F`
extends the proposal. -/

namespace Consensus.Goldilocks.Compose

/-- **A1.7, inclusion.** -/
theorem inclusion : Inclusion := by
  intro sp ro dg H tr ΔF hrun hnc hsl hg p hp k P s hP hPs hpj y hy i hc ht hyw hyj hyw₀ hyj₀ hnr hu
  obtain ⟨hrec, hF⟩ :=
    included_facts hrun hnc hsl hg hp hP hPs hpj hy hc ht hyw hyj hyw₀ hyj₀ hnr hu
  by_cases hin : ∃ R, RecordAt tr y i R
  · obtain ⟨R, hR⟩ := hin
    rw [(head_confirmed_of_support hrun hy hR (hrec R hR).2).2]
    exact (hrec R hR).1
  · have hc : tr.confirmedAt y i = (Node.frame (tr.state y i)).F :=
      SA.acConfirmed_eq_F (frameOK_state hrun.toLocalRun hy i)
        fun ⟨R, hR, hr⟩ => hin ⟨R, hR, hr⟩
    rw [hc]
    exact hF hin

end Consensus.Goldilocks.Compose

end
