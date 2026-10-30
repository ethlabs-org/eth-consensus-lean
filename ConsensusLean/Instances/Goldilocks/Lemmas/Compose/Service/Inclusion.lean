module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record

public section

/-! # Goldilocks milestone Service: A1.7, inclusion

From the inclusion facts (`included_facts`, the open Sleepy induction: the record's block extends
the honest proposal and has `HeadSupport`) with `head_confirmed_of_support`: the confirmed tip is
the record's block. -/

namespace Consensus.Goldilocks.Compose

/-- **A1.7, inclusion.** -/
theorem inclusion : Inclusion := by
  intro sp ro dg H tr ΔF hrun hnc hsl hg p hp k P s hP hPs hpj y hy i hc ht hyw hyj hyw₀ hyj₀ hnr hu
  obtain ⟨R, hR, hPR, hs⟩ :=
    included_facts hrun hnc hsl hg hp hP hPs hpj hy hc ht hyw hyj hyw₀ hyj₀ hnr hu
  rw [(head_confirmed_of_support hrun hy hR hs).2]
  exact hPR

end Consensus.Goldilocks.Compose

end
