module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.Candidates
import ConsensusLean.Instances.Goldilocks.Lemmas.Candidates.LateCertificate
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Steps

public section

/-! # Goldilocks comparison instances at Tier A over candidate runs (Slice 0)

A run of a candidate SA at mode `m`, forgotten, is a run at mode `m` with the unlock given by the
candidate's oracle (`localRunU_projTraceM`, `localRunU_projTraceCM`); with the other premises it
is H.1's setting `StandaloneRunU m` there, and tight H.1 at a width-`k` mode
(`ac_healing_standalone_of_parent_tightU`) gives the claim at `acFree0`. The named rules are the
free instances at their modes (each of width `k`). -/

namespace Consensus.Goldilocks.Comparison

open SA EvidenceRelease LateCertificate Consensus.Comparison

private theorem acFree0_mono (sp : SAParams) : AdverseMonotone (acFree0 sp) := by
  intro q q' ⟨_, hf, _⟩
  unfold acFree0
  by_cases h' : 2 * q'.fcap < sp.n
  · simp [h', lt_of_le_of_lt (by omega : 2 * q.fcap ≤ 2 * q'.fcap) h']
  · simp [h']

private theorem acFree0_eq {sp : SAParams} {q : Slice0Q (Fin sp.n)} {c : ℕ}
    (hc : acFree0 sp q = c) : c = 8 * sp.k + 4 := by
  unfold acFree0 at hc
  split_ifs at hc
  · exact (WithTop.coe_injective hc).symm
  · exact absurd hc WithTop.top_ne_coe

theorem healProfileER0_free : HealProfileER0Free := by
  intro sp m hw
  refine ⟨acFree0_mono sp, ?_⟩
  intro FGP ro H U tr proposer q c b₀ g hc hI p P hpH hP hp
  obtain rfl := acFree0_eq hc
  obtain ⟨hrun, hobj, hdr, htriv, hcore, hf, hcatch, -⟩ := hI
  exact ac_healing_standalone_of_parent_tightU
    ⟨⟨⟨localRunU_projTraceM hrun, hobj⟩, hdr, hcore, hf, hcatch⟩, htriv⟩ hw hpH hP
    (by push_cast at hp; exact hp)

theorem healProfileCert0_free : HealProfileCert0Free := by
  intro sp m hw
  refine ⟨acFree0_mono sp, ?_⟩
  intro FGP ro H U tr proposer q c b₀ g hc hI p P hpH hP hp
  obtain rfl := acFree0_eq hc
  obtain ⟨hrun, hobj, hdr, htriv, hcore, hf, hcatch, -⟩ := hI
  exact ac_healing_standalone_of_parent_tightU
    ⟨⟨⟨localRunU_projTraceCM hrun, hobj⟩, hdr, hcore, hf, hcatch⟩, htriv⟩ hw hpH hP
    (by push_cast at hp; exact hp)

theorem healProfileERParent0 : HealProfileERParent0 := fun sp => healProfileER0_free sp _ rfl

theorem healProfileCertParent0 : HealProfileCertParent0 :=
  fun sp => healProfileCert0_free sp _ rfl

theorem healProfileMinimalAC0 : HealProfileMinimalAC0 := fun sp => healProfileER0_free sp _ rfl

theorem healProfileMinimalACOptLocked0 : HealProfileMinimalACOptLocked0 :=
  fun sp => healProfileER0_free sp _ rfl

end Consensus.Goldilocks.Comparison

end
