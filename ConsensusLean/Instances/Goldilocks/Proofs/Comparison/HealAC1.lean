module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.HealAC1
public import ConsensusLean.Instances.Goldilocks.Proofs.Comparison.TierA
public import ConsensusLean.Instances.Goldilocks.Proofs.Comparison.Candidates
public import ConsensusLean.Proofs.Comparison.Main

public section

/-! # Slice 1 at Tier A (proofs)

The Slice 1 coordinates only add premises: `IncidentAC1` (resp. `IncidentER1`, `IncidentCert1`)
contains the Slice 0 premises at `q.slice0`, and `acFree1 q` is `acFree0 q.slice0`, so every free
instance is the Slice 0 instance at `q.slice0`. The order inclusion: the Slice 0 premises are
monotone in `⟨L, fcap, a.async⟩`, the hold is dropped when the class leaves `splitHeld`, and the
activity and participation bounds are monotone in `hpre`, `hpost` and `m`. -/

namespace Consensus.Goldilocks.Comparison

open SA EvidenceRelease LateCertificate Consensus.Comparison

private theorem groupSync_mono {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}
    {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {b₀ g : Time} {tr : SATrace sp FGP ro}
    {a a' : AsyncClass (Fin sp.n)} (h : a ≤ a') (hs : GroupSyncACOn H U b₀ g tr a) :
    GroupSyncACOn H U b₀ g tr a' := by
  cases a' with
  | any => trivial
  | split G' =>
    cases a with
    | any => exact absurd h id
    | split G =>
      change G = G' at h
      subst h
      exact hs

private theorem hold_mono {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}
    {H : Set (Fin sp.n)} {b₀ g : Time} {tr : SATrace sp FGP ro}
    {a a' : IncidentClass (Fin sp.n)} (h : a ≤ a') (hs : HoldACOn H b₀ g tr a) :
    HoldACOn H b₀ g tr a' := by
  cases a' with
  | any => trivial
  | split _ => trivial
  | splitHeld G' =>
    cases a with
    | any => exact absurd h id
    | split _ => exact absurd h id
    | splitHeld G =>
      change G = G' at h
      subst h
      exact hs

private theorem slice1AC_mono {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}
    {H : Set (Fin sp.n)} {b₀ g : Time} {tr : SATrace sp FGP ro} {q q' : HealQ (Fin sp.n)}
    (hq : q ≤ q') (h : Slice1AC q b₀ g tr H) : Slice1AC q' b₀ g tr H := by
  obtain ⟨-, hpre, hpost, hm, -, ha, -⟩ := hq
  obtain ⟨hh, h1, h2, h3⟩ := h
  exact ⟨hold_mono ha hh, h1.trans hpre, h2.trans hpost, hm.trans h3⟩

theorem incidentAC1_mono : IncidentAC1Mono := by
  intro sp m u FGP ro H U tr proposer q q' b₀ g hq ⟨⟨hS, hw, hf, hsync, hb, hL, hg⟩, h1⟩
  have hΔ := sp.toParams.hΔ
  have h1' := slice1AC_mono hq h1
  obtain ⟨hLq, hfq, ha⟩ := healQ_slice0_mono _ q q' hq
  refine ⟨⟨hS, hw, hf.trans hfq, hsync, hb, hL.trans ?_, groupSync_mono ha hg⟩, h1'⟩
  exact Int.mul_le_mul_of_nonneg_right (by exact_mod_cast hLq) hΔ.le

private theorem acFree1_mono (sp : SAParams) : AdverseMonotone (acFree1 sp) := by
  intro q q' ⟨_, _, _, _, hf, _⟩
  unfold acFree1
  by_cases h' : 2 * q'.fcap < sp.n
  · simp [h', lt_of_le_of_lt (by omega : 2 * q.fcap ≤ 2 * q'.fcap) h']
  · simp [h']

theorem healProfileAC1_free : HealProfileAC1Free := by
  intro sp
  refine ⟨acFree1_mono sp, ?_⟩
  intro m hw u FGP ro H U tr proposer q c b₀ g hc hI
  exact (healProfileAC0_free sp).2 m hw u FGP ro H U tr proposer q.slice0 c b₀ g hc hI.1

theorem healProfileER1_free : HealProfileER1Free := by
  intro sp m hw
  refine ⟨acFree1_mono sp, ?_⟩
  intro FGP ro H U tr proposer q c b₀ g hc hI
  exact (healProfileER0_free sp m hw).2 FGP ro H U tr proposer q.slice0 c b₀ g hc hI.1

theorem healProfileCert1_free : HealProfileCert1Free := by
  intro sp m hw
  refine ⟨acFree1_mono sp, ?_⟩
  intro FGP ro H U tr proposer q c b₀ g hc hI
  exact (healProfileCert0_free sp m hw).2 FGP ro H U tr proposer q.slice0 c b₀ g hc hI.1

theorem healProfileERParent1 : HealProfileERParent1 := fun sp => healProfileER1_free sp _ rfl

theorem healProfileCertParent1 : HealProfileCertParent1 :=
  fun sp => healProfileCert1_free sp _ rfl

theorem healProfileMinimalAC1 : HealProfileMinimalAC1 := fun sp => healProfileER1_free sp _ rfl

theorem healProfileMinimalACOptLocked1 : HealProfileMinimalACOptLocked1 :=
  fun sp => healProfileER1_free sp _ rfl

end Consensus.Goldilocks.Comparison

end
