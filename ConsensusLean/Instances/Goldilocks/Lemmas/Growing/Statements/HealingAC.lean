module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.AC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Const

public section

/-! # The growing-fault AC healing statements imply the static ones

At `H := fun _ => H₀` the AC-level `Healthy`, `Catch`, trivial frames, driven traces, protected
blocks, `Inv` and `Geo` are the static ones, and the proposer's hold is `· ∈ H₀`, so each
statement of `Statements/Healing/Growing/AC` implies its static counterpart. -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {proposer : Nat → Fin sp.n}

theorem healthyAC_const {g : Time} :
    Growing.HealthyAC tr (fun _ => H) U g ↔ HealthyAC tr H U g := by
  simp only [Growing.HealthyAC, HealthyAC]; aesop

theorem catchAC_const {g κ : Time} :
    Growing.CatchAC tr (fun _ => H) U g κ ↔ CatchAC tr H U g κ := by
  simp only [Growing.CatchAC, CatchAC]; aesop

theorem trivialFrames_const :
    Growing.TrivialFrames tr (fun _ => H) ↔ TrivialFrames tr H := by
  exact ⟨fun h y hy i ℓ hc => h y i ℓ hy hc, fun h y i ℓ hy hc => h y hy i ℓ hc⟩

theorem driven_const :
    Growing.Driven proposer tr (fun _ => H) ↔ Driven proposer tr H := by
  constructor
  · intro h
    exact
      { blocks := fun y hy i B ha hg => h.blocks y i B hy ha hg
        honest_slot := fun y hy i B ha hg hp => h.honest_slot y i B hy ha hg hp
        tick := fun y hy t ht hp ha => h.tick y t hy ht hp ha
        proposal := fun s hs p hp hpe ha hj => h.proposal s hs p hp hpe ha hj
        tick_first := fun y hy i j ℓ ℓ' hc hc' ht he hm =>
          h.tick_first y i j ℓ ℓ' hy hc hc' ht he hm
        proposal_first := fun y hy i j ℓ ℓ' hc hc' hp he hm =>
          h.proposal_first y i j ℓ ℓ' hy hc hc' hp he hm }
  · intro h
    exact
      { blocks := fun y i B hy ha hg => h.blocks y hy i B ha hg
        honest_slot := fun y i B hy ha hg hp => h.honest_slot y hy i B ha hg hp
        tick := fun y t hy ht hp ha => h.tick y hy t ht hp ha
        proposal := fun s hs p hp hpe ha hj => h.proposal s hs p hp hpe ha hj
        tick_first := fun y i j ℓ ℓ' hy hc hc' ht he hm =>
          h.tick_first y hy i j ℓ ℓ' hc hc' ht he hm
        proposal_first := fun y i j ℓ ℓ' hy hc hc' hp he hm =>
          h.proposal_first y hy i j ℓ ℓ' hc hc' hp he hm }

theorem protected_const {t₀ : Time} {B : Blk sp.n FGP} {j : Nat} :
    Growing.Protected proposer tr (fun _ => H) t₀ B j ↔ Protected proposer tr H t₀ B j := by
  simp only [Growing.Protected, Protected]; aesop

theorem inv_const {t₀ : Time} :
    Growing.Inv proposer tr (fun _ => H) U t₀ ↔ Inv proposer tr H U t₀ := by
  exact ⟨fun h B j hP y hy i ℓ hc ht => h B j (protected_const.mpr hP) y i ℓ hy hc ht,
    fun h B j hP y i ℓ hy hc ht => h B j (protected_const.mp hP) y hy i ℓ hc ht⟩

theorem geo_const {p : Nat} {P : Blk sp.n FGP} :
    Growing.Geo proposer tr (fun _ => H) p P ↔ Geo proposer tr H p P := by
  exact ⟨fun h k ℓP hc hp ht y hy i ℓ e he hs => h k ℓP hc hp ht y i ℓ e hy he hs,
    fun h k ℓP hc hp ht y i ℓ e hy he hs => h k ℓP hc hp ht y hy i ℓ e he hs⟩

theorem acHealingStandalone_of_growing (h : Growing.ACHealingStandalone (sp := sp)) :
    ACHealingStandalone (sp := sp) := by
  intro FGP ro H U tr proposer g hrun hd htf hh hc p P hp hP ht
  obtain ⟨h1, h2⟩ := h FGP ro (fun _ => H) U tr proposer g (acRun_const.mpr hrun)
    (driven_const.mpr hd) (trivialFrames_const.mpr htf)
    (healthyAC_const.mpr hh) (catchAC_const.mpr hc) p P hp hP ht
  exact ⟨fun x hx j e hv hs => h1 x j e hx hv hs, fun y hy j ℓ hcl ht' htk =>
    h2 y j ℓ hy hcl ht' htk⟩

theorem acHealingStandaloneCorollary_of_growing
    (h : Growing.ACHealingStandaloneCorollary (sp := sp)) :
    ACHealingStandaloneCorollary (sp := sp) := by
  intro FGP ro H U tr proposer g Gp hrun hd htf hh hc hprop t ht
  obtain ⟨p, P, h1, h2, h3, h4⟩ := h FGP ro (fun _ => H) U tr proposer g Gp
    (acRun_const.mpr hrun) (driven_const.mpr hd) (trivialFrames_const.mpr htf)
    (healthyAC_const.mpr hh) (catchAC_const.mpr hc) hprop t ht
  exact ⟨p, P, h1, h2, h3, fun y hy j ℓ hcl ht' htk => h4 y j ℓ hy hcl ht' htk⟩

theorem acInclusion_of_growing (h : Growing.ACInclusion (sp := sp)) :
    ACInclusion (sp := sp) := by
  intro FGP ro H U tr proposer g t₀ hrun hd hh hc hg hinv p P hp hP ht
  obtain ⟨h1, h2⟩ := h FGP ro (fun _ => H) U tr proposer g t₀ (acRun_const.mpr hrun)
    (driven_const.mpr hd) (healthyAC_const.mpr hh) (catchAC_const.mpr hc) hg
    (inv_const.mpr hinv)
    p P hp hP ht
  refine ⟨fun hgeo x hx j e hv hs => h1 (geo_const.mpr hgeo) x j e hx hv hs,
    fun hu y hy j ℓ hcl ht' htk => h2 (fun x j e hx hv hs => hu x hx j e hv hs) y j ℓ hy hcl ht'
      htk⟩

theorem acHealingStandaloneAll_of_growing (h : Growing.ACHealingStandaloneAll) :
    ACHealingStandaloneAll := fun sp => acHealingStandalone_of_growing (h sp)

theorem acHealingStandaloneCorollaryAll_of_growing (h : Growing.ACHealingStandaloneCorollaryAll) :
    ACHealingStandaloneCorollaryAll := fun sp => acHealingStandaloneCorollary_of_growing (h sp)

theorem acInclusionAll_of_growing (h : Growing.ACInclusionAll) : ACInclusionAll :=
  fun sp => acInclusion_of_growing (h sp)

end Consensus.Goldilocks.SA

end
