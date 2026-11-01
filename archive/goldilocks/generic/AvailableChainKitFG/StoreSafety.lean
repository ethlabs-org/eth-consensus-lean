module
public import AvailableChainKitFG.StoreSafetyDef
public import AvailableChainKitFG.AccountableCore

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

omit [RowCodec V] in
/-- Every evidence signer is faulty, so the strict weight bound excludes evidence. -/
theorem no_slashableWeight_of_fault_bound (E : Electorate V) (faulty : Finset V)
    (A B : Finset (Row V)) (hcap : E.weightOf faulty + E.totalWeight < 2 * E.q)
    (hno : NoSlashOutside faulty A B) : ¬ HasSlashableWeightBetween E A B := by
  rintro ⟨S, hS, he⟩
  have hsub : S ⊆ faulty := by
    intro i hi
    obtain ⟨a, ha, b, hb, hai, _, hab⟩ := he i hi
    by_contra hif
    exact hno a ha b hb (hai ▸ hif) hab
  have hw : E.weightOf S ≤ E.weightOf faulty := Finset.sum_le_sum_of_subset hsub
  change 2 * E.q ≤ E.totalWeight + E.weightOf S at hS
  omega

/-- Remove the evidence branch with an explicit no-evidence premise. -/
theorem finalized_preceq_of_no_evidence (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (D W : FGBlock V) (hroot : RootInjectiveOn D W) (hh : (f D).h_F < (H W).h)
    (hno : ¬ HasSlashableWeightBetween E (chainRows D) (chainRows W)) :
    FGBlock.Preceq (f D).F W :=
  (slashableWeight_or_finalized_preceq_of_certificate E H f hc D W hroot hh).resolve_left hno

/-- A fault bound alone is insufficient; honest rows must also exclude slashing. -/
theorem finalized_preceq_of_fault_bound (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (D W : FGBlock V) (hroot : RootInjectiveOn D W) (faulty : Finset V) (hh : (f D).h_F < (H W).h)
    (hcap : E.weightOf faulty + E.totalWeight < 2 * E.q)
    (hno : NoSlashOutside faulty (chainRows D) (chainRows W)) :
    FGBlock.Preceq (f D).F W :=
  finalized_preceq_of_no_evidence E H f hc D W hroot hh
    (no_slashableWeight_of_fault_bound E faulty _ _ hcap hno)

/-- The same explicit fault premises remove the compatibility evidence branch. -/
theorem finalized_compatible_of_fault_bound (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (D W : FGBlock V) (hroot : RootInjectiveOn D W) (faulty : Finset V)
    (hcap : E.weightOf faulty + E.totalWeight < 2 * E.q)
    (hno : NoSlashOutside faulty (chainRows D) (chainRows W)) :
    FGBlock.compatible (f D).F (f W).F = true :=
  (slashableWeight_or_finalized_compatible_of_certificate E H f hc D W hroot).resolve_left
    (no_slashableWeight_of_fault_bound E faulty _ _ hcap hno)

/-- The carrier supplies the historical threshold for every compared view member. -/
theorem viewLock_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (D F : FGBlock V) (vw : View V) (θ : Height)
    (hroots : ∀ W ∈ vw, RootInjectiveOn D W)
    (hF : (f D).F = F) (hθ : (f D).h_F ≤ θ)
    (hno : ∀ W ∈ vw, ¬ HasSlashableWeightBetween E (chainRows D) (chainRows W)) :
    ∀ W ∈ vw, θ < (H W).h → FGBlock.Preceq F W := by
  intro W hW hh
  exact hF ▸ finalized_preceq_of_no_evidence E H f hc D W (hroots W hW) (hθ.trans_lt hh) (hno W hW)

/-- A view lock from a strict fault bound and cross-chain no-slashing. -/
theorem viewLock_of_fault_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (D F : FGBlock V) (vw : View V) (θ : Height)
    (hroots : ∀ W ∈ vw, RootInjectiveOn D W) (faulty : Finset V)
    (hF : (f D).F = F) (hθ : (f D).h_F ≤ θ)
    (hcap : E.weightOf faulty + E.totalWeight < 2 * E.q)
    (hno : ∀ W ∈ vw, NoSlashOutside faulty (chainRows D) (chainRows W)) :
    ∀ W ∈ vw, θ < (H W).h → FGBlock.Preceq F W :=
  viewLock_of_certificate E H f hc D F vw θ hroots hF hθ
    (fun W hW => no_slashableWeight_of_fault_bound E faulty _ _ hcap (hno W hW))

/-- Genesis has ancestry directly. Other accepted anchors use their carrier height. -/
theorem accepted_lock_of_no_evidence (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (D F W : FGBlock V) (hroot : RootInjectiveOn D W) (hF : (f D).F = F)
    (hh : acceptedThreshold F (f D).h_F < (H W).h)
    (hno : ¬ HasSlashableWeightBetween E (chainRows D) (chainRows W)) :
    FGBlock.Preceq F W := by
  by_cases hg : F = .genesis
  · rw [hg]
    exact genesis_preceq W
  · rw [acceptedThreshold_def, ite_eq_right hg] at hh
    exact hF ▸ finalized_preceq_of_no_evidence E H f hc D W hroot hh hno

/-- Accepted-threshold form with both fault premises explicit. -/
theorem accepted_lock_of_fault_bound (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (D F W : FGBlock V) (hroot : RootInjectiveOn D W) (faulty : Finset V) (hF : (f D).F = F)
    (hh : acceptedThreshold F (f D).h_F < (H W).h)
    (hcap : E.weightOf faulty + E.totalWeight < 2 * E.q)
    (hno : NoSlashOutside faulty (chainRows D) (chainRows W)) :
    FGBlock.Preceq F W :=
  accepted_lock_of_no_evidence E H f hc D F W hroot hF hh
    (no_slashableWeight_of_fault_bound E faulty _ _ hcap hno)

/-- Structural store suppliers and certificates suffice to assemble store safety. -/
theorem FGStoreSafety.of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    {S : Type} (read : S → Store V) (cache : S → FGBlock V → FGHeight V × FGFinality V)
    (initial : S) (step : S → FGBlock V → S) (Good : S → Prop) (StepOK : S → FGBlock V → Prop)
    (hinit : Good initial)
    (hinv : ∀ s, Good s → FGStoreInvariant H f (read s))
    (hstep : ∀ s B, Good s → StepOK s B → Good (step s B))
    (htree : ∀ s B, Good s → (read s).TF ⊆ (read (step s B)).TF)
    (hmono : ∀ s B, Good s → FGBlock.Preceq (read s).F (read (step s B)).F)
    (hcache : ∀ s, Good s → ∀ B ∈ (read s).TF, cache s B = (H B, f B)) :
    FGStoreSafety E H f read cache initial step Good StepOK where
  initial_good := hinit
  invariant := hinv
  step_good := hstep
  tree_mono := htree
  accepted_F_mono := hmono
  cache_eq := hcache
  F_lock_no_evidence := by
    intro s _ D W hroot _ hF hh hno
    exact hF ▸ finalized_preceq_of_no_evidence E H f hc D W hroot hh hno
  F_lock_fault := by
    intro s _ D W hroot faulty _ hF hh hcap hno
    exact hF ▸ finalized_preceq_of_fault_bound E H f hc D W hroot faulty hh hcap hno

/-- Use a store safety interface with the accepted genesis threshold. -/
theorem FGStoreSafety.accepted_lock_no_evidence (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V)
    {S : Type} {read : S → Store V} {cache : S → FGBlock V → FGHeight V × FGFinality V}
    {initial : S} {step : S → FGBlock V → S} {Good : S → Prop} {StepOK : S → FGBlock V → Prop}
    (hs : FGStoreSafety E H f read cache initial step Good StepOK)
    (s : S) (hgood : Good s) (D W : FGBlock V) (hroot : RootInjectiveOn D W) (hD : D ∈ (read s).TF)
    (hF : (f D).F = (read s).F)
    (hh : acceptedThreshold (read s).F (f D).h_F < (H W).h)
    (hno : ¬ HasSlashableWeightBetween E (chainRows D) (chainRows W)) :
    FGBlock.Preceq (read s).F W := by
  by_cases hg : (read s).F = .genesis
  · rw [hg]
    exact genesis_preceq W
  · rw [acceptedThreshold_def, ite_eq_right hg] at hh
    exact hs.F_lock_no_evidence s hgood D W hroot hD hF hh hno

/-- Fault elimination also applies to an arbitrary store safety interface. -/
theorem FGStoreSafety.accepted_lock_fault (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V)
    {S : Type} {read : S → Store V} {cache : S → FGBlock V → FGHeight V × FGFinality V}
    {initial : S} {step : S → FGBlock V → S} {Good : S → Prop} {StepOK : S → FGBlock V → Prop}
    (hs : FGStoreSafety E H f read cache initial step Good StepOK)
    (s : S) (hgood : Good s) (D W : FGBlock V) (hroot : RootInjectiveOn D W) (faulty : Finset V)
    (hD : D ∈ (read s).TF) (hF : (f D).F = (read s).F)
    (hh : acceptedThreshold (read s).F (f D).h_F < (H W).h)
    (hcap : E.weightOf faulty + E.totalWeight < 2 * E.q)
    (hno : NoSlashOutside faulty (chainRows D) (chainRows W)) :
    FGBlock.Preceq (read s).F W :=
  hs.accepted_lock_no_evidence E H f s hgood D W hroot hD hF hh
    (no_slashableWeight_of_fault_bound E faulty _ _ hcap hno)

end AvailableChain.KitFG
end
