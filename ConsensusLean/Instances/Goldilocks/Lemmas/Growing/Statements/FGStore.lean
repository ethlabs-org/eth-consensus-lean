module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGStore.Growing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Const

public section

/-! # The growing-fault FGStore statements imply the static ones

At `H := fun _ => H₀` the FG trace contract, the namers, the honest proposal and the good window
are the static ones, so each statement of `Statements/FGStore/Growing` implies its static
counterpart. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type}

/-- A static good window is a growing-fault good window of the constant honest set. -/
theorem Growing.goodWindow_of_static {H : Set (Fin P.n)} {tr : FGTrace P ACP} {cF : Nat}
    {T : NodeBlock P ACP} {a kF : Nat} {p : Fin P.n} {i : Nat} {Bs Pr : NodeBlock P ACP}
    {R : Finset (FG.Att P.n)} (h : Store.GoodWindow P ACP H tr cF T a kF p i Bs Pr R) :
    Growing.GoodWindow P ACP (fun _ => H) tr cF T a kF p i Bs Pr R :=
  { proposal := h.proposal
    entry := h.entry
    extends_entry := h.extends_entry
    window := h.window
    quorum := h.quorum
    fgAtts := h.fgAtts
    emitted := h.emitted
    pooled := h.pooled
    params := h.params }

variable (P ACP)

theorem finalizedSafety_of_growing (h : Growing.FinalizedSafety P ACP) : FinalizedSafety P ACP :=
  fun acp₀ H U tr hrun hf y hy z hz i j =>
    h acp₀ (fun _ => H) U tr (Goldilocks.Growing.FGLocalRun.const_iff.mpr hrun) y z i j hy hz hf

theorem quorumFreeEntries_of_growing (h : Growing.QuorumFreeEntries P ACP) :
    QuorumFreeEntries P ACP :=
  fun acp₀ H U tr 𝓔 T₀ T y hrun h₀ hT hy hq hs i X hX ht =>
    h acp₀ (fun _ => H) U tr 𝓔 T₀ T y (Goldilocks.Growing.FGLocalRun.const_iff.mpr hrun) h₀ hT hq
      (fun v j a hv ha hlo hhi => hs v hv j a ha hlo hhi) i X hy hX ht

theorem previousHeightJustifiedEntry_of_growing (h : Growing.PreviousHeightJustifiedEntry P ACP) :
    PreviousHeightJustifiedEntry P ACP :=
  fun acp₀ H U tr hrun cF T a kF p i Bs Pr R hw =>
    h acp₀ (fun _ => H) U tr (Goldilocks.Growing.FGLocalRun.const_iff.mpr hrun) cF T a kF p i Bs Pr
      R (Growing.goodWindow_of_static hw)

theorem previousHeightNotJustifiedEntry_of_growing
    (h : Growing.PreviousHeightNotJustifiedEntry P ACP) :
    PreviousHeightNotJustifiedEntry P ACP := by
  intro acp₀ H U tr hrun cF T a₀ kF p i Bs Pr R hw hn
  obtain ⟨X, h1, h2, h3, h4, h5, h6, h7⟩ := h acp₀ (fun _ => H) U tr
    (Goldilocks.Growing.FGLocalRun.const_iff.mpr hrun) cF T a₀ kF p i Bs Pr R
    (Growing.goodWindow_of_static hw) hn
  exact ⟨X, h1, h2, h3, h4, h5, h6, fun a₁ p₁ i₁ Bs₁ Pr₁ R₁ hw₁ =>
    h7 a₁ p₁ i₁ Bs₁ Pr₁ R₁ (Growing.goodWindow_of_static hw₁)⟩

theorem crossing_of_growing (h : Growing.Crossing P ACP) : Crossing P ACP :=
  fun acp₀ H U tr hrun y hy k C T g r hC hT hTC hg hr hslot hwin =>
    h acp₀ (fun _ => H) U tr (Goldilocks.Growing.FGLocalRun.const_iff.mpr hrun) y k C T g r hy hC
      hT hTC hg hr hslot hwin

theorem coverage_of_growing (h : Growing.Coverage P ACP) : Coverage P ACP :=
  fun acp₀ H U tr hrun cF T₁ T a₀ kF p i Bs Pr R hw hn hT₁ hanc hne hfail X hX hXB a₁ p₁ i₁ Bs₁
      Pr₁ R₁ hw₁ =>
    h acp₀ (fun _ => H) U tr (Goldilocks.Growing.FGLocalRun.const_iff.mpr hrun) cF T₁ T a₀ kF p i Bs
      Pr R (Growing.goodWindow_of_static hw) hn hT₁ hanc hne hfail X hX hXB a₁ p₁ i₁ Bs₁ Pr₁ R₁
      (Growing.goodWindow_of_static hw₁)

variable {P ACP}

/-- The growing-fault FGStore part 2 implies the static one. -/
theorem fgStoreTrace_of_growing (h : Growing.FGStoreTrace) : FGStoreTrace := fun P ACP =>
  ⟨finalizedSafety_of_growing P ACP (h P ACP).finalizedSafety,
    quorumFreeEntries_of_growing P ACP (h P ACP).quorumFreeEntries⟩

/-- The growing-fault FGStore part 3, with the static `CacheAcceptance`, implies the static
one. -/
theorem fgStoreService_of_growing (h : Growing.FGStoreService)
    (hc : ∀ (P : Params) (ACP : Type), CacheAcceptance P ACP) : FGStoreService := fun P ACP =>
  ⟨previousHeightJustifiedEntry_of_growing P ACP (h P ACP).previousHeightJustifiedEntry,
    previousHeightNotJustifiedEntry_of_growing P ACP (h P ACP).previousHeightNotJustifiedEntry,
    crossing_of_growing P ACP (h P ACP).crossing, coverage_of_growing P ACP (h P ACP).coverage,
    hc P ACP⟩

end Consensus.Goldilocks.Store

end
