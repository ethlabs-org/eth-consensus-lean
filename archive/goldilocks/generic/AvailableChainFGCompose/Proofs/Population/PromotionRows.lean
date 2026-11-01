module
public import AvailableChainFGCompose.Proofs.Population.Promotion
public import AvailableChainFGCompose.Proofs.Healing.PromotionRows

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot)
variable (H : FGHeightView (Fin n)) (T : FGTiming) (I : V2.D.Interface Prot)
variable (pair : Wire → NamedHeightPair)
variable (parentFG : Prot.State → Block → Option (FGBlock (Fin n)))
variable (parentHeight : Prot.State → Slot → FGBlock (Fin n) → Height × BlockId)
variable (validFor : Prot.State → Slot → FGBlock (Fin n) → Wire → Bool)
variable (fold : Prot.State → Slot → FGBlock (Fin n) → Window.State (Fin n))
variable (Ef : Electorate (Fin n)) (laws : FGHeightLaws Ef H)

include laws in
/-- SAME: preserve a given fixed batch while transferring its entry to the actual parent. -/
theorem p0d3_same_batch_on_holder {A : Finset (Fin n)} {r height : Nat} {s : Slot}
    {Q : Block} {X U : FGBlock (Fin n)}
    (hA : A ⊆ FGHonestSeats S rho) (hne : A.Nonempty) (hentry : EntryAt H U height)
    (hrows : FixedRowsFG R S E rho H T pair A r height Q U)
    (hParents : ∀ x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq K X.parent)
    (hslot : X.slot = s)
    (read : ∃ nd, proposalStateAt E rho I s = some nd ∧
      parentFG nd (R.erase X).parent = some X.parent ∧
      (fold nd s X.parent).h = (H X.parent).h ∧
      (fold nd s X.parent).T_h = (H X.parent).T_h ∧
      parentHeight nd s X.parent = ((fold nd s X.parent).h, (fold nd s X.parent).T_h.root) ∧
      ∀ a, validFor nd s X.parent a =
        match S.decode a with | none => false | some b => Window.r6w (fold nd s X.parent) b)
    (decodeRows : ∀ j x rSent a, HonestRowAt S E rho T j x rSent a →
      ∃ b, S.decode a = some b ∧ b.height_pair = pair a) :
    FGBlock.Preceq U X.parent ∧
    ∀ i ∈ A, let x := safetyHolder S rho i; ∃ K nd j rSent a,
      postClock E rho x (T.action r) = some nd ∧
      actionSourceFG R E rho T x r = some (some K) ∧ K ∈ (R.core nd).fg.TF ∧
      Block.Preceq Q (R.erase K) ∧ FGBlock.Preceq U K ∧ K.slot ≤ r * T.roundSlots ∧
      (H K).h = height ∧ (H K).T_h = U ∧ rSent ≤ r ∧ HonestRowAt S E rho T j x rSent a ∧
      NamesEntry pair .progress a height U ∧
      ((H X.parent).h = height →
        ValidForParent E rho I parentFG validFor X.slot (R.erase X) a ∧
        HeightMatch E rho I (fun a => namedEntry (pair a)) parentFG parentHeight
          X.slot (R.erase X) a) := by
  obtain ⟨i₀, hi₀⟩ := hne
  let x₀ := safetyHolder S rho i₀
  have hx₀ : x₀ ∈ rho.honest := by
    simpa only [FGHonestSeats_def, Finset.mem_filter, Finset.mem_univ, true_and] using hA hi₀
  obtain ⟨K₀, _, _, _, _, _, hK₀, _, _, hUK₀, _⟩ := hrows i₀ hi₀
  have hUP := KitFG.preceq_trans hUK₀ (hParents x₀ K₀ hx₀ hK₀)
  refine ⟨hUP, ?_⟩
  intro i hi
  let x := safetyHolder S rho i
  obtain ⟨K, nd, j, rSent, a, hnd, hK, hmem, hQ, hUK, hKslot, hh, hKU, hr, ha, hn⟩ :=
    hrows i hi
  refine ⟨K, nd, j, rSent, a, hnd, hK, hmem, hQ, hUK, hKslot, hh, hKU, hr, ha, hn, ?_⟩
  intro hheight
  obtain ⟨nd', hread, hparent, hfh, hft, hph, hv⟩ := read
  exact p0d3_same_row R S E rho H I pair parentFG parentHeight validFor fold Ef laws
    hslot hentry hUP hheight hread hparent ⟨hfh, hft⟩ hph
    (decodeRows j x rSent a ha) hn (hv a)

include laws in
/-- SAME: select the opening batch before using the new proposal's parent read. -/
theorem p0d3_same_batch_holder {A : Finset (Fin n)} {r height : Nat} {s : Slot} {Q : Block}
    {X : FGBlock (Fin n)} (hA : A ⊆ FGHonestSeats S rho) (hne : A.Nonempty)
    (batch : ∃ U, EntryAt H U height ∧ U.slot ≤ r * T.roundSlots ∧
      FixedRowsFG R S E rho H T pair A r height Q U)
    (hParents : ∀ x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq K X.parent)
    (hslot : X.slot = s)
    (read : ∃ nd, proposalStateAt E rho I s = some nd ∧
      parentFG nd (R.erase X).parent = some X.parent ∧
      (fold nd s X.parent).h = (H X.parent).h ∧
      (fold nd s X.parent).T_h = (H X.parent).T_h ∧
      parentHeight nd s X.parent = ((fold nd s X.parent).h, (fold nd s X.parent).T_h.root) ∧
      ∀ a, validFor nd s X.parent a =
        match S.decode a with | none => false | some b => Window.r6w (fold nd s X.parent) b)
    (decodeRows : ∀ j x rSent a, HonestRowAt S E rho T j x rSent a →
      ∃ b, S.decode a = some b ∧ b.height_pair = pair a) :
    ∃ U, EntryAt H U height ∧ U.slot ≤ r * T.roundSlots ∧ FGBlock.Preceq U X.parent ∧
    ∀ i ∈ A, let x := safetyHolder S rho i; ∃ K nd j rSent a,
      postClock E rho x (T.action r) = some nd ∧
      actionSourceFG R E rho T x r = some (some K) ∧ K ∈ (R.core nd).fg.TF ∧
      Block.Preceq Q (R.erase K) ∧ FGBlock.Preceq U K ∧ K.slot ≤ r * T.roundSlots ∧
      (H K).h = height ∧ (H K).T_h = U ∧ rSent ≤ r ∧ HonestRowAt S E rho T j x rSent a ∧
      NamesEntry pair .progress a height U ∧
      ((H X.parent).h = height →
        ValidForParent E rho I parentFG validFor X.slot (R.erase X) a ∧
        HeightMatch E rho I (fun a => namedEntry (pair a)) parentFG parentHeight
          X.slot (R.erase X) a) := by
  obtain ⟨U, hU, hslotU, hrows⟩ := batch
  obtain ⟨hUP, hsame⟩ := p0d3_same_batch_on_holder R S E rho H T I pair
    parentFG parentHeight validFor fold Ef laws hA hne hU hrows hParents hslot read decodeRows
  exact ⟨U, hU, hslotU, hUP, hsame⟩

include laws in
/-- SAME: select the opening batch before using the new proposal's parent read. -/
theorem healing_promotion_same_rows_on_holder {A : Finset (Fin n)}
    {r height : Nat} {s : Slot} {Q : Block}
    {X : FGBlock (Fin n)} (hA : A ⊆ FGHonestSeats S rho) (hne : A.Nonempty)
    (hentry : OpeningEntry R E rho H T r height)
    (hcovered : OpeningCoveredFG R S E rho H T pair A r Q)
    (entryAgreement : ∀ x y K L, x ∈ rho.honest → y ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) →
      actionSourceFG R E rho T y r = some (some L) →
      (H K).T_h.root = (H L).T_h.root → (H K).T_h = (H L).T_h)
    (sourceSlot : ∀ x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → K.slot ≤ r * T.roundSlots)
    (ancestorSlot : ∀ x K A, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq A K →
      A.slot ≤ K.slot)
    (hParents : ∀ x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq K X.parent)
    (hslot : X.slot = s)
    (read : ∃ nd, proposalStateAt E rho I s = some nd ∧
      parentFG nd (R.erase X).parent = some X.parent ∧
      (fold nd s X.parent).h = (H X.parent).h ∧
      (fold nd s X.parent).T_h = (H X.parent).T_h ∧
      parentHeight nd s X.parent = ((fold nd s X.parent).h, (fold nd s X.parent).T_h.root) ∧
      ∀ a, validFor nd s X.parent a =
        match S.decode a with | none => false | some b => Window.r6w (fold nd s X.parent) b)
    (decodeRows : ∀ j x rSent a, HonestRowAt S E rho T j x rSent a →
      ∃ b, S.decode a = some b ∧ b.height_pair = pair a) :
    ∃ U, EntryAt H U height ∧ U.slot ≤ r * T.roundSlots ∧ FGBlock.Preceq U X.parent ∧
    ∀ i ∈ A, let x := safetyHolder S rho i; ∃ K nd j rSent a,
      postClock E rho x (T.action r) = some nd ∧
      actionSourceFG R E rho T x r = some (some K) ∧ K ∈ (R.core nd).fg.TF ∧
      Block.Preceq Q (R.erase K) ∧ FGBlock.Preceq U K ∧ K.slot ≤ r * T.roundSlots ∧
      (H K).h = height ∧ (H K).T_h = U ∧ rSent ≤ r ∧ HonestRowAt S E rho T j x rSent a ∧
      NamesEntry pair .progress a height U ∧
      ((H X.parent).h = height →
        ValidForParent E rho I parentFG validFor X.slot (R.erase X) a ∧
        HeightMatch E rho I (fun a => namedEntry (pair a)) parentFG parentHeight
          X.slot (R.erase X) a) := by
  have batch := healing_promotion_bounded_rows_holder R S E rho H T pair Ef laws
    hA hne hentry hcovered entryAgreement sourceSlot ancestorSlot
  exact p0d3_same_batch_holder R S E rho H T I pair parentFG parentHeight validFor fold Ef laws
    hA hne batch hParents hslot read decodeRows

include laws in
/-- SAME: select the opening batch before using the new proposal's parent read. -/
theorem healing_promotion_same_rows_holder {A : Finset (Fin n)}
    {r height : Nat} {s : Slot} {Q : Block}
    {X : FGBlock (Fin n)} (hA : A ⊆ FGHonestSeats S rho) (hne : A.Nonempty)
    (hentry : OpeningEntry R E rho H T r height)
    (hcovered : OpeningCoveredFG R S E rho H T pair A r Q)
    (entryAgreement : ∀ x y K L, x ∈ rho.honest → y ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) →
      actionSourceFG R E rho T y r = some (some L) →
      (H K).T_h.root = (H L).T_h.root → (H K).T_h = (H L).T_h)
    (sourceSlot : ∀ x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → K.slot ≤ r * T.roundSlots)
    (ancestorSlot : ∀ x K A, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq A K →
      A.slot ≤ K.slot)
    (hParents : ∀ x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq K X.parent)
    (hslot : X.slot = s)
    (read : ∃ nd, proposalStateAt E rho I s = some nd ∧
      parentFG nd (R.erase X).parent = some X.parent ∧
      (fold nd s X.parent).h = (H X.parent).h ∧
      (fold nd s X.parent).T_h = (H X.parent).T_h ∧
      parentHeight nd s X.parent = ((fold nd s X.parent).h, (fold nd s X.parent).T_h.root) ∧
      ∀ a, validFor nd s X.parent a =
        match S.decode a with | none => false | some b => Window.r6w (fold nd s X.parent) b)
    (decodeRows : ∀ j x rSent a, HonestRowAt S E rho T j x rSent a →
      ∃ b, S.decode a = some b ∧ b.height_pair = pair a) :
    ∃ U, EntryAt H U height ∧ U.slot ≤ r * T.roundSlots ∧ FGBlock.Preceq U X.parent ∧
    ∀ i ∈ A, let x := safetyHolder S rho i; ∃ K nd j rSent a,
      postClock E rho x (T.action r) = some nd ∧
      actionSourceFG R E rho T x r = some (some K) ∧ K ∈ (R.core nd).fg.TF ∧
      Block.Preceq Q (R.erase K) ∧ FGBlock.Preceq U K ∧ K.slot ≤ r * T.roundSlots ∧
      (H K).h = height ∧ (H K).T_h = U ∧ rSent ≤ r ∧ HonestRowAt S E rho T j x rSent a ∧
      NamesEntry pair .progress a height U ∧
      ((H X.parent).h = height →
        ValidForParent E rho I parentFG validFor X.slot (R.erase X) a ∧
        HeightMatch E rho I (fun a => namedEntry (pair a)) parentFG parentHeight
          X.slot (R.erase X) a) := by
  exact healing_promotion_same_rows_on_holder R S E rho H T I pair
    parentFG parentHeight validFor fold Ef laws hA hne hentry hcovered
    entryAgreement sourceSlot ancestorSlot hParents hslot read decodeRows

end AvailableChain.FGCompose
end
