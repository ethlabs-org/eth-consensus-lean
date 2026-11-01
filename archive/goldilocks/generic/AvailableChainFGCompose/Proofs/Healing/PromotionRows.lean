module
public import AvailableChainFGCompose.Proofs.Healing.Promotion
public import AvailableChainKitFG.Ancestry
public import AvailableChainSimplexFG.Window

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
/-- SAME: decode the fixed wire and prove R6-window from its matching height pair.
The finality field is retained and can have any value. -/
theorem p0d3_same_row {s : Slot} {X U : FGBlock (Fin n)} {height : Nat} {nd : Prot.State}
    (hslot : X.slot = s) (hentry : EntryAt H U height)
    (hpath : FGBlock.Preceq U X.parent) (hheight : (H X.parent).h = height)
    (hread : proposalStateAt E rho I s = some nd)
    (hparent : parentFG nd (R.erase X).parent = some X.parent)
    (hfold : (fold nd s X.parent).h = (H X.parent).h ∧
      (fold nd s X.parent).T_h = (H X.parent).T_h)
    (hparentHeight : parentHeight nd s X.parent =
      ((fold nd s X.parent).h, (fold nd s X.parent).T_h.root))
    {a : Wire} (decoded : ∃ b, S.decode a = some b ∧ b.height_pair = pair a)
    (hn : NamesEntry pair .progress a height U)
    (hvalid : validFor nd s X.parent a =
      match S.decode a with | none => false | some b => Window.r6w (fold nd s X.parent) b) :
    ValidForParent E rho I parentFG validFor X.slot (R.erase X) a ∧
      HeightMatch E rho I (fun a => namedEntry (pair a)) parentFG parentHeight
        X.slot (R.erase X) a := by
  have hT : (H X.parent).T_h = U :=
    (laws.entry_plateau hpath (hentry.1.trans hheight.symm)).symm.trans hentry.2
  have hh : (fold nd s X.parent).h = height := hfold.1.trans hheight
  have ht : (fold nd s X.parent).T_h = U := hfold.2.trans hT
  obtain ⟨b, hb, hpair⟩ := decoded
  obtain ⟨timeout, hn⟩ := hn
  have hm : Window.heightMatch (fold nd s X.parent) b = true := by
    rw [Window.heightMatch_def, hpair, hn, hh, ht]
    change decide (height = height ∧ U.root = U.root) = true
    exact decide_eq_true ⟨rfl, rfl⟩
  have hv : validFor nd s X.parent a = true := by
    simp only [hvalid, hb, Window.r6w_def, hm, Bool.true_or]
  rw [hslot]
  refine ⟨⟨nd, X.parent, hread, hparent, hv⟩, nd, X.parent, hread, hparent, ?_⟩
  dsimp only
  rw [hparentHeight, hn, hh, ht]
  rfl

include laws in
/-- SAME: preserve a given fixed batch while transferring its entry to the actual parent. -/
theorem p0d3_same_batch_on {r height : Nat} {s : Slot}
    {Q : Block} {X U : FGBlock (Fin n)}
    (hne : rho.honest.Nonempty) (hentry : EntryAt H U height)
    (hrows : FixedRows R S E rho H T pair r height Q U)
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
    ∀ x ∈ rho.honest, ∃ K nd j rSent a,
      postClock E rho x (T.action r) = some nd ∧
      actionSourceFG R E rho T x r = some (some K) ∧ K ∈ (R.core nd).fg.TF ∧
      Block.Preceq Q (R.erase K) ∧ FGBlock.Preceq U K ∧ K.slot ≤ r * T.roundSlots ∧
      (H K).h = height ∧ (H K).T_h = U ∧ rSent ≤ r ∧ HonestRowAt S E rho T j x rSent a ∧
      NamesEntry pair .progress a height U ∧
      ((H X.parent).h = height →
        ValidForParent E rho I parentFG validFor X.slot (R.erase X) a ∧
        HeightMatch E rho I (fun a => namedEntry (pair a)) parentFG parentHeight
          X.slot (R.erase X) a) := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨K₀, _, _, _, _, _, hK₀, _, _, hUK₀, _⟩ := hrows x₀ hx₀
  have hUP := KitFG.preceq_trans hUK₀ (hParents x₀ K₀ hx₀ hK₀)
  refine ⟨hUP, ?_⟩
  intro x hx
  obtain ⟨K, nd, j, rSent, a, hnd, hK, hmem, hQ, hUK, hKslot, hh, hKU, hr, ha, hn⟩ :=
    hrows x hx
  refine ⟨K, nd, j, rSent, a, hnd, hK, hmem, hQ, hUK, hKslot, hh, hKU, hr, ha, hn, ?_⟩
  intro hheight
  obtain ⟨nd', hread, hparent, hfh, hft, hph, hv⟩ := read
  exact p0d3_same_row R S E rho H I pair parentFG parentHeight validFor fold Ef laws
    hslot hentry hUP hheight hread hparent ⟨hfh, hft⟩ hph
    (decodeRows j x rSent a ha) hn (hv a)

include laws in
/-- SAME: select the opening batch before using the new proposal's parent read. -/
theorem p0d3_same_batch {r height : Nat} {s : Slot} {Q : Block}
    {X : FGBlock (Fin n)} (hne : rho.honest.Nonempty)
    (batch : ∃ U, EntryAt H U height ∧ U.slot ≤ r * T.roundSlots ∧
      FixedRows R S E rho H T pair r height Q U)
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
    ∀ x ∈ rho.honest, ∃ K nd j rSent a,
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
  obtain ⟨hUP, hsame⟩ := p0d3_same_batch_on R S E rho H T I pair
    parentFG parentHeight validFor fold Ef laws hne hU hrows hParents hslot read decodeRows
  exact ⟨U, hU, hslotU, hUP, hsame⟩

include laws in
/-- SAME: select the opening batch before using the new proposal's parent read. -/
theorem healing_promotion_same_rows_on {r height : Nat} {s : Slot} {Q : Block}
    {X : FGBlock (Fin n)} (hne : rho.honest.Nonempty)
    (hentry : OpeningEntry R E rho H T r height)
    (hcovered : OpeningCovered R S E rho H T pair r Q)
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
    ∀ x ∈ rho.honest, ∃ K nd j rSent a,
      postClock E rho x (T.action r) = some nd ∧
      actionSourceFG R E rho T x r = some (some K) ∧ K ∈ (R.core nd).fg.TF ∧
      Block.Preceq Q (R.erase K) ∧ FGBlock.Preceq U K ∧ K.slot ≤ r * T.roundSlots ∧
      (H K).h = height ∧ (H K).T_h = U ∧ rSent ≤ r ∧ HonestRowAt S E rho T j x rSent a ∧
      NamesEntry pair .progress a height U ∧
      ((H X.parent).h = height →
        ValidForParent E rho I parentFG validFor X.slot (R.erase X) a ∧
        HeightMatch E rho I (fun a => namedEntry (pair a)) parentFG parentHeight
          X.slot (R.erase X) a) := by
  have batch := healing_promotion_bounded_rows R S E rho H T pair Ef laws
    hne hentry hcovered entryAgreement sourceSlot ancestorSlot
  exact p0d3_same_batch R S E rho H T I pair parentFG parentHeight validFor fold Ef laws
    hne batch hParents hslot read decodeRows

include laws in
/-- SAME: select the opening batch before using the new proposal's parent read. -/
theorem healing_promotion_same_rows {r height : Nat} {s : Slot} {Q : Block}
    {X : FGBlock (Fin n)} (hne : rho.honest.Nonempty)
    (hentry : OpeningEntry R E rho H T r height)
    (hcovered : OpeningCovered R S E rho H T pair r Q)
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
    ∀ x ∈ rho.honest, ∃ K nd j rSent a,
      postClock E rho x (T.action r) = some nd ∧
      actionSourceFG R E rho T x r = some (some K) ∧ K ∈ (R.core nd).fg.TF ∧
      Block.Preceq Q (R.erase K) ∧ FGBlock.Preceq U K ∧ K.slot ≤ r * T.roundSlots ∧
      (H K).h = height ∧ (H K).T_h = U ∧ rSent ≤ r ∧ HonestRowAt S E rho T j x rSent a ∧
      NamesEntry pair .progress a height U ∧
      ((H X.parent).h = height →
        ValidForParent E rho I parentFG validFor X.slot (R.erase X) a ∧
        HeightMatch E rho I (fun a => namedEntry (pair a)) parentFG parentHeight
          X.slot (R.erase X) a) := by
  exact healing_promotion_same_rows_on R S E rho H T I pair
    parentFG parentHeight validFor fold Ef laws hne hentry hcovered
    entryAgreement sourceSlot ancestorSlot hParents hslot read decodeRows

end AvailableChain.FGCompose
end
