module
public import AvailableChainFGSA.Model.Objects
public import AvailableChainFGSA.Proofs.BlockAncestry
public import AvailableChainKitFG.Correspondence

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG

/-! The local carrier bridge (K5 local; `bp.carrier.v1`, bp01 §2.2 steps 1–6).
With the flat wire (DQ1) there is one erasure, `eraseFG`. Step 3 of bp01
becomes the root injectivity of ONE view (`ViewRootInj`). The two-store form
needs the content premise `ContentAgree` (Task 12). -/

variable {V : Type} [DecidableEq V] [RowCodec V]

omit [DecidableEq V] in
/-- [bp bp.carrier.v1; K5 local] (step 1) -/
theorem eraseFG_slot (B : FGBlock V) : (eraseFG B).slot = B.slot := by
  cases B <;> rfl
omit [DecidableEq V] in
/-- [ROOT-DIGEST W1; DC NamedWire.erase] Erasure copies every stored root. -/
theorem eraseFG_root (B : FGBlock V) : (eraseFG B).root = B.root := by
  cases B <;> rfl
omit [DecidableEq V] in
/-- [bp bp.carrier.v1; K5 local] (step 1) -/
theorem eraseFG_parent (B : FGBlock V) : (eraseFG B).parent = eraseFG B.parent := by
  cases B <;> rfl
omit [DecidableEq V] in
/-- [bp bp.carrier.v1; K5 local] (step 1) -/
theorem eraseFG_eq_genesis {B : FGBlock V} : eraseFG B = .genesis ↔ B = .genesis := by
  cases B <;> simp [eraseFG]
omit [DecidableEq V] in
/-- [ROOT-DIGEST W1; DC NamedWire.erase] Erasure keeps every structural field. -/
theorem eraseFG_injective : Function.Injective (eraseFG (V := V)) := by
  intro A
  induction A with
  | genesis =>
    intro B h
    cases B <;> simp_all [eraseFG]
  | node p s r x rs ih =>
    intro B h
    cases B with
    | genesis => simp [eraseFG] at h
    | node q t u y ts =>
      simp only [eraseFG, Block.node.injEq] at h
      obtain ⟨hp, hs, hr, hb⟩ := h
      obtain ⟨hx, hrows⟩ := encFGBody_inj hb
      cases ih hp
      cases hs
      cases hr
      cases hx
      cases hrows
      rfl

/-- [bp bp.carrier.v1; K5 local] (step 2; DC `NamedWire.erase_preceq`) Forward ancestry. -/
theorem eraseFG_preceq {A B : FGBlock V} (h : FGBlock.Preceq A B) :
    Block.Preceq (eraseFG A) (eraseFG B) := by
  induction B with
  | genesis =>
      rw [KitFG.preceq_genesis] at h
      subst h
      exact block_preceq_refl _
  | node p s r_s r rs ih =>
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with rfl | h
      · exact block_preceq_refl _
      · have hp := ih h
        change Block.preceq (eraseFG A) (Block.node (eraseFG p) s r_s (encFGBody r rs)) = true
        simp only [Block.preceq, Bool.or_eq_true]
        exact Or.inr hp
/-- [bp bp.carrier.v1; K5 local] (step 2) Forward compatibility. -/
theorem eraseFG_compatible {A B : FGBlock V} (h : FGBlock.compatible A B = true) :
    Block.Compatible (eraseFG A) (eraseFG B) := by
  unfold FGBlock.compatible at h
  unfold Block.Compatible Block.compatible
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inl (eraseFG_preceq h)
  · exact Or.inr (eraseFG_preceq h)
/-- [ROOT-DIGEST W1; DC NamedWire.erase_preceq] Erasure reflects ancestry globally. -/
theorem eraseFG_preceq_iff {A B : FGBlock V} :
    Block.Preceq (eraseFG A) (eraseFG B) ↔ FGBlock.Preceq A B := by
  constructor
  · intro h
    induction B with
    | genesis =>
      have hg : eraseFG A = .genesis := by
        simpa [eraseFG, Block.Preceq, Block.preceq] using h
      rw [eraseFG_eq_genesis.mp hg]
      exact KitFG.preceq_refl _
    | node p s r x rs ih =>
      simp only [eraseFG, Block.Preceq, Block.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at h
      rcases h with h | h
      · have he : A = .node p s r x rs := eraseFG_injective h
        rw [he]
        exact KitFG.preceq_refl _
      · exact KitFG.preceq_node_of_preceq s r x rs (ih h)
  · exact eraseFG_preceq

/-- [bp bp.carrier.v1; K5 local] (step 3) Erasure is injective on the ancestors
of a root-injective view. -/
theorem eraseFG_injOn {Vw : View V} (hinj : ViewRootInj Vw) {A B : FGBlock V}
    (hA : ∃ W ∈ Vw, FGBlock.Preceq A W) (hB : ∃ W ∈ Vw, FGBlock.Preceq B W)
    (h : eraseFG A = eraseFG B) : A = B :=
  hinj A B hA hB (by rw [← eraseFG_root A, ← eraseFG_root B, h])
/-- [bp bp.carrier.v1; K5 local] (step 4) Erasure reflects ancestry on such a view. -/
theorem preceq_of_eraseFG_preceq {Vw : View V} (hinj : ViewRootInj Vw) {A B : FGBlock V}
    (hA : ∃ W ∈ Vw, FGBlock.Preceq A W) (hB : ∃ W ∈ Vw, FGBlock.Preceq B W)
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B := by
  induction B with
  | genesis =>
      have hg : eraseFG A = .genesis := by
        simpa [eraseFG, Block.Preceq, Block.preceq] using h
      rw [eraseFG_eq_genesis.mp hg]
      exact KitFG.preceq_refl _
  | node p s r_s r rs ih =>
      change Block.preceq (eraseFG A) (Block.node (eraseFG p) s r_s (encFGBody r rs)) = true at h
      simp only [Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · have hAB : A = .node p s r_s r rs := eraseFG_injOn hinj hA hB h
        subst hAB
        exact KitFG.preceq_refl _
      · obtain ⟨W, hW, hBW⟩ := hB
        have hpB : FGBlock.Preceq p (.node p s r_s r rs) := by
          simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true, decide_eq_true_eq]
          exact Or.inr (KitFG.preceq_refl p)
        exact KitFG.preceq_trans (ih ⟨W, hW, KitFG.preceq_trans hpB hBW⟩ h) hpB
/-- [bp bp.carrier.v1; K5 local] (step 5) -/
theorem compatible_iff_eraseFG {Vw : View V} (hinj : ViewRootInj Vw) {A B : FGBlock V}
    (hA : ∃ W ∈ Vw, FGBlock.Preceq A W) (hB : ∃ W ∈ Vw, FGBlock.Preceq B W) :
    FGBlock.compatible A B = Block.compatible (eraseFG A) (eraseFG B) := by
  unfold FGBlock.compatible Block.compatible
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true]
  constructor
  · rintro (h | h)
    · exact Or.inl (eraseFG_preceq h)
    · exact Or.inr (eraseFG_preceq h)
  · rintro (h | h)
    · exact Or.inl (preceq_of_eraseFG_preceq hinj hA hB h)
    · exact Or.inr (preceq_of_eraseFG_preceq hinj hB hA h)
/-- [bp bp.carrier.v1; K5 local] (step 6) A parent-closed, root-injective block
set satisfies `ViewRootInj`. -/
theorem viewRootInj_of_rootInj {T : Finset (FGBlock V)} (hcl : ∀ B ∈ T, B.parent ∈ T)
    (hinj : ∀ X ∈ T, ∀ Y ∈ T, X.root = Y.root → X = Y) : ViewRootInj T := by
  rintro X Y ⟨W, hW, hXW⟩ ⟨W', hW', hYW'⟩ hr
  have hanc := KitFG.ancestor_closed_of_parent_closed T hcl
  exact hinj X (hanc W hW X hXW) Y (hanc W' hW' Y hYW') hr
/-- [bp bp.carrier.v1; K5 local] (step 6, two chains of ONE view) The
`KitFG.accountable` premise. Two chains at two nodes: Task 12,
`rootInjectiveOn_across`. -/
theorem rootInjectiveOn_of_viewRootInj {T : Finset (FGBlock V)} (hinj : ViewRootInj T)
    {B₁ B₂ : FGBlock V} (h₁ : B₁ ∈ T) (h₂ : B₂ ∈ T) : KitFG.RootInjectiveOn B₁ B₂ := by
  have hw : ∀ {X : FGBlock V}, (X.Preceq B₁ ∨ X.Preceq B₂) → ∃ W ∈ T, FGBlock.Preceq X W := by
    rintro X (h | h)
    · exact ⟨B₁, h₁, h⟩
    · exact ⟨B₂, h₂, h⟩
  intro X Y hX hY hr
  exact hinj X Y (hw hX) (hw hY) hr
/-- [bp bp.carrier.v1; K5 local] The erased blocks of a root-injective view have
distinct roots (the AC `RootInjective` shape, for T7). -/
theorem erase_rootInjective {T : Finset (FGBlock V)} (hinj : ViewRootInj T) :
    ∀ b ∈ T.image eraseFG, ∀ c ∈ T.image eraseFG, b.root = c.root → b = c := by
  intro b hb c hc hr
  obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hc
  rw [eraseFG_root, eraseFG_root] at hr
  rw [hinj X Y ⟨X, hX, KitFG.preceq_refl X⟩ ⟨Y, hY, KitFG.preceq_refl Y⟩ hr]

/-! ### The packed content (D9) -/

section Packing
variable {n : Nat}

/-- [helper] The label code is injective. -/
theorem encLabel_inj : Function.Injective encLabel := by
  intro a b h
  cases a <;> cases b <;> dsimp only [encLabel] at h <;>
    first
    | exact absurd (epair_inj h).1 (by decide)
    | rw [(epair_inj h).2]
    | rfl

/-- [helper] The auth code is injective. -/
theorem encAuth_inj : Function.Injective (encAuth (n := n)) := by
  intro a b h
  cases a <;> cases b <;> simp only [encAuth] at h <;>
    first
    | exact absurd (epair_inj h).1 (by decide)
    | skip
  · obtain ⟨-, h⟩ := epair_inj h
    obtain ⟨hl, hi⟩ := epair_inj h
    rw [encLabel_inj hl, Fin.ext hi]
  · rw [(epair_inj h).2]
  · rfl

/-- [helper] The row-body code is injective. -/
theorem encRowBody_inj : Function.Injective encRowBody := by
  intro a b h
  obtain ⟨hh, hf⟩ := epair_inj h
  cases a; cases b
  cases encHeightPair_inj hh
  cases encOption_inj encFinalityPair_inj hf
  rfl

/-- The payload sum preserves the full vote body. -/
theorem encRowPayload_inj : Function.Injective encRowPayload := by
  rintro ⟨a⟩ ⟨b⟩ h
  have hab := encRowBody_inj (epair_inj h).2
  exact congrArg RowPayload.vote hab

/-- [helper] The signed-row code is injective: it keeps the auth (fixed label and
seat included) and the body. -/
theorem encRowWire_inj : Function.Injective (encRowWire (n := n)) := by
  intro a b h
  obtain ⟨ha, hb⟩ := epair_inj h
  cases a; cases b
  cases encAuth_inj ha
  cases encRowPayload_inj hb
  rfl

/-- [D9] The application value of a packed body. -/
@[simp] theorem appOf_packBody (app : Nat) (rw : List (RowWire n)) :
    appOf (packBody app rw) = app := by
  simp [appOf, packBody, packInner, encFGBody]

/-- [D9] The inner packed value is injective in the application value and the
ordered signed rows. -/
theorem packInner_inj {app app' : Nat} {rw rw' : List (RowWire n)}
    (h : packInner app rw = packInner app' rw') : app = app' ∧ rw = rw' := by
  obtain ⟨ha, hr⟩ := epair_inj h
  exact ⟨ha, encList_inj encRowWire_inj hr⟩

/-- [D9] The packed body is injective in the application value and the ordered
signed rows, rounds included. -/
theorem packBody_inj {app app' : Nat} {rw rw' : List (RowWire n)}
    (h : packBody app rw = packBody app' rw') : app = app' ∧ rw = rw' :=
  packInner_inj (encFGBody_inj h).1

/-- [D9] The content check is the full packing equality of the body. -/
theorem rowsOk_iff (b : Block) (rw : List (RowWire n)) :
    rowsOk b rw = true ↔ b.body = packBody (appOf b.body) rw := by
  simp [rowsOk]

/-- [D9] A node whose body packs the rows passes the content check (the honest
proposer's block, `propose`). -/
theorem rowsOk_node_packBody (P : Block) (s : Slot) (r_s : BlockId) (app : Nat) (rw : List
  (RowWire n)) :
    rowsOk (.node P s r_s (packBody app rw)) rw = true := by
  rw [rowsOk_iff]
  simp [Block.body]

/-- [D9] Two bodies that pass the content check are equal only for equal
ordered signed rows. -/
theorem rows_eq_of_rowsOk {b : Block} {rw rw' : List (RowWire n)} (h : rowsOk b rw = true)
    (h' : rowsOk b rw' = true) : rw = rw' := by
  rw [rowsOk_iff] at h h'
  exact (packBody_inj (h.symm.trans h')).2

/-- [ROOT-DIGEST W1; DC NamedBlocks] The full content check keeps BODY validity. -/
theorem contentOk_rowsOk {p : Params} {b : Block} {raw support : List (HeadWire p.n)}
    {rows : List (RowWire p.n)} (h : contentOk p b raw support rows = true) :
    rowsOk b rows = true := (Bool.and_eq_true_iff.mp h).1

/-- [ROOT-DIGEST W1; DC NamedBlocks] The smart constructor passes both content checks. -/
theorem contentOk_proposalBlock (p : Params) (H : Block) (s : Slot) (app : Nat)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) :
    contentOk p (proposalBlock p H s app raw support rows) raw support rows = true := by
  simp [contentOk, rowsOk, proposalBlock, proposalInput, Block.body, Block.root,
    Block.parent, Block.slot]

end Packing

end AvailableChain.FGSA
end
