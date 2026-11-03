module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
public import ConsensusLean.Instances.Goldilocks.Spec.Node.Handlers
public import Mathlib.Data.Set.Card
@[expose] public section

/-! # A computable mirror of the Goldilocks node: the block table

The first module of a computable mirror of `Node.exec` for the SA (`goldilocksSA`), restricted to
runs whose blocks come from a fixed finite **table**: every non-genesis block has an empty FG
payload, an empty AC payload, and one fixed (faulty) proposer `f`. The mirror is parametric in
the SA parameters (with `Δ = 1`, so `t_s = 4s`), the proposer key and the table.

A table row names its block's root, parent root, slot and input, and lists the roots of its
strict ancestors (`Row.anc`, parent first). `Fix.OK` is the decidable table check: roots
distinct and different from genesis, each row's ancestor list the parent's chain, the parent a
known root of a smaller slot, and the chain without repeats.

For a list `M` of roots closed under parents (`Fix.Closed`), `T M` is the set of their blocks
and `frameOf M` the frame `(T M, genesis, genesis, T M)`: the frame of every FG state of the
fragment (no attestation in a block, so the FG never justifies or finalizes anything). The
module proves ancestry, coherence, depth and `deepest` inside `T M` by the table (`anc_T_blk`,
`frameOK`, `depth_blk`, `deepest_eq`), the slot arithmetic `slot t = ⌊t / 4⌋` and the counting
of finite sets given by lists (`ncard_list`). The classical choices of a best block by a key
(`deepest`, the walk's `IsBest`) are computed by `bestBy` on roots (`best_blk`, `pick_eq`). -/

namespace Consensus.Goldilocks.Test.HalfCommittee

open SA

/-- A row of the block table: root, parent root, slot, input, and the roots of the strict
ancestors, parent first. -/
structure Row where
  /-- The root. -/
  root : Nat
  /-- The root of the parent. -/
  parent : Nat
  /-- The slot. -/
  slot : Nat
  /-- The input (`Block.input`). -/
  input : Nat
  /-- The roots of the strict ancestors, parent first. -/
  anc : List Nat

/-- The fixture of the mirror: SA parameters with `Δ = 1`, the proposer key of the table's
blocks, and the table. -/
structure Fix where
  /-- The SA parameters. -/
  sp : SAParams
  /-- `Δ = 1`. -/
  hΔ : sp.Δ = 1
  /-- The proposer of every table block. -/
  f : Fin sp.n
  /-- The table. -/
  tbl : List Row

/-- The best root of a list by the key `f`: the greatest key, ties by the smaller root. -/
def bestBy (f : Nat → Nat) (L : List Nat) : Option Nat :=
  L.foldl (fun acc r =>
    match acc with
    | none => some r
    | some b => if f b < f r ∨ (f b = f r ∧ r < b) then some r else some b) none

/-- `c` beats `r` by the key `f`: a greater key, or the same key and a smaller root. -/
def Beats (f : Nat → Nat) (c r : Nat) : Prop := f r < f c ∨ (f r = f c ∧ c < r)

/-- The slot of a time with `Δ = 1`: `⌊t / 4⌋`, and `0` before time `0`. -/
def slotT (t : Int) : Nat := (t / 4).toNat

namespace Fix

variable (X : Fix)

/-- The genesis root. -/
abbrev g : Nat := X.sp.genesisRoot

/-- The blocks of the node. -/
abbrev Blk := SA.Blk X.sp.n (List (FG.Att X.sp.n))

/-- The frames of the node. -/
abbrev Frm := SA.Frm X.sp.n (List (FG.Att X.sp.n))

/-- The row of a root. -/
def row (r : Nat) : Option Row := X.tbl.find? (fun b => b.root == r)

/-- Genesis, with the empty AC payload. -/
def gBlk : X.Blk := X.sp.toParams.genesisBlock ([], [])

/-- The block of a row. -/
def mkBlk (b : Row) : X.Blk := ⟨b.root, some b.parent, b.slot, X.f, b.input, [], ([], [])⟩

/-- The block of a root: its row's block, or genesis. -/
def blk (r : Nat) : X.Blk :=
  match X.row r with
  | some b => X.mkBlk b
  | none => X.gBlk

/-- The strict ancestors of a root (none for genesis or an unknown root). -/
def anc (r : Nat) : List Nat :=
  match X.row r with
  | some b => b.anc
  | none => []

/-- The chain of a root: the root and its strict ancestors. -/
def chain (r : Nat) : List Nat := r :: X.anc r

/-- The parent root (genesis for genesis or an unknown root). -/
def par (r : Nat) : Nat :=
  match X.row r with
  | some b => b.parent
  | none => X.g

/-- The slot of a root (`0` for genesis or an unknown root). -/
def slotR (r : Nat) : Nat :=
  match X.row r with
  | some b => b.slot
  | none => 0

/-- The roots of the table. -/
def roots : List Nat := X.tbl.map Row.root

/-- A valid root: genesis or a root of the table. -/
def Valid (r : Nat) : Prop := r = X.g ∨ r ∈ X.roots

instance (r : Nat) : Decidable (X.Valid r) := inferInstanceAs (Decidable (_ ∨ _))

/-- The table check. -/
structure OK : Prop where
  /-- Roots are distinct. -/
  nodup : X.roots.Nodup
  /-- No row has the genesis root. -/
  g_not : X.g ∉ X.roots
  /-- Each row: its ancestors are its parent's chain, the parent is valid and of a smaller
  slot, and its chain has no repeats. -/
  rows : ∀ b ∈ X.tbl, b.anc = X.chain b.parent ∧ X.Valid b.parent ∧
    X.slotR b.parent < b.slot ∧ (b.root :: b.anc).Nodup

instance : Decidable X.OK :=
  decidable_of_iff (X.roots.Nodup ∧ X.g ∉ X.roots ∧ ∀ b ∈ X.tbl, b.anc = X.chain b.parent ∧
      X.Valid b.parent ∧ X.slotR b.parent < b.slot ∧ (b.root :: b.anc).Nodup)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

/-- A list of roots closed under parents, with genesis. -/
structure Closed (M : List Nat) : Prop where
  /-- Genesis is in. -/
  g_mem : X.g ∈ M
  /-- Every root is valid. -/
  valid : ∀ r ∈ M, X.Valid r
  /-- The parent of a non-genesis root is in. -/
  par_mem : ∀ r ∈ M, r ≠ X.g → X.par r ∈ M

instance (M : List Nat) : Decidable (X.Closed M) :=
  decidable_of_iff (X.g ∈ M ∧ (∀ r ∈ M, X.Valid r) ∧ ∀ r ∈ M, r ≠ X.g → X.par r ∈ M)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

/-- The blocks of a list of roots. -/
def T (M : List Nat) : Set X.Blk := {B | ∃ r ∈ M, B = X.blk r}

/-- The frame of the fragment for a tree of roots `M`: tree `T M`, `F = fc_root = genesis`, every
block a viable head. -/
def frameOf (M : List Nat) : X.Frm := ⟨X.T M, X.gBlk, X.gBlk, X.T M⟩

/-- The deepest root of a list (by chain length, ties by the smaller root). -/
def deep (L : List Nat) : Option Nat := bestBy (fun r => (X.chain r).length) L

/-! ## The table -/

variable {X}

theorem row_some {r : Nat} {b : Row} (h : X.row r = some b) : b ∈ X.tbl ∧ b.root = r := by
  unfold row at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem row_none_iff {r : Nat} : X.row r = none ↔ r ∉ X.roots := by
  unfold row roots
  simp [List.find?_eq_none]

theorem row_of_mem (hX : X.OK) {b : Row} (hb : b ∈ X.tbl) : X.row b.root = some b := by
  obtain ⟨b', hb'⟩ : ∃ b', X.row b.root = some b' := by
    cases h : X.row b.root with
    | none => exact absurd (List.mem_map_of_mem hb) (row_none_iff.1 h)
    | some b' => exact ⟨b', rfl⟩
  obtain ⟨hm, hr⟩ := row_some hb'
  rw [hb']
  congr 1
  exact List.inj_on_of_nodup_map hX.nodup hm hb hr

theorem exists_row {r : Nat} (h : r ∈ X.roots) : ∃ b, X.row r = some b := by
  cases hr : X.row r with
  | none => exact absurd h (row_none_iff.1 hr)
  | some b => exact ⟨b, rfl⟩

theorem row_g (hX : X.OK) : X.row X.g = none := row_none_iff.2 hX.g_not

theorem blk_g (hX : X.OK) : X.blk X.g = X.gBlk := by rw [blk, row_g hX]

theorem anc_g (hX : X.OK) : X.anc X.g = [] := by rw [anc, row_g hX]

theorem chain_g (hX : X.OK) : X.chain X.g = [X.g] := by rw [chain, anc_g hX]

theorem slotR_g (hX : X.OK) : X.slotR X.g = 0 := by rw [slotR, row_g hX]

theorem blk_root {r : Nat} (hr : X.Valid r) : (X.blk r).root = r := by
  unfold blk
  split
  · rename_i b hb; exact (row_some hb).2
  · rename_i hb
    rcases hr with rfl | hr
    · rfl
    · exact absurd hr (row_none_iff.1 hb)

theorem blk_slot (r : Nat) : (X.blk r).slot = X.slotR r := by
  unfold blk slotR; split <;> rfl

theorem blk_acPayload (r : Nat) : (X.blk r).acPayload = ([], []) := by
  unfold blk; split <;> rfl

theorem blk_fgPayload (r : Nat) : (X.blk r).fgPayload = [] := by
  unfold blk; split <;> rfl

theorem blk_parent_of_mem {r : Nat} (hr : r ∈ X.roots) : (X.blk r).parent = some (X.par r) := by
  obtain ⟨b, hb⟩ := exists_row hr
  simp only [blk, par, hb]; rfl

theorem blk_parent_g (hX : X.OK) : (X.blk X.g).parent = none := by rw [blk_g hX]; rfl

theorem blk_inj {a b : Nat} (ha : X.Valid a) (hb : X.Valid b) (h : X.blk a = X.blk b) : a = b := by
  rw [← blk_root ha, ← blk_root hb, h]

theorem mem_roots_of_valid {r : Nat} (hr : X.Valid r) (hg : r ≠ X.g) : r ∈ X.roots :=
  hr.resolve_left hg

theorem valid_g : X.Valid X.g := Or.inl rfl

theorem row_facts (hX : X.OK) {r : Nat} (hr : r ∈ X.roots) :
    X.chain r = r :: X.chain (X.par r) ∧ X.Valid (X.par r) ∧ X.slotR (X.par r) < X.slotR r ∧
      (X.chain r).Nodup := by
  obtain ⟨b, hb⟩ := exists_row hr
  obtain ⟨hm, hroot⟩ := row_some hb
  obtain ⟨h1, h2, h3, h4⟩ := hX.rows b hm
  simp only [chain, anc, par, slotR, hb]
  exact ⟨by rw [h1]; rfl, h2, h3, by rw [← hroot]; exact h4⟩

theorem chain_par (hX : X.OK) {r : Nat} (hr : r ∈ X.roots) :
    X.chain r = r :: X.chain (X.par r) := (row_facts hX hr).1

theorem valid_par (hX : X.OK) {r : Nat} (hr : r ∈ X.roots) : X.Valid (X.par r) :=
  (row_facts hX hr).2.1

theorem slotR_par_lt (hX : X.OK) {r : Nat} (hr : r ∈ X.roots) : X.slotR (X.par r) < X.slotR r :=
  (row_facts hX hr).2.2.1

theorem chain_nodup (hX : X.OK) {r : Nat} (hr : X.Valid r) : (X.chain r).Nodup := by
  by_cases hg : r = X.g
  · subst hg; rw [chain_g hX]; exact List.nodup_singleton _
  · exact (row_facts hX (mem_roots_of_valid hr hg)).2.2.2

theorem par_ne (hX : X.OK) {r : Nat} (hr : r ∈ X.roots) : X.par r ≠ r := by
  intro h
  have hn := chain_nodup hX (Or.inr hr)
  rw [chain_par hX hr, List.nodup_cons] at hn
  exact hn.1 (by rw [h]; exact List.mem_cons_self)

/-- Induction along the table: a property of genesis that passes from the parent to each row
holds at every valid root. -/
theorem chain_induction (hX : X.OK) {p : Nat → Prop} (h0 : p X.g)
    (h1 : ∀ r ∈ X.roots, p (X.par r) → p r) {r : Nat} (hr : X.Valid r) : p r := by
  suffices ∀ k r, X.Valid r → (X.chain r).length ≤ k → p r from this _ r hr le_rfl
  intro k
  induction k with
  | zero => intro r _ h; simp [chain] at h
  | succ k ih =>
    intro r hr hk
    by_cases hg : r = X.g
    · exact hg ▸ h0
    · have hm := mem_roots_of_valid hr hg
      refine h1 r hm (ih _ (valid_par hX hm) ?_)
      rw [chain_par hX hm, List.length_cons] at hk
      omega

theorem chain_valid (hX : X.OK) {r : Nat} (hr : X.Valid r) : ∀ a ∈ X.chain r, X.Valid a := by
  refine chain_induction hX (p := fun r => ∀ a ∈ X.chain r, X.Valid a) ?_ ?_ hr
  · intro a ha; rw [chain_g hX, List.mem_singleton] at ha; exact ha ▸ valid_g
  · intro r hm ih a ha
    rw [chain_par hX hm, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact Or.inr hm
    · exact ih a ha

theorem g_mem_chain (hX : X.OK) {r : Nat} (hr : X.Valid r) : X.g ∈ X.chain r := by
  refine chain_induction hX (p := fun r => X.g ∈ X.chain r) ?_ ?_ hr
  · rw [chain_g hX]; exact List.mem_singleton_self _
  · intro r hm ih; rw [chain_par hX hm]; exact List.mem_cons_of_mem _ ih

theorem self_mem_chain (r : Nat) : r ∈ X.chain r := List.mem_cons_self

/-- The chain of a member of a closed list stays in it. -/
theorem chain_sub {M : List Nat} (hX : X.OK) (hM : X.Closed M) {r : Nat} (hr : r ∈ M) :
    ∀ a ∈ X.chain r, a ∈ M := by
  refine chain_induction hX (p := fun r => r ∈ M → ∀ a ∈ X.chain r, a ∈ M) ?_ ?_
    (hM.valid r hr) hr
  · intro h a ha; rw [chain_g hX, List.mem_singleton] at ha; exact ha ▸ h
  · intro r hm ih h a ha
    rw [chain_par hX hm, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact h
    · exact ih (hM.par_mem r h (fun e => hX.g_not (e ▸ hm))) a ha

/-- The chain of an ancestor is a suffix of the chain. -/
theorem chain_mono (hX : X.OK) {r a : Nat} (hr : X.Valid r) (ha : a ∈ X.chain r) :
    ∀ c ∈ X.chain a, c ∈ X.chain r := by
  refine chain_induction hX (p := fun r => ∀ a ∈ X.chain r, ∀ c ∈ X.chain a, c ∈ X.chain r)
    ?_ ?_ hr a ha
  · intro a ha c hc; rw [chain_g hX, List.mem_singleton] at ha; subst ha; exact hc
  · intro r hm ih a ha c hc
    rw [chain_par hX hm, List.mem_cons] at ha ⊢
    rcases ha with rfl | ha
    · rw [chain_par hX hm, List.mem_cons] at hc; exact hc
    · exact Or.inr (ih a ha c hc)

/-! ## Ancestry inside `T M` -/

theorem mem_T {M : List Nat} {B : X.Blk} : B ∈ X.T M ↔ ∃ r ∈ M, B = X.blk r := Iff.rfl

theorem blk_mem_T {M : List Nat} {r : Nat} (hr : r ∈ M) : X.blk r ∈ X.T M := ⟨r, hr, rfl⟩

theorem blk_mem_T_iff {M : List Nat} (hM : X.Closed M) {r : Nat} (hr : X.Valid r) :
    X.blk r ∈ X.T M ↔ r ∈ M := by
  refine ⟨fun ⟨a, ha, h⟩ => ?_, blk_mem_T⟩
  rw [blk_inj hr (hM.valid a ha) h]; exact ha

theorem root_mem_of_T {M : List Nat} (hM : X.Closed M) {B : X.Blk} (hB : B ∈ X.T M) :
    B.root ∈ M ∧ B = X.blk B.root := by
  obtain ⟨r, hr, rfl⟩ := hB
  rw [blk_root (hM.valid r hr)]; exact ⟨hr, rfl⟩

theorem parentIn_T (hX : X.OK) {M : List Nat} (hM : X.Closed M) {a b : Nat} (ha : a ∈ M)
    (hb : b ∈ M) : ParentIn (X.T M) (X.blk a) (X.blk b) ↔ b ≠ X.g ∧ a = X.par b := by
  constructor
  · rintro ⟨-, -, hp⟩
    have hbg : b ≠ X.g := by rintro rfl; rw [blk_parent_g hX] at hp; cases hp
    have hbm := mem_roots_of_valid (hM.valid b hb) hbg
    rw [blk_parent_of_mem hbm, blk_root (hM.valid a ha)] at hp
    exact ⟨hbg, (Option.some_injective _ hp).symm⟩
  · rintro ⟨hbg, rfl⟩
    refine ⟨blk_mem_T ha, blk_mem_T hb, ?_⟩
    rw [blk_parent_of_mem (mem_roots_of_valid (hM.valid b hb) hbg), blk_root (hM.valid _ ha)]

/-- Ancestry inside `T M` of a block of `T M` is membership in its chain. -/
theorem anc_T (hX : X.OK) {M : List Nat} (hM : X.Closed M) {b : Nat} (hb : b ∈ M)
    {A : X.Blk} : Anc (X.T M) A (X.blk b) ↔ ∃ a ∈ X.chain b, A = X.blk a := by
  constructor
  · intro h
    suffices ∀ C, Anc (X.T M) A C → ∀ y ∈ M, C = X.blk y → ∃ a ∈ X.chain y, A = X.blk a from
      this _ h b hb rfl
    intro C hC
    induction hC with
    | refl => intro y _ hy; exact ⟨y, self_mem_chain y, hy⟩
    | @tail c d _ hcd ih =>
      intro y hy hd
      obtain ⟨z, hz, rfl⟩ := hcd.1
      subst hd
      obtain ⟨hyg, rfl⟩ := (parentIn_T hX hM hz hy).1 hcd
      obtain ⟨a, ha, hA⟩ := ih (X.par y) hz rfl
      refine ⟨a, ?_, hA⟩
      rw [chain_par hX (mem_roots_of_valid (hM.valid y hy) hyg)]
      exact List.mem_cons_of_mem _ ha
  · rintro ⟨a, ha, rfl⟩
    refine chain_induction hX
      (p := fun b => b ∈ M → ∀ a ∈ X.chain b, Anc (X.T M) (X.blk a) (X.blk b)) ?_ ?_
      (hM.valid b hb) hb a ha
    · intro _ a ha; rw [chain_g hX, List.mem_singleton] at ha; subst ha; exact .refl
    · intro r hm ih hr a ha
      have hrg : r ≠ X.g := fun e => hX.g_not (e ▸ hm)
      have hp := hM.par_mem r hr hrg
      rw [chain_par hX hm, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact .refl
      · exact (ih hp a ha).tail ((parentIn_T hX hM hp hr).2 ⟨hrg, rfl⟩)

theorem anc_T_blk (hX : X.OK) {M : List Nat} (hM : X.Closed M) {a b : Nat} (ha : X.Valid a)
    (hb : b ∈ M) : Anc (X.T M) (X.blk a) (X.blk b) ↔ a ∈ X.chain b := by
  rw [anc_T hX hM hb]
  refine ⟨fun ⟨c, hc, h⟩ => ?_, fun h => ⟨a, h, rfl⟩⟩
  rw [blk_inj ha (chain_valid hX (hM.valid b hb) c hc) h]; exact hc

theorem coherent_T (hX : X.OK) {M : List Nat} (hM : X.Closed M) : Coherent (X.T M) := by
  refine ⟨fun B hB C hC h => ?_, fun B hB C hC h => ?_⟩
  · calc B = X.blk B.root := (root_mem_of_T hM hB).2
      _ = X.blk C.root := by rw [h]
      _ = C := (root_mem_of_T hM hC).2.symm
  · obtain ⟨b, hb, rfl⟩ := hB
    obtain ⟨c, hc, rfl⟩ := hC
    have hcg : c ≠ X.g := by rintro rfl; rw [blk_parent_g hX] at h; cases h
    have hcm := mem_roots_of_valid (hM.valid c hc) hcg
    rw [blk_parent_of_mem hcm, blk_root (hM.valid b hb)] at h
    rw [blk_slot, blk_slot, ← Option.some_injective _ h]
    exact slotR_par_lt hX hcm

theorem T_eq_image (M : List Nat) : X.T M = X.blk '' {r | r ∈ M} := by
  ext B; simp [T, eq_comm]

theorem T_finite (M : List Nat) : (X.T M).Finite := by
  rw [T_eq_image]; exact (List.finite_toSet M).image _

theorem gBlk_mem_T (hX : X.OK) {M : List Nat} (hM : X.Closed M) : X.gBlk ∈ X.T M :=
  blk_g hX ▸ blk_mem_T hM.g_mem

theorem gBlk_anc (hX : X.OK) {M : List Nat} (hM : X.Closed M) {B : X.Blk} (hB : B ∈ X.T M) :
    Anc (X.T M) X.gBlk B := by
  obtain ⟨b, hb, rfl⟩ := hB
  rw [← blk_g hX, anc_T_blk hX hM valid_g hb]
  exact g_mem_chain hX (hM.valid b hb)

/-- `frameOf M` is a well-formed frame. -/
theorem frameOK (hX : X.OK) {M : List Nat} (hM : X.Closed M) : FrameOK (X.frameOf M) where
  finite := T_finite M
  coherent := coherent_T hX hM
  rooted := ⟨gBlk_mem_T hX hM, fun _ hC => gBlk_anc hX hM hC⟩
  fcRoot_mem := gBlk_mem_T hX hM
  F_anc_fcRoot := .refl
  viableHeads_subset := le_rfl
  fcRoot_anc_viableHeads := fun _ hW => gBlk_anc hX hM hW

/-! ## Counting and depth -/

/-- A set given by an injective image of a list without repeats has the list's length. -/
theorem ncard_list {α β : Type} (h : β → α) {L : List β}
    (hinj : ∀ a ∈ L, ∀ b ∈ L, h a = h b → a = b) (hnd : L.Nodup) :
    {x | ∃ r ∈ L, x = h r}.ncard = L.length := by
  classical
  have e : {x | ∃ r ∈ L, x = h r} = ↑(L.map h).toFinset := by ext x; simp [eq_comm]
  rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup (hnd.map_on hinj), List.length_map]

/-- The set of the members of a list has the length of the list without repeats. -/
theorem ncard_mem {α : Type} [DecidableEq α] (L : List α) : {x | x ∈ L}.ncard = L.dedup.length := by
  have e : {x | x ∈ L} = ↑L.toFinset := by ext x; simp
  rw [e, Set.ncard_coe_finset, List.card_toFinset]

theorem ncard_T {M : List Nat} (hM : X.Closed M) (hnd : M.Nodup) :
    (X.T M).ncard = M.length :=
  ncard_list X.blk (fun a ha b hb h => blk_inj (hM.valid a ha) (hM.valid b hb) h) hnd

theorem depth_blk (hX : X.OK) {M : List Nat} (hM : X.Closed M) {b : Nat} (hb : b ∈ M) :
    depth (X.frameOf M) (X.blk b) = (X.chain b).length := by
  have hv := chain_valid hX (hM.valid b hb)
  have e : {A | (X.frameOf M).Anc A (X.blk b)} = {A | ∃ a ∈ X.chain b, A = X.blk a} := by
    ext A; exact anc_T hX hM hb
  rw [depth, e]
  exact ncard_list X.blk (fun a ha c hc h => blk_inj (hv a ha) (hv c hc) h)
    (chain_nodup hX (hM.valid b hb))

/-! ## The best root -/

theorem bestBy_spec_aux (f : Nat → Nat) (L : List Nat) (acc : Option Nat) (S : List Nat)
    (hacc : ∀ d, acc = some d → d ∈ S ∧ ∀ r ∈ S, r = d ∨ Beats f d r)
    (hnone : acc = none → S = []) :
    ∀ d, L.foldl (fun acc r =>
      match acc with
      | none => some r
      | some b => if f b < f r ∨ (f b = f r ∧ r < b) then some r else some b) acc = some d →
      d ∈ S ++ L ∧ ∀ r ∈ S ++ L, r = d ∨ Beats f d r := by
  induction L generalizing acc S with
  | nil => intro d h; simpa using hacc d h
  | cons x L ih =>
    intro d h
    rw [List.foldl_cons] at h
    have e : S ++ x :: L = (S ++ [x]) ++ L := by simp
    rw [e]
    refine ih _ (S ++ [x]) ?_ ?_ d h
    · intro d' hd'
      cases acc with
      | none =>
        cases hd'; rw [hnone rfl]
        exact ⟨List.mem_singleton_self _, fun r hr => Or.inl (by simpa using hr)⟩
      | some b =>
        obtain ⟨hbS, hb⟩ := hacc b rfl
        simp only at hd'
        split at hd' <;> cases hd'
        · rename_i hx
          refine ⟨by simp, fun r hr => ?_⟩
          rw [List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · right; rcases hb r hr with rfl | h' <;> unfold Beats at * <;> omega
          · exact Or.inl rfl
        · rename_i hx
          refine ⟨by simp [hbS], fun r hr => ?_⟩
          rw [List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · exact hb r hr
          · unfold Beats; omega
    · intro h'
      cases acc with
      | none => simp at h'
      | some b => simp only at h'; split at h' <;> cases h'

theorem bestBy_spec {f : Nat → Nat} {L : List Nat} {d : Nat} (h : bestBy f L = some d) :
    d ∈ L ∧ ∀ r ∈ L, r = d ∨ Beats f d r := by
  simpa using bestBy_spec_aux f L none [] (by simp) (fun _ => rfl) d h

theorem bestBy_eq_none {f : Nat → Nat} {L : List Nat} : bestBy f L = none ↔ L = [] := by
  constructor
  · intro h
    cases L with
    | nil => rfl
    | cons x L =>
      exfalso
      have key : ∀ (L : List Nat) (b : Nat), L.foldl (fun acc r =>
          match acc with
          | none => some r
          | some b => if f b < f r ∨ (f b = f r ∧ r < b) then some r else some b) (some b) ≠
            none := by
        intro L
        induction L with
        | nil => intro b; simp
        | cons y L ih => intro b; simp only [List.foldl_cons]; split <;> exact ih _
      exact key L x h
  · rintro rfl; rfl

/-- The best block of a set given by a list of valid roots, for a key that agrees with `f` on
the list: the block of `bestBy f`, and no other. -/
theorem best_blk {S : Set X.Blk} {L : List Nat} (hv : ∀ r ∈ L, X.Valid r)
    (hS : ∀ B, B ∈ S ↔ ∃ r ∈ L, B = X.blk r) (κ : X.Blk → Nat) (f : Nat → Nat)
    (hκ : ∀ r ∈ L, κ (X.blk r) = f r) :
    let P := fun C : X.Blk => C ∈ S ∧ ∀ D ∈ S, D ≠ C → κ D < κ C ∨ (κ D = κ C ∧ C.root < D.root)
    (∀ d, bestBy f L = some d → P (X.blk d) ∧ ∀ C, P C → C = X.blk d) ∧
      (bestBy f L = none → ∀ C, ¬ P C) := by
  intro P
  refine ⟨fun d hd => ?_, fun hn C hC => ?_⟩
  · obtain ⟨hdL, hbest⟩ := bestBy_spec hd
    have hD : P (X.blk d) := by
      refine ⟨(hS _).2 ⟨d, hdL, rfl⟩, fun C hC hne => ?_⟩
      obtain ⟨r, hr, rfl⟩ := (hS C).1 hC
      rcases hbest r hr with rfl | hb
      · exact absurd rfl hne
      · rw [hκ r hr, hκ d hdL, blk_root (hv d hdL), blk_root (hv r hr)]
        exact hb
    refine ⟨hD, fun C hc => ?_⟩
    by_contra hne
    rcases hc.2 _ hD.1 (Ne.symm hne) with h₁ | ⟨h₁, h₁'⟩ <;>
      rcases hD.2 _ hc.1 hne with h₂ | ⟨h₂, h₂'⟩ <;> omega
  · rw [bestBy_eq_none] at hn; subst hn
    simpa using (hS C).1 hC.1

/-- A classical choice of the unique block satisfying `P`, computed by a root. -/
theorem pick_eq {β : Type} {P : X.Blk → Prop} {o : Option Nat}
    (hsome : ∀ d, o = some d → P (X.blk d) ∧ ∀ C, P C → C = X.blk d)
    (hnone : o = none → ∀ C, ¬ P C) {_ : Decidable (∃ B, P B)} (k : X.Blk → β) (z : β) :
    (if h : ∃ B, P B then k h.choose else z) = (o.map X.blk).elim z k := by
  cases ho : o with
  | none =>
    have : ¬ ∃ B, P B := fun ⟨B, hB⟩ => hnone ho B hB
    simp [this]
  | some d =>
    obtain ⟨hd, huniq⟩ := hsome d ho
    have hex : ∃ B, P B := ⟨_, hd⟩
    simp only [hex, ↓reduceDIte, Option.map_some, Option.elim_some]
    rw [huniq _ hex.choose_spec]

/-- `deepest` of a set given by a list of roots of the tree is the deepest root's block. -/
theorem deepest_eq (hX : X.OK) {M : List Nat} (hM : X.Closed M) {S : Set X.Blk} {L : List Nat}
    (hL : ∀ r ∈ L, r ∈ M) (hS : ∀ B, B ∈ S ↔ ∃ r ∈ L, B = X.blk r) :
    deepest (X.frameOf M) S = (X.deep L).map X.blk := by
  have h := best_blk (fun r hr => hM.valid r (hL r hr)) hS (depth (X.frameOf M))
    (fun r => (X.chain r).length) (fun r hr => depth_blk hX hM (hL r hr))
  unfold deepest
  refine (pick_eq (P := IsDeepest (X.frameOf M) S) h.1 h.2 some none).trans ?_
  unfold deep
  cases bestBy (fun r => (X.chain r).length) L <;> rfl

/-! ## Slots -/

theorem ts_eq (s : Int) : X.sp.ts s = 4 * s := by
  simp only [SAParams.ts, X.hΔ]; ring

/-- With `Δ = 1`, `slot t = ⌊t / 4⌋` (and `0` before time `0`). -/
theorem slot_eq (t : Int) : X.sp.slot t = slotT t := by
  unfold slotT
  by_cases ht : 0 ≤ t
  · have h := SA.slot_eq X.sp ht
    rw [X.hΔ] at h
    omega
  · have h1 : t.toNat = 0 := by omega
    have h2 : (t / 4).toNat = 0 := by omega
    simp only [SAParams.slot, Params.slotOf, h1, h2, Nat.findGreatest_zero]

end Fix

end Consensus.Goldilocks.Test.HalfCommittee

end
