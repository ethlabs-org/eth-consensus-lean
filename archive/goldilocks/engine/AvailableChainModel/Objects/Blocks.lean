module
public import Mathlib.Data.Finset.Basic
public import AvailableChainModel.Objects.Codec
public import AvailableChainModel.Objects.Identifiers

@[expose] public section

namespace AvailableChain

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The root of a node block with parent root `pr`, slot `s` and body `x`.
The `+ 1` keeps every node root above `genesisRoot`. -/
def nodeRoot (pr : BlockId) (s : Slot) (x : Nat) : BlockId :=
  ⟨epair pr.value (epair s x) + 1⟩

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
A structural chain block. Protocol wire objects belong to an instance.
ROOT-DIGEST W1; DC NamedBlocks. The proposer of slot `s` signs with the
slot-scoped `Auth.proposer s` (see `Objects/Seats.lean`). A node carries a
body and an explicit root. The run contract limits root collisions. -/
inductive Block where
  | genesis
  | node (parent : Block) (slot : Slot) (root : BlockId) (body : Nat)
deriving DecidableEq, Repr

namespace Block
def slot : Block → Slot
  | .genesis => 0
  | .node _ s _ _ => s

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[ROOT-DIGEST W1; DC NamedBlocks] Read the stored root. -/
def root : Block → BlockId
  | .genesis => genesisRoot
  | .node _ _ r _ => r

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The body of a node block (`0` for genesis). -/
def body : Block → Nat
  | .genesis => 0
  | .node _ _ _ x => x

def parent? : Block → Option (Block)
  | .genesis => none
  | .node p _ _ _ => some p

def parent : Block → Block
  | .genesis => .genesis
  | .node p _ _ _ => p

def depth : Block → Nat
  | .genesis => 0
  | .node p _ _ _ => p.depth + 1

/-- [ROOT-DIGEST-2 W1; DC Blocks.find?] Resolve exactly one distinct stored body. -/
def findByRoot? (tree : List Block) (r : BlockId) : Option Block :=
  match (tree.filter (fun B => B.root == r)).eraseDups with
  | [B] => some B
  | _ => none

/-- [ROOT-DIGEST-2 W1; DC Blocks.find?] First-copy filtering removes duplicates. -/
private theorem lookup_nodup {α : Type} [BEq α] [LawfulBEq α] (xs : List α) :
    xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons a xs =>
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      constructor
      · simp
      · exact lookup_nodup (xs.filter (fun b => !b == a))
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- [ROOT-DIGEST-2 W1; DC Blocks.find?] Characterize a one-body resolution. -/
theorem findByRoot?_spec (tree : List Block) (r : BlockId) (B : Block) :
    findByRoot? tree r = some B ↔
      B ∈ tree ∧ B.root = r ∧ ∀ C ∈ tree, C.root = r → C = B := by
  let xs := (tree.filter (fun C => C.root == r)).eraseDups
  have hm (C : Block) : C ∈ xs ↔ C ∈ tree ∧ C.root = r := by
    simp [xs]
  have hn : xs.Nodup := lookup_nodup _
  unfold findByRoot?
  constructor
  · intro h
    split at h
    · rename_i C he
      cases h
      have hB := (hm B).mp (by simp [xs, he])
      refine ⟨hB.1, hB.2, ?_⟩
      intro C hC hr
      have := (hm C).mpr ⟨hC, hr⟩
      simpa [xs, he] using this
    · contradiction
  · rintro ⟨hB, hr, hu⟩
    have hb : B ∈ xs := (hm B).mpr ⟨hB, hr⟩
    have hall : ∀ C ∈ xs, C = B := fun C hC =>
      hu C ((hm C).mp hC).1 ((hm C).mp hC).2
    have he : xs = [B] := by
      cases hxs : xs with
      | nil => simp [hxs] at hb
      | cons C cs =>
          rw [hxs] at hn hall
          have hc : C = B := hall C (by simp)
          subst C
          have hempty : cs = [] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            intro C hC
            have he := hall C (by simp [hC])
            subst C
            exact (List.nodup_cons.mp hn).1 hC
          simp [hempty]
    change (tree.filter (fun C => C.root == r)).eraseDups = [B] at he
    simp [he]

/-- [ROOT-DIGEST-2 W1; DC Blocks.find?] A resolved body belongs to the domain. -/
theorem findByRoot?_mem {tree : List Block} {r : BlockId} {B : Block}
    (h : findByRoot? tree r = some B) : B ∈ tree :=
  ((findByRoot?_spec tree r B).mp h).1

/-- [ROOT-DIGEST-2 W1; DC Blocks.find?] Resolution keeps the requested identifier. -/
theorem findByRoot?_root {tree : List Block} {r : BlockId} {B : Block}
    (h : findByRoot? tree r = some B) : B.root = r :=
  ((findByRoot?_spec tree r B).mp h).2.1

/-- [ROOT-DIGEST-2 W1; DC Blocks.find?] No other matching body exists in the domain. -/
theorem findByRoot?_unique {tree : List Block} {r : BlockId} {B C : Block}
    (h : findByRoot? tree r = some B) (hC : C ∈ tree) (hr : C.root = r) : C = B :=
  ((findByRoot?_spec tree r B).mp h).2.2 C hC hr

/-- [ROOT-DIGEST-2 W1; DC Blocks.find?] Permutations preserve resolution. -/
theorem findByRoot?_perm {tree tree' : List Block} (h : tree.Perm tree') (r : BlockId) :
    findByRoot? tree r = findByRoot? tree' r := by
  apply Option.ext
  intro B
  simp only [findByRoot?_spec, h.mem_iff]

/-- [ROOT-DIGEST-2 W1; DC Blocks.find?] A member of a root-unique tree resolves. -/
theorem findByRoot?_of_unique {tree : List Block} {B : Block} (hB : B ∈ tree)
    (hu : ∀ C ∈ tree, ∀ D ∈ tree, C.root = D.root → C = D) :
    findByRoot? tree B.root = some B :=
  (findByRoot?_spec tree B.root B).mpr ⟨hB, rfl, fun C hC hr => hu C hC B hB hr⟩

section Ancestry

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
`B ⪯ C`, by walking from `C` to genesis. -/
def preceq (B : Block) : Block → Bool
  | .genesis => decide (B = Block.genesis)
  | C@(.node p _ _ _) => decide (B = C) || preceq B p

def prec (B C : Block) : Bool :=
  !decide (B = C) && preceq B C

def Preceq (B C : Block) : Prop := preceq B C = true

def Prec (B C : Block) : Prop := prec B C = true

instance (B C : Block) : Decidable (Preceq B C) :=
  inferInstanceAs (Decidable (preceq B C = true))

instance (B C : Block) : Decidable (Prec B C) :=
  inferInstanceAs (Decidable (prec B C = true))

def compatible (B C : Block) : Bool :=
  preceq B C || preceq C B

def Compatible (B C : Block) : Prop := compatible B C = true

end Ancestry

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[ROOT-DIGEST W1; DC NamedRootCollisionFree] Scoped node/genesis separation. -/
theorem root_ne_genesis_of_node (p : Block) (s : Slot) (r : BlockId) (x : Nat)
    (hr : (Block.node p s r x).root = genesisRoot → Block.node p s r x = .genesis) :
    (Block.node p s r x).root ≠ genesisRoot := fun h => Block.noConfusion (hr h)

end Block

/-! ### Store lookup by root

The lookup is over the image of `Block.root`, genesis included. This is a
resolved-block model: every carried parent is some `Block`, and the store
check `b.parent ∈ blocks` is equivalent to a lookup by its root. A root-only
wire needs more than these lemmas and a decoder: its adapter must also keep
authentication, dependencies, handler calls, refusals and proposal origin.
That refinement is open. -/

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The parent is in the store exactly when a stored block has its root. This
holds in the resolved-block model only; see the section note for what a
root-only wire needs. -/
theorem parent_mem_iff_root (b : Block) (blocks : List Block)
    (hr : ∀ p ∈ blocks, p.root = b.parent.root → p = b.parent) :
    b.parent ∈ blocks ↔ ∃ p ∈ blocks, p.root = b.parent.root := by
  constructor
  · intro h
    exact ⟨b.parent, h, rfl⟩
  · rintro ⟨p, hp, hroot⟩
    rwa [← hr p hp hroot]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
A test `q` on the stored parent is the same test on the stored block that
the root lookup finds. Pass `q` explicitly. -/
theorem parent_mem_and_iff_root (b : Block) (blocks : List Block) (q : Block → Prop)
    (hr : ∀ p ∈ blocks, p.root = b.parent.root → p = b.parent) :
    (b.parent ∈ blocks ∧ q b.parent) ↔ ∃ p ∈ blocks, p.root = b.parent.root ∧ q p := by
  constructor
  · rintro ⟨h, hq⟩
    exact ⟨b.parent, h, rfl, hq⟩
  · rintro ⟨p, hp, hroot, hq⟩
    rw [← hr p hp hroot]
    exact ⟨hp, hq⟩

private theorem Block.Compatible_eq_1_export : type_of% (@Block.Compatible.eq_1) :=
  @Block.Compatible.eq_1
private theorem Block.compatible_eq_1_export : type_of% (@Block.compatible.eq_1) :=
  @Block.compatible.eq_1

-- ROOT-DIGEST-2 option 3: generate equations in their home module (BUILD B3a).
private theorem Block_Preceq_eq_1_export :
    type_of% (@Block.Preceq.eq_1) := @Block.Preceq.eq_1
private theorem Block_preceq_eq_1_export :
    type_of% (@Block.preceq.eq_1) := @Block.preceq.eq_1
private theorem Block_preceq_eq_2_export :
    type_of% (@Block.preceq.eq_2) := @Block.preceq.eq_2
private theorem Block_preceq_eq_def_export :
    type_of% (@Block.preceq.eq_def) := @Block.preceq.eq_def

end AvailableChain
end
