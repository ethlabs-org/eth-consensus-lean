module
public import AvailableChainPCSA.Model.Frame
public import AvailableChainGeneric.Proofs.Pure.Fold
public import AvailableChainGeneric.Proofs.Pure.BlockOrder
public import AvailableChainFGSA.Proofs.Carrier
public import AvailableChainKitFG.FrameGeometry

public section

/-! PC-SA L*′ root geometry (pcsa34-r4.3 §§3.3, 3.7; plan §3). -/

namespace AvailableChain.PCSA

open AvailableChain.SimplexFG Gen.Pure

/-- PC-SA and FG-SA use the same structural erasure for FG blocks. -/
theorem pcsa_eraseFG_eq {V : Type} [RowCodec V] (B : FGBlock V) :
    eraseFG B = FGSA.eraseFG B := by
  induction B with
  | genesis => rfl
  | node P s r x rs ih =>
    change Block.node (eraseFG P) s r (encFGBody x rs) =
      Block.node (FGSA.eraseFG P) s r (encFGBody x rs)
    rw [ih]

/-- The walk starts at the active view target, or at Z. -/
abbrev walkBase (p : Params) (st : State p.n) (c : Option (PC p.n)) : Block :=
  match c with
  | some v => if frameActive p st v then v.target else eraseFG (controls p st).Z
  | none => eraseFG (controls p st).Z

/-- L*′ keeps live lock targets in the tree, above the start, and compatible
with both the start and the view. -/
abbrev walkLocks (p : Params) (st : State p.n) (c : Option (PC p.n)) : List Block :=
  st.base.obligations.filterMap (fun row =>
    if st.base.now < row.2.2 && (decide (∃ B ∈ fullTree p st, eraseFG B = row.1)) &&
        Block.compatible row.1 (walkBase p st c) &&
        (walkBase p st c).depth < row.1.depth &&
        c.all (fun v => Block.compatible row.1 v.target) then some row.1 else none)

/-- The live root is the depth and root ordered fold over the L*′ locks. -/
theorem pcsa_liveRoot_fold (p : Params) (st : State p.n) (c : Option (PC p.n)) :
    liveRoot p st c = (walkLocks p st c).foldl
      (fun best b => if deeper best b then b else best) (walkBase p st c) := rfl

/-- A retained lock is live, in the tree, and above the start. -/
theorem pcsa_walkLocks_mem (p : Params) (st : State p.n) (c : Option (PC p.n)) (b : Block) :
    b ∈ walkLocks p st c ↔
      ∃ row ∈ st.base.obligations, row.1 = b ∧ st.base.now < row.2.2 ∧
        (∃ B ∈ fullTree p st, eraseFG B = b) ∧
        Block.Compatible b (walkBase p st c) ∧
        (walkBase p st c).depth < b.depth ∧
        c.all (fun v => Block.compatible b v.target) = true := by
  simp only [walkLocks, List.mem_filterMap]
  constructor
  · rintro ⟨row, hr, he⟩
    split at he
    · rename_i ht
      cases he
      have ht' := ht
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
      exact ⟨row, hr, rfl, ht'.1.1.1.1, ht'.1.1.1.2, ht'.1.1.2, ht'.1.2, ht'.2⟩
    · contradiction
  · rintro ⟨row, hr, he, ht, hm, hc, hd, hv⟩
    refine ⟨row, hr, ?_⟩
    change Block.compatible b (walkBase p st c) = true at hc
    simp only [he, ht, decide_true, hm, hc, hd, hv, Bool.and_self, ite_true]

/-- The fold returns the start or one retained lock target. -/
theorem pcsa_liveRoot_origin (p : Params) (st : State p.n) (c : Option (PC p.n)) :
    liveRoot p st c = walkBase p st c ∨ liveRoot p st c ∈ walkLocks p st c := by
  rw [pcsa_liveRoot_fold]
  exact foldl_select_mem deeper _ _

private theorem pcsa_deeper_depth (a b : Block) (h : deeper a b = false) :
    b.depth ≤ a.depth := by
  dsimp only [deeper] at h
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  exact Nat.le_of_not_gt h.1

private theorem pcsa_fold_depth (xs : List Block) (a : Block) :
    a.depth ≤ (xs.foldl (fun best b => if deeper best b then b else best) a).depth ∧
      ∀ b ∈ xs, b.depth ≤
        (xs.foldl (fun best b => if deeper best b then b else best) a).depth := by
  induction xs generalizing a with
  | nil => exact ⟨le_refl _, by simp⟩
  | cons b xs ih =>
    simp only [List.foldl_cons]
    split
    · rename_i hab
      have hd : a.depth ≤ b.depth := by
        dsimp only [deeper] at hab
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq] at hab
        rcases hab with h | ⟨h, _⟩ <;> omega
      exact ⟨hd.trans (ih b).1, fun d hm => by
        rcases List.mem_cons.mp hm with he | hm
        · subst d
          exact (ih b).1
        · exact (ih b).2 d hm⟩
    · rename_i hab
      have hf : deeper a b = false := Bool.eq_false_iff.mpr hab
      exact ⟨(ih a).1, fun d hm => by
        rcases List.mem_cons.mp hm with he | hm
        · subst d
          exact (pcsa_deeper_depth a b hf).trans (ih a).1
        · exact (ih a).2 d hm⟩

/-- The live root has maximum depth among the start and retained locks. -/
theorem pcsa_liveRoot_depth (p : Params) (st : State p.n) (c : Option (PC p.n)) :
    (walkBase p st c).depth ≤ (liveRoot p st c).depth ∧
      ∀ b ∈ walkLocks p st c, b.depth ≤ (liveRoot p st c).depth := by
  rw [pcsa_liveRoot_fold]
  exact pcsa_fold_depth _ _

/-- Each retained lock extends the walk start. -/
theorem pcsa_walkLocks_extends (p : Params) (st : State p.n) (c : Option (PC p.n))
    {b : Block} (hb : b ∈ walkLocks p st c) : Block.Preceq (walkBase p st c) b := by
  obtain ⟨_, _, _, _, _, hc, hd, _⟩ := (pcsa_walkLocks_mem p st c b).mp hb
  rcases Bool.or_eq_true_iff.mp hc with h | h
  · have := prefix_depth b (walkBase p st c) h
    omega
  · exact h

/-- The live root extends its walk start. -/
theorem pcsa_liveRoot_extends_base (p : Params) (st : State p.n) (c : Option (PC p.n)) :
    Block.Preceq (walkBase p st c) (liveRoot p st c) := by
  rcases pcsa_liveRoot_origin p st c with he | hm
  · rw [he]
    exact block_preceq_refl _
  · exact pcsa_walkLocks_extends p st c hm

/-- An active PC view is below the live root. -/
theorem pcsa_liveRoot_extends_view (p : Params) (st : State p.n) (v : PC p.n)
    (hv : frameActive p st v = true) : Block.Preceq v.target (liveRoot p st (some v)) := by
  simpa only [walkBase, hv, ite_true] using pcsa_liveRoot_extends_base p st (some v)

/-- The live root stays compatible with a view when Z is compatible with it. -/
theorem pcsa_liveRoot_compatible_view (p : Params) (st : State p.n) (v : PC p.n)
    (hz : Block.Compatible (eraseFG (controls p st).Z) v.target) :
    Block.Compatible (liveRoot p st (some v)) v.target := by
  rcases pcsa_liveRoot_origin p st (some v) with he | hm
  · rw [he]
    simp only [walkBase]
    split
    · exact block_compatible_of_common (block_preceq_refl _) (block_preceq_refl _)
    · exact hz
  · obtain ⟨_, _, _, _, _, _, _, hv⟩ := (pcsa_walkLocks_mem p st (some v) _).mp hm
    exact hv

/-- A live root is in the full tree if its walk start is in the full tree. -/
theorem pcsa_liveRoot_in_tree (p : Params) (st : State p.n) (c : Option (PC p.n))
    (hb : ∃ B ∈ fullTree p st, eraseFG B = walkBase p st c) :
    ∃ B ∈ fullTree p st, eraseFG B = liveRoot p st c := by
  rcases pcsa_liveRoot_origin p st c with he | hm
  · simpa only [he] using hb
  · obtain ⟨_, _, _, _, ht, _⟩ := (pcsa_walkLocks_mem p st c _).mp hm
    exact ht

/-- Z is below the live root, including when an active view supplies the start. -/
theorem pcsa_liveRoot_extends_Z (p : Params) (st : State p.n) (c : Option (PC p.n)) :
    Block.Preceq (eraseFG (controls p st).Z) (liveRoot p st c) := by
  apply block_preceq_trans (B := walkBase p st c) _ (pcsa_liveRoot_extends_base p st c)
  cases c with
  | none => exact block_preceq_refl _
  | some v =>
    change Block.Preceq _ (if frameActive p st v then v.target else _)
    split
    · rename_i hv
      obtain ⟨B, hB, he⟩ := of_decide_eq_true hv
      rw [← he]
      rw [fullTree_def] at hB
      rw [pcsa_eraseFG_eq, pcsa_eraseFG_eq]
      exact FGSA.eraseFG_preceq
        ((KitFG.mem_filteredFromView (FGSA.heightView p) (controls p st) st.fg.TF B).mp hB).2.2.1
    · exact block_preceq_refl _

/-- With no effective lock, the live root is the walk start. -/
theorem pcsa_liveRoot_of_no_locks (p : Params) (st : State p.n) (c : Option (PC p.n))
    (h : walkLocks p st c = []) : liveRoot p st c = walkBase p st c := by
  rw [pcsa_liveRoot_fold, h, List.foldl_nil]

/-- A common chain bound contains the live root. -/
theorem pcsa_liveRoot_below_bound (p : Params) (st : State p.n) (c : Option (PC p.n))
    (B : Block) (hbase : Block.Preceq (walkBase p st c) B)
    (hlocks : ∀ row ∈ st.base.obligations, st.base.now < row.2.2 →
      Block.Preceq row.1 B) : Block.Preceq (liveRoot p st c) B := by
  rcases pcsa_liveRoot_origin p st c with he | hm
  · simpa only [he] using hbase
  · obtain ⟨row, hr, he, ht, _⟩ := (pcsa_walkLocks_mem p st c _).mp hm
    exact he ▸ hlocks row hr ht

/-- Compatibility of the start and live locks gives compatibility of the root. -/
theorem pcsa_liveRoot_compatible (p : Params) (st : State p.n) (c : Option (PC p.n))
    (B : Block) (hbase : Block.Compatible (walkBase p st c) B)
    (hlocks : ∀ row ∈ st.base.obligations, st.base.now < row.2.2 →
      Block.Compatible row.1 B) : Block.Compatible (liveRoot p st c) B := by
  rcases pcsa_liveRoot_origin p st c with he | hm
  · simpa only [he] using hbase
  · obtain ⟨row, hr, he, ht, _⟩ := (pcsa_walkLocks_mem p st c _).mp hm
    exact he ▸ hlocks row hr ht

/-- On one chain, every effective lock is below the selected root. -/
theorem pcsa_liveRoot_extends_lock (p : Params) (st : State p.n) (c : Option (PC p.n))
    {b : Block} (hb : b ∈ walkLocks p st c)
    (hchain : ∀ A ∈ walkLocks p st c, ∀ B ∈ walkLocks p st c, Block.Compatible A B) :
    Block.Preceq b (liveRoot p st c) := by
  have hd := (pcsa_liveRoot_depth p st c).2 b hb
  rcases pcsa_liveRoot_origin p st c with he | hm
  · obtain ⟨_, _, _, _, _, _, hlt, _⟩ := (pcsa_walkLocks_mem p st c b).mp hb
    rw [he] at hd
    omega
  · rcases Bool.or_eq_true_iff.mp (hchain b hb _ hm) with h | h
    · exact h
    · rw [prefix_eq_of_depth _ _ h hd]
      exact block_preceq_refl _

end AvailableChain.PCSA
end
