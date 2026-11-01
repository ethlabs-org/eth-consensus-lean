module
public import AvailableChainGridCO.Model.StoreKeys

public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy] {mode : HeadMode}

open AvailableChain.Generic

/-- [ROOT-DIGEST-2 W1; DC legacy HEAD] Keep the old block-mode receipt equation. -/
theorem resolvedBefore_block {n : Nat} (st : State n) (o : Wire n) (cutoff : Time) :
    resolvedBefore st o cutoff = (match headTarget? o with
      | none => false
      | some B => blockKnown st B && B.slot ≤ (headLabel? o).getD 0 &&
          stampVote st o < cutoff && stampBlock st B < cutoff) := by
  unfold resolvedBefore resolvedHead?
  cases ht : headTarget? o with
  | none => rfl
  | some B =>
    by_cases hm : B ∈ st.blocks <;>
      simp [resolveTarget, resolutionTree, blockKnown, hm]

/-- [ROOT-DIGEST-2 W1; DC legacy HEAD] Keep the old block-mode score equation. -/
theorem goldfishScore_block_eq {n : Nat} (tree : List Block)
    (raw support : List (Wire n)) (B : Block) :
    goldfishScore tree raw support B =
      ((seats n raw).filter (fun i => equivocates raw i || (seatVotes support i).any
        (fun o => match headTarget? o with
          | some C => C ∈ tree && C.slot ≤ (headLabel? o).getD 0 && Block.preceq B C
          | none => false))).length := by
  unfold goldfishScore goldfishScoreOn
  congr 1
  apply List.filter_congr
  intro i _
  apply congrArg (fun x => equivocates raw i || x)
  apply List.any_congr rfl
  intro o
  cases ht : headTarget? o with
  | none => rfl
  | some C =>
    by_cases hm : C ∈ tree <;> simp [resolveTarget, hm]

/-- [ROOT-DIGEST-2 W1; DC legacy HEAD] Block-mode prefix support uses the old score domain. -/
theorem prefixSupport_block_eq (p : Params) {n : Nat} (st : State n) (r : Slot) (B : Block) :
    prefixSupport p st r B =
      goldfishScore st.blocks (cleanSupport p st r) (cleanSupport p st r) B := rfl

private theorem foldl_option_origin {α : Type}
    (f : Option α → α → Option α)
    (hchoose : ∀ acc x, f acc x = acc ∨ f acc x = some x)
    (xs : List α) (acc : Option α) (b : α)
    (hresult : xs.foldl f acc = some b) :
    acc = some b ∨ b ∈ xs := by
  induction xs generalizing acc with
  | nil => exact Or.inl hresult
  | cons x xs ih =>
      rcases ih (f acc x) hresult with hfirst | htail
      · rcases hchoose acc x with hkeep | htake
        · exact Or.inl (hkeep.symm.trans hfirst)
        · have heq : x = b := Option.some.inj (htake.symm.trans hfirst)
          exact Or.inr (List.mem_cons.mpr (Or.inl heq.symm))
      · exact Or.inr (List.mem_cons.mpr (Or.inr htail))

/-- [ROOT-DIGEST-2 W1; DC shared HEAD modes] A successful GHOST step selects a stored eligible child
of its anchor. -/
theorem ghostStep_child (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor child : Block)
    (hstep : ghostStep tree score eligible anchor = some child) :
    child ∈ tree ∧ child.parent? = some anchor ∧ eligible child = true := by
  let children := tree.filter (fun b => b.parent? == some anchor && eligible b)
  let select : Option Block → Block → Option Block := fun best b =>
    match best with
    | none => some b
    | some old =>
        if score old < score b || (score old == score b && old.root < b.root)
        then some b else best
  have hchoose : ∀ best b, select best b = best ∨ select best b = some b := by
    intro best b
    cases best with
    | none => exact Or.inr rfl
    | some old =>
        simp only [select]
        split
        · exact Or.inr rfl
        · exact Or.inl rfl
  let best := children.foldl select none
  change (match best with
    | none => none
    | some b =>
      if children.any (fun c => c != b && score c == score b && c.root == b.root)
      then none else some b) = some child at hstep
  cases hbest : best with
  | none => simp [hbest] at hstep
  | some b =>
      have hb : b ∈ children := by
        rcases foldl_option_origin select hchoose children none b hbest with
          himpossible | hmem
        · cases himpossible
        · exact hmem
      simp only [hbest] at hstep
      split at hstep
      · simp at hstep
      · have hchild : b = child := Option.some.inj hstep
        subst b
        have hp := List.mem_filter.mp hb
        have ⟨hparent, helig⟩ := Bool.and_eq_true_iff.mp hp.2
        exact ⟨hp.1, by simpa using hparent, helig⟩

/-- [ROOT-DIGEST-2 W1; DC shared HEAD modes] The GHOST walk returns its anchor or a member of its
tree. This ports
the source `Records.ghost_walk_mem` argument to the list-based walk. -/
theorem ghostWalk_mem (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (fuel : Nat) (anchor : Block) :
    ghostWalk tree score eligible fuel anchor = anchor ∨
      ghostWalk tree score eligible fuel anchor ∈ tree := by
  induction fuel generalizing anchor with
  | zero => exact Or.inl rfl
  | succ fuel ih =>
      simp only [ghostWalk]
      cases hs : ghostStep tree score eligible anchor with
      | none => exact Or.inl rfl
      | some child =>
          change ghostWalk tree score eligible fuel child = anchor ∨
            ghostWalk tree score eligible fuel child ∈ tree
          rcases ih child with he | hm
          · apply Or.inr
            rw [he]
            exact (ghostStep_child tree score eligible anchor child hs).1
          · exact Or.inr hm

omit [LeasePolicy] in
theorem confirmationFrom_mem (p : Params) {n : Nat} (a : Block) (st : State n mode)
    (r : Slot) (B : Block) (hc : confirmationFrom p a st r = some B) :
    B = a ∨ B ∈ st.blocks := by
  unfold confirmationFrom at hc
  dsimp only at hc
  split at hc
  · have he := Option.some.inj hc
    rw [← he]
    rcases ghostWalk_mem st.blocks.eraseDups _ _ st.blocks.eraseDups.length a
      with hg | hm
    · exact Or.inl hg
    · exact Or.inr (List.mem_eraseDups.mp hm)
  · contradiction

theorem gateFrom_eq_writeKeys (p : Params) {n : Nat} (a : Block) (st : State n mode)
    (r : Slot) (C : Block)
    (hc : confirmationFrom p a st r = some C)
    (hguard : st.obligations.any (fun (target, _, _) =>
      !Block.compatible target C) = false) :
    gateFrom p a st r =
      writeKeys { st with
        goldfishRecord := advance st.goldfishRecord C
        genuine := recordGenuine st r (some C)
        stableRecord := advance st.stableRecord C }
        (gateWriteKeys p st r C) (gateTime p r + lifetime p) := by
  simp [gateFrom, hc, hguard, writeKeys_def, gateWriteKeys_def,
    List.foldl_flatMap, List.foldl_map]

private theorem writeKeys_target_origin {n : Nat} (st : State n mode)
    (keys : List (Block × Nat)) (limit : Time) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (writeKeys st keys limit).obligations) :
    (∃ k deadline, (B, k, deadline) ∈ st.obligations) ∨ ∃ k, (B, k) ∈ keys := by
  induction keys generalizing st with
  | nil => exact Or.inl ⟨g, d, hm⟩
  | cons key keys ih =>
      rcases ih _ hm with ⟨k, deadline, hold⟩ | ⟨k, hk⟩
      · rcases List.mem_append.mp hold with hold | hnew
        · exact Or.inl ⟨k, deadline, (List.mem_filter.mp hold).1⟩
        · have he : B = key.1 := congrArg Prod.fst (List.mem_singleton.mp hnew)
          exact Or.inr ⟨key.2, List.mem_cons.mpr (Or.inl (by simp [he]))⟩
      · exact Or.inr ⟨k, List.mem_cons_of_mem key hk⟩

/-- [ROOT-DIGEST-2 W1; DC shared HEAD modes] An anchored gate can add only prefixes of its genuine
result to the map. -/
theorem gateFrom_target_origin (p : Params) {n : Nat} (a : Block) (st : State n mode)
    (r : Slot) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (gateFrom p a st r).obligations) :
    (∃ k deadline, (B, k, deadline) ∈ st.obligations) ∨
      ∃ C, confirmationFrom p a st r = some C ∧ Block.Preceq B C := by
  cases hc : confirmationFrom p a st r with
  | none => exact Or.inl ⟨g, d, by simpa [gateFrom, hc] using hm⟩
  | some C =>
      by_cases hg : st.obligations.any (fun (target, _, _) => !Block.compatible target C) = true
      · exact Or.inl ⟨g, d, by simpa [gateFrom, hc, hg] using hm⟩
      · rw [gateFrom_eq_writeKeys p a st r C hc (Bool.eq_false_iff.mpr hg)] at hm
        rcases writeKeys_target_origin _ _ _ B g d hm with hold | ⟨k, hk⟩
        · exact Or.inl hold
        · obtain ⟨A, hA, hmap⟩ := List.mem_flatMap.mp hk
          obtain ⟨_, _, he⟩ := List.mem_map.mp hmap
          have heA : A = B := congrArg Prod.fst he
          subst A
          exact Or.inr ⟨C, rfl, (Bool.and_eq_true_iff.mp (List.mem_filter.mp hA).2).2⟩

theorem admitVote_blocks (p : Params) {n : Nat} (st : State n mode)
    (o : Wire n mode) : (admitVote p st o).blocks = st.blocks := by
  unfold admitVote
  split <;> simp_all
  split <;> rfl

theorem admitVote_obligations (p : Params) {n : Nat} (st : State n mode)
    (o : Wire n mode) : (admitVote p st o).obligations = st.obligations := by
  unfold admitVote
  split <;> simp_all
  split <;> rfl

private theorem foldl_blocks {n : Nat} {α : Type}
    (f : State n mode → α → State n mode) (xs : List α) (st : State n mode)
    (hf : ∀ acc x, (f acc x).blocks = acc.blocks) :
    (xs.foldl f st).blocks = st.blocks := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih, hf]

theorem gateFrom_blocks (p : Params) {n : Nat} (a : Block) (st : State n mode) (r : Slot) :
    (gateFrom p a st r).blocks = st.blocks := by
  cases hc : confirmationFrom p a st r with
  | none => simp [gateFrom, hc]
  | some C =>
      cases hguard : st.obligations.any (fun (target, _, _) =>
          !Block.compatible target C) with
      | true => simp [gateFrom, hc, hguard]
      | false =>
          simp only [gateFrom, hc, hguard]
          apply foldl_blocks
          intro acc b
          apply foldl_blocks
          intro acc g
          rfl

theorem admitVote_stable (p : Params) {n : Nat} (st : State n mode) (o : Wire n mode) :
    (admitVote p st o).stableRecord = st.stableRecord := by
  unfold admitVote
  split
  · dsimp only; split <;> rfl
  · rfl

@[simp] theorem genesis_prefix (B : Block) : Block.Preceq .genesis B := by
  induction B <;> simp_all [Block.Preceq, Block.preceq]

theorem block_preceq_self (b : Block) : Block.Preceq b b := by
  cases b <;> simp [Block.Preceq, Block.preceq]

private theorem preceq_trans (A B C : Block)
    (hAB : Block.preceq A B = true)
    (hBC : Block.preceq B C = true) :
    Block.preceq A C = true := by
  induction C with
  | genesis =>
      have h : B = .genesis := by simpa [Block.preceq] using hBC
      subst B
      exact hAB
  | node parent slot r_slot root ih =>
      have h : B = .node parent slot r_slot root ∨ Block.preceq B parent = true := by
        simpa [Block.preceq, Bool.or_eq_true] using hBC
      rcases h with h | h
      · subst B
        exact hAB
      · have hAC := ih h
        simp [Block.preceq, hAC]

private theorem preceq_parent (anchor child : Block)
    (hparent : child.parent? = some anchor) :
    Block.preceq anchor child = true := by
  cases child with
  | genesis => simp [Block.parent?] at hparent
  | node parent slot r_slot root =>
      have h : parent = anchor := by simpa [Block.parent?] using hparent
      subst parent
      simp only [Block.preceq, Bool.or_eq_true]
      exact Or.inr (block_preceq_self anchor)

theorem ghostWalk_extends (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (fuel : Nat) (anchor : Block) :
    Block.preceq anchor (ghostWalk tree score eligible fuel anchor) = true := by
  induction fuel generalizing anchor with
  | zero => exact block_preceq_self anchor
  | succ fuel ih =>
      cases hstep : ghostStep tree score eligible anchor with
      | none => simpa [ghostWalk, hstep] using! block_preceq_self anchor
      | some child =>
          have hchild := ghostStep_child tree score eligible anchor child hstep
          have hpre := preceq_parent anchor child hchild.2.1
          simpa [ghostWalk, hstep] using
            preceq_trans anchor child (ghostWalk tree score eligible fuel child)
              hpre (ih child)

theorem ghost_extends (anchor : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool) :
    Block.preceq anchor (ghost anchor tree score eligible) = true := by
  exact ghostWalk_extends tree.eraseDups score eligible tree.eraseDups.length anchor

private theorem fold_admitVote_obligations (p : Params) {n : Nat}
    (raw : List (HeadWire n mode)) (st : State n mode) :
    (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st).obligations =
      st.obligations := by
  induction raw generalizing st with
  | nil => rfl
  | cons row raw ih =>
      simpa only [List.foldl_cons] using
        (ih (admitVote p st (fromHead row))).trans
          (admitVote_obligations p st (fromHead row))

theorem admitProposal_obligations (p : Params) {n : Nat}
    (st : State n mode) (o : Wire n mode) (b : Block) (raw : List (HeadWire n mode)) :
    (admitProposal p st o b raw).obligations = st.obligations := by
  let bad : Bool :=
    b.slot > (st.now / (4 * p.Δ)).toNat || !blockKnown st b.parent ||
      b ∈ st.blocks || !(b.parent.slot < b.slot) ||
      !(match o.auth with
        | .proposer s => s == b.slot
        | _ => false)
  let st' : State n mode := { st with
    blocks := st.blocks ++ [b]
    blockStamp := st.blockStamp ++ [(b, st.now)]
    proposals := st.proposals ++ [o] }
  change (if bad then st else
    raw.foldl (fun acc row => admitVote p acc (fromHead row)) st').obligations =
      st.obligations
  split
  · rfl
  · exact fold_admitVote_obligations p raw st'

end AvailableChain.GridCO
end
