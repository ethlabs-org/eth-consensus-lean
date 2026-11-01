module
public import AvailableChainFGSA.Proofs.Port.Resolution
public import AvailableChainFGSA.Proofs.Port.VoteMerge
public import AvailableChainFGSA.Proofs.Head.Pool -- shake: keep (re-export)

public section

namespace AvailableChain.FGSA.Next

open AvailableChain.SimplexFG

/-- Feeds `fgsa_active_support_of_receipt`: the held head must resolve in the
cumulative domain and extend F. No root uniqueness assumption is added. -/
theorem port_proposerSupport_positive {n : Nat} (st : State n) (s : Slot)
    (o : GridCO.Wire n .root) (H : Block)
    (ho : o ∈ GridCO.votesAt st.base (s - 1))
    (hh : H ∈ st.base.blocks) (ht : ∃ r, GridCO.headTarget? o = some r ∧
      GridCO.resolveTarget .root (GridCO.resolutionTree st.base) r = some H)
    (hF : Block.Preceq (eraseFG st.fg.F) H) (hs : H.slot ≤ s - 1) :
    o ∈ proposerSupportNext st s := by
  apply proposerSupportNext_keep st s o H ho _ hF hs
  obtain ⟨r, hr, hresolve⟩ := ht
  simp [GridCO.resolvedHead?, hr, hresolve, hh]

/-- Feeds `fgsa_score_eq_on_retained_suffix`: express the score with the same
cumulative resolver as the support readers. -/
theorem port_scoreOn_resolved {n : Nat} (v : GridCO.State n .root)
    (raw support : List (GridCO.Wire n .root)) (B : Block) :
    GridCO.goldfishScoreOn (GridCO.resolutionTree v) v.blocks raw support B =
      ((GridCO.seats n raw).filter (fun i => GridCO.equivocates raw i ||
        (GridCO.seatVotes support i).any (fun o => (GridCO.resolvedHead? v o).any
          (fun H => decide (H.slot ≤ (GridCO.headLabel? o).getD 0) &&
            Block.preceq B H)))).length := by
  unfold GridCO.goldfishScoreOn
  congr 2
  funext i
  congr 1
  apply List.any_congr rfl
  intro o
  unfold GridCO.resolvedHead?
  cases ht : GridCO.headTarget? o with
  | none => rfl
  | some r =>
    cases hr : GridCO.resolveTarget .root (GridCO.resolutionTree v) r with
    | none => simp [hr]
    | some H =>
      by_cases hm : H ∈ v.blocks <;> simp [hr, hm]

/-- Feeds proposer, frozen, and FG-head score reads: a prefix filter preserves
support incidence above F without preserving the internal support list. -/
theorem port_support_filter_incidence {n : Nat} (v : GridCO.State n .root)
    (support : List (GridCO.Wire n .root)) (F B : Block) (hFB : Block.Preceq F B)
    (i : Fin n) :
    (GridCO.seatVotes (support.filter (fun o =>
      (GridCO.resolvedHead? v o).any (Block.preceq F))) i).any (fun o =>
        (GridCO.resolvedHead? v o).any (fun H =>
          decide (H.slot ≤ (GridCO.headLabel? o).getD 0) && Block.preceq B H)) =
    (GridCO.seatVotes support i).any (fun o => (GridCO.resolvedHead? v o).any
      (fun H => decide (H.slot ≤ (GridCO.headLabel? o).getD 0) && Block.preceq B H)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [GridCO.seatVotes, List.any_eq_true, List.mem_filter]
  constructor
  · rintro ⟨o, ⟨⟨ho, _⟩, hi⟩, h⟩
    exact ⟨o, ⟨ho, hi⟩, h⟩
  · rintro ⟨o, ⟨ho, hi⟩, h⟩
    refine ⟨o, ⟨⟨ho, ?_⟩, hi⟩, h⟩
    cases hr : GridCO.resolvedHead? v o with
    | none => simp [hr] at h
    | some H =>
      simp only [hr, Option.any_some, Bool.and_eq_true] at h
      exact block_preceq_trans hFB h.2

/-- Feeds `proposerSupportNext_scoreOn` and local HEAD comparisons. Raw
participation and equivocation are fixed; only support is projected. -/
theorem port_support_filter_score {n : Nat} (v : GridCO.State n .root)
    (raw support : List (GridCO.Wire n .root)) (F B : Block) (hFB : Block.Preceq F B) :
    GridCO.goldfishScoreOn (GridCO.resolutionTree v) v.blocks raw
      (support.filter (fun o => (GridCO.resolvedHead? v o).any (Block.preceq F))) B =
    GridCO.goldfishScoreOn (GridCO.resolutionTree v) v.blocks raw support B := by
  rw [port_scoreOn_resolved, port_scoreOn_resolved]
  congr 2
  funext i
  rw [port_support_filter_incidence v support F B hFB i]

/-- Feeds `fgsa_scoreRun_support_backward`: all old supporting votes above F
survive the carried-head filter when proposal rows agree and held heads have
an FG tree representative. Frozen support is unchanged. -/
theorem port_headSupport_incidence (p : Params) (st : State p.n) (s : Slot)
    (hP : proposalsAtNext p st s = proposalsAt st s)
    (hT : ∀ H ∈ st.base.blocks, Block.Preceq (eraseFG st.fg.F) H →
      ∃ B ∈ tree p st, eraseFG B = H)
    (B : Block) (hFB : Block.Preceq (eraseFG st.fg.F) B) (o : GridCO.Wire p.n .root)
    (H : Block) (hr : GridCO.resolvedHead? st.base o = some H)
    (hBH : Block.Preceq B H) :
    o ∈ headSupportNext p st s ↔ o ∈ headSupport p st s := by
  have _ := hT
  have _ := hFB
  have _ := hr
  have _ := hBH
  delta headSupportNext headSupport
  rw [hP]
  rfl

/-- Feeds `fgsa_score_eq_on_run`: fixed raw pools give equal HEAD scores above
F, even when the support lists differ. -/
theorem port_headSupport_scoreOn (p : Params) (st : State p.n) (s : Slot)
    (hP : proposalsAtNext p st s = proposalsAt st s)
    (hT : ∀ H ∈ st.base.blocks, Block.Preceq (eraseFG st.fg.F) H →
      ∃ B ∈ tree p st, eraseFG B = H)
    (raw : List (GridCO.Wire p.n .root)) (B : Block)
    (hFB : Block.Preceq (eraseFG st.fg.F) B) :
    GridCO.goldfishScoreOn (GridCO.resolutionTree st.base) st.base.blocks raw
      (headSupportNext p st s) B =
    GridCO.goldfishScoreOn (GridCO.resolutionTree st.base) st.base.blocks raw
      (headSupport p st s) B := by
  rw [port_scoreOn_resolved, port_scoreOn_resolved]
  congr 2
  funext i
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [GridCO.seatVotes, List.any_eq_true, List.mem_filter]
  constructor <;> rintro ⟨o, ⟨ho, hi⟩, hh⟩
  all_goals
    cases hr : GridCO.resolvedHead? st.base o with
    | none => simp [hr] at hh
    | some H =>
      have hh' := hh
      simp only [hr, Option.any_some, Bool.and_eq_true] at hh'
      have hb : Block.Preceq B H := hh'.2
      have he := port_headSupport_incidence p st s hP hT B hFB o H hr hb
      exact ⟨o, ⟨by simpa only [he] using ho, hi⟩, hh⟩

/-- Feeds the local `fgsa_score_eq_on_run` adapter. Proposal retention is
required for raw HEAD equality; candidate geometry alone does not imply it. -/
theorem port_headVotes_score (p : Params) (st : State p.n) (s : Slot)
    (hP : proposalsAtNext p st s = proposalsAt st s)
    (hT : ∀ H ∈ st.base.blocks, Block.Preceq (eraseFG st.fg.F) H →
      ∃ B ∈ tree p st, eraseFG B = H)
    (B : Block) (hFB : Block.Preceq (eraseFG st.fg.F) B) :
    GridCO.goldfishScoreOn (GridCO.resolutionTree st.base) st.base.blocks
      (headVotesNext p st s) (headSupportNext p st s) B =
    GridCO.goldfishScoreOn (GridCO.resolutionTree st.base) st.base.blocks
      (headVotes p st s) (headSupport p st s) B := by
  rw [headVotesNext_eq_of_proposals p st s hP]
  exact port_headSupport_scoreOn p st s hP hT _ B hFB

/-- Feeds `fgsa_cleanSupport_no_equivocation` at the correspondence boundary.
A clean pool used as both raw and support counts exactly its supporting seats. -/
theorem port_clean_score_card {n : Nat} (v : GridCO.State n .root)
    (support : List (GridCO.Wire n .root))
    (hc : ∀ i, GridCO.equivocates support i = false) (B : Block) :
    GridCO.goldfishScoreOn (GridCO.resolutionTree v) v.blocks support support B =
      (Finset.univ.filter (fun i => (GridCO.seatVotes support i).any (fun o =>
        (GridCO.resolvedHead? v o).any (fun H =>
          decide (H.slot ≤ (GridCO.headLabel? o).getD 0) && Block.preceq B H)))).card := by
  rw [port_scoreOn_resolved]
  simp only [hc, Bool.false_or]
  rw [← List.toFinset_card_of_nodup
    (List.Nodup.filter _ (show (GridCO.seats n support).Nodup from List.nodup_dedup _))]
  congr 1
  ext i
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro hi
    refine ⟨?_, hi⟩
    obtain ⟨o, ho, _⟩ := List.any_eq_true.mp hi
    obtain ⟨ho, hs⟩ := List.mem_filter.mp ho
    exact List.mem_dedup.mpr (List.mem_filterMap.mpr ⟨o, ho, by simpa using hs⟩)

/-- Feeds `GridCO.confirmationFrom` and `fastSet`. Clean support is used in
both score arguments, so non-equivocation is required in addition to incidence. -/
theorem port_clean_filter_score {n : Nat} (v : GridCO.State n .root)
    (support : List (GridCO.Wire n .root))
    (hc : ∀ i, GridCO.equivocates support i = false)
    (F B : Block) (hFB : Block.Preceq F B) :
    let kept := support.filter (fun o => (GridCO.resolvedHead? v o).any (Block.preceq F))
    GridCO.goldfishScoreOn (GridCO.resolutionTree v) v.blocks kept kept B =
      GridCO.goldfishScoreOn (GridCO.resolutionTree v) v.blocks support support B := by
  dsimp only
  have hc' (i : Fin n) : GridCO.equivocates
      (support.filter (fun o => (GridCO.resolvedHead? v o).any (Block.preceq F))) i = false :=
    Gen.AC.Root.vote_pool_clean_subset _ _ i (by intro o ho; exact (List.mem_filter.mp ho).1) (hc i)
  rw [port_clean_score_card _ _ hc', port_clean_score_card _ _ hc]
  congr 2
  funext i
  rw [port_support_filter_incidence v support F B hFB i]

/-- Feeds `headInTree`: the child fold uses scores only on its candidates. -/
private theorem port_choose_fold_congr (xs : List Block) (P : Block → Prop)
    (a b : Block → Nat) (ha : ∀ x, P x → a x = b x)
    (hx : ∀ x ∈ xs, P x) (best : Option Block) (hb : ∀ x, best = some x → P x) :
    xs.foldl (fun acc x => match acc with
      | none => some x
      | some y => if a y < a x || (a y == a x && y.root < x.root) then some x else acc)
      best =
    xs.foldl (fun acc x => match acc with
      | none => some x
      | some y => if b y < b x || (b y == b x && y.root < x.root) then some x else acc)
      best := by
  induction xs generalizing best with
  | nil => rfl
  | cons x xs ih =>
    have hp := hx x (by simp)
    have htail : ∀ y ∈ xs, P y := fun y hy => hx y (by simp [hy])
    cases best with
    | none => exact ih htail (some x) (by intro y h; cases h; exact hp)
    | some y =>
      have hy := hb y rfl
      simp only [List.foldl_cons, ha x hp, ha y hy]
      split
      · exact ih htail (some x) (by intro z h; cases h; exact hp)
      · exact ih htail (some y) (by intro z h; cases h; exact hy)

/-- Feeds `headInTree`: the child fold preserves its candidate predicate. -/
private theorem port_choose_fold_property (xs : List Block) (P : Block → Prop)
    (a : Block → Nat) (hx : ∀ x ∈ xs, P x) (best : Option Block)
    (hb : ∀ x, best = some x → P x) :
    ∀ z, xs.foldl (fun acc x => match acc with
      | none => some x
      | some y => if a y < a x || (a y == a x && y.root < x.root) then some x else acc)
      best = some z → P z := by
  induction xs generalizing best with
  | nil => exact hb
  | cons x xs ih =>
    have hp := hx x (by simp)
    have htail : ∀ y ∈ xs, P y := fun y hy => hx y (by simp [hy])
    cases best with
    | none => exact ih htail (some x) (by intro y h; cases h; exact hp)
    | some y =>
      have hy := hb y rfl
      simp only [List.foldl_cons]
      split
      · exact ih htail (some x) (by intro z h; cases h; exact hp)
      · exact ih htail (some y) (by intro z h; cases h; exact hy)

/-- Feeds `headInTree`: each child extends the current walk anchor. -/
private theorem port_child_prefix (a b : Block) (hp : b.parent? = some a) :
    Block.Preceq a b := by
  cases b with
  | genesis => cases hp
  | node q s r v =>
    have hq : q = a := Option.some.inj hp
    subst q
    exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl a))

/-- Feeds `headInTree`: every returned step is a child of its anchor. -/
private theorem port_step_child (T : List Block) (a : Block → Nat)
    (e : Block → Bool) (A C : Block) (hc : GridCO.ghostStep T a e A = some C) :
    C.parent? = some A := by
  let xs := T.filter (fun B => B.parent? == some A && e B)
  let choose := fun (acc : Option Block) (x : Block) => match acc with
    | none => some x
    | some y => if a y < a x || (a y == a x && y.root < x.root) then some x else acc
  have hx : ∀ B ∈ xs, B.parent? = some A := by
    intro B hB
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp (List.mem_filter.mp hB).2).1
  have hfold := port_choose_fold_property xs (fun B => B.parent? = some A)
    a hx none (by simp)
  change (match xs.foldl choose none with
    | none => none
    | some B => if xs.any (fun D => D != B && a D == a B && D.root == B.root)
        then none else some B) = some C at hc
  cases hb : xs.foldl choose none with
  | none => simp [hb] at hc
  | some B =>
    rw [hb] at hc
    change (if xs.any (fun D => D != B && a D == a B && D.root == B.root)
      then none else some B) = some C at hc
    split at hc
    · contradiction
    · have heq : B = C := Option.some.inj hc
      subst C
      exact hfold B hb

/-- Feeds `GridCO.confirmationFrom`: every walk result extends its anchor. -/
private theorem port_ghost_extends (A : Block) (T : List Block)
    (a : Block → Nat) (e : Block → Bool) : Block.Preceq A (GridCO.ghost A T a e) := by
  have walk (fuel : Nat) (A : Block) :
      Block.Preceq A (GridCO.ghostWalk T.eraseDups a e fuel A) := by
    induction fuel generalizing A with
    | zero => exact block_preceq_refl A
    | succ fuel ih =>
      change Block.Preceq A (match GridCO.ghostStep T.eraseDups a e A with
        | none => A
        | some C => GridCO.ghostWalk T.eraseDups a e fuel C)
      cases hc : GridCO.ghostStep T.eraseDups a e A with
      | none => exact block_preceq_refl A
      | some C =>
        exact block_preceq_trans (port_child_prefix A C
          (port_step_child T.eraseDups a e A C hc)) (ih C)
  exact walk T.eraseDups.length A

/-- Feeds `headInTree` and `GridCO.confirmationFrom`: a fixed local GHOST step
uses scores and eligibility only above its anchor. Ambiguous ties are preserved. -/
theorem port_ghostStep_congr (T : List Block) (F A : Block) (hFA : Block.Preceq F A)
    (a b : Block → Nat) (e f : Block → Bool)
    (hs : ∀ B, Block.Preceq F B → a B = b B)
    (he : ∀ B, Block.Preceq F B → e B = f B) :
    GridCO.ghostStep T a e A = GridCO.ghostStep T b f A := by
  have hc : T.filter (fun B => B.parent? == some A && e B) =
      T.filter (fun B => B.parent? == some A && f B) := by
    apply List.filter_congr
    intro B _
    by_cases hp : B.parent? = some A
    · rw [he B (block_preceq_trans hFA (port_child_prefix A B hp))]
    · have hn : (B.parent? == some A) = false := beq_eq_false_iff_ne.mpr hp
      rw [hn, Bool.false_and, Bool.false_and]
  let children := T.filter (fun B => B.parent? == some A && f B)
  have hchildren : ∀ B ∈ children, Block.Preceq F B := by
    intro B hB
    have hp := (Bool.and_eq_true_iff.mp (List.mem_filter.mp hB).2).1
    exact block_preceq_trans hFA (port_child_prefix A B (by simpa using hp))
  let sourceChildren := T.filter (fun B => B.parent? == some A && e B)
  change (match sourceChildren.foldl (fun acc x => match acc with
    | none => some x
    | some y => if a y < a x || (a y == a x && y.root < x.root) then some x else acc)
    none with
    | none => none
    | some B => if sourceChildren.any (fun C => C != B && a C == a B && C.root == B.root)
        then none else some B) =
    (match children.foldl (fun acc x => match acc with
    | none => some x
    | some y => if b y < b x || (b y == b x && y.root < x.root) then some x else acc)
    none with
    | none => none
    | some B => if children.any (fun C => C != B && b C == b B && C.root == B.root)
        then none else some B)
  have hsc : sourceChildren = children := hc
  rw [hsc]
  rw [port_choose_fold_congr children (Block.Preceq F) a b hs hchildren none (by simp)]
  cases hb : children.foldl (fun acc x => match acc with
      | none => some x
      | some y => if b y < b x || (b y == b x && y.root < x.root) then some x else acc)
      none with
  | none => rfl
  | some B =>
    have hFB := port_choose_fold_property children (Block.Preceq F) b hchildren
      none (by simp) B hb
    have ht : children.any (fun C => C != B && a C == a B && C.root == B.root) =
        children.any (fun C => C != B && b C == b B && C.root == B.root) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor <;> rintro ⟨C, hC, hh⟩ <;> refine ⟨C, hC, ?_⟩
      · simpa only [hs C (hchildren C hC), hs B hFB] using hh
      · simpa only [hs C (hchildren C hC), hs B hFB] using hh
    dsimp only
    rw [ht]

/-- Feeds the selected-head correspondence for a fixed frame and raw pool.
Score equality is required only above F, including the starting anchor. -/
theorem port_ghost_congr (T : List Block) (F A : Block) (hFA : Block.Preceq F A)
    (a b : Block → Nat) (e f : Block → Bool)
    (hs : ∀ B, Block.Preceq F B → a B = b B)
    (he : ∀ B, Block.Preceq F B → e B = f B) :
    GridCO.ghost A T a e = GridCO.ghost A T b f := by
  have walk (fuel : Nat) (A : Block) (hFA : Block.Preceq F A) :
      GridCO.ghostWalk T.eraseDups a e fuel A =
        GridCO.ghostWalk T.eraseDups b f fuel A := by
    induction fuel generalizing A with
    | zero => rfl
    | succ fuel ih =>
      change (match GridCO.ghostStep T.eraseDups a e A with
        | none => A
        | some C => GridCO.ghostWalk T.eraseDups a e fuel C) =
        (match GridCO.ghostStep T.eraseDups b f A with
        | none => A
        | some C => GridCO.ghostWalk T.eraseDups b f fuel C)
      rw [port_ghostStep_congr _ F A hFA a b e f hs he]
      cases hc : GridCO.ghostStep T.eraseDups b f A with
      | none => rfl
      | some C =>
        apply ih C
        have hp := port_step_child T.eraseDups b f A C hc
        exact block_preceq_trans hFA (port_child_prefix A C hp)
  exact walk T.eraseDups.length A hFA

/-- Feeds `GridCO.confirmationFrom` at the F-anchored gate. The late raw pool,
local tree, domain, and timestamps stay fixed. Clean-support non-equivocation
is explicit because confirmation uses support as both score arguments. -/
theorem port_confirmation_filter (p : Params) (v : GridCO.State p.n .root)
    (F : Block) (s : Slot)
    (hc : ∀ i, GridCO.equivocates (GridCO.cleanSupport p.toParams.engine v s) i = false) :
    let kept := (GridCO.cleanSupport p.toParams.engine v s).filter
      (fun o => (GridCO.resolvedHead? v o).any (Block.preceq F))
    let score := GridCO.goldfishScoreOn (GridCO.resolutionTree v) v.blocks kept kept
    let eligible := fun B => decide
      (GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) < 2 * score B)
    let H := GridCO.ghost F v.blocks score eligible
    (if eligible H then some H else none) = GridCO.confirmationFrom p.toParams.engine F v s := by
  dsimp only
  let old := GridCO.cleanSupport p.toParams.engine v s
  let kept := old.filter (fun o => (GridCO.resolvedHead? v o).any (Block.preceq F))
  let a := GridCO.goldfishScoreOn (GridCO.resolutionTree v) v.blocks kept kept
  let b := GridCO.goldfishScoreOn (GridCO.resolutionTree v) v.blocks old old
  let count := GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s)
  have hs (B : Block) (hFB : Block.Preceq F B) : a B = b B :=
    port_clean_filter_score v old hc F B hFB
  have he (B : Block) (hFB : Block.Preceq F B) :
      decide (count < 2 * a B) = decide (count < 2 * b B) := by rw [hs B hFB]
  have hw := port_ghost_congr v.blocks F F (block_preceq_refl F) a b
    (fun B => decide (count < 2 * a B)) (fun B => decide (count < 2 * b B)) hs he
  let ea := fun B => decide (count < 2 * a B)
  let eb := fun B => decide (count < 2 * b B)
  unfold GridCO.confirmationFrom
  simp only [decide_eq_true_eq]
  change (if count < 2 * a (GridCO.ghost F v.blocks a ea) then
    some (GridCO.ghost F v.blocks a ea) else none) =
    (if count < 2 * b (GridCO.ghost F v.blocks b eb) then
      some (GridCO.ghost F v.blocks b eb) else none)
  rw [hw, hs _ (port_ghost_extends F v.blocks b eb)]

/-- Feeds `getHead`/`headVote` local correspondence. Controls, the local frame,
and the raw pool are fixed; support may differ outside the suffix above F. -/
theorem port_selected_head_eq (p : Params) (st : State p.n) (T : List Block)
    (raw left right : List (GridCO.Wire p.n .root))
    (hc : controls p st = FGSA.controls p st)
    (hF : Block.Preceq (eraseFG st.fg.F) (liveRoot p st))
    (hs : ∀ B, Block.Preceq (eraseFG st.fg.F) B →
      GridCO.goldfishScore st.base.blocks raw left B =
        GridCO.goldfishScore st.base.blocks raw right B) :
    headInTreeNext p st T raw left = headInTree p st T raw right := by
  rw [headInTreeNext_eq_of_controls p st hc]
  unfold headInTree
  apply port_ghost_congr T (eraseFG st.fg.F) _ hF _ _ _ _ hs
  intro B hFB
  unfold eligible
  rw [hs B hFB]

/-- Feeds `proposeNext`: the canonical and Next proposer supports select the
same parent in a fixed local frame. Equality of the support lists is not needed. -/
theorem port_proposer_selected_head (p : Params) (st : State p.n) (s : Slot)
    (T : List Block) (hc : controls p st = FGSA.controls p st)
    (hF : Block.Preceq (eraseFG st.fg.F) (liveRoot p st))
    (hd : st.base.headDomain = none) (raw : List (GridCO.Wire p.n .root)) :
    headInTreeNext p st T raw (proposerSupportNext st s) =
      headInTree p st T raw (proposerSupport st s) := by
  apply port_selected_head_eq p st T raw _ _ hc hF
  intro B hFB
  exact proposerSupportNext_score st s B hFB hd raw

/-- Feeds `headVoteNext`: a fixed frame and retained proposal rows give equal
selected heads even when the old and new carried support lists differ. -/
theorem port_voter_selected_head (p : Params) (st : State p.n) (s : Slot)
    (T : List Block) (hc : controls p st = FGSA.controls p st)
    (hF : Block.Preceq (eraseFG st.fg.F) (liveRoot p st))
    (hd : st.base.headDomain = none)
    (hP : proposalsAtNext p st s = proposalsAt st s)
    (hT : ∀ H ∈ st.base.blocks, Block.Preceq (eraseFG st.fg.F) H →
      ∃ B ∈ tree p st, eraseFG B = H) :
    headInTreeNext p st T (headVotesNext p st s) (headSupportNext p st s) =
      headInTree p st T (headVotes p st s) (headSupport p st s) := by
  rw [headVotesNext_eq_of_proposals p st s hP]
  apply port_selected_head_eq p st T _ _ _ hc hF
  intro B hFB
  change GridCO.goldfishScoreOn st.base.blocks st.base.blocks _ _ B =
    GridCO.goldfishScoreOn st.base.blocks st.base.blocks _ _ B
  simpa only [GridCO.resolutionTree, hd, Option.getD_none] using
    port_headSupport_scoreOn p st s hP hT (headVotes p st s) B hFB

/-- Feeds `GridCO.releaseCount`: count the set of non-equivocating opposing seats. -/
private theorem port_release_count_card {n : Nat} (q : GridCO.Params)
    (v : GridCO.State n .root) (s : Slot) (B : Block) :
    GridCO.releaseCount q v s B = (Finset.univ.filter (fun i =>
      GridCO.equivocates (GridCO.votesAt v s) i = false ∧
      ∃ o ∈ GridCO.votesAt v s, GridCO.resolvedBefore v o (GridCO.releaseTime q s) = true ∧
        GridCO.headSeat? o = some i ∧
        (GridCO.resolvedHead? v o).any (fun H => !Block.compatible H B) = true)).card := by
  have hp : (fun o : GridCO.Wire n .root => match GridCO.resolvedHead? v o with
      | some H => !Block.compatible H B
      | none => false) = (fun o => (GridCO.resolvedHead? v o).any
        (fun H => !Block.compatible H B)) := by
    funext o
    cases GridCO.resolvedHead? v o <;> rfl
  unfold GridCO.releaseCount
  dsimp only
  change ((GridCO.seats n ((GridCO.votesAt v s).filter (fun o =>
      GridCO.resolvedBefore v o (GridCO.releaseTime q s)))).filter (fun i =>
    !GridCO.equivocates (GridCO.votesAt v s) i &&
    (GridCO.seatVotes ((GridCO.votesAt v s).filter (fun o =>
      GridCO.resolvedBefore v o (GridCO.releaseTime q s))) i).any (fun o =>
      match GridCO.resolvedHead? v o with
      | some H => !Block.compatible H B
      | none => false))).length = _
  rw [hp, ← List.toFinset_card_of_nodup
    (List.Nodup.filter _ (show (GridCO.seats n ((GridCO.votesAt v s).filter
      (fun o => GridCO.resolvedBefore v o (GridCO.releaseTime q s)))).Nodup from
        List.nodup_dedup _))]
  congr 1
  ext i
  simp only [List.mem_toFinset, List.mem_filter, Bool.and_eq_true,
    Bool.not_eq_true', List.any_eq_true, GridCO.seatVotes, beq_iff_eq,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, he, o, ⟨⟨ho, hr⟩, hi⟩, hh⟩
    exact ⟨he, o, ho, hr, hi, hh⟩
  · rintro ⟨he, o, ho, hr, hi, hh⟩
    refine ⟨?_, he, o, ⟨⟨ho, hr⟩, hi⟩, hh⟩
    exact List.mem_dedup.mpr (List.mem_filterMap.mpr
      ⟨o, List.mem_filter.mpr ⟨ho, hr⟩, hi⟩)

/-- Feeds `GridCO.releaseCount`: an opposing active head must extend F. -/
private theorem port_opponent_above (F B H : Block)
    (hFB : Block.Compatible F B) (hHF : Block.Compatible H F)
    (hHB : Block.compatible H B = false) : Block.Preceq F H := by
  rcases Bool.or_eq_true_iff.mp hHF with hHF | hFH
  · have hHB' : Block.Compatible H B := by
      rcases Bool.or_eq_true_iff.mp hFB with hFB | hBF
      · exact Bool.or_eq_true_iff.mpr (Or.inl (block_preceq_trans hHF hFB))
      · exact block_compatible_of_common hHF hBF
    change Block.compatible H B = true at hHB'
    rw [hHB] at hHB'
    contradiction
  · exact hFH

/-- Feeds `active_releaseCount_le`, `Release`, and the revocation adapter.
Equality holds only for targets compatible with F. The resolved lists and
release snapshots can differ. The caller supplies local reader laws only. -/
theorem port_releaseCount_eq {n : Nat} (q : GridCO.Params)
    (v w : GridCO.State n .root) (s : Slot) (F B : Block)
    (hFB : Block.Compatible F B)
    (hraw : GridCO.votesAt w s = GridCO.votesAt v s)
    (hres : ∀ o, GridCO.resolvedHead? w o =
      (GridCO.resolvedHead? v o).filter (Block.preceq F))
    (hbefore : ∀ o, GridCO.resolvedBefore w o (GridCO.releaseTime q s) =
      (GridCO.resolvedBefore v o (GridCO.releaseTime q s) &&
        (GridCO.resolvedHead? v o).any (Block.preceq F)))
    (hactive : ∀ o ∈ GridCO.votesAt v s, ∀ H,
      GridCO.resolvedHead? v o = some H → Block.Compatible H F) :
    GridCO.releaseCount q w s B = GridCO.releaseCount q v s B := by
  rw [port_release_count_card, port_release_count_card, hraw]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨he, o, ho, ht, hi, hh⟩
    rw [hbefore] at ht
    refine ⟨he, o, ho, (Bool.and_eq_true_iff.mp ht).1, hi, ?_⟩
    rw [hres] at hh
    cases hr : GridCO.resolvedHead? v o with
    | none => simp [hr] at hh
    | some H =>
      cases hf : Block.preceq F H <;> simp [hr, hf, Option.filter] at hh
      simpa [hr] using hh
  · rintro ⟨he, o, ho, ht, hi, hh⟩
    cases hr : GridCO.resolvedHead? v o with
    | none => simp [hr] at hh
    | some H =>
      have hn : Block.compatible H B = false := by simpa [hr] using hh
      have hf := port_opponent_above F B H hFB (hactive o ho H hr) hn
      change Block.preceq F H = true at hf
      refine ⟨he, o, ho, ?_, hi, ?_⟩
      · rw [hbefore]
        simp [ht, hr, hf]
      · rw [hres]
        simp [hr, Option.filter, hf, hn]

/-- Support incidence and selected heads agree with Legacy under the old local facts. -/
theorem port_headSupport_incidence_legacy (p : Params) (st : State p.n) (s : Slot)
    (hP : proposalsAtNext p st s = Legacy.proposalsAt st s)
    (hT : ∀ H ∈ st.base.blocks, Block.Preceq (eraseFG st.fg.F) H →
      ∃ B ∈ tree p st, eraseFG B = H)
    (B : Block) (hFB : Block.Preceq (eraseFG st.fg.F) B) (o : GridCO.Wire p.n .root)
    (H : Block) (hr : GridCO.resolvedHead? st.base o = some H)
    (hBH : Block.Preceq B H) :
    o ∈ headSupportNext p st s ↔ o ∈ Legacy.headSupport p st s := by
  have hm := hT H (resolvedHead_mem st.base o hr) (block_preceq_trans hFB hBH)
  let frozen := (GridCO.votesAt st.base (s - 1)).filter (fun o =>
    GridCO.resolvedBefore (actView st) o (SA.freezeTime p.toParams (s - 1)))
  change o ∈ (frozen ++ ((proposalsAtNext p st s).flatMap
      (fun row => row.2.map baseVote)).filter (fun o =>
        GridCO.headLabel? o == some (s - 1) &&
          match GridCO.resolvedHead? st.base o with
          | some H => decide (∃ B ∈ tree p st, eraseFG B = H) &&
              decide (H.slot ≤ s - 1)
          | none => false)).eraseDups ↔
    o ∈ (frozen ++ ((Legacy.proposalsAt st s).flatMap (fun row => row.2.map baseVote)).filter
      (fun o => GridCO.headLabel? o == some (s - 1) &&
        match GridCO.resolvedHead? st.base o with
        | some H => decide (H.slot ≤ s - 1)
        | none => false)).eraseDups
  rw [List.mem_eraseDups, List.mem_eraseDups, List.mem_append, List.mem_append]
  apply or_congr Iff.rfl
  rw [List.mem_filter, List.mem_filter, hP, hr]
  change (_ ∧ (GridCO.headLabel? o == some (s - 1) &&
    (decide (∃ B ∈ tree p st, eraseFG B = H) && decide (H.slot ≤ s - 1))) = true) ↔
    (_ ∧ (GridCO.headLabel? o == some (s - 1) && decide (H.slot ≤ s - 1)) = true)
  simp only [hm, decide_true, Bool.true_and]

theorem port_headSupport_scoreOn_legacy (p : Params) (st : State p.n) (s : Slot)
    (hP : proposalsAtNext p st s = Legacy.proposalsAt st s)
    (hT : ∀ H ∈ st.base.blocks, Block.Preceq (eraseFG st.fg.F) H →
      ∃ B ∈ tree p st, eraseFG B = H)
    (raw : List (GridCO.Wire p.n .root)) (B : Block)
    (hFB : Block.Preceq (eraseFG st.fg.F) B) :
    GridCO.goldfishScoreOn (GridCO.resolutionTree st.base) st.base.blocks raw
      (headSupportNext p st s) B =
    GridCO.goldfishScoreOn (GridCO.resolutionTree st.base) st.base.blocks raw
      (Legacy.headSupport p st s) B := by
  rw [port_scoreOn_resolved, port_scoreOn_resolved]
  congr 2
  funext i
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [GridCO.seatVotes, List.any_eq_true, List.mem_filter]
  constructor <;> rintro ⟨o, ⟨ho, hi⟩, hh⟩
  all_goals
    cases hr : GridCO.resolvedHead? st.base o with
    | none => simp [hr] at hh
    | some H =>
      have hh' := hh
      simp only [hr, Option.any_some, Bool.and_eq_true] at hh'
      have hb : Block.Preceq B H := hh'.2
      have he := port_headSupport_incidence_legacy p st s hP hT B hFB o H hr hb
      exact ⟨o, ⟨by simpa only [he] using ho, hi⟩, hh⟩

theorem port_headVotes_score_legacy (p : Params) (st : State p.n) (s : Slot)
    (hP : proposalsAtNext p st s = Legacy.proposalsAt st s)
    (hT : ∀ H ∈ st.base.blocks, Block.Preceq (eraseFG st.fg.F) H →
      ∃ B ∈ tree p st, eraseFG B = H)
    (B : Block) (hFB : Block.Preceq (eraseFG st.fg.F) B) :
    GridCO.goldfishScoreOn (GridCO.resolutionTree st.base) st.base.blocks
      (headVotesNext p st s) (headSupportNext p st s) B =
    GridCO.goldfishScoreOn (GridCO.resolutionTree st.base) st.base.blocks
      (Legacy.headVotes p st s) (Legacy.headSupport p st s) B := by
  rw [port_headVotes_eq_legacy_of_proposals p st s hP]
  exact port_headSupport_scoreOn_legacy p st s hP hT _ B hFB

theorem port_selected_head_eq_legacy (p : Params) (st : State p.n) (T : List Block)
    (raw left right : List (GridCO.Wire p.n .root))
    (hc : controls p st = Legacy.controls p st)
    (hF : Block.Preceq (eraseFG st.fg.F) (Legacy.liveRoot p st))
    (hs : ∀ B, Block.Preceq (eraseFG st.fg.F) B →
      GridCO.goldfishScore st.base.blocks raw left B =
        GridCO.goldfishScore st.base.blocks raw right B) :
    headInTreeNext p st T raw left = Legacy.headInTree p st T raw right := by
  rw [port_headInTree_eq_legacy_of_controls p st hc]
  unfold Legacy.headInTree
  apply port_ghost_congr T (eraseFG st.fg.F) _ hF _ _ _ _ hs
  intro B hFB
  unfold Legacy.eligible
  rw [hs B hFB]

theorem port_proposer_selected_head_legacy (p : Params) (st : State p.n) (s : Slot)
    (T : List Block) (hc : controls p st = Legacy.controls p st)
    (hF : Block.Preceq (eraseFG st.fg.F) (Legacy.liveRoot p st))
    (hd : st.base.headDomain = none) (raw : List (GridCO.Wire p.n .root)) :
    headInTreeNext p st T raw (proposerSupportNext st s) =
      Legacy.headInTree p st T raw (Legacy.proposerSupport st s) := by
  apply port_selected_head_eq_legacy p st T raw _ _ hc hF
  intro B hFB
  exact port_proposerSupport_score_legacy st s B hFB hd raw

theorem port_voter_selected_head_legacy (p : Params) (st : State p.n) (s : Slot)
    (T : List Block) (hc : controls p st = Legacy.controls p st)
    (hF : Block.Preceq (eraseFG st.fg.F) (Legacy.liveRoot p st))
    (hd : st.base.headDomain = none)
    (hP : proposalsAtNext p st s = Legacy.proposalsAt st s)
    (hT : ∀ H ∈ st.base.blocks, Block.Preceq (eraseFG st.fg.F) H →
      ∃ B ∈ tree p st, eraseFG B = H) :
    headInTreeNext p st T (headVotesNext p st s) (headSupportNext p st s) =
      Legacy.headInTree p st T (Legacy.headVotes p st s) (Legacy.headSupport p st s) := by
  rw [port_headVotes_eq_legacy_of_proposals p st s hP]
  apply port_selected_head_eq_legacy p st T _ _ _ hc hF
  intro B hFB
  change GridCO.goldfishScoreOn st.base.blocks st.base.blocks _ _ B =
    GridCO.goldfishScoreOn st.base.blocks st.base.blocks _ _ B
  simpa only [GridCO.resolutionTree, hd, Option.getD_none] using
    port_headSupport_scoreOn_legacy p st s hP hT (Legacy.headVotes p st s) B hFB

end AvailableChain.FGSA.Next
end
