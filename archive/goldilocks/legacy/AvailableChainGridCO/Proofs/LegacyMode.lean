module
public import AvailableChainGridCO.Model.Legacy

-- Find matcher bodies in the two definitions; do not depend on generated names.
local elab "hygieneEq% " lhs:term:max rhs:term:max : term => do
  let left ← Lean.Elab.Term.elabTerm lhs none
  let right ← Lean.Elab.Term.elabTerm rhs none
  let a ← Lean.getConstInfo left.getAppFn.constName!
  let b ← Lean.getConstInfo right.getAppFn.constName!
  for x in a.value!.getUsedConstants do
    unless (← Lean.Meta.getMatcherInfo? x).isSome do continue
    let ex ← Lean.Meta.mkConstWithFreshMVarLevels x
    for y in b.value!.getUsedConstants do
      unless (← Lean.Meta.getMatcherInfo? y).isSome do continue
      let ey ← Lean.Meta.mkConstWithFreshMVarLevels y
      if ← Lean.Meta.isDefEq (← Lean.Meta.inferType ex) (← Lean.Meta.inferType ey) then
        if ← Lean.Meta.isDefEq ex ey then
          return ← Lean.Meta.mkEq ex ey
  throwError "No equal matcher bodies in the supplied definitions"

namespace AvailableChain.GridCO.Legacy

open AvailableChain.Generic

-- ROOT-DIGEST-2 option 3: use a private copy of the same matcher (BUILD B3).
private def hygiene_goldfishScore {n : Nat} (tree : List Block)
    (raw support : List (Wire n)) (b : Block) : Nat :=
  ((seats n raw).filter (fun i =>
    equivocates raw i || (seatVotes support i).any (fun o =>
      match headTarget? o with
      | some target => target ∈ tree && target.slot ≤ (headLabel? o).getD 0 &&
          Block.preceq b target
      | none => false))).length

-- The generated matcher bodies are definitionally equal.
private theorem hygiene_goldfishScore_match_1_eq :
    hygieneEq% (@goldfishScore) (@hygiene_goldfishScore) := rfl

end AvailableChain.GridCO.Legacy

namespace AvailableChain.GridCO.Legacy

open AvailableChain.Generic

-- ROOT-DIGEST-2 option 3: use a private copy of the same matcher (BUILD B3).
private def hygiene_voterView (_p : Params) {n : Nat} (st : State n) (s : Slot) : List (Wire n) :=
  let pool := match frozenAt st (s - 1) with
    | some (raw, _, _) => raw
    | none => []
  (pool ++ carriedRaw st s).eraseDups

-- The generated matcher bodies are definitionally equal.
private theorem hygiene_voterView_match_1_eq :
    hygieneEq% (@voterView) (@hygiene_voterView) := rfl

end AvailableChain.GridCO.Legacy

namespace AvailableChain.GridCO

open AvailableChain.Generic

-- ROOT-DIGEST-2 option 3: use a private copy of the same matcher (BUILD B3).
private def hygiene_goldfishScoreOn {n : Nat} {mode : HeadMode} (domain tree : List Block)
    (raw support : List (Wire n mode)) (b : Block) : Nat :=
  ((seats n raw).filter (fun i =>
    equivocates raw i || (seatVotes support i).any (fun o =>
      match headTarget? o with
      | none => false
      | some target => match resolveTarget mode domain target with
        | none => false
        | some B => decide (B ∈ tree) && decide (B.slot ≤ (headLabel? o).getD 0) &&
            Block.preceq b B))).length

-- The generated matcher bodies are definitionally equal.
private theorem hygiene_goldfishScoreOn_match_1_eq :
    hygieneEq% (@goldfishScoreOn) (@hygiene_goldfishScoreOn) := rfl

end AvailableChain.GridCO

namespace AvailableChain.GridCO

open AvailableChain.Generic

-- ROOT-DIGEST-2 option 3: use a private copy of the same matcher (BUILD B3).
private def hygiene_proposerSupportView
    {n : Nat} {mode : HeadMode} (st : State n mode) (s : Slot) : List
    (Wire n mode) :=
  (proposerView st s).filter (fun o =>
    match resolvedHead? st o with
    | some b => b.slot ≤ s - 1
    | none => false)

-- The generated matcher bodies are definitionally equal.
private theorem hygiene_proposerSupportView_match_1_eq :
    hygieneEq% (@proposerSupportView) (@Legacy.hygiene_goldfishScore) := rfl

end AvailableChain.GridCO

namespace AvailableChain.GridCO

open AvailableChain.Generic

-- ROOT-DIGEST-2 option 3: use a private copy of the same matcher (BUILD B3).
private def hygiene_resolvedBefore {n : Nat} {mode : HeadMode}
    (st : State n mode) (o : Wire n mode) (cutoff : Time) : Bool :=
  match resolvedHead? st o with
  | none => false
  | some B => decide (B.slot ≤ (headLabel? o).getD 0) &&
      decide (stampVote st o < cutoff) && decide (stampBlock st B < cutoff)

-- The generated matcher bodies are definitionally equal.
private theorem hygiene_resolvedBefore_match_1_eq :
    hygieneEq% (@resolvedBefore) (@hygiene_goldfishScoreOn) := rfl

end AvailableChain.GridCO

namespace AvailableChain.GridCO

open AvailableChain.Generic

-- ROOT-DIGEST-2 option 3: use a private copy of the same matcher (BUILD B3).
private def hygiene_voterView
    (_p : Params) {n : Nat} {mode : HeadMode} (st : State n mode) (s : Slot) : List
    (Wire n mode) :=
  let pool := match frozenAt st (s - 1) with
    | some (raw, _, _) => raw
    | none => []
  (pool ++ carriedRaw st s).eraseDups

-- The generated matcher bodies are definitionally equal.
private theorem hygiene_voterView_match_1_eq :
    hygieneEq% (@voterView) (@hygiene_voterView) := rfl

end AvailableChain.GridCO

-- Rewrite before simp can generate equations for the public matcher.
attribute [local simp↓]
  AvailableChain.GridCO.Legacy.hygiene_goldfishScore_match_1_eq
  AvailableChain.GridCO.Legacy.hygiene_voterView_match_1_eq
  AvailableChain.GridCO.hygiene_goldfishScoreOn_match_1_eq
  AvailableChain.GridCO.hygiene_proposerSupportView_match_1_eq
  AvailableChain.GridCO.hygiene_resolvedBefore_match_1_eq
  AvailableChain.GridCO.hygiene_voterView_match_1_eq

local macro "hygiene_split" : tactic =>
  `(tactic| (
    try rw [AvailableChain.GridCO.Legacy.hygiene_goldfishScore_match_1_eq] at *;
    try rw [AvailableChain.GridCO.Legacy.hygiene_voterView_match_1_eq] at *;
    try rw [AvailableChain.GridCO.hygiene_goldfishScoreOn_match_1_eq] at *;
    try rw [AvailableChain.GridCO.hygiene_proposerSupportView_match_1_eq] at *;
    try rw [AvailableChain.GridCO.hygiene_resolvedBefore_match_1_eq] at *;
    try rw [AvailableChain.GridCO.hygiene_voterView_match_1_eq] at *;
    all_goals split))

local macro "hygiene_split" "at" h:ident : tactic =>
  `(tactic| (
    try rw [AvailableChain.GridCO.Legacy.hygiene_goldfishScore_match_1_eq] at *;
    try rw [AvailableChain.GridCO.Legacy.hygiene_voterView_match_1_eq] at *;
    try rw [AvailableChain.GridCO.hygiene_goldfishScoreOn_match_1_eq] at *;
    try rw [AvailableChain.GridCO.hygiene_proposerSupportView_match_1_eq] at *;
    try rw [AvailableChain.GridCO.hygiene_resolvedBefore_match_1_eq] at *;
    try rw [AvailableChain.GridCO.hygiene_voterView_match_1_eq] at *;
    all_goals split at $h:ident))

public section

namespace AvailableChain.GridCO.Legacy

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Preserve the old headLabel? reader. -/
@[simp] theorem headLabel_block {n : Nat} (o : Wire n) :
    GridCO.headLabel? o = headLabel? o := by
  rcases o with ⟨a, m⟩
  cases a <;> cases m <;> rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Preserve the old headSeat? reader. -/
@[simp] theorem headSeat_block {n : Nat} (o : Wire n) :
    GridCO.headSeat? o = headSeat? o := by
  rcases o with ⟨a, m⟩
  cases a <;> cases m <;> rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Preserve the old headTarget? reader. -/
@[simp] theorem headTarget_block {n : Nat} (o : Wire n) :
    GridCO.headTarget? o = headTarget? o := by
  rcases o with ⟨a, m⟩
  cases a <;> cases m <;> rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Preserve the old toHead? reader. -/
@[simp] theorem toHead_block {n : Nat} (o : Wire n) :
    GridCO.toHead? o = toHead? o := by
  rcases o with ⟨a, m⟩
  cases a <;> cases m <;> rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Preserve the old same-seat reader. -/
@[simp] theorem sameSeat_block {n : Nat} (o u : Wire n) :
    GridCO.sameSeat o u = sameSeat o u := by
  rcases o with ⟨a, m⟩
  rcases u with ⟨b, k⟩
  cases a <;> cases b <;> rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Preserve old participant seats. -/
@[simp] theorem seats_block {n : Nat} (xs : List (Wire n)) :
    GridCO.seats n xs = seats n xs := by simp (config := { instances := true }) [GridCO.seats,
      seats]

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Preserve old per-seat pools. -/
@[simp] theorem seatVotes_block {n : Nat} (xs : List (Wire n)) (i : Fin n) :
    GridCO.seatVotes xs i = seatVotes xs i := by simp (config := { instances := true })
      [GridCO.seatVotes, seatVotes]

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Preserve old equivocation. -/
@[simp] theorem equivocates_block {n : Nat} (xs : List (Wire n)) (i : Fin n) :
    GridCO.equivocates xs i = equivocates xs i := by
  simp (config := { instances := true }) [GridCO.equivocates, equivocates]

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Preserve old label pools. -/
@[simp] theorem votesAt_embed {n : Nat} (st : State n) (s : Slot) :
    GridCO.votesAt (embed st) s = votesAt st s := by simp (config := { instances := true })
      [GridCO.votesAt, votesAt, embed]


/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Keep vote receipt stamps. -/
@[simp] theorem stampVote_embed {n : Nat} (st : State n) (o : Wire n) :
    GridCO.stampVote (embed st) o = stampVote st o := rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Keep block receipt stamps. -/
@[simp] theorem stampBlock_embed {n : Nat} (st : State n) (B : Block) :
    GridCO.stampBlock (embed st) B = stampBlock st B := rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Keep late vote pools. -/
@[simp] theorem lateVotes_embed {n : Nat} (p : Params) (st : State n) (s : Slot) :
    GridCO.lateVotes p (embed st) s = lateVotes p st s := by
  unfold GridCO.lateVotes lateVotes
  rw [votesAt_embed]
  apply List.filter_congr
  intro o _
  exact congrArg (fun (t : Time) => decide (t < gateTime p s)) (stampVote_embed st o)

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Legacy resolution uses structural membership. -/
theorem resolvedBefore_embed {n : Nat} (st : State n) (o : Wire n) (t : Time) :
    GridCO.resolvedBefore (embed st) o t = resolvedBefore st o t := by
  unfold GridCO.resolvedBefore resolvedBefore
  rcases o with ⟨a, m⟩
  cases m with
  | proposal B raw sup => rfl
  | head B =>
      have htarget : GridCO.resolvedHead? (embed st) ⟨a, .head B⟩ =
          if B ∈ st.blocks then some B else none := by
        by_cases hm : B ∈ st.blocks <;>
          simp [GridCO.resolvedHead?, GridCO.headTarget?, GridCO.resolveTarget,
            GridCO.resolutionTree, embed, hm]
      rw [htarget]
      change (match (if B ∈ st.blocks then some B else none) with
        | none => false
        | some C => decide (C.slot ≤ (GridCO.headLabel? ⟨a, .head B⟩).getD 0) &&
          decide (GridCO.stampVote (embed st) ⟨a, .head B⟩ < t) &&
          decide (GridCO.stampBlock (embed st) C < t)) = _
      by_cases hm : B ∈ st.blocks
      · rw [ite_eq_left hm]
        dsimp only
        rw [stampVote_embed, stampBlock_embed, headLabel_block]
        simp [headTarget?, blockKnown, hm]
      · rw [ite_eq_right hm]
        simp [headTarget?, blockKnown, hm]

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Legacy score keeps arbitrary Block targets. -/
theorem goldfishScore_block {n : Nat} (tree : List Block)
    (raw support : List (Wire n)) (B : Block) :
    GridCO.goldfishScore tree raw support B = goldfishScore tree raw support B := by
  unfold GridCO.goldfishScore GridCO.goldfishScoreOn goldfishScore
  simp (config := { instances := true }) only [
      ↓AvailableChain.GridCO.Legacy.hygiene_goldfishScore_match_1_eq,
      ↓AvailableChain.GridCO.hygiene_goldfishScoreOn_match_1_eq,
      ↓AvailableChain.GridCO.hygiene_resolvedBefore_match_1_eq,
      seats_block, seatVotes_block, equivocates_block]
  congr 1
  apply List.filter_congr
  intro i _
  apply congrArg (fun b => equivocates raw i || b)
  apply List.any_congr rfl
  intro o
  rcases o with ⟨a, m⟩
  cases m with
  | proposal C rs ss => rfl
  | head C =>
      by_cases h : C ∈ tree <;>
        simp (config := { instances := true }) [GridCO.headTarget?, headTarget?,
          GridCO.resolveTarget, h,
          headLabel_block]

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] The old raw and late cuts are unchanged. -/
theorem cleanSupport_embed {n : Nat} (p : Params) (st : State n) (s : Slot) :
    GridCO.cleanSupport p (embed st) s = cleanSupport p st s := by
  simp (config := { instances := true }) only [GridCO.cleanSupport, cleanSupport,
    GridCO.earlyVotes, earlyVotes,
    resolvedBefore_embed, votesAt_embed]
  simp (config := { instances := true }) only [lateVotes_embed, sameSeat_block]

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] HEAD admission keeps the complete old state. -/
theorem admitVote_embed {n : Nat} (p : Params) (st : State n) (o : Wire n) :
    GridCO.admitVote p (embed st) o = embed (admitVote p st o) := by
  rcases o with ⟨a, m⟩
  cases a <;> cases m <;>
    simp (config := { instances := true }) only [GridCO.admitVote, admitVote, votesAt_embed,
      equivocates_block]
  all_goals dsimp (config := { instances := true }) only [embed]
  all_goals split_ifs <;> rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Exclusion keeps the old arbitrary-input formula. -/
theorem excludes_embed {n : Nat} (p : Params) (st : State n) (o : Wire n) :
    GridCO.excludes p (embed st) o = excludes p st o := by
  rcases o with ⟨a, m⟩
  cases a <;> cases m <;>
    simp (config := { instances := true }) only [GridCO.excludes, excludes, votesAt_embed,
      equivocates_block]
  rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] The old componentwise state survives vote folds. -/
theorem votes_fold_embed {n : Nat} (p : Params) (st : State n) (raw : List (HeadWire n)) :
    raw.foldl (fun acc row => GridCO.admitVote p acc (GridCO.fromHead row)) (embed st) =
      embed (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st) := by
  apply List.foldl_hom embed
  intro acc row
  exact admitVote_embed p acc (fromHead row)

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Proposal admission keeps every old field. -/
theorem admitProposal_embed {n : Nat} (p : Params) (st : State n) (o : Wire n)
    (B : Block) (raw : List (HeadWire n)) :
    GridCO.admitProposal p (embed st) o B raw = embed (admitProposal p st o B raw) := by
  let denied := B.slot > (st.now / (4 * p.Δ)).toNat ||
    !blockKnown st B.parent || decide (B ∈ st.blocks) ||
    !decide (B.parent.slot < B.slot) ||
    !(match o.auth with | .proposer s => s == B.slot | _ => false)
  let next : State n := { st with
    blocks := st.blocks ++ [B]
    blockStamp := st.blockStamp ++ [(B, st.now)]
    proposals := st.proposals ++ [o] }
  have hnew : GridCO.admitProposal p (embed st) o B raw =
      if denied then embed st else
        raw.foldl (fun acc row => GridCO.admitVote p acc (GridCO.fromHead row)) (embed next) := by
    rcases o with ⟨a, m⟩
    cases a <;> rfl
  have hold : admitProposal p st o B raw =
      if denied then st else raw.foldl (fun acc row => admitVote p acc (fromHead row)) next := by
    rcases o with ⟨a, m⟩
    cases a <;> rfl
  rw [hnew, hold]
  split_ifs
  · rfl
  · exact votes_fold_embed p next raw

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Processing commutes for every legacy input. -/
theorem process_embed {n : Nat} (p : Params) (st : State n) (o : Wire n) :
    GridCO.process p (embed st) o = embed (process p st o) := by
  rcases o with ⟨a, m⟩
  cases a <;> cases m <;>
    simp only [GridCO.process, process, admitVote_embed, admitProposal_embed]

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Delivery folds commute for arbitrary old wires. -/
theorem deliveries_embed {n : Nat} (p : Params) (st : State n) (events : List (Wire n)) :
    events.foldl (GridCO.process p) (embed st) = embed (events.foldl (process p) st) :=
  List.foldl_hom embed (fun acc o => process_embed p acc o)

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Resolve an old HEAD by structural membership. -/
theorem resolvedHead_embed {n : Nat} (st : State n) (o : Wire n) :
    GridCO.resolvedHead? (embed st) o =
      (headTarget? o).filter (fun B => decide (B ∈ st.blocks)) := by
  rcases o with ⟨a, m⟩
  cases m with
  | proposal B raw sup => rfl
  | head B =>
      by_cases hm : B ∈ st.blocks <;>
        simp [GridCO.resolvedHead?, GridCO.headTarget?, GridCO.resolveTarget,
          GridCO.resolutionTree, headTarget?, embed, hm, Option.filter]

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Early support has a known target. -/
theorem resolvedHead_of_before {n : Nat} (st : State n) (o : Wire n) (t : Time)
    (h : resolvedBefore st o t = true) :
    GridCO.resolvedHead? (embed st) o = headTarget? o := by
  rw [resolvedHead_embed]
  unfold resolvedBefore at h
  cases ht : headTarget? o with
  | none => rfl
  | some B =>
      simp only [ht, Bool.and_eq_true, decide_eq_true_eq, blockKnown] at h
      simp [Option.filter, h.1.1.1]

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Compare predicates only at list members. -/
private theorem any_eq_on {α : Type} (xs : List α) (f g : α → Bool)
    (h : ∀ a ∈ xs, f a = g a) : xs.any f = xs.any g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.any_cons]
      rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Release keeps the complete old count formula. -/
theorem releaseCount_embed {n : Nat} (p : Params) (st : State n) (s : Slot) (B : Block) :
    GridCO.releaseCount p (embed st) s B = releaseCount p st s B := by
  unfold GridCO.releaseCount releaseCount
  simp only [
      ↓AvailableChain.GridCO.Legacy.hygiene_goldfishScore_match_1_eq,
      ↓AvailableChain.GridCO.hygiene_proposerSupportView_match_1_eq,
      votesAt_embed, resolvedBefore_embed, seats_block, equivocates_block, seatVotes_block]
  congr 1
  apply List.filter_congr
  intro i _
  apply congrArg (fun b => !equivocates (votesAt st s) i && b)
  apply any_eq_on
  intro o ho
  have hr := (List.mem_filter.mp (List.mem_filter.mp ho).1).2
  rw [resolvedHead_of_before st o _ hr]

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Count the same old participants. -/
@[simp] theorem voterCount_block {n : Nat} (xs : List (Wire n)) :
    GridCO.voterCount xs = voterCount xs := by simp [GridCO.voterCount, voterCount]

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Keep the old live-root selection. -/
@[simp] theorem liveRoot_embed {n : Nat} (st : State n) :
    GridCO.liveRoot (embed st) = liveRoot st := rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Keep the old frozen views. -/
@[simp] theorem frozenAt_embed {n : Nat} (st : State n) (s : Slot) :
    GridCO.frozenAt (embed st) s = frozenAt st s := rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Keep old proposer raw votes. -/
@[simp] theorem proposerView_embed {n : Nat} (st : State n) (s : Slot) :
    GridCO.proposerView (embed st) s = proposerView st s := votesAt_embed st (s - 1)

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Keep old proposer support. -/
@[simp] theorem proposerSupportView_embed {n : Nat} (st : State n) (s : Slot) :
    GridCO.proposerSupportView (embed st) s = proposerSupportView st s := by
  unfold GridCO.proposerSupportView proposerSupportView
  rw [proposerView_embed]
  apply List.filter_congr
  intro o _
  rw [resolvedHead_embed]
  cases ht : headTarget? o with
  | none => rfl
  | some B =>
      by_cases hm : B ∈ st.blocks <;> simp [Option.filter, blockKnown, hm]

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Keep old proposal selection by slot. -/
@[simp] theorem proposalsAt_embed {n : Nat} (st : State n) (s : Slot) :
    GridCO.proposalsAt (embed st) s = proposalsAt st s := by
  unfold GridCO.proposalsAt proposalsAt
  apply List.filter_congr
  intro o _
  cases o.payload <;> rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Keep old carried raw votes. -/
@[simp] theorem carriedRaw_embed {n : Nat} (st : State n) (s : Slot) :
    GridCO.carriedRaw (embed st) s = carriedRaw st s := by
  unfold GridCO.carriedRaw carriedRaw
  rw [proposalsAt_embed]
  apply congrArg₂ List.filter
  · funext o
    rw [headLabel_block]
  · apply List.flatMap_congr
    intro o _
    cases o.payload <;> rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Keep old carried support votes. -/
@[simp] theorem carriedSupport_embed {n : Nat} (st : State n) (s : Slot) :
    GridCO.carriedSupport (embed st) s = carriedSupport st s := by
  unfold GridCO.carriedSupport carriedSupport
  rw [proposalsAt_embed]
  apply congrArg₂ List.filter
  · funext o
    rw [headLabel_block, resolvedHead_embed]
    cases ht : headTarget? o with
    | none => rfl
    | some B =>
        by_cases hb : B ∈ st.blocks <;> simp [Option.filter, blockKnown, hb]
  · apply List.flatMap_congr
    intro o _
    cases o.payload <;> rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Keep the old voter raw merge. -/
@[simp] theorem voterView_embed {n : Nat} (p : Params) (st : State n) (s : Slot) :
    GridCO.voterView p (embed st) s = voterView p st s := by
  simp only [
      ↓AvailableChain.GridCO.Legacy.hygiene_voterView_match_1_eq,
      ↓AvailableChain.GridCO.hygiene_voterView_match_1_eq,
      GridCO.voterView, voterView, frozenAt_embed, carriedRaw_embed]
  cases frozenAt st (s - 1) with
  | none => rfl
  | some x => rcases x with ⟨raw, sup, blocks⟩; rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Keep the old voter support merge. -/
@[simp] theorem voterSupportView_embed {n : Nat} (p : Params) (st : State n) (s : Slot) :
    GridCO.voterSupportView p (embed st) s = voterSupportView p st s := by
  simp only [
      ↓AvailableChain.GridCO.Legacy.hygiene_voterView_match_1_eq,
      ↓AvailableChain.GridCO.hygiene_voterView_match_1_eq,
      GridCO.voterSupportView, voterSupportView, frozenAt_embed, carriedSupport_embed]
  cases frozenAt st (s - 1) with
  | none => rfl
  | some x => rcases x with ⟨raw, sup, blocks⟩; rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Keep the old voter tree. -/
@[simp] theorem voterTree_embed {n : Nat} (p : Params) (st : State n) (s : Slot) :
    GridCO.voterTree p (embed st) s = voterTree p st s := by
  unfold GridCO.voterTree voterTree
  rw [proposalsAt_embed, frozenAt_embed]
  cases frozenAt st (s - 1) with
  | none =>
      apply List.filter_congr
      intro B _
      congr 1
      apply List.any_congr
      · apply List.filterMap_congr
        intro o _
        cases o.payload <;> rfl
      · intro C; rfl
  | some x =>
      rcases x with ⟨raw, sup, blocks⟩
      apply List.filter_congr
      intro B _
      congr 1
      apply List.any_congr
      · apply List.filterMap_congr
        intro o _
        cases o.payload <;> rfl
      · intro C; rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Keep the old eligibility rule. -/
@[simp] theorem goldfishEligible_block {n : Nat} (tree : List Block)
    (raw sup : List (Wire n)) (s : Slot) (B : Block) :
    GridCO.goldfishEligible tree raw sup s B = goldfishEligible tree raw sup s B := by
  unfold GridCO.goldfishEligible goldfishEligible
  rw [goldfishScore_block, voterCount_block]

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Keep the old geometric fork choice. -/
@[simp] theorem forkChoice_embed {n : Nat} (st : State n) (tree : List Block)
    (raw sup : List (Wire n)) (s : Slot) :
    GridCO.forkChoice (embed st) tree raw sup s = forkChoice st tree raw sup s := by
  simp only [GridCO.forkChoice, forkChoice, liveRoot_embed]
  change ghost (liveRoot st) tree (GridCO.goldfishScore st.blocks raw sup)
    (GridCO.goldfishEligible st.blocks raw sup s) = _
  apply congrArg₂ (ghost (liveRoot st) tree)
  · funext B; exact goldfishScore_block _ _ _ B
  · funext B; exact goldfishEligible_block _ _ _ _ B

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Action commutes for every old state. -/
theorem act_embed {n : Nat} (p : Params) (st : State n) (s : Slot) :
    GridCO.act p (embed st) s = act p st s := by
  simp only [GridCO.act, act, voterTree_embed, voterView_embed, voterSupportView_embed,
    forkChoice_embed, GridCO.targetOfBlock]

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Expiry commutes with the old state embedding. -/
@[simp] theorem expire_embed {n : Nat} (st : State n) (t : Time) :
    GridCO.expire (embed st) t = embed (expire st t) := rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Lease writes commute with the old state embedding. -/
@[simp] theorem writeObligation_embed {n : Nat} (st : State n) (B : Block) (g : Nat) (t : Time) :
    GridCO.writeObligation (embed st) B g t = embed (writeObligation st B g t) := rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Saved labels have the old values. -/
@[simp] theorem savedGenuine_embed {n : Nat} (st : State n) (s : Slot) :
    GridCO.savedGenuine (embed st) s = savedGenuine st s := rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Saved result writes keep the old rule. -/
@[simp] theorem recordGenuine_embed [LeasePolicy] {n : Nat} (st : State n)
    (s : Slot) (result : Option Block) :
    GridCO.recordGenuine (embed st) s result = recordGenuine st s result := rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] The early cut retains exactly the old votes. -/
@[simp] theorem earlyVotes_embed {n : Nat} (p : Params) (st : State n) (s : Slot) :
    GridCO.earlyVotes p (embed st) s = earlyVotes p st s := by
  simp only [GridCO.earlyVotes, earlyVotes, votesAt_embed, resolvedBefore_embed]

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Confirmation has the old geometric result. -/
@[simp] theorem confirmationFrom_embed {n : Nat} (p : Params) (a : Block)
    (st : State n) (s : Slot) :
    GridCO.confirmationFrom p a (embed st) s = confirmationFrom p a st s := by
  unfold GridCO.confirmationFrom confirmationFrom
  dsimp only
  rw [cleanSupport_embed, lateVotes_embed, voterCount_block]
  have he : GridCO.goldfishScoreOn (GridCO.resolutionTree (embed st)) (embed st).blocks
      (cleanSupport p st s) (cleanSupport p st s) =
      goldfishScore st.blocks (cleanSupport p st s) (cleanSupport p st s) := by
    funext B
    exact goldfishScore_block _ _ _ B
  rw [he]
  rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Prefix support keeps the old count. -/
@[simp] theorem prefixSupport_embed {n : Nat} (p : Params) (st : State n) (s : Slot) (B : Block) :
    GridCO.prefixSupport p (embed st) s B = prefixSupport p st s B := by
  unfold GridCO.prefixSupport prefixSupport
  rw [cleanSupport_embed]
  exact goldfishScore_block _ _ _ B

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Slow eligibility keeps the old history test. -/
@[simp] theorem slowEligible_embed {n : Nat} (p : Params) (st : State n) (s : Slot) (B : Block) :
    GridCO.slowEligible p (embed st) s B = slowEligible p st s B := by
  unfold GridCO.slowEligible slowEligible
  congr 1

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] The lease levels keep their old tests and bounds. -/
@[simp] theorem admissionLevels_embed [LeasePolicy] {n : Nat} (p : Params)
    (st : State n) (s : Slot) (B : Block) :
    GridCO.admissionLevels p (embed st) s B = admissionLevels p st s B := by
  simp only [GridCO.admissionLevels, admissionLevels, prefixSupport_embed, slowEligible_embed,
    GridCO.releaseThreshold, releaseThreshold]
  congr 4

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] The freeze keeps both old cut lists. -/
@[simp] theorem freeze_embed {n : Nat} (p : Params) (st : State n) (s : Slot) :
    GridCO.freeze p (embed st) s = embed (freeze p st s) := by
  have hv : ((GridCO.votesAt (embed st) s).filter (fun o =>
      GridCO.stampVote (embed st) o < freezeTime p s)) =
      ((votesAt st s).filter (fun o => stampVote st o < freezeTime p s)) := by
    rw [votesAt_embed]
    apply List.filter_congr
    intro o _
    exact congrArg (fun (t : Time) => decide (t < freezeTime p s)) (stampVote_embed st o)
  have hs : ((GridCO.votesAt (embed st) s).filter (fun o =>
      GridCO.resolvedBefore (embed st) o (freezeTime p s))) =
      ((votesAt st s).filter (fun o => resolvedBefore st o (freezeTime p s))) := by
    simp only [votesAt_embed, resolvedBefore_embed]
  have hb : ((embed st).blocks.filter (fun B =>
      GridCO.stampBlock (embed st) B < freezeTime p s)) =
      (st.blocks.filter (fun B => stampBlock st B < freezeTime p s)) := by
    apply List.filter_congr
    intro B _
    exact congrArg (fun (t : Time) => decide (t < freezeTime p s)) (stampBlock_embed st B)
  unfold GridCO.freeze freeze
  dsimp only
  rw [hv, hs, hb]
  rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Release keeps the old snapshots and leases. -/
@[simp] theorem release_embed {n : Nat} (p : Params) (st : State n) (s : Slot) :
    GridCO.release p (embed st) s = embed (release p st s) := by
  have hr : ((GridCO.votesAt (embed st) s).filter (fun o =>
      GridCO.resolvedBefore (embed st) o (releaseTime p s))) =
      ((votesAt st s).filter (fun o => resolvedBefore st o (releaseTime p s))) := by
    simp only [votesAt_embed, resolvedBefore_embed]
  have hl : (embed st).obligations.filter (fun (B, g, _) =>
      GridCO.releaseCount p (embed st) s B < g) =
      st.obligations.filter (fun (B, g, _) => releaseCount p st s B < g) := by
    apply List.filter_congr
    rintro ⟨B, g, t⟩ _
    exact congrArg (fun k => decide (k < g)) (releaseCount_embed p st s B)
  unfold GridCO.release release
  dsimp only
  rw [hr, votesAt_embed, hl]
  rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Gate writes commute with old lease folds. -/
theorem gateFrom_embed [LeasePolicy] {n : Nat} (p : Params) (a : Block)
    (st : State n) (s : Slot) :
    GridCO.gateFrom p a (embed st) s = embed (gateFrom p a st s) := by
  unfold GridCO.gateFrom gateFrom
  rw [confirmationFrom_embed]
  cases hc : confirmationFrom p a st s with
  | none =>
      simp only [recordGenuine_embed]
      rfl
  | some H =>
      simp only [recordGenuine_embed]
      have levels : GridCO.admissionLevels p (embed st) s = admissionLevels p st s := by
        funext B
        exact admissionLevels_embed p st s B
      rw [levels]
      let mid : State n := { st with
        goldfishRecord := advance st.goldfishRecord H
        genuine := recordGenuine st s (some H) }
      let last : State n := { mid with stableRecord := advance mid.stableRecord H }
      let prefixes := st.blocks.filter (fun B => B != .genesis && Block.preceq B H)
      change (if st.obligations.any (fun (B, _, _) => !Block.compatible B H) then
        embed mid else prefixes.foldl (fun acc B =>
          (admissionLevels p st s B).foldl
            (fun acc g => GridCO.writeObligation acc B g (gateTime p s + lifetime p)) acc)
          (embed last)) =
        embed (if st.obligations.any (fun (B, _, _) => !Block.compatible B H) then
          mid else prefixes.foldl (fun acc B =>
            (admissionLevels p st s B).foldl
              (fun acc g => writeObligation acc B g (gateTime p s + lifetime p)) acc) last)
      split_ifs
      · rfl
      · apply List.foldl_hom embed
        intro acc B
        exact List.foldl_hom embed (fun acc g => writeObligation_embed acc B g _)

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Clock updates embed componentwise. -/
@[simp] theorem embed_now {n : Nat} (st : State n) (t : Time) :
    { embed st with now := t } = embed { st with now := t } := rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Early snapshots embed componentwise. -/
@[simp] theorem embed_early {n : Nat} (st : State n) (rows : List (Slot × List (Wire n))) :
    { embed st with early := rows } = embed { st with early := rows } := rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Conditional old states embed componentwise. -/
@[simp] theorem embed_ite {n : Nat} (h : Prop) [Decidable h] (st st' : State n) :
    (if h then embed st else embed st') = embed (if h then st else st') := by
  hygiene_split <;> rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Public clocks commute for every legacy state. -/
theorem clockFrom_embed [LeasePolicy] {n : Nat} (p : Params) (a : Block)
    (st : State n) (t : Time) :
    GridCO.clockFrom p a (embed st) t = embed (clockFrom p a st t) := by
  unfold GridCO.clockFrom clockFrom
  dsimp only
  simp only [embed_now, expire_embed, freeze_embed, embed_ite, earlyVotes_embed,
    embed_early, release_embed, gateFrom_embed]
  rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] The genesis-anchored clock keeps old behavior. -/
theorem clock_embed [LeasePolicy] {n : Nat} (p : Params) (st : State n) (t : Time) :
    GridCO.clock p (embed st) t = embed (clock p st t) := by
  rw [GridCO.clock_eq_from_genesis, clock_eq_from_genesis]
  exact clockFrom_embed p .genesis st t

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Old proposals keep their selected parent and lists. -/
theorem propose_embed {n : Nat} (p : Params) (st : State n) (s : Slot) :
    GridCO.propose p (embed st) s = propose p st s := by
  have ht : @GridCO.toHead? n .block = @toHead? n := funext toHead_block
  unfold GridCO.propose propose
  split_ifs
  · rfl
  · simp only [proposerView_embed, proposerSupportView_embed, forkChoice_embed, ht]
    rfl

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Every old clock or delivery step commutes. -/
theorem world_step_embed [LeasePolicy] (p : Params) {V : Type} [DecidableEq V]
    (w : V → State p.n) (e : Generic.Event V (Wire p.n)) :
    Generic.World.step (P := GridCO.gridCO p) (fun x => embed (w x)) e =
      fun x => embed (Generic.World.step (P := gridCO p) w e x) := by
  funext x
  cases e with
  | tick v t =>
      change Function.update (fun y => embed (w y)) v (GridCO.clock p (embed (w v)) t) x =
        embed (Function.update w v (clock p (w v) t) x)
      rw [clock_embed]
      simp [Function.update_apply]
  | deliver v o t =>
      change Function.update (fun y => embed (w y)) v (GridCO.process p (embed (w v)) o) x =
        embed (Function.update w v (process p (w v) o) x)
      rw [process_embed]
      simp [Function.update_apply]

/-- [ROOT-DIGEST-2 W1; DC deferred behavior] Induct over every arbitrary legacy event list. -/
theorem event_fold_embed [LeasePolicy] (p : Params) {V : Type} [DecidableEq V]
    (w : V → State p.n) (events : List (Generic.Event V (Wire p.n))) :
    events.foldl (Generic.World.step (P := GridCO.gridCO p)) (fun x => embed (w x)) =
      fun x => embed (events.foldl (Generic.World.step (P := gridCO p)) w x) :=
  List.foldl_hom (fun w x => embed (w x)) (fun w e => world_step_embed p w e)

end AvailableChain.GridCO.Legacy
end
