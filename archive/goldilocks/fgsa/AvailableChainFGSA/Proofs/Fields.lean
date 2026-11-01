module
public import AvailableChainGridCO.Proofs.StoreFacts
public import AvailableChainFGSA.Statements.Invariants
public import AvailableChainFGSA.Proofs.FrameViews -- shake: keep (re-export)
public import AvailableChainFGSA.Proofs.BlockAncestry

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

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

-- ROOT-DIGEST-2 option 3: use a private copy of the same matcher (BUILD B3).
private def hygiene_admitBlock (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) : State p.n :=
  if !namedParentHeld st N then st else
  match parentFG st N.erase with
  | none => st
  | some P =>
      if blockAccepted p st s N P then
        let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
          fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
        let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
        N.rows.foldl (admitRow p) st2
      else st

-- The generated matcher bodies are definitionally equal.
private theorem hygiene_admitBlock_match_1_eq :
    hygieneEq% (@admitBlock) (@hygiene_admitBlock) := rfl

end AvailableChain.FGSA

-- Rewrite before simp can generate equations for the public matcher.
attribute [local simp↓]
  AvailableChain.FGSA.hygiene_admitBlock_match_1_eq

local macro "hygiene_split" : tactic =>
  `(tactic| (
    try rw [AvailableChain.FGSA.hygiene_admitBlock_match_1_eq] at *;
    all_goals split))

local macro "hygiene_split" "at" h:ident : tactic =>
  `(tactic| (
    try rw [AvailableChain.FGSA.hygiene_admitBlock_match_1_eq] at *;
    all_goals split at $h:ident))

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-! The write sets of the steps (Task 7, Step 2): for each step, the fields that
it does not write, and the exact gate effects that K1 and K6 need. -/

variable {n : Nat}

/-! ### `admitHead` -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A vote writes no FG field. -/
theorem admitHead_fg (p : Params) (st : State p.n) (s : Slot) (i : Fin p.n) (b : BlockId) :
    (admitHead p st s i b).fg = st.fg := rfl
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A vote writes no block. -/
theorem admitHead_base_blocks (p : Params) (st : State p.n) (s : Slot) (i : Fin p.n) (b : BlockId) :
    (admitHead p st s i b).base.blocks = st.base.blocks :=
  @GridCO.admitVote_blocks GridCO.slowLeasePolicy .root _ _ _ _
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A vote does not write S. -/
theorem admitHead_base_stable (p : Params) (st : State p.n) (s : Slot) (i : Fin p.n) (b : BlockId) :
    (admitHead p st s i b).base.stableRecord = st.base.stableRecord :=
  @GridCO.admitVote_stable GridCO.slowLeasePolicy .root _ _ _ _
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A vote writes no lease. -/
theorem admitHead_obligations (p : Params) (st : State p.n) (s : Slot) (i : Fin p.n)
    (b : BlockId) : (admitHead p st s i b).base.obligations = st.base.obligations :=
  @GridCO.admitVote_obligations GridCO.slowLeasePolicy .root _ _ _ _
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A vote does not write `fastWrite`. -/
theorem admitHead_fastWrite (p : Params) (st : State p.n) (s : Slot) (i : Fin p.n) (b : BlockId) :
    (admitHead p st s i b).fastWrite = st.fastWrite := rfl
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A vote writes no saved result. -/
theorem admitHead_genuine (p : Params) (st : State p.n) (s : Slot) (i : Fin p.n) (b : BlockId) :
    (admitHead p st s i b).base.genuine = st.base.genuine := by
  simp only [admitHead, GridCO.admitVote]
  hygiene_split <;> rfl

/-! ### `admitRow` and `admitBlock` -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A row changes only the row pool: the state is
unchanged, or the row
is appended. -/
theorem admitRow_eq (p : Params) (st : State p.n) (a : RowWire p.n) :
    admitRow p st a = st ∨ admitRow p st a = { st with rowPool := st.rowPool ++ [a] } := by
  unfold admitRow
  hygiene_split
  · hygiene_split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact Or.inl rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A refused block changes nothing: no stored parent, or
a failed
acceptance test. -/
theorem admitBlock_refused (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n)
    (h : namedParentHeld st N = false ∨ parentFG st N.erase = none ∨
      ∃ P, parentFG st N.erase = some P ∧ blockAccepted p st s N P = false) :
    admitBlock p st s N = st := by
  unfold admitBlock
  rcases h with h | h | ⟨P, hP, ha⟩
  · simp only [
      ↓AvailableChain.FGSA.hygiene_admitBlock_match_1_eq,
      h, Bool.not_false, ite_true]
  · hygiene_split <;> simp only [h]
  · hygiene_split <;> simp only [hP, ha, Bool.false_eq_true, ite_false]

/-! ### `onView`, `normalizeS`, `reconcile` -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [M2] `onView` writes no FG field. -/
theorem onView_fg (f : GridCO.State n .root → GridCO.State n .root) (st : State n) :
    (onView f st).fg = st.fg := rfl
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [M2] `onView` keeps the cumulative block list. -/
theorem onView_base_blocks (f : GridCO.State n .root → GridCO.State n .root) (st : State n) :
    (onView f st).base.blocks = st.base.blocks := rfl
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [M2] `onView` writes no proposal wire. -/
theorem onView_proposals (f : GridCO.State n .root → GridCO.State n .root) (st : State n) :
    (onView f st).proposals = st.proposals := rfl
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [M2] `onView` writes no row. -/
theorem onView_rowPool (f : GridCO.State n .root → GridCO.State n .root) (st : State n) :
    (onView f st).rowPool = st.rowPool := rfl
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [M2] `onView` does not write `fastWrite`. -/
theorem onView_fastWrite (f : GridCO.State n .root → GridCO.State n .root) (st : State n) :
    (onView f st).fastWrite = st.fastWrite := rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] `normalizeS` writes no FG field. -/
theorem normalizeS_fg (st : State n) : (normalizeS st).fg = st.fg := by
  unfold normalizeS
  hygiene_split <;> rfl
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] `normalizeS` writes only S: `S := F` if `F ⋠ S`. -/
theorem normalizeS_fields (st : State n) :
    normalizeS st = { st with base := { st.base with
      stableRecord := if Block.preceq (eraseFG st.fg.F) st.base.stableRecord then
        st.base.stableRecord else eraseFG st.fg.F } } := by
  unfold normalizeS
  hygiene_split <;> rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] `reconcile` writes no FG field. -/
theorem reconcile_fg (st : State n) : (reconcile st).fg = st.fg := by
  unfold reconcile
  rw [normalizeS_fg]

/-! ### The GridCO steps that the tick runs keep `blocks` -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The freeze cache step keeps `blocks`. -/
theorem freeze_blocks (q : GridCO.Params) (v : GridCO.State n .root) (r : Slot) :
    (GridCO.freeze q v r).blocks = v.blocks := rfl
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The release step keeps `blocks`. -/
theorem release_blocks (p : SA.Params) (v : GridCO.State n .root) (r : Slot) :
    (SA.Root.release p v r).blocks = v.blocks := rfl
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The SA gate with the walk from `a` keeps `blocks`.
Proof:
`@GridCO.gateFrom_blocks GridCO.slowLeasePolicy .root p.engine n a v r` (the default
instance would elaborate the GRID gate). -/
theorem saGate_blocks (p : SA.Params) (a : Block) (v : GridCO.State n .root) (r : Slot) :
    (SA.Root.gateFrom p a v r).blocks = v.blocks :=
  @GridCO.gateFrom_blocks GridCO.slowLeasePolicy .root p.engine n a v r

/-! ### The gate -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The gate writes no FG field. -/
theorem gateStep_fg (p : Params) (st : State p.n) (s : Slot) :
    (gateStep p st s).fg = st.fg := by
  unfold gateStep
  rw [normalizeS_fg]
  split_ifs <;> rfl
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The gate keeps the cumulative block list. -/
theorem gateStep_base_blocks (p : Params) (st : State p.n) (s : Slot) :
    (gateStep p st s).base.blocks = st.base.blocks := by
  unfold gateStep
  rw [normalizeS_fields]
  split_ifs <;> rfl
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The gate writes no proposal wire. -/
theorem gateStep_proposals (p : Params) (st : State p.n) (s : Slot) :
    (gateStep p st s).proposals = st.proposals := by
  unfold gateStep
  rw [normalizeS_fields]
  split_ifs <;> rfl
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The gate writes no row. -/
theorem gateStep_rowPool (p : Params) (st : State p.n) (s : Slot) :
    (gateStep p st s).rowPool = st.rowPool := by
  unfold gateStep
  rw [normalizeS_fields]
  split_ifs <;> rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] `savedGenuine` of a list with one appended label `s`,
when `s` was
not saved: label `s` reads the new result, and every other label is unchanged. -/
theorem savedGenuine_append (v : GridCO.State n .root) (s : Slot) (x : Option Block)
    (hnew : GridCO.savedGenuine v s = none) (r : Slot) :
    GridCO.savedGenuine { v with genuine := v.genuine ++ [(s, x)] } r =
      if r = s then some x else GridCO.savedGenuine v r := by
  unfold GridCO.savedGenuine at hnew ⊢
  simp only [Option.map_eq_none_iff] at hnew
  rw [List.find?_append]
  hygiene_split
  · next hr =>
    subst hr
    rw [hnew]
    simp
  · next hr =>
    cases hf : v.genuine.find? (fun row => row.1 == r) with
    | some row => simp
    | none =>
        have hne : ((s, x).1 == r) = false := beq_false_of_ne (Ne.symm hr)
        simp [List.find?, hne]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The SA gate with the walk from `a`, on a view whose
label `s` is not
saved, appends `(s, confirmationFrom a)` to `genuine` and writes no other saved
result. -/
theorem saGate_genuine (p : SA.Params) (a : Block) (v : GridCO.State n .root) (s : Slot)
    (hnew : GridCO.savedGenuine v s = none) :
    (SA.Root.gateFrom p a v s).genuine = v.genuine ++ [(s, SA.Root.confirmationFrom p a v s)] := by
  have hrec : ∀ x, @GridCO.recordGenuine GridCO.slowLeasePolicy n .root v s x =
      v.genuine ++ [(s, x)] := by
    intro x
    simp [GridCO.recordGenuine, hnew]
  have hfold : ∀ (bs : List Block) (f : Block → List Nat) (d : Time) (acc : GridCO.State n .root),
      (bs.foldl (fun acc b => (f b).foldl
        (fun acc g => GridCO.writeObligation acc b g d) acc) acc).genuine = acc.genuine := by
    intro bs f d
    induction bs with
    | nil => intro acc; rfl
    | cons b bs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih]
        generalize f b = gs
        induction gs generalizing acc with
        | nil => rfl
        | cons g gs ihg => simp only [List.foldl_cons]; rw [ihg]; rfl
  simp only [SA.Root.gateFrom, GridCO.gateFrom, SA.Root.confirmationFrom]
  hygiene_split
  · next hc => simp only [hrec, hc]
  · next h hc =>
    hygiene_split
    · simp only [hrec, hc]
    · rw [hfold]
      simp only [hrec, hc]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.leaseOrigins.v1; K1, K6; spec 4e85ff34: 885–913,
1280–1297] A fresh
gate saves the confirmation of the view with the walk from `Σ.F`
(`genuine_result`) and adds exactly `fastSet` of the view at the same anchor; a
saved label changes neither. -/
theorem gateStep_fresh (p : Params) (st : State p.n) (s : Slot)
    (hnew : GridCO.savedGenuine st.base s = none) (hj : joinedNow p st = true) :
    GridCO.savedGenuine (gateStep p st s).base s =
      some (SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s) ∧
    (∀ r ≠ s, GridCO.savedGenuine (gateStep p st s).base r = GridCO.savedGenuine st.base r) ∧
    (gateStep p st s).fastWrite =
      st.fastWrite ++ [(s, fastSet p (eraseFG st.fg.F) (actView st) s)] := by
  have hv : GridCO.savedGenuine (actView st) s = none := hnew
  have hg := saGate_genuine p.toParams (eraseFG st.fg.F) (actView st) s hv
  have hsave : ∀ r, GridCO.savedGenuine (gateStep p st s).base r =
      if r = s then some (SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s)
      else GridCO.savedGenuine st.base r := by
    intro r
    have := savedGenuine_append (actView st) s
      (SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s) hv r
    unfold gateStep
    rw [normalizeS_fields]
    simp only [hnew, Option.isSome_none, Bool.false_eq_true, ite_false, hj,
      Bool.not_true]
    unfold onView
    simp only [GridCO.savedGenuine] at this ⊢
    rw [hg]
    exact this
  refine ⟨by simpa using hsave s, fun r hr => by simpa [hr] using hsave r, ?_⟩
  unfold gateStep
  rw [normalizeS_fields]
  simp [hnew, hj]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A saved label: the gate is `normalizeS` only. -/
theorem gateStep_saved (p : Params) (st : State p.n) (s : Slot)
    (hs : (GridCO.savedGenuine st.base s).isSome) : gateStep p st s = normalizeS st := by
  unfold gateStep
  simp only [hs, ite_true]

/-- [Sleep v6; plan §14.3] An unjoined gate saves empty lists and keeps durable outputs. -/
theorem gateStep_unjoined (p : Params) (st : State p.n) (s : Slot)
    (hnew : GridCO.savedGenuine st.base s = none) (hj : joinedNow p st = false) :
    GridCO.savedGenuine (gateStep p st s).base s = some none ∧
    (gateStep p st s).fastWrite = st.fastWrite ++ [(s, [])] ∧
    (NestOK st → (gateStep p st s).fg = st.fg ∧
      (gateStep p st s).base.obligations = st.base.obligations ∧
      (gateStep p st s).base.stableRecord = st.base.stableRecord) := by
  have he : gateStep p st s = normalizeS
      { onView (fun v => { v with genuine := v.genuine ++ [(s, none)] }) st with
        fastWrite := st.fastWrite ++ [(s, [])] } := by
    simp only [gateStep, hnew, Option.isSome_none, Bool.false_eq_true, ite_false,
      hj, Bool.not_false, ite_true]
  refine ⟨?_, ?_, ?_⟩
  · rw [he, normalizeS_fields]
    simpa only [GridCO.savedGenuine, onView, actView, ite_true] using
      savedGenuine_append (actView st) s none hnew s
  · rw [he, normalizeS_fields]
  · intro hn
    rw [he, normalizeS_fields]
    exact ⟨rfl, rfl, ite_eq_left hn⟩

/-- [Sleep v6; plan §14.3] A fresh unjoined gate saves an empty result. -/
theorem gateStep_unjoined_eq (p : Params) (st : State p.n) (s : Slot)
    (hnew : GridCO.savedGenuine st.base s = none) (hj : joinedNow p st = false) :
    gateStep p st s = normalizeS
      { onView (fun v => { v with genuine := v.genuine ++ [(s, none)] }) st with
        fastWrite := st.fastWrite ++ [(s, [])] } := by
  simp only [gateStep, hnew, Option.isSome_none, Bool.false_eq_true, ite_false,
    hj, Bool.not_false, ite_true]

/-- [Sleep v6; plan §14.3] A gate keeps each other saved label. -/
theorem gateStep_other (p : Params) (st : State p.n) (s r : Slot) (hr : r ≠ s) :
    GridCO.savedGenuine (gateStep p st s).base r = GridCO.savedGenuine st.base r := by
  cases hs : GridCO.savedGenuine st.base s with
  | some x =>
      rw [gateStep_saved p st s (by simp [hs]), normalizeS_fields]
      rfl
  | none =>
      cases hj : joinedNow p st with
      | true => exact (gateStep_fresh p st s hs hj).2.1 r hr
      | false =>
          rw [gateStep_unjoined_eq p st s hs hj, normalizeS_fields]
          exact (savedGenuine_append (actView st) s none hs r).trans (ite_eq_right hr)

/-- [Sleep v6; plan §14.3] The two cases of a fresh gate. -/
theorem gateStep_fresh_cases (p : Params) (st : State p.n) (s : Slot)
    (hnew : GridCO.savedGenuine st.base s = none) :
    GridCO.savedGenuine (gateStep p st s).base s =
      (if joinedNow p st then
        some (SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s)
      else some none) ∧
    (gateStep p st s).fastWrite = st.fastWrite ++
      [(s, if joinedNow p st then fastSet p (eraseFG st.fg.F) (actView st) s else [])] := by
  cases hj : joinedNow p st with
  | true => simpa only [ite_true] using
      ⟨(gateStep_fresh p st s hnew hj).1, (gateStep_fresh p st s hnew hj).2.2⟩
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [gateStep_unjoined_eq p st s hnew hj, normalizeS_fields]
      exact ⟨by simpa only [GridCO.savedGenuine, onView, actView, ite_true] using
      savedGenuine_append (actView st) s none hnew s, rfl⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] Every member of `fastSet` at anchor `a` is a
non-genesis prefix of
the confirmation with the walk from `a`. -/
theorem fastSet_prefix (p : Params) (a : Block) (v : GridCO.State p.n .root) (s : Slot)
    {B : Block} (hB : B ∈ fastSet p a v s) :
    ∃ h, SA.Root.confirmationFrom p.toParams a v s = some h ∧ Block.Preceq B h ∧ B ∈ v.blocks ∧
      B ≠ .genesis := by
  unfold fastSet at hB
  hygiene_split at hB
  · simp at hB
  · next h hc =>
    hygiene_split at hB
    · simp at hB
    · simp only [List.mem_filter, Bool.and_eq_true] at hB
      exact ⟨h, hc, hB.2.1.2, hB.1, by simpa using hB.2.1.1⟩

/-! ### The tick -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The tick before the gate writes no FG field, no block,
no proposal
wire, no row, no saved result and no `fastWrite` set. -/
theorem clockPre_fields (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).fg = st.fg ∧ (clockPre p st t).base.blocks = st.base.blocks ∧
    (clockPre p st t).proposals = st.proposals ∧ (clockPre p st t).rowPool = st.rowPool ∧
    (clockPre p st t).base.genuine = st.base.genuine ∧
    (clockPre p st t).fastWrite = st.fastWrite := by
  unfold clockPre
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The tick before the gate writes no FG field. -/
theorem clockPre_fg (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).fg = st.fg := (clockPre_fields p st t).1
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The tick before the gate writes no saved result. -/
theorem clockPre_genuine (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).base.genuine = st.base.genuine := (clockPre_fields p st t).2.2.2.2.1
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The tick before the gate does not write `fastWrite`.
-/
theorem clockPre_fastWrite (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).fastWrite = st.fastWrite := (clockPre_fields p st t).2.2.2.2.2

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The tick writes no FG field. -/
theorem clock_fg (p : Params) (st : State p.n) (t : Time) : (clock p st t).fg = st.fg := by
  unfold clock
  dsimp only
  hygiene_split
  · rw [gateStep_fg, clockPre_fg]
  · exact clockPre_fg p st t
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The tick keeps the cumulative block list. -/
theorem clock_base_blocks (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).base.blocks = st.base.blocks := by
  unfold clock
  dsimp only
  hygiene_split
  · rw [gateStep_base_blocks]; exact (clockPre_fields p st t).2.1
  · exact (clockPre_fields p st t).2.1
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The tick writes no proposal wire. -/
theorem clock_proposals (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).proposals = st.proposals := by
  unfold clock
  dsimp only
  hygiene_split
  · rw [gateStep_proposals]; exact (clockPre_fields p st t).2.2.1
  · exact (clockPre_fields p st t).2.2.1
/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The tick writes no row. -/
theorem clock_rowPool (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).rowPool = st.rowPool := by
  unfold clock
  dsimp only
  hygiene_split
  · rw [gateStep_rowPool]; exact (clockPre_fields p st t).2.2.2.1
  · exact (clockPre_fields p st t).2.2.2.1

end AvailableChain.FGSA
end
