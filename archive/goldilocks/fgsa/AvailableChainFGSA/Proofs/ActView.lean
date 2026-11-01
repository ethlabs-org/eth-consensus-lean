module
public import AvailableChainFGSA.Statements.Invariants
public import AvailableChainFGSA.Proofs.Fields
public import AvailableChainFGSA.Proofs.Carrier
public import AvailableChainFGSA.Proofs.HeadResolution

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

-- The generated matcher bodies are definitionally equal.
private theorem fgsa_hygiene_proposerSupportView_match_1_eq :
    hygieneEq% (@proposerSupportView) (@hygiene_proposerSupportView) := rfl

end AvailableChain.GridCO

-- Rewrite before simp can generate equations for the public matcher.
attribute [local simp↓]
  AvailableChain.GridCO.fgsa_hygiene_proposerSupportView_match_1_eq

local macro "hygiene_split" : tactic =>
  `(tactic| (
    try rw [AvailableChain.GridCO.fgsa_hygiene_proposerSupportView_match_1_eq] at *;
    all_goals split))

local macro "hygiene_split" "at" h:ident : tactic =>
  `(tactic| (
    try rw [AvailableChain.GridCO.fgsa_hygiene_proposerSupportView_match_1_eq] at *;
    all_goals split at $h:ident))

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-! The active view `act(Σ)` (bp01 §5, `bp.activeView.v1`, items 1–6), the
commutation of `actView` with the view steps (M2), and the tick SA bridge
(comp D3). -/

variable {n : Nat}

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] `A ⪯ B` gives `A ∥ B` compatible. -/
theorem block_compatible_of_preceq {A B : Block} (h : Block.Preceq A B) :
    Block.Compatible A B := by
  unfold Block.Compatible Block.compatible
  simp only [Bool.or_eq_true]
  exact Or.inl h

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] If `K ⪯ F`, a block compatible with `F` is compatible
with `K`. -/
theorem block_compatible_of_below {b K F : Block} (hK : Block.Preceq K F)
    (hb : Block.Compatible b F) : Block.Compatible b K := by
  unfold Block.Compatible Block.compatible at hb
  simp only [Bool.or_eq_true] at hb
  rcases hb with hbF | hFb
  · exact block_compatible_of_common hbF hK
  · have hKb := block_preceq_trans hK hFb
    unfold Block.Compatible Block.compatible
    simp only [Bool.or_eq_true]
    exact Or.inr hKb

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] An ancestor of an erased member of an ancestor-closed
set is the
erasure of a member. -/
theorem eraseFG_ancestor_mem {T : Finset (FGBlock (Fin n))} (hcl : ∀ B ∈ T, B.parent ∈ T)
    {B : FGBlock (Fin n)} (hB : B ∈ T) {c : Block} (hc : Block.Preceq c (eraseFG B)) :
    ∃ C ∈ T, eraseFG C = c := by
  induction B with
  | genesis =>
      simp only [eraseFG, Block.Preceq, Block.preceq, decide_eq_true_eq] at hc
      exact ⟨.genesis, hB, hc.symm⟩
  | node P s r_s r rows ih =>
      simp only [eraseFG, Block.Preceq, Block.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hc
      rcases hc with hc | hc
      · exact ⟨.node P s r_s r rows, hB, hc.symm⟩
      · exact ih (hcl _ hB) hc

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.activeView.v1] (item 1, first part) `actView` keeps only
stored blocks. -/
theorem actView_blocks (st : State n) (b : Block) :
    b ∈ (actView st).blocks ↔ b ∈ st.base.blocks ∧ Block.Compatible b (eraseFG st.fg.F) := by
  simp [actView, activeCompatible, Block.Compatible]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.activeView.v1] (item 1) A ⊆ T, and g, F ∈ A. -/
theorem actView_genesis_F (p : Params) (st : State p.n) (h : CStoreInv p st) :
    Block.genesis ∈ (actView st).blocks ∧ eraseFG st.fg.F ∈ (actView st).blocks := by
  refine ⟨(actView_blocks st _).2 ⟨(h.baseTree _).2 ⟨.genesis, h.fg.gen, rfl⟩, ?_⟩,
    (actView_blocks st _).2 ⟨(h.baseTree _).2 ⟨st.fg.F, h.fg.Fmem, rfl⟩, ?_⟩⟩
  · exact block_compatible_of_preceq (block_genesis_preceq _)
  · exact block_compatible_of_preceq (block_preceq_refl _)

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.activeView.v1] (item 2) A is ancestor-closed. -/
theorem actView_ancestor_closed (p : Params) (st : State p.n) (h : CStoreInv p st)
    {b c : Block} (hb : b ∈ (actView st).blocks) (hc : Block.Preceq c b) :
    c ∈ (actView st).blocks := by
  rw [actView_blocks] at hb ⊢
  obtain ⟨B, hB, rfl⟩ := (h.baseTree _).1 hb.1
  obtain ⟨C, hC, rfl⟩ := eraseFG_ancestor_mem h.fg.closed hB hc
  exact ⟨(h.baseTree _).2 ⟨C, hC, rfl⟩, block_compatible_of_preceq_compatible hc hb.2⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.activeView.v1] (item 3) For fixed Σ.T, a later F gives a
smaller view. -/
theorem actView_antitone (st : State n) {F' : FGBlock (Fin n)} (h : FGBlock.Preceq st.fg.F F') :
    ∀ b ∈ (actView { st with fg := { st.fg with F := F' } }).blocks, b ∈ (actView st).blocks := by
  intro b hb
  rw [actView_blocks] at hb ⊢
  refine ⟨hb.1, ?_⟩
  by_contra hn
  exact block_incompatible_of_preceq hn (eraseFG_preceq h) hb.2

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.activeView.v1] (item 4) Heads above F are active, and so
is every
path vertex from F to them. -/
theorem actView_path (p : Params) (st : State p.n) (h : CStoreInv p st) {B K : Block}
    (hK : K ∈ st.base.blocks) (hFB : Block.Preceq (eraseFG st.fg.F) B) (hBK : Block.Preceq B K) :
    K ∈ (actView st).blocks ∧ B ∈ (actView st).blocks := by
  have hKa : K ∈ (actView st).blocks := by
    rw [actView_blocks]
    refine ⟨hK, ?_⟩
    rw [Block.Compatible, block_compatible_comm]
    exact block_compatible_of_preceq (block_preceq_trans hFB hBK)
  exact ⟨hKa, actView_ancestor_closed p st h hKa hBK⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.activeView.v1] (item 5; DQ9) Exclusion is stable under F
advances. -/
theorem blockExcluded_stable (st : State n) {F' : FGBlock (Fin n)} (h : FGBlock.Preceq st.fg.F F')
    (b : Block) (hx : blockExcluded st b = true) :
    blockExcluded { st with fg := { st.fg with F := F' } } b = true := by
  simp only [blockExcluded, activeCompatible, Bool.not_eq_true'] at hx ⊢
  have hn : ¬ Block.Compatible b (eraseFG st.fg.F) := by
    simp [Block.Compatible, hx]
  have := block_incompatible_of_preceq hn (eraseFG_preceq h)
  simpa [Block.Compatible] using this

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.activeView.v1] (item 5, second sentence; G7 m1) View
restriction
filters blocks and pins the cumulative HEAD resolution domain. -/
theorem actView_eq (st : State n) :
    actView st = { st.base with
      blocks := st.base.blocks.filter (activeCompatible st)
      headDomain := some (GridCO.resolutionTree st.base) } := rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.activeView.v1] (item 5, second sentence) View
restriction changes no
signed pool, no stamp, no lease, no saved result, no S and no time.
`actView_eq` also gives the resolution metadata. -/
theorem actView_fields (st : State n) :
    (actView st).votes = st.base.votes ∧ (actView st).voteStamp = st.base.voteStamp ∧
    (actView st).blockStamp = st.base.blockStamp ∧ (actView st).proposals = st.base.proposals ∧
    (actView st).genuine = st.base.genuine ∧ (actView st).obligations = st.base.obligations ∧
    (actView st).stableRecord = st.base.stableRecord ∧ (actView st).now = st.base.now :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.activeView.v1] (item 6) If `K ⪯ F`, every active block
is compatible
with `K`, so a lease on `K` cannot veto an active genuine result. -/
theorem actView_noVeto (st : State n) {K : Block} (hK : Block.Preceq K (eraseFG st.fg.F)) :
    ∀ b ∈ (actView st).blocks, Block.Compatible K b := by
  intro b hb
  rw [actView_blocks] at hb
  rw [Block.Compatible, block_compatible_comm]
  exact block_compatible_of_below hK hb.2

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.activeView.v1] (item 6; K11 base case) If `K ⪯ F`, the
active release
count against `K` is zero, for every label. -/
theorem actView_releaseCount_zero (st : State n) (q : GridCO.Params) (r : Slot) {K : Block}
    (hK : Block.Preceq K (eraseFG st.fg.F)) : GridCO.releaseCount q (actView st) r K = 0 := by
  unfold GridCO.releaseCount
  simp only [
      ↓AvailableChain.GridCO.fgsa_hygiene_proposerSupportView_match_1_eq,
      List.length_eq_zero_iff, List.filter_eq_nil_iff, Bool.and_eq_true,
    Bool.not_eq_true', List.any_eq_true, not_and, not_exists]
  intro i _ _ o ho
  simp only [GridCO.seatVotes, List.mem_filter] at ho
  have hrb := ho.1.2
  unfold GridCO.resolvedBefore at hrb
  hygiene_split at hrb
  · simp at hrb
  · next b hb =>
    rw [hb]
    have hm := resolvedHead_mem (actView st) o hb
    have hc := block_compatible_of_below hK ((actView_blocks st b).1 hm).2
    simp only [Block.Compatible] at hc
    simp [hc]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [M2] A step that preserves blocks and resolution metadata
commutes with `actView`. -/
theorem actView_onView (f : GridCO.State n .root → GridCO.State n .root)
    (hf : ∀ v, (f v).blocks = v.blocks)
    (hd : ∀ v, (f v).headDomain = v.headDomain) (st : State n) :
    actView (onView f st) = f (actView st) := by
  change { f (actView st) with
    blocks := (actView st).blocks, headDomain := (actView st).headDomain } = f (actView st)
  rw [← hf (actView st), ← hd (actView st)]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A vote admission commutes with `actView` (SA's vote
pool reads no block). -/
theorem actView_admitHead (p : Params) (st : State p.n) (s : Slot) (i : Fin p.n) (b : BlockId) :
    actView (admitHead p st s i b) =
      GridCO.admitVote p.toParams.engine (actView st) ⟨.seat s i, .head b⟩ := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [actView, admitHead, GridCO.admitVote]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

/-! ### The tick SA bridge (comp D3) -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [M8; helper] The tick before the gate is ONE `onView` step: the
SA pre-gate
steps (expiry, freeze, early, release) on the active view. -/
theorem clockPre_eq (p : Params) (st : State p.n) (t : Time) :
    clockPre p st t = onView (fun v =>
      let q := p.toParams
      let v := GridCO.expire { v with now := t } t
      let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
      let v := if 0 ≤ t - 3 * p.Δ && t == SA.freezeTime q fSlot then
        GridCO.freeze q.engine v fSlot else v
      let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
      let v := if 0 ≤ t - 2 * p.Δ && t == SA.earlyTime q eSlot then
        { v with early := v.early ++ [(eSlot, GridCO.earlyVotes q.engine v eSlot)] } else v
      let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
      if 0 ≤ t - 5 * p.Δ && t == SA.releaseTime q qSlot && joinedAtTime p st.restartTime t then
        SA.Root.release q v qSlot else v) st := by
  unfold clockPre
  by_cases h1 : (0 ≤ t - 3 * p.Δ &&
    t == SA.freezeTime p.toParams ((t - 3 * p.Δ) / (4 * p.Δ)).toNat) = true <;>
  by_cases h2 : (0 ≤ t - 2 * p.Δ &&
    t == SA.earlyTime p.toParams ((t - 2 * p.Δ) / (4 * p.Δ)).toNat) = true <;>
  by_cases h3 : (0 ≤ t - 5 * p.Δ &&
    t == SA.releaseTime p.toParams ((t - 5 * p.Δ) / (4 * p.Δ)).toNat &&
    joinedAtTime p st.restartTime t) = true
  all_goals simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true]
  all_goals dsimp only [joinedNow, onView, actView, GridCO.expire, GridCO.freeze]
  all_goals simp only [h3, ite_true]
  all_goals rfl


/-- [ROOT-DIGEST-2 W1; DC root HEAD] [M2; helper] Two `onView` steps are one when the first
preserves
`blocks` and `headDomain`. -/
theorem onView_onView (f g : GridCO.State n .root → GridCO.State n .root)
    (hf : ∀ v, (f v).blocks = v.blocks)
    (hd : ∀ v, (f v).headDomain = v.headDomain) (st : State n) :
    onView g (onView f st) = onView (fun v => g (f v)) st := by
  have h := actView_onView f hf hd st
  unfold onView at h ⊢
  rw [h]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [comp D3; M7, M8] Off the gate times, the composite tick is the
SA tick on
the active view with the cumulative block list and resolution metadata restored. -/
theorem clock_eq_saClock_offGate (p : Params) (st : State p.n) (t : Time)
    (hg : ¬ (0 ≤ t - 6 * p.Δ ∧ t = SA.gateTime p.toParams ((t - 6 * p.Δ) / (4 * p.Δ)).toNat))
    (hj : joinedAtTime p st.restartTime t = true) :
    clock p st t =
      { st with base := { SA.Root.clock p.toParams (actView st) t with
        blocks := st.base.blocks, headDomain := st.base.headDomain } } := by
  have hc : ¬ ((decide (0 ≤ t - 6 * p.Δ) &&
      t == SA.gateTime p.toParams ((t - 6 * p.Δ) / (4 * p.Δ)).toNat) = true) := by
    simpa using hg
  unfold clock
  rw [ite_eq_right hc, clockPre_eq,
    show SA.Root.clock p.toParams (actView st) t = _ from ite_eq_right hc]
  simp only [hj, Bool.and_true]
  rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [comp D3; M7, DQ5; Opus m1; spec 4e85ff34: 885–913, 1280–1297]
At a gate
time of an unsaved label, the composite tick is `normalizeS` of the SA tick with
the walk from F (`SA.Root.clockFrom` at `eraseFG st.fg.F`) on the active view, with
EXACTLY the fast set (at the same anchor) of the view before the gate added. The
tick does not move F before the gate (`clockPre_fg`), so the anchor is F of the
tick input. -/
theorem clock_eq_saClockFrom_gate (p : Params) (st : State p.n) (t : Time) (s : Slot)
    (hs : s = ((t - 6 * p.Δ) / (4 * p.Δ)).toNat) (hg : 0 ≤ t - 6 * p.Δ)
    (ht : t = SA.gateTime p.toParams s)
    (hnew : GridCO.savedGenuine st.base s = none)
    (hj : joinedAtTime p st.restartTime t = true) :
    clock p st t = normalizeS { st with
      base := { SA.Root.clockFrom p.toParams (eraseFG st.fg.F) (actView st) t with
        blocks := st.base.blocks, headDomain := st.base.headDomain },
      fastWrite := st.fastWrite ++
        [(s, fastSet p (eraseFG st.fg.F) (actView (clockPre p st t)) s)] } := by
  have hc : (decide (0 ≤ t - 6 * p.Δ) &&
      t == SA.gateTime p.toParams ((t - 6 * p.Δ) / (4 * p.Δ)).toNat) = true := by
    rw [← hs]
    have : 6 * p.Δ ≤ t := by linarith
    simp [this, ← ht]
  have hn : GridCO.savedGenuine (clockPre p st t).base s = none := by
    unfold GridCO.savedGenuine at hnew ⊢
    rw [clockPre_genuine]
    exact hnew
  have hjpre : joinedNow p (clockPre p st t) = true := by
    unfold clockPre joinedNow
    dsimp only
    split_ifs <;> exact hj
  unfold clock
  rw [ite_eq_left hc, ← hs]
  unfold gateStep
  dsimp only
  rw [ite_eq_right (by simp [hn])]
  simp only [hjpre, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [clockPre_fastWrite, clockPre_fg]
  rw [clockPre_eq, onView_onView _ _ (fun v => by
      dsimp only
      hygiene_split <;> hygiene_split <;> hygiene_split <;> rfl)
    (fun v => by
      dsimp only
      hygiene_split <;> hygiene_split <;> hygiene_split <;> rfl)]
  simp only [hj, Bool.and_true]
  subst hs
  rw [show SA.Root.clockFrom p.toParams (eraseFG st.fg.F) (actView st) t = _ from ite_eq_left hc]
  rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [comp D3; M7, DQ5; G7 m3] `clock_eq_saClockFrom_gate` with only
the gate time
and the unsaved label: the other two premises follow from `Δ > 0`. -/
theorem clock_eq_saClockFrom_gate' (p : Params) (st : State p.n) (t : Time) (s : Slot)
    (ht : t = SA.gateTime p.toParams s)
    (hnew : GridCO.savedGenuine st.base s = none)
    (hj : joinedAtTime p st.restartTime t = true) :
    clock p st t = normalizeS { st with
      base := { SA.Root.clockFrom p.toParams (eraseFG st.fg.F) (actView st) t with
        blocks := st.base.blocks, headDomain := st.base.headDomain },
      fastWrite := st.fastWrite ++
        [(s, fastSet p (eraseFG st.fg.F) (actView (clockPre p st t)) s)] } := by
  have hΔ : 0 < p.Δ := p.deltaPos
  have h4 : t - 6 * p.Δ = 4 * p.Δ * (s : Int) := by
    rw [ht]; simp only [SA.gateTime, GridCO.gateTime, GridCO.proposalTime]
    change 4 * p.Δ * (s : Int) + 6 * p.Δ - 6 * p.Δ = _; ring
  refine clock_eq_saClockFrom_gate p st t s ?_ (by rw [h4]; positivity) ht hnew hj
  rw [h4, Int.mul_ediv_cancel_left _ (by positivity)]
  simp

end AvailableChain.FGSA
end
