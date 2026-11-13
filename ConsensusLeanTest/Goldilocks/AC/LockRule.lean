module
public import ConsensusLeanTest.Goldilocks.AC.GradedLocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Base
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart
@[expose] public section

/-! # Witnesses for the ACBase lock statements on the graded lock rule

The seven lock statements of milestone ACBase (`Statements/AC/Base`) instantiated on the
`Goldilocks/AC/GradedLocks` fixtures (one validator, `Δ = 1`, `t_s = 4s`, `k = 6`, `c = 2`; the tree
`U` with genesis `g`, `B1` and its conflicting children `B2`, `B3`; the frames `Φ`, both children
viable, and `Φv`, only `B2` viable). Each theorem meets the statement's premises with concrete
values and proves its conclusion there on the trusted definitions, with a non-vacuity clause (a
lock is live, moved, or a candidate); a rejection shows a premise's role where it is cheap.

* **F.1 (b) `LockExpiry`**: the lock `(B3, 2, fast, 5)` is live at `20` and `23` (slot `5`), the
  same set; rejection: at `24 = t_6` it has expired.
* **A0.4 (c) `LocksMoveBack`**: `liveLocks` and `addLocks` move a lock on the non-viable `B3` back
  to `B1` in `Φv`; `unlock` moves it to `B1` against the vote on `B2` in `Φ`; each keeps slot, fast
  bit and expiry. Rejection: a move from `B1` forward to `B3` is not `MovesBack`.
* **A0.4 (d) `UnlockIdempotent`**: the unlock that moves `(B3, 2, fast, 5)` to `B1` is a fixed
  point the second time.
* **A0.4 (e) `UnlockNoFallback`**: with no equivocator, `Φ.F` has no opponent; rejection: with
  `v0` equivocating (the premise fails) `Φ.F` has half the committee as opponents.
* **A0.4 (a), (b), (f), A0.5** (`LiveLocksChain`, `CandidatesChain`, `LockToTip`, over reachable
  states): the run of two calls from the initial state, `ac_on_block(B1)` at `6` and the slot-`2`
  vote on `B1` at `8`, reaches a state with the optimistic fast lock `(B1, 2, fast, 4)` (expiry
  `2 + 2`, the floor of `fastExpiry`) and the record `B1`. From `8` on: the live lock blocks and
  the FG candidates are within `{B1}`, `B1` is viable, the anchor extends the candidates, and the
  record extends the locks; at `8` each set is `{B1}`. Rejections: unreachable states with live
  locks on both `B2` and `B3` break the chain and the candidates' chain, and one whose record is
  genesis under a lock on `B1` breaks lock to tip.

The `*_applies` theorems apply each statement, assumed, to its witness: the premises are
discharged as the statement states them, and its conclusion there is the one proved. -/

namespace Consensus.Goldilocks.SA.Test.LockRule

open Consensus.Goldilocks.SA.Test.Graded

theorem slot_20 : sp.slot 20 = 5 := by decide
theorem slot_23 : sp.slot 23 = 5 := by decide
theorem slot_24 : sp.slot 24 = 6 := by decide
theorem slot_6 : sp.slot 6 = 1 := by decide
theorem slot_8 : sp.slot 8 = 2 := by decide

/-! ## F.1 (b) `LockExpiry` -/

/-- The fast lock of slot `2` on `B3`, expiry `5`. -/
def lB3 : Lock := ⟨3, 2, true, 5⟩

/-- **`LockExpiry` witness.** At `20` and `23`, both in slot `5`, the live locks are the same set,
the lock on `B3` itself. -/
theorem lockExpiry_witness :
    (sp.ts (5 : Nat) ≤ 20 ∧ (20 : Time) < sp.ts (5 + 1 : Nat) ∧ sp.ts (5 : Nat) ≤ 23 ∧
      (23 : Time) < sp.ts (5 + 1 : Nat)) ∧
    liveLocks sp {lB3} Φ 20 = liveLocks sp {lB3} Φ 23 ∧ liveLocks sp {lB3} Φ 23 = {lB3} := by
  have h20 := liveLocks_Φ (L := {lB3}) (t := 20) (by
    rintro l rfl; exact ⟨by decide, by rw [slot_20]; decide⟩)
  have h23 := liveLocks_Φ (L := {lB3}) (t := 23) (by
    rintro l rfl; exact ⟨by decide, by rw [slot_23]; decide⟩)
  exact ⟨by decide, h20.trans h23.symm, h23⟩

/-- **Rejection: the same slot.** Across the slot boundary `24 = t_6` the live locks differ: the
lock on `B3` has expired. -/
theorem lockExpiry_across_slots : liveLocks sp {lB3} Φ 24 = ∅ ∧
    liveLocks sp {lB3} Φ 23 ≠ liveLocks sp {lB3} Φ 24 := by
  have h24 : liveLocks sp {lB3} Φ 24 = ∅ := by
    ext l'
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨l, rfl, -, -, -, hlive, -⟩
    exact absurd hlive (by rw [Lock.LiveAt, slot_24]; decide)
  refine ⟨h24, ?_⟩
  rw [h24, (lockExpiry_witness).2.2]
  exact Set.singleton_ne_empty lB3

/-! ## A0.4 (c) `LocksMoveBack` -/

/-- **`LocksMoveBack` witness** (`Φv` and `Φ` are well formed). `liveLocks` moves `lB3` back to
`B1` in `Φv`; `addLocks` moves a new lock on `B3` back to `B1` in `Φv`; `unlock` against the vote
on `B2` moves `lB3` to `B1` in `Φ`; each is `MovesBack`, and each changed the block. -/
theorem locksMoveBack_witness :
    FrameOK Φv ∧ FrameOK Φ ∧
    MovesBack sp Φv {lB3} (liveLocks sp {lB3} Φv 16) ∧
    liveLocks sp {lB3} Φv 16 = {⟨1, 2, true, 5⟩} ∧
    MovesBack sp Φv (∅ ∪ {l | ∃ p ∈ ({(3, true, 7)} : Set (Nat × Bool × Nat)),
      l = ⟨p.1, 4, p.2.1, p.2.2⟩}) (addLocks sp ∅ Φv 16 4 {(3, true, 7)}) ∧
    addLocks sp ∅ Φv 16 4 {(3, true, 7)} = {⟨1, 4, true, 7⟩} ∧
    MovesBack sp Φ {lB3} (unlock sp {lB3} Φ 16 3 Vw) ∧
    unlock sp {lB3} Φ 16 3 Vw = {⟨1, 2, true, 5⟩} := by
  refine ⟨frameOK_Φv, frameOK_Φ, ?_, liveLocks_moves_back, ?_, addLocks_moves_back, ?_,
    unlock_keeps⟩
  · rw [show lB3 = ⟨3, 2, true, 5⟩ from rfl, liveLocks_moves_back]
    rintro l' rfl
    exact ⟨lB3, rfl, rfl, rfl, rfl, B3, B3_mem, rfl, B1, B1_mem, rfl, anc_B1_B3⟩
  · rw [addLocks_moves_back]
    rintro l' rfl
    exact ⟨⟨3, 4, true, 7⟩, Or.inr ⟨(3, true, 7), rfl, rfl⟩, rfl, rfl, rfl, B3, B3_mem, rfl,
      B1, B1_mem, rfl, anc_B1_B3⟩
  · rw [show lB3 = ⟨3, 2, true, 5⟩ from rfl, unlock_keeps]
    rintro l' rfl
    exact ⟨lB3, rfl, rfl, rfl, rfl, B3, B3_mem, rfl, B1, B1_mem, rfl, anc_B1_B3⟩

/-- **Rejection: `MovesBack` is not trivial.** Moving a lock from `B1` forward to `B3` is not a
move back. -/
theorem movesBack_forward_rejected : ¬ MovesBack sp Φ {⟨1, 2, true, 5⟩} {lB3} := by
  intro h
  obtain ⟨l, rfl, -, -, -, B, hB, hBr, B', hB', hB'r, hanc⟩ := h lB3 rfl
  rw [eq_of_root hB B1_mem hBr, eq_of_root hB' B3_mem hB'r] at hanc
  simpa [AncRoot, B1, B3] using ancRoot_of_anc hanc

/-! ## A0.4 (d) `UnlockIdempotent` -/

/-- Against the vote on `B2`, a lock on `B1` stays on `B1`: nobody opposes `B1`. -/
theorem unlockTarget_B1 : unlockTarget sp Φ Vw 3 B1 = B1 := by
  have h0 : ∀ {B : Blk sp.n Unit}, Compatible U B2 B → (opponents sp Φ Vw 3 B).ncard = 0 :=
    fun hc => ncard_validators_zero (mem_opponents.not.2 (not_not.2 hc))
  unfold unlockTarget
  rw [deepest_top (D := B1) ?h1 B1_mem ?h2]
  · rfl
  case h1 => exact ⟨B1_mem, Relation.ReflTransGen.refl, by rw [h0 (Or.inr anc_B1_B2)]; decide⟩
  case h2 => exact fun C hC => hC.2.1

/-- `unlock` keeps a slot-`2` lock on `B1` against the vote on `B2`. -/
theorem unlock_B1 : unlock sp {⟨1, 2, true, 5⟩} Φ 16 3 Vw = {⟨1, 2, true, 5⟩} := by
  have hlive : liveLocks sp {⟨1, 2, true, 5⟩} Φ 16 = {⟨1, 2, true, 5⟩} :=
    liveLocks_Φ (by rintro l rfl; exact ⟨by decide, by rw [slot_16]; decide⟩)
  ext l'
  constructor
  · rintro ⟨l, hl, B, hB, hr, rfl⟩
    rw [hlive] at hl
    obtain rfl : l = _ := hl
    rw [eq_of_root hB B1_mem hr, ite_eq_left (by decide), unlockTarget_B1]
    rfl
  · rintro rfl
    refine ⟨⟨1, 2, true, 5⟩, by rw [hlive]; rfl, B1, B1_mem, rfl, ?_⟩
    rw [ite_eq_left (by decide), unlockTarget_B1]
    rfl

/-- **`UnlockIdempotent` witness.** The unlock that moves `lB3` to `B1` (it changes the locks) is
a fixed point the second time. -/
theorem unlockIdempotent_witness :
    FrameOK Φ ∧ unlock sp (unlock sp {lB3} Φ 16 3 Vw) Φ 16 3 Vw = unlock sp {lB3} Φ 16 3 Vw ∧
      unlock sp {lB3} Φ 16 3 Vw ≠ {lB3} := by
  have h1 : unlock sp {lB3} Φ 16 3 Vw = {⟨1, 2, true, 5⟩} := unlock_keeps
  refine ⟨frameOK_Φ, by rw [h1, unlock_B1], ?_⟩
  rw [h1]
  intro h
  have : (⟨1, 2, true, 5⟩ : Lock) ∈ ({lB3} : Set Lock) := h ▸ rfl
  exact absurd this (by simp [lB3])

/-! ## A0.4 (e) `UnlockNoFallback` -/

/-- **`UnlockNoFallback` witness.** In the view of the vote on `B2` nobody equivocates, and
`Φ.F = g` has no opponent. -/
theorem unlockNoFallback_witness :
    FrameOK Φ ∧ 2 * (equivocators Vw.votes).ncard < sp.n ∧
      (opponents sp Φ Vw 3 Φ.F).ncard = 0 ∧ 2 * (opponents sp Φ Vw 3 Φ.F).ncard < sp.n := by
  have he : (equivocators Vw.votes).ncard = 0 :=
    ncard_validators_zero (not_equivocator (fun x hx => hx) v0)
  have ho : (opponents sp Φ Vw 3 Φ.F).ncard = 0 :=
    ncard_validators_zero (mem_opponents.not.2 (not_not.2 (Or.inr (anc_g _ B2_mem))))
  refine ⟨frameOK_Φ, ?_, ho, ?_⟩ <;> [rw [he]; rw [ho]] <;> decide

/-- A second slot-`3` vote of `v0`, on `B3`. -/
def w' : Vote sp.n := ⟨v0, 3, 3⟩

/-- The view in which `v0` equivocates. -/
def Veq : View sp.n := ⟨{w, w'}, {w, w'}⟩

/-- **Rejection: the equivocation premise.** When `v0` equivocates (`2 · 1 < 1` fails), `Φ.F`
has half of the committee as opponents, so the conclusion fails as well. -/
theorem unlockNoFallback_equivocation :
    ¬ 2 * (equivocators Veq.votes).ncard < sp.n ∧
      ¬ 2 * (opponents sp Φ Veq 3 Φ.F).ncard < sp.n := by
  have heq : v0 ∈ equivocators Veq.votes :=
    ⟨w, Or.inl rfl, w', Or.inr rfl, by simp [w, w'], rfl, rfl⟩
  rw [ncard_validators_one heq, ncard_validators_one (Or.inl heq)]
  decide

/-! ## A reachable run with a graded optimistic lock -/

/-- A replay order for restarts. -/
noncomputable abbrev ro : ReplayOrder sp Unit := ReplayOrder.choice sp

/-- The Goldilocks SA with the fixture's parameters. -/
noncomputable abbrev GA : ACInterface sp.toParams Unit := goldilocksSA sp Unit ro

/-- The genesis frame. -/
def Φ₀ : Frm sp.n Unit := ⟨{g}, g, g, {g}⟩

/-- The frame after `B1`: `g` and `B1`, `B1` the viable head. -/
def Φ₁ : Frm sp.n Unit := ⟨insert B1 {g}, g, g, {B1}⟩

theorem tree₁_sub : Φ₁.tree ⊆ U := by
  rintro B (rfl | rfl)
  exacts [B1_mem, g_mem]

theorem frameOK_Φ₀ : FrameOK Φ₀ where
  finite := Set.finite_singleton g
  coherent := ⟨coherent_U.1.mono (by rintro B rfl; exact g_mem),
    fun B hB C hC h => coherent_U.2 B (by rw [hB]; exact g_mem) C (by rw [hC]; exact g_mem) h⟩
  rooted := ⟨rfl, fun C hC => by rw [Set.mem_singleton_iff.mp hC]; exact Relation.ReflTransGen.refl⟩
  fcRoot_mem := rfl
  F_anc_fcRoot := Relation.ReflTransGen.refl
  viableHeads_subset := le_rfl
  fcRoot_anc_viableHeads := fun W hW => by
    rw [Set.mem_singleton_iff.mp hW]; exact Relation.ReflTransGen.refl

theorem B1_mem₁ : B1 ∈ Φ₁.tree := Set.mem_insert _ _
theorem g_mem₁ : g ∈ Φ₁.tree := Set.mem_insert_of_mem _ rfl

/-- `g ⪯ B1` in `Φ₁`. -/
theorem anc₁_g_B1 : Φ₁.Anc g B1 := Relation.ReflTransGen.single ⟨g_mem₁, B1_mem₁, rfl⟩

theorem anc₁_g {B : Blk sp.n Unit} (hB : B ∈ Φ₁.tree) : Φ₁.Anc g B := by
  rcases hB with rfl | rfl
  exacts [anc₁_g_B1, Relation.ReflTransGen.refl]

/-- Every block of `Φ₁` is an ancestor of `B1`. -/
theorem anc₁_B1 {B : Blk sp.n Unit} (hB : B ∈ Φ₁.tree) : Φ₁.Anc B B1 := by
  rcases hB with rfl | rfl
  exacts [Relation.ReflTransGen.refl, anc₁_g_B1]

/-- Ancestry in `Φ₁` is ancestry in `U`. -/
theorem anc_U_of_anc₁ {B C : Blk sp.n Unit} (h : Φ₁.Anc B C) : Anc U B C := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ e ih => exact ih.tail ⟨tree₁_sub e.1, tree₁_sub e.2.1, e.2.2⟩

theorem frameOK_Φ₁ : FrameOK Φ₁ where
  finite := (Set.finite_singleton g).insert B1
  coherent := ⟨coherent_U.1.mono tree₁_sub,
    fun B hB C hC h => coherent_U.2 B (tree₁_sub hB) C (tree₁_sub hC) h⟩
  rooted := ⟨g_mem₁, fun _ hC => anc₁_g hC⟩
  fcRoot_mem := g_mem₁
  F_anc_fcRoot := Relation.ReflTransGen.refl
  viableHeads_subset := by rintro W rfl; exact B1_mem₁
  fcRoot_anc_viableHeads := by rintro W rfl; exact anc₁_g_B1

/-- `B1` is in the viable tree of `Φ₁`. -/
theorem B1_viable₁ : B1 ∈ Φ₁.viableTree Φ₁.tree :=
  ⟨B1_mem₁, anc₁_g_B1, B1, B1_mem₁, rfl, Relation.ReflTransGen.refl⟩

theorem eq_of_root₁ {B : Blk sp.n Unit} (hB : B ∈ Φ₁.tree) (h : B.root = 1) : B = B1 :=
  eq_of_root (tree₁_sub hB) B1_mem h

theorem deepest_top₁ {S : Set (Blk sp.n Unit)} (hD : B1 ∈ S) (hS : S ⊆ Φ₁.tree) :
    deepest Φ₁ S = some B1 := by
  have hex : IsDeepest Φ₁ S B1 := ⟨hD, fun C hC hne =>
    Or.inl (depth_lt_of_anc frameOK_Φ₁ (anc₁_B1 (hS hC)) hne B1_mem₁)⟩
  have hex' : ∃ B, IsDeepest Φ₁ S B := ⟨B1, hex⟩
  unfold deepest
  rw [dite_eq_left hex']
  congr 1
  have hc := hex'.choose_spec
  by_contra hne
  rcases hc.2 B1 hex.1 (Ne.symm hne) with h₁ | ⟨h₁, h₁'⟩ <;>
    rcases hex.2 _ hc.1 hne with h₂ | ⟨h₂, h₂'⟩ <;> omega

/-- The initial frame law and `Φ₀ ⊑_{B1} Φ₁`. -/
theorem frameStep_B1 : FrameStep Φ₀ B1 Φ₁ where
  new := by rintro h; simp [Φ₀, B1, g] at h
  parent_mem := ⟨g, rfl, rfl⟩
  F_anc_F' := Relation.ReflTransGen.refl
  F'_anc_B := Relation.ReflTransGen.single ⟨Set.mem_insert_of_mem _ rfl, Set.mem_insert _ _, rfl⟩
  tree_eq := by
    ext X
    refine ⟨fun hX => ⟨hX, ?_⟩, fun hX => hX.1⟩
    rcases hX with rfl | rfl
    · exact Relation.ReflTransGen.single ⟨Set.mem_insert_of_mem _ rfl, Set.mem_insert _ _, rfl⟩
    · exact Relation.ReflTransGen.refl

/-- The vote of `v0` in slot `2` on `B1`. -/
def w2 : Vote sp.n := ⟨v0, 2, 1⟩

/-- After `ac_on_block(B1)` at `6` (slot `1`, after `t_1 + Δ`: no vote, and no optimistic check
from `t_1 + 2Δ`). -/
noncomputable def S1 : SAState sp.n := ((GA).step v0 (GA).initial Φ₁ 6 (.block B1)).1

/-- After the slot-`2` vote on `B1` at `8 = t_2`. -/
noncomputable def S2 : SAState sp.n := ((GA).step v0 S1 Φ₁ 8 (.message w2)).1

theorem reachable_init : (GA).ReachableAt v0 U (GA).initial Φ₀ 0 :=
  ACInterface.ReachableAtFrom.init (A := GA) (self := v0) (U := U) Φ₀ ⟨rfl, rfl, rfl, rfl, rfl⟩
    ⟨frameOK_Φ₀, fun B hB => by rw [Set.mem_singleton_iff.mp hB]; exact g_mem⟩

/-- `ac_on_block(B1)` at `6` obeys the call law: `Φ₀ ⊑_{B1} Φ₁`, a valid payload, slot `1`. -/
theorem callOK_B1 : (GA).CallOK U Φ₀ 6 (.block B1) Φ₁ :=
  ⟨⟨frameOK_Φ₁, tree₁_sub⟩, frameStep_B1,
    ⟨fun v hv => by simp [blockVotes, B1] at hv, fun v hv => by simp [blockSupport, B1] at hv⟩,
    by decide⟩

/-- The vote message at `8` obeys the call law (same frame). -/
theorem callOK_w2 : (GA).CallOK U Φ₁ 8 (.message w2) Φ₁ := ⟨⟨frameOK_Φ₁, tree₁_sub⟩, rfl, trivial⟩

theorem reachable_S1 : (GA).ReachableAt v0 U S1 Φ₁ 6 := by
  unfold S1
  exact ACInterface.ReachableAtFrom.step (A := GA) (self := v0) (U := U) (s := (GA).initial)
    (Φ := Φ₀) (Φ' := Φ₁) (t := 0) (t' := 6) (.block B1) reachable_init (by decide) callOK_B1

/-- **The run is reachable**, inside the coherent `U`, with frame `Φ₁` at time `8`. -/
theorem reachable_S2 : (GA).ReachableAt v0 U S2 Φ₁ 8 := by
  unfold S2
  exact ACInterface.ReachableAtFrom.step (A := GA) (self := v0) (U := U) (s := S1)
    (Φ := Φ₁) (Φ' := Φ₁) (t := 6) (t' := 8) (.message w2) reachable_S1 (by decide) callOK_w2

/-- The first call only stamps `B1`. -/
theorem S1_eq : S1 = blockReceipt sp (SAState.initial 0) 6 B1 := by
  change (acOnBlock sp v0 (SAState.initial 0) Φ₁ 6 B1).1 = _
  unfold acOnBlock optimisticConfirmation optimisticSelect
  dsimp only
  rw [slot_6, ite_eq_left (Or.inr (Or.inr (by decide)))]
  dsimp only
  unfold tryVote
  dsimp only
  rw [slot_6, ite_eq_left (Or.inr (Or.inr (by decide)))]

theorem S1_locks : S1.locks = ∅ := by rw [S1_eq]; rfl
theorem S1_pool (s : Nat) : S1.pool s = [] := by rw [S1_eq]; rfl
theorem S1_restart : S1.restartTime = ⊥ := by rw [S1_eq]; rfl
theorem S1_latest : S1.latestConfirmed = 0 := by rw [S1_eq]; rfl
theorem S1_votedSlot : S1.votedSlot = -1 := by rw [S1_eq]; rfl

/-- The admission of the slot-`2` vote. -/
noncomputable def A2 : SAState sp.n := admitVote sp S1 8 w2

theorem A2_eq : A2 = { S1 with
    pool := Function.update S1.pool 2 (S1.pool 2 ++ [w2])
    voteStamp := Function.update S1.voteStamp w2 (ETime.of 8) } := by
  unfold A2 admitVote
  rw [ite_eq_right (by rw [slot_8, S1_pool]; simp [w2]),
    ite_eq_right (by rw [S1_pool]; simp)]
  rfl

theorem A2_pool : A2.pool 2 = [w2] := by
  rw [A2_eq]
  change Function.update S1.pool 2 _ 2 = _
  rw [Function.update_self, S1_pool]
  rfl

/-- `fastExpiry` with no lock: the floor `2 + 2`. -/
theorem fastExpiry_A2 : fastExpiry sp ∅ Φ₁ 8 2 = 4 := by
  unfold fastExpiry
  dsimp only
  rw [ite_eq_right]
  · decide
  rintro ⟨e, l, ⟨l0, hl0, -⟩, -⟩
  exact hl0

/-- The optimistic lock of slot `2` on `B1`, with the floor expiry `4`. -/
def lockA : Lock := ⟨1, 2, true, 4⟩

/-- Every block of `Φ₁` is its own viable ancestor. -/
theorem viableAncestor_Φ₁ {B : Blk sp.n Unit} (hB : B ∈ Φ₁.tree) : Φ₁.viableAncestor B = B := by
  refine viableAncestor_self frameOK_Φ₁ hB ?_
  rcases hB with rfl | rfl
  exacts [Or.inl B1_viable₁, Or.inr Relation.ReflTransGen.refl]

/-- The live locks of `{lockA}` at `t`: itself through slot `4`. -/
theorem mem_liveLocks_lockA {t : Time} {l' : Lock} :
    l' ∈ liveLocks sp {lockA} Φ₁ t ↔ l' = lockA ∧ sp.slot t ≤ 4 := by
  constructor
  · rintro ⟨l, rfl, B, hB, hr, hlive, rfl⟩
    rw [eq_of_root₁ hB hr, viableAncestor_Φ₁ B1_mem₁]
    exact ⟨rfl, hlive⟩
  · rintro ⟨rfl, hlive⟩
    exact ⟨lockA, rfl, B1, B1_mem₁, rfl, hlive, by rw [viableAncestor_Φ₁ B1_mem₁]; rfl⟩

theorem updateLatestConfirmed_locks (A : SAState sp.n) (Ψ : Frm sp.n Unit) (C : Blk sp.n Unit) :
    (updateLatestConfirmed sp A Ψ C).locks = A.locks := by
  unfold updateLatestConfirmed
  split_ifs <;> rfl

/-- At `8 < t_2 + Δ` there is no slot-`2` proposal, so `try_vote` waits. -/
theorem tryVote_8 (A : SAState sp.n) : tryVote sp v0 A Φ₁ 8 = (A, []) := by
  have hr : ¬ voteReady sp Φ₁ 2 := by
    rintro ⟨B, hB, hs, -⟩
    rcases hB with rfl | rfl <;> simp [B1, g] at hs
  unfold tryVote
  dsimp only
  rw [slot_8]
  split_ifs with h1 h2
  all_goals first | rfl | exact absurd ⟨by decide, Or.inr hr⟩ h2

theorem S2_eq : S2 = optimisticConfirmation sp A2 Φ₁ 8 := by
  change (acOnMessage sp v0 S1 Φ₁ 8 w2).1 = _
  unfold acOnMessage
  rw [tryVote_8]
  rfl

theorem A2_locks : A2.locks = ∅ := by rw [A2_eq]; exact S1_locks

/-- The optimistic check at `8` selects `B1`: the vote of the whole committee (one validator)
extends it, and no lock is live. -/
theorem optimisticSelect_A2 : optimisticSelect sp A2 Φ₁ 8 = some B1 := by
  have hj : joined sp A2 8 := by
    rw [joined, A2_eq]; change S1.restartTime ≤ _; rw [S1_restart]; exact bot_le
  unfold optimisticSelect
  dsimp only
  rw [slot_8, ite_eq_right (by
    rintro (h | h | h)
    · exact h hj
    · exact absurd h (by decide)
    · exact absurd h (by decide))]
  refine deepest_top₁ ⟨B1_mem₁, ?_, ?_⟩ fun B hB => hB.1
  · rw [ncard_validators_one (S := optimisticVoters sp A2 Φ₁ 2 B1)
      ⟨w2, by rw [A2_pool]; exact List.mem_singleton.2 rfl, rfl, B1, B1_mem₁, rfl,
        Relation.ReflTransGen.refl⟩]
    decide
  · rintro ⟨B, ⟨-, l, hl, -⟩, -⟩
    rw [A2_locks] at hl
    obtain ⟨l0, hl0, -⟩ := hl
    exact hl0

/-- **The second call writes the graded optimistic lock** on `B1`: slot `2`, expiry `2 + 2 = 4`
(the floor of `fastExpiry`, no earlier fast lock). -/
theorem S2_locks : S2.locks = {lockA} := by
  rw [S2_eq]
  unfold optimisticConfirmation
  rw [optimisticSelect_A2]
  dsimp only
  rw [updateLatestConfirmed_locks]
  change addLocks sp A2.locks Φ₁ 8 (sp.slot 8) {(B1.root, true,
    fastExpiry sp A2.locks Φ₁ 8 (sp.slot 8))} = _
  rw [A2_locks, slot_8, fastExpiry_A2]
  unfold addLocks
  rw [show (∅ ∪ {l | ∃ p ∈ ({(B1.root, true, 4)} : Set (Nat × Bool × Nat)),
      l = ⟨p.1, 2, p.2.1, p.2.2⟩}) = ({lockA} : Set Lock) by ext; simp [lockA, B1]]
  ext l'
  rw [mem_liveLocks_lockA, slot_8]
  simp

/-- **The record moves to `B1`.** -/
theorem S2_latest : S2.latestConfirmed = 1 := by
  rw [S2_eq]
  unfold optimisticConfirmation
  rw [optimisticSelect_A2]
  dsimp only
  unfold updateLatestConfirmed
  rw [ite_eq_right]
  · rfl
  rintro ⟨R, hR, hr, hanc⟩
  change R.root = A2.latestConfirmed at hr
  rw [A2_eq] at hr
  change R.root = S1.latestConfirmed at hr
  rw [S1_latest] at hr
  rw [eq_of_root (tree₁_sub hR) g_mem hr] at hanc
  simpa [AncRoot, B1, g] using ancRoot_of_anc (anc_U_of_anc₁ hanc)

/-- The live lock blocks of the run's state at `t`: within `{B1}`, and `B1` through slot `4`. -/
theorem mem_liveLockBlocks_S2 {t : Time} {B : Blk sp.n Unit} :
    B ∈ liveLockBlocks sp S2.locks Φ₁ t ↔ B = B1 ∧ sp.slot t ≤ 4 := by
  rw [S2_locks]
  constructor
  · rintro ⟨hB, l, hl, hr⟩
    obtain ⟨rfl, hlive⟩ := mem_liveLocks_lockA.1 hl
    exact ⟨eq_of_root₁ hB hr.symm, hlive⟩
  · rintro ⟨rfl, hlive⟩
    exact ⟨B1_mem₁, lockA, mem_liveLocks_lockA.2 ⟨rfl, hlive⟩, rfl⟩

/-! ## A0.4 (a), (b) `LiveLocksChain` -/

/-- **`LiveLocksChain` witness.** At the reachable state `S2` (frame `Φ₁`, time `8`) and every
later time, the live lock blocks lie on one chain and are viable; at `8` they are `{B1}`. -/
theorem liveLocksChain_witness :
    Coherent U ∧ (GA).ReachableAt v0 U S2 Φ₁ 8 ∧
    (∀ t, 8 ≤ t →
      (∀ B ∈ liveLockBlocks sp S2.locks Φ₁ t, ∀ C ∈ liveLockBlocks sp S2.locks Φ₁ t,
        Compatible Φ₁.tree B C) ∧
      ∀ B ∈ liveLockBlocks sp S2.locks Φ₁ t, B ∈ Φ₁.viableTree Φ₁.tree ∨ Φ₁.Anc B Φ₁.fcRoot) ∧
    liveLockBlocks sp S2.locks Φ₁ 8 = {B1} := by
  refine ⟨coherent_U, reachable_S2, fun t _ => ⟨fun B hB C hC => ?_, fun B hB => ?_⟩, ?_⟩
  · rw [(mem_liveLockBlocks_S2.1 hB).1, (mem_liveLockBlocks_S2.1 hC).1]
    exact Or.inl Relation.ReflTransGen.refl
  · rw [(mem_liveLockBlocks_S2.1 hB).1]
    exact Or.inl B1_viable₁
  · ext B
    rw [mem_liveLockBlocks_S2, slot_8]
    simp

/-- An unreachable state with live fast locks on both conflicting children `B2` and `B3`. -/
def Sbad : SAState sp.n := { SAState.initial 0 with locks := {⟨2, 3, true, 5⟩, ⟨3, 3, true, 5⟩} }

theorem liveLocks_Sbad : liveLocks sp Sbad.locks Φ 16 = Sbad.locks :=
  liveLocks_Φ (by rintro l (rfl | rfl) <;> exact ⟨by decide, by rw [slot_16]; decide⟩)

/-- **Rejection: reachability.** At `Sbad` the live lock blocks `B2` and `B3` conflict, so the
chain conclusion fails: the statement's reachability premise carries it. -/
theorem liveLocksChain_unreachable :
    ¬ ∀ B ∈ liveLockBlocks sp Sbad.locks Φ 16, ∀ C ∈ liveLockBlocks sp Sbad.locks Φ 16,
      Compatible Φ.tree B C := by
  intro h
  refine not_compatible_B2_B3 (h B2 ⟨B2_mem, ⟨2, 3, true, 5⟩, ?_, rfl⟩
    B3 ⟨B3_mem, ⟨3, 3, true, 5⟩, ?_, rfl⟩)
  · rw [liveLocks_Sbad]; exact Or.inl rfl
  · rw [liveLocks_Sbad]; exact Or.inr rfl

/-! ## A0.4 (f) `CandidatesChain` -/

/-- The anchor of `S2` while its lock is live: the lock block `B1`. -/
theorem getAnchor_S2 {t : Time} (ht : sp.slot t ≤ 4) : getAnchor sp S2 Φ₁ t = B1 := by
  unfold getAnchor
  rw [deepest_top₁ (Or.inl (mem_liveLockBlocks_S2.2 ⟨rfl, ht⟩))]
  · rfl
  rintro B (hB | rfl)
  · rw [(mem_liveLockBlocks_S2.1 hB).1]; exact B1_mem₁
  · exact g_mem₁

/-- The FG candidates of `S2` at `t`: `B1` while its fast lock is live and recent. -/
theorem mem_candidates_S2 {t : Time} {B : Blk sp.n Unit} :
    B ∈ toFGCandidates sp S2 Φ₁ t ↔ B = B1 ∧ sp.slot t ≤ 4 := by
  rw [toFGCandidates, Set.mem_ofPred_eq, S2_locks]
  constructor
  · rintro ⟨hB, l, hl, hr, -, -⟩
    obtain ⟨rfl, hlive⟩ := mem_liveLocks_lockA.1 hl
    exact ⟨eq_of_root₁ hB.1 hr.symm, hlive⟩
  · rintro ⟨rfl, hlive⟩
    exact ⟨B1_viable₁, lockA, mem_liveLocks_lockA.2 ⟨rfl, hlive⟩, rfl, rfl,
      by change sp.slot t ≤ 2 + 2; omega⟩

/-- **`CandidatesChain` witness.** At the reachable state `S2` and every later time, the
candidates of `ac_to_fg` lie on one chain and the anchor extends them; at `8` the candidate is
`B1` and the anchor is `B1`. -/
theorem candidatesChain_witness :
    Coherent U ∧ (GA).ReachableAt v0 U S2 Φ₁ 8 ∧
    (∀ t, 8 ≤ t →
      (∀ B ∈ toFGCandidates sp S2 Φ₁ t, ∀ C ∈ toFGCandidates sp S2 Φ₁ t,
        Compatible Φ₁.tree B C) ∧
      ∀ B ∈ toFGCandidates sp S2 Φ₁ t, Φ₁.Anc B (getAnchor sp S2 Φ₁ t)) ∧
    toFGCandidates sp S2 Φ₁ 8 = {B1} ∧ getAnchor sp S2 Φ₁ 8 = B1 := by
  refine ⟨coherent_U, reachable_S2, fun t _ => ⟨fun B hB C hC => ?_, fun B hB => ?_⟩, ?_,
    getAnchor_S2 (by rw [slot_8]; decide)⟩
  · rw [(mem_candidates_S2.1 hB).1, (mem_candidates_S2.1 hC).1]
    exact Or.inl Relation.ReflTransGen.refl
  · obtain ⟨rfl, ht⟩ := mem_candidates_S2.1 hB
    rw [getAnchor_S2 ht]
    exact Relation.ReflTransGen.refl
  · ext B
    rw [mem_candidates_S2, slot_8]
    simp

/-- **Rejection: reachability.** At `Sbad` both `B2` and `B3` are candidates (viable, under live
recent fast locks), and they conflict. -/
theorem candidatesChain_unreachable :
    ¬ ∀ B ∈ toFGCandidates sp Sbad Φ 16, ∀ C ∈ toFGCandidates sp Sbad Φ 16,
      Compatible Φ.tree B C := by
  intro h
  refine not_compatible_B2_B3 (h B2 ⟨⟨B2_mem, anc_g _ B2_mem, B2, B2_mem, Or.inl rfl,
    Relation.ReflTransGen.refl⟩, ⟨2, 3, true, 5⟩, ?_, rfl, rfl, by rw [slot_16]; decide⟩
    B3 ⟨⟨B3_mem, anc_g _ B3_mem, B3, B3_mem, Or.inr rfl, Relation.ReflTransGen.refl⟩,
      ⟨3, 3, true, 5⟩, ?_, rfl, rfl, by rw [slot_16]; decide⟩)
  · rw [liveLocks_Sbad]; exact Or.inl rfl
  · rw [liveLocks_Sbad]; exact Or.inr rfl

/-! ## A0.5 `LockToTip` -/

theorem lookup₁_1 : lookup Φ₁ 1 = some B1 := by
  cases h : lookup Φ₁ 1 with
  | none => exact absurd ⟨B1, B1_mem₁, rfl⟩ (lookup_eq_none h)
  | some B =>
    obtain ⟨hB, hr⟩ := lookup_eq_some h
    exact congrArg some (eq_of_root₁ hB hr)

/-- **`LockToTip` witness.** At the reachable state `S2` and every later time, every live lock
block is an ancestor of the effective record, `B1`; at `8` the lock on `B1` is live. -/
theorem lockToTip_witness :
    Coherent U ∧ (GA).ReachableAt v0 U S2 Φ₁ 8 ∧
    (∀ t, 8 ≤ t → ∀ B ∈ liveLockBlocks sp S2.locks Φ₁ t,
      Φ₁.Anc B ((lookup Φ₁ S2.latestConfirmed).getD Φ₁.F)) ∧
    (lookup Φ₁ S2.latestConfirmed).getD Φ₁.F = B1 ∧ B1 ∈ liveLockBlocks sp S2.locks Φ₁ 8 := by
  have hrec : (lookup Φ₁ S2.latestConfirmed).getD Φ₁.F = B1 := by rw [S2_latest, lookup₁_1]; rfl
  refine ⟨coherent_U, reachable_S2, fun t _ B hB => ?_, hrec,
    mem_liveLockBlocks_S2.2 ⟨rfl, by rw [slot_8]; decide⟩⟩
  rw [hrec, (mem_liveLockBlocks_S2.1 hB).1]
  exact Relation.ReflTransGen.refl

/-- **Rejection: reachability.** An unreachable state with the lock on `B1` but the record at
genesis breaks lock to tip. -/
theorem lockToTip_unreachable :
    ¬ ∀ B ∈ liveLockBlocks sp ({ S2 with latestConfirmed := 0 } : SAState sp.n).locks Φ₁ 8,
      Φ₁.Anc B ((lookup Φ₁ 0).getD Φ₁.F) := by
  intro h
  have := h B1 (mem_liveLockBlocks_S2.2 ⟨rfl, by rw [slot_8]; decide⟩)
  have hg : (lookup Φ₁ 0).getD Φ₁.F = g := by
    cases hl : lookup Φ₁ 0 with
    | none => rfl
    | some B =>
      obtain ⟨hB, hr⟩ := lookup_eq_some hl
      exact eq_of_root (tree₁_sub hB) g_mem hr
  rw [hg] at this
  simpa [AncRoot, B1, g] using ancRoot_of_anc (anc_U_of_anc₁ this)

/-! ## The statements reach the witnesses

Each statement, assumed, applies to its witness with the premises above, and its conclusion there
is the one the witness proves (so the witnesses are instances of the statements as written). -/

theorem lockExpiry_applies (h : LockExpiry sp) :
    liveLocks sp {lB3} Φ 20 = liveLocks sp {lB3} Φ 23 :=
  h Unit {lB3} Φ 5 20 23 (by decide) (by decide) (by decide) (by decide)

theorem locksMoveBack_applies (h : LocksMoveBack sp) :
    MovesBack sp Φv {lB3} (liveLocks sp {lB3} Φv 16) ∧
    MovesBack sp Φv (∅ ∪ {l | ∃ p ∈ ({(3, true, 7)} : Set (Nat × Bool × Nat)),
      l = ⟨p.1, 4, p.2.1, p.2.2⟩}) (addLocks sp ∅ Φv 16 4 {(3, true, 7)}) ∧
    MovesBack sp Φ {lB3} (unlock sp {lB3} Φ 16 3 Vw) :=
  ⟨(h Unit Φv {lB3} 16 frameOK_Φv).1, (h Unit Φv ∅ 16 frameOK_Φv).2.1 4 {(3, true, 7)},
    (h Unit Φ {lB3} 16 frameOK_Φ).2.2 3 Vw⟩

theorem unlockIdempotent_applies (h : UnlockIdempotent sp) :
    unlock sp (unlock sp {lB3} Φ 16 3 Vw) Φ 16 3 Vw = unlock sp {lB3} Φ 16 3 Vw :=
  h Unit Φ {lB3} 16 3 Vw frameOK_Φ

theorem unlockNoFallback_applies (h : UnlockNoFallback sp) :
    2 * (opponents sp Φ Vw 3 Φ.F).ncard < sp.n :=
  h Unit Φ Vw 3 frameOK_Φ unlockNoFallback_witness.2.1

theorem liveLocksChain_applies (h : LiveLocksChain sp) : ∀ t, 8 ≤ t →
    (∀ B ∈ liveLockBlocks sp S2.locks Φ₁ t, ∀ C ∈ liveLockBlocks sp S2.locks Φ₁ t,
      Compatible Φ₁.tree B C) ∧
    ∀ B ∈ liveLockBlocks sp S2.locks Φ₁ t, B ∈ Φ₁.viableTree Φ₁.tree ∨ Φ₁.Anc B Φ₁.fcRoot :=
  fun t _ => h Unit ro v0 U coherent_U S2 Φ₁ 8 reachable_S2 t

theorem candidatesChain_applies (h : CandidatesChain sp) : ∀ t, 8 ≤ t →
    (∀ B ∈ toFGCandidates sp S2 Φ₁ t, ∀ C ∈ toFGCandidates sp S2 Φ₁ t,
      Compatible Φ₁.tree B C) ∧
    ∀ B ∈ toFGCandidates sp S2 Φ₁ t, Φ₁.Anc B (getAnchor sp S2 Φ₁ t) :=
  fun t _ => h Unit ro v0 U coherent_U S2 Φ₁ 8 reachable_S2 t

theorem lockToTip_applies (h : LockToTip sp) : ∀ t, 8 ≤ t →
    ∀ B ∈ liveLockBlocks sp S2.locks Φ₁ t, Φ₁.Anc B ((lookup Φ₁ S2.latestConfirmed).getD Φ₁.F) :=
  fun t _ => h Unit ro v0 U coherent_U S2 Φ₁ 8 reachable_S2 t

end Consensus.Goldilocks.SA.Test.LockRule
