module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
public import Mathlib.Data.Set.Card
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.State
@[expose] public section

/-! # Graded fast locks: the expiry rules on concrete values

Every other Goldilocks witness runs at `k = c = 2`, where the floor `s + 2` and the cap `s + k`
of `fastExpiry` coincide, so the grading, the cap and the per-slot fast deadline are never
exercised there. These tests compute the trusted definitions (`Spec/SA/Locks`,
`Spec/SA/Confirmation`) at `k = 6`, `c = 2`, with one validator, `Δ = 1` and `t_s = 4s`; they use
no lemma beyond `Lemmas/AC/Basic`. Each value is chosen so that a plausible wrong rule gives a
different number.

The tree `U` has genesis `g` (root `0`), `B1` (root `1`, slot `1`) on `g`, and two children of
`B1`: `B2` (root `2`) and `B3` (root `3`), both of slot `2`. In `Φ` both children are viable
heads; in `Φv` only `B2` is, so a lock on `B3` moves back to `B1` there.

* `fastExpiry`: `s + 2` with no fast lock of an earlier slot; `e + c` between the bounds
  (grading); the cap `s + k`; the latest of several expiries; and a same-slot fast lock, an
  expired one or a slow one does not raise it (rejection tests).
* The expiry is kept: by `liveLocks` (also when it moves a lock back), `addLocks` and `unlock`
  (also when it moves a lock to its unlock target).
* `updateConfirmation` of slot `3` at `t = 18`: unvetoed, the fast lock goes to the deepest
  fast block `D` with `fastExpiry`, and the slow lock independently to the deepest slow block
  `X` with `s + k`; vetoed by a live lock on `B3`, the record stays but the locks are still
  written on the part of the path the lock does not veto. -/

namespace Consensus.Goldilocks.SA.Test.Graded

/-- The shared parameters: one validator, `Δ = 1`, `t_s = 4s`, genesis root `0`. -/
abbrev P : Params where
  n := 1
  hn := le_rfl
  Δ := 1
  hΔ := one_pos
  slotTime := fun s => 4 * (s : Int)
  slotTime_zero := by simp
  slotTime_strictMono := fun a b h => by change 4 * (a : Int) < 4 * (b : Int); omega
  slotTime_public := fun _ => one_dvd _
  genesisRoot := 0
  δt := 0

/-- The SA parameters: `P` with `k = 6`, `c = 2`. -/
abbrev sp : SAParams where
  toParams := P
  slotTime_eq := fun s => by change 4 * (s : Int) = 4 * 1 * s; omega
  k := 6
  two_le_k := by decide
  c := 2
  two_le_c := le_rfl

/-- The validator. -/
abbrev v0 : Fin sp.n := ⟨0, Nat.one_pos⟩

/-- Every validator is `v0`. -/
theorem eq_v0 (i : Fin sp.n) : i = v0 := Subsingleton.elim _ _

/-- A set of validators has one element when it holds `v0`, none otherwise. -/
theorem ncard_validators_one {S : Set (Fin sp.n)} (h : v0 ∈ S) : S.ncard = 1 := by
  rw [show S = {v0} from Set.eq_singleton_iff_unique_mem.2 ⟨h, fun i _ => eq_v0 i⟩]
  exact Set.ncard_singleton v0

/-- A set of validators without `v0` is empty. -/
theorem ncard_validators_zero {S : Set (Fin sp.n)} (h : v0 ∉ S) : S.ncard = 0 := by
  rw [show S = ∅ from Set.eq_empty_of_forall_notMem fun i hi => h (eq_v0 i ▸ hi)]
  exact Set.ncard_empty _

/-- Genesis. -/
def g : Blk sp.n Unit := ⟨0, none, 0, v0, 0, (), ([], [])⟩
/-- The slot-`1` block on genesis. -/
def B1 : Blk sp.n Unit := ⟨1, some 0, 1, v0, 0, (), ([], [])⟩
/-- A slot-`2` child of `B1`. -/
def B2 : Blk sp.n Unit := ⟨2, some 1, 2, v0, 0, (), ([], [])⟩
/-- The other slot-`2` child of `B1`, conflicting with `B2`. -/
def B3 : Blk sp.n Unit := ⟨3, some 1, 2, v0, 0, (), ([], [])⟩

/-- The tree. -/
def U : Set (Blk sp.n Unit) := {g, B1, B2, B3}

/-- Ancestry in `U`, by roots. -/
def AncRoot (a b : Nat) : Prop := a = b ∨ a = 0 ∨ (a = 1 ∧ (b = 2 ∨ b = 3))


theorem g_mem : g ∈ U := Or.inl rfl
theorem B1_mem : B1 ∈ U := Or.inr (Or.inl rfl)
theorem B2_mem : B2 ∈ U := Or.inr (Or.inr (Or.inl rfl))
theorem B3_mem : B3 ∈ U := Or.inr (Or.inr (Or.inr rfl))

/-- A block of `U` is determined by its root. -/
theorem eq_of_root {B C : Blk sp.n Unit} (hB : B ∈ U) (hC : C ∈ U) (h : B.root = C.root) :
    B = C := by
  rcases hB with rfl | rfl | rfl | rfl <;> rcases hC with rfl | rfl | rfl | rfl <;>
    first | rfl | simp [g, B1, B2, B3] at h

/-- Ancestry inside `U` is `AncRoot` on the roots. -/
theorem ancRoot_of_anc {B C : Blk sp.n Unit} (h : Anc U B C) : AncRoot B.root C.root := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail c d _ e ih =>
    obtain ⟨-, hd, hp⟩ := e
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp only [g, B1, B2, B3, Option.some.injEq, reduceCtorEq] at hp <;>
      simp only [AncRoot, B1, B2, B3, true_or, or_true, and_true] at ih ⊢ <;> omega

theorem anc_g (B : Blk sp.n Unit) (hB : B ∈ U) : Anc U g B := by
  have h1 : Anc U g B1 := Relation.ReflTransGen.single ⟨g_mem, B1_mem, rfl⟩
  rcases hB with rfl | rfl | rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact h1
  · exact h1.tail ⟨B1_mem, B2_mem, rfl⟩
  · exact h1.tail ⟨B1_mem, B3_mem, rfl⟩

theorem anc_B1_B2 : Anc U B1 B2 := Relation.ReflTransGen.single ⟨B1_mem, B2_mem, rfl⟩
theorem anc_B1_B3 : Anc U B1 B3 := Relation.ReflTransGen.single ⟨B1_mem, B3_mem, rfl⟩

/-- `B2` and `B3` conflict. -/
theorem not_compatible_B2_B3 : ¬ Compatible U B2 B3 := by
  rintro (h | h) <;> simpa [AncRoot, B2, B3] using ancRoot_of_anc h

theorem coherent_U : Coherent U := by
  refine ⟨fun B hB C hC h => eq_of_root hB hC h, fun B hB C hC h => ?_⟩
  rcases hB with rfl | rfl | rfl | rfl <;> rcases hC with rfl | rfl | rfl | rfl <;>
    simp [g, B1, B2, B3] at h ⊢

/-- The frame with both children of `B1` viable. -/
def Φ : Frm sp.n Unit := ⟨U, g, g, {B2, B3}⟩

/-- The frame with only `B2` viable. -/
def Φv : Frm sp.n Unit := ⟨U, g, g, {B2}⟩

theorem finite_U : U.Finite := by
  simp only [U]
  exact ((((Set.finite_singleton B3).insert B2).insert B1).insert g)

theorem frameOK_Φ : FrameOK Φ where
  finite := finite_U
  coherent := coherent_U
  rooted := ⟨g_mem, anc_g⟩
  fcRoot_mem := g_mem
  F_anc_fcRoot := Relation.ReflTransGen.refl
  viableHeads_subset := by rintro W (rfl | rfl); exacts [B2_mem, B3_mem]
  fcRoot_anc_viableHeads := by rintro W (rfl | rfl); exacts [anc_g _ B2_mem, anc_g _ B3_mem]

theorem frameOK_Φv : FrameOK Φv where
  finite := finite_U
  coherent := coherent_U
  rooted := ⟨g_mem, anc_g⟩
  fcRoot_mem := g_mem
  F_anc_fcRoot := Relation.ReflTransGen.refl
  viableHeads_subset := by rintro W rfl; exact B2_mem
  fcRoot_anc_viableHeads := by rintro W rfl; exact anc_g _ B2_mem

/-- In `Φ` every block is its own viable ancestor. -/
theorem viableAncestor_Φ {B : Blk sp.n Unit} (hB : B ∈ U) : Φ.viableAncestor B = B := by
  refine viableAncestor_self frameOK_Φ hB ?_
  rcases hB with rfl | rfl | rfl | rfl
  · exact Or.inr Relation.ReflTransGen.refl
  · exact Or.inl ⟨B1_mem, anc_g _ B1_mem, B2, B2_mem, Or.inl rfl, anc_B1_B2⟩
  · exact Or.inl ⟨B2_mem, anc_g _ B2_mem, B2, B2_mem, Or.inl rfl, Relation.ReflTransGen.refl⟩
  · exact Or.inl ⟨B3_mem, anc_g _ B3_mem, B3, B3_mem, Or.inr rfl, Relation.ReflTransGen.refl⟩

/-- In `Φv`, `B3` (not viable) moves back to `B1`. -/
theorem viableAncestor_Φv_B3 : Φv.viableAncestor B3 = B1 := by
  obtain ⟨hA, hc, hmax⟩ := viableAncestor_spec frameOK_Φv B3_mem
  have hB1 : Φv.Anc B1 (Φv.viableAncestor B3) :=
    hmax B1 anc_B1_B3 (Or.inr ⟨B1_mem, anc_g _ B1_mem, B2, B2_mem, rfl, anc_B1_B2⟩)
  have h1 := ancRoot_of_anc hB1
  have h3 := ancRoot_of_anc hA
  obtain h | h | h | h : _ = g ∨ _ = B1 ∨ _ = B2 ∨ _ = B3 := mem_of_anc hA B3_mem
  · rw [h] at h1; simp [AncRoot, B1, g] at h1
  · exact h
  · rw [h] at h3; simp [AncRoot, B2, B3] at h3
  · exfalso
    rw [h] at hc
    rcases hc with hc | ⟨-, -, W, -, rfl, hW⟩
    · simpa [AncRoot, B3, g, Φv] using ancRoot_of_anc hc
    · simpa [AncRoot, B2, B3] using ancRoot_of_anc hW

/-- The block of a root at most `3`. -/
theorem exists_root {r : Nat} (hr : r ≤ 3) : ∃ B ∈ U, B.root = r := by
  obtain rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  exacts [⟨g, g_mem, rfl⟩, ⟨B1, B1_mem, rfl⟩, ⟨B2, B2_mem, rfl⟩, ⟨B3, B3_mem, rfl⟩]

theorem deepest_eq_of_isDeepest {S : Set (Blk sp.n Unit)} {D : Blk sp.n Unit}
    (h : IsDeepest Φ S D) : deepest Φ S = some D := by
  have hex : ∃ B, IsDeepest Φ S B := ⟨D, h⟩
  unfold deepest
  rw [dite_eq_left hex]
  congr 1
  have hc := hex.choose_spec
  by_contra hne
  rcases hc.2 D h.1 (Ne.symm hne) with h₁ | ⟨h₁, h₁'⟩ <;>
    rcases h.2 _ hc.1 hne with h₂ | ⟨h₂, h₂'⟩ <;> omega

/-- The deepest block of a set whose blocks are all ancestors of its member `D` is `D`. -/
theorem deepest_top {S : Set (Blk sp.n Unit)} {D : Blk sp.n Unit} (hD : D ∈ S) (hDU : D ∈ U)
    (hS : ∀ C ∈ S, Anc U C D) : deepest Φ S = some D :=
  deepest_eq_of_isDeepest ⟨hD, fun C hC hne => Or.inl (depth_lt_of_anc frameOK_Φ (hS C hC) hne hDU)⟩

/-- In `Φ`, live locks on blocks of the tree stay as they are. -/
theorem liveLocks_Φ {L : Set Lock} {t : Time} (hL : ∀ l ∈ L, l.block ≤ 3 ∧ sp.slot t ≤ l.expiry) :
    liveLocks sp L Φ t = L := by
  ext l'
  constructor
  · rintro ⟨l, hl, B, hB, hr, -, rfl⟩
    rw [viableAncestor_Φ hB, hr]
    exact hl
  · intro hl
    obtain ⟨B, hB, hr⟩ := exists_root (hL l' hl).1
    exact ⟨l', hl, B, hB, hr, (hL l' hl).2, by rw [viableAncestor_Φ hB, hr]⟩

/-- In `Φv`, a live lock on `B3` moves back to `B1` with its slot, fast bit and expiry. -/
theorem liveLocks_Φv_B3 {s : Nat} {f : Bool} {e : Nat} {t : Time} (he : sp.slot t ≤ e) :
    liveLocks sp {⟨3, s, f, e⟩} Φv t = {⟨1, s, f, e⟩} := by
  ext l'
  constructor
  · rintro ⟨l, rfl, B, hB, hr, -, rfl⟩
    rw [eq_of_root hB B3_mem hr, viableAncestor_Φv_B3]
    rfl
  · rintro rfl
    exact ⟨_, rfl, B3, B3_mem, rfl, he, by rw [viableAncestor_Φv_B3]; rfl⟩

open Classical in
/-- `fastExpiry` in `Φ` when every lock is live and on a block of the tree. -/
theorem fastExpiry_Φ {L : Set Lock} {t : Time} {s : Nat}
    (hL : ∀ l ∈ L, l.block ≤ 3 ∧ sp.slot t ≤ l.expiry) :
    fastExpiry sp L Φ t s =
      min (s + 6) (if {e | ∃ l ∈ L, l.fast = true ∧ l.slot < s ∧ e = l.expiry}.Nonempty
        then max (s + 2) (sSup {e | ∃ l ∈ L, l.fast = true ∧ l.slot < s ∧ e = l.expiry} + 2)
        else s + 2) := by
  unfold fastExpiry
  rw [liveLocks_Φ hL]

theorem slot_16 : sp.slot 16 = 4 := by decide

/-! ## `fastExpiry` -/

/-- With no lock, a fast lock of slot `s` gets the floor `s + 2`. -/
theorem fastExpiry_none (t : Time) (s : Nat) : fastExpiry sp ∅ Φ t s = s + 2 := by
  rw [fastExpiry_Φ (by simp), ite_eq_right (by simp)]
  omega

/-- **Grading.** A live fast lock of slot `3` with expiry `5` gives a slot-`4` fast lock the
expiry `5 + c = 7`: neither the floor `6` nor the cap `10`. -/
theorem fastExpiry_graded : fastExpiry sp {⟨0, 3, true, 5⟩} Φ 16 4 = 7 := by
  rw [fastExpiry_Φ (by rintro l rfl; exact ⟨by decide, by rw [slot_16]; decide⟩)]
  rw [show {e | ∃ l ∈ ({⟨0, 3, true, 5⟩} : Set Lock), l.fast = true ∧ l.slot < 4 ∧
    e = l.expiry} = {5} by ext; simp, ite_eq_left (Set.singleton_nonempty 5), csSup_singleton]
  decide

/-- **The cap.** A live fast lock of slot `3` with expiry `9` would give `9 + c = 11`; the cap
`s + k = 10` binds. -/
theorem fastExpiry_capped : fastExpiry sp {⟨0, 3, true, 9⟩} Φ 16 4 = 10 := by
  rw [fastExpiry_Φ (by rintro l rfl; exact ⟨by decide, by rw [slot_16]; decide⟩)]
  rw [show {e | ∃ l ∈ ({⟨0, 3, true, 9⟩} : Set Lock), l.fast = true ∧ l.slot < 4 ∧
    e = l.expiry} = {9} by ext; simp, ite_eq_left (Set.singleton_nonempty 9), csSup_singleton]
  decide

/-- The fast deadline is the latest expiry: of two live fast locks of earlier slots with
expiries `5` and `7`, the later one counts (`7 + c = 9`, not `5 + c = 7`). -/
theorem fastExpiry_latest :
    fastExpiry sp {⟨0, 2, true, 5⟩, ⟨0, 3, true, 7⟩} Φ 16 4 = 9 := by
  rw [fastExpiry_Φ (by
    rintro l (rfl | rfl) <;> exact ⟨by decide, by rw [slot_16]; decide⟩)]
  rw [show {e | ∃ l ∈ ({⟨0, 2, true, 5⟩, ⟨0, 3, true, 7⟩} : Set Lock), l.fast = true ∧
    l.slot < 4 ∧ e = l.expiry} = {5, 7} by ext; simp, ite_eq_left (Set.insert_nonempty 5 _),
    csSup_pair]
  decide

/-- **Per-slot `E` (rejection).** A live fast lock of the same slot `4` with expiry `6` does not
raise a slot-`4` fast lock: it gets the floor `6`, not `6 + c = 8`. -/
theorem fastExpiry_same_slot : fastExpiry sp {⟨0, 4, true, 6⟩} Φ 16 4 = 6 := by
  rw [fastExpiry_Φ (by rintro l rfl; exact ⟨by decide, by rw [slot_16]; decide⟩), ite_eq_right]
  · decide
  rintro ⟨e, l, rfl, -, h, -⟩
  exact absurd h (by decide)

/-- **An expired lock (rejection).** A fast lock with expiry `3` is not live in slot `4`: the
floor `6`, not `3 + c = 5` raised to the floor or anything above it. -/
theorem fastExpiry_expired : fastExpiry sp {⟨0, 1, true, 3⟩} Φ 16 4 = 6 := by
  have : liveLocks sp {⟨0, 1, true, 3⟩} Φ 16 = ∅ := by
    ext l'
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨l, rfl, -, -, -, hlive, -⟩
    exact absurd hlive (by rw [Lock.LiveAt, slot_16]; decide)
  unfold fastExpiry
  dsimp only
  rw [this, ite_eq_right (by simp)]
  decide

/-- **A slow lock (rejection).** A live slow lock of slot `3` with expiry `9` does not raise a
fast lock: the floor `6`, not the cap `10`. -/
theorem fastExpiry_slow : fastExpiry sp {⟨0, 3, false, 9⟩} Φ 16 4 = 6 := by
  rw [fastExpiry_Φ (by rintro l rfl; exact ⟨by decide, by rw [slot_16]; decide⟩), ite_eq_right]
  · decide
  rintro ⟨e, l, rfl, h, -⟩
  exact absurd h (by decide)

/-! ## The expiry is kept -/

/-- `liveLocks` keeps a live lock with its expiry. -/
theorem liveLocks_keeps : liveLocks sp {⟨0, 3, true, 5⟩} Φ 16 = {⟨0, 3, true, 5⟩} :=
  liveLocks_Φ (by rintro l rfl; exact ⟨by decide, by rw [slot_16]; decide⟩)

/-- `liveLocks` moves a lock on the non-viable `B3` back to `B1`, with its slot, fast bit and
expiry. -/
theorem liveLocks_moves_back : liveLocks sp {⟨3, 2, true, 5⟩} Φv 16 = {⟨1, 2, true, 5⟩} :=
  liveLocks_Φv_B3 (by rw [slot_16]; decide)

/-- `addLocks` writes the new lock with the expiry it is given and keeps the stored one's. -/
theorem addLocks_keeps :
    addLocks sp {⟨0, 3, true, 5⟩} Φ 16 4 {(0, true, 7)} = {⟨0, 3, true, 5⟩, ⟨0, 4, true, 7⟩} := by
  unfold addLocks
  rw [liveLocks_Φ]
  · ext l
    simp [or_comm]
  · rintro l (rfl | ⟨p, rfl, rfl⟩) <;> exact ⟨by decide, by rw [slot_16]; decide⟩

/-- `addLocks` moves a new lock on the non-viable `B3` back to `B1` with its expiry. -/
theorem addLocks_moves_back : addLocks sp ∅ Φv 16 4 {(3, true, 7)} = {⟨1, 4, true, 7⟩} := by
  unfold addLocks
  rw [show (∅ ∪ {l | ∃ p ∈ ({(3, true, 7)} : Set (Nat × Bool × Nat)), l = ⟨p.1, 4, p.2.1, p.2.2⟩})
    = ({⟨3, 4, true, 7⟩} : Set Lock) by ext; simp]
  exact liveLocks_Φv_B3 (by rw [slot_16]; decide)

/-- The slot-`3` vote of `v0`, on `B2`. -/
def w : Vote sp.n := ⟨v0, 3, 2⟩

/-- The view of the vote `w` alone, as votes and as support. -/
def Vw : View sp.n := ⟨{w}, {w}⟩

/-- Nobody equivocates in a view of one vote. -/
theorem not_equivocator {S : Set (Vote sp.n)} (hS : ∀ x ∈ S, x = w) (i : Fin sp.n) :
    i ∉ equivocators S := by
  rintro ⟨x, hx, y, hy, hne, -, -⟩
  exact hne ((hS x hx).trans (hS y hy).symm)

/-- `v0` opposes `B'` against `w` exactly when `B'` conflicts with `B2`. -/
theorem mem_opponents {B' : Blk sp.n Unit} :
    v0 ∈ opponents sp Φ Vw 3 B' ↔ ¬ Compatible U B2 B' := by
  constructor
  · rintro (h | ⟨x, hx, -, -, H, hH, hHr, hnc⟩)
    · exact absurd h (not_equivocator (fun x hx => hx) v0)
    · obtain rfl : x = w := hx
      rwa [eq_of_root hH B2_mem hHr] at hnc
  · exact fun h => Or.inr ⟨w, rfl, rfl, rfl, B2, B2_mem, rfl, h⟩

/-- Against `w`, a lock on `B3` unlocks to `B1`, the deepest ancestor that `w` does not oppose. -/
theorem unlockTarget_B3 : unlockTarget sp Φ Vw 3 B3 = B1 := by
  unfold unlockTarget
  rw [deepest_top (D := B1) ?h1 B1_mem ?h2]
  · rfl
  case h1 =>
    refine ⟨B1_mem, anc_B1_B3, ?_⟩
    rw [ncard_validators_zero (mem_opponents.not.2 (not_not.2 (Or.inr anc_B1_B2)))]
    decide
  case h2 =>
    rintro C ⟨hC, hCB3, hopp⟩
    rcases hC with rfl | rfl | rfl | rfl
    · exact anc_g _ B1_mem
    · exact Relation.ReflTransGen.refl
    · simpa [AncRoot, B2, B3] using ancRoot_of_anc hCB3
    · rw [ncard_validators_one (mem_opponents.2 not_compatible_B2_B3)] at hopp
      exact absurd hopp (by decide)

/-- `unlock` moves a lock of an earlier slot to its unlock target with its slot, fast bit and
expiry: the slot-`2` fast lock on `B3` with expiry `5` goes to `B1` against `w`. -/
theorem unlock_keeps : unlock sp {⟨3, 2, true, 5⟩} Φ 16 3 Vw = {⟨1, 2, true, 5⟩} := by
  have hlive : liveLocks sp {⟨3, 2, true, 5⟩} Φ 16 = {⟨3, 2, true, 5⟩} :=
    liveLocks_Φ (by rintro l rfl; exact ⟨by decide, by rw [slot_16]; decide⟩)
  ext l'
  constructor
  · rintro ⟨l, hl, B, hB, hr, rfl⟩
    rw [hlive] at hl
    obtain rfl : l = _ := hl
    rw [eq_of_root hB B3_mem hr, ite_eq_left (by decide), unlockTarget_B3]
    rfl
  · rintro rfl
    refine ⟨⟨3, 2, true, 5⟩, by rw [hlive]; rfl, B3, B3_mem, rfl, ?_⟩
    rw [ite_eq_left (by decide), unlockTarget_B3]
    rfl

/-! ## The update of slot `3` -/

/-- The state before the update of slot `3`: the slot-`3` vote `w` (stamped at `0`, as is every
block), saved results `B1` for the earlier slots, record genesis, and the locks `L`. -/
def base (L : Set Lock) : SAState sp.n where
  pool := fun s => if s = 3 then [w] else []
  voteStamp := fun _ => ETime.of 0
  blockStamp := fun _ => ETime.of 0
  saved := fun _ => some 1
  locks := L
  latestConfirmed := 0
  fgReported := 0
  votedSlot := 3
  restartTime := ⊥

theorem lookup_2 : lookup Φ 2 = some B2 := by
  cases h : lookup Φ 2 with
  | none => exact absurd ⟨B2, B2_mem, rfl⟩ (lookup_eq_none h)
  | some B =>
    obtain ⟨hB, hr⟩ := lookup_eq_some h
    exact congrArg some (eq_of_root hB B2_mem hr)

theorem mem_pool_3 {L : Set Lock} {x : Vote sp.n} (hx : x ∈ {v | v ∈ (base L).pool 3}) : x = w :=
  List.mem_singleton.1 hx

theorem resolutionTime_w (L : Set Lock) :
    resolutionTime (base L) Φ w < ETime.of (sp.ts (3 : Nat) + 2 * sp.Δ) := by
  unfold resolutionTime
  rw [show w.head = 2 from rfl, lookup_2]
  simp [w, B2, base, ETime.of, SAParams.ts, SAParams.Δ]

/-- The early support of the update of slot `3`. -/
theorem early_eq (L : Set Lock) :
    {v | v ∈ (base L).pool 3 ∧
      resolutionTime (base L) Φ v < ETime.of (sp.ts (3 : Nat) + 2 * sp.Δ)} = {w} := by
  ext x
  constructor
  · exact fun h => mem_pool_3 h.1
  · rintro rfl
    exact ⟨List.mem_singleton.2 rfl, resolutionTime_w L⟩

theorem score_pos (L : Set Lock) {B : Blk sp.n Unit} (h : Φ.Anc B B2) :
    confirmationScore sp (base L) Φ 3 B = 1 := by
  unfold confirmationScore
  dsimp only
  rw [early_eq]
  exact ncard_validators_one ⟨not_equivocator (fun _ => mem_pool_3) v0, w, rfl, rfl, rfl,
    B2, B2_mem, rfl, h⟩

theorem score_zero (L : Set Lock) {B : Blk sp.n Unit} (h : ¬ Φ.Anc B B2) :
    confirmationScore sp (base L) Φ 3 B = 0 := by
  unfold confirmationScore
  dsimp only
  rw [early_eq]
  refine ncard_validators_zero ?_
  rintro ⟨-, x, hx, -, -, R, hR, hRr, hanc⟩
  obtain rfl : x = w := hx
  exact h (eq_of_root hR B2_mem hRr ▸ hanc)

theorem voters_ncard (L : Set Lock) : (voters {v | v ∈ (base L).pool 3}).ncard = 1 :=
  ncard_validators_one ⟨w, List.mem_singleton.2 rfl, rfl⟩

/-- The result of the update of slot `3` is `B2`, the head of `w`. -/
theorem getConfirmation_base (L : Set Lock) : getConfirmation sp (base L) Φ 3 = some B2 := by
  unfold getConfirmation
  refine deepest_top ⟨B2_mem, anc_g _ B2_mem, ?_⟩ B2_mem ?_
  · rw [voters_ncard, score_pos L Relation.ReflTransGen.refl]
    decide
  · rintro C ⟨-, -, hlt⟩
    by_contra h
    rw [voters_ncard, score_zero L h] at hlt
    omega

/-- The fast test passes on the ancestors of `B2`. -/
theorem fastTest_base (L : Set Lock) {B : Blk sp.n Unit} :
    FastTest sp (base L) Φ 3 B ↔ Φ.Anc B B2 := by
  constructor
  · intro h
    by_contra hn
    unfold FastTest at h
    rw [score_zero L hn] at h
    exact absurd h (by decide)
  · intro h
    unfold FastTest
    rw [score_pos L h]
    decide

open Classical in
/-- The locks after an update of slot `s` with result `C`, `updateConfirmation` read off: the fast
lock on the deepest fast block `D` and the slow lock on the deepest slow block `X` of the path
that no live lock vetoes (`updateLatestConfirmed` keeps the locks). -/
theorem updateConfirmation_locks {A : SAState sp.n} {Ψ : Frm sp.n Unit} {t : Time} {s : Nat}
    {C : Blk sp.n Unit} (hC : getConfirmation sp A Ψ s = some C) {D X : Option (Blk sp.n Unit)}
    (hD : deepest Ψ {B | (B ∈ confirmationPath sp Ψ C ∧
      ¬ conflictsWithLock sp A.locks Ψ t B) ∧ FastTest sp A Ψ s B} = D)
    (hX : deepest Ψ {B | (B ∈ confirmationPath sp Ψ C ∧
      ¬ conflictsWithLock sp A.locks Ψ t B) ∧ ∀ j : Int, (s : Int) - sp.k < j → j < s →
        ∃ S ∈ Ψ.tree, Function.update A.saved s (some C.root) j = some S.root ∧ Ψ.Anc B S} = X) :
    (updateConfirmation sp A Ψ t s).locks = addLocks sp A.locks Ψ t s
      {p | (∃ B, D = some B ∧ p = (B.root, true, fastExpiry sp A.locks Ψ t s)) ∨
        (∃ B, X = some B ∧ p = (B.root, false, s + sp.k))} := by
  subst hD hX
  unfold updateConfirmation
  simp only [hC]
  split_ifs
  · rfl
  · unfold updateLatestConfirmed
    split_ifs <;> rfl

open Classical in
/-- The record after an update of slot `s` with result `C`: kept when a live lock vetoes `C`. -/
theorem updateConfirmation_latest {A : SAState sp.n} {Ψ : Frm sp.n Unit} {t : Time} {s : Nat}
    {C : Blk sp.n Unit} (hC : getConfirmation sp A Ψ s = some C) :
    (updateConfirmation sp A Ψ t s).latestConfirmed =
      if conflictsWithLock sp A.locks Ψ t C ∨ AncR Ψ C A.latestConfirmed then A.latestConfirmed
      else C.root := by
  unfold updateConfirmation
  simp only [hC]
  by_cases h : conflictsWithLock sp A.locks Ψ t C
  · rw [ite_eq_left h, ite_eq_left (Or.inl h)]
  · rw [ite_eq_right h]
    unfold updateLatestConfirmed
    by_cases h' : AncR Ψ C A.latestConfirmed
    · rw [ite_eq_left h', ite_eq_left (Or.inr h')]
    · rw [ite_eq_right h', ite_eq_right (not_or.2 ⟨h, h'⟩)]

/-- The path of the result `B2`: `B1` and `B2`. -/
theorem mem_path {B : Blk sp.n Unit} : B ∈ confirmationPath sp Φ B2 ↔ B = B1 ∨ B = B2 := by
  constructor
  · rintro ⟨hB, hr, hanc⟩
    have := ancRoot_of_anc hanc
    rcases hB with rfl | rfl | rfl | rfl
    · exact absurd rfl hr
    · exact Or.inl rfl
    · exact Or.inr rfl
    · simp [AncRoot, B2, B3] at this
  · rintro (rfl | rfl)
    · exact ⟨B1_mem, by decide, anc_B1_B2⟩
    · exact ⟨B2_mem, by decide, Relation.ReflTransGen.refl⟩

theorem anc_B2_of_path {B : Blk sp.n Unit} (h : B ∈ confirmationPath sp Φ B2) : Φ.Anc B B2 :=
  h.2.2

/-- The slow test of the update of slot `3` (saved results `B1`) passes exactly below `B1`. -/
theorem slow_iff (L : Set Lock) {B : Blk sp.n Unit} :
    (∀ j : Int, ((3 : Nat) : Int) - sp.k < j → j < (3 : Nat) → ∃ S ∈ Φ.tree,
      Function.update (base L).saved ((3 : Nat) : Int) (some B2.root) j = some S.root ∧
        Φ.Anc B S) ↔ Φ.Anc B B1 := by
  constructor
  · intro h
    obtain ⟨S, hS, hsv, hanc⟩ := h 2 (by decide) (by decide)
    rw [Function.update_of_ne (by decide)] at hsv
    rwa [eq_of_root hS B1_mem (Option.some.inj (hsv : some 1 = some S.root)).symm] at hanc
  · intro h j _ hj
    exact ⟨B1, B1_mem, by rw [Function.update_of_ne (by omega)]; rfl, h⟩

/-- A live lock on `B1` vetoes no ancestor of `B2`. -/
theorem not_conflicts_u {B : Blk sp.n Unit} (hB : Φ.Anc B B2) :
    ¬ conflictsWithLock sp ({⟨1, 2, true, 6⟩} : Set Lock) Φ 18 B := by
  rintro ⟨L', ⟨hL', l, hl, hr⟩, hnc⟩
  rw [liveLocks_Φ (by rintro l rfl; exact ⟨by decide, by decide⟩)] at hl
  obtain rfl : l = _ := hl
  rw [eq_of_root hL' B1_mem hr.symm] at hnc
  exact hnc (anc_total coherent_U hB anc_B1_B2)

/-- A live lock on `B3` vetoes exactly the blocks that conflict with `B3`. -/
theorem conflicts_v {B : Blk sp.n Unit} :
    conflictsWithLock sp ({⟨3, 2, true, 5⟩} : Set Lock) Φ 18 B ↔ ¬ Compatible U B B3 := by
  have hlive : liveLocks sp ({⟨3, 2, true, 5⟩} : Set Lock) Φ 18 = {⟨3, 2, true, 5⟩} :=
    liveLocks_Φ (by rintro l rfl; exact ⟨by decide, by decide⟩)
  constructor
  · rintro ⟨L', ⟨hL', l, hl, hr⟩, hnc⟩
    rw [hlive] at hl
    obtain rfl : l = _ := hl
    rwa [eq_of_root hL' B3_mem hr.symm] at hnc
  · exact fun h => ⟨B3, ⟨B3_mem, ⟨3, 2, true, 5⟩, by rw [hlive]; rfl, rfl⟩, h⟩

/-- The unvetoed update: a live fast lock of slot `2` on `B1` with expiry `6`. -/
def Au : SAState sp.n := base {⟨1, 2, true, 6⟩}

/-- The vetoed update: a live fast lock of slot `2` on `B3` (conflicting with the result `B2`)
with expiry `5`. -/
def Av : SAState sp.n := base {⟨3, 2, true, 5⟩}

/-- **The unvetoed update of slot `3`, independent writes.** The fast lock goes to the deepest
fast block `D = B2` with `fastExpiry = 6 + c = 8` (the live fast lock of slot `2` raises it above
the floor `5`, and the slow test does not lift it to `s + k`); the slow lock goes independently to
the deepest slow block `X = B1` with `s + k = 9`; the stored lock keeps its expiry. -/
theorem update_unvetoed_locks : (updateConfirmation sp Au Φ 18 3).locks =
    {⟨1, 2, true, 6⟩, ⟨2, 3, true, 8⟩, ⟨1, 3, false, 9⟩} := by
  rw [updateConfirmation_locks (A := Au) (getConfirmation_base _) (D := some B2) (X := some B1)]
  · have hfe : fastExpiry sp Au.locks Φ 18 3 = 8 := by
      rw [show Au.locks = {⟨1, 2, true, 6⟩} from rfl,
        fastExpiry_Φ (by rintro l rfl; exact ⟨by decide, by decide⟩)]
      rw [show {e | ∃ l ∈ ({⟨1, 2, true, 6⟩} : Set Lock), l.fast = true ∧ l.slot < 3 ∧
        e = l.expiry} = {6} by ext; simp, ite_eq_left (Set.singleton_nonempty 6), csSup_singleton]
      decide
    rw [hfe]
    unfold addLocks
    rw [liveLocks_Φ]
    · ext l
      simp [Au, base, B1, B2, or_comm]
    · rintro l (rfl | ⟨p, (⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩), rfl⟩)
      · exact ⟨by decide, by decide⟩
      · cases hB; exact ⟨by decide, by decide⟩
      · cases hB; exact ⟨by decide, by decide⟩
  · refine deepest_top ⟨⟨mem_path.2 (Or.inr rfl), not_conflicts_u Relation.ReflTransGen.refl⟩,
      (fastTest_base _).2 Relation.ReflTransGen.refl⟩ B2_mem fun C hC => anc_B2_of_path hC.1.1
  · refine deepest_top ⟨⟨mem_path.2 (Or.inl rfl), not_conflicts_u anc_B1_B2⟩,
      (slow_iff _).2 Relation.ReflTransGen.refl⟩ B1_mem fun C hC => (slow_iff _).1 hC.2

/-- The unvetoed update moves the record to the result `B2`. -/
theorem update_unvetoed_latest : (updateConfirmation sp Au Φ 18 3).latestConfirmed = 2 := by
  rw [updateConfirmation_latest (A := Au) (getConfirmation_base _), ite_eq_right]
  · rfl
  rintro (h | ⟨R, hR, hr, hanc⟩)
  · exact not_conflicts_u Relation.ReflTransGen.refl h
  · rw [eq_of_root hR g_mem hr] at hanc
    simpa [AncRoot, B2, g] using ancRoot_of_anc hanc

/-- **The vetoed update of slot `3` still writes (fix 2(a)).** The live lock on `B3` vetoes the
result `B2`, so the record stays at genesis, but the locks are written on the unvetoed part of
the path, `{B1}`: the fast lock with `fastExpiry = 5 + c = 7` and the slow lock with `s + k = 9`,
both on `B1`; the vetoing lock keeps its expiry. -/
theorem update_vetoed_locks : (updateConfirmation sp Av Φ 18 3).locks =
    {⟨3, 2, true, 5⟩, ⟨1, 3, true, 7⟩, ⟨1, 3, false, 9⟩} := by
  have hB1 : ¬ conflictsWithLock sp Av.locks Φ 18 B1 :=
    conflicts_v.not.2 (not_not.2 (Or.inl anc_B1_B3))
  have hup : ∀ C, C ∈ confirmationPath sp Φ B2 → ¬ conflictsWithLock sp Av.locks Φ 18 C →
      Φ.Anc C B1 := by
    intro C hC hnc
    rcases mem_path.1 hC with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact absurd (conflicts_v.2 not_compatible_B2_B3) hnc
  rw [updateConfirmation_locks (A := Av) (getConfirmation_base _) (D := some B1) (X := some B1)]
  · have hfe : fastExpiry sp Av.locks Φ 18 3 = 7 := by
      rw [show Av.locks = {⟨3, 2, true, 5⟩} from rfl,
        fastExpiry_Φ (by rintro l rfl; exact ⟨by decide, by decide⟩)]
      rw [show {e | ∃ l ∈ ({⟨3, 2, true, 5⟩} : Set Lock), l.fast = true ∧ l.slot < 3 ∧
        e = l.expiry} = {5} by ext; simp, ite_eq_left (Set.singleton_nonempty 5), csSup_singleton]
      decide
    rw [hfe]
    unfold addLocks
    rw [liveLocks_Φ]
    · ext l
      simp [Av, base, B1, or_comm]
    · rintro l (rfl | ⟨p, (⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩), rfl⟩)
      · exact ⟨by decide, by decide⟩
      · cases hB; exact ⟨by decide, by decide⟩
      · cases hB; exact ⟨by decide, by decide⟩
  · exact deepest_top ⟨⟨mem_path.2 (Or.inl rfl), hB1⟩, (fastTest_base _).2 anc_B1_B2⟩ B1_mem
      fun C hC => hup C hC.1.1 hC.1.2
  · exact deepest_top ⟨⟨mem_path.2 (Or.inl rfl), hB1⟩, (slow_iff _).2 Relation.ReflTransGen.refl⟩
      B1_mem fun C hC => hup C hC.1.1 hC.1.2

/-- The vetoed update keeps the record. -/
theorem update_vetoed_latest : (updateConfirmation sp Av Φ 18 3).latestConfirmed = 0 := by
  have h : conflictsWithLock sp Av.locks Φ 18 B2 := conflicts_v.2 not_compatible_B2_B3
  rw [updateConfirmation_latest (A := Av) (getConfirmation_base _), ite_eq_left (Or.inl h)]
  rfl

end Consensus.Goldilocks.SA.Test.Graded
