module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
public import Mathlib.Data.Set.Card
@[expose] public section

/-! # Graded fast locks: the veto path in a short run (fix 2(a))

`GoldilocksGradedLocks` checks single `updateConfirmation` calls. This file runs one node's AC
calls over two slots and a sleep, through the trusted handlers (`acOnTick`, `acOnMessage`,
`tryVote`, `optimisticConfirmation`, `updateConfirmation`, `acRestart`), at `k = 6`, `c = 2`,
four validators, `Δ = 1`, `t_s = 4s`. The node is `v0`; it is never the slot proposer, so it
makes no `ac_proposal` call, and its FG updates (`ac_to_fg`, which writes only `fg_reported`)
are left out.

The tree: genesis `g` (root `0`), `B1` (root `1`, slot `1`) on `g`, and the conflicting children
`Bc` (root `2`, slot `2`) and `Bv` (root `3`, slot `3`) of `B1`, both viable heads.

**The run** (`j₀ = 8`; the start state `S0` has the four slot-`8` votes on `Bc`, received at `32`,
and the saved results `Bc` of the earlier slots, so the slot-`8` update is slow-qualified):
* `t = 36` (slot `9`): the tick (no-op), then the slot-`9` votes of `v1`, `v2`, `v3` on `Bv`.
  The third gives three quarters of the committee: **an optimistic fast lock of slot `9` on
  `Bv`**, expiry `9 + 2 = 11`.
* `t = 37`: the tick votes. The anchor is `Bv` (the lock), a leaf, so the own vote is on `Bv`.
* `t = 38`: the tick runs the update of slot `8`. Its result `Bc` conflicts with the node's own
  newer lock on `Bv`: **vetoed**, the record stays. Under 2(a) the locks are still written on
  the unvetoed part of the path, `{B1}`: the fast lock with `fastExpiry = 8 + 2 = 10` (the newer
  slot-`9` lock does not raise it: per-slot `E`) and **the slow lock on `B1` with
  `s + k = 14`**.
* The node sleeps after `38` and wakes at `56 = t_14` (`j₀ + k = 14`): `acRestart`, with any
  replay order, keeps the locks.
* **At slot `14` the slow lock on `B1` is the node's only live lock** and its anchor is `B1`;
  the lock on `Bv` expired after slot `11`. At slot `15` nothing is live (the expiry is `s + k`
  exactly).

**Rejection control.** `updateConfirmationOld` is a local copy of the old rule, "a veto writes
nothing", which the spec no longer has. In the same run, it leaves the lock on `Bv` alone, so at
slot `14` the node has no live lock and its anchor is genesis. -/

namespace Consensus.Goldilocks.SA.Test.GradedVeto

/-- The shared parameters: four validators, `Δ = 1`, `t_s = 4s`, genesis root `0`. -/
abbrev P : Params where
  n := 4
  hn := by decide
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

/-- The validators; `v0` is the node. -/
abbrev v0 : Fin sp.n := ⟨0, by decide⟩
abbrev v1 : Fin sp.n := ⟨1, by decide⟩
abbrev v2 : Fin sp.n := ⟨2, by decide⟩
abbrev v3 : Fin sp.n := ⟨3, by decide⟩

/-! ## The tree and the frame -/

/-- Genesis. -/
def g : Blk sp.n Unit := ⟨0, none, 0, v0, 0, (), ([], [])⟩
/-- The fork block, slot `1`. -/
def B1 : Blk sp.n Unit := ⟨1, some 0, 1, v1, 0, (), ([], [])⟩
/-- The result side, slot `2`. -/
def Bc : Blk sp.n Unit := ⟨2, some 1, 2, v2, 0, (), ([], [])⟩
/-- The optimistic side, slot `3`, conflicting with `Bc`. -/
def Bv : Blk sp.n Unit := ⟨3, some 1, 3, v3, 0, (), ([], [])⟩

/-- The tree. -/
def U : Set (Blk sp.n Unit) := {g, B1, Bc, Bv}

/-- Ancestry in `U`, by roots. -/
def AncRoot (a b : Nat) : Prop := a = b ∨ a = 0 ∨ (a = 1 ∧ (b = 2 ∨ b = 3))

theorem g_mem : g ∈ U := Or.inl rfl
theorem B1_mem : B1 ∈ U := Or.inr (Or.inl rfl)
theorem Bc_mem : Bc ∈ U := Or.inr (Or.inr (Or.inl rfl))
theorem Bv_mem : Bv ∈ U := Or.inr (Or.inr (Or.inr rfl))

/-- A block of `U` is determined by its root. -/
theorem eq_of_root {B C : Blk sp.n Unit} (hB : B ∈ U) (hC : C ∈ U) (h : B.root = C.root) :
    B = C := by
  rcases hB with rfl | rfl | rfl | rfl <;> rcases hC with rfl | rfl | rfl | rfl <;>
    first | rfl | simp [g, B1, Bc, Bv] at h

/-- Ancestry inside `U` is `AncRoot` on the roots. -/
theorem ancRoot_of_anc {B C : Blk sp.n Unit} (h : Anc U B C) : AncRoot B.root C.root := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail c d _ e ih =>
    obtain ⟨-, hd, hp⟩ := e
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp only [g, B1, Bc, Bv, Option.some.injEq, reduceCtorEq] at hp <;>
      simp only [AncRoot, B1, Bc, Bv, true_or, or_true, and_true] at ih ⊢ <;> omega

theorem anc_g (B : Blk sp.n Unit) (hB : B ∈ U) : Anc U g B := by
  have h1 : Anc U g B1 := Relation.ReflTransGen.single ⟨g_mem, B1_mem, rfl⟩
  rcases hB with rfl | rfl | rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact h1
  · exact h1.tail ⟨B1_mem, Bc_mem, rfl⟩
  · exact h1.tail ⟨B1_mem, Bv_mem, rfl⟩

theorem anc_B1_Bc : Anc U B1 Bc := Relation.ReflTransGen.single ⟨B1_mem, Bc_mem, rfl⟩
theorem anc_B1_Bv : Anc U B1 Bv := Relation.ReflTransGen.single ⟨B1_mem, Bv_mem, rfl⟩

/-- `Bc` and `Bv` conflict. -/
theorem not_compatible_Bc_Bv : ¬ Compatible U Bc Bv := by
  rintro (h | h) <;> simpa [AncRoot, Bc, Bv] using ancRoot_of_anc h

theorem coherent_U : Coherent U := by
  refine ⟨fun B hB C hC h => eq_of_root hB hC h, fun B hB C hC h => ?_⟩
  rcases hB with rfl | rfl | rfl | rfl <;> rcases hC with rfl | rfl | rfl | rfl <;>
    simp [g, B1, Bc, Bv] at h ⊢

/-- The frame: `F = fc_root = g`, both children of `B1` viable. -/
def Φ : Frm sp.n Unit := ⟨U, g, g, {Bc, Bv}⟩

theorem finite_U : U.Finite := by
  simp only [U]
  exact ((((Set.finite_singleton Bv).insert Bc).insert B1).insert g)

theorem frameOK_Φ : FrameOK Φ where
  finite := finite_U
  coherent := coherent_U
  rooted := ⟨g_mem, anc_g⟩
  fcRoot_mem := g_mem
  F_anc_fcRoot := Relation.ReflTransGen.refl
  viableHeads_subset := by rintro W (rfl | rfl); exacts [Bc_mem, Bv_mem]
  fcRoot_anc_viableHeads := by rintro W (rfl | rfl); exacts [anc_g _ Bc_mem, anc_g _ Bv_mem]

/-- Every block is its own viable ancestor. -/
theorem viableAncestor_Φ {B : Blk sp.n Unit} (hB : B ∈ U) : Φ.viableAncestor B = B := by
  refine viableAncestor_self frameOK_Φ hB ?_
  rcases hB with rfl | rfl | rfl | rfl
  · exact Or.inr Relation.ReflTransGen.refl
  · exact Or.inl ⟨B1_mem, anc_g _ B1_mem, Bc, Bc_mem, Or.inl rfl, anc_B1_Bc⟩
  · exact Or.inl ⟨Bc_mem, anc_g _ Bc_mem, Bc, Bc_mem, Or.inl rfl, Relation.ReflTransGen.refl⟩
  · exact Or.inl ⟨Bv_mem, anc_g _ Bv_mem, Bv, Bv_mem, Or.inr rfl, Relation.ReflTransGen.refl⟩

/-- The block of a root at most `3`. -/
theorem exists_root {r : Nat} (hr : r ≤ 3) : ∃ B ∈ U, B.root = r := by
  obtain rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  exacts [⟨g, g_mem, rfl⟩, ⟨B1, B1_mem, rfl⟩, ⟨Bc, Bc_mem, rfl⟩, ⟨Bv, Bv_mem, rfl⟩]

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

/-- `AncR Φ B r` for a root `r` of a block `R` of the tree is `B ⪯ R`. -/
theorem ancR_iff {B R : Blk sp.n Unit} (hR : R ∈ U) : AncR Φ B R.root ↔ Φ.Anc B R :=
  ⟨fun ⟨_, hR', hr, h⟩ => eq_of_root hR' hR hr ▸ h, fun h => ⟨R, hR, rfl, h⟩⟩

/-- Live locks on blocks of the tree stay as they are. -/
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

/-- The blocks of a set of live locks on the roots of tree blocks. -/
theorem liveLockBlocks_Φ {L : Set Lock} {t : Time}
    (hL : ∀ l ∈ L, l.block ≤ 3 ∧ sp.slot t ≤ l.expiry)
    {B : Blk sp.n Unit} : B ∈ liveLockBlocks sp L Φ t ↔ B ∈ U ∧ ∃ l ∈ L, l.block = B.root := by
  unfold liveLockBlocks
  rw [liveLocks_Φ hL]
  rfl

/-! ## Times -/

theorem slot_36 : sp.slot 36 = 9 := by decide
theorem slot_37 : sp.slot 37 = 9 := by decide
theorem slot_38 : sp.slot 38 = 9 := by decide
theorem slot_56 : sp.slot 56 = 14 := by decide
theorem slot_60 : sp.slot 60 = 15 := by decide

theorem ts_9 : sp.ts ((9 : Nat) : Int) = 36 := by decide

theorem Δ_eq : sp.Δ = 1 := rfl

/-! ## Votes and the start state -/

/-- The slot-`8` vote of `i`, on `Bc`. -/
def vc (i : Fin sp.n) : Vote sp.n := ⟨i, 8, 2⟩

/-- The slot-`9` vote of `i`, on `Bv`. -/
def vv (i : Fin sp.n) : Vote sp.n := ⟨i, 9, 3⟩

/-- The slot-`8` pool: every validator on `Bc`. -/
def P8 : List (Vote sp.n) := [vc v0, vc v1, vc v2, vc v3]

/-- The fast lock of slot `9` on `Bv` that the optimistic confirmation writes, expiry `11`. -/
def lockV : Lock := ⟨3, 9, true, 11⟩

/-- The fast lock of slot `8` on `B1` that the vetoed update writes, expiry `10`. -/
def fastB1 : Lock := ⟨1, 8, true, 10⟩

/-- The slow lock of slot `8` on `B1` that the vetoed update writes, expiry `8 + k = 14`. -/
def slowB1 : Lock := ⟨1, 8, false, 14⟩

/-- The state of `v0` at `t_9 = 36`: the slot-`8` votes received at `32` (before `t_8 + 2Δ`),
every block received at `0`, the saved results `Bc` of the earlier slots (so the update of slot
`8` is slow-qualified on `Bc`), no locks, record genesis, voted in slot `8`, never restarted. -/
def S0 : SAState sp.n where
  pool := fun s => if s = 8 then P8 else []
  voteStamp := fun x => if x ∈ P8 then ETime.of 32 else ⊤
  blockStamp := fun r => if r = 0 then ⊥ else ETime.of 0
  saved := fun _ => some 2
  locks := ∅
  latestConfirmed := 0
  fgReported := 0
  votedSlot := 8
  restartTime := ⊥

/-- The fields the run does not change before the update and that the update reads. -/
structure Fixed (A : SAState sp.n) : Prop where
  pool8 : A.pool 8 = P8
  stamp : ∀ x ∈ P8, A.voteStamp x = ETime.of 32
  block : A.blockStamp = S0.blockStamp
  saved : A.saved = S0.saved
  rt : A.restartTime = ⊥

theorem fixed_S0 : Fixed S0 :=
  ⟨rfl, fun x hx => by simp [S0, hx], rfl, rfl, rfl⟩

theorem fixed_with {A : SAState sp.n} (h : Fixed A) (L : Set Lock) (r : Nat) (vs : Int) :
    Fixed { A with locks := L, latestConfirmed := r, votedSlot := vs } :=
  ⟨h.1, h.2, h.3, h.4, h.5⟩

theorem slot_of_mem_P8 {x : Vote sp.n} (hx : x ∈ P8) : x.slot = 8 := by
  simp only [P8, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> rfl

/-! ## Generic facts about the handlers -/

/-- Admission writes only the pool and the stamps. -/
theorem admitVote_eq (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    admitVote sp A t v = A ∨ admitVote sp A t v = { A with
      pool := Function.update A.pool v.slot (A.pool v.slot ++ [v])
      voteStamp := Function.update A.voteStamp v (ETime.of t) } := by
  unfold admitVote
  split_ifs
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem admitVote_locks (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).locks = A.locks := by
  rcases admitVote_eq A t v with h | h <;> rw [h]

theorem admitVote_restartTime (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).restartTime = A.restartTime := by
  rcases admitVote_eq A t v with h | h <;> rw [h]

/-- A slot-`9` vote's admission keeps `Fixed`. -/
theorem fixed_admitVote {A : SAState sp.n} (h : Fixed A) (t : Time) {v : Vote sp.n}
    (hv : v.slot = 9) : Fixed (admitVote sp A t v) := by
  rcases admitVote_eq A t v with he | he
  · rw [he]; exact h
  · rw [he]
    refine ⟨?_, fun x hx => ?_, h.3, h.4, h.5⟩
    · change Function.update A.pool v.slot _ 8 = P8
      rw [Function.update_of_ne (by rw [hv]; decide)]
      exact h.1
    · change Function.update A.voteStamp v _ x = _
      rw [Function.update_of_ne (fun e => by
        have := slot_of_mem_P8 hx; rw [e, hv] at this; exact absurd this (by decide))]
      exact h.2 x hx

/-- A fresh vote of slot `slot(t)` under the cap enters the pool. -/
theorem admitVote_pool {A : SAState sp.n} {t : Time} {v : Vote sp.n} (hs : v.slot = sp.slot t)
    (hn : v ∉ A.pool v.slot)
    (hc : ((A.pool v.slot).filter (fun x => x.val = v.val)).dedup.length < 2) :
    (admitVote sp A t v).pool v.slot = A.pool v.slot ++ [v] := by
  unfold admitVote
  rw [ite_eq_right (by rintro (h | h | h) <;> [omega; omega; exact hn h]), ite_eq_right (by omega)]
  exact Function.update_self _ _ _

/-- The optimistic confirmation writes only the locks and the record. -/
theorem optimisticConfirmation_eq (A : SAState sp.n) (Ψ : Frm sp.n Unit) (t : Time) :
    ∃ L r, optimisticConfirmation sp A Ψ t = { A with locks := L, latestConfirmed := r } := by
  unfold optimisticConfirmation
  split
  · exact ⟨A.locks, A.latestConfirmed, rfl⟩
  · unfold updateLatestConfirmed
    split_ifs
    · exact ⟨_, A.latestConfirmed, rfl⟩
    · exact ⟨_, _, rfl⟩

theorem updateLatestConfirmed_locks (A : SAState sp.n) (Ψ : Frm sp.n Unit) (C : Blk sp.n Unit) :
    (updateLatestConfirmed sp A Ψ C).locks = A.locks := by
  unfold updateLatestConfirmed
  split_ifs <;> rfl

/-- With an empty candidate set, the optimistic confirmation writes nothing. -/
theorem optimisticConfirmation_none {A : SAState sp.n} {t : Time}
    (h : optimisticSelect sp A Φ t = none) : optimisticConfirmation sp A Φ t = A := by
  unfold optimisticConfirmation
  rw [h]

/-- The optimistic voters are at most the pool's length. -/
theorem ncard_optimisticVoters_le (A : SAState sp.n) (s : Nat) (B : Blk sp.n Unit) :
    (optimisticVoters sp A Φ s B).ncard ≤ (A.pool s).length := by
  calc (optimisticVoters sp A Φ s B).ncard
      ≤ (((A.pool s).map Vote.val).toFinset : Set (Fin sp.n)).ncard :=
        Set.ncard_le_ncard (fun i ⟨x, hx, hxi, _⟩ => by
          simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]; exact ⟨x, hx, hxi⟩)
          (Finset.finite_toSet _)
    _ = ((A.pool s).map Vote.val).toFinset.card := Set.ncard_coe_finset _
    _ ≤ ((A.pool s).map Vote.val).length := List.toFinset_card_le _
    _ = (A.pool s).length := List.length_map _

/-- A block with an optimistic voter, when every slot-`9` head is `Bv`, is an ancestor of `Bv`. -/
theorem anc_Bv_of_voters {A : SAState sp.n} (hh : ∀ x ∈ A.pool 9, x.head = 3)
    {B : Blk sp.n Unit} (hB : (optimisticVoters sp A Φ 9 B).Nonempty) : Φ.Anc B Bv := by
  obtain ⟨i, x, hx, -, hanc⟩ := hB
  rw [hh x hx] at hanc
  exact (ancR_iff Bv_mem).1 hanc

/-- Three slot-`9` voters on `Bv` count for every ancestor of `Bv`. -/
theorem three_le_optimisticVoters {A : SAState sp.n}
    (h1 : vv v1 ∈ A.pool 9) (h2 : vv v2 ∈ A.pool 9) (h3 : vv v3 ∈ A.pool 9)
    {B : Blk sp.n Unit} (hB : Φ.Anc B Bv) : 3 ≤ (optimisticVoters sp A Φ 9 B).ncard := by
  have hsub : (({v1, v2, v3} : Finset (Fin sp.n)) : Set (Fin sp.n)) ⊆
      optimisticVoters sp A Φ 9 B := by
    intro i hi
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl | rfl
    exacts [⟨_, h1, rfl, (ancR_iff Bv_mem).2 hB⟩, ⟨_, h2, rfl, (ancR_iff Bv_mem).2 hB⟩,
      ⟨_, h3, rfl, (ancR_iff Bv_mem).2 hB⟩]
  calc 3 = (({v1, v2, v3} : Finset (Fin sp.n)) : Set (Fin sp.n)).ncard := by
        rw [Set.ncard_coe_finset]; rfl
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

/-- With the slot-`9` votes of `v1`, `v2`, `v3` (and only votes on `Bv`), the optimistic check
selects `Bv` when no live lock conflicts with it. -/
theorem optimisticSelect_Bv {A : SAState sp.n} {t : Time} (hj : joined sp A t)
    (hs : sp.slot t = 9) (ht : t < 38) (hh : ∀ x ∈ A.pool 9, x.head = 3)
    (h1 : vv v1 ∈ A.pool 9) (h2 : vv v2 ∈ A.pool 9) (h3 : vv v3 ∈ A.pool 9)
    (hc : ¬ conflictsWithLock sp A.locks Φ t Bv) : optimisticSelect sp A Φ t = some Bv := by
  unfold optimisticSelect
  dsimp only
  rw [hs, ite_eq_right (by
    rintro (h | h | h)
    · exact h hj
    · exact absurd h (by decide)
    · exact absurd (lt_of_le_of_lt h ht) (by decide))]
  refine deepest_top ⟨Bv_mem, ?_, hc⟩ Bv_mem fun C ⟨_, hC, _⟩ => ?_
  · have := three_le_optimisticVoters h1 h2 h3 (B := Bv) Relation.ReflTransGen.refl
    change 12 ≤ 4 * _; omega
  · refine anc_Bv_of_voters hh (Set.nonempty_of_ncard_ne_zero ?_)
    change 12 ≤ 4 * _ at hC; omega

/-- The walk from a leaf stays there. -/
theorem ghost_Bv {T : Set (Blk sp.n Unit)} (hT : T ⊆ U) (score : Blk sp.n Unit → Nat)
    (elig : Blk sp.n Unit → Prop) : ∀ fuel, ghost sp T score elig fuel Bv = Bv
  | 0 => rfl
  | fuel + 1 => by
    rw [ghost, dite_eq_right]
    rintro ⟨C, ⟨hCT, hp, -⟩, -⟩
    rcases hT hCT with rfl | rfl | rfl | rfl <;> simp [g, B1, Bc, Bv] at hp

/-- The fast deadline ignores the locks of the update's slot or later. -/
theorem fastExpiry_floor {L : Set Lock} {t : Time} {s : Nat}
    (hL : ∀ l ∈ L, l.block ≤ 3 ∧ sp.slot t ≤ l.expiry) (hs : ∀ l ∈ L, l.fast = true → s ≤ l.slot) :
    fastExpiry sp L Φ t s = s + 2 := by
  unfold fastExpiry
  dsimp only
  rw [liveLocks_Φ hL, ite_eq_right]
  · omega
  · rintro ⟨e, l, hl, hf, hlt, -⟩
    exact absurd (hs l hl hf) (by omega)

/-! ## The run: slot `9` -/

/-- The first and second slot-`9` messages enter the pool and lock nothing; the node does not
vote before `t_9 + Δ` without a slot-`9` proposal. -/
theorem tryVote_36 (A : SAState sp.n) : tryVote sp v0 A Φ 36 = (A, []) := by
  unfold tryVote
  dsimp only
  rw [slot_36]
  have hr : ¬ voteReady sp Φ 9 := by
    rintro ⟨B, hB, hs, -⟩
    rcases hB with rfl | rfl | rfl | rfl <;> simp [g, B1, Bc, Bv] at hs
  split_ifs with h1 h2
  all_goals first | rfl | exact absurd ⟨by rw [ts_9]; decide, Or.inr hr⟩ h2

/-- The tick at `t_9 = 36` does nothing. -/
theorem tick_36 (A : SAState sp.n) : acOnTick sp v0 A Φ 36 = (A, []) := by
  unfold acOnTick
  dsimp only
  rw [slot_36, ite_eq_right (show ¬ ((36 : Time) = sp.ts ((9 : Nat) : Int) + sp.Δ) by decide),
    ite_eq_right (show ¬ ((36 : Time) = sp.ts ((9 : Nat) : Int) + 2 * sp.Δ ∧ 0 < 9) by decide)]
  split_ifs <;> rfl

/-- After the first message. -/
def S1 : SAState sp.n := admitVote sp S0 36 (vv v1)
/-- After the second message. -/
def S2 : SAState sp.n := admitVote sp S1 36 (vv v2)
/-- The third vote admitted, before the optimistic check. -/
def S3' : SAState sp.n := admitVote sp S2 36 (vv v3)
/-- After the third message: the optimistic check has run. -/
noncomputable def S3 : SAState sp.n := optimisticConfirmation sp S3' Φ 36

theorem S0_pool9 : S0.pool 9 = [] := by simp [S0]

theorem S1_pool : S1.pool 9 = [vv v1] := by
  have := admitVote_pool (A := S0) (t := 36) (v := vv v1) slot_36.symm
    (by rw [show (vv v1).slot = 9 from rfl, S0_pool9]; simp)
    (by rw [show (vv v1).slot = 9 from rfl, S0_pool9]; simp)
  rwa [show (vv v1).slot = 9 from rfl, S0_pool9] at this
theorem S2_pool : S2.pool 9 = [vv v1, vv v2] := by
  have := admitVote_pool (A := S1) (t := 36) (v := vv v2) slot_36.symm
    (by rw [show (vv v2).slot = 9 from rfl, S1_pool]; decide)
    (by rw [show (vv v2).slot = 9 from rfl, S1_pool]; decide)
  rwa [show (vv v2).slot = 9 from rfl, S1_pool] at this
theorem S3'_pool : S3'.pool 9 = [vv v1, vv v2, vv v3] := by
  have := admitVote_pool (A := S2) (t := 36) (v := vv v3) slot_36.symm
    (by rw [show (vv v3).slot = 9 from rfl, S2_pool]; decide)
    (by rw [show (vv v3).slot = 9 from rfl, S2_pool]; decide)
  rwa [show (vv v3).slot = 9 from rfl, S2_pool] at this

theorem fixed_S1 : Fixed S1 := fixed_admitVote fixed_S0 _ rfl
theorem fixed_S2 : Fixed S2 := fixed_admitVote fixed_S1 _ rfl
theorem fixed_S3' : Fixed S3' := fixed_admitVote fixed_S2 _ rfl
theorem fixed_S3 : Fixed S3 := by
  obtain ⟨L, r, h⟩ := optimisticConfirmation_eq S3' Φ 36
  rw [S3, h]
  exact fixed_with fixed_S3' L r S3'.votedSlot

theorem S2_locks : S2.locks = ∅ := by
  rw [S2, admitVote_locks, S1, admitVote_locks]; rfl

/-- Two voters are fewer than three quarters of four: the check selects nothing. -/
theorem optimisticSelect_few {A : SAState sp.n} {t : Time} (h : (A.pool 9).length ≤ 2)
    (hs : sp.slot t = 9) : optimisticSelect sp A Φ t = none := by
  unfold optimisticSelect
  dsimp only
  rw [hs]
  split_ifs
  · rfl
  · unfold deepest
    rw [dite_eq_right]
    rintro ⟨B, ⟨-, hB, -⟩, -⟩
    have := ncard_optimisticVoters_le A 9 B
    change 12 ≤ 4 * _ at hB
    omega

/-- **`t = 36`, first message** (`v1` on `Bv`): admitted, nothing locked. -/
theorem msg_1 : acOnMessage sp v0 S0 Φ 36 (vv v1) = (S1, []) := by
  unfold acOnMessage
  rw [optimisticConfirmation_none (optimisticSelect_few (by rw [← S1, S1_pool]; decide) slot_36),
    tryVote_36]
  rfl

/-- **`t = 36`, second message** (`v2` on `Bv`): admitted, nothing locked. -/
theorem msg_2 : acOnMessage sp v0 S1 Φ 36 (vv v2) = (S2, []) := by
  unfold acOnMessage
  rw [optimisticConfirmation_none (optimisticSelect_few (by rw [← S2, S2_pool]; decide) slot_36),
    tryVote_36]
  rfl

/-- **`t = 36`, third message** (`v3` on `Bv`): the optimistic check runs. -/
theorem msg_3 : acOnMessage sp v0 S2 Φ 36 (vv v3) = (S3, []) := by
  unfold acOnMessage
  rw [tryVote_36]
  rfl

theorem heads_S3' : ∀ x ∈ S3'.pool 9, x.head = 3 := by
  rw [S3'_pool]; decide

/-- **The optimistic lock**: three quarters of the committee on `Bv` before `t_9 + 2Δ` give the
node a fast lock of slot `9` on `Bv`, with the floor expiry `9 + 2 = 11`. -/
theorem S3_locks : S3.locks = {lockV} := by
  have hsel : optimisticSelect sp S3' Φ 36 = some Bv := by
    refine optimisticSelect_Bv (by rw [joined, fixed_S3'.rt]; exact bot_le) slot_36 (by decide)
      heads_S3' (by rw [S3'_pool]; decide) (by rw [S3'_pool]; decide) (by rw [S3'_pool]; decide) ?_
    rintro ⟨B, hB, -⟩
    rw [show S3'.locks = ∅ by rw [S3', admitVote_locks, S2_locks]] at hB
    rw [liveLockBlocks_Φ (by simp)] at hB
    simp at hB
  unfold S3 optimisticConfirmation
  rw [hsel, updateLatestConfirmed_locks]
  dsimp only
  have hL : S3'.locks = ∅ := by rw [S3', admitVote_locks, S2_locks]
  rw [hL, fastExpiry_floor (by simp) (by simp)]
  unfold addLocks
  rw [liveLocks_Φ (by
    rintro l (h | ⟨p, rfl, rfl⟩)
    · exact absurd h (Set.notMem_empty _)
    · exact ⟨by decide, by rw [slot_36]; decide⟩)]
  ext l
  simp [lockV, Bv, slot_36]

/-- The lock on `Bv` is live in slot `9` and is its own viable ancestor. -/
theorem liveLocks_lockV {t : Time} (ht : sp.slot t ≤ 11) : liveLocks sp {lockV} Φ t = {lockV} :=
  liveLocks_Φ (by rintro l rfl; exact ⟨by decide, ht⟩)

/-- The lock on `Bv` vetoes exactly the blocks that conflict with `Bv`. -/
theorem conflicts_lockV {t : Time} (ht : sp.slot t ≤ 11) {B : Blk sp.n Unit} :
    conflictsWithLock sp {lockV} Φ t B ↔ ¬ Compatible U B Bv := by
  constructor
  · rintro ⟨L', hL', hnc⟩
    rw [liveLockBlocks_Φ (by rintro l rfl; exact ⟨by decide, ht⟩)] at hL'
    obtain ⟨hL'U, l, rfl, hr⟩ := hL'
    rwa [eq_of_root hL'U Bv_mem hr.symm] at hnc
  · exact fun h => ⟨Bv, (liveLockBlocks_Φ (by rintro l rfl; exact ⟨by decide, ht⟩)).2
      ⟨Bv_mem, lockV, rfl, rfl⟩, h⟩

/-- Unlocking against the slot-`8` votes keeps the slot-`9` lock. -/
theorem unlock_lockV (W : View sp.n) :
    unlock sp {lockV} Φ 37 ((9 : Nat) - 1 : Int) W = {lockV} := by
  have hlive := liveLocks_lockV (t := 37) (by rw [slot_37]; decide)
  ext l'
  constructor
  · rintro ⟨l, hl, B, -, -, rfl⟩
    rw [hlive] at hl
    obtain rfl : l = lockV := hl
    rw [ite_eq_right (by decide)]
    rfl
  · rintro rfl
    exact ⟨lockV, by rw [hlive]; rfl, Bv, Bv_mem, rfl, by rw [ite_eq_right (by decide)]⟩

/-- The anchor of a node whose only lock is the one on `Bv` is `Bv`. -/
theorem getAnchor_lockV {A : SAState sp.n} {t : Time} (hA : A.locks = {lockV})
    (ht : sp.slot t ≤ 11) : getAnchor sp A Φ t = Bv := by
  have hL : ∀ l ∈ ({lockV} : Set Lock), l.block ≤ 3 ∧ sp.slot t ≤ l.expiry := by
    rintro l rfl; exact ⟨by decide, ht⟩
  unfold getAnchor
  rw [hA, deepest_top (D := Bv) (Or.inl ((liveLockBlocks_Φ hL).2 ⟨Bv_mem, lockV, rfl, rfl⟩))
    Bv_mem]
  · rfl
  rintro C (hC | rfl)
  · rw [liveLockBlocks_Φ hL] at hC
    obtain ⟨hCU, l, rfl, hr⟩ := hC
    rw [eq_of_root hCU Bv_mem hr.symm]
    exact Relation.ReflTransGen.refl
  · exact anc_g _ Bv_mem

/-- The state after the own vote at `t_9 + Δ = 37`. -/
noncomputable def S4 : SAState sp.n :=
  optimisticConfirmation sp (admitVote sp { S3 with votedSlot := 9 } 37 (vv v0)) Φ 37

/-- **`t = 37`, the tick votes**: the anchor is the lock block `Bv`, a leaf, so the own vote is
on `Bv`; it is admitted and the optimistic check runs again. -/
theorem admitVote_votedSlot (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).votedSlot = A.votedSlot := by
  rcases admitVote_eq A t v with h | h <;> rw [h]

theorem S3_votedSlot : S3.votedSlot = 8 := by
  obtain ⟨L, r, he⟩ := optimisticConfirmation_eq S3' Φ 36
  rw [S3, he]
  change S3'.votedSlot = 8
  rw [S3', admitVote_votedSlot, S2, admitVote_votedSlot, S1, admitVote_votedSlot]
  rfl

theorem tick_37 : (acOnTick sp v0 S3 Φ 37).1 = S4 := by
  have hj : joined sp S3 37 := by rw [joined, fixed_S3.rt]; exact bot_le
  have hA1 : ∀ W : View sp.n,
      ({ S3 with locks := unlock sp S3.locks Φ 37 ((9 : Nat) - 1 : Int) W } : SAState sp.n) =
        S3 := by
    intro W
    rw [S3_locks, unlock_lockV, ← S3_locks]
  unfold acOnTick
  dsimp only
  rw [slot_37, ite_eq_right (not_not.2 hj),
    ite_eq_left (show (37 : Time) = sp.ts ((9 : Nat) : Int) + sp.Δ by decide),
    ite_eq_right (show ¬ ((37 : Time) = sp.ts ((9 : Nat) : Int) + 2 * sp.Δ ∧ 0 < 9) by decide)]
  unfold tryVote
  dsimp only
  rw [slot_37, ite_eq_right (by
    rintro (h | h | h)
    · exact h hj
    · rw [S3_votedSlot] at h; exact absurd h (by decide)
    · exact absurd h (by decide)),
    ite_eq_right (show ¬ ((37 : Time) < sp.ts ((9 : Nat) : Int) + sp.Δ ∧
      ((9 : Nat) = 0 ∨ ¬ voteReady sp Φ 9)) from fun h => absurd h.1 (by decide)),
    ite_eq_left (show 0 < (9 : Nat) by decide), hA1]
  unfold getHead
  rw [getAnchor_lockV S3_locks (by rw [slot_37]; decide),
    ghost_Bv (fun B hB => by rcases hB.1 with ⟨h, -⟩ | ⟨h, -⟩; exacts [h.1, h])]
  rfl

theorem fixed_S4 : Fixed S4 := by
  obtain ⟨L, r, h⟩ :=
    optimisticConfirmation_eq (admitVote sp { S3 with votedSlot := 9 } 37 (vv v0)) Φ 37
  rw [S4, h]
  exact fixed_with
    (fixed_admitVote (fixed_with fixed_S3 S3.locks S3.latestConfirmed 9) 37 rfl) L r _

/-- After its own vote the node still holds the one lock on `Bv`: the check selects `Bv` again
and writes the same lock (the slot-`9` lock does not raise a slot-`9` expiry). -/
theorem S4_locks : S4.locks = {lockV} := by
  set A : SAState sp.n := admitVote sp { S3 with votedSlot := 9 } 37 (vv v0) with hA
  have hpool : A.pool 9 = [vv v1, vv v2, vv v3, vv v0] := by
    have h3 : ({ S3 with votedSlot := 9 } : SAState sp.n).pool 9 = [vv v1, vv v2, vv v3] := by
      obtain ⟨L, r, he⟩ := optimisticConfirmation_eq S3' Φ 36
      change S3.pool 9 = _
      rw [S3, he]
      exact S3'_pool
    have := admitVote_pool (A := { S3 with votedSlot := 9 }) (t := 37) (v := vv v0) slot_37.symm
      (by rw [show (vv v0).slot = 9 from rfl, h3]; decide)
      (by rw [show (vv v0).slot = 9 from rfl, h3]; decide)
    rw [show (vv v0).slot = 9 from rfl, h3] at this
    exact this
  have hL : A.locks = {lockV} := by rw [hA, admitVote_locks]; exact S3_locks
  have hsel : optimisticSelect sp A Φ 37 = some Bv :=
    optimisticSelect_Bv (by rw [joined, admitVote_restartTime]; exact fixed_S3.rt ▸ bot_le)
      slot_37 (by decide) (by rw [hpool]; decide) (by rw [hpool]; decide)
      (by rw [hpool]; decide) (by rw [hpool]; decide)
      (by rw [hL, conflicts_lockV (by rw [slot_37]; decide)]; exact not_not.2 (Or.inl
        Relation.ReflTransGen.refl))
  unfold S4 optimisticConfirmation
  rw [← hA, hsel, updateLatestConfirmed_locks]
  dsimp only
  rw [hL, fastExpiry_floor (by rintro l rfl; exact ⟨by decide, by rw [slot_37]; decide⟩)
    (by rintro l rfl _; exact le_rfl)]
  unfold addLocks
  rw [liveLocks_Φ (by
    rintro l (rfl | ⟨p, rfl, rfl⟩) <;> exact ⟨by decide, by rw [slot_37]; decide⟩)]
  ext l
  simp [lockV, Bv, slot_37]

/-! ## The run: the update of slot `8` at `t_9 + 2Δ = 38` -/

/-- **`t = 38`, the tick runs the update of slot `8`.** -/
theorem tick_38 {A : SAState sp.n} (h : Fixed A) :
    acOnTick sp v0 A Φ 38 = (updateConfirmation sp A Φ 38 8, []) := by
  have hj : joined sp A 38 := by rw [joined, h.rt]; exact bot_le
  unfold acOnTick
  dsimp only
  rw [slot_38, ite_eq_right (not_not.2 hj),
    ite_eq_right (show ¬ ((38 : Time) = sp.ts ((9 : Nat) : Int) + sp.Δ) by decide),
    ite_eq_left (show (38 : Time) = sp.ts ((9 : Nat) : Int) + 2 * sp.Δ ∧ 0 < 9 by decide)]

theorem lookup_2 : lookup Φ 2 = some Bc := by
  cases h : lookup Φ 2 with
  | none => exact absurd ⟨Bc, Bc_mem, rfl⟩ (lookup_eq_none h)
  | some B =>
    obtain ⟨hB, hr⟩ := lookup_eq_some h
    exact congrArg some (eq_of_root hB Bc_mem hr)

/-- No validator has two slot-`8` votes. -/
theorem no_equivocators (i : Fin sp.n) : i ∉ equivocators {v | v ∈ P8} := by
  rintro ⟨x, hx, y, hy, hne, hxi, hyi⟩
  have : ∀ x ∈ P8, ∀ y ∈ P8, x.val = y.val → x = y := by decide
  exact hne (this x hx y hy (hxi.trans hyi.symm))

/-- Every slot-`8` vote is resolved before `t_8 + 2Δ = 34`. -/
theorem early_eq {A : SAState sp.n} (h : Fixed A) :
    {v | v ∈ A.pool 8 ∧ resolutionTime A Φ v < ETime.of (sp.ts (8 : Nat) + 2 * sp.Δ)} =
      {v | v ∈ P8} := by
  ext x
  simp only [Set.mem_ofPred_eq, h.pool8, and_iff_left_iff_imp]
  intro hx
  have hh : x.head = 2 := by
    simp only [P8, vc, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> rfl
  unfold resolutionTime
  rw [hh, lookup_2]
  dsimp only
  rw [slot_of_mem_P8 hx, ite_eq_right (show ¬ 8 < Bc.slot by decide), h.2 x hx, h.block,
    show sp.ts ((8 : Nat) : Int) + 2 * sp.Δ = 34 by decide]
  simp only [S0, ETime.of, ite_eq_right (show (2 : Nat) ≠ 0 by decide)]
  exact max_lt (WithBot.coe_lt_coe.2 (WithTop.coe_lt_coe.2 (by decide)))
    (WithBot.coe_lt_coe.2 (WithTop.coe_lt_coe.2 (by decide)))

theorem vc_mem (i : Fin sp.n) : vc i ∈ P8 := by
  revert i; decide

theorem ncard_univ_4 : (Set.univ : Set (Fin sp.n)).ncard = 4 := by
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

open Classical in
/-- The slot-`8` score: all four validators for the ancestors of `Bc`, nobody otherwise. -/
theorem score_eq {A : SAState sp.n} (h : Fixed A) (B : Blk sp.n Unit) :
    confirmationScore sp A Φ 8 B = if Φ.Anc B Bc then 4 else 0 := by
  unfold confirmationScore
  dsimp only
  rw [early_eq h, h.pool8]
  split_ifs with hB
  · rw [show supporters Φ ⟨{v | v ∈ P8}, {v | v ∈ P8}⟩ (8 : Nat) B = Set.univ from
      Set.eq_univ_of_forall fun i => ⟨no_equivocators i, vc i, vc_mem i,
        rfl, rfl, (ancR_iff Bc_mem).2 hB⟩, ncard_univ_4]
  · refine (Set.ncard_eq_zero (Set.toFinite _)).2 (Set.eq_empty_of_forall_notMem ?_)
    rintro i ⟨-, x, hx, -, -, hanc⟩
    have hh : x.head = 2 := by
      simp only [Set.mem_ofPred_eq, P8, vc, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> rfl
    rw [hh] at hanc
    exact hB ((ancR_iff Bc_mem).1 hanc)

theorem voters_P8 : (voters {v | v ∈ P8}).ncard = 4 := by
  rw [show voters {v | v ∈ P8} = Set.univ from Set.eq_univ_of_forall fun i => ⟨vc i, vc_mem i, rfl⟩,
    ncard_univ_4]

/-- The result of the update of slot `8` is `Bc`. -/
theorem getConfirmation_8 {A : SAState sp.n} (h : Fixed A) :
    getConfirmation sp A Φ 8 = some Bc := by
  unfold getConfirmation
  rw [h.pool8, voters_P8]
  refine deepest_top ⟨Bc_mem, anc_g _ Bc_mem, ?_⟩ Bc_mem ?_
  · rw [score_eq h, ite_eq_left (show Φ.Anc Bc Bc from Relation.ReflTransGen.refl)]; decide
  · rintro C ⟨-, -, hlt⟩
    by_contra hC
    rw [score_eq h, ite_eq_right (show ¬ Φ.Anc C Bc from hC)] at hlt
    omega

theorem fastTest_8 {A : SAState sp.n} (h : Fixed A) {B : Blk sp.n Unit} :
    FastTest sp A Φ 8 B ↔ Φ.Anc B Bc := by
  unfold FastTest
  rw [score_eq h]
  split_ifs with hB
  · exact iff_of_true (by decide) hB
  · exact iff_of_false (by decide) hB

/-- The path of the result `Bc`: `B1` and `Bc`. -/
theorem mem_path {B : Blk sp.n Unit} : B ∈ confirmationPath sp Φ Bc ↔ B = B1 ∨ B = Bc := by
  constructor
  · rintro ⟨hB, hr, hanc⟩
    have := ancRoot_of_anc hanc
    rcases hB with rfl | rfl | rfl | rfl
    · exact absurd rfl hr
    · exact Or.inl rfl
    · exact Or.inr rfl
    · simp [AncRoot, Bc, Bv] at this
  · rintro (rfl | rfl)
    · exact ⟨B1_mem, by decide, anc_B1_Bc⟩
    · exact ⟨Bc_mem, by decide, Relation.ReflTransGen.refl⟩

/-- On the path, the lock on `Bv` vetoes `Bc` and leaves `B1`. -/
theorem path_unvetoed {B : Blk sp.n Unit} (hB : B ∈ confirmationPath sp Φ Bc) :
    ¬ conflictsWithLock sp {lockV} Φ 38 B ↔ B = B1 := by
  rw [conflicts_lockV (by rw [slot_38]; decide), not_not]
  rcases mem_path.1 hB with rfl | rfl
  · exact ⟨fun _ => rfl, fun _ => Or.inl anc_B1_Bv⟩
  · exact ⟨fun h => absurd h not_compatible_Bc_Bv, fun h => by simp [Bc, B1] at h⟩

/-- The slow test (saved results `Bc` in the previous `k − 1` slots) passes below `Bc`. -/
theorem slow_iff {A : SAState sp.n} (h : Fixed A) {B : Blk sp.n Unit} :
    (∀ j : Int, ((8 : Nat) : Int) - sp.k < j → j < (8 : Nat) → ∃ S ∈ Φ.tree,
      Function.update A.saved ((8 : Nat) : Int) (some Bc.root) j = some S.root ∧ Φ.Anc B S) ↔
        Φ.Anc B Bc := by
  constructor
  · intro hs
    obtain ⟨S, hS, hsv, hanc⟩ := hs 7 (by decide) (by decide)
    rw [Function.update_of_ne (by decide), h.saved] at hsv
    rwa [eq_of_root hS Bc_mem (Option.some.inj (hsv : some 2 = some S.root)).symm] at hanc
  · intro hB j _ hj
    exact ⟨Bc, Bc_mem, by rw [Function.update_of_ne (by omega), h.saved]; rfl, hB⟩

open Classical in
/-- The locks after an update of slot `s` with result `C` (the `updateConfirmation` body read
off; `updateLatestConfirmed` keeps the locks). -/
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

/-- The state after the update of slot `8`. -/
noncomputable def S5 : SAState sp.n := updateConfirmation sp S4 Φ 38 8

/-- **The update of slot `8` is vetoed by the node's own newer lock on `Bv`**: its result `Bc`
conflicts with it. -/
theorem update_vetoed : getConfirmation sp S4 Φ 8 = some Bc ∧
    conflictsWithLock sp S4.locks Φ 38 Bc := by
  refine ⟨getConfirmation_8 fixed_S4, ?_⟩
  rw [S4_locks, conflicts_lockV (by rw [slot_38]; decide)]
  exact not_compatible_Bc_Bv

/-- The vetoed update keeps the record. -/
theorem S5_latest : S5.latestConfirmed = S4.latestConfirmed := by
  unfold S5 updateConfirmation
  simp only [getConfirmation_8 fixed_S4]
  rw [ite_eq_left update_vetoed.2]

/-- **Fix 2(a): the vetoed update still writes** on the unvetoed part of the path, `{B1}`: the
fast lock with `fastExpiry = 8 + 2 = 10` (the newer slot-`9` lock does not raise it) and the slow
lock with `s + k = 14`, beside the lock on `Bv`. -/
theorem S5_locks : S5.locks = {lockV, fastB1, slowB1} := by
  have hset : ∀ (T : Blk sp.n Unit → Prop), (∀ B, Φ.Anc B Bc → T B) →
      deepest Φ {B | (B ∈ confirmationPath sp Φ Bc ∧ ¬ conflictsWithLock sp S4.locks Φ 38 B) ∧
        T B} = some B1 := by
    intro T hT
    rw [S4_locks]
    refine deepest_top ⟨⟨mem_path.2 (Or.inl rfl), (path_unvetoed (mem_path.2 (Or.inl rfl))).2 rfl⟩,
      hT _ anc_B1_Bc⟩ B1_mem fun C ⟨⟨hp, hc⟩, _⟩ => ?_
    rw [(path_unvetoed hp).1 hc]
    exact Relation.ReflTransGen.refl
  rw [S5, updateConfirmation_locks (getConfirmation_8 fixed_S4) (D := some B1) (X := some B1)
    ((by
      have := hset (FastTest sp S4 Φ 8) fun B hB => (fastTest_8 fixed_S4).2 hB
      exact this))
    ((by
      have := hset (fun B => ∀ j : Int, ((8 : Nat) : Int) - sp.k < j → j < (8 : Nat) →
        ∃ S ∈ Φ.tree, Function.update S4.saved ((8 : Nat) : Int) (some Bc.root) j =
          some S.root ∧ Φ.Anc B S) fun B hB => (slow_iff fixed_S4).2 hB
      exact this)), S4_locks,
    fastExpiry_floor (by rintro l rfl; exact ⟨by decide, by rw [slot_38]; decide⟩)
      (by rintro l rfl _; decide)]
  unfold addLocks
  rw [liveLocks_Φ (by
    rintro l (rfl | ⟨p, (⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩), rfl⟩)
    · exact ⟨by decide, by rw [slot_38]; decide⟩
    · cases hB; exact ⟨by decide, by rw [slot_38]; decide⟩
    · cases hB; exact ⟨by decide, by rw [slot_38]; decide⟩)]
  ext l
  simp [lockV, fastB1, slowB1, B1, or_comm]

/-! ## Sleep and the restart at `t_{j₀+k} = 56` -/

theorem not_joined_56 {A : SAState sp.n} (h : A.restartTime = ((56 : Time) : WithBot Time)) :
    ¬ joined sp A 56 := by
  rw [joined, h, slot_56, show sp.ts (((14 : Nat) : Int) - 1) = 52 by decide]
  exact fun h' => absurd (WithBot.coe_le_coe.1 h') (by decide)

theorem blockReceipt_locks_rt (A : SAState sp.n) (t : Time) (B : Blk sp.n Unit) :
    (blockReceipt sp A t B).locks = A.locks ∧
      (blockReceipt sp A t B).restartTime = A.restartTime := by
  unfold blockReceipt
  suffices ∀ (l : List (Vote sp.n)) (X : SAState sp.n),
      (l.foldl (fun A v => admitVote sp A t v) X).locks = X.locks ∧
        (l.foldl (fun A v => admitVote sp A t v) X).restartTime = X.restartTime from this _ _
  intro l
  induction l with
  | nil => exact fun _ => ⟨rfl, rfl⟩
  | cons v l ih =>
    intro X
    rw [List.foldl_cons, (ih _).1, (ih _).2, admitVote_locks, admitVote_restartTime]
    exact ⟨rfl, rfl⟩

/-- A block replayed by a restart at `56` changes no lock: the node is not joined. -/
theorem acOnBlock_56 {A : SAState sp.n} (h : A.restartTime = ((56 : Time) : WithBot Time))
    (B : Blk sp.n Unit) : (acOnBlock sp v0 A Φ 56 B).1.locks = A.locks ∧
      (acOnBlock sp v0 A Φ 56 B).1.restartTime = A.restartTime := by
  obtain ⟨hl, hr⟩ := blockReceipt_locks_rt A 56 B
  have hnj : ¬ joined sp (blockReceipt sp A 56 B) 56 := not_joined_56 (hr.trans h)
  have hopt : optimisticConfirmation sp (blockReceipt sp A 56 B) Φ 56 = blockReceipt sp A 56 B := by
    refine optimisticConfirmation_none ?_
    unfold optimisticSelect
    rw [ite_eq_left (Or.inl hnj)]
  unfold acOnBlock
  rw [hopt]
  unfold tryVote
  dsimp only
  rw [ite_eq_left (Or.inl hnj)]
  exact ⟨hl, hr⟩

/-- **The restart keeps the locks**, for every replay order. -/
theorem restart_locks (ro : ReplayOrder sp Unit) (A : SAState sp.n) :
    (acRestart sp ro v0 A Φ 56).1.locks = A.locks := by
  unfold acRestart
  dsimp only
  suffices ∀ (l : List (Blk sp.n Unit)) (acc : SAState sp.n × List (Em sp Unit)),
      acc.1.restartTime = ((56 : Time) : WithBot Time) →
      (l.foldl (fun acc B => let r := acOnBlock sp v0 acc.1 Φ 56 B; (r.1, acc.2 ++ r.2))
        acc).1.locks = acc.1.locks from this _ _ rfl
  intro l
  induction l with
  | nil => exact fun _ _ => rfl
  | cons B l ih =>
    intro acc hacc
    rw [List.foldl_cons, ih _ (by dsimp only; rw [(acOnBlock_56 hacc B).2, hacc])]
    exact (acOnBlock_56 hacc B).1

/-- The live locks at a time of slot `14 = j₀ + k`, `15` from the locks a vetoed update leaves. -/
theorem liveLocks_at {t : Time} {L : Set Lock} (hL : ∀ l ∈ L, l.block ≤ 3) :
    liveLocks sp L Φ t = {l ∈ L | sp.slot t ≤ l.expiry} := by
  ext l'
  constructor
  · rintro ⟨l, hl, B, hB, hr, hlive, rfl⟩
    rw [viableAncestor_Φ hB, hr]
    exact ⟨hl, hlive⟩
  · rintro ⟨hl, hlive⟩
    obtain ⟨B, hB, hr⟩ := exists_root (hL l' hl)
    exact ⟨l', hl, B, hB, hr, hlive, by rw [viableAncestor_Φ hB, hr]⟩

/-- **At slot `j₀ + k = 14`, after the restart, the slow lock on `B1` is the node's only live
lock** (for every replay order): the lock on `Bv` (expiry `11`) and the fast lock on `B1`
(expiry `10`) have expired. -/
theorem live_at_j0k (ro : ReplayOrder sp Unit) :
    liveLocks sp (acRestart sp ro v0 S5 Φ 56).1.locks Φ 56 = {slowB1} := by
  rw [restart_locks, S5_locks, liveLocks_at (by
    rintro l (rfl | rfl | rfl) <;> decide), slot_56]
  ext l
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨rfl | rfl | rfl, h⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · rfl
  · rintro rfl
    exact ⟨Or.inr (Or.inr rfl), by decide⟩

/-- The lock on `Bv` is not live at slot `14`. -/
theorem lockV_expired : ¬ lockV.LiveAt sp 56 := by
  rw [Lock.LiveAt, slot_56]; decide

/-- **The anchor at slot `14` is the fork block `B1`.** -/
theorem anchor_at_j0k (ro : ReplayOrder sp Unit) :
    getAnchor sp (acRestart sp ro v0 S5 Φ 56).1 Φ 56 = B1 := by
  unfold getAnchor liveLockBlocks
  rw [live_at_j0k, deepest_top (D := B1) (Or.inl ⟨B1_mem, slowB1, rfl, rfl⟩) B1_mem]
  · rfl
  rintro C (⟨hC, l, rfl, hr⟩ | rfl)
  · rw [eq_of_root hC B1_mem hr.symm]
    exact Relation.ReflTransGen.refl
  · exact anc_g _ B1_mem

/-- The slow lock's expiry is exactly `s + k`: at slot `15` nothing is live. -/
theorem none_live_after (ro : ReplayOrder sp Unit) :
    liveLocks sp (acRestart sp ro v0 S5 Φ 56).1.locks Φ 60 = ∅ := by
  rw [restart_locks, S5_locks, liveLocks_at (by
    rintro l (rfl | rfl | rfl) <;> decide), slot_60]
  ext l
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨rfl | rfl | rfl, h⟩ <;> exact absurd h (by decide)

/-! ## Rejection control: the old rule, "a veto writes nothing" -/

open Classical in
/-- A local copy of the rule before 2(a): a vetoed update saves its result and writes nothing
else; otherwise it is the current update. (Not the spec; used only as a control.) -/
noncomputable def updateConfirmationOld (A : SAState sp.n) (Ψ : Frm sp.n Unit) (t : Time)
    (s : Nat) : SAState sp.n :=
  let C := getConfirmation sp A Ψ s
  let A₁ := { A with saved := Function.update A.saved s (C.map Block.root) }
  match C with
  | none => A₁
  | some C => if conflictsWithLock sp A₁.locks Ψ t C then A₁ else updateConfirmation sp A Ψ t s

/-- Under the old rule the vetoed update of slot `8` writes no lock. -/
theorem old_locks : (updateConfirmationOld S4 Φ 38 8).locks = {lockV} := by
  unfold updateConfirmationOld
  simp only [getConfirmation_8 fixed_S4]
  rw [ite_eq_left update_vetoed.2]
  exact S4_locks

/-- **Rejection control.** In the same run under the old rule, the node has **no** live lock
at slot `j₀ + k = 14`. -/
theorem old_live_at_j0k (ro : ReplayOrder sp Unit) :
    liveLocks sp (acRestart sp ro v0 (updateConfirmationOld S4 Φ 38 8) Φ 56).1.locks Φ 56 = ∅ := by
  rw [restart_locks, old_locks, liveLocks_at (by rintro l rfl; decide), slot_56]
  ext l
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨rfl, h⟩
  exact absurd h (by decide)

/-- Under the old rule the anchor at slot `14` falls back to `fc_root = g`. -/
theorem old_anchor_at_j0k (ro : ReplayOrder sp Unit) :
    getAnchor sp (acRestart sp ro v0 (updateConfirmationOld S4 Φ 38 8) Φ 56).1 Φ 56 = g := by
  unfold getAnchor liveLockBlocks
  rw [old_live_at_j0k, deepest_top (D := g) (Or.inr rfl) g_mem]
  · rfl
  rintro C (⟨-, l, hl, -⟩ | rfl)
  · exact absurd hl (Set.notMem_empty _)
  · exact Relation.ReflTransGen.refl

/-! ## The whole run -/

/-- **The veto run.** From `S0` at `t_9 = 36`: the tick and three slot-`9` messages on `Bv` (the
third gives the optimistic lock on `Bv`, expiry `11`); the tick at `37` (own vote on `Bv`); the
tick at `38` (the update of slot `8`, vetoed by that lock, writes the slow lock on `B1` with
expiry `8 + k = 14` under 2(a)); sleep; the restart at `t_14 = 56` with any replay order. At slot
`14` the node's only live lock is the slow lock on `B1`, and its anchor is `B1`. -/
theorem veto_run (ro : ReplayOrder sp Unit) :
    acOnTick sp v0 S0 Φ 36 = (S0, []) ∧
    acOnMessage sp v0 S0 Φ 36 (vv v1) = (S1, []) ∧
    acOnMessage sp v0 S1 Φ 36 (vv v2) = (S2, []) ∧
    acOnMessage sp v0 S2 Φ 36 (vv v3) = (S3, []) ∧ S3.locks = {lockV} ∧
    (acOnTick sp v0 S3 Φ 37).1 = S4 ∧
    acOnTick sp v0 S4 Φ 38 = (S5, []) ∧ conflictsWithLock sp S4.locks Φ 38 Bc ∧
    S5.locks = {lockV, fastB1, slowB1} ∧
    liveLocks sp (acRestart sp ro v0 S5 Φ 56).1.locks Φ 56 = {slowB1} ∧
    getAnchor sp (acRestart sp ro v0 S5 Φ 56).1 Φ 56 = B1 :=
  ⟨tick_36 S0, msg_1, msg_2, msg_3, S3_locks, tick_37, tick_38 fixed_S4, update_vetoed.2,
    S5_locks, live_at_j0k ro, anchor_at_j0k ro⟩

end Consensus.Goldilocks.SA.Test.GradedVeto
