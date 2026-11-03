module
public import ConsensusLeanTest.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
public import ConsensusLean.Instances.Goldilocks.Proofs.ACSteps.Main
@[expose] public section

/-! # Witnesses for the premises of the Goldilocks optimistic-path ACSteps statements

Review item B3-O1: the hypotheses of A1.4 (a) `OptimisticTransfer`, A1.4 (b)
`OptimisticNextUpdate` and A1.5 `SourceAge` (`Statements/AC/Steps.lean`) hold together of one
concrete run, so none of the three proved milestones is vacuous. The parameters are
`GoldilocksAC`'s (one validator `v0`, `Δ = 1`, `t_s = 4s`, `k = 2`, genesis `g` of root `0`).

The frame of every call is `Φ₁`: tree `{g, B1}` with `B1` the slot-`1` block on `g` (root `1`,
empty payloads), `F = fc_root = g`, viable heads `{B1}`. The coherent set is `U₁ = {g, B1}`, the
honest set all of `Fin 1`, the slot proposer `v0`. `v0` is awake throughout and never restarts.
The run `trW` (each post-state the call's literal output, threaded):

| cut | time | call | effect |
|---|---|---|---|
| 0 | `4 = t_1` | `ac_on_block(B1)` | stamp `4`; vote `(v0, 1, B1)`; optimistic lock (slot 1) |
| 1 | `9 = t_2 + Δ` | `ac_on_tick` | vote `(v0, 2, B1)`; optimistic lock (slot 2) |
| 2 | `12 = t_3` | `ac_to_fg` | returns `B1` (live fast lock of slot `1 ≥ slot(12) − 2`) |
| 3 | `14 = t_2 + 6Δ` | `ac_on_tick` | the update of slot `2` |

`*_premises_satisfiable` state, for each statement at `sp1`, `FGP := Unit`, `ro1`, that there are
values of all its universally bound variables satisfying `ACRun` and every hypothesis (copied from
the statement); `*_on_witness` apply the proved milestones (`acStepsAt`) to the run. -/

namespace Consensus.Goldilocks.SA.Test

/-! ## The frame -/

/-- The block of slot `1`: root `1`, parent genesis, proposer `v0`, empty payloads. -/
def B1 : Blk sp1.n Unit := ⟨1, some 0, 1, v0, 0, (), ([], [])⟩

/-- The coherent set of the run: genesis and `B1`. -/
def U₁ : Set (Blk sp1.n Unit) := {g, B1}

/-- The frame of every call: tree `{genesis, B1}`, `F = fc_root = genesis`, viable heads `{B1}`. -/
def Φ₁ : Frm sp1.n Unit := ⟨U₁, g, g, {B1}⟩

theorem g_ne_B1 : g ≠ B1 := fun h => absurd (congrArg Block.root h) (by simp [g, B1])

theorem coherent_U₁ : Coherent U₁ := by
  refine ⟨?_, ?_⟩
  · rintro X (rfl | rfl) Y (rfl | rfl) h <;> first | rfl | simp [g, B1] at h
  · rintro X (rfl | rfl) Y (rfl | rfl) h <;> simp [g, B1] at h ⊢

theorem g_mem : g ∈ U₁ := Or.inl rfl

theorem B1_mem : B1 ∈ U₁ := Or.inr rfl

theorem anc_g_B1 : Anc U₁ g B1 := Relation.ReflTransGen.single ⟨g_mem, B1_mem, rfl⟩

theorem not_anc_B1_g : ¬ Anc U₁ B1 g := fun h => by
  have := (h.slot_le coherent_U₁).1
  simp [g, B1] at this

theorem anc_B1_of_mem {X : Blk sp1.n Unit} (hX : X ∈ U₁) : Anc U₁ X B1 := by
  rcases hX with rfl | rfl
  · exact anc_g_B1
  · exact Relation.ReflTransGen.refl

theorem anc_g_of_mem {X : Blk sp1.n Unit} (hX : X ∈ U₁) : Anc U₁ g X := by
  rcases hX with rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact anc_g_B1

theorem mem_of_anc_U₁ {X Y : Blk sp1.n Unit} (h : Anc U₁ X Y) (hY : Y ∈ U₁) : X ∈ U₁ := by
  by_cases hXY : X = Y
  · exact hXY ▸ hY
  · exact (Anc.mem h hXY).1

theorem compatible_U₁ {X Y : Blk sp1.n Unit} (hX : X ∈ U₁) (hY : Y ∈ U₁) : Compatible U₁ X Y := by
  rcases hX with rfl | rfl
  · exact Or.inl (anc_g_of_mem hY)
  · exact Or.inr (anc_B1_of_mem hY)

/-- The frame is well formed. -/
theorem frameOK_Φ₁ : FrameOK Φ₁ where
  finite := (Set.finite_singleton B1).insert g
  coherent := coherent_U₁
  rooted := ⟨g_mem, fun _ hC => anc_g_of_mem hC⟩
  fcRoot_mem := g_mem
  F_anc_fcRoot := Relation.ReflTransGen.refl
  viableHeads_subset := Set.singleton_subset_iff.2 B1_mem
  fcRoot_anc_viableHeads := fun W hW => by rw [Set.mem_singleton_iff.1 hW]; exact anc_g_B1

/-- The genesis frame steps to `Φ₁` by accepting `B1`. -/
theorem frameStep_Φ₁ : FrameStep Φ₀ B1 Φ₁ where
  new := fun h => g_ne_B1 (Set.mem_singleton_iff.1 h).symm
  parent_mem := ⟨g, rfl, rfl⟩
  F_anc_F' := Relation.ReflTransGen.refl
  F'_anc_B := Relation.ReflTransGen.single ⟨Or.inr rfl, Or.inl rfl, rfl⟩
  tree_eq := by
    ext X
    constructor
    · rintro (rfl | rfl)
      · exact ⟨Or.inr rfl, Relation.ReflTransGen.refl⟩
      · exact ⟨Or.inl rfl, Relation.ReflTransGen.single ⟨Or.inr rfl, Or.inl rfl, rfl⟩⟩
    · rintro ⟨h | h, -⟩
      · exact Or.inr h
      · exact Or.inl h

theorem B1_viable {S : Set (Blk sp1.n Unit)} (h : B1 ∈ S) : B1 ∈ Φ₁.viableTree S :=
  ⟨h, anc_g_B1, B1, h, rfl, Relation.ReflTransGen.refl⟩

/-! ## Times -/

theorem slot_4 : sp1.slot 4 = 1 := by decide
theorem slot_9 : sp1.slot 9 = 2 := by decide
theorem slot_12 : sp1.slot 12 = 3 := by decide
theorem slot_14 : sp1.slot 14 = 3 := by decide
theorem slot_0 : sp1.slot 0 = 0 := by decide

/-! ## The SA on `Φ₁` -/

theorem joined_bot {A : SAState sp1.n} (h : A.restartTime = ⊥) (t : Time) : joined sp1 A t := by
  unfold joined; rw [h]; exact bot_le

theorem lookup_B1 : lookup Φ₁ 1 = some B1 := by
  cases h : lookup Φ₁ 1 with
  | none => exact absurd ⟨B1, B1_mem, rfl⟩ (lookup_eq_none h)
  | some B =>
    obtain ⟨hB, hr⟩ := lookup_eq_some h
    exact congrArg some (coherent_U₁.1 hB B1_mem hr)

theorem deepest_eq_of_isDeepest {S : Set (Blk sp1.n Unit)} {D : Blk sp1.n Unit}
    (h : IsDeepest Φ₁ S D) : deepest Φ₁ S = some D := by
  have hex : ∃ B, IsDeepest Φ₁ S B := ⟨D, h⟩
  unfold deepest
  rw [dite_eq_left hex]
  congr 1
  have hc := hex.choose_spec
  by_contra hne
  rcases hc.2 D h.1 (Ne.symm hne) with h₁ | ⟨h₁, h₁'⟩ <;>
    rcases h.2 _ hc.1 hne with h₂ | ⟨h₂, h₂'⟩ <;> omega

/-- The deepest block of a set of blocks of the tree that holds `B1` is `B1`. -/
theorem deepest_B1 {S : Set (Blk sp1.n Unit)} (hS : S ⊆ U₁) (hB : B1 ∈ S) :
    deepest Φ₁ S = some B1 :=
  deepest_eq_of_isDeepest ⟨hB, fun _ hC hne =>
    Or.inl (depth_lt_of_anc frameOK_Φ₁ (anc_B1_of_mem (hS hC)) hne B1_mem)⟩

theorem deepest_empty : deepest Φ₁ (∅ : Set (Blk sp1.n Unit)) = none := by
  unfold deepest
  rw [dite_eq_right]
  rintro ⟨B, hB, -⟩
  exact hB

theorem viableAncestor_B1 : Φ₁.viableAncestor B1 = B1 :=
  viableAncestor_self frameOK_Φ₁ B1_mem (Or.inl (B1_viable B1_mem))

/-- Live locks on `B1` stay as they are. -/
theorem liveLocks_eq {L : Set Lock} {t : Time}
    (hL : ∀ l ∈ L, l.block = 1 ∧ sp1.slot t ≤ l.slot + 2) : liveLocks sp1 L Φ₁ t = L := by
  ext l'
  constructor
  · rintro ⟨l, hl, B, hB, hr, -, rfl⟩
    obtain rfl : B = B1 := by
      rcases hB with rfl | rfl
      · rw [(hL l hl).1] at hr; simp [g] at hr
      · rfl
    rw [viableAncestor_B1]
    obtain ⟨b, s, f⟩ := l
    obtain rfl : b = 1 := (hL _ hl).1
    exact hl
  · intro hl
    refine ⟨l', hl, B1, B1_mem, (hL l' hl).1.symm, (hL l' hl).2, ?_⟩
    rw [viableAncestor_B1]
    obtain ⟨b, s, f⟩ := l'
    obtain rfl : b = 1 := (hL _ hl).1
    rfl

theorem not_conflicts {L : Set Lock} {t : Time} {B : Blk sp1.n Unit} (hB : B ∈ U₁) :
    ¬ conflictsWithLock sp1 L Φ₁ t B :=
  fun ⟨_, hC, hnc⟩ => hnc (compatible_U₁ hB hC.1)

theorem getAnchor_mem (A : SAState sp1.n) (t : Time) : getAnchor sp1 A Φ₁ t ∈ U₁ := by
  unfold getAnchor
  cases h : deepest Φ₁ (liveLockBlocks sp1 A.locks Φ₁ t ∪ {Φ₁.fcRoot}) with
  | none => exact g_mem
  | some D =>
    rcases (deepest_mem h).1 with hD | hD
    · exact hD.1
    · rw [Set.mem_singleton_iff.1 hD]; exact g_mem

theorem ghost_B1 {T : Set (Blk sp1.n Unit)} (hT : T ⊆ U₁) (sc : Blk sp1.n Unit → Nat)
    (el : Blk sp1.n Unit → Prop) : ∀ f, ghost sp1 T sc el f B1 = B1
  | 0 => rfl
  | f + 1 => by
    rw [ghost, dite_eq_right]
    rintro ⟨C, ⟨hC, hpar, -⟩, -⟩
    rcases hT hC with rfl | rfl <;> simp [g, B1] at hpar

/-- Every head walk of a domain that holds `B1` ends at `B1`. -/
theorem getHead_eq {T : Set (Blk sp1.n Unit)} (hT : T ⊆ U₁) (hB : B1 ∈ T) (A : SAState sp1.n)
    (t : Time) (V : View sp1.n) (s : Int) : getHead sp1 A Φ₁ t T V s = B1 := by
  unfold getHead
  rcases getAnchor_mem A t with h | h
  · rw [h, show Φ₁.tree.ncard = 1 + 1 from Set.ncard_pair g_ne_B1, ghost_add 1 1,
      ghost_succ_of_best 0 g (C := B1) ?_, ghost_B1 hT]
    refine ⟨⟨hB, rfl, Or.inl ?_⟩, fun D ⟨hD, hpar, _⟩ hne => absurd ?_ hne⟩
    · rintro ⟨W, hW, hp⟩
      rw [Set.mem_singleton_iff.1 hW] at hp
      simp [B1] at hp
    · rcases hT hD with rfl | rfl
      · simp [g] at hpar
      · rfl
  · rw [Set.mem_singleton_iff.1 h]
    exact ghost_B1 hT _ _ _

/-- Unlocking keeps live locks on `B1` of a slot at least `s`. -/
theorem unlock_eq {L : Set Lock} {t : Time} {s : Int} (V : View sp1.n)
    (hL : ∀ l ∈ L, l.block = 1 ∧ sp1.slot t ≤ l.slot + 2 ∧ s ≤ l.slot) :
    unlock sp1 L Φ₁ t s V = L := by
  have hlive := liveLocks_eq (L := L) (t := t) fun l hl => ⟨(hL l hl).1, (hL l hl).2.1⟩
  ext l'
  constructor
  · rintro ⟨l, hl, B, -, -, rfl⟩
    rw [hlive] at hl
    rw [ite_eq_right (not_lt.2 (hL l hl).2.2)]
    exact hl
  · intro hl
    refine ⟨l', hlive.symm ▸ hl, B1, B1_mem, (hL l' hl).1.symm, ?_⟩
    rw [ite_eq_right (not_lt.2 (hL l' hl).2.2)]

theorem ncard_univ_v : (Set.univ : Set (Fin sp1.n)).ncard = 1 := by simp

/-- The optimistic check selects `B1` once the pool of the slot holds a vote on `B1`. -/
theorem optimisticSelect_B1 {A : SAState sp1.n} {t : Time} (hj : A.restartTime = ⊥)
    (hs : sp1.slot t ≠ 0) (ht : t < sp1.ts (sp1.slot t) + 2 * sp1.Δ)
    (hx : ∃ x ∈ A.pool (sp1.slot t), x.head = 1) : optimisticSelect sp1 A Φ₁ t = some B1 := by
  unfold optimisticSelect
  dsimp only
  rw [ite_eq_right fun h => by
    rcases h with h | h | h
    · exact h (joined_bot hj t)
    · exact hs h
    · exact absurd h (not_le.2 ht)]
  refine deepest_B1 (fun B hB => hB.1) ⟨B1_mem, ?_, not_conflicts B1_mem⟩
  have : optimisticVoters sp1 A Φ₁ (sp1.slot t) B1 = Set.univ := by
    obtain ⟨x, hx, hh⟩ := hx
    exact Set.eq_univ_of_forall fun i =>
      ⟨x, hx, Subsingleton.elim _ _, B1, B1_mem, hh.symm, Relation.ReflTransGen.refl⟩
  rw [this, ncard_univ_v]
  decide

theorem optimisticSelect_none {A : SAState sp1.n} {t : Time} (h : A.pool (sp1.slot t) = []) :
    optimisticSelect sp1 A Φ₁ t = none := by
  unfold optimisticSelect
  dsimp only
  split_ifs
  · rfl
  · convert deepest_empty
    ext B
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, h3, -⟩
    have : optimisticVoters sp1 A Φ₁ (sp1.slot t) B = ∅ := by
      ext i; simp [optimisticVoters, h]
    rw [this] at h3
    simp at h3

theorem optimisticConfirmation_none {A : SAState sp1.n} {t : Time}
    (h : optimisticSelect sp1 A Φ₁ t = none) : optimisticConfirmation sp1 A Φ₁ t = A := by
  unfold optimisticConfirmation; rw [h]

theorem optimisticConfirmation_some {A : SAState sp1.n} {t : Time}
    (h : optimisticSelect sp1 A Φ₁ t = some B1) : optimisticConfirmation sp1 A Φ₁ t =
      updateLatestConfirmed sp1
        { A with locks := addLocks sp1 A.locks Φ₁ t (sp1.slot t) {(B1.root, true)} } Φ₁ B1 := by
  unfold optimisticConfirmation; rw [h]

theorem updateLatestConfirmed_new {A : SAState sp1.n} (h : A.latestConfirmed = 0) :
    updateLatestConfirmed sp1 A Φ₁ B1 = { A with latestConfirmed := 1 } := by
  unfold updateLatestConfirmed
  rw [ite_eq_right]
  · rfl
  rintro ⟨R, hR, hr, hanc⟩
  rcases hR with rfl | rfl
  · exact not_anc_B1_g hanc
  · rw [h] at hr; simp [B1] at hr

theorem updateLatestConfirmed_keep {A : SAState sp1.n} (h : A.latestConfirmed = 1) :
    updateLatestConfirmed sp1 A Φ₁ B1 = A := by
  unfold updateLatestConfirmed
  rw [ite_eq_left ⟨B1, B1_mem, h.symm, Relation.ReflTransGen.refl⟩]

theorem admitVote_fresh (A : SAState sp1.n) (t : Time) (v : Vote sp1.n) (hs : sp1.slot t = v.slot)
    (hp : A.pool v.slot = []) : admitVote sp1 A t v = { A with
      pool := Function.update A.pool v.slot [v]
      voteStamp := Function.update A.voteStamp v (ETime.of t) } := by
  unfold admitVote
  rw [ite_eq_right (by rw [hs, hp]; simp), ite_eq_right (by rw [hp]; simp), hp]
  rfl

/-! ## The run -/

/-- The slot-`1` vote of `v0`, on `B1`. -/
def vote1 : Vote sp1.n := ⟨v0, 1, 1⟩

/-- The slot-`2` vote of `v0`, on `B1`. -/
def vote2 : Vote sp1.n := ⟨v0, 2, 1⟩

/-- The optimistic fast lock of slot `1` on `B1`. -/
def lock1 : Lock := ⟨1, 1, true⟩

/-- The optimistic fast lock of slot `2` on `B1`. -/
def lock2 : Lock := ⟨1, 2, true⟩

/-- Cut 0: `ac_on_block(B1)` at `t_1 = 4`. -/
noncomputable def r0 : SAState sp1.n × List (Em sp1 Unit) :=
  acOnBlock sp1 v0 (SAState.initial 0) Φ₁ 4 B1

/-- Cut 1: `ac_on_tick` at `t_2 + Δ = 9`. -/
noncomputable def r1 : SAState sp1.n × List (Em sp1 Unit) := acOnTick sp1 v0 r0.1 Φ₁ 9

/-- Cut 2: `ac_to_fg` at `t_3 = 12`. -/
noncomputable def r2 : SAState sp1.n × Option (Blk sp1.n Unit) :=
  acToFG sp1 r1.1 Φ₁ 12

/-- Cut 3: `ac_on_tick` at `t_3 + 2Δ = 14` (the update of slot `2`). -/
noncomputable def r3 : SAState sp1.n × List (Em sp1 Unit) := acOnTick sp1 v0 r2.1 Φ₁ 14

theorem voteDomain_sub (A : SAState sp1.n) (s : Nat) : voteDomain sp1 A Φ₁ s ⊆ U₁ := by
  rintro B (⟨h, -⟩ | ⟨h, -⟩)
  · exact h.1
  · exact h

/-- Adding a fast lock on `B1` to live locks on `B1`. -/
theorem addLocks_eq {L : Set Lock} {t : Time} {s : Nat}
    (hL : ∀ l ∈ L, l.block = 1 ∧ sp1.slot t ≤ l.slot + 2) (hs : sp1.slot t ≤ s + 2) :
    addLocks sp1 L Φ₁ t s {(B1.root, true)} = insert ⟨1, s, true⟩ L := by
  unfold addLocks
  rw [liveLocks_eq]
  · ext l
    simp [B1, or_comm]
  · rintro l (hl | ⟨p, hp, rfl⟩)
    · exact hL l hl
    · rw [Set.mem_singleton_iff.1 hp]
      exact ⟨rfl, hs⟩

/-- The state after the unlocking of a vote at `t`. -/
noncomputable def unlocked (A : SAState sp1.n) (t : Time) : SAState sp1.n :=
  { A with
    locks := unlock sp1 A.locks Φ₁ t ((sp1.slot t : Int) - 1)
      (mergedVoteView sp1 A Φ₁ (sp1.slot t)) }

/-- A vote of `v0` in slot `s > 0` at `t`: the head is `B1`. -/
theorem tryVote_cast (A : SAState sp1.n) (t : Time) (hs0 : 0 < sp1.slot t)
    (hj : A.restartTime = ⊥) (hv : A.votedSlot ≠ sp1.slot t)
    (ht : t ≤ sp1.ts (sp1.slot t) + sp1.Δ)
    (hr : ¬ (t < sp1.ts (sp1.slot t) + sp1.Δ ∧
      (sp1.slot t = 0 ∨ ¬ voteReady sp1 Φ₁ (sp1.slot t))))
    (hdom : B1 ∈ voteDomain sp1 (unlocked A t) Φ₁ (sp1.slot t)) :
    ∃ d, tryVote sp1 v0 A Φ₁ t =
      (optimisticConfirmation sp1 (admitVote sp1 { unlocked A t with votedSlot := sp1.slot t } t
        ⟨v0, sp1.slot t, 1⟩) Φ₁ t,
       [⟨⟨v0, sp1.slot t, 1⟩, { unlocked A t with votedSlot := sp1.slot t }, some d⟩]) := by
  unfold tryVote
  rw [ite_eq_right (fun h => by
      rcases h with h | h | h
      · exact h (joined_bot hj t)
      · exact hv h
      · exact absurd h (not_lt.2 ht)), ite_eq_right hr]
  dsimp only
  have hh := getHead_eq (fun _ hB => voteDomain_sub _ _ hB.1) (B1_viable hdom)
  unfold unlocked at hh
  rw [ite_eq_left hs0, hh]
  exact ⟨_, rfl⟩

/-- The state after the receipt of `B1`. -/
def Rb : SAState sp1.n :=
  { SAState.initial 0 with
    blockStamp := Function.update (SAState.initial 0 : SAState sp1.n).blockStamp 1 (ETime.of 4) }

/-- The read point of the slot-`1` vote. -/
def R0 : SAState sp1.n := { Rb with votedSlot := 1 }

/-- The state after cut 0. -/
def S1 : SAState sp1.n :=
  { R0 with
    pool := Function.update R0.pool 1 [vote1]
    voteStamp := Function.update R0.voteStamp vote1 (ETime.of 4)
    locks := insert lock1 ∅
    latestConfirmed := 1 }

theorem voteReady_1 : voteReady sp1 Φ₁ 1 :=
  ⟨B1, B1_mem, rfl, fun x hx => by cases hx⟩

theorem B1_mem_voteDomain {A : SAState sp1.n} {s : Nat}
    (h : B1 ∈ voterBlockTree sp1 A Φ₁ s) : B1 ∈ voteDomain sp1 A Φ₁ s :=
  Or.inl ⟨h, B1, B1_viable h⟩

theorem unlocked_Rb : unlocked Rb 4 = Rb := by
  unfold unlocked
  rw [unlock_eq _ (fun l hl => hl.elim)]

theorem r0_eq : ∃ d, r0 = (S1, [⟨vote1, R0, some d⟩]) := by
  unfold r0 acOnBlock
  rw [show blockReceipt sp1 (SAState.initial 0) 4 B1 = Rb from rfl,
    optimisticConfirmation_none (optimisticSelect_none (by rw [slot_4]; rfl))]
  have hr : ¬ ((4 : Time) < sp1.ts (sp1.slot 4) + sp1.Δ ∧
      (sp1.slot 4 = 0 ∨ ¬ voteReady sp1 Φ₁ (sp1.slot 4))) := by
    rw [slot_4]
    rintro ⟨-, h | h⟩
    · exact absurd h (by decide)
    · exact h voteReady_1
  have hdom : B1 ∈ voteDomain sp1 (unlocked Rb 4) Φ₁ (sp1.slot 4) := by
    rw [slot_4]
    exact B1_mem_voteDomain ⟨B1_mem, Or.inr ⟨B1, B1_mem, rfl, Relation.ReflTransGen.refl⟩⟩
  obtain ⟨d, hd⟩ := tryVote_cast Rb 4 (by rw [slot_4]; decide) rfl (by rw [slot_4]; decide)
    (by rw [slot_4]; decide) hr hdom
  refine ⟨d, ?_⟩
  rw [hd, unlocked_Rb, slot_4]
  change (optimisticConfirmation sp1 (admitVote sp1 R0 4 vote1) Φ₁ 4,
    ([⟨vote1, R0, some d⟩] : List (Em sp1 Unit))) = _
  have hsel : optimisticSelect sp1 { R0 with
      pool := Function.update R0.pool vote1.slot [vote1]
      voteStamp := Function.update R0.voteStamp vote1 (ETime.of 4) } Φ₁ 4 = some B1 :=
    optimisticSelect_B1 rfl (by rw [slot_4]; decide) (by rw [slot_4]; decide)
      ⟨vote1, by rw [slot_4]; simp [vote1], rfl⟩
  rw [admitVote_fresh R0 4 vote1 slot_4 rfl, optimisticConfirmation_some hsel,
    addLocks_eq (fun l hl => hl.elim) (by rw [slot_4]; decide), updateLatestConfirmed_new rfl,
    slot_4]
  rfl

theorem acOnTick_vote {A : SAState sp1.n} {t : Time} (hj : A.restartTime = ⊥)
    (h1 : t = sp1.ts (sp1.slot t) + sp1.Δ) : acOnTick sp1 v0 A Φ₁ t = tryVote sp1 v0 A Φ₁ t := by
  have hΔ : sp1.Δ = 1 := rfl
  unfold acOnTick
  dsimp only
  rw [ite_eq_right (not_not.2 (joined_bot hj t)), ite_eq_left h1,
    ite_eq_right (fun h => by linarith [h.1])]

theorem acOnTick_update {A : SAState sp1.n} {t : Time} (hj : A.restartTime = ⊥)
    (h1 : t ≠ sp1.ts (sp1.slot t) + sp1.Δ) (h2 : t = sp1.ts (sp1.slot t) + 2 * sp1.Δ)
    (hs : 0 < sp1.slot t) :
    acOnTick sp1 v0 A Φ₁ t = (updateConfirmation sp1 A Φ₁ t (sp1.slot t - 1), []) := by
  unfold acOnTick
  dsimp only
  rw [ite_eq_right (not_not.2 (joined_bot hj t)), ite_eq_right h1, ite_eq_left ⟨h2, hs⟩]

theorem updateConfirmation_pool (A : SAState sp1.n) (t : Time) (s : Nat) :
    (updateConfirmation sp1 A Φ₁ t s).pool = A.pool := by
  unfold updateConfirmation
  dsimp only
  split
  · rfl
  · split_ifs
    · rfl
    · unfold updateLatestConfirmed
      split_ifs <;> rfl

/-- The read point of the slot-`2` vote. -/
def R1 : SAState sp1.n := { S1 with votedSlot := 2 }

/-- The state after cut 1. -/
def S2 : SAState sp1.n :=
  { R1 with
    pool := Function.update R1.pool 2 [vote2]
    voteStamp := Function.update R1.voteStamp vote2 (ETime.of 9)
    locks := insert lock2 S1.locks }

/-- The state after cut 2. -/
def S3 : SAState sp1.n := { S2 with fgReported := 1 }

theorem mem_S1_locks {l : Lock} (hl : l ∈ S1.locks) : l = lock1 := by
  rcases hl with rfl | h
  · rfl
  · exact h.elim

theorem unlocked_S1 : unlocked S1 9 = S1 := by
  unfold unlocked
  rw [unlock_eq]
  intro l hl
  rw [mem_S1_locks hl, slot_9]
  exact ⟨rfl, by decide, by decide⟩

theorem r1_eq : ∃ d, r1 = (S2, [⟨vote2, R1, some d⟩]) := by
  obtain ⟨d0, h0⟩ := r0_eq
  unfold r1
  rw [h0]
  dsimp only
  rw [acOnTick_vote rfl (by rw [slot_9]; decide)]
  have hr : ¬ ((9 : Time) < sp1.ts (sp1.slot 9) + sp1.Δ ∧
      (sp1.slot 9 = 0 ∨ ¬ voteReady sp1 Φ₁ (sp1.slot 9))) := by
    rw [slot_9]
    rintro ⟨h, -⟩
    exact absurd h (by decide)
  have hdom : B1 ∈ voteDomain sp1 (unlocked S1 9) Φ₁ (sp1.slot 9) := by
    rw [unlocked_S1, slot_9]
    refine B1_mem_voteDomain ⟨B1_mem, Or.inl ?_⟩
    change ETime.of 4 < ETime.of (sp1.ts ((2 : Nat) - 1 : Int) + 3 * sp1.Δ)
    decide
  obtain ⟨d, hd⟩ := tryVote_cast S1 9 (by rw [slot_9]; decide) rfl (by rw [slot_9]; decide)
    (by rw [slot_9]; decide) hr hdom
  refine ⟨d, ?_⟩
  rw [hd, unlocked_S1, slot_9]
  change (optimisticConfirmation sp1 (admitVote sp1 R1 9 vote2) Φ₁ 9,
    ([⟨vote2, R1, some d⟩] : List (Em sp1 Unit))) = _
  have hsel : optimisticSelect sp1 { R1 with
      pool := Function.update R1.pool vote2.slot [vote2]
      voteStamp := Function.update R1.voteStamp vote2 (ETime.of 9) } Φ₁ 9 = some B1 :=
    optimisticSelect_B1 rfl (by rw [slot_9]; decide) (by rw [slot_9]; decide)
      ⟨vote2, by rw [slot_9]; simp [vote2], rfl⟩
  rw [admitVote_fresh R1 9 vote2 slot_9 rfl, optimisticConfirmation_some hsel,
    addLocks_eq (fun l hl => by rw [mem_S1_locks hl, slot_9]; exact ⟨rfl, by decide⟩)
      (by rw [slot_9]; decide), updateLatestConfirmed_keep rfl, slot_9]
  rfl

theorem notAncR_B1_0 : ¬ AncR Φ₁ B1 0 := by
  rintro ⟨R, hR, hr, hanc⟩
  rcases hR with rfl | rfl
  · exact not_anc_B1_g hanc
  · simp [B1] at hr

theorem toFG_S2 : (acToFG sp1 S2 Φ₁ 12).1 = S3 ∧ (acToFG sp1 S2 Φ₁ 12).2 = some B1 := by
  have hc : deepest Φ₁ (toFGCandidates sp1 S2 Φ₁ 12) = some B1 := by
    refine deepest_B1 (fun B hB => hB.1.1) ⟨B1_viable B1_mem, lock1, ?_, rfl, rfl, ?_⟩
    · rw [liveLocks_eq]
      · exact Or.inr (Or.inl rfl)
      · rintro l (rfl | hl)
        · rw [slot_12]; exact ⟨rfl, by decide⟩
        · rw [mem_S1_locks hl, slot_12]; exact ⟨rfl, by decide⟩
    · rw [slot_12]; decide
  unfold acToFG
  rw [ite_eq_right (not_not.2 (joined_bot rfl 12)), hc]
  dsimp only
  rw [ite_eq_right (show ¬ AncR Φ₁ B1 S2.fgReported from notAncR_B1_0)]
  exact ⟨rfl, rfl⟩

theorem r3_eq : r3 = (updateConfirmation sp1 S3 Φ₁ 14 2, []) := by
  obtain ⟨d, h1⟩ := r1_eq
  unfold r3 r2
  rw [h1]
  dsimp only
  rw [toFG_S2.1, acOnTick_update rfl (by rw [slot_14]; decide) (by rw [slot_14]; decide)
    (by rw [slot_14]; decide), slot_14]

/-- The vote emission of cut 0. -/
noncomputable def e0 : Em sp1 Unit := ⟨vote1, R0, some (Classical.choose r0_eq)⟩

/-- The vote emission of cut 1. -/
noncomputable def e1 : Em sp1 Unit := ⟨vote2, R1, some (Classical.choose r1_eq)⟩

theorem r0_eq' : r0 = (S1, [e0]) := Classical.choose_spec r0_eq

theorem r1_eq' : r1 = (S2, [e1]) := Classical.choose_spec r1_eq

/-- The label of cut 0. -/
noncomputable def ℓ0 : ACLabel GA1 := ⟨.block B1, Φ₁, r0.2⟩

/-- The label of cut 1. -/
noncomputable def ℓ1 : ACLabel GA1 := ⟨.tick, Φ₁, r1.2⟩

/-- The label of cut 2. -/
noncomputable def ℓ2 : ACLabel GA1 := ⟨.toFG, Φ₁, []⟩

/-- The label of cut 3. -/
noncomputable def ℓ3 : ACLabel GA1 := ⟨.tick, Φ₁, r3.2⟩

/-- The run: `v0` accepts `B1` at `t_1 = 4` (its slot-`1` vote and optimistic lock), ticks at
`t_2 + Δ = 9` (its slot-`2` vote and optimistic lock), calls `ac_to_fg` at `t_3 = 12` and ticks at
`t_2 + 6Δ = 14` (the update of slot `2`); every post-state is the call's output. -/
noncomputable def trW : SATrace sp1 Unit ro1 where
  init := fun _ => SAState.initial 0
  node := fun _ => v0
  time := fun i => if i = 0 then 4 else if i = 1 then 9 else if i = 2 then 12 else 14
  event := fun i => i
  pos := fun _ => 0
  label := fun i => match i with
    | 0 => some ℓ0
    | 1 => some ℓ1
    | 2 => some ℓ2
    | 3 => some ℓ3
    | _ => none
  post := fun i => match i with
    | 0 => r0.1
    | 1 => r1.1
    | 2 => r2.1
    | _ => r3.1
  awake := fun _ _ => True

theorem trW_label {i : Nat} {ℓ : ACLabel GA1} (h : trW.label i = some ℓ) :
    (i = 0 ∧ ℓ = ℓ0) ∨ (i = 1 ∧ ℓ = ℓ1) ∨ (i = 2 ∧ ℓ = ℓ2) ∨ (i = 3 ∧ ℓ = ℓ3) := by
  rcases i with _ | _ | _ | _ | i <;> simp [trW] at h <;> simp [h]

theorem trW_frame {i : Nat} {ℓ : ACLabel GA1} (h : trW.label i = some ℓ) : ℓ.frame = Φ₁ := by
  rcases trW_label h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl

theorem trW_time_mono : Monotone trW.time := by
  intro a b h
  simp only [trW]
  split_ifs <;> first | omega | norm_num

theorem trW_state_succ (y : Fin sp1.n) {i : Nat} (hi : i ≤ 3) :
    trW.state y (i + 1) = trW.post i := by
  simp only [Trace.state]
  rw [ite_eq_left ⟨Subsingleton.elim _ _, by
    rcases i with _ | _ | _ | _ | i <;> first | omega | simp [trW]⟩]

theorem trW_state_1 (y : Fin sp1.n) : trW.state y 1 = S1 := by
  rw [trW_state_succ y (by decide)]; exact congrArg Prod.fst r0_eq'

theorem trW_state_2 (y : Fin sp1.n) : trW.state y 2 = S2 := by
  rw [trW_state_succ y (by decide)]; exact congrArg Prod.fst r1_eq'

theorem trW_state_3 (y : Fin sp1.n) : trW.state y 3 = S3 := by
  rw [trW_state_succ y (by decide)]
  change r2.1 = S3
  unfold r2
  rw [r1_eq']
  exact toFG_S2.1

theorem trW_state_late (y : Fin sp1.n) (i : Nat) :
    trW.state y (i + 4) = updateConfirmation sp1 S3 Φ₁ 14 2 := by
  induction i with
  | zero =>
    rw [trW_state_succ y le_rfl]
    exact congrArg Prod.fst r3_eq
  | succ i ih =>
    change trW.state y (i + 4 + 1) = _
    rw [Trace.state.eq_2, ite_eq_right (fun h => h.2 (by simp [trW])), ih]

theorem trW_no_restart (y : Fin sp1.n) (k : Nat) : ¬ trW.RestartAt y k := by
  rintro ⟨ℓ, ⟨-, h⟩, hc⟩
  rcases trW_label h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases hc

theorem trW_lastWake (y : Fin sp1.n) (k : Nat) : trW.lastWake y k = ⊥ := by
  induction k with
  | zero => simp only [ACTrace.lastWake]; rw [ite_eq_right (trW_no_restart y 0)]
  | succ k ih => simp only [ACTrace.lastWake]; rw [ite_eq_right (trW_no_restart y _), ih]

theorem trW_deadline (y : Fin sp1.n) (k : Nat) (τ : Time) : trW.deadline y k τ = τ + 1 := by
  unfold ACTrace.deadline
  rw [trW_lastWake]
  rfl

theorem trW_callAt {y : Fin sp1.n} {i : Nat} {ℓ : ACLabel GA1} (h : trW.label i = some ℓ) :
    trW.CallAt y i ℓ :=
  ⟨Subsingleton.elim _ _, h⟩

theorem trW_time_ge {i : Nat} (hi : 2 ≤ i) : 12 ≤ trW.time i := by
  simp only [trW]
  split_ifs <;> first | omega | norm_num

theorem trW_post_0 : trW.post 0 = S1 := congrArg Prod.fst r0_eq'

theorem trW_post_1 : trW.post 1 = S2 := congrArg Prod.fst r1_eq'

theorem e0_mem : e0 ∈ ℓ0.emits := by
  change e0 ∈ r0.2
  rw [r0_eq']
  exact List.mem_singleton_self _

theorem e1_mem : e1 ∈ ℓ1.emits := by
  change e1 ∈ r1.2
  rw [r1_eq']
  exact List.mem_singleton_self _

theorem voteAt_0 (y : Fin sp1.n) : VoteAt trW y 0 e0 := ⟨ℓ0, trW_callAt rfl, e0_mem⟩

theorem voteAt_1 (y : Fin sp1.n) : VoteAt trW y 1 e1 := ⟨ℓ1, trW_callAt rfl, e1_mem⟩

/-- The votes of the run: `vote1` at cut 0 and `vote2` at cut 1. -/
theorem voteAt_cases {x : Fin sp1.n} {j : Nat} {e : Em sp1 Unit} (h : VoteAt trW x j e) :
    (j = 0 ∧ e = e0) ∨ (j = 1 ∧ e = e1) := by
  obtain ⟨ℓ, ⟨-, hl⟩, he⟩ := h
  rcases trW_label hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · change e ∈ r0.2 at he
    rw [r0_eq'] at he
    exact Or.inl ⟨rfl, List.mem_singleton.1 he⟩
  · change e ∈ r1.2 at he
    rw [r1_eq'] at he
    exact Or.inr ⟨rfl, List.mem_singleton.1 he⟩
  · cases he
  · change e ∈ r3.2 at he
    rw [r3_eq] at he
    cases he

theorem mem_S1_pool {σ : Nat} {v : Vote sp1.n} (h : v ∈ S1.pool σ) : v = vote1 := by
  simp only [S1, R0, Rb, SAState.initial, Function.update_apply] at h
  split_ifs at h <;> simp_all

theorem mem_S2_pool {σ : Nat} {v : Vote sp1.n} (h : v ∈ S2.pool σ) : v = vote1 ∨ v = vote2 := by
  simp only [S2, R1, S1, R0, Rb, SAState.initial, Function.update_apply] at h
  split_ifs at h <;> simp_all

theorem vote1_mem_S1 : vote1 ∈ S1.pool vote1.slot := by simp [S1, vote1]

theorem vote2_mem_S2 : vote2 ∈ S2.pool 2 := by simp [S2, vote2]

theorem validPayload_B1 : validPayload B1 := ⟨fun _ hv => (by cases hv), fun _ hv => (by cases hv)⟩

theorem frameIn_Φ₁ : GA1.FrameIn U₁ Φ₁ := ⟨frameOK_Φ₁, subset_rfl⟩

/-- The run satisfies the AC trace contract for the honest set `{v0}` inside `{genesis, B1}`. -/
theorem localRun_W : ACLocalRun GA1 Set.univ U₁ trW where
  coherent := coherent_U₁
  init := fun _ _ => rfl
  exec := fun i ℓ h _ => by
    rcases trW_label h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    all_goals rw [trW_state_succ _ (by decide)]; rfl
  frameLaw := fun y _ i ℓ h => by
    rcases trW_label h.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨fun k _ hk => absurd hk (Nat.not_lt_zero k), Φ₀, ⟨rfl, rfl, rfl, rfl, rfl⟩,
        ⟨frameOK_Φ₀, Set.singleton_subset_iff.2 g_mem⟩, frameIn_Φ₁, frameStep_Φ₁, validPayload_B1,
        by decide⟩
    · exact Or.inr ⟨0, ℓ0, by decide, trW_callAt rfl, fun k hk hk' => absurd hk' (by omega),
        frameIn_Φ₁, rfl⟩
    · exact Or.inr ⟨1, ℓ1, by decide, trW_callAt rfl, fun k hk hk' => absurd hk' (by omega),
        frameIn_Φ₁, rfl⟩
    · exact Or.inr ⟨2, ℓ2, by decide, trW_callAt rfl, fun k hk hk' => absurd hk' (by omega),
        frameIn_Φ₁, rfl⟩
  time_nonneg := fun i => by
    simp only [trW]
    split_ifs <;> norm_num
  time_mono := trW_time_mono
  awake_of_call := fun _ _ _ _ _ => trivial
  restart_of_sleep := fun _ _ _ _ _ _ _ _ hu _ => absurd trivial hu
  restart_at_wake := fun _ _ _ _ _ _ hu _ => absurd trivial hu
  sleep_of_restart := fun y _ i ℓ h hr => absurd ⟨ℓ, h, hr⟩ (trW_no_restart y i)

/-- The honest-object facts of the run. -/
theorem honest_W : HonestObjects (fun _ => v0) trW Set.univ where
  pool_vote := fun y _ i σ v hv _ => by
    rcases i with _ | _ | _ | _ | i
    · cases hv
    · rw [trW_state_1] at hv
      rw [mem_S1_pool hv]
      exact ⟨0, by decide, e0, voteAt_0 _, rfl⟩
    all_goals
      first
      | rw [trW_state_2] at hv
      | rw [trW_state_3] at hv
      | rw [trW_state_late, updateConfirmation_pool] at hv
      rcases mem_S2_pool hv with rfl | rfl
      · exact ⟨0, by omega, e0, voteAt_0 _, rfl⟩
      · exact ⟨1, by omega, e1, voteAt_1 _, rfl⟩
  message_vote := fun y _ i ℓ v h hc _ => by
    rcases trW_label h.2 with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases hc
  carried_vote := fun y _ i ℓ h B hB v hv _ => by
    rw [trW_frame h.2] at hB
    rcases hB with rfl | rfl <;> cases hv
  proposer := fun _ _ _ => Subsingleton.elim _ _
  one_block := fun B B' ⟨_, _, i, ℓ, h, hB⟩ ⟨_, _, i', ℓ', h', hB'⟩ _ _ hs => by
    rw [trW_frame h.2] at hB
    rw [trW_frame h'.2] at hB'
    rcases hB with rfl | rfl <;> rcases hB' with rfl | rfl <;> first | rfl | simp [g, B1] at hs

/-- (a) The run is an AC run (the hypothesis `ACRun` of every ACSteps statement). -/
theorem acRun_W : ACRun (fun _ => v0) trW Set.univ U₁ := ⟨localRun_W, honest_W⟩

/-! ## The premises -/

/-- The state at which the optimistic check after the own slot-`1` vote runs. -/
noncomputable def A0 : SAState sp1.n := admitVote sp1 R0 4 vote1

/-- The counted votes of the optimistic lock of slot `1`. -/
noncomputable def CV1 : Set (Vote sp1.n) := {v | v ∈ A0.pool 1 ∧ AncR Φ₁ B1 v.head}

theorem A0_eq : A0 = { R0 with
    pool := Function.update R0.pool vote1.slot [vote1]
    voteStamp := Function.update R0.voteStamp vote1 (ETime.of 4) } :=
  admitVote_fresh R0 4 vote1 slot_4 rfl

theorem optimisticSelect_A0 : optimisticSelect sp1 A0 Φ₁ 4 = some B1 := by
  rw [A0_eq]
  exact optimisticSelect_B1 rfl (by rw [slot_4]; decide) (by rw [slot_4]; decide)
    ⟨vote1, by rw [slot_4]; simp [vote1], rfl⟩

/-- The optimistic confirmation of slot `1` at cut 0 locks `B1`. -/
theorem optimisticLock_W : OptimisticLockAt trW v0 0 1 B1 CV1 :=
  ⟨ℓ0, A0, ⟨trW_callAt rfl, Or.inr (Or.inr ⟨e0, e0_mem, rfl⟩)⟩, slot_4, optimisticSelect_A0, rfl⟩

theorem mem_CV1 {v : Vote sp1.n} (hv : v ∈ CV1) : v = vote1 := by
  have h := hv.1
  rw [A0_eq] at h
  simpa [R0, Rb, SAState.initial, vote1, Function.update_apply] using h

theorem castAt_W : CastAt trW v0 1 ℓ1 e1 := ⟨trW_callAt rfl, e1_mem⟩

theorem faults_W : 2 * (Set.univ : Set (Fin sp1.n))ᶜ.ncard < sp1.n := by simp

/-- `Carry_{v0}(1, S, B1)` at the slot-`2` vote. -/
theorem carry_W : CarryAt trW U₁ v0 1 e1 1 CV1 where
  awake := trivial
  joined := joined_bot rfl _
  heads := fun v hv => by
    obtain rfl := mem_CV1 hv
    refine ⟨B1, B1_mem, rfl, fun X hX => ?_⟩
    rcases mem_of_anc_U₁ hX B1_mem with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨0, ⟨ℓ0, trW_callAt rfl, rfl⟩, by decide⟩
  holds := fun v hv => by
    obtain rfl := mem_CV1 hv
    refine Or.inl ⟨vote1_mem_S1, ?_⟩
    change Function.update R0.voteStamp vote1 (ETime.of 4) vote1 < _
    rw [Function.update_self]
    decide

theorem viable_W : ViableAtVote ℓ1 e1 2 B1 :=
  Or.inl (B1_viable ⟨B1_mem, Or.inl (by
    change ETime.of 4 < ETime.of (sp1.ts ((2 : Nat) - 1 : Int) + 3 * sp1.Δ)
    decide)⟩)

theorem earlier_W : EarlierVotesExtend trW Set.univ U₁ 1 2 B1 := fun _ _ j hj e he hs => by
  rcases voteAt_cases he with ⟨-, rfl⟩ | ⟨rfl, -⟩
  · exact absurd hs (by decide)
  · omega

theorem slot2_extend_W : ∀ x' ∈ (Set.univ : Set (Fin sp1.n)), ∀ j e, VoteAt trW x' j e →
    e.msg.slot = 1 + 1 → VoteExtends U₁ e.msg B1 := fun _ _ j e he hs => by
  rcases voteAt_cases he with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact absurd hs (by decide)
  · exact ⟨B1, B1_mem, rfl, Relation.ReflTransGen.refl⟩

/-- `Sync[a, b]` for every `b` before `12`: a message sent at cut 0 or 1, or newly held after it,
is that cut's own emission, processed there; the only acceptance is at cut 0. -/
theorem sync_W {a b : Time} (hb : b < 12) : SyncAC GA1 Set.univ U₁ a b trW := by
  refine ⟨fun x _ i m hsa _ hib y _ j ℓ _ hd => ?_, fun x _ i B hacc _ _ y _ j ℓ _ hd _ => ?_⟩
  · rw [trW_deadline] at hd
    have hij : i < j := trW_time_mono.reflect_lt (by linarith)
    refine ⟨i, hij.le, le_rfl, ?_, by rw [trW_deadline]; linarith⟩
    obtain ⟨ℓ', hc', hm⟩ := hsa
    rcases hm with ⟨e, he, rfl⟩ | ⟨-, hn, hh⟩
    · exact ⟨ℓ', ⟨Subsingleton.elim _ _, hc'.2⟩, Or.inr ⟨e, he, rfl⟩⟩
    have hi : i = 0 ∨ i = 1 := by
      by_contra hc
      have := trW_time_ge (i := i) (by omega)
      linarith
    change m ∈ (trW.post i).pool m.slot at hh
    change m ∉ (trW.state x i).pool m.slot at hn
    rcases hi with rfl | rfl
    · rw [trW_post_0] at hh
      obtain rfl := mem_S1_pool hh
      exact ⟨ℓ0, trW_callAt rfl, Or.inr ⟨e0, e0_mem, rfl⟩⟩
    · rw [trW_post_1] at hh
      rw [trW_state_1] at hn
      rcases mem_S2_pool hh with rfl | rfl
      · exact absurd vote1_mem_S1 hn
      · exact ⟨ℓ1, trW_callAt rfl, Or.inr ⟨e1, e1_mem, rfl⟩⟩
  · rw [trW_deadline] at hd
    have hij : i < j := trW_time_mono.reflect_lt (by linarith)
    obtain ⟨ℓ', hc', hB⟩ := hacc
    exact ⟨i, hij.le, ⟨ℓ', ⟨Subsingleton.elim _ _, hc'.2⟩, hB⟩, by rw [trW_deadline]; linarith⟩

theorem update_W : UpdateAt trW v0 3 2 ℓ3 :=
  ⟨trW_callAt rfl, rfl, by decide, by rw [trW_state_3]; exact joined_bot rfl _⟩

theorem S3_pool_2 : S3.pool 2 = [vote2] := by simp [S3, S2, vote2]

theorem participation_W : sp1.n ≤ 2 * {v | v ∈ (Set.univ : Set (Fin sp1.n)) ∧
    ∃ x' ∈ (trW.state v0 3).pool (1 + 1), x'.val = v}.ncard := by
  rw [trW_state_3]
  have : {v | v ∈ (Set.univ : Set (Fin sp1.n)) ∧ ∃ x' ∈ S3.pool (1 + 1), x'.val = v} =
      Set.univ :=
    Set.eq_univ_of_forall fun _ => ⟨trivial, vote2, by rw [S3_pool_2]; simp,
      Subsingleton.elim _ _⟩
  rw [this, ncard_univ_v]
  decide

theorem resolutionTime_B1 (A : SAState sp1.n) {v : Vote sp1.n} (hv : v.head = 1) :
    resolutionTime A Φ₁ v = if v.slot < 1 then ⊤ else max (A.voteStamp v) (A.blockStamp 1) := by
  unfold resolutionTime
  rw [hv, lookup_B1]
  rfl

theorem resolved_W : ∀ x' ∈ (trW.state v0 3).pool (1 + 1), x'.val ∈ (Set.univ : Set (Fin sp1.n)) →
    resolutionTime (trW.state v0 3) ℓ3.frame x' <
      ETime.of (sp1.ts (1 + 1 : Nat) + 2 * sp1.Δ) := by
  rw [trW_state_3]
  intro x hx _
  rw [S3_pool_2, List.mem_singleton] at hx
  subst hx
  change resolutionTime S3 Φ₁ vote2 < _
  rw [resolutionTime_B1 S3 rfl]
  simp [S3, S2, R1, S1, R0, Rb, SAState.initial, vote1, vote2]
  decide

theorem toFG_W : ToFGAt trW v0 2 ℓ2 B1 :=
  ⟨trW_callAt rfl, rfl, by rw [trW_state_2]; exact toFG_S2.2⟩

/-! ## The witnesses -/

/-- **A1.4 (a), `OptimisticTransfer`: the premises are satisfiable.** Every hypothesis of the
statement holds of the run at `s = 1`: `v0`'s optimistic lock of slot `1` on `B1` at cut 0 and its
slot-`2` vote at cut 1. -/
theorem optimisticTransfer_premises_satisfiable :
    ∃ (H : Set (Fin sp1.n)) (U : Set (Blk sp1.n Unit)) (tr : SATrace sp1 Unit ro1)
      (proposer : Nat → Fin sp1.n) (s : Nat) (x y : Fin sp1.n) (i₀ i : Nat)
      (B : Blk sp1.n Unit) (CV : Set (Vote sp1.n)) (ℓ : ACLabel (goldilocksSA sp1 Unit ro1))
      (e : Em sp1 Unit),
    ACRun proposer tr H U ∧
    x ∈ H ∧ OptimisticLockAt tr x i₀ s B CV ∧ 2 * Hᶜ.ncard < sp1.n ∧
    y ∈ H ∧ CastAt tr y i ℓ e ∧ e.msg.slot = s + 1 ∧
    SyncAC (goldilocksSA sp1 Unit ro1) H U (sp1.ts s) (tr.time i) tr ∧
    CarryAt tr U y i e s CV ∧
    ViableAtVote ℓ e (s + 1) B ∧ EarlierVotesExtend tr H U i (s + 1) B :=
  ⟨Set.univ, U₁, trW, fun _ => v0, 1, v0, v0, 0, 1, B1, CV1, ℓ1, e1, acRun_W, trivial,
    optimisticLock_W, faults_W, trivial, castAt_W, rfl, sync_W (by decide), carry_W, viable_W,
    earlier_W⟩

/-- **A1.4 (b), `OptimisticNextUpdate`: the premises are satisfiable.** Every hypothesis of the
statement holds of the run at `s = 1`, `B = B1` (not genesis, so the fast-select clause of the
conclusion is in force): the update of slot `2` at cut 3, holding `vote2` (stamp `9`, resolved
before `t_2 + 2Δ = 10`). -/
theorem optimisticNextUpdate_premises_satisfiable :
    ∃ (H : Set (Fin sp1.n)) (U : Set (Blk sp1.n Unit)) (tr : SATrace sp1 Unit ro1)
      (proposer : Nat → Fin sp1.n) (s : Nat) (x z : Fin sp1.n) (i₀ k : Nat)
      (B : Blk sp1.n Unit) (CV : Set (Vote sp1.n)) (ℓ : ACLabel (goldilocksSA sp1 Unit ro1)),
    ACRun proposer tr H U ∧
    x ∈ H ∧ OptimisticLockAt tr x i₀ s B CV ∧ 2 * Hᶜ.ncard < sp1.n ∧
    SyncAC (goldilocksSA sp1 Unit ro1) H U (sp1.ts s) (sp1.ts (s + 1 : Nat) + sp1.Δ) tr ∧
    (∀ x' ∈ H, ∀ j e, VoteAt tr x' j e → e.msg.slot = s + 1 → VoteExtends U e.msg B) ∧
    z ∈ H ∧ UpdateAt tr z k (s + 1) ℓ ∧
    sp1.n ≤ 2 * {v | v ∈ H ∧ ∃ x' ∈ (tr.state z k).pool (s + 1), x'.val = v}.ncard ∧
    (∀ x' ∈ (tr.state z k).pool (s + 1), x'.val ∈ H →
      resolutionTime (tr.state z k) ℓ.frame x' < ETime.of (sp1.ts (s + 1 : Nat) + 2 * sp1.Δ)) :=
  ⟨Set.univ, U₁, trW, fun _ => v0, 1, v0, v0, 0, 3, B1, CV1, ℓ3, acRun_W, trivial,
    optimisticLock_W, faults_W, sync_W (by decide), slot2_extend_W, trivial, update_W,
    participation_W, resolved_W⟩

/-- **A1.5, `SourceAge`: the premises are satisfiable.** Every hypothesis of the statement holds of
the run at `τ = 0`: `ac_to_fg` returns `B1` at cut 2, time `12`, and
`slot(0) + 3 = 3 = slot(12)`. -/
theorem sourceAge_premises_satisfiable :
    ∃ (H : Set (Fin sp1.n)) (U : Set (Blk sp1.n Unit)) (tr : SATrace sp1 Unit ro1)
      (proposer : Nat → Fin sp1.n) (τ : Time) (x : Fin sp1.n) (i : Nat)
      (ℓ : ACLabel (goldilocksSA sp1 Unit ro1)) (C : Blk sp1.n Unit),
    ACRun proposer tr H U ∧
    x ∈ H ∧ ToFGAt tr x i ℓ C ∧ sp1.slot τ + 3 ≤ sp1.slot (tr.time i) :=
  ⟨Set.univ, U₁, trW, fun _ => v0, 0, v0, 2, ℓ2, B1, acRun_W, trivial, toFG_W, by decide⟩

/-! ## The milestones on the witness -/

/-- A1.4 (a) on the run: the slot-`2` vote extends `B1`. -/
theorem optimisticTransfer_on_witness : VoteExtends U₁ e1.msg B1 :=
  (acStepsAt sp1).optimisticTransfer Unit ro1 Set.univ U₁ trW (fun _ => v0) acRun_W 1 v0 v0 0 1
    B1 CV1 ℓ1 e1 trivial optimisticLock_W faults_W trivial castAt_W rfl (sync_W (by decide))
    carry_W viable_W earlier_W

/-- A1.4 (b) on the run: the update of slot `2` has a result extending `B1`, and, `B1` not being
genesis, its fast test selects a block extending `B1`. -/
theorem optimisticNextUpdate_on_witness :
    ∃ C, getConfirmation sp1 (trW.state v0 3) ℓ3.frame (1 + 1) = some C ∧ Anc U₁ B1 C ∧
      ∃ D, fastSelect sp1 (trW.state v0 3) ℓ3.frame (1 + 1) C = some D ∧ Anc U₁ B1 D := by
  obtain ⟨C, hC, hBC, hD⟩ := (acStepsAt sp1).optimisticNextUpdate Unit ro1 Set.univ U₁ trW
    (fun _ => v0) acRun_W 1 v0 v0 0 3 B1 CV1 ℓ3 trivial optimisticLock_W faults_W
    (sync_W (by decide)) slot2_extend_W trivial update_W participation_W resolved_W
  exact ⟨C, hC, hBC, hD (by decide)⟩

/-- A1.5 on the run: `B1`, returned by `ac_to_fg` at cut 2, is at or below the block of a fast
lock of a slot `s'` with `slot(12) ≤ s' + 2`, written after time `0`. -/
theorem sourceAge_on_witness :
    ∃ j ≤ 2, ∃ s' B' CV', FastLockAt trW v0 j s' B' CV' ∧ (0 : Time) < trW.time j ∧
      sp1.slot (trW.time 2) ≤ s' + 2 ∧ Anc U₁ B1 B' :=
  (acStepsAt sp1).sourceAge Unit ro1 Set.univ U₁ trW (fun _ => v0) acRun_W 0 v0 2 ℓ2 B1 trivial
    toFG_W (by decide)

end Consensus.Goldilocks.SA.Test

end
