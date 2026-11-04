module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Base
public import ConsensusLeanTest.GoldilocksNode
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
@[expose] public section

/-! # Threshold and genesis-root rejections (ACBase A0.3, Compose C0.3)

Labelled by kind (CONTRIBUTING "Statements"). On the frame `Φ` with genesis `g` and two
conflicting children `B`, `C` of `g`:

* (r) `majorityChain_needs_strict_majority`: `MajorityChain` (A0.3) with the threshold one below
  (`|voters| ≤ 2 · |supporters|`, half instead of a strict majority) fails: two validators, one
  voting `B` and one voting `C`; every other premise holds, and `B`, `C` conflict.
* (r) `optimisticChain_needs_three_quarters`: `OptimisticChain` (A0.3) with the threshold one
  below (`3n ≤ 4 · |voters| + 1`) fails: three validators, `0` votes `B`, `2` votes `C`, `1` votes
  both; one equivocator (`2 · 1 < 3`), each block has two optimistic voters (`9 ≤ 9`, but
  `9 > 8`), and `B`, `C` conflict.
* (r) `honestBlockAccepted_needs_genesisRoot`: `HonestBlockAccepted` (C0.3) without its premise
  that genesis's root is its digest fails (consensus-lean#73 style). On `GoldilocksNode`'s
  `rootAC` with a digest `dg₂` under which genesis (slot `0`) has digest `5 ≠ 0 = genesisRoot`
  and a slot-`1` block has digest `0`: the AC meets its requirements, the proposer's tick at
  `t_1 = 1` from the initial configuration is a step, and `ac_proposal` returns a proposal; the
  digest is collision free on the tree with the new block, yet its root `0` is held (by
  genesis), so the conclusion fails. -/

namespace Consensus.Goldilocks.Test.ThresholdRejections

open SA

/-- `n` validators, `Δ = 1`, slot `s` starts at `4s`, genesis root `0`. -/
abbrev Pn (n : Nat) (hn : 1 ≤ n) : Params where
  n := n
  hn := hn
  Δ := 1
  hΔ := one_pos
  slotTime s := 4 * (s : Int)
  slotTime_zero := by simp
  slotTime_strictMono := fun a b h => by change 4 * (a : Int) < 4 * (b : Int); omega
  slotTime_public := fun s => ⟨4 * (s : Int), by ring⟩
  genesisRoot := 0
  δt := 2

/-- The SA parameters on `Pn n`, `k = c = 2`. -/
abbrev spn (n : Nat) (hn : 1 ≤ n) : SAParams where
  toParams := Pn n hn
  slotTime_eq := fun s => by change 4 * (s : Int) = 4 * 1 * s; ring
  k := 2
  two_le_k := le_rfl
  c := 2
  two_le_c := le_rfl

section Frame

variable {n : Nat}

/-- Genesis. -/
def g (p : Fin n) : Blk n Unit := ⟨0, none, 0, p, 0, (), ([], [])⟩
/-- A child of genesis, root `1`. -/
def bB (p : Fin n) : Blk n Unit := ⟨1, some 0, 1, p, 0, (), ([], [])⟩
/-- Another child of genesis, root `2`. -/
def bC (p : Fin n) : Blk n Unit := ⟨2, some 0, 1, p, 0, (), ([], [])⟩

/-- The frame `{g, B, C}` rooted at `g`. -/
def Φ (p : Fin n) : Frm n Unit := ⟨{g p, bB p, bC p}, g p, g p, {g p}⟩

theorem mem_iff (p : Fin n) (X : Blk n Unit) :
    X ∈ (Φ p).tree ↔ X = g p ∨ X = bB p ∨ X = bC p := by
  simp [Φ]

/-- Genesis has no strict ancestor. -/
theorem anc_g {S : Set (Blk n Unit)} {p : Fin n} {A : Blk n Unit} (h : Anc S A (g p)) :
    A = g p := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨_, _, ⟨_, _, he⟩⟩
  · exact h.symm
  · simp [g] at he

theorem edge_g {p : Fin n} {X : Blk n Unit} (hX : X = bB p ∨ X = bC p) :
    (Φ p).Anc (g p) X :=
  Relation.ReflTransGen.single ⟨by simp [Φ], by rcases hX with rfl | rfl <;> simp [Φ],
    by rcases hX with rfl | rfl <;> rfl⟩

theorem frameOK (p : Fin n) : FrameOK (Φ p) where
  finite := by simp [Φ]
  coherent := by
    refine ⟨?_, ?_⟩
    · intro x hx y hy h
      rw [mem_iff] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp_all [g, bB, bC]
    · intro x hx y hy h
      rw [mem_iff] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp_all [g, bB, bC]
  rooted := ⟨by simp [Φ], fun X hX => by
    rcases (mem_iff p X).1 hX with rfl | h
    · exact Relation.ReflTransGen.refl
    · exact edge_g h⟩
  fcRoot_mem := by simp [Φ]
  F_anc_fcRoot := Relation.ReflTransGen.refl
  viableHeads_subset := by simp [Φ]
  fcRoot_anc_viableHeads := fun W hW => by
    rw [show W = g p from hW]; exact Relation.ReflTransGen.refl

/-- `B` is not below `C`, and `C` is not below `B`: each has parent `g`. -/
theorem not_anc_children (p : Fin n) {X Y : Blk n Unit} (hX : X = bB p ∨ X = bC p)
    (hY : Y = bB p ∨ Y = bC p) (hne : X ≠ Y) : ¬ (Φ p).Anc X Y := by
  intro h
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨P, hXP, hP, -, hYP⟩
  · exact hne h.symm
  have hPg : P = g p := by
    rcases (mem_iff p P).1 hP with h | rfl | rfl
    · exact h
    all_goals rcases hY with rfl | rfl <;> simp [bB, bC] at hYP
  subst hPg
  have := anc_g hXP
  rcases hX with rfl | rfl <;> simp [bB, bC, g] at this

theorem conflict (p : Fin n) : ¬ Compatible (Φ p).tree (bB p) (bC p) := by
  rintro (h | h)
  · exact not_anc_children p (Or.inl rfl) (Or.inr rfl) (by simp [bB, bC]) h
  · exact not_anc_children p (Or.inr rfl) (Or.inl rfl) (by simp [bB, bC]) h

theorem ancR_self (p : Fin n) {X : Blk n Unit} (hX : X ∈ (Φ p).tree) :
    AncR (Φ p) X X.root :=
  ⟨X, hX, rfl, Relation.ReflTransGen.refl⟩

end Frame

/-! ## MajorityChain -/

/-- Two validators. -/
abbrev sp2 : SAParams := spn 2 (by norm_num)

/-- One slot-`0` vote for `B` (validator `0`) and one for `C` (validator `1`), all support. -/
def V2 : View sp2.n :=
  ⟨{⟨0, 0, 1⟩, ⟨1, 0, 2⟩}, {⟨0, 0, 1⟩, ⟨1, 0, 2⟩}⟩

theorem no_equivocators_V2 : equivocators V2.votes = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun i ⟨x, hx, y, hy, hne, hxi, hyi⟩ => hne ?_
  simp only [V2, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  all_goals first | rfl | exact absurd (hxi.trans hyi.symm) (by decide)

theorem voters_le (V : View sp2.n) : (voters V.votes).ncard ≤ 2 := by
  have := Set.ncard_le_ncard (Set.subset_univ (voters V.votes)) (Set.toFinite _)
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this

theorem one_le_supporters {X : Blk sp2.n Unit} (hX : X ∈ (Φ (0 : Fin 2)).tree) (i : Fin 2)
    (hv : (⟨i, 0, X.root⟩ : Vote sp2.n) ∈ V2.support) :
    1 ≤ (supporters (Φ 0) V2 0 X).ncard := by
  exact (Set.ncard_pos (Set.toFinite _)).2 ⟨i, by rw [no_equivocators_V2]; exact Set.notMem_empty _,
    _, hv, rfl, rfl, ancR_self 0 hX⟩

/-- (r) **`MajorityChain` needs the strict majority.** With `|voters| ≤ 2 · |supporters|` (one
below `<`), every other premise holds for `B` and `C`, and they conflict. -/
theorem majorityChain_needs_strict_majority :
    FrameOK (Φ (0 : Fin 2)) ∧ V2.support ⊆ V2.votes ∧ bB 0 ∈ (Φ (0 : Fin 2)).tree ∧
      bC 0 ∈ (Φ (0 : Fin 2)).tree ∧
      (voters V2.votes).ncard ≤ 2 * (supporters (Φ 0) V2 0 (bB 0)).ncard ∧
      (voters V2.votes).ncard ≤ 2 * (supporters (Φ 0) V2 0 (bC 0)).ncard ∧
      ¬ Compatible (Φ (0 : Fin 2)).tree (bB 0) (bC 0) := by
  have hB : bB (0 : Fin 2) ∈ (Φ (0 : Fin 2)).tree := by simp [Φ]
  have hC : bC (0 : Fin 2) ∈ (Φ (0 : Fin 2)).tree := by simp [Φ]
  refine ⟨frameOK 0, le_rfl, hB, hC, ?_, ?_, conflict 0⟩
  · have := one_le_supporters hB 0 (by simp [V2, bB]); have := voters_le V2; omega
  · have := one_le_supporters hC 1 (by simp [V2, bC]); have := voters_le V2; omega

/-! ## OptimisticChain -/

/-- Three validators. -/
abbrev sp3 : SAParams := spn 3 (by norm_num)

/-- The slot-`0` pool: `0` votes `B`, `1` votes `B` and `C`, `2` votes `C`. -/
def A3 : SAState sp3.n :=
  { SAState.initial 0 with pool := fun _ => [⟨0, 0, 1⟩, ⟨1, 0, 1⟩, ⟨1, 0, 2⟩, ⟨2, 0, 2⟩] }

theorem equivocators_A3 : equivocators {x | x ∈ A3.pool 0} ⊆ {1} := by
  rintro i ⟨x, hx, y, hy, hne, rfl, hyi⟩
  simp only [A3, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> simp_all

theorem two_le_optimisticVoters {X : Blk sp3.n Unit} (hX : X ∈ (Φ (0 : Fin 3)).tree)
    (i j : Fin 3) (hij : i ≠ j) (hi : (⟨i, 0, X.root⟩ : Vote sp3.n) ∈ A3.pool 0)
    (hj : (⟨j, 0, X.root⟩ : Vote sp3.n) ∈ A3.pool 0) :
    2 ≤ (optimisticVoters sp3 A3 (Φ 0) 0 X).ncard := by
  have hsub : ({i, j} : Set (Fin 3)) ⊆ optimisticVoters sp3 A3 (Φ 0) 0 X := by
    rintro k (rfl | rfl)
    · exact ⟨_, hi, rfl, ancR_self 0 hX⟩
    · exact ⟨_, hj, rfl, ancR_self 0 hX⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [Set.ncard_pair hij] at this

/-- (r) **`OptimisticChain` needs three quarters.** With `3n ≤ 4 · |voters| + 1` (one below
`3n ≤ 4 · |voters|`), fewer than `n/2` equivocators, `B` and `C` in a well-formed frame, they
conflict. -/
theorem optimisticChain_needs_three_quarters :
    FrameOK (Φ (0 : Fin 3)) ∧ 2 * (equivocators {x | x ∈ A3.pool 0}).ncard < sp3.n ∧
      bB 0 ∈ (Φ (0 : Fin 3)).tree ∧ bC 0 ∈ (Φ (0 : Fin 3)).tree ∧
      3 * sp3.n ≤ 4 * (optimisticVoters sp3 A3 (Φ 0) 0 (bB 0)).ncard + 1 ∧
      3 * sp3.n ≤ 4 * (optimisticVoters sp3 A3 (Φ 0) 0 (bC 0)).ncard + 1 ∧
      ¬ Compatible (Φ (0 : Fin 3)).tree (bB 0) (bC 0) := by
  have hB : bB (0 : Fin 3) ∈ (Φ (0 : Fin 3)).tree := by simp [Φ]
  have hC : bC (0 : Fin 3) ∈ (Φ (0 : Fin 3)).tree := by simp [Φ]
  refine ⟨frameOK 0, ?_, hB, hC, ?_, ?_, conflict 0⟩
  · have := Set.ncard_le_ncard equivocators_A3 (Set.toFinite _)
    rw [Set.ncard_singleton] at this
    change _ < 3
    omega
  · have := two_le_optimisticVoters hB 0 1 (by decide) (by simp [A3, bB]) (by simp [A3, bB])
    change 9 ≤ _; omega
  · have := two_le_optimisticVoters hC 1 2 (by decide) (by simp [A3, bC]) (by simp [A3, bC])
    change 9 ≤ _; omega

/-! ## HonestBlockAccepted -/

open Compose.Test in
/-- A digest under which genesis (slot `0`) is not its own root (`5 ≠ 0`) and every slot-`1`
block gets root `0`. -/
def dg₂ : Digest (List (FG.Att P₁.n)) Unit := fun _ s _ _ _ => if s = 1 then 0 else s + 5

open Compose.Test in
/-- `dg₂` is collision free on genesis and a slot-`1` block: their digests are `5` and `0`. -/
theorem noColl_init {B : rootAC.Blk} (hB : B.slot = 1) :
    Compose.NoCollOn (A := rootAC) dg₂ (insert B (Store.init (P := P₁) ()).tree) := by
  have hgen : ∀ X ∈ (Store.init (P := P₁) ()).tree, X = P₁.genesisBlock () := by
    intro X hX
    simp only [Store.tree, Store.init, Set.mem_ofPred_eq] at hX
    split_ifs at hX
    exact (Option.some.inj hX).symm
  intro X hX Y hY hXY
  rcases hX with rfl | hX <;> rcases hY with rfl | hY
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rw [hgen Y hY] at hXY; simp [dg₂, hB, Params.genesisBlock] at hXY
  · rw [hgen X hX] at hXY; simp [dg₂, hB, Params.genesisBlock] at hXY
  · rw [hgen X hX, hgen Y hY]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

open Compose.Test in
/-- (r) **`HonestBlockAccepted` needs the genesis-root premise.** On `rootAC` with `dg₂`: the
requirements hold, genesis's root is not its digest, and the conclusion of
`HonestBlockAccepted` fails for the proposer's tick at `t_1 = 1` from the initial configuration:
the digest is collision free on the tree with the new block, but its root `0` is held. -/
theorem honestBlockAccepted_needs_genesisRoot :
    rootAC.Requirements ∧ ¬ (P₁.genesisBlock rootAC.genesisPayload).RootOk dg₂ ∧
      ¬ (∀ (cfg cfg' : Node.Config rootAC) (t : Time) (x : Nat),
          Node.Reachable (fun _ => v₀) dg₂ v₀ cfg →
          Node.Step (fun _ => v₀) dg₂ v₀ cfg (.tick x) t cfg' →
          Node.Proposes (P := P₁) (fun _ => v₀) v₀ t →
          let st₁ := (Node.tickStep (fun _ => v₀) dg₂ v₀ cfg.st t x .acTick).1
          let r := Node.acProposal st₁ t
          ∀ d p, r.2.2 = some (d, p) →
            let B := Node.mkBlock dg₂ v₀ r.1.fg t x d.head p
            d.head ∈ r.1.fg.tree ∧ r.1.fg.Anc r.1.fg.F d.head ∧ d.head.slot < B.slot ∧
            (∀ a ∈ B.fgPayload, a.WellFormed ∧ (r.1.fg.σ d.head.root).validAtt a) ∧
            rootAC.validPayload B ∧ B.RootOk dg₂ ∧
            (Compose.NoCollOn dg₂ (insert B r.1.fg.tree) → r.1.fg.blocks B.root = none ∧
              ∃ fg', r.1.fg.onBlock B = some fg')) := by
  refine ⟨rootAC_requirements,
    fun h => by simp [Block.RootOk, dg₂, Params.genesisBlock, P₁] at h, fun h => ?_⟩
  have hstep : Node.Step (fun _ => v₀) dg₂ v₀ (Node.Config.init rootAC) (.tick 0) 1
      ⟨(Node.exec (fun _ => v₀) dg₂ v₀ (Node.init rootAC) 1 (.tick 0)).1, 1, .post⟩ :=
    ⟨by decide, ⟨one_dvd _, by simp [Node.Phase.at, Node.Config.init]⟩, trivial, rfl, rfl, rfl⟩
  have hc := h _ _ 1 0 Relation.ReflTransGen.refl hstep proposes_at_one _ () rfl
  have hfg : (Node.acProposal (Node.tickStep (fun _ => v₀) dg₂ v₀ (Node.Config.init rootAC).st 1 0
      .acTick).1 1).1.fg = Store.init () := rfl
  simp only [hfg] at hc
  obtain ⟨-, -, -, -, -, -, hnc⟩ := hc
  refine absurd (hnc (noColl_init slotOf_one)).1 ?_
  simp only [Node.mkBlock, dg₂, slotOf_one, ite_true]
  simp [Store.init, P₁]

end Consensus.Goldilocks.Test.ThresholdRejections

end
