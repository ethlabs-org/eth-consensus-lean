module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
@[expose] public section

/-! # Witness: `unlock`'s target depends on the frame

A mechanism witness, not one of the witness kinds (a)–(c) of CONTRIBUTING "Statements" (it
witnesses no statement's hypotheses): a concrete configuration of the SA lock code
(`Spec/SA/Locks.lean`: `opponents`, `unlockTarget`), with no trace. It records the mechanism
behind the open step of HS.3 (a), the retired `voter_unlock_keeps_lock` (AgreeLater, removed in
61076d7f). The proposal walk starts at a live lock `L` that survives the proposer's `unlock`.
`opponents` counts only support votes whose head is in the frame's tree, so a voter whose `Σ.F` is
strictly below the proposer's can count more opponents of `L` against the same votes. Its `unlock`
can then move the lock below `L`.

* `frameOK_Φp`, `frameOK_Φy`: the two frames are well formed. `Φy` is rooted at `F_y = G` and `Φp`
  at `F_p = F ≻ G`, and `Φp`'s tree is contained in `Φy`'s.
* `unlockTarget_frame_dependent`: against one view of seven slot-2 votes (no equivocators), the
  target of `L` is `L` in `Φp` and `F ≺ L` in `Φy`. -/

namespace Consensus.Goldilocks.SA.Test.UnlockFrame

/-- The shared parameters: seven validators, `Δ = 1`, `t_s = 4s`, genesis root `0`. -/
abbrev P7 : Params where
  n := 7
  hn := by decide
  Δ := 1
  hΔ := one_pos
  slotTime := fun s => 4 * (s : Int)
  slotTime_zero := by simp
  slotTime_strictMono := fun a b h => by change 4 * (a : Int) < 4 * (b : Int); omega
  slotTime_public := fun _ => one_dvd _
  genesisRoot := 0
  δt := 0

/-- The SA parameters: `P7` with `k = 2`. -/
abbrev sp7 : SAParams where
  toParams := P7
  slotTime_eq := fun s => by change 4 * (s : Int) = 4 * 1 * s; omega
  k := 2
  two_le_k := le_rfl
  c := 2
  two_le_c := le_rfl

/-- The blocks of the witness (no FG payload). -/
abbrev Bk := Blk sp7.n Unit

/-- The proposer of every block (never read). -/
def v0 : Fin sp7.n := ⟨0, by decide⟩

/-- `G`, root `0`: the voter's `Σ.F`. -/
def bG : Bk := ⟨0, none, 0, v0, 0, (), ([], [])⟩
/-- `H`, root `1`, on `G`: a branch that conflicts with the proposer's `Σ.F`. -/
def bH : Bk := ⟨1, some 0, 1, v0, 0, (), ([], [])⟩
/-- `F`, root `2`, on `G`: the proposer's `Σ.F`. -/
def bF : Bk := ⟨2, some 0, 1, v0, 0, (), ([], [])⟩
/-- `X`, root `3`, on `F`: a block that conflicts with `L`. -/
def bX : Bk := ⟨3, some 2, 2, v0, 0, (), ([], [])⟩
/-- `L`, root `4`, on `F`: the locked block. -/
def bL : Bk := ⟨4, some 2, 2, v0, 0, (), ([], [])⟩

/-- The proposer's frame: rooted at `F`, so `H` is not in it. -/
def Φp : Frm sp7.n Unit := ⟨{bF, bX, bL}, bF, bF, {bX, bL}⟩

/-- The voter's frame: rooted at `G ≺ F`, with the same blocks and `H`. -/
def Φy : Frm sp7.n Unit := ⟨{bG, bH, bF, bX, bL}, bG, bG, {bH, bX, bL}⟩

/-- The head of validator `i`'s vote: `L` for `0, 1, 2`, `X` for `3, 4, 5`, `H` for `6`. -/
def head (i : Fin sp7.n) : Nat := if i.val < 3 then 4 else if i.val < 6 then 3 else 1

/-- Validator `i`'s slot-2 vote. -/
def vote (i : Fin sp7.n) : Vote sp7.n := ⟨i, 2, head i⟩

/-- The view: one vote per validator, every vote in the support set. -/
def V : View sp7.n := ⟨Set.range vote, Set.range vote⟩

/-- All blocks of the witness. -/
def U : Set Bk := {bG, bH, bF, bX, bL}

/-- The roots of the ancestors of the block with root `r`, for the blocks of `U`. -/
def ancRoots : Nat → List Nat
  | 0 => [0]
  | 1 => [1, 0]
  | 2 => [2, 0]
  | 3 => [3, 2, 0]
  | 4 => [4, 2, 0]
  | _ => []

/-- A parent edge inside `S` gives ancestry. -/
theorem edge {S : Set Bk} {B C : Bk} (hB : B ∈ S) (hC : C ∈ S) (h : C.parent = some B.root) :
    Anc S B C :=
  Relation.ReflTransGen.single ⟨hB, hC, h⟩

/-- Ancestry inside a subset of `U` follows the parent roots. -/
theorem anc_roots {S : Set Bk} (hS : S ⊆ U) {A B : Bk} (h : Anc S A B) (hB : B ∈ S) :
    A.root ∈ ancRoots B.root := by
  induction h with
  | refl =>
    rcases hS hB with rfl | rfl | rfl | rfl | rfl <;> decide
  | tail _ hCD ih =>
    obtain ⟨hC, hD, hp⟩ := hCD
    have h := ih hC
    rcases hS hD with rfl | rfl | rfl | rfl | rfl <;>
      simp only [bG, bH, bF, bX, bL, reduceCtorEq, Option.some.injEq] at hp ⊢ <;>
      rw [← hp] at h <;>
      simp only [ancRoots, List.mem_cons, List.not_mem_nil, or_false] at h ⊢ <;> omega

/-- The proposer's tree is among the witness blocks (and in the voter's tree). -/
theorem Φp_sub : Φp.tree ⊆ U := by
  intro B hB; rcases hB with rfl | rfl | rfl <;> simp [U]

/-- The voter's tree is all the witness blocks. -/
theorem Φy_sub : Φy.tree ⊆ U := fun _ h => h

/-- The proposer's frame is well formed. -/
theorem frameOK_Φp : FrameOK Φp where
  finite := ((Set.finite_singleton _).insert _).insert _
  coherent := by
    refine ⟨?_, ?_⟩
    · intro a ha b hb h
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first | rfl | simp [bF, bX, bL] at h
    · intro B hB C hC h
      rcases hB with rfl | rfl | rfl <;> rcases hC with rfl | rfl | rfl <;>
        simp_all [bF, bX, bL]
  rooted := ⟨Or.inl rfl, fun C hC => by
    rcases hC with rfl | rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact edge (Or.inl rfl) (Or.inr (Or.inl rfl)) rfl
    · exact edge (Or.inl rfl) (Or.inr (Or.inr rfl)) rfl⟩
  fcRoot_mem := Or.inl rfl
  F_anc_fcRoot := Relation.ReflTransGen.refl
  viableHeads_subset := by
    intro W hW; rcases hW with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  fcRoot_anc_viableHeads := by
    intro W hW; rcases hW with rfl | rfl
    · exact edge (Or.inl rfl) (Or.inr (Or.inl rfl)) rfl
    · exact edge (Or.inl rfl) (Or.inr (Or.inr rfl)) rfl

/-- Every block of the voter's tree extends `G`. -/
theorem Φy_rooted (C : Bk) (hC : C ∈ Φy.tree) : Φy.Anc bG C := by
  have hG : bG ∈ Φy.tree := Or.inl rfl
  have hF : bF ∈ Φy.tree := Or.inr (Or.inr (Or.inl rfl))
  have hGF : Φy.Anc bG bF := edge hG hF rfl
  rcases hC with rfl | rfl | rfl | rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact edge hG (Or.inr (Or.inl rfl)) rfl
  · exact hGF
  · exact hGF.tail ⟨hF, Or.inr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
  · exact hGF.tail ⟨hF, Or.inr (Or.inr (Or.inr (Or.inr rfl))), rfl⟩

/-- The voter's frame is well formed. -/
theorem frameOK_Φy : FrameOK Φy where
  finite := ((((Set.finite_singleton _).insert _).insert _).insert _).insert _
  coherent := by
    refine ⟨?_, ?_⟩
    · intro a ha b hb h
      rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl <;>
        first | rfl | simp [bG, bH, bF, bX, bL] at h
    · intro B hB C hC h
      rcases hB with rfl | rfl | rfl | rfl | rfl <;> rcases hC with rfl | rfl | rfl | rfl | rfl <;>
        simp_all [bG, bH, bF, bX, bL]
  rooted := ⟨Or.inl rfl, Φy_rooted⟩
  fcRoot_mem := Or.inl rfl
  F_anc_fcRoot := Relation.ReflTransGen.refl
  viableHeads_subset := by
    intro W hW; rcases hW with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  fcRoot_anc_viableHeads := fun W hW => by
    refine Φy_rooted W ?_
    rcases hW with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- `B` and `C` conflict inside a subset of `U` when neither root is among the other's ancestor
roots. -/
theorem not_compatible {S : Set Bk} (hS : S ⊆ U) {B C : Bk} (hB : B ∈ S) (hC : C ∈ S)
    (h₁ : B.root ∉ ancRoots C.root) (h₂ : C.root ∉ ancRoots B.root) : ¬ Compatible S B C :=
  fun h => h.elim (fun h => h₁ (anc_roots hS h hC)) fun h => h₂ (anc_roots hS h hB)

/-- No validator equivocates in `V`. -/
theorem equivocators_V : equivocators V.votes = ∅ := by
  ext i
  simp only [equivocators, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, hne, ha, hb⟩
  have hab : a = b := ha.trans hb.symm
  exact hne (hab ▸ rfl)

/-- A validator with an opponent vote in frame `Φ`: its vote's head is a block of the tree that
conflicts with `B`. -/
theorem mem_opponents {Φ : Frm sp7.n Unit} {B : Bk} {i : Fin sp7.n} :
    i ∈ opponents sp7 Φ V 2 B ↔
      ∃ H ∈ Φ.tree, H.root = head i ∧ ¬ Compatible Φ.tree H B := by
  simp only [opponents, equivocators_V, Set.empty_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, rfl, -, H, hH, hr, hc⟩
    exact ⟨H, hH, hr, hc⟩
  · rintro ⟨H, hH, hr, hc⟩
    exact ⟨vote i, ⟨i, rfl⟩, rfl, rfl, H, hH, hr, hc⟩

/-- At the proposer, `L`'s opponents are at most the three `X` voters: `H` is not in `Φp`. -/
theorem opponents_Φp_L :
    opponents sp7 Φp V 2 bL ⊆ ((({3, 4, 5} : Finset (Fin 7)) : Set (Fin 7))) := by
  intro i hi
  obtain ⟨H, hH, hr, hc⟩ := mem_opponents.1 hi
  have hi7 : i.val < 7 := i.isLt
  have hL : bL ∈ Φp.tree := Or.inr (Or.inr rfl)
  rcases hH with rfl | rfl | rfl
  · exact absurd (Or.inl (edge (Or.inl rfl) hL rfl)) hc
  · have h3 : i.val = 3 ∨ i.val = 4 ∨ i.val = 5 := by
      simp only [bX, head] at hr; split_ifs at hr <;> omega
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, Fin.ext_iff]
    exact h3
  · exact absurd (Or.inl Relation.ReflTransGen.refl) hc

/-- At the voter, `L`'s opponents include the three `X` voters and the `H` voter. -/
theorem opponents_Φy_L :
    ((({3, 4, 5, 6} : Finset (Fin 7)) : Set (Fin 7))) ⊆ opponents sp7 Φy V 2 bL := by
  intro i hi
  have hX : bX ∈ Φy.tree := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have hH : bH ∈ Φy.tree := Or.inr (Or.inl rfl)
  have hL : bL ∈ Φy.tree := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  refine mem_opponents.2 ?_
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact ⟨bX, hX, rfl, not_compatible Φy_sub hX hL (by decide) (by decide)⟩
  · exact ⟨bX, hX, rfl, not_compatible Φy_sub hX hL (by decide) (by decide)⟩
  · exact ⟨bX, hX, rfl, not_compatible Φy_sub hX hL (by decide) (by decide)⟩
  · exact ⟨bH, hH, rfl, not_compatible Φy_sub hH hL (by decide) (by decide)⟩

/-- At the voter, `F`'s opponents are at most the `H` voter. -/
theorem opponents_Φy_F :
    opponents sp7 Φy V 2 bF ⊆ ((({6} : Finset (Fin 7)) : Set (Fin 7))) := by
  intro i hi
  obtain ⟨H, hH, hr, hc⟩ := mem_opponents.1 hi
  have hi7 : i.val < 7 := i.isLt
  have hFt : bF ∈ Φy.tree := Or.inr (Or.inr (Or.inl rfl))
  rcases hH with rfl | rfl | rfl | rfl | rfl
  · exact absurd (Or.inl (Φy_rooted _ hFt)) hc
  · have h6 : i.val = 6 := by
      simp only [bH, head] at hr; split_ifs at hr <;> omega
    simp only [Finset.coe_singleton, Set.mem_singleton_iff, Fin.ext_iff]
    exact h6
  · exact absurd (Or.inl Relation.ReflTransGen.refl) hc
  · exact absurd (Or.inr (edge hFt (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) rfl)) hc
  · exact absurd (Or.inr (edge hFt (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) rfl)) hc

/-- A deepest block of a set is the one `deepest` returns. -/
private theorem deepest_eq_of_isDeepest {Φ : Frm sp7.n Unit} {S : Set Bk} {D : Bk}
    (h : IsDeepest Φ S D) : deepest Φ S = some D := by
  have hex : ∃ B, IsDeepest Φ S B := ⟨D, h⟩
  cases hd : deepest Φ S with
  | none =>
    unfold deepest at hd
    simp only [hex, ↓reduceDIte, reduceCtorEq] at hd
  | some D' =>
    have h' := deepest_mem hd
    by_contra hne
    have hne' : D' ≠ D := fun h => hne (congrArg some h)
    rcases h.2 D' h'.1 hne' with h₁ | ⟨h₁, h₂⟩ <;>
      rcases h'.2 D h.1 (Ne.symm hne') with h₃ | ⟨h₃, h₄⟩ <;> omega

/-- **The target of `unlock` depends on the frame.** Against the same view `V` of seven slot-2
votes (three on `L`, three on `X`, one on `H`; no equivocators), the lock on `L` is moved by
`unlockTarget` as follows:
* in the proposer's frame `Φp` (`Σ.F = F`), it stays on `L`: `H` is not in `Φp`'s tree, so `L` has
  at most the three `X` voters as opponents and `2 · 3 < 7`;
* in the voter's frame `Φy` (`Σ.F = G ≺ F`), it moves back to `F`, which does not extend `L`:
  the `H` voter is now an opponent too, so `L` has at least four opponents and `2 · 4 ≥ 7`.

Both frames are well formed (`frameOK_Φp`, `frameOK_Φy`), `Φp`'s tree is contained in `Φy`'s,
and `Φy.F ⪯ Φp.F`.

**What it shows.** `opponents` counts only support votes whose head is in the frame's tree, so
`unlockTarget` depends on the frame. A lock that survives the proposer's `unlock` need not
survive the voter's, even against the same votes. That is the step HS.3 (a) needs and the
retired leaf `voter_unlock_keeps_lock` (AgreeLater, removed in 61076d7f) stated: that a live lock
block of the voter's read point extends the proposer's lock `L`. The proposer's survival does
not transfer to the voter by the view comparison alone.

**What it does not show.** This is a configuration of the lock code, not a trace. It does not
show that the configuration is reachable under `AgreeSetting` (a Goldilocks run with the HS
shared premises, settled, with a ready proposal), nor that `voter_unlock_keeps_lock` or HS.3 (a)
(`FrozenTreeAgreement`) is false. In particular it does not construct the run's FG histories with
the voter's `Σ.F` below the proposer's, the honest locks that HS.3 (a)'s start premise requires,
or a vote that differs from the proposal. -/
theorem unlockTarget_frame_dependent :
    unlockTarget sp7 Φp V 2 bL = bL ∧ unlockTarget sp7 Φy V 2 bL = bF ∧
      ¬ Φy.Anc bL (unlockTarget sp7 Φy V 2 bL) ∧
      Φp.tree ⊆ Φy.tree ∧ Φy.Anc Φy.F Φp.F ∧ Φy.F ≠ Φp.F := by
  have hLp : bL ∈ Φp.tree := Or.inr (Or.inr rfl)
  have hLy : bL ∈ Φy.tree := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have hFy : bF ∈ Φy.tree := Or.inr (Or.inr (Or.inl rfl))
  have hp : unlockTarget sp7 Φp V 2 bL = bL := by
    have hlt : 2 * (opponents sp7 Φp V 2 bL).ncard < sp7.n := by
      have := Set.ncard_le_ncard opponents_Φp_L (Finset.finite_toSet _)
      rw [Set.ncard_coe_finset] at this
      change 2 * _ < 7
      have h3 : ({3, 4, 5} : Finset (Fin 7)).card = 3 := rfl
      omega
    unfold unlockTarget
    rw [deepest_eq_of_isDeepest (D := bL) ?_]
    · rfl
    exact ⟨⟨hLp, Relation.ReflTransGen.refl, hlt⟩,
      fun C hC hne => Or.inl (depth_lt_of_anc frameOK_Φp hC.2.1 hne hLp)⟩
  have hy : unlockTarget sp7 Φy V 2 bL = bF := by
    have hF : 2 * (opponents sp7 Φy V 2 bF).ncard < sp7.n := by
      have := Set.ncard_le_ncard opponents_Φy_F (Finset.finite_toSet _)
      rw [Set.ncard_coe_finset] at this
      change 2 * _ < 7
      have h1 : ({6} : Finset (Fin 7)).card = 1 := rfl
      omega
    have hL : ¬ 2 * (opponents sp7 Φy V 2 bL).ncard < sp7.n := by
      have := Set.ncard_le_ncard opponents_Φy_L (Set.toFinite _)
      rw [Set.ncard_coe_finset] at this
      change ¬ 2 * _ < 7
      have h4 : ({3, 4, 5, 6} : Finset (Fin 7)).card = 4 := rfl
      omega
    unfold unlockTarget
    rw [deepest_eq_of_isDeepest (D := bF) ?_]
    · rfl
    refine ⟨⟨hFy, edge hFy hLy rfl, hF⟩, fun C hC hne => ?_⟩
    obtain ⟨hCt, hCL, hCo⟩ := hC
    have hr := anc_roots Φy_sub hCL hLy
    rcases hCt with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (depth_lt_of_anc frameOK_Φy (edge (Or.inl rfl) hFy rfl) hne hFy)
    · exact absurd hr (by decide)
    · exact absurd rfl hne
    · exact absurd hr (by decide)
    · exact absurd hCo hL
  refine ⟨hp, hy, ?_, Φp_sub, edge (Or.inl rfl) hFy rfl, fun h => ?_⟩
  · rw [hy]; intro h; exact absurd (anc_roots Φy_sub h hFy) (by decide)
  · exact absurd (congrArg Block.root h) (by decide)

end Consensus.Goldilocks.SA.Test.UnlockFrame

end
