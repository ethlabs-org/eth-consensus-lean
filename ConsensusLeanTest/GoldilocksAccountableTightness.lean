module
public import ConsensusLean
@[expose] public section

/-! # Tightness of `AccountableSafety`'s bound `2q − n`, for every `n`

`GoldilocksFaultyWitness` meets the bound at `n = 4`. Here the same pair of chains is built for
every number `n ≥ 1` of validators (`q = ⌈2n/3⌉`): branch A is signed by `[0, q)`, branch B by
`[n − q, n)`, and each finalizes its first block. Everything is proved for all `n` at once (the
chain states by `simp`, no evaluation); `tightness_four`, `tightness_seven` and `tightness_ten`
read off `n ∈ {4, 7, 10}`. Labelled by kind (CONTRIBUTING "Statements"):

* (a) `conflicting_finalizations`: the hypotheses of `AccountableSafety` hold on the two chains,
  and the validators with a slashable pair among their attestations are exactly the overlap
  `[n − q, q)`, of size `2q − n`.
* (a) `accountable_safety_tight`: the proved `accountable_safety` applied to the two chains; any set
  it yields is the overlap. `slashable_card_le`: no set of validators with slashable pairs on these
  chains is larger than `2q − n`, so the bound of `AccountableSafety` cannot be raised. -/

namespace Consensus.Goldilocks.AccountableTightness

open FG

variable (n : Nat)

/-- The target votes of the validators `vs` at height `h` for root `T`, with finality pair `f`. -/
def tvs (vs : List (Fin n)) (h T : Nat) (f : Option (Nat × Nat)) : List (Att n) :=
  vs.map fun v => ⟨v, h, T, false, f⟩

theorem mem_tvs (vs : List (Fin n)) (h T : Nat) (f : Option (Nat × Nat)) (a : Att n) :
    a ∈ tvs n vs h T f ↔ ∃ v ∈ vs, (⟨v, h, T, false, f⟩ : Att n) = a := by
  simp [tvs]

/-- Counting target votes for the chain's own entry, without a finality pair. -/
theorem foldl_tvs_none (vs : List (Fin n)) (σ : ChainState n) (h T : Nat) (hh : σ.h = h)
    (hT : σ.Th = T) :
    (tvs n vs h T none).foldl ChainState.processAtt σ =
      { σ with prog := σ.prog ∪ vs.toFinset, target := σ.target ∪ vs.toFinset } := by
  induction vs generalizing σ with
  | nil => simp [tvs]
  | cons v vs ih =>
    simp only [tvs, List.map_cons, List.foldl_cons] at ih ⊢
    rw [ih _ (by simp [ChainState.processAtt, hh, hT]) (by simp [ChainState.processAtt, hh, hT])]
    simp [ChainState.processAtt, hh, hT]

/-- Counting target votes for the chain's own entry, with a pending finality pair `p`. -/
theorem foldl_tvs_some (vs : List (Fin n)) (σ : ChainState n) (h T : Nat) (p : Nat × Nat)
    (hh : σ.h = h) (hT : σ.Th = T) (hp : p ∈ σ.pending) :
    (tvs n vs h T (some p)).foldl ChainState.processAtt σ =
      { σ with prog := σ.prog ∪ vs.toFinset, target := σ.target ∪ vs.toFinset,
               fin := Function.update σ.fin p.1 (σ.fin p.1 ∪ vs.toFinset) } := by
  induction vs generalizing σ with
  | nil => simp [tvs]
  | cons v vs ih =>
    simp only [tvs, List.map_cons, List.foldl_cons] at ih ⊢
    rw [ih _ (by simp [ChainState.processAtt, hh, hT, hp])
      (by simp [ChainState.processAtt, hh, hT, hp]) (by simp [ChainState.processAtt, hh, hT, hp])]
    simp [ChainState.processAtt, hh, hT, hp]

/-- The validators `[a, b)` with `b ≤ n` are `b − a`. -/
theorem card_filter_Ico (a b : Nat) (hb : b ≤ n) :
    (Finset.univ.filter fun v : Fin n => a ≤ v.val ∧ v.val < b).card = b - a := by
  have h : (Finset.univ.filter fun v : Fin n => a ≤ v.val ∧ v.val < b).map Fin.valEmbedding =
      Finset.Ico a b := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact hv
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map, h, Nat.card_Ico]

variable [NeZero n]

/-- `n` validators, `δt = 2`, genesis root `0`. -/
abbrev gp : FGParams := ⟨n, Nat.pos_of_neZero n, 2, 0⟩

theorem q_le : (gp n).q ≤ n := by simp only [FGParams.q]; omega

/-- The signers of branch A: the `q` validators `[0, q)`. -/
def signersA : List (Fin n) := (List.finRange n).filter fun v => v.val < (gp n).q

/-- The signers of branch B: the `q` validators `[n − q, n)`. -/
def signersB : List (Fin n) := (List.finRange n).filter fun v => n - (gp n).q ≤ v.val

theorem signersA_card : (signersA n).toFinset.card = (gp n).q := by
  have : (signersA n).toFinset =
      Finset.univ.filter fun v : Fin n => 0 ≤ v.val ∧ v.val < (gp n).q := by
    ext v; simp [signersA]
  rw [this, card_filter_Ico n _ _ (q_le n)]; rfl

theorem signersB_card : (signersB n).toFinset.card = (gp n).q := by
  have : (signersB n).toFinset =
      Finset.univ.filter fun v : Fin n => n - (gp n).q ≤ v.val ∧ v.val < n := by
    ext v; simp [signersB]
  rw [this, card_filter_Ico n _ _ le_rfl]
  have := q_le n
  omega

/-- Branch A, signed by `[0, q)`: blocks `1, 2, 3` on genesis, each carrying a target quorum for
the current entry, with the predecessor as finality pair from height `2` on. -/
def chainA : List (FGBlock n) :=
  [⟨1, 1, 0, tvs n (signersA n) 1 0 none⟩, ⟨2, 2, 0, tvs n (signersA n) 2 1 (some (1, 0))⟩,
   ⟨3, 3, 0, tvs n (signersA n) 3 2 (some (2, 1))⟩]

/-- Branch B, signed by `[n − q, n)`: blocks `11, 12, 13` on genesis, finalizing `11`. -/
def chainB : List (FGBlock n) :=
  [⟨11, 1, 0, tvs n (signersB n) 1 0 none⟩, ⟨12, 2, 0, tvs n (signersB n) 2 11 (some (1, 0))⟩,
   ⟨13, 3, 0, tvs n (signersB n) 3 12 (some (2, 11))⟩]

/-- The attestations of the two chains. -/
def bothAtts : List (Att n) := (gp n).chainAtts (chainA n) ++ (gp n).chainAtts (chainB n)

/-- The overlap `[n − q, q)`: the validators that sign both branches. -/
def overlap : Finset (Fin n) :=
  Finset.univ.filter fun v => n - (gp n).q ≤ v.val ∧ v.val < (gp n).q

/-- The validators with a slashable pair among the attestations of the two chains. -/
def convicted : Finset (Fin n) :=
  Finset.univ.filter fun v => ∃ a ∈ bothAtts n, ∃ b ∈ bothAtts n, a.val = v ∧ slashable a b

/-- A three-block branch on genesis whose blocks carry target votes of at least `q` validators
finalizes its first block. -/
theorem branch_F (vs : List (Fin n)) (hvs : (gp n).q ≤ vs.toFinset.card) (r₁ r₂ r₃ : Nat) :
    ((gp n).chainState
      [⟨r₁, 1, 0, tvs n vs 1 0 none⟩, ⟨r₂, 2, 0, tvs n vs 2 r₁ (some (1, 0))⟩,
       ⟨r₃, 3, 0, tvs n vs 3 r₂ (some (2, r₁))⟩]).map (fun σ => σ.F) = some r₁ := by
  simp [FGParams.chainState, FGParams.stateTransition, ChainState.init, foldl_tvs_none,
    foldl_tvs_some, mem_tvs, FGParams.heightEvents, FGParams.finalizePrune, FGParams.bestFinal,
    FGParams.justifies, FGParams.timesOut, ChainState.advance,
    ChainState.previousHeightJustified, ChainState.validAtt, Att.WellFormed, hvs, FGParams.KW]

theorem mem_bothAtts (a : Att n) : a ∈ bothAtts n ↔
    (∃ v : Fin n, v.val < (gp n).q ∧ (⟨v, 1, 0, false, none⟩ : Att n) = a) ∨
    (∃ v : Fin n, v.val < (gp n).q ∧ (⟨v, 2, 1, false, some (1, 0)⟩ : Att n) = a) ∨
    (∃ v : Fin n, v.val < (gp n).q ∧ (⟨v, 3, 2, false, some (2, 1)⟩ : Att n) = a) ∨
    (∃ v : Fin n, n ≤ v.val + (gp n).q ∧ (⟨v, 1, 0, false, none⟩ : Att n) = a) ∨
    (∃ v : Fin n, n ≤ v.val + (gp n).q ∧ (⟨v, 2, 11, false, some (1, 0)⟩ : Att n) = a) ∨
    (∃ v : Fin n, n ≤ v.val + (gp n).q ∧ (⟨v, 3, 12, false, some (2, 11)⟩ : Att n) = a) := by
  simp [bothAtts, FGParams.chainAtts, chainA, chainB, tvs, signersA, signersB]

/-- The convicted validators are the overlap: an overlap validator votes for `1` and for `11` at
height `2` (E2), and the votes of one branch are not slashable with each other. -/
theorem convicted_eq_overlap : convicted n = overlap n := by
  ext v
  simp only [convicted, overlap, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, b, hb, rfl, hab⟩
    rw [mem_bothAtts] at ha hb
    rcases ha with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ |
        ⟨x, hx, rfl⟩ <;>
      rcases hb with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ |
        ⟨y, hy, rfl⟩ <;>
      simp [slashable, e1, e2] at hab ⊢ <;>
      omega
  · rintro ⟨h1, h2⟩
    refine ⟨⟨v, 2, 1, false, some (1, 0)⟩, (mem_bothAtts n _).mpr ?_,
      ⟨v, 2, 11, false, some (1, 0)⟩, (mem_bothAtts n _).mpr ?_, rfl, ?_⟩
    · exact Or.inr (Or.inl ⟨v, h2, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, by omega, rfl⟩))))
    · simp [slashable, e2]

/-- The overlap has `2q − n` validators. -/
theorem overlap_card : (overlap n).card = 2 * (gp n).q - n := by
  have := q_le n
  rw [overlap, card_filter_Ico n _ _ this]
  omega

/-- (a) The hypotheses of `AccountableSafety` for `n` validators: chain A finalizes `1`, chain B
finalizes `11`, and neither finalized block is on the other chain. Exactly the `2q − n`
validators of the overlap `[n − q, q)` are convicted. -/
theorem conflicting_finalizations :
    ∃ σA σB : ChainState (gp n).n, (gp n).chainState (chainA n) = some σA ∧
      (gp n).chainState (chainB n) = some σB ∧ σA.F = 1 ∧ σB.F = 11 ∧
      σA.F ∉ (gp n).roots (chainB n) ∧ σB.F ∉ (gp n).roots (chainA n) ∧
      convicted n = overlap n ∧ (convicted n).card = 2 * (gp n).q - (gp n).n := by
  obtain ⟨σA, hσA, hFA⟩ := Option.map_eq_some_iff.mp
    (branch_F n (signersA n) (signersA_card n).ge 1 2 3)
  obtain ⟨σB, hσB, hFB⟩ := Option.map_eq_some_iff.mp
    (branch_F n (signersB n) (signersB_card n).ge 11 12 13)
  refine ⟨σA, σB, hσA, hσB, hFA, hFB, ?_, ?_, convicted_eq_overlap n, ?_⟩
  · rw [hFA]; simp [FGParams.roots, chainB]
  · rw [hFB]; simp [FGParams.roots, chainA]
  · rw [convicted_eq_overlap, overlap_card]

/-- Every set of validators with a slashable pair among the attestations of the two chains lies
in the overlap, so it has at most `2q − n` validators. -/
theorem slashable_card_le (S : Finset (Fin n))
    (hS : ∀ v ∈ S, ∃ a ∈ bothAtts n, ∃ b ∈ bothAtts n, a.val = v ∧ slashable a b) :
    S ⊆ overlap n ∧ S.card ≤ 2 * (gp n).q - n := by
  have hsub : S ⊆ overlap n := by
    rw [← convicted_eq_overlap]
    exact fun v hv => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS v hv⟩
  exact ⟨hsub, overlap_card n ▸ Finset.card_le_card hsub⟩

/-- (a) `AccountableSafety`'s conclusion on the two chains: the proved `accountable_safety` yields
a set of at least `2q − n` validators, each with a slashable pair among their attestations, and
any such set is the overlap. -/
theorem accountable_safety_tight :
    ∃ S : Finset (Fin (gp n).n), 2 * (gp n).q - (gp n).n ≤ S.card ∧ S = overlap n ∧
      ∀ v ∈ S, ∃ a ∈ bothAtts n, ∃ b ∈ bothAtts n, a.val = v ∧ slashable a b := by
  obtain ⟨σA, σB, hσA, hσB, -, -, h1, h11, -⟩ := conflicting_finalizations n
  obtain ⟨S, hS, hv⟩ := accountable_safety (gp n) (chainA n) (chainB n) σA σB hσA hσB h1 h11
  obtain ⟨hsub, -⟩ := slashable_card_le n S hv
  refine ⟨S, hS, Finset.eq_of_subset_of_card_le hsub ?_, hv⟩
  rw [overlap_card]
  exact hS

/-- `n = 4`: `q = 3`, and `accountable_safety` convicts exactly `{1, 2}`, `2q − n = 2`. -/
theorem tightness_four :
    (gp 4).q = 3 ∧ 2 * (gp 4).q - 4 = 2 ∧ overlap 4 = {1, 2} ∧
      ∃ S : Finset (Fin 4), 2 ≤ S.card ∧ S = {1, 2} ∧
        ∀ v ∈ S, ∃ a ∈ bothAtts 4, ∃ b ∈ bothAtts 4, a.val = v ∧ slashable a b := by
  have h : overlap 4 = {1, 2} := by decide
  obtain ⟨S, hS, rfl, hv⟩ := accountable_safety_tight 4
  exact ⟨by decide, by decide, h, _, hS, h, hv⟩

/-- `n = 7`: `q = 5`, and `accountable_safety` convicts exactly `{2, 3, 4}`, `2q − n = 3`. -/
theorem tightness_seven :
    (gp 7).q = 5 ∧ 2 * (gp 7).q - 7 = 3 ∧ overlap 7 = {2, 3, 4} ∧
      ∃ S : Finset (Fin 7), 3 ≤ S.card ∧ S = {2, 3, 4} ∧
        ∀ v ∈ S, ∃ a ∈ bothAtts 7, ∃ b ∈ bothAtts 7, a.val = v ∧ slashable a b := by
  have h : overlap 7 = {2, 3, 4} := by decide
  obtain ⟨S, hS, rfl, hv⟩ := accountable_safety_tight 7
  exact ⟨by decide, by decide, h, _, hS, h, hv⟩

/-- `n = 10`: `q = 7`, and `accountable_safety` convicts exactly `{3, 4, 5, 6}`, `2q − n = 4`. -/
theorem tightness_ten :
    (gp 10).q = 7 ∧ 2 * (gp 10).q - 10 = 4 ∧ overlap 10 = {3, 4, 5, 6} ∧
      ∃ S : Finset (Fin 10), 4 ≤ S.card ∧ S = {3, 4, 5, 6} ∧
        ∀ v ∈ S, ∃ a ∈ bothAtts 10, ∃ b ∈ bothAtts 10, a.val = v ∧ slashable a b := by
  have h : overlap 10 = {3, 4, 5, 6} := by decide
  obtain ⟨S, hS, rfl, hv⟩ := accountable_safety_tight 10
  exact ⟨by decide, by decide, h, _, hS, h, hv⟩

end Consensus.Goldilocks.AccountableTightness

end
