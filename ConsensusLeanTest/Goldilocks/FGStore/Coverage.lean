module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service
public import ConsensusLeanTest.Goldilocks.FGStore.TimeoutEntry
@[expose] public section

/-! # Witness for G1.8 (b), coverage after failed entries (FGStore)

`Coverage` applied on an extension `trV` of the timeout-entry trace `trT` (`P₁`: `Δ = 1`,
`δ_t = 2`, `q = 1`; one node `w₀`, honest), with every premise realized: `T₁ = Bf` (the entry of
height `3`, slot `2`) strictly below `T = Bc` (the entry of height `4`, slot `5`, reached by a
timeout, previous height not justified), the only entry between them being `Bc`; `T`'s good
window served by `Bx` (which justifies `Bc` and enters height `5` with entry `Bx`), and the good
window of that actual successor entry `Bx` served by `By`, which finalizes `(4, Bc)`. Labelled by
kind (CONTRIBUTING "Statements"): (a) `trV_localRun`, `trV_goodWindow_Bc`, `trV_goodWindow_Bx`,
`trV_coverage_premises`, `trV_coverage`, `trV_coverage_witness`.

**The trace `trV`.** Cuts `0`–`14` are those of `trT` (`trV_agree`). Then (cut, time: label,
effect):
* `15`, `6`: attest with source `Bx`, sign `aX = (5, Bx, target, (4, Bc))`: `Bx`'s previous
  height is justified, so the row carries `σ[Bx]`'s predecessor `(h_j, J) = (4, Bc)`, which the
  record `ΛC` permits;
* `16`, `6`: process `aX`;
* `17`, `7`: accept the own proposal `By` (root `6`, slot `7`, on `Bx`, payload `[aX]`): `aX` is
  a finality quorum for `(4, Bc)` and a target quorum for `Bx`, so `σ[By]` finalizes `Bc`
  (`F = Bc`, `h_F = 4`), justifies `Bx` (`J = Bx`, `h_j = 5`) and enters height `6`; the FG state
  moves `Σ.F` to `Bc`.

Then it stutters. The second window is `a₁ = 0`, `c_F = 1`, `k_F = 0`: `Bx.slot + 1 = 7 =
By.slot`, and `aX` is signed at time `6 ≤ t_6 + 6Δ`. `Coverage`'s slot bound is then
`T₁.slot + (T.slot − T₁.slot) + D₀ + D₁ = 2 + 3 + 1 + 1 = 7`, attained: the only witness is
`By`, of slot `7` (`trV_coverage_witness`). -/

namespace Consensus.Goldilocks.Store.Test

/-! ## The second window: `aX` and `By` -/

/-- `w₀`'s target vote for `Bx` at height `5`, with `σ[Bx]`'s predecessor `(4, Bc)` as its
finality pair. -/
def aX : FG.Att P₁.n := ⟨w₀, 5, 5, false, some (4, 4)⟩

/-- `w₀`'s record after signing `aX`. -/
def ΛX : FG.Record := ΛC.recordAtt aX

/-- On `stX` and `ΛC`, `fg_attest` with source `Bx` signs `aX`: `ΛC` permits `(4, Bc)`. -/
theorem attest_stX : stX.attest ΛC w₀ Bx = some (aX, ΛX) := rfl

/-- `stX` with `aX` pooled. -/
def stXa : Store P₁ Unit := { stX with atts := [a₀, a₁, aK, aF, aC, aX] }

/-- `w₀`'s proposal of slot `7` on `Bx` carrying `aX`: root `6`. -/
def By : NodeBlock P₁ Unit := ⟨6, some 5, 7, w₀, 0, [aX], ()⟩

/-- The chain state of `By`: `aX` sets the finality bit of `(4, Bc)`, so `(4, Bc)` is finalized
(`F = 4`, `h_F = 4`) and pruned; `aX` is also a target quorum for `Bx`, whose previous height is
justified and `h_F = h_j`, so `By` justifies `Bx` (`J = 5`, `h_j = 5`, pending `[(5, 5)]`) and
enters height `6` with entry `By`. -/
def σBy : FG.ChainState P₁.n where
  L := 6
  s := 7
  h := 6
  Th := 6
  ThSlot := 7
  target := ∅
  prog := ∅
  pending := [(5, 5)]
  fin := Function.update (Function.update σBx.fin 4 (insert w₀ ∅)) 5 ∅
  J := 5
  hj := 5
  F := 4
  hF := 4

/-- `state_transition` of `By` from `σBx` gives `σBy`. -/
theorem stateTransition_By : P₁.fg.stateTransition (stXa.σ 5) By.fgView = some σBy := rfl

/-- `stXa` with `By` and its chain state added (before the finality update). -/
def stY₀ : Store P₁ Unit :=
  { stXa with
    blocks := Function.update stXa.blocks 6 (some By)
    σ := Function.update stXa.σ 6 σBy }

/-- `stY₀` after the `h_max` and justification steps: `h_max = 6`, cache `(5, Bx)`. -/
def stY₁ : Store P₁ Unit := { stY₀ with J := Bx, hj := 5, hmax := 6 }

/-- The FG state after accepting `By` on `stXa`: `By` and `σBy` added, `h_max = 6`, the
justification cache at `Bx` with height `5`, and `F` moved to `Bc`. -/
def stY : Store P₁ Unit := { stY₁ with F := Bc }

/-- `stY` holds genesis, `Bs`, `Bf`, `Bk`, `Bc`, `Bx` and `By`. -/
theorem mem_tree_stY {X : NodeBlock P₁ Unit} (h : X ∈ stY.tree) :
    X = g₁ ∨ X = Bs ∨ X = Bf ∨ X = Bk ∨ X = Bc ∨ X = Bx ∨ X = By := by
  change Function.update stX.blocks 6 (some By) X.root = some X at h
  rcases eq_or_of_update h with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · exact (mem_tree_stX h).imp_right
      (Or.imp_right (Or.imp_right (Or.imp_right (Or.imp_right Or.inl))))

open Classical in
/-- The finality update of `By` on `stY₀` gives `stY`: the justification step takes `(5, Bx)`,
and the finalization step moves `Σ.F` from genesis to `Bc` (`Bc ⪯ Σ.J = Bx`, and `By` is a
viable descendant: its height `6` is `h_max`). -/
theorem updateFinality_stY₀ : stY₀.updateFinality σBy = stY := by
  unfold updateFinality
  extract_lets st₁ st₂
  have h2 : st₂ = stY₁ := by
    change (match st₁.blocks 5 with
      | some X => if st₁.Anc st₁.F X ∧ LexLt (st₁.hj, st₁.J.root) (5, 5) then
          { st₁ with J := X, hj := 5 } else st₁
      | none => st₁) = stY₁
    rw [show st₁.blocks 5 = some Bx from rfl]
    dsimp only
    have hgx : st₁.Anc g₁ Bx :=
      (anc_g₁_Bc (S := st₁.tree) rfl rfl rfl rfl).tail (b := Bc) ⟨rfl, rfl, rfl⟩
    rw [ite_eq_left ⟨hgx, Or.inl (by decide)⟩]
    rfl
  have hgc : stY₁.Anc g₁ Bc := anc_g₁_Bc (S := stY₁.tree) rfl rfl rfl rfl
  have hcx : stY₁.Anc Bc Bx := Relation.ReflTransGen.single (b := Bx) ⟨rfl, rfl, rfl⟩
  have hcy : stY₁.Anc Bc By := hcx.tail (c := By) ⟨rfl, rfl, rfl⟩
  rw [h2, show stY₁.blocks σBy.F = some Bc from rfl]
  dsimp only
  rw [ite_eq_left ⟨hgc, fun h => absurd (congrArg Block.root h) (by decide), hcx, By, rfl, hcy,
    (headHeightFloor_bounds stY₁).2⟩]
  rfl

/-- `stXa` accepts `By`, with post-state `stY` (`aX` is pooled already). -/
theorem onBlock_stXa_By : stXa.onBlock By = some stY := by
  have hgc : Goldilocks.Anc (insert By stXa.tree) g₁ Bc :=
    anc_g₁_Bc (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
  have hgx : Goldilocks.Anc (insert By stXa.tree) g₁ Bx := hgc.tail ⟨Or.inr rfl, Or.inr rfl, rfl⟩
  have hanc : Goldilocks.Anc (insert By stXa.tree) stXa.F By :=
    hgx.tail ⟨Or.inr rfl, Or.inl rfl, rfl⟩
  have hneg : ¬ ((stXa.blocks By.root).isSome = true ∨ (stXa.blocks 5).isNone = true ∨
      ¬ Goldilocks.Anc (insert By stXa.tree) stXa.F By) := by
    rintro (h | h | h)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact h hanc
  unfold onBlock
  split
  · next h => cases h
  next pr h =>
  cases h
  simp only [hneg, ↓reduceIte]
  split
  · next h => rw [stateTransition_By] at h; cases h
  next σ' h =>
  rw [stateTransition_By] at h; cases h
  change some ((updateFinality stY₀ σBy).addAtts [aX]) = some stY
  rw [updateFinality_stY₀]
  rfl

/-! ## The trace `trV` -/

/-- The coverage trace: `trT`'s cuts `0`–`14`, then the target vote `aX` for `Bx` at time `6`
and the own proposal `By` at time `7`; then it stutters. -/
def trV : FGTrace P₁ Unit where
  init _ := (Store.init (), FG.Record.empty)
  node _ := w₀
  time i := if i < 2 then 0 else if i < 5 then 1 else if i < 6 then 2 else if i < 9 then 3
    else if i < 11 then 4 else if i < 14 then 5 else if i < 17 then 6 else 7
  event i := if i < 2 then 0 else if i < 5 then 1 else if i < 6 then 2 else if i < 9 then 3
    else if i < 11 then 4 else if i < 14 then 5 else if i < 17 then 6 else 7
  pos
    | 1 => 1
    | 3 => 1
    | 4 => 2
    | 7 => 1
    | 8 => 2
    | 10 => 1
    | 12 => 1
    | 13 => 2
    | 15 => 1
    | 16 => 2
    | _ => 0
  label
    | 0 => some (.attest g₁ (some a₀))
    | 1 => some (.attestation a₀)
    | 2 => some (.block Bs true)
    | 3 => some (.attest Bs (some a₁))
    | 4 => some (.attestation a₁)
    | 5 => some (.block Bf true)
    | 6 => some (.block Bk true)
    | 7 => some (.attest Bk (some aK))
    | 8 => some (.attestation aK)
    | 9 => some (.attest Bf (some aF))
    | 10 => some (.attestation aF)
    | 11 => some (.block Bc true)
    | 12 => some (.attest Bc (some aC))
    | 13 => some (.attestation aC)
    | 14 => some (.block Bx true)
    | 15 => some (.attest Bx (some aX))
    | 16 => some (.attestation aX)
    | 17 => some (.block By true)
    | _ => none
  post
    | 0 => (Store.init (), Λ₀)
    | 1 => (stA, Λ₀)
    | 2 => (stBs, Λ₀)
    | 3 => (stBs, Λ₁)
    | 4 => (stBa, Λ₁)
    | 5 => (stBf, Λ₁)
    | 6 => (stK, Λ₁)
    | 7 => (stK, ΛK)
    | 8 => (stKa, ΛK)
    | 9 => (stKa, ΛF)
    | 10 => (stKb, ΛF)
    | 11 => (stC, ΛF)
    | 12 => (stC, ΛC)
    | 13 => (stCa, ΛC)
    | 14 => (stX, ΛC)
    | 15 => (stX, ΛX)
    | 16 => (stXa, ΛX)
    | _ => (stY, ΛX)
  awake _ _ := True

/-- `trV` agrees with `trT` on the labels and post-states of cuts `0`–`14`. -/
theorem trV_agree (i : Nat) (hi : i ≤ 14) :
    trV.label i = trT.label i ∧ trV.post i = trT.post i := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    first | exact ⟨rfl, rfl⟩ | omega

/-- `trV` agrees with `trT` on the times of cuts `0`–`16`. -/
theorem trV_time (i : Nat) (hi : i < 17) : trV.time i = trT.time i := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    first | rfl | omega

/-- The labelled cuts of `trV`: those of `trT` up to cut `14`, then `15`–`17`. -/
theorem trV_label (i : Nat) (ℓ : FGLabel P₁ Unit) (h : trV.label i = some ℓ) :
    (i ≤ 14 ∧ trT.label i = some ℓ) ∨ (i = 15 ∧ ℓ = .attest Bx (some aX)) ∨
      (i = 16 ∧ ℓ = .attestation aX) ∨ (i = 17 ∧ ℓ = .block By true) := by
  by_cases hi : i ≤ 14
  · exact Or.inl ⟨hi, (trV_agree i hi).1 ▸ h⟩
  · obtain rfl | rfl | rfl | h18 : i = 15 ∨ i = 16 ∨ i = 17 ∨ 18 ≤ i := by omega
    · exact Or.inr (Or.inl ⟨rfl, (Option.some.inj h).symm⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, (Option.some.inj h).symm⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, (Option.some.inj h).symm⟩))
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h18
      simp [trV] at h

/-- After a labelled cut `i ≤ 17` of `trV`, the state of `w₀` is the cut's post-state. -/
theorem trV_state_succ (i : Nat) (hi : i ≤ 17) : trV.state w₀ (i + 1) = trV.post i := by
  have h : trV.node i = w₀ ∧ trV.label i ≠ none := by
    refine ⟨rfl, ?_⟩
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
      first | (dsimp only [trV]; exact Option.some_ne_none _) | omega
  rw [Trace.state, ite_eq_left h]

/-- Before cuts `0`–`15`, the state of `w₀` in `trV` is the one in `trT`. -/
theorem trV_state_eq (i : Nat) (hi : i ≤ 15) : trV.state w₀ i = trT.state w₀ i := by
  rcases i with _ | i
  · rfl
  · rw [trV_state_succ i (by omega), trT_state_succ i (by omega)]
    exact (trV_agree i (by omega)).2

/-- The states of `w₀` before cuts `15`, `16`, `17` and after cut `17` of `trV`. -/
theorem trV_state :
    trV.state w₀ 15 = (stX, ΛC) ∧ trV.state w₀ 16 = (stX, ΛX) ∧
      trV.state w₀ 17 = (stXa, ΛX) ∧ ∀ i, trV.state w₀ (i + 18) = (stY, ΛX) := by
  refine ⟨trV_state_succ 14 (by omega), trV_state_succ 15 (by omega),
    trV_state_succ 16 (by omega), fun i => ?_⟩
  induction i with
  | zero => exact trV_state_succ 17 le_rfl
  | succ i ih => rw [Trace.state, ite_eq_right (by simp [trV])]; exact ih

/-- The FG state of `w₀` before and after cuts `14` and `17` of `trV`. -/
theorem trV_store :
    trV.store w₀ 14 = stCa ∧ trV.store w₀ (14 + 1) = stX ∧ trV.store w₀ 17 = stXa ∧
      trV.store w₀ (17 + 1) = stY :=
  ⟨(congrArg Prod.fst (trV_state_eq 14 (by omega))).trans trT_store.1,
    congrArg Prod.fst trV_state.1, congrArg Prod.fst trV_state.2.2.1,
    congrArg Prod.fst (trV_state.2.2.2 0)⟩

/-- `U` of `trV` (genesis, `Bs`, `Bf`, `Bk`, `Bc`, `Bx`, `By`) is coherent. -/
theorem trV_coherent : Coherent ({g₁, Bs, Bf, Bk, Bc, Bx, By} : Set (NodeBlock P₁ Unit)) := by
  refine ⟨?_, ?_⟩
  · rintro X (rfl | rfl | rfl | rfl | rfl | rfl | rfl) Y (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      h <;> first | rfl | exact absurd h (by decide)
  · rintro X (rfl | rfl | rfl | rfl | rfl | rfl | rfl) Y (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      h <;> first | decide | exact absurd h (by decide)

/-- Each call of `trV` executes the FG on its pre-state. -/
theorem trV_exec (i : Nat) (ℓ : FGLabel P₁ Unit) (h : trV.label i = some ℓ) :
    FGLabel.Step (trV.node i) (trV.state (trV.node i) i) ℓ (trV.post i) := by
  rcases trV_label i ℓ h with ⟨hi, h'⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · change FGLabel.Step w₀ (trV.state w₀ i) ℓ (trV.post i)
    rw [trV_state_eq i (by omega), (trV_agree i hi).2]
    exact trT_exec i ℓ h'
  · change FGLabel.Step w₀ (trV.state w₀ 15) _ (stX, ΛX)
    rw [trV_state.1]
    exact ⟨rfl, by rw [attest_stX]; exact ⟨rfl, rfl⟩⟩
  · change FGLabel.Step w₀ (trV.state w₀ 16) _ (stXa, ΛX)
    rw [trV_state.2.1]
    rfl
  · change FGLabel.Step w₀ (trV.state w₀ 17) _ (stY, ΛX)
    rw [trV_state.2.2.1]
    exact Or.inl ⟨rfl, onBlock_stXa_By, rfl⟩

/-- Every block that `w₀` holds in `trV` lies in `{genesis, Bs, Bf, Bk, Bc, Bx, By}`. -/
theorem trV_tree_subset (y : Fin P₁.n) (i : Nat) :
    (trV.store y i).tree ⊆ ({g₁, Bs, Bf, Bk, Bc, Bx, By} : Set (NodeBlock P₁ Unit)) := by
  intro X hX
  obtain rfl := eq_w₀ y
  have hX' (h : X = g₁ ∨ X = Bs ∨ X = Bf ∨ X = Bk ∨ X = Bc ∨ X = Bx) :
      X ∈ ({g₁, Bs, Bf, Bk, Bc, Bx, By} : Set (NodeBlock P₁ Unit)) :=
    h.imp_right (Or.imp_right (Or.imp_right (Or.imp_right (Or.imp_right Or.inl))))
  by_cases hi : i ≤ 15
  · rw [FGTrace.store, trV_state_eq i hi] at hX
    exact hX' (trT_tree_subset w₀ i hX)
  · obtain rfl | rfl | h18 : i = 16 ∨ i = 17 ∨ 18 ≤ i := by omega
    · rw [FGTrace.store, trV_state.2.1] at hX; exact hX' (mem_tree_stX hX)
    · rw [FGTrace.store, trV_state.2.2.1] at hX; exact hX' (mem_tree_stX hX)
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h18
      rw [FGTrace.store, trV_state.2.2.2] at hX; exact mem_tree_stY hX

/-- From cut `17` on, the time of `trV` is `7`. -/
private theorem trV_time_tail (i : Nat) : trV.time (i + 17) = 7 := by
  simp only [trV]; split_ifs <;> first | rfl | omega

/-- The times of `trV` do not decrease from one cut to the next. -/
private theorem trV_time_succ : ∀ i, trV.time i ≤ trV.time (i + 1)
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 => by decide
  | i + 17 => by rw [trV_time_tail, Nat.add_right_comm, trV_time_tail]

private theorem trV_time_mono {i j : Nat} (h : i ≤ j) : trV.time i ≤ trV.time j :=
  monotone_nat_of_le_succ trV_time_succ h

/-- The tick order of `trV`, (a): each own proposal is accepted at the first cut of its time. -/
theorem trV_own_first (y : Fin P₁.n) (i : Nat) (B : NodeBlock P₁ Unit)
    (h : trV.CallAt y i (.block B true)) (k : Nat) (hk : k < i) : trV.time k < trV.time i := by
  rcases trV_label i _ h.2 with ⟨hi, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩
  · rw [trV_time k (by omega), trV_time i (by omega)]
    exact trT_own_first y i B ⟨h.1, h'⟩ k hk
  · cases h'
  · cases h'
  · exact lt_of_le_of_lt (trV_time_mono (Nat.le_pred_of_lt hk)) (by decide)

/-- The tick order of `trV`, (b): before an `attest` call at its time, only the own proposal. -/
theorem trV_attest_order (y : Fin P₁.n) (j : Nat) (src : NodeBlock P₁ Unit)
    (signed : Option (FG.Att P₁.n)) (h : trV.CallAt y j (.attest src signed)) (i : Nat)
    (ℓ : FGLabel P₁ Unit) (hij : i < j) (hi : trV.CallAt y i ℓ) (ht : trV.time i = trV.time j) :
    ∃ B acc, ℓ = .block B acc ∧ B.proposer = y ∧ P₁.slotTime B.slot = trV.time j := by
  obtain rfl := eq_w₀ y
  rcases trV_label j _ h.2 with ⟨hj, h'⟩ | ⟨rfl, -⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩
  · rw [trV_time i (by omega), trV_time j (by omega)] at ht
    rw [trV_time j (by omega)]
    exact trT_attest_order w₀ j src signed ⟨h.1, h'⟩ i ℓ hij
      ⟨hi.1, (trV_agree i (by omega)).1 ▸ hi.2⟩ ht
  · rcases trV_label i ℓ hi.2 with ⟨-, hi'⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rw [trV_time i (by omega)] at ht
      rcases trT_label i ℓ hi' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        first | exact absurd ht (by decide) | exact ⟨_, true, rfl, rfl, rfl⟩
    all_goals omega
  · cases h'
  · cases h'

/-- The own proposals of `trV` carry pooled attestations. -/
theorem trV_own_payload (y : Fin P₁.n) (i : Nat) (X : NodeBlock P₁ Unit)
    (h : trV.CallAt y i (.block X true)) (a : FG.Att P₁.n) (ha : a ∈ X.fgPayload) :
    a ∈ (trV.store y i).atts := by
  obtain rfl := eq_w₀ y
  rcases trV_label i _ h.2 with ⟨hi, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩
  · rw [FGTrace.store, trV_state_eq i (by omega)]
    exact trT_own_payload w₀ i X ⟨rfl, h'⟩ a ha
  · cases h'
  · cases h'
  · cases h'
    rw [List.mem_singleton.mp ha, trV_store.2.2.1]
    decide

/-- Every attestation processed in `trV` was signed at an earlier cut. -/
theorem trV_unforgeable (y : Fin P₁.n) (i : Nat) (a : FG.Att P₁.n) (h : trV.ProcessAt y i a) :
    ∃ j < i, trV.SignAt a.val j a := by
  obtain ⟨ℓ, hℓ, ha⟩ := h
  rcases trV_label i ℓ hℓ.2 with ⟨hi, h'⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨j, hj, src, hs⟩ := trT_unforgeable y i a ⟨ℓ, ⟨hℓ.1, h'⟩, ha⟩
    exact ⟨j, hj, src, hs.1, (trV_agree j (by omega)).1.trans hs.2⟩
  · cases ha
  · rw [List.mem_singleton.mp ha]; exact ⟨15, by omega, Bx, rfl, rfl⟩
  · rw [List.mem_singleton.mp ha]; exact ⟨15, by omega, Bx, rfl, rfl⟩

/-- (a) `trV` is an `FGLocalRun` for the honest set `{w₀}` inside
`{genesis, Bs, Bf, Bk, Bc, Bx, By}`. -/
theorem trV_localRun : FGLocalRun () {w₀} {g₁, Bs, Bf, Bk, Bc, Bx, By} trV where
  coherent := trV_coherent
  init _ _ := rfl
  exec i ℓ h _ := trV_exec i ℓ h
  tree_subset y _ i := trV_tree_subset y i
  time_nonneg i := le_trans (by decide) (trV_time_mono (Nat.zero_le i))
  time_mono i j hij := trV_time_mono hij
  attest_public _ _ _ _ _ _ := one_dvd _
  own_first y _ i X h _ _ k hk _ _ := trV_own_first y i X h k hk
  attest_order y _ j src signed h i ℓ hij hi ht := trV_attest_order y j src signed h i ℓ hij hi ht
  own_payload y _ i X h _ _ a ha := trV_own_payload y i X h a ha
  unforgeable y _ i a h _ := trV_unforgeable y i a h

/-! ## The two good windows -/

/-- (a) On `trV`, the timeout entry `Bc` has the good window of `trT_goodWindow`: `a₀ = 0`,
`c_F = 1`, `k_F = 0`, served by `Bx` at cut `14` with the rows `{aC}`. -/
theorem trV_goodWindow_Bc : GoodWindow P₁ Unit {w₀} trV 1 Bc 0 0 w₀ 14 Bx Bc {aC} := by
  refine ⟨⟨rfl, ⟨rfl, rfl⟩, rfl, rfl, ?_, rfl, ?_⟩, ?_, ?_, ⟨le_rfl, le_rfl⟩, by decide, ?_, ?_,
    ?_, ⟨by decide, by decide⟩⟩ <;> rw [trV_store.1]
  · exact (rfl : stCa.blocks 4 = some Bc)
  · intro r hr hv _
    change r ∈ [a₀, a₁, aK, aF, aC] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact List.mem_singleton_self _
  · exact ⟨rfl, rfl⟩
  · exact Relation.ReflTransGen.refl
  · intro r hr
    rw [Finset.mem_singleton.mp hr]
    exact ⟨rfl, rfl, rfl, fun h => absurd h (by decide)⟩
  · intro r hr
    rw [Finset.mem_singleton.mp hr]
    exact Or.inr fun _ => ⟨12, ⟨Bc, rfl, rfl⟩, by decide⟩
  · intro r hr
    rw [Finset.mem_singleton.mp hr]
    exact Or.inr (by decide)

/-- (a) On `trV`, the successor entry `Bx` (height `5`, slot `6`, previous height justified,
`(h_j, J) = (4, Bc)`) has a good window with `a₁ = 0`, `c_F = 1`, `k_F = 0`, served by `w₀`'s
proposal `By` of slot `7` at cut `17` on `Bx`, with the rows `{aX}` (signed at cut `15`, time
`6`, carrying `(4, Bc)`, pooled at cut `16`). -/
theorem trV_goodWindow_Bx : GoodWindow P₁ Unit {w₀} trV 1 Bx 0 0 w₀ 17 By Bx {aX} := by
  refine ⟨⟨rfl, ⟨rfl, rfl⟩, rfl, rfl, ?_, rfl, ?_⟩, ?_, ?_, ⟨le_rfl, le_rfl⟩, by decide, ?_, ?_,
    ?_, ⟨by decide, by decide⟩⟩ <;> rw [trV_store.2.2.1]
  · exact (rfl : stXa.blocks 5 = some Bx)
  · intro r hr hv _
    change r ∈ [a₀, a₁, aK, aF, aC, aX] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact List.mem_singleton_self _
  · exact ⟨rfl, rfl⟩
  · exact Relation.ReflTransGen.refl
  · intro r hr
    rw [Finset.mem_singleton.mp hr]
    exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
  · intro r hr
    rw [Finset.mem_singleton.mp hr]
    exact Or.inr fun _ => ⟨15, ⟨Bx, rfl, rfl⟩, by decide⟩
  · intro r hr
    rw [Finset.mem_singleton.mp hr]
    exact Or.inr (by decide)

/-! ## G1.8 (b) -/

/-- Between `Bf` and `Bc` on `stCa`, every entry other than `Bf` (only `Bc`) does not have its
previous height justified: genesis and `Bs` lie below `Bf` (by slot), and the fork entry `Bk`
does not extend `Bf` (its parent is genesis). -/
theorem stCa_failed_entries (Y : NodeBlock P₁ Unit) (hY : IsEntry P₁ Unit stCa Y)
    (hfY : stCa.Anc Bf Y) (hYc : stCa.Anc Y Bc) (hne : Y ≠ Bf) :
    ¬ (stCa.σ Y.root).previousHeightJustified := by
  have hsub := trT_tree_subset w₀ 14
  rw [trT_store.1] at hsub
  have hlt (Z : NodeBlock P₁ Unit) (hZ : Z.slot < Bf.slot) : ¬ stCa.Anc Bf Z := fun h =>
    absurd (Goldilocks.Anc.slot_le (trT_coherent.mono hsub) h).1 (by omega)
  rcases mem_tree_stC hY.1 with rfl | rfl | rfl | rfl | rfl
  · exact absurd hfY (hlt _ (by decide))
  · exact absurd hfY (hlt _ (by decide))
  · exact absurd rfl hne
  · obtain h | ⟨c, hc, hcK⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hfY
    · exact absurd (congrArg Block.root h) (by decide)
    · rcases mem_tree_stC hcK.1 with rfl | rfl | rfl | rfl | rfl
      · exact absurd hc (hlt _ (by decide))
      all_goals exact absurd hcK.2.2 (by decide)
  · decide

/-- (a) Every premise of `Coverage` holds together on `trV` at `c_F = 1`, `T₁ = Bf`, `T = Bc`,
`a₀ = 0`, `k_F = 0`, `p = w₀`, `i = 14`, `B*₀ = Bx`, `Pr = Bc`, `R = {aC}`, `X = Bx`, `a₁ = 0`,
`p₁ = w₀`, `i₁ = 17`, `B*₁ = By`, `Pr₁ = Bx`, `R₁ = {aX}`: a local run; `T`'s good window;
`T`'s previous height not justified; `T₁` an entry strictly below `T`; every entry after `T₁` up
to `T` failed (previous height not justified); `X` justifies `T` after cut `14` on `B*₀`'s
chain; and the good window of the actual successor entry `X`. -/
theorem trV_coverage_premises :
    FGLocalRun () {w₀} {g₁, Bs, Bf, Bk, Bc, Bx, By} trV ∧
      GoodWindow P₁ Unit {w₀} trV 1 Bc 0 0 w₀ 14 Bx Bc {aC} ∧
      ¬ ((trV.store w₀ 14).σ Bc.root).previousHeightJustified ∧
      IsEntry P₁ Unit (trV.store w₀ 14) Bf ∧ (trV.store w₀ 14).Anc Bf Bc ∧ Bf ≠ Bc ∧
      (∀ Y, IsEntry P₁ Unit (trV.store w₀ 14) Y → (trV.store w₀ 14).Anc Bf Y →
        (trV.store w₀ 14).Anc Y Bc → Y ≠ Bf →
        ¬ ((trV.store w₀ 14).σ Y.root).previousHeightJustified) ∧
      JustifiesEntry P₁ Unit (trV.store w₀ (14 + 1)) Bc ((trV.store w₀ 14).σ Bc.root).h Bx ∧
      (trV.store w₀ (14 + 1)).Anc Bx Bx ∧
      GoodWindow P₁ Unit {w₀} trV 1 Bx 0 0 w₀ 17 By Bx {aX} := by
  obtain ⟨-, -, -, -, -, ⟨X, hX⟩, hXB⟩ := trT_justifier_misses_entry_pair
  obtain rfl := (hXB X hX).1
  rw [trT_store.1, trT_store.2] at hX
  rw [trV_store.1, trV_store.2.1]
  exact ⟨trV_localRun, trV_goodWindow_Bc, by decide, ⟨rfl, rfl⟩,
    Relation.ReflTransGen.single ⟨rfl, rfl, rfl⟩,
    fun h => absurd (congrArg Block.root h) (by decide), stCa_failed_entries, hX,
    Relation.ReflTransGen.refl, trV_goodWindow_Bx⟩

/-- (a) G1.8 (b) applied on `trV` (`coverage` at the premises of `trV_coverage_premises`): on
the chain of `By`, after cut `17`, some `Z ⪯ By` of slot at most
`Bf.slot + (Bc.slot − Bf.slot) + D₀ + D₁ = 7` has a finalized block extending `Bf`. -/
theorem trV_coverage :
    ∃ Z ∈ (trV.store w₀ (17 + 1)).tree, (trV.store w₀ (17 + 1)).Anc Z By ∧
      Z.slot ≤ Bf.slot + (Bc.slot - Bf.slot) + (0 + 1 + 0) + (0 + 1 + 0) ∧
      ∃ F ∈ (trV.store w₀ (17 + 1)).tree, F.root = ((trV.store w₀ (17 + 1)).σ Z.root).F ∧
        (trV.store w₀ (17 + 1)).Anc Bf F := by
  obtain ⟨hr, hw, hnb, hT₁, hT₁T, hne, hfail, hJ, hXB, hw₁⟩ := trV_coverage_premises
  exact coverage P₁ Unit () {w₀} _ trV hr 1 Bf Bc 0 0 w₀ 14 Bx Bc {aC} hw hnb hT₁ hT₁T hne hfail
    Bx hJ hXB 0 w₀ 17 By Bx {aX} hw₁

/-- (a) The conclusion of `trV_coverage`, concretely and tight: after cut `17`, `By` (slot
`7`) finalizes `Bc` (`σ[By].F = Bc.root`, `h_F = 4`), which extends `Bf`; the slot bound
`2 + 3 + 1 + 1 = 7` equals `By.slot`; and `By` is the only witness: every other block of the chain
of `By` has `F` at genesis, which does not extend `Bf`. -/
theorem trV_coverage_witness :
    By ∈ (trV.store w₀ (17 + 1)).tree ∧ (trV.store w₀ (17 + 1)).Anc By By ∧
      ((trV.store w₀ (17 + 1)).σ By.root).F = Bc.root ∧
      ((trV.store w₀ (17 + 1)).σ By.root).hF = 4 ∧
      Bc ∈ (trV.store w₀ (17 + 1)).tree ∧ (trV.store w₀ (17 + 1)).Anc Bf Bc ∧
      By.slot = 7 ∧ Bf.slot + (Bc.slot - Bf.slot) + (0 + 1 + 0) + (0 + 1 + 0) = By.slot ∧
      ∀ Z ∈ (trV.store w₀ (17 + 1)).tree, (trV.store w₀ (17 + 1)).Anc Z By →
        (∃ F ∈ (trV.store w₀ (17 + 1)).tree, F.root = ((trV.store w₀ (17 + 1)).σ Z.root).F ∧
          (trV.store w₀ (17 + 1)).Anc Bf F) → Z = By := by
  have hsub := trV_tree_subset w₀ (17 + 1)
  rw [trV_store.2.2.2] at hsub ⊢
  refine ⟨rfl, Relation.ReflTransGen.refl, rfl, rfl, rfl,
    Relation.ReflTransGen.single ⟨rfl, rfl, rfl⟩, rfl, rfl, fun Z hZ _ ⟨F, hF, hFZ, hBfF⟩ => ?_⟩
  have hF0 (h : F.root = 0) : False := by
    rcases mem_tree_stY hF with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (Goldilocks.Anc.slot_le (trV_coherent.mono hsub) hBfF).1 (by decide)
    all_goals exact absurd h (by decide)
  rcases mem_tree_stY hZ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | exact (hF0 hFZ).elim

end Consensus.Goldilocks.Store.Test

end
