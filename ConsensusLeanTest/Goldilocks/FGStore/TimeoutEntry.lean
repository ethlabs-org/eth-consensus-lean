module
public import ConsensusLeanTest.Goldilocks.FGStore.Entry
@[expose] public section

/-! # Control for G1.6 at a timeout-reached entry (FGStore)

G1.7 (`previousHeightNotJustified_entry`) applied at an entry whose previous height is not
justified, reached by a timeout with `h_j > 0`, where G1.6's finalization equations fail at the
justifying block: `σ[X].F ≠ σ[T].J` and `σ[X].h_F ≠ σ[T].h_j`. Labelled by kind (CONTRIBUTING
"Statements"): (a) `trT_localRun`, `trT_goodWindow`, `trT_previousHeightNotJustifiedEntry`;
(control) `trT_justifier_misses_entry_pair`, with `trT_entry_reached_by_timeout` and
`trT_record_forbids_entry_pair`.

**The obstacle.** At an entry `T` whose previous height is not justified (after a timeout), the
pair `(σ[T].h_j, σ[T].J)` is the newest pending pair (the last appended pair; a timeout keeps
the pending pairs), and an honest row for `T` carries the newest pending pair that its record
permits. So when every row of the justifying quorum comes from a record that permits
`(h_j, J)`, the justifying block `X` also finalizes `(h_j, J)`, and G1.6's equations
`σ[X].F = σ[T].J`, `σ[X].h_F = σ[T].h_j` hold at such entries too. A failing control needs a
quorum row without that pair. Here, with one honest validator (`n = 1`, no faulty rows), the
record of `w₀` does not permit `(2, Bs)`, because after its target vote for
`Bs` at height `2` it signs a timeout at height `2` naming the fork entry `Bk`
(`heightPair` gives a timeout since `target[2] = Bs ≠ Bk`; the `sent` check blocks only the same
root), so `timeout[2] = {Bk} ⊄ {Bs}`. Then its target row for `Bf` (height `3`, previous height
justified) carries no finality pair, so `Bc` does not finalize `(2, Bs)` and cannot justify `Bf`
(`h_F = 1 ≠ 2 = h_j`): it times out into the entry `Bc` (height `4`, `h_j = 2`). The row for
`Bc` again carries no finality pair, so the justifier `Bx` finalizes nothing: `σ[Bx].F` is
genesis with `h_F = 1`, against `σ[Bc].J = Bs`, `σ[Bc].h_j = 2`. (The other route, a faulty
row in an `n = 4` quorum that omits the pair, is not needed.)

**The trace `trT`** (`P₁`: `Δ = 1`, `δ_t = 2`, `q = 1`; one node `w₀`, honest). Cuts `0`–`5`
are those of `trJ`. Then (cut, time: label, effect):
* `6`, `3`: accept the own proposal `Bk` (root `3`, slot `3`, on genesis, payload `[a₀]`):
  the fork entry of height `2` (`σ[Bk]` justifies genesis like `σ[Bs]`);
* `7`, `3`: attest with source `Bk`, sign `aK = (2, Bk, timeout, (1, genesis))`;
* `8`, `3`: process `aK`;
* `9`, `4`: attest with source `Bf`, sign `aF = (3, Bf, target, none)` (`(2, Bs)` not
  permitted);
* `10`, `4`: process `aF`;
* `11`, `5`: accept the own proposal `Bc` (root `4`, slot `5`, on `Bf`, payload `[aF]`): a
  progress and target quorum for `Bf`, no finalization, so no justification; `5 ≥ 2 + δ_t`, so
  a timeout into height `4` with entry `Bc`, `(h_j, J) = (2, Bs)`, pending `[(2, Bs)]`;
* `12`, `5`: attest with source `Bc`, sign `aC = (4, Bc, target, none)`;
* `13`, `5`: process `aC`;
* `14`, `6`: accept the own proposal `Bx` (root `5`, slot `6`, on `Bc`, payload `[aC]`): it
  justifies `Bc` (`J = Bc`, `h_j = 4`) and enters height `5`; `F` stays genesis, `h_F = 1`.

The good window of `Bc` is `a = 0`, `c_F = 1`, `k_F = 0`, served by `Bx` at cut `14` with the rows
`{aC}`. -/

namespace Consensus.Goldilocks.Store.Test

/-! ## Blocks, chain states and FG states -/

/-- The fork block: `w₀`'s proposal of slot `3` on genesis carrying `a₀`: root `3`. -/
def Bk : NodeBlock P₁ Unit := ⟨3, some 0, 3, w₀, 0, [a₀], ()⟩

/-- The chain state of `Bk`: as `σBs`, at slot `3`: it justifies genesis (`J = 0`, `h_j = 1`,
pending `[(1, 0)]`) and enters height `2` with entry `Bk`. -/
def σBk : FG.ChainState P₁.n where
  L := 3
  s := 3
  h := 2
  Th := 3
  ThSlot := 3
  target := ∅
  prog := ∅
  pending := [(1, 0)]
  fin := Function.update (fun _ => ∅) 1 ∅
  J := 0
  hj := 1
  F := 0
  hF := 0

/-- `state_transition` of `Bk` from the genesis state gives `σBk`. -/
theorem stateTransition_Bk : P₁.fg.stateTransition (stBf.σ 0) Bk.fgView = some σBk := rfl

/-- The FG state after accepting `Bk` on `stBf`: `Bk` and `σBk` added; the finality update
changes nothing (`(1, genesis)` is lex-below the cache `(2, Bs)`). -/
def stK : Store P₁ Unit :=
  { stBf with
    blocks := Function.update stBf.blocks 3 (some Bk)
    σ := Function.update stBf.σ 3 σBk }

/-- `stK` holds genesis, `Bs`, `Bf` and `Bk`. -/
theorem mem_tree_stK {X : NodeBlock P₁ Unit} (h : X ∈ stK.tree) :
    X = g₁ ∨ X = Bs ∨ X = Bf ∨ X = Bk := by
  change Function.update stBf.blocks 3 (some Bk) X.root = some X at h
  rcases eq_or_of_update h with h | h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact (mem_tree_stBf h).imp_right (Or.imp_right Or.inl)

open Classical in
/-- The finality update of `Bk` on `stK` changes nothing. -/
theorem updateFinality_stK : stK.updateFinality σBk = stK := by
  unfold updateFinality
  extract_lets st₁ st₂
  have h2 : st₂ = stK := by
    change (match st₁.blocks 0 with
      | some X => if st₁.Anc st₁.F X ∧ LexLt (st₁.hj, st₁.J.root) (1, 0) then
          { st₁ with J := X, hj := 1 } else st₁
      | none => st₁) = stK
    rw [show st₁.blocks 0 = some g₁ from rfl]
    dsimp only
    rw [ite_eq_right fun h => by
      have h' : LexLt (2, 1) (1, 0) := h.2
      simp [LexLt] at h']
    rfl
  rw [h2, show stK.blocks σBk.F = some g₁ from rfl]
  dsimp only
  rw [ite_eq_right (fun h => h.2.1 rfl)]

/-- `stBf` accepts `Bk`, with post-state `stK` (`a₀` is pooled already). -/
theorem onBlock_stBf_Bk : stBf.onBlock Bk = some stK := by
  have hanc : Goldilocks.Anc (insert Bk stBf.tree) stBf.F Bk :=
    Relation.ReflTransGen.single ⟨Or.inr rfl, Or.inl rfl, rfl⟩
  have hneg : ¬ ((stBf.blocks Bk.root).isSome = true ∨ (stBf.blocks 0).isNone = true ∨
      ¬ Goldilocks.Anc (insert Bk stBf.tree) stBf.F Bk) := by
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
  · next h => rw [stateTransition_Bk] at h; cases h
  next σ' h =>
  rw [stateTransition_Bk] at h; cases h
  change some ((updateFinality stK σBk).addAtts [a₀]) = some stK
  rw [updateFinality_stK]
  rfl

/-- `w₀`'s timeout at height `2` naming the fork entry `Bk`, with `σ[Bk]`'s predecessor
`(1, genesis)` as its finality pair. -/
def aK : FG.Att P₁.n := ⟨w₀, 2, 3, true, some (1, 0)⟩

/-- `w₀`'s record after signing `aK`: `timeout[2] = {Bk}`. -/
def ΛK : FG.Record := Λ₁.recordAtt aK

/-- On `stK` and `Λ₁`, `fg_attest` with source `Bk` signs the timeout `aK`: `target[2] = Bs`
names another block, and `a₁` (a target vote for `Bs`) does not block a timeout for `Bk`. -/
theorem attest_stK : stK.attest Λ₁ w₀ Bk = some (aK, ΛK) := rfl

/-- `stK` with `aK` pooled. -/
def stKa : Store P₁ Unit := { stK with atts := [a₀, a₁, aK] }

/-- `w₀`'s target vote for `Bf` at height `3`, without a finality pair: `ΛK` does not permit
`σ[Bf]`'s predecessor `(2, Bs)`. -/
def aF : FG.Att P₁.n := ⟨w₀, 3, 2, false, none⟩

/-- `w₀`'s record after signing `aF`. -/
def ΛF : FG.Record := ΛK.recordAtt aF

/-- On `stKa` and `ΛK`, `fg_attest` with source `Bf` signs `aF`. -/
theorem attest_stKa : stKa.attest ΛK w₀ Bf = some (aF, ΛF) := rfl

/-- `stK` with `aK` and `aF` pooled. -/
def stKb : Store P₁ Unit := { stK with atts := [a₀, a₁, aK, aF] }

/-- `w₀`'s proposal of slot `5` on `Bf` carrying `aF`: root `4`. -/
def Bc : NodeBlock P₁ Unit := ⟨4, some 2, 5, w₀, 0, [aF], ()⟩

/-- The chain state of `Bc`: `aF` is a target and progress quorum for `Bf`, but `(2, Bs)` has no
finality bit, so `h_F = 1 ≠ 2 = h_j` blocks the justification; the entry `Bf` has slot `2`
and `5 ≥ 2 + δ_t`, so `Bc` times out into height `4` with entry `Bc`, keeping `(h_j, J) =
(2, Bs)`, `(h_F, F) = (1, genesis)` and pending `[(2, 1)]`. -/
def σBc : FG.ChainState P₁.n where
  L := 4
  s := 5
  h := 4
  Th := 4
  ThSlot := 5
  target := ∅
  prog := ∅
  pending := [(2, 1)]
  fin := σBf.fin
  J := 1
  hj := 2
  F := 0
  hF := 1

/-- `state_transition` of `Bc` from `σBf` gives `σBc`. -/
theorem stateTransition_Bc : P₁.fg.stateTransition (stKb.σ 2) Bc.fgView = some σBc := rfl

/-- `stKb` with `Bc` and its chain state added (before the finality update). -/
def stC₀ : Store P₁ Unit :=
  { stKb with
    blocks := Function.update stKb.blocks 4 (some Bc)
    σ := Function.update stKb.σ 4 σBc }

/-- The FG state after accepting `Bc` on `stKb`: `Bc` and `σBc` added, `h_max = 4`. -/
def stC : Store P₁ Unit := { stC₀ with hmax := 4 }

/-- `stC` holds genesis, `Bs`, `Bf`, `Bk` and `Bc`. -/
theorem mem_tree_stC {X : NodeBlock P₁ Unit} (h : X ∈ stC.tree) :
    X = g₁ ∨ X = Bs ∨ X = Bf ∨ X = Bk ∨ X = Bc := by
  change Function.update stK.blocks 4 (some Bc) X.root = some X at h
  rcases eq_or_of_update h with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact (mem_tree_stK h).imp_right (Or.imp_right (Or.imp_right Or.inl))

/-- `Bc` descends from genesis through `Bs` and `Bf` in any set holding the four. -/
theorem anc_g₁_Bc {S : Set (NodeBlock P₁ Unit)} (h0 : g₁ ∈ S) (h1 : Bs ∈ S) (h2 : Bf ∈ S)
    (h4 : Bc ∈ S) : Goldilocks.Anc S g₁ Bc :=
  ((Relation.ReflTransGen.single ⟨h0, h1, rfl⟩).tail ⟨h1, h2, rfl⟩).tail ⟨h2, h4, rfl⟩

open Classical in
/-- The finality update of `Bc` on `stC₀` gives `stC`: `(2, Bs)` is the cache already, and
`σBc.F` is genesis. -/
theorem updateFinality_stC₀ : stC₀.updateFinality σBc = stC := by
  unfold updateFinality
  extract_lets st₁ st₂
  have h2 : st₂ = stC := by
    change (match st₁.blocks 1 with
      | some X => if st₁.Anc st₁.F X ∧ LexLt (st₁.hj, st₁.J.root) (2, 1) then
          { st₁ with J := X, hj := 2 } else st₁
      | none => st₁) = stC
    rw [show st₁.blocks 1 = some Bs from rfl]
    dsimp only
    rw [ite_eq_right fun h => by
      have h' : LexLt (2, 1) (2, 1) := h.2
      simp [LexLt] at h']
    rfl
  rw [h2, show stC.blocks σBc.F = some g₁ from rfl]
  dsimp only
  rw [ite_eq_right (fun h => h.2.1 rfl)]

/-- `stKb` accepts `Bc`, with post-state `stC` (`aF` is pooled already). -/
theorem onBlock_stKb_Bc : stKb.onBlock Bc = some stC := by
  have hanc : Goldilocks.Anc (insert Bc stKb.tree) stKb.F Bc :=
    anc_g₁_Bc (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)
  have hneg : ¬ ((stKb.blocks Bc.root).isSome = true ∨ (stKb.blocks 2).isNone = true ∨
      ¬ Goldilocks.Anc (insert Bc stKb.tree) stKb.F Bc) := by
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
  · next h => rw [stateTransition_Bc] at h; cases h
  next σ' h =>
  rw [stateTransition_Bc] at h; cases h
  change some ((updateFinality stC₀ σBc).addAtts [aF]) = some stC
  rw [updateFinality_stC₀]
  rfl

/-- `w₀`'s target vote for `Bc` at height `4`, without a finality pair: the only pending pair of
`σ[Bc]` is `(2, Bs)`, which `ΛF` does not permit. -/
def aC : FG.Att P₁.n := ⟨w₀, 4, 4, false, none⟩

/-- `w₀`'s record after signing `aC`. -/
def ΛC : FG.Record := ΛF.recordAtt aC

/-- On `stC` and `ΛF`, `fg_attest` with source `Bc` signs `aC`. -/
theorem attest_stC : stC.attest ΛF w₀ Bc = some (aC, ΛC) := rfl

/-- `stC` with `aC` pooled. -/
def stCa : Store P₁ Unit := { stC with atts := [a₀, a₁, aK, aF, aC] }

/-- `w₀`'s proposal of slot `6` on `Bc` carrying `aC`: root `5`. -/
def Bx : NodeBlock P₁ Unit := ⟨5, some 4, 6, w₀, 0, [aC], ()⟩

/-- The chain state of `Bx`: `aC` is a target quorum for `Bc`, whose previous height is not
justified, so `Bx` justifies `Bc` (`J = 4`, `h_j = 4`, pending `[(2, 1), (4, 4)]`) and enters
height `5` with entry `Bx`; nothing is finalized (`F = 0`, `h_F = 1`). -/
def σBx : FG.ChainState P₁.n where
  L := 5
  s := 6
  h := 5
  Th := 5
  ThSlot := 6
  target := ∅
  prog := ∅
  pending := [(2, 1), (4, 4)]
  fin := Function.update σBf.fin 4 ∅
  J := 4
  hj := 4
  F := 0
  hF := 1

/-- `state_transition` of `Bx` from `σBc` gives `σBx`. -/
theorem stateTransition_Bx : P₁.fg.stateTransition (stCa.σ 4) Bx.fgView = some σBx := rfl

/-- `stCa` with `Bx` and its chain state added (before the finality update). -/
def stX₀ : Store P₁ Unit :=
  { stCa with
    blocks := Function.update stCa.blocks 5 (some Bx)
    σ := Function.update stCa.σ 5 σBx }

/-- The FG state after accepting `Bx` on `stCa`: `Bx` and `σBx` added, `h_max = 5`, and the
justification cache at `Bc` with height `4`; `F` stays at genesis. -/
def stX : Store P₁ Unit := { stX₀ with J := Bc, hj := 4, hmax := 5 }

/-- `stX` holds genesis, `Bs`, `Bf`, `Bk`, `Bc` and `Bx`. -/
theorem mem_tree_stX {X : NodeBlock P₁ Unit} (h : X ∈ stX.tree) :
    X = g₁ ∨ X = Bs ∨ X = Bf ∨ X = Bk ∨ X = Bc ∨ X = Bx := by
  change Function.update stC.blocks 5 (some Bx) X.root = some X at h
  rcases eq_or_of_update h with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · exact (mem_tree_stC h).imp_right (Or.imp_right (Or.imp_right (Or.imp_right Or.inl)))

open Classical in
/-- The finality update of `Bx` on `stX₀` gives `stX`. -/
theorem updateFinality_stX₀ : stX₀.updateFinality σBx = stX := by
  unfold updateFinality
  extract_lets st₁ st₂
  have h2 : st₂ = stX := by
    change (match st₁.blocks 4 with
      | some X => if st₁.Anc st₁.F X ∧ LexLt (st₁.hj, st₁.J.root) (4, 4) then
          { st₁ with J := X, hj := 4 } else st₁
      | none => st₁) = stX
    rw [show st₁.blocks 4 = some Bc from rfl]
    dsimp only
    rw [ite_eq_left ⟨anc_g₁_Bc rfl rfl rfl rfl, Or.inl (by decide)⟩]
    rfl
  rw [h2, show stX.blocks σBx.F = some g₁ from rfl]
  dsimp only
  rw [ite_eq_right (fun h => h.2.1 rfl)]

/-- `stCa` accepts `Bx`, with post-state `stX` (`aC` is pooled already). -/
theorem onBlock_stCa_Bx : stCa.onBlock Bx = some stX := by
  have hanc : Goldilocks.Anc (insert Bx stCa.tree) stCa.F Bx :=
    (anc_g₁_Bc (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)).tail
      ⟨Or.inr rfl, Or.inl rfl, rfl⟩
  have hneg : ¬ ((stCa.blocks Bx.root).isSome = true ∨ (stCa.blocks 4).isNone = true ∨
      ¬ Goldilocks.Anc (insert Bx stCa.tree) stCa.F Bx) := by
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
  · next h => rw [stateTransition_Bx] at h; cases h
  next σ' h =>
  rw [stateTransition_Bx] at h; cases h
  change some ((updateFinality stX₀ σBx).addAtts [aC]) = some stX
  rw [updateFinality_stX₀]
  rfl

/-! ## The trace `trT` -/

/-- The timeout-entry trace: `trJ`'s cuts `0`–`5`, then the fork `Bk` and the timeout `aK` at
time `3`, the target vote `aF` for `Bf` at time `4`, the timeout block `Bc` and the target vote
`aC` for it at time `5`, and the justifier `Bx` at time `6`; then it stutters. -/
def trT : FGTrace P₁ Unit where
  init _ := (Store.init (), FG.Record.empty)
  node _ := w₀
  time i := if i < 2 then 0 else if i < 5 then 1 else if i < 6 then 2 else if i < 9 then 3
    else if i < 11 then 4 else if i < 14 then 5 else 6
  event i := if i < 2 then 0 else if i < 5 then 1 else if i < 6 then 2 else if i < 9 then 3
    else if i < 11 then 4 else if i < 14 then 5 else 6
  pos
    | 1 => 1
    | 3 => 1
    | 4 => 2
    | 7 => 1
    | 8 => 2
    | 10 => 1
    | 12 => 1
    | 13 => 2
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
    | _ => (stX, ΛC)
  awake _ _ := True

/-- The labelled cuts of `trT`. -/
theorem trT_label (i : Nat) (ℓ : FGLabel P₁ Unit) (h : trT.label i = some ℓ) :
    (i = 0 ∧ ℓ = .attest g₁ (some a₀)) ∨ (i = 1 ∧ ℓ = .attestation a₀) ∨
      (i = 2 ∧ ℓ = .block Bs true) ∨ (i = 3 ∧ ℓ = .attest Bs (some a₁)) ∨
      (i = 4 ∧ ℓ = .attestation a₁) ∨ (i = 5 ∧ ℓ = .block Bf true) ∨
      (i = 6 ∧ ℓ = .block Bk true) ∨ (i = 7 ∧ ℓ = .attest Bk (some aK)) ∨
      (i = 8 ∧ ℓ = .attestation aK) ∨ (i = 9 ∧ ℓ = .attest Bf (some aF)) ∨
      (i = 10 ∧ ℓ = .attestation aF) ∨ (i = 11 ∧ ℓ = .block Bc true) ∨
      (i = 12 ∧ ℓ = .attest Bc (some aC)) ∨ (i = 13 ∧ ℓ = .attestation aC) ∨
      (i = 14 ∧ ℓ = .block Bx true) := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    dsimp only [trT] at h <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> simp [h]

/-- After a labelled cut `i ≤ 14` of `trT`, the state of `w₀` is the cut's post-state. -/
theorem trT_state_succ (i : Nat) (hi : i ≤ 14) : trT.state w₀ (i + 1) = trT.post i := by
  have h : trT.node i = w₀ ∧ trT.label i ≠ none := by
    refine ⟨rfl, ?_⟩
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
      first | (dsimp only [trT]; exact Option.some_ne_none _) | omega
  rw [Trace.state, ite_eq_left h]

/-- The states of `w₀` before each cut of `trT`. -/
theorem trT_state :
    trT.state w₀ 0 = (Store.init (), FG.Record.empty) ∧ trT.state w₀ 1 = (Store.init (), Λ₀) ∧
      trT.state w₀ 2 = (stA, Λ₀) ∧ trT.state w₀ 3 = (stBs, Λ₀) ∧
      trT.state w₀ 4 = (stBs, Λ₁) ∧ trT.state w₀ 5 = (stBa, Λ₁) ∧
      trT.state w₀ 6 = (stBf, Λ₁) ∧ trT.state w₀ 7 = (stK, Λ₁) ∧
      trT.state w₀ 8 = (stK, ΛK) ∧ trT.state w₀ 9 = (stKa, ΛK) ∧
      trT.state w₀ 10 = (stKa, ΛF) ∧ trT.state w₀ 11 = (stKb, ΛF) ∧
      trT.state w₀ 12 = (stC, ΛF) ∧ trT.state w₀ 13 = (stC, ΛC) ∧
      trT.state w₀ 14 = (stCa, ΛC) ∧ ∀ i, trT.state w₀ (i + 15) = (stX, ΛC) := by
  refine ⟨rfl, trT_state_succ 0 (by omega), trT_state_succ 1 (by omega),
    trT_state_succ 2 (by omega), trT_state_succ 3 (by omega), trT_state_succ 4 (by omega),
    trT_state_succ 5 (by omega), trT_state_succ 6 (by omega), trT_state_succ 7 (by omega),
    trT_state_succ 8 (by omega), trT_state_succ 9 (by omega), trT_state_succ 10 (by omega),
    trT_state_succ 11 (by omega), trT_state_succ 12 (by omega), trT_state_succ 13 (by omega),
    fun i => ?_⟩
  induction i with
  | zero => exact trT_state_succ 14 le_rfl
  | succ i ih => rw [Trace.state, ite_eq_right (by simp [trT])]; exact ih

/-- The FG state of `w₀` before cuts `14` and `15` of `trT`. -/
theorem trT_store : trT.store w₀ 14 = stCa ∧ trT.store w₀ (14 + 1) = stX :=
  ⟨congrArg Prod.fst trT_state.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    congrArg Prod.fst (trT_state.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 0)⟩

/-- `U` of `trT` (genesis, `Bs`, `Bf`, `Bk`, `Bc`, `Bx`) is coherent. -/
theorem trT_coherent : Coherent ({g₁, Bs, Bf, Bk, Bc, Bx} : Set (NodeBlock P₁ Unit)) := by
  refine ⟨?_, ?_⟩
  · rintro X (rfl | rfl | rfl | rfl | rfl | rfl) Y (rfl | rfl | rfl | rfl | rfl | rfl) h <;>
      first | rfl | exact absurd h (by decide)
  · rintro X (rfl | rfl | rfl | rfl | rfl | rfl) Y (rfl | rfl | rfl | rfl | rfl | rfl) h <;>
      first | decide | exact absurd h (by decide)

/-- Each call of `trT` executes the FG on its pre-state. -/
theorem trT_exec (i : Nat) (ℓ : FGLabel P₁ Unit) (h : trT.label i = some ℓ) :
    FGLabel.Step (trT.node i) (trT.state (trT.node i) i) ℓ (trT.post i) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -⟩ := trT_state
  rcases trT_label i ℓ h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · change FGLabel.Step w₀ (trT.state w₀ 0) _ (Store.init (), Λ₀)
    rw [h0]
    exact ⟨rfl, by rw [attest_init]; exact ⟨rfl, rfl⟩⟩
  · change FGLabel.Step w₀ (trT.state w₀ 1) _ (stA, Λ₀)
    rw [h1]
    rfl
  · change FGLabel.Step w₀ (trT.state w₀ 2) _ (stBs, Λ₀)
    rw [h2]
    exact Or.inl ⟨rfl, onBlock_stA_Bs, rfl⟩
  · change FGLabel.Step w₀ (trT.state w₀ 3) _ (stBs, Λ₁)
    rw [h3]
    exact ⟨rfl, by rw [attest_stBs]; exact ⟨rfl, rfl⟩⟩
  · change FGLabel.Step w₀ (trT.state w₀ 4) _ (stBa, Λ₁)
    rw [h4]
    rfl
  · change FGLabel.Step w₀ (trT.state w₀ 5) _ (stBf, Λ₁)
    rw [h5]
    exact Or.inl ⟨rfl, onBlock_stBa_Bf, rfl⟩
  · change FGLabel.Step w₀ (trT.state w₀ 6) _ (stK, Λ₁)
    rw [h6]
    exact Or.inl ⟨rfl, onBlock_stBf_Bk, rfl⟩
  · change FGLabel.Step w₀ (trT.state w₀ 7) _ (stK, ΛK)
    rw [h7]
    exact ⟨rfl, by rw [attest_stK]; exact ⟨rfl, rfl⟩⟩
  · change FGLabel.Step w₀ (trT.state w₀ 8) _ (stKa, ΛK)
    rw [h8]
    rfl
  · change FGLabel.Step w₀ (trT.state w₀ 9) _ (stKa, ΛF)
    rw [h9]
    exact ⟨rfl, by rw [attest_stKa]; exact ⟨rfl, rfl⟩⟩
  · change FGLabel.Step w₀ (trT.state w₀ 10) _ (stKb, ΛF)
    rw [h10]
    rfl
  · change FGLabel.Step w₀ (trT.state w₀ 11) _ (stC, ΛF)
    rw [h11]
    exact Or.inl ⟨rfl, onBlock_stKb_Bc, rfl⟩
  · change FGLabel.Step w₀ (trT.state w₀ 12) _ (stC, ΛC)
    rw [h12]
    exact ⟨rfl, by rw [attest_stC]; exact ⟨rfl, rfl⟩⟩
  · change FGLabel.Step w₀ (trT.state w₀ 13) _ (stCa, ΛC)
    rw [h13]
    rfl
  · change FGLabel.Step w₀ (trT.state w₀ 14) _ (stX, ΛC)
    rw [h14]
    exact Or.inl ⟨rfl, onBlock_stCa_Bx, rfl⟩

/-- Every block that `w₀` holds in `trT` lies in `{genesis, Bs, Bf, Bk, Bc, Bx}`. -/
theorem trT_tree_subset (y : Fin P₁.n) (i : Nat) :
    (trT.store y i).tree ⊆ ({g₁, Bs, Bf, Bk, Bc, Bx} : Set (NodeBlock P₁ Unit)) := by
  intro X hX
  obtain rfl := eq_w₀ y
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := trT_state
  have hK (h : X ∈ stK.tree) : X ∈ ({g₁, Bs, Bf, Bk, Bc, Bx} : Set (NodeBlock P₁ Unit)) :=
    (mem_tree_stK h).imp_right (Or.imp_right (Or.imp_right Or.inl))
  have hC (h : X ∈ stC.tree) : X ∈ ({g₁, Bs, Bf, Bk, Bc, Bx} : Set (NodeBlock P₁ Unit)) :=
    (mem_tree_stC h).imp_right (Or.imp_right (Or.imp_right (Or.imp_right Or.inl)))
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  · rw [FGTrace.store, h0] at hX; exact Or.inl (eq_g₁_of_init hX)
  · rw [FGTrace.store, h1] at hX; exact Or.inl (eq_g₁_of_init hX)
  · rw [FGTrace.store, h2] at hX; exact Or.inl (eq_g₁_of_init hX)
  · rw [FGTrace.store, h3] at hX; exact (mem_tree_stBs hX).imp_right Or.inl
  · rw [FGTrace.store, h4] at hX; exact (mem_tree_stBs hX).imp_right Or.inl
  · rw [FGTrace.store, h5] at hX; exact (mem_tree_stBs hX).imp_right Or.inl
  · rw [FGTrace.store, h6] at hX
    exact (mem_tree_stBf hX).imp_right (Or.imp_right Or.inl)
  · rw [FGTrace.store, h7] at hX; exact hK hX
  · rw [FGTrace.store, h8] at hX; exact hK hX
  · rw [FGTrace.store, h9] at hX; exact hK hX
  · rw [FGTrace.store, h10] at hX; exact hK hX
  · rw [FGTrace.store, h11] at hX; exact hK hX
  · rw [FGTrace.store, h12] at hX; exact hC hX
  · rw [FGTrace.store, h13] at hX; exact hC hX
  · rw [FGTrace.store, h14] at hX; exact hC hX
  · rw [FGTrace.store, h15] at hX; exact mem_tree_stX hX

/-- From cut `14` on, the time of `trT` is `6`. -/
private theorem trT_time_tail (i : Nat) : trT.time (i + 14) = 6 := by
  simp only [trT]; split_ifs <;> first | rfl | omega

/-- The times of `trT` do not decrease from one cut to the next. -/
private theorem trT_time_succ : ∀ i, trT.time i ≤ trT.time (i + 1)
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 => by decide
  | i + 14 => by rw [trT_time_tail, Nat.add_right_comm, trT_time_tail]

private theorem trT_time_mono {i j : Nat} (h : i ≤ j) : trT.time i ≤ trT.time j :=
  monotone_nat_of_le_succ trT_time_succ h

/-- The tick order of `trT`, (a): each own proposal is accepted at the first cut of its time. -/
theorem trT_own_first (y : Fin P₁.n) (i : Nat) (B : NodeBlock P₁ Unit)
    (h : trT.CallAt y i (.block B true)) (k : Nat) (hk : k < i) : trT.time k < trT.time i := by
  rcases trT_label i _ h.2 with ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ |
    ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ |
    ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ <;>
    first | (cases h'; done) |
      exact lt_of_le_of_lt (trT_time_mono (Nat.le_pred_of_lt hk)) (by decide)

/-- The tick order of `trT`, (b): before an `attest` call at its time, only the own proposal. -/
theorem trT_attest_order (y : Fin P₁.n) (j : Nat) (src : NodeBlock P₁ Unit)
    (signed : Option (FG.Att P₁.n)) (h : trT.CallAt y j (.attest src signed)) (i : Nat)
    (ℓ : FGLabel P₁ Unit) (hij : i < j) (hi : trT.CallAt y i ℓ) (ht : trT.time i = trT.time j) :
    ∃ B acc, ℓ = .block B acc ∧ B.proposer = y ∧ P₁.slotTime B.slot = trT.time j := by
  obtain rfl := eq_w₀ y
  rcases trT_label j _ h.2 with ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ |
    ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ |
    ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ <;>
    try (cases h'; done)
  all_goals
    rcases trT_label i ℓ hi.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first | omega | exact absurd ht (by decide) | exact ⟨_, true, rfl, rfl, rfl⟩

/-- The own proposals of `trT` carry pooled attestations. -/
theorem trT_own_payload (y : Fin P₁.n) (i : Nat) (X : NodeBlock P₁ Unit)
    (h : trT.CallAt y i (.block X true)) (a : FG.Att P₁.n) (ha : a ∈ X.fgPayload) :
    a ∈ (trT.store y i).atts := by
  obtain rfl := eq_w₀ y
  obtain ⟨-, -, h2, -, -, h5, h6, -, -, -, -, h11, -, -, h14, -⟩ := trT_state
  rcases trT_label i _ h.2 with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨rfl, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ |
    ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨rfl, h'⟩ | ⟨-, h'⟩ |
    ⟨-, h'⟩ | ⟨rfl, h'⟩ <;>
    cases h' <;> rw [List.mem_singleton.mp ha, FGTrace.store]
  · rw [h2]; decide
  · rw [h5]; decide
  · rw [h6]; decide
  · rw [h11]; decide
  · rw [h14]; decide

/-- Every attestation processed in `trT` was signed at an earlier cut. -/
theorem trT_unforgeable (y : Fin P₁.n) (i : Nat) (a : FG.Att P₁.n) (h : trT.ProcessAt y i a) :
    ∃ j < i, trT.SignAt a.val j a := by
  obtain ⟨ℓ, hℓ, ha⟩ := h
  rcases trT_label i ℓ hℓ.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases ha
  · rw [List.mem_singleton.mp ha]; exact ⟨0, by omega, g₁, rfl, rfl⟩
  · rw [List.mem_singleton.mp ha]; exact ⟨0, by omega, g₁, rfl, rfl⟩
  · cases ha
  · rw [List.mem_singleton.mp ha]; exact ⟨3, by omega, Bs, rfl, rfl⟩
  · rw [List.mem_singleton.mp ha]; exact ⟨3, by omega, Bs, rfl, rfl⟩
  · rw [List.mem_singleton.mp ha]; exact ⟨0, by omega, g₁, rfl, rfl⟩
  · cases ha
  · rw [List.mem_singleton.mp ha]; exact ⟨7, by omega, Bk, rfl, rfl⟩
  · cases ha
  · rw [List.mem_singleton.mp ha]; exact ⟨9, by omega, Bf, rfl, rfl⟩
  · rw [List.mem_singleton.mp ha]; exact ⟨9, by omega, Bf, rfl, rfl⟩
  · cases ha
  · rw [List.mem_singleton.mp ha]; exact ⟨12, by omega, Bc, rfl, rfl⟩
  · rw [List.mem_singleton.mp ha]; exact ⟨12, by omega, Bc, rfl, rfl⟩

/-- (a) `trT` is an `FGLocalRun` for the honest set `{w₀}` inside
`{genesis, Bs, Bf, Bk, Bc, Bx}`. -/
theorem trT_localRun : FGLocalRun () {w₀} {g₁, Bs, Bf, Bk, Bc, Bx} trT where
  coherent := trT_coherent
  init _ _ := rfl
  exec i ℓ h _ := trT_exec i ℓ h
  tree_subset y _ i := trT_tree_subset y i
  time_nonneg i := le_trans (by decide) (trT_time_mono (Nat.zero_le i))
  time_mono i j hij := trT_time_mono hij
  attest_public _ _ _ _ _ _ := one_dvd _
  own_first y _ i X h _ _ k hk _ _ := trT_own_first y i X h k hk
  attest_order y _ j src signed h i ℓ hij hi ht := trT_attest_order y j src signed h i ℓ hij hi ht
  own_payload y _ i X h _ _ a ha := trT_own_payload y i X h a ha
  unforgeable y _ i a h _ := trT_unforgeable y i a h

/-! ## The timeout entry `Bc` and G1.7 -/

/-- The record of `w₀` from cut `8` on does not permit `(2, Bs)`: the timeout `aK` made
`timeout[2] = {Bk}`. So its rows `aF` (for `Bf`) and `aC` (for `Bc`) carry no finality pair. -/
theorem trT_record_forbids_entry_pair :
    (trT.state w₀ 9).2 = ΛK ∧ (trT.state w₀ 12).2 = ΛF ∧ ΛK.timeout 2 = {Bk.root} ∧
      ΛF.timeout 2 = {Bk.root} ∧ ¬ ΛK.permits 2 Bs.root ∧ ¬ ΛF.permits 2 Bs.root ∧
      aF.fin = none ∧ aC.fin = none := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h9, -, -, h12, -⟩ := trT_state
  rw [h9, h12]
  exact ⟨rfl, rfl, by decide, by decide, by decide, by decide, rfl, rfl⟩

/-- At cut `14` of `trT`, the entry `Bc` was reached by a timeout with `h_j > 0`: its parent
`Bf` is the entry of height `3` (slot `2`, previous height justified, `h_j = 2` but `h_F = 1`,
so it cannot justify), `Bc` (slot `5 ≥ 2 + δ_t`) enters height `4` keeping `(h_j, J) =
(2, Bs)`, and its previous height `3` is not justified. -/
theorem trT_entry_reached_by_timeout :
    Bc.parent = some Bf.root ∧ Bf.slot + P₁.δt ≤ Bc.slot ∧
      ((trT.store w₀ 14).σ Bf.root).h = 3 ∧ ((trT.store w₀ 14).σ Bf.root).Th = Bf.root ∧
      ((trT.store w₀ 14).σ Bf.root).previousHeightJustified ∧
      ((trT.store w₀ 14).σ Bf.root).hj = 2 ∧ ((trT.store w₀ 14).σ Bf.root).hF = 1 ∧
      ((trT.store w₀ 14).σ Bc.root).h = 4 ∧ ((trT.store w₀ 14).σ Bc.root).Th = Bc.root ∧
      ((trT.store w₀ 14).σ Bc.root).hj = 2 ∧ ((trT.store w₀ 14).σ Bc.root).J = Bs.root ∧
      0 < ((trT.store w₀ 14).σ Bc.root).hj ∧
      ¬ ((trT.store w₀ 14).σ Bc.root).previousHeightJustified := by
  rw [trT_store.1]
  exact ⟨rfl, by decide, rfl, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩

/-- (a) On `trT`, the entry `Bc` (height `4`, slot `5`, previous height not justified) has a good
window with `a = 0`, `c_F = 1`, `k_F = 0`, served by `w₀`'s proposal `Bx` of slot `6` at cut
`14` on `Bc`, with the rows `{aC}` (signed at cut `12`, time `5`, pooled at cut `13`). -/
theorem trT_goodWindow : GoodWindow P₁ Unit {w₀} trT 1 Bc 0 0 w₀ 14 Bx Bc {aC} := by
  refine ⟨⟨rfl, ⟨rfl, rfl⟩, rfl, rfl, ?_, rfl, ?_⟩, ?_, ?_, ⟨le_rfl, le_rfl⟩, by decide, ?_, ?_,
    ?_, ⟨by decide, by decide⟩⟩ <;> rw [trT_store.1]
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

/-- (a) G1.7 applied on `trT`: the timeout-reached entry `Bc` with its good window
`trT_goodWindow` gives `previousHeightNotJustified_entry`'s full conclusion. -/
theorem trT_previousHeightNotJustifiedEntry :
    ∃ X, JustifiesEntry P₁ Unit (trT.store w₀ (14 + 1)) Bc ((trT.store w₀ 14).σ Bc.root).h X ∧
      (trT.store w₀ (14 + 1)).Anc X Bx ∧
      (((trT.store w₀ 14).σ Bc.root).h, Bc.root) ∈ ((trT.store w₀ (14 + 1)).σ X.root).pending ∧
      ((trT.store w₀ (14 + 1)).σ X.root).h = ((trT.store w₀ 14).σ Bc.root).h + 1 ∧
      ((trT.store w₀ (14 + 1)).σ X.root).Th = X.root ∧
      ((trT.store w₀ (14 + 1)).σ X.root).previousHeightJustified ∧
      ∀ (a₁ : Nat) (p₁ : Fin P₁.n) (i₁ : Nat) (Bs₁ Pr₁ : NodeBlock P₁ Unit)
        (R₁ : Finset (FG.Att P₁.n)), GoodWindow P₁ Unit {w₀} trT 1 X a₁ 0 p₁ i₁ Bs₁ Pr₁ R₁ →
        ∃ Z ∈ (trT.store p₁ (i₁ + 1)).tree, (trT.store p₁ (i₁ + 1)).Anc Z Bs₁ ∧
          ((trT.store p₁ (i₁ + 1)).σ Z.root).F = Bc.root ∧
          ((trT.store p₁ (i₁ + 1)).σ Z.root).hF = ((trT.store w₀ 14).σ Bc.root).h :=
  previousHeightNotJustified_entry P₁ Unit () {w₀} {g₁, Bs, Bf, Bk, Bc, Bx} trT trT_localRun 1
    Bc 0 0 w₀ 14 Bx Bc {aC} trT_goodWindow trT_entry_reached_by_timeout.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## Control -/

/-- (control) At the timeout-reached entry `Bc` (height `4`, previous height not justified,
`(h_j, J) = (2, Bs)`, `h_F = 1`), G1.6's finalization equations fail at the justifier, both of
them: G1.7 gives a block `X` that justifies `Bc` after cut `14`, every such `X` is `Bx`, and
`σ[Bx].F = genesis ≠ Bs = σ[Bc].J`, `σ[Bx].h_F = 1 ≠ 2 = σ[Bc].h_j`; so
`¬ (σ[X].F = σ[T].J ∧ σ[X].h_F = σ[T].h_j)` with `σ[T].h_j > 0` (not the genesis `0 = 0`). The
row `aC` of `Bx` carries no finality pair, since `w₀`'s record does not permit `(2, Bs)`
(`trT_record_forbids_entry_pair`): with rows from records that permit it, `X` would finalize
`(h_j, J)` and the equations would hold. -/
theorem trT_justifier_misses_entry_pair :
    ((trT.store w₀ 14).σ Bc.root).h = 4 ∧ ((trT.store w₀ 14).σ Bc.root).hj = 2 ∧
      ((trT.store w₀ 14).σ Bc.root).J = Bs.root ∧ ((trT.store w₀ 14).σ Bc.root).hF = 1 ∧
      ¬ ((trT.store w₀ 14).σ Bc.root).previousHeightJustified ∧
      (∃ X, JustifiesEntry P₁ Unit (trT.store w₀ (14 + 1)) Bc ((trT.store w₀ 14).σ Bc.root).h X) ∧
      ∀ X, JustifiesEntry P₁ Unit (trT.store w₀ (14 + 1)) Bc ((trT.store w₀ 14).σ Bc.root).h X →
        X = Bx ∧ ((trT.store w₀ (14 + 1)).σ X.root).F = g₁.root ∧
        ((trT.store w₀ (14 + 1)).σ X.root).hF = 1 ∧
        ((trT.store w₀ (14 + 1)).σ X.root).F ≠ ((trT.store w₀ 14).σ Bc.root).J ∧
        ((trT.store w₀ (14 + 1)).σ X.root).hF ≠ ((trT.store w₀ 14).σ Bc.root).hj ∧
        ¬ (((trT.store w₀ (14 + 1)).σ X.root).F = ((trT.store w₀ 14).σ Bc.root).J ∧
          ((trT.store w₀ (14 + 1)).σ X.root).hF = ((trT.store w₀ 14).σ Bc.root).hj) := by
  obtain ⟨X₀, hX₀, -⟩ := trT_previousHeightNotJustifiedEntry
  rw [trT_store.1, trT_store.2] at hX₀ ⊢
  refine ⟨rfl, rfl, rfl, rfl, by decide, ⟨X₀, hX₀⟩, fun X hX => ?_⟩
  have hXB : X = Bx := by
    rcases mem_tree_stX hX.1 with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | exact absurd hX.2.2.1 (by decide)
  subst hXB
  exact ⟨rfl, rfl, rfl, by decide, by decide, by decide⟩

end Consensus.Goldilocks.Store.Test

end
