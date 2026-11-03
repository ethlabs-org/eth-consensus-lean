module
public import ConsensusLeanTest.GoldilocksFGStoreService
@[expose] public section

/-! # Witnesses for G1.6 and G1.7 (FGStore entries) and their controls

Over the n = 1 trace pieces of `GoldilocksFGStoreService` (`P₁`: `Δ = 1`, `δ_t = 2`, `q = 1`;
`w₀`, `a₀`, `Bs`, `trS`). `trJ` extends `trS`'s run: after accepting `Bs` (cut `2`, time `1`),
`w₀` attests with source `Bs` (cut `3`, time `1`) and signs `a₁` (target vote for the entry `Bs`
at height `2`, finality pair `(1, genesis)`), processes `a₁` (cut `4`, time `1`), and accepts its
own proposal `Bf` of slot `2` on `Bs` carrying `a₁` (cut `5`, time `2`). Its chain state `σ[Bf]`
finalizes `(1, genesis)`, justifies `Bs` and enters height `3`. Labelled by kind (CONTRIBUTING
"Statements"):

* (a) G1.7 on `trS`: `trS_previousHeightNotJustifiedEntry` applies
  `previousHeightNotJustified_entry` to `trS_goodWindow` (the genesis entry, previous height not
  justified); `trS_justifier` shows that its block is `Bs` and computes `σ[Bs]`. Its second-window
  clause holds vacuously on `trS` (`trS_no_window_at_justifier`).
* (a) G1.6 on `trJ`: `trJ_localRun`, `trJ_goodWindow` (the entry `Bs`, previous height `1`
  justified, `a = 0`, `c_F = 1`, `k_F = 0`, served by `Bf` at cut `5` with the rows `{a₁}`),
  `trJ_previousHeightJustifiedEntry` applies `previousHeightJustified_entry`; `trJ_justifier` shows
  that its block is `Bf`, with `σ[Bf].F = genesis = σ[Bs].J` and `σ[Bf].h_F = 1 = σ[Bs].h_j`.
* (a) G1.7 with both windows on `trJ`: `trJ_genesis_goodWindow` (the genesis entry at cut `2`)
  and `trJ_previousHeightNotJustifiedEntry`; its second window is `trJ_goodWindow`, so
  `trJ_genesis_second_window` gets the finalization of `(1, genesis)` at `Z = Bf`.
* (control) `trS_justifier_finalizes_nothing`: at the G1.7 witness, G1.6's finalization equations
  hold only as `0 = 0`: the justifying block finalizes nothing beyond the entry state's genesis
  finalization, and `(1, genesis)` is pending there.
* (control) `trJ_justifier_finalizes_predecessor_only`: at the G1.6 witness, the justifying block
  raises `h_F` from `0` to `1 = h − 1` (G1.6's finalization of the predecessor) but not to `h`:
  the pair `(h, T_h) = (2, Bs)` is pending, not finalized, at it. G1.7's first conclusions hold
  there too (loose BJ: both kinds append the entry and enter `h + 1` with the previous height
  justified), and its second-window clause would be vacuous on `trJ`
  (`trJ_no_window_at_justifier`). -/

namespace Consensus.Goldilocks.Store.Test

/-! ## Blocks, trees and ancestry -/

/-- A block held under an updated root map is the added block or was held before. -/
theorem eq_or_of_update {f : Nat → Option (NodeBlock P₁ Unit)} {r : Nat}
    {B X : NodeBlock P₁ Unit} (h : Function.update f r (some B) X.root = some X) :
    X = B ∨ f X.root = some X := by
  by_cases hr : X.root = r
  · rw [hr, Function.update_self, Option.some.injEq] at h
    exact Or.inl h.symm
  · rw [Function.update_of_ne hr] at h
    exact Or.inr h

/-- The initial tree holds genesis only. -/
theorem eq_g₁_of_init {X : NodeBlock P₁ Unit} (h : X ∈ (Store.init (P := P₁) ()).tree) :
    X = g₁ := by
  change (Store.init (P := P₁) ()).blocks X.root = some X at h
  simp only [Store.init] at h
  split at h
  · exact (Option.some_inj.mp h).symm
  · cases h

/-- `stBs` holds genesis and `Bs`. -/
theorem mem_tree_stBs {X : NodeBlock P₁ Unit} (h : X ∈ stBs.tree) : X = g₁ ∨ X = Bs := by
  change Function.update (Store.init (P := P₁) ()).blocks 1 (some Bs) X.root = some X at h
  exact (eq_or_of_update h).symm.imp_left eq_g₁_of_init

/-- Genesis has no parent: its only ancestor, in any set, is itself. -/
theorem eq_g₁_of_anc {S : Set (NodeBlock P₁ Unit)} {B : NodeBlock P₁ Unit}
    (h : Goldilocks.Anc S B g₁) : B = g₁ := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨C, -, hC⟩
  · exact h.symm
  · cases hC.2.2

/-! ## G1.7 on `trS`: the genesis entry, previous height not justified -/

/-- (a) G1.7 applied on `trS`: the genesis entry (height `1`, previous height not justified) with
its good window `trS_goodWindow` gives `previousHeightNotJustified_entry`'s full conclusion. -/
theorem trS_previousHeightNotJustifiedEntry :
    ∃ X, JustifiesEntry P₁ Unit (trS.store w₀ (2 + 1)) g₁ ((trS.store w₀ 2).σ g₁.root).h X ∧
      (trS.store w₀ (2 + 1)).Anc X Bs ∧
      (((trS.store w₀ 2).σ g₁.root).h, g₁.root) ∈ ((trS.store w₀ (2 + 1)).σ X.root).pending ∧
      ((trS.store w₀ (2 + 1)).σ X.root).h = ((trS.store w₀ 2).σ g₁.root).h + 1 ∧
      ((trS.store w₀ (2 + 1)).σ X.root).Th = X.root ∧
      ((trS.store w₀ (2 + 1)).σ X.root).previousHeightJustified ∧
      ∀ (a₁ : Nat) (p₁ : Fin P₁.n) (i₁ : Nat) (Bs₁ Pr₁ : NodeBlock P₁ Unit)
        (R₁ : Finset (FG.Att P₁.n)), GoodWindow P₁ Unit {w₀} trS 1 X a₁ 0 p₁ i₁ Bs₁ Pr₁ R₁ →
        ∃ Z ∈ (trS.store p₁ (i₁ + 1)).tree, (trS.store p₁ (i₁ + 1)).Anc Z Bs₁ ∧
          ((trS.store p₁ (i₁ + 1)).σ Z.root).F = g₁.root ∧
          ((trS.store p₁ (i₁ + 1)).σ Z.root).hF = ((trS.store w₀ 2).σ g₁.root).h :=
  previousHeightNotJustified_entry P₁ Unit () {w₀} {g₁, Bs} trS trS_localRun 1 g₁ 0 0 w₀ 2 Bs g₁
    {a₀} trS_goodWindow trS_previousHeightNotJustifiedEntry_first.1

/-- The FG state of `w₀` before cuts `2` and `3` of `trS`. -/
theorem trS_store : trS.store w₀ 2 = stA ∧ trS.store w₀ (2 + 1) = stBs :=
  ⟨congrArg Prod.fst (trOf_state Bs stBs w₀).2.2.1,
    congrArg Prod.fst ((trOf_state Bs stBs w₀).2.2.2 0)⟩

/-- (a) The block of G1.7's conclusion on `trS` is `Bs`, the only block that justifies the genesis
entry after cut `2`; the entry has height `1`, and `σ[Bs]` has `(1, genesis)` pending, height `2`,
entry `Bs`, the justification `(1, genesis)`, its previous height justified, and `F = genesis`
with `h_F = 0`. -/
theorem trS_justifier :
    (∀ X, JustifiesEntry P₁ Unit (trS.store w₀ (2 + 1)) g₁ ((trS.store w₀ 2).σ g₁.root).h X →
      X = Bs) ∧
    ((trS.store w₀ 2).σ g₁.root).h = 1 ∧
    ((trS.store w₀ (2 + 1)).σ Bs.root).pending = [(1, g₁.root)] ∧
    ((trS.store w₀ (2 + 1)).σ Bs.root).h = 2 ∧ ((trS.store w₀ (2 + 1)).σ Bs.root).Th = Bs.root ∧
    ((trS.store w₀ (2 + 1)).σ Bs.root).hj = 1 ∧
    ((trS.store w₀ (2 + 1)).σ Bs.root).J = g₁.root ∧
    ((trS.store w₀ (2 + 1)).σ Bs.root).previousHeightJustified ∧
    ((trS.store w₀ (2 + 1)).σ Bs.root).F = g₁.root ∧
    ((trS.store w₀ (2 + 1)).σ Bs.root).hF = 0 := by
  rw [trS_store.1, trS_store.2]
  refine ⟨fun X hX => ?_, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl⟩
  rcases mem_tree_stBs hX.1 with rfl | rfl
  · exact absurd hX.2.2.1 (by decide)
  · rfl

/-- On `trS`, no good window has the entry `Bs`: `w₀` accepts a block only at cut `2`, before it
holds `Bs`. So G1.7's second-window clause holds vacuously on `trS`. -/
theorem trS_no_window_at_justifier (cF a kF : Nat) (p : Fin P₁.n) (i : Nat)
    (B Pr : NodeBlock P₁ Unit) (R : Finset (FG.Att P₁.n)) :
    ¬ GoodWindow P₁ Unit {w₀} trS cF Bs a kF p i B Pr R := by
  intro hw
  obtain rfl := eq_w₀ p
  have hacc := hw.proposal.2.1
  obtain ⟨rfl, -⟩ := (trOf_label Bs stBs i _ hacc.2).resolve_left (by simp)
    |>.resolve_left (by simp)
  have hT := hw.entry.1
  rw [trS_store.1] at hT
  exact absurd (congrArg Block.root (eq_g₁_of_init hT)) (by decide)

/-! ## The extended run `trJ` -/

/-- `w₀`'s row for the entry `Bs`: the target vote for `Bs` at height `2`, with `Bs`'s
predecessor `(1, genesis)` as its finality pair. -/
def a₁ : FG.Att P₁.n := ⟨w₀, 2, 1, false, some (1, 0)⟩

/-- `w₀`'s record after signing `a₁`. -/
def Λ₁ : FG.Record := Λ₀.recordAtt a₁

/-- On `stBs` and the record `Λ₀`, `fg_attest` with source `Bs` signs `a₁`: the entry state is
`σBs` (height `2`, entry `Bs`, previous height justified by genesis), and `Λ₀` permits `(1, 0)`. -/
theorem attest_stBs : stBs.attest Λ₀ w₀ Bs = some (a₁, Λ₁) := rfl

/-- `stBs` with `a₁` pooled. -/
def stBa : Store P₁ Unit := { stBs with atts := [a₀, a₁] }

/-- Processing `a₁` on `stBs` gives `stBa`. -/
theorem onAttestation_stBs : stBs.onAttestation a₁ = stBa := rfl

/-- `w₀`'s proposal of slot `2` on `Bs` carrying `a₁`: root `2`. -/
def Bf : NodeBlock P₁ Unit := ⟨2, some 1, 2, w₀, 0, [a₁], ()⟩

/-- The chain state of `Bf`: `a₁` sets the finality bit of `(1, 0)` (a finality quorum, `q = 1`),
so `(1, 0)` is finalized (`F = 0`, `h_F = 1`) and pruned; `a₁` is also a target quorum for `Bs`,
whose previous height is justified with `h_F = h_j`, so `Bf` justifies `Bs` (`J = 1`, `h_j = 2`,
pending `[(2, 1)]`) and enters height `3` with entry `Bf`. -/
def σBf : FG.ChainState P₁.n where
  L := 2
  s := 2
  h := 3
  Th := 2
  ThSlot := 2
  target := ∅
  prog := ∅
  pending := [(2, 1)]
  fin := Function.update (Function.update σBs.fin 1 (insert w₀ (σBs.fin 1))) 2 ∅
  J := 1
  hj := 2
  F := 0
  hF := 1

/-- `state_transition` of `Bf` from `σBs` gives `σBf`. -/
theorem stateTransition_Bf : P₁.fg.stateTransition (stBa.σ 1) Bf.fgView = some σBf := rfl

/-- `stBa` with `Bf` and its chain state added (before the finality update). -/
def stBf₀ : Store P₁ Unit :=
  { stBa with
    blocks := Function.update stBa.blocks 2 (some Bf)
    σ := Function.update stBa.σ 2 σBf }

/-- The FG state after accepting `Bf` on `stBa`: `Bf` and `σBf` added, `h_max = 3`, and the
justification cache at `Bs` with height `2`; `F` stays at genesis (the store's finality step
needs `Σ.F ≺ σ.F`, and `σBf.F` is genesis). -/
def stBf : Store P₁ Unit := { stBf₀ with J := Bs, hj := 2, hmax := 3 }

/-- `stBf` holds genesis, `Bs` and `Bf`. -/
theorem mem_tree_stBf {X : NodeBlock P₁ Unit} (h : X ∈ stBf.tree) :
    X = g₁ ∨ X = Bs ∨ X = Bf := by
  change Function.update stBs.blocks 2 (some Bf) X.root = some X at h
  rcases eq_or_of_update h with h | h
  · exact Or.inr (Or.inr h)
  · exact (mem_tree_stBs h).imp_right Or.inl

open Classical in
/-- The finality update of `Bf` on `stBf₀` gives `stBf`. -/
theorem updateFinality_stBf₀ : stBf₀.updateFinality σBf = stBf := by
  unfold updateFinality
  extract_lets st₁ st₂
  have h2 : st₂ = stBf := by
    change (match st₁.blocks 1 with
      | some X => if st₁.Anc st₁.F X ∧ LexLt (st₁.hj, st₁.J.root) (2, 1) then
          { st₁ with J := X, hj := 2 } else st₁
      | none => st₁) = stBf
    rw [show st₁.blocks 1 = some Bs from rfl]
    dsimp only
    rw [ite_eq_left ⟨Relation.ReflTransGen.single ⟨rfl, rfl, rfl⟩, Or.inl (by decide)⟩]
    rfl
  rw [h2, show stBf.blocks σBf.F = some g₁ from rfl]
  dsimp only
  rw [ite_eq_right (fun h => h.2.1 rfl)]

/-- `stBa` accepts `Bf`, with post-state `stBf` (`a₁` is pooled already). -/
theorem onBlock_stBa_Bf : stBa.onBlock Bf = some stBf := by
  have hanc : Goldilocks.Anc (insert Bf stBa.tree) stBa.F Bf :=
    Relation.ReflTransGen.tail (b := Bs)
      (Relation.ReflTransGen.single ⟨Or.inr rfl, Or.inr rfl, rfl⟩) ⟨Or.inr rfl, Or.inl rfl, rfl⟩
  have hneg : ¬ ((stBa.blocks Bf.root).isSome = true ∨ (stBa.blocks 1).isNone = true ∨
      ¬ Goldilocks.Anc (insert Bf stBa.tree) stBa.F Bf) := by
    rintro (h | h | h)
    · simp [stBa, stBs, stBs₀, stA, Store.init, Bf, P₁] at h
    · simp [stBa, stBs, stBs₀] at h
    · exact h hanc
  unfold onBlock
  split
  · next h => cases h
  next pr h =>
  cases h
  simp only [hneg, ↓reduceIte]
  split
  · next h => rw [stateTransition_Bf] at h; cases h
  next σ' h =>
  rw [stateTransition_Bf] at h; cases h
  change some ((updateFinality stBf₀ σBf).addAtts [a₁]) = some stBf
  rw [updateFinality_stBf₀]
  rfl

/-- The extended n = 1 trace: `trS`'s cuts `0`–`2` (`w₀` signs `a₀` at time `0`, processes it,
accepts `Bs` at time `1`), then at time `1` `w₀` attests with source `Bs` and signs `a₁` (cut `3`)
and processes `a₁` (cut `4`), and at time `2` accepts its own proposal `Bf` (cut `5`); then it
stutters. -/
def trJ : FGTrace P₁ Unit where
  init _ := (Store.init (), FG.Record.empty)
  node _ := w₀
  time i := if i < 2 then 0 else if i < 5 then 1 else 2
  event i := if i < 2 then 0 else if i < 5 then 1 else 2
  pos
    | 1 => 1
    | 3 => 1
    | 4 => 2
    | _ => 0
  label
    | 0 => some (.attest g₁ (some a₀))
    | 1 => some (.attestation a₀)
    | 2 => some (.block Bs true)
    | 3 => some (.attest Bs (some a₁))
    | 4 => some (.attestation a₁)
    | 5 => some (.block Bf true)
    | _ => none
  post
    | 0 => (Store.init (), Λ₀)
    | 1 => (stA, Λ₀)
    | 2 => (stBs, Λ₀)
    | 3 => (stBs, Λ₁)
    | 4 => (stBa, Λ₁)
    | _ => (stBf, Λ₁)
  awake _ _ := True

/-- The states of `trJ` before each cut. -/
theorem trJ_state (y : Fin P₁.n) :
    trJ.state y 0 = (Store.init (), FG.Record.empty) ∧ trJ.state y 1 = (Store.init (), Λ₀) ∧
      trJ.state y 2 = (stA, Λ₀) ∧ trJ.state y 3 = (stBs, Λ₀) ∧ trJ.state y 4 = (stBs, Λ₁) ∧
      trJ.state y 5 = (stBa, Λ₁) ∧ ∀ i, trJ.state y (i + 6) = (stBf, Λ₁) := by
  obtain rfl := eq_w₀ y
  refine ⟨rfl, by simp [Trace.state, trJ], by simp [Trace.state, trJ], by simp [Trace.state, trJ],
    by simp [Trace.state, trJ], by simp [Trace.state, trJ], fun i => ?_⟩
  induction i with
  | zero => simp [Trace.state, trJ]
  | succ i ih => rw [Trace.state, ite_eq_right (by simp [trJ])]; exact ih

/-- The FG state of `w₀` before cuts `2`–`6` of `trJ`. -/
theorem trJ_store :
    trJ.store w₀ 2 = stA ∧ trJ.store w₀ (2 + 1) = stBs ∧ trJ.store w₀ 4 = stBs ∧
      trJ.store w₀ 5 = stBa ∧ trJ.store w₀ (5 + 1) = stBf := by
  obtain ⟨-, -, h2, h3, h4, h5, h6⟩ := trJ_state w₀
  exact ⟨congrArg Prod.fst h2, congrArg Prod.fst h3, congrArg Prod.fst h4, congrArg Prod.fst h5,
    congrArg Prod.fst (h6 0)⟩

/-- The labelled cuts of `trJ`. -/
theorem trJ_label (i : Nat) (ℓ : FGLabel P₁ Unit) (h : trJ.label i = some ℓ) :
    (i = 0 ∧ ℓ = .attest g₁ (some a₀)) ∨ (i = 1 ∧ ℓ = .attestation a₀) ∨
      (i = 2 ∧ ℓ = .block Bs true) ∨ (i = 3 ∧ ℓ = .attest Bs (some a₁)) ∨
      (i = 4 ∧ ℓ = .attestation a₁) ∨ (i = 5 ∧ ℓ = .block Bf true) := by
  rcases i with _ | _ | _ | _ | _ | _ | i <;> simp [trJ] at h <;> simp [h]

/-- (a) `trJ` is an `FGLocalRun` for the honest set `{w₀}` inside `{genesis, Bs, Bf}`. -/
theorem trJ_localRun : FGLocalRun () {w₀} {g₁, Bs, Bf} trJ where
  coherent := by
    refine ⟨?_, ?_⟩
    · rintro X (rfl | rfl | rfl) Y (rfl | rfl | rfl) h <;>
        first | rfl | exact absurd h (by decide)
    · rintro X (rfl | rfl | rfl) Y (rfl | rfl | rfl) h <;>
        first | decide | exact absurd h (by decide)
  init _ _ := rfl
  exec i ℓ h _ := by
    obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := trJ_state w₀
    rcases trJ_label i ℓ h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩
    · change FGLabel.Step w₀ (trJ.state w₀ 0) _ (Store.init (), Λ₀)
      rw [h0]
      exact ⟨rfl, by rw [attest_init]; exact ⟨rfl, rfl⟩⟩
    · change FGLabel.Step w₀ (trJ.state w₀ 1) _ (stA, Λ₀)
      rw [h1]
      rfl
    · change FGLabel.Step w₀ (trJ.state w₀ 2) _ (stBs, Λ₀)
      rw [h2]
      exact Or.inl ⟨rfl, onBlock_stA_Bs, rfl⟩
    · change FGLabel.Step w₀ (trJ.state w₀ 3) _ (stBs, Λ₁)
      rw [h3]
      exact ⟨rfl, by rw [attest_stBs]; exact ⟨rfl, rfl⟩⟩
    · change FGLabel.Step w₀ (trJ.state w₀ 4) _ (stBa, Λ₁)
      rw [h4]
      rfl
    · change FGLabel.Step w₀ (trJ.state w₀ 5) _ (stBf, Λ₁)
      rw [h5]
      exact Or.inl ⟨rfl, onBlock_stBa_Bf, rfl⟩
  tree_subset y _ i := by
    intro X hX
    obtain rfl := eq_w₀ y
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := trJ_state w₀
    rcases i with _ | _ | _ | _ | _ | _ | i
    · rw [FGTrace.store, h0] at hX; exact Or.inl (eq_g₁_of_init hX)
    · rw [FGTrace.store, h1] at hX; exact Or.inl (eq_g₁_of_init hX)
    · rw [FGTrace.store, h2] at hX; exact Or.inl (eq_g₁_of_init hX)
    · rw [FGTrace.store, h3] at hX; exact (mem_tree_stBs hX).imp_right Or.inl
    · rw [FGTrace.store, h4] at hX; exact (mem_tree_stBs hX).imp_right Or.inl
    · rw [FGTrace.store, h5] at hX; exact (mem_tree_stBs hX).imp_right Or.inl
    · rw [FGTrace.store, h6] at hX; exact mem_tree_stBf hX
  time_nonneg i := by simp only [trJ]; split_ifs <;> decide
  time_mono i j hij := by simp only [trJ]; split_ifs <;> first | decide | omega
  attest_public _ _ _ _ _ _ := one_dvd _
  own_first y _ i X h _ _ k hk ℓ _ := by
    rcases trJ_label i _ h.2 with ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ |
      ⟨rfl, h'⟩ <;>
      first | (cases h'; done) | (simp only [trJ]; split_ifs <;> first | decide | omega)
  attest_order y _ j src signed h i ℓ hij hi ht := by
    obtain rfl := eq_w₀ y
    rcases trJ_label j _ h.2 with ⟨rfl, -⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨rfl, -⟩ | ⟨-, h'⟩ | ⟨-, h'⟩
    · omega
    · cases h'
    · cases h'
    · rcases trJ_label i ℓ hi.2 with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, rfl⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
        ⟨rfl, -⟩
      · exact absurd ht (by decide)
      · exact absurd ht (by decide)
      · exact ⟨Bs, true, rfl, rfl, rfl⟩
      all_goals omega
    · cases h'
    · cases h'
  own_payload y _ i X h _ _ a ha := by
    obtain rfl := eq_w₀ y
    rcases trJ_label i _ h.2 with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨rfl, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨rfl, h'⟩ <;>
      cases h'
    · rw [List.mem_singleton.mp ha, trJ_store.1]
      exact List.mem_singleton_self _
    · rw [List.mem_singleton.mp ha, trJ_store.2.2.2.1]
      exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  unforgeable y _ i a h _ := by
    obtain ⟨ℓ, hℓ, ha⟩ := h
    rcases trJ_label i ℓ hℓ.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases ha
    · rw [List.mem_singleton.mp ha]; exact ⟨0, by omega, g₁, rfl, rfl⟩
    · rw [List.mem_singleton.mp ha]; exact ⟨0, by omega, g₁, rfl, rfl⟩
    · cases ha
    · rw [List.mem_singleton.mp ha]; exact ⟨3, by omega, Bs, rfl, rfl⟩
    · rw [List.mem_singleton.mp ha]; exact ⟨3, by omega, Bs, rfl, rfl⟩

/-! ## G1.6 on `trJ`: the entry `Bs`, previous height justified -/

/-- (a) On `trJ`, the entry `Bs` (height `2`, slot `1`; its previous height `1` is justified by
genesis) has a good window with `a = 0`, `c_F = 1`, `k_F = 0`, served by `w₀`'s proposal `Bf` of
slot `2` at cut `5` on `Bs`, with the rows `{a₁}` (signed at cut `3`, time `1`, pooled at cut
`4`; `a₁` carries `P_E = (1, genesis)`). -/
theorem trJ_goodWindow : GoodWindow P₁ Unit {w₀} trJ 1 Bs 0 0 w₀ 5 Bf Bs {a₁} := by
  refine ⟨⟨rfl, ⟨rfl, rfl⟩, rfl, rfl, ?_, rfl, ?_⟩, ?_, ?_, ⟨le_rfl, le_rfl⟩, by decide, ?_, ?_,
    ?_, ⟨by decide, by decide⟩⟩ <;> rw [trJ_store.2.2.2.1]
  · exact (rfl : stBa.blocks 1 = some Bs)
  · intro r hr hv _
    rcases List.mem_cons.mp hr with rfl | hr
    · exact absurd hv (by decide)
    · rw [List.mem_singleton.mp hr]
      exact List.mem_singleton_self _
  · exact ⟨rfl, rfl⟩
  · exact Relation.ReflTransGen.refl
  · intro r hr
    rw [Finset.mem_singleton.mp hr]
    exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
  · intro r hr
    rw [Finset.mem_singleton.mp hr]
    exact Or.inr fun _ => ⟨3, ⟨Bs, rfl, rfl⟩, by decide⟩
  · intro r hr
    rw [Finset.mem_singleton.mp hr]
    exact Or.inr (List.mem_cons_of_mem _ (List.mem_singleton_self _))

/-- (a) At cut `5` of `trJ`, the entry `Bs` has its previous height justified. -/
theorem trJ_entry_previousHeightJustified :
    ((trJ.store w₀ 5).σ Bs.root).previousHeightJustified := by
  rw [trJ_store.2.2.2.1]
  decide

/-- (a) G1.6 applied on `trJ`: the entry `Bs` with its good window `trJ_goodWindow` gives
`previousHeightJustified_entry`'s conclusion. -/
theorem trJ_previousHeightJustifiedEntry :
    ∃ X, JustifiesEntry P₁ Unit (trJ.store w₀ (5 + 1)) Bs ((trJ.store w₀ 5).σ Bs.root).h X ∧
      (trJ.store w₀ (5 + 1)).Anc X Bf ∧
      ((trJ.store w₀ (5 + 1)).σ X.root).F = ((trJ.store w₀ 5).σ Bs.root).J ∧
      ((trJ.store w₀ (5 + 1)).σ X.root).hF = ((trJ.store w₀ 5).σ Bs.root).hj :=
  previousHeightJustified_entry P₁ Unit () {w₀} {g₁, Bs, Bf} trJ trJ_localRun 1 Bs 0 0 w₀ 5 Bf
    Bs {a₁} trJ_goodWindow trJ_entry_previousHeightJustified

/-- (a) The block of G1.6's conclusion on `trJ` is `Bf`, the only block that justifies `Bs` after
cut `5`: the entry state `σ[Bs]` has height `2`, `P_E = (h_j, J) = (1, genesis)` and `h_F = 0`,
and `σ[Bf]` finalizes `P_E`: `F = genesis`, `h_F = 1`. -/
theorem trJ_justifier :
    (∀ X, JustifiesEntry P₁ Unit (trJ.store w₀ (5 + 1)) Bs ((trJ.store w₀ 5).σ Bs.root).h X →
      X = Bf) ∧
    JustifiesEntry P₁ Unit (trJ.store w₀ (5 + 1)) Bs ((trJ.store w₀ 5).σ Bs.root).h Bf ∧
    ((trJ.store w₀ 5).σ Bs.root).h = 2 ∧ ((trJ.store w₀ 5).σ Bs.root).hj = 1 ∧
    ((trJ.store w₀ 5).σ Bs.root).J = g₁.root ∧ ((trJ.store w₀ 5).σ Bs.root).hF = 0 ∧
    ((trJ.store w₀ (5 + 1)).σ Bf.root).F = g₁.root ∧
    ((trJ.store w₀ (5 + 1)).σ Bf.root).hF = 1 := by
  rw [trJ_store.2.2.2.1, trJ_store.2.2.2.2]
  refine ⟨fun X hX => ?_, ⟨rfl, Relation.ReflTransGen.single ⟨rfl, rfl, rfl⟩, rfl, rfl, ?_⟩, rfl,
    rfl, rfl, rfl, rfl, rfl⟩
  · rcases mem_tree_stBf hX.1 with rfl | rfl | rfl
    · exact absurd hX.2.2.1 (by decide)
    · exact absurd hX.2.2.1 (by decide)
    · rfl
  · intro Y hY hBY _ hne
    rcases mem_tree_stBf hY with rfl | rfl | rfl
    · exact absurd (congrArg Block.root (eq_g₁_of_anc hBY)) (by decide)
    · exact ⟨rfl, rfl⟩
    · exact absurd rfl hne

/-! ## G1.7 with both windows on `trJ` -/

/-- (a) On `trJ`, the genesis entry has the good window of `trS_goodWindow`: served by `Bs` at
cut `2` on genesis, with the rows `{a₀}`. -/
theorem trJ_genesis_goodWindow : GoodWindow P₁ Unit {w₀} trJ 1 g₁ 0 0 w₀ 2 Bs g₁ {a₀} := by
  refine ⟨⟨rfl, ⟨rfl, rfl⟩, rfl, rfl, ?_, rfl, ?_⟩, ?_, ?_, ⟨le_rfl, le_rfl⟩, by decide, ?_, ?_,
    ?_, ⟨by decide, by decide⟩⟩ <;> rw [trJ_store.1]
  · exact g₁_mem_stA
  · exact fun r hr _ _ => hr
  · exact ⟨g₁_mem_stA, rfl⟩
  · exact Relation.ReflTransGen.refl
  · intro r hr
    rw [Finset.mem_singleton.mp hr]
    exact ⟨rfl, rfl, rfl, fun h => absurd h (by decide)⟩
  · intro r hr
    rw [Finset.mem_singleton.mp hr]
    exact Or.inr fun _ => ⟨0, ⟨g₁, rfl, rfl⟩, by decide⟩
  · intro r hr
    rw [Finset.mem_singleton.mp hr]
    exact Or.inr (List.mem_singleton_self _)

/-- (a) G1.7 applied on `trJ` at the genesis entry (previous height not justified at cut `2`). -/
theorem trJ_previousHeightNotJustifiedEntry :
    ∃ X, JustifiesEntry P₁ Unit (trJ.store w₀ (2 + 1)) g₁ ((trJ.store w₀ 2).σ g₁.root).h X ∧
      (trJ.store w₀ (2 + 1)).Anc X Bs ∧
      (((trJ.store w₀ 2).σ g₁.root).h, g₁.root) ∈ ((trJ.store w₀ (2 + 1)).σ X.root).pending ∧
      ((trJ.store w₀ (2 + 1)).σ X.root).h = ((trJ.store w₀ 2).σ g₁.root).h + 1 ∧
      ((trJ.store w₀ (2 + 1)).σ X.root).Th = X.root ∧
      ((trJ.store w₀ (2 + 1)).σ X.root).previousHeightJustified ∧
      ∀ (a₁ : Nat) (p₁ : Fin P₁.n) (i₁ : Nat) (Bs₁ Pr₁ : NodeBlock P₁ Unit)
        (R₁ : Finset (FG.Att P₁.n)), GoodWindow P₁ Unit {w₀} trJ 1 X a₁ 0 p₁ i₁ Bs₁ Pr₁ R₁ →
        ∃ Z ∈ (trJ.store p₁ (i₁ + 1)).tree, (trJ.store p₁ (i₁ + 1)).Anc Z Bs₁ ∧
          ((trJ.store p₁ (i₁ + 1)).σ Z.root).F = g₁.root ∧
          ((trJ.store p₁ (i₁ + 1)).σ Z.root).hF = ((trJ.store w₀ 2).σ g₁.root).h :=
  previousHeightNotJustified_entry P₁ Unit () {w₀} {g₁, Bs, Bf} trJ trJ_localRun 1 g₁ 0 0 w₀ 2
    Bs g₁ {a₀} trJ_genesis_goodWindow (by rw [trJ_store.1]; decide)

/-- (a) G1.7's second window on `trJ` is not vacuous: the block of its first conclusion is `Bs`,
whose good window is `trJ_goodWindow`, so the pair `(1, genesis)` is finalized on the chain of
`Bf`; the block that finalizes it is `Bf` (`F = genesis`, `h_F = 1`). -/
theorem trJ_genesis_second_window :
    (∃ Z ∈ (trJ.store w₀ (5 + 1)).tree, (trJ.store w₀ (5 + 1)).Anc Z Bf ∧
      ((trJ.store w₀ (5 + 1)).σ Z.root).F = g₁.root ∧
      ((trJ.store w₀ (5 + 1)).σ Z.root).hF = ((trJ.store w₀ 2).σ g₁.root).h) ∧
    ∀ Z ∈ (trJ.store w₀ (5 + 1)).tree,
      ((trJ.store w₀ (5 + 1)).σ Z.root).hF = ((trJ.store w₀ 2).σ g₁.root).h → Z = Bf := by
  obtain ⟨X, hX, -, -, -, -, -, hZ⟩ := trJ_previousHeightNotJustifiedEntry
  have hXB : X = Bs := by
    rw [trJ_store.1, trJ_store.2.1] at hX
    rcases mem_tree_stBs hX.1 with rfl | rfl
    · exact absurd hX.2.2.1 (by decide)
    · rfl
  subst hXB
  refine ⟨hZ 0 w₀ 5 Bf Bs {a₁} trJ_goodWindow, fun Z hZt hZh => ?_⟩
  rw [trJ_store.1, trJ_store.2.2.2.2] at *
  rcases mem_tree_stBf hZt with rfl | rfl | rfl
  · exact absurd hZh (by decide)
  · exact absurd hZh (by decide)
  · rfl

/-! ## Controls -/

/-- (control) At the G1.7 witness, G1.6's finalization part carries no content: the block that
justifies the genesis entry finalizes nothing beyond the entry state's own finalization (`F` and
`h_F` of `σ[X]` are those of the genesis state, `h_F = 0`), so `σ[X].h_F = σ[T].h_j` holds only
as `0 = 0` (genesis height `1` has no predecessor height to justify), and the pair `(1, genesis)`
that `X` justifies is pending, not finalized, at `X`. -/
theorem trS_justifier_finalizes_nothing :
    ∀ X, JustifiesEntry P₁ Unit (trS.store w₀ (2 + 1)) g₁ ((trS.store w₀ 2).σ g₁.root).h X →
      ((trS.store w₀ (2 + 1)).σ X.root).F = ((trS.store w₀ 2).σ g₁.root).F ∧
      ((trS.store w₀ (2 + 1)).σ X.root).hF = ((trS.store w₀ 2).σ g₁.root).hF ∧
      ((trS.store w₀ 2).σ g₁.root).hF = 0 ∧ ((trS.store w₀ 2).σ g₁.root).hj = 0 ∧
      ((trS.store w₀ (2 + 1)).σ X.root).hF < ((trS.store w₀ 2).σ g₁.root).h ∧
      (((trS.store w₀ 2).σ g₁.root).h, g₁.root) ∈ ((trS.store w₀ (2 + 1)).σ X.root).pending := by
  intro X hX
  obtain rfl := trS_justifier.1 X hX
  rw [trS_store.1, trS_store.2]
  exact ⟨rfl, rfl, rfl, rfl, by decide, List.mem_singleton_self _⟩

/-- (control) At the G1.6 witness, the justifying block finalizes the predecessor and only it:
`σ[X].h_F` rises from the entry state's `0` to `1 = h − 1`, but stays below `h = 2`, and
`σ[X].F` is not `Bs`: the pair `(h, T_h) = (2, Bs)` is pending, not finalized, at `X`. G1.7's
first conclusions hold at `X` too (`(h, T_h)` pending, height `h + 1`, entry `X`, previous height
justified). -/
theorem trJ_justifier_finalizes_predecessor_only :
    ∀ X, JustifiesEntry P₁ Unit (trJ.store w₀ (5 + 1)) Bs ((trJ.store w₀ 5).σ Bs.root).h X →
      ((trJ.store w₀ 5).σ Bs.root).hF < ((trJ.store w₀ (5 + 1)).σ X.root).hF ∧
      ((trJ.store w₀ (5 + 1)).σ X.root).hF + 1 = ((trJ.store w₀ 5).σ Bs.root).h ∧
      ((trJ.store w₀ (5 + 1)).σ X.root).F ≠ Bs.root ∧
      (((trJ.store w₀ 5).σ Bs.root).h, Bs.root) ∈ ((trJ.store w₀ (5 + 1)).σ X.root).pending ∧
      ((trJ.store w₀ (5 + 1)).σ X.root).h = ((trJ.store w₀ 5).σ Bs.root).h + 1 ∧
      ((trJ.store w₀ (5 + 1)).σ X.root).Th = X.root ∧
      ((trJ.store w₀ (5 + 1)).σ X.root).previousHeightJustified := by
  intro X hX
  obtain rfl := trJ_justifier.1 X hX
  rw [trJ_store.2.2.2.1, trJ_store.2.2.2.2]
  exact ⟨by decide, rfl, by decide, List.mem_singleton_self _, rfl, rfl, by decide⟩

/-- On `trJ`, no good window has the entry `Bf`: `w₀` accepts blocks only at cuts `2` and `5`,
before it holds `Bf`. So G1.7's second-window clause for the entry `Bs` would be vacuous on
`trJ`. -/
theorem trJ_no_window_at_justifier (cF a kF : Nat) (p : Fin P₁.n) (i : Nat)
    (B Pr : NodeBlock P₁ Unit) (R : Finset (FG.Att P₁.n)) :
    ¬ GoodWindow P₁ Unit {w₀} trJ cF Bf a kF p i B Pr R := by
  intro hw
  obtain rfl := eq_w₀ p
  have hT := hw.entry.1
  rcases trJ_label i _ hw.proposal.2.1.2 with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨rfl, -⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ |
    ⟨rfl, -⟩
  · cases h'
  · cases h'
  · rw [trJ_store.1] at hT
    exact absurd (congrArg Block.root (eq_g₁_of_init hT)) (by decide)
  · cases h'
  · cases h'
  · rw [trJ_store.2.2.2.1] at hT
    rcases mem_tree_stBs hT with h | h <;> exact absurd (congrArg Block.root h) (by decide)

end Consensus.Goldilocks.Store.Test

end
