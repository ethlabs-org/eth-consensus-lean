module
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service
@[expose] public section

/-! # The `1 ≤ r` premise of the Goldilocks crossing bound (G1.8 (a)) at `δ_t = 0`

On `Statements/FGStore/Service`, labelled by kind (CONTRIBUTING "Statements"). A
premise-necessity fixture, not a counterexample to `Crossing`: the n = 1 FG trace of
`GoldilocksFGStoreService` (`w₀` signs the target row `a₀` for genesis at time `0`, pools it, and
proposes `Bs` of slot `1` carrying it at time `1`), rebuilt at `P₀`, the parameters `P₁` with
`δ_t = 0`. At `δ_t = 0` the bound of `Crossing` is `T.slot + max(δ_t, r) + g − 1 = u + r + g − 1`,
so the `1 ≤ r` premise is not implied by `δ_t` (at `δ_t ≥ 1` it would be).

* (a) `trS₀_localRun`: the trace is an `FGLocalRun` for `{w₀}` inside `{genesis, Bs}`; at
  `δ_t = 0` the timeout arm does not fire before `Bs` (no progress quorum on the genesis state),
  and `Bs` justifies genesis (justification takes precedence over timeout), as at `δ_t = 2`.
* (a) `trS₀_proposal_Bs`, `trS₀_quorum`, `trS₀_window`: `Bs` is an honest proposal at cut `2`
  whose proposer's pool holds a progress quorum of current-entry rows (`{a₀}`, `q = 1`), so the
  window condition of `Crossing` holds for `T = genesis`, `C = Bs`, `g = 1` and every `r`.
* (r) `crossing_needs_one_le_r`: with `g = 1`, `r = 0`, `T = genesis` (height `1`, slot `0`) and
  `C = Bs` at cut `3`, every premise of `Crossing` but `1 ≤ r` holds, and its conclusion fails:
  `Bs` leaves height `1` at slot `1`, but the bound is `0 + max 0 0 + 1 − 1 = 0`, one slot short
  (the statement's docstring: rows for an entry of slot `u` are signed from `t_u` on).
* (a) `crossing_one_le_r`: the same instance with `r = 1` satisfies every premise, `crossing`
  gives its conclusion (bound `1`), and its only witness is `Bs`, at slot `1`. -/

namespace Consensus.Goldilocks.Store.Test.DeltaZero

/-- One validator, `Δ = 1`, slot `s` starts at `s`, genesis root `0`, `δ_t = 0`. -/
def P₀ : Params where
  n := 1
  hn := le_rfl
  Δ := 1
  hΔ := one_pos
  slotTime s := s
  slotTime_zero := rfl
  slotTime_strictMono := fun _ _ h => Nat.cast_lt.mpr h
  slotTime_public := fun _ => one_dvd _
  genesisRoot := 0
  δt := 0

/-- The only validator of `P₀`. -/
def w₀ : Fin P₀.n := ⟨0, Nat.one_pos⟩

/-- Every validator of `P₀` is `w₀`. -/
theorem eq_w₀ (y : Fin P₀.n) : y = w₀ := Fin.ext (Nat.lt_one_iff.mp y.isLt)

/-- Genesis of `P₀` (root `0`, slot `0`). -/
abbrev g₀ : NodeBlock P₀ Unit := P₀.genesisBlock ()

/-- `w₀`'s attestation with source genesis: the target vote for genesis at height `1`, no
finality pair. -/
def a₀ : FG.Att P₀.n := ⟨w₀, 1, 0, false, none⟩

/-- `w₀`'s record after signing `a₀`. -/
def Λ₀ : FG.Record := FG.Record.empty.recordAtt a₀

/-- On the initial state and the empty record, `fg_attest` with source genesis signs `a₀`. -/
theorem attest_init : (Store.init (P := P₀) ()).attest FG.Record.empty w₀ g₀ = some (a₀, Λ₀) :=
  rfl

/-- The initial state with `a₀` pooled. -/
def stA : Store P₀ Unit := { Store.init () with atts := [a₀] }

/-- Processing `a₀` on the initial state gives `stA`. -/
theorem onAttestation_init : (Store.init (P := P₀) ()).onAttestation a₀ = stA := rfl

/-- Genesis is held in `stA`. -/
theorem g₀_mem_stA : g₀ ∈ stA.tree := rfl

/-- `w₀`'s proposal of slot `1` on genesis carrying `a₀`: root `1`. -/
def Bs : NodeBlock P₀ Unit := ⟨1, some 0, 1, w₀, 0, [a₀], ()⟩

/-- The chain state of `Bs`: `a₀` is a target quorum (`q = 1`) for genesis, so `Bs` justifies
genesis (`J = 0`, `h_j = 1`, pending `[(1, 0)]`) and enters height `2` with entry `Bs`. -/
def σBs : FG.ChainState P₀.n where
  L := 1
  s := 1
  h := 2
  Th := 1
  ThSlot := 1
  target := ∅
  prog := ∅
  pending := [(1, 0)]
  fin := Function.update (fun _ => ∅) 1 ∅
  J := 0
  hj := 1
  F := 0
  hF := 0

/-- `state_transition` of `Bs` from the genesis state gives `σBs` at `δ_t = 0` too. -/
theorem stateTransition_Bs : P₀.fg.stateTransition (stA.σ 0) Bs.fgView = some σBs := rfl

/-- `stA` with `Bs` and its chain state added (before the finality update). -/
def stBs₀ : Store P₀ Unit :=
  { stA with
    blocks := Function.update stA.blocks 1 (some Bs)
    σ := Function.update stA.σ 1 σBs }

/-- The FG state after accepting `Bs` on `stA`: `Bs` and `σBs` added, `h_max = 2`, and the
justification cache at genesis with height `1`; `F` stays at genesis. -/
def stBs : Store P₀ Unit := { stBs₀ with hj := 1, hmax := 2 }

open Classical in
/-- The finality update of `Bs` on `stBs₀` gives `stBs`. -/
theorem updateFinality_stBs₀ : stBs₀.updateFinality σBs = stBs := by
  unfold updateFinality
  extract_lets st₁ st₂
  have h2 : st₂ = stBs := by
    change (match st₁.blocks 0 with
      | some X => if st₁.Anc st₁.F X ∧ LexLt (st₁.hj, st₁.J.root) (1, 0) then
          { st₁ with J := X, hj := 1 } else st₁
      | none => st₁) = stBs
    rw [show st₁.blocks 0 = some g₀ from rfl]
    dsimp only
    rw [ite_eq_left ⟨Relation.ReflTransGen.refl, Or.inl Nat.one_pos⟩]
    rfl
  rw [h2, show stBs.blocks σBs.F = some g₀ from rfl]
  dsimp only
  rw [ite_eq_right (fun h => h.2.1 rfl)]

/-- `stA` accepts `Bs`, with post-state `stBs` (`a₀` is pooled already). -/
theorem onBlock_stA_Bs : stA.onBlock Bs = some stBs := by
  have hanc : Goldilocks.Anc (insert Bs stA.tree) stA.F Bs :=
    Relation.ReflTransGen.single ⟨Or.inr g₀_mem_stA, Or.inl rfl, rfl⟩
  have hneg : ¬ ((stA.blocks Bs.root).isSome = true ∨ (stA.blocks 0).isNone = true ∨
      ¬ Goldilocks.Anc (insert Bs stA.tree) stA.F Bs) := by
    rintro (h | h | h)
    · simp [stA, Store.init, Bs, P₀] at h
    · simp [stA, Store.init, P₀] at h
    · exact h hanc
  unfold onBlock
  split
  · next h => cases h
  next pr h =>
  cases h
  simp only [hneg, ↓reduceIte]
  split
  · next h => rw [stateTransition_Bs] at h; cases h
  next σ' h =>
  rw [stateTransition_Bs] at h; cases h
  change some ((updateFinality stBs₀ σBs).addAtts [a₀]) = some stBs
  rw [updateFinality_stBs₀]
  rfl

/-- The n = 1 trace: `w₀` attests with source genesis at time `0` and signs `a₀` (cut `0`),
processes `a₀` (cut `1`, same tick), and accepts its own proposal `Bs` of slot `1` at time `1`
with post-state `stBs` (cut `2`); then it stutters. -/
def trS₀ : FGTrace P₀ Unit where
  init _ := (Store.init (), FG.Record.empty)
  node _ := w₀
  time i := if i < 2 then 0 else 1
  event i := if i < 2 then 0 else 1
  pos i := if i = 1 then 1 else 0
  label
    | 0 => some (.attest g₀ (some a₀))
    | 1 => some (.attestation a₀)
    | 2 => some (.block Bs true)
    | _ => none
  post
    | 0 => (Store.init (), Λ₀)
    | 1 => (stA, Λ₀)
    | _ => (stBs, Λ₀)
  awake _ _ := True

/-- The states of `trS₀`: the initial one, then after `a₀` is signed, after it is processed, and
after `Bs` is accepted. -/
theorem trS₀_state (y : Fin P₀.n) :
    trS₀.state y 0 = (Store.init (), FG.Record.empty) ∧ trS₀.state y 1 = (Store.init (), Λ₀) ∧
      trS₀.state y 2 = (stA, Λ₀) ∧ ∀ i, trS₀.state y (i + 3) = (stBs, Λ₀) := by
  obtain rfl := eq_w₀ y
  refine ⟨rfl, by simp [Trace.state, trS₀], by simp [Trace.state, trS₀], fun i => ?_⟩
  induction i with
  | zero => simp [Trace.state, trS₀]
  | succ i ih => rw [Trace.state, ite_eq_right (by simp [trS₀])]; exact ih

/-- The trees of `trS₀`: the initial one before `Bs` is accepted, `stBs`'s after. -/
theorem trS₀_blocks (y : Fin P₀.n) (i : Nat) :
    (trS₀.store y i).blocks = (Store.init ()).blocks ∨ (trS₀.store y i).blocks = stBs.blocks := by
  obtain ⟨h0, h1, h2, h3⟩ := trS₀_state y
  rcases i with _ | _ | _ | i
  · exact Or.inl (by rw [FGTrace.store, h0])
  · exact Or.inl (by rw [FGTrace.store, h1])
  · exact Or.inl (by rw [FGTrace.store, h2]; rfl)
  · exact Or.inr (by rw [FGTrace.store, h3])

/-- The labelled cuts of `trS₀`. -/
theorem trS₀_label (i : Nat) (ℓ : FGLabel P₀ Unit) (h : trS₀.label i = some ℓ) :
    (i = 0 ∧ ℓ = .attest g₀ (some a₀)) ∨ (i = 1 ∧ ℓ = .attestation a₀) ∨
      (i = 2 ∧ ℓ = .block Bs true) := by
  rcases i with _ | _ | _ | i <;> simp [trS₀] at h <;> simp [h]

/-- (a) `trS₀` is an `FGLocalRun` for the honest set `{w₀}` inside `{genesis, Bs}`. -/
theorem trS₀_localRun : FGLocalRun () {w₀} {g₀, Bs} trS₀ where
  coherent := by
    refine ⟨?_, ?_⟩
    · rintro X (rfl | rfl) Y (rfl | rfl) h <;> first | rfl | simp_all [Params.genesisBlock, P₀, Bs]
    · rintro X (rfl | rfl) Y (rfl | rfl) h <;> simp_all [Params.genesisBlock, P₀, Bs]
  init _ _ := rfl
  exec i ℓ h _ := by
    obtain ⟨h0, h1, h2, -⟩ := trS₀_state w₀
    rcases trS₀_label i ℓ h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · change FGLabel.Step w₀ (trS₀.state w₀ 0) _ (Store.init (), Λ₀)
      rw [h0]
      exact ⟨rfl, by rw [attest_init]; exact ⟨rfl, rfl⟩⟩
    · change FGLabel.Step w₀ (trS₀.state w₀ 1) _ (stA, Λ₀)
      rw [h1]
      rfl
    · change FGLabel.Step w₀ (trS₀.state w₀ 2) _ (stBs, Λ₀)
      rw [h2]
      exact Or.inl ⟨rfl, onBlock_stA_Bs, rfl⟩
  tree_subset y _ i := by
    intro X hX
    change (trS₀.store y i).blocks X.root = some X at hX
    have hg : ∀ r, (Store.init (P := P₀) ()).blocks r = some X → X = g₀ := by
      intro r hr
      simp only [Store.init] at hr
      split at hr
      · exact (Option.some_inj.mp hr).symm
      · cases hr
    rcases trS₀_blocks y i with h | h <;> rw [h] at hX
    · exact Or.inl (hg _ hX)
    · change Function.update stA.blocks 1 (some Bs) X.root = some X at hX
      by_cases h1 : X.root = 1
      · rw [h1, Function.update_self, Option.some.injEq] at hX
        exact Or.inr hX.symm
      · rw [Function.update_of_ne h1] at hX
        exact Or.inl (hg _ hX)
  time_nonneg i := by simp only [trS₀]; split <;> decide
  time_mono i j hij := by simp only [trS₀]; split <;> split <;> first | decide | omega
  attest_public _ _ _ _ _ _ := one_dvd _
  own_first y _ i X h _ _ k hk ℓ _ := by
    obtain ⟨rfl, -⟩ := (trS₀_label i _ h.2).resolve_left (by simp) |>.resolve_left (by simp)
    simp only [trS₀]
    rw [ite_eq_left hk]
    decide
  attest_order y _ j src signed h i ℓ hij _ _ := by
    obtain ⟨rfl, -⟩ := (trS₀_label j _ h.2).elim id fun h' => by
      rcases h' with ⟨-, h'⟩ | ⟨-, h'⟩ <;> cases h'
    omega
  own_payload y _ i X h _ _ a ha := by
    obtain ⟨rfl, h'⟩ := (trS₀_label i _ h.2).resolve_left (by simp) |>.resolve_left (by simp)
    cases h'
    rw [List.mem_singleton.mp ha, FGTrace.store, (trS₀_state y).2.2.1]
    exact List.mem_singleton_self _
  unforgeable y _ i a h _ := by
    obtain ⟨ℓ, hℓ, ha⟩ := h
    have ha₀ : a = a₀ := by
      rcases trS₀_label i ℓ hℓ.2 with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · cases ha
      · exact List.mem_singleton.mp ha
      · exact List.mem_singleton.mp ha
    subst ha₀
    refine ⟨0, ?_, g₀, rfl, rfl⟩
    rcases trS₀_label i ℓ hℓ.2 with ⟨rfl, rfl⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · cases ha
    · omega
    · omega

/-- `w₀`'s state at the proposal cut `2` of `Bs` is `stA`. -/
theorem trS₀_store_two : trS₀.store w₀ 2 = stA := by
  rw [FGTrace.store, (trS₀_state w₀).2.2.1]

/-- `w₀`'s state from cut `3` on (after `Bs` is accepted) is `stBs`. -/
theorem trS₀_store_three : trS₀.store w₀ 3 = stBs := by
  rw [FGTrace.store, (trS₀_state w₀).2.2.2 0]

/-- (a) `Bs` is `w₀`'s honest proposal at cut `2` on genesis: accepted at the start of slot `1`,
with `a₀`, the only pooled row, included. -/
theorem trS₀_proposal_Bs : HonestProposal P₀ Unit {w₀} trS₀ w₀ 2 Bs g₀ := by
  refine ⟨rfl, ⟨rfl, rfl⟩, rfl, rfl, ?_, rfl, ?_⟩ <;> rw [trS₀_store_two]
  · exact g₀_mem_stA
  · exact fun r hr _ _ => hr

/-- (a) At the proposal cut of `Bs`, `w₀`'s pool holds a progress quorum (`q = 1`) of
current-entry rows for genesis at cut `3`: `a₀`, of height `1` and root `0`. -/
theorem trS₀_quorum :
    P₀.fg.q ≤ (((trS₀.store w₀ 2).atts.filter fun x =>
      x.h = ((trS₀.store w₀ 3).σ g₀.root).h ∧ x.T = g₀.root).map FG.Att.val).toFinset.card := by
  rw [trS₀_store_two, trS₀_store_three]
  decide

/-- (a) The window condition of `Crossing` for `T = genesis`, `C = Bs` at cut `3` and `g = 1`
holds for every `r`: the only window is slot `1`, served by `Bs` (`trS₀_proposal_Bs`,
`trS₀_quorum`). -/
theorem trS₀_window (r : Nat) :
    ∀ w, g₀.slot < w → w + 1 - 1 ≤ Bs.slot →
      ∃ (Y Pr : NodeBlock P₀ Unit) (p : Fin P₀.n) (j : Nat),
        HonestProposal P₀ Unit {w₀} trS₀ p j Y Pr ∧ (trS₀.store w₀ 3).Anc Y Bs ∧ w ≤ Y.slot ∧
        Y.slot ≤ w + 1 - 1 ∧
        (g₀.slot + r ≤ Y.slot →
          P₀.fg.q ≤ (((trS₀.store p j).atts.filter fun x =>
            x.h = ((trS₀.store w₀ 3).σ g₀.root).h ∧ x.T = g₀.root).map
              FG.Att.val).toFinset.card) := by
  intro w hw hwC
  have hw1 : w = 1 := by
    change 0 < w at hw
    change w + 1 - 1 ≤ 1 at hwC
    omega
  subst hw1
  exact ⟨Bs, g₀, w₀, 2, trS₀_proposal_Bs, Relation.ReflTransGen.refl, le_rfl, le_rfl,
    fun _ => trS₀_quorum⟩

/-- `Bs` is held at cut `3`, and genesis is an entry block there that `Bs` extends. -/
theorem trS₀_premises :
    Bs ∈ (trS₀.store w₀ 3).tree ∧ IsEntry P₀ Unit (trS₀.store w₀ 3) g₀ ∧
      (trS₀.store w₀ 3).Anc g₀ Bs := by
  rw [trS₀_store_three]
  exact ⟨rfl, ⟨rfl, rfl⟩, Relation.ReflTransGen.single ⟨rfl, rfl, rfl⟩⟩

/-- At cut `3`, a held block whose height is greater than genesis's is `Bs` (the tree is
`{genesis, Bs}`). -/
theorem trS₀_leaves_height_eq_Bs (X : NodeBlock P₀ Unit) (hX : X ∈ (trS₀.store w₀ 3).tree)
    (hh : ((trS₀.store w₀ 3).σ g₀.root).h < ((trS₀.store w₀ 3).σ X.root).h) :
    X = Bs := by
  rcases trS₀_localRun.tree_subset w₀ rfl 3 hX with rfl | hXB
  · exact absurd hh (lt_irrefl _)
  · exact hXB

/-- (r) The `1 ≤ r` premise of `Crossing` is needed at `δ_t = 0`. On `trS₀` (an `FGLocalRun`)
at the honest `w₀` and cut `3`, with `C = Bs`, `T = genesis`, `g = 1` and `r = 0`, every other
premise holds (`C` held, `T` an entry block with `T ⪯ C`, `1 ≤ g`, the slot bound, and the window
condition for every `w`), `1 ≤ r` fails, and so does the conclusion: the bound
`T.slot + max(δ_t, r) + g − 1` is `0`, one slot short of `Bs`, the first block above height `1`. -/
theorem crossing_needs_one_le_r :
    FGLocalRun () {w₀} {g₀, Bs} trS₀ ∧ w₀ ∈ ({w₀} : Set (Fin P₀.n)) ∧
    Bs ∈ (trS₀.store w₀ 3).tree ∧ IsEntry P₀ Unit (trS₀.store w₀ 3) g₀ ∧
    (trS₀.store w₀ 3).Anc g₀ Bs ∧ 1 ≤ 1 ∧ ¬ 1 ≤ 0 ∧ g₀.slot + max P₀.δt 0 + 1 - 1 ≤ Bs.slot ∧
    (∀ w, g₀.slot < w → w + 1 - 1 ≤ Bs.slot →
      ∃ (Y Pr : NodeBlock P₀ Unit) (p : Fin P₀.n) (j : Nat),
        HonestProposal P₀ Unit {w₀} trS₀ p j Y Pr ∧ (trS₀.store w₀ 3).Anc Y Bs ∧ w ≤ Y.slot ∧
        Y.slot ≤ w + 1 - 1 ∧
        (g₀.slot + 0 ≤ Y.slot →
          P₀.fg.q ≤ (((trS₀.store p j).atts.filter fun x =>
            x.h = ((trS₀.store w₀ 3).σ g₀.root).h ∧ x.T = g₀.root).map FG.Att.val).toFinset.card)) ∧
    ¬ ∃ X ∈ (trS₀.store w₀ 3).tree, (trS₀.store w₀ 3).Anc g₀ X ∧ (trS₀.store w₀ 3).Anc X Bs ∧
      ((trS₀.store w₀ 3).σ g₀.root).h < ((trS₀.store w₀ 3).σ X.root).h ∧
      X.slot ≤ g₀.slot + max P₀.δt 0 + 1 - 1 := by
  obtain ⟨hC, hT, hTC⟩ := trS₀_premises
  refine ⟨trS₀_localRun, rfl, hC, hT, hTC, le_rfl, by decide, by decide, trS₀_window 0, ?_⟩
  rintro ⟨X, hX, -, -, hh, hs⟩
  obtain rfl := trS₀_leaves_height_eq_Bs X hX hh
  exact absurd hs (by decide)

/-- (a) The same instance with `r = 1`: every premise of `Crossing` holds, `crossing` gives its
conclusion (bound `0 + max 0 1 + 1 − 1 = 1`), and every witness is `Bs`, of slot `1`. -/
theorem crossing_one_le_r :
    FGLocalRun () {w₀} {g₀, Bs} trS₀ ∧ w₀ ∈ ({w₀} : Set (Fin P₀.n)) ∧
    Bs ∈ (trS₀.store w₀ 3).tree ∧ IsEntry P₀ Unit (trS₀.store w₀ 3) g₀ ∧
    (trS₀.store w₀ 3).Anc g₀ Bs ∧ 1 ≤ 1 ∧ 1 ≤ 1 ∧ g₀.slot + max P₀.δt 1 + 1 - 1 ≤ Bs.slot ∧
    (∀ w, g₀.slot < w → w + 1 - 1 ≤ Bs.slot →
      ∃ (Y Pr : NodeBlock P₀ Unit) (p : Fin P₀.n) (j : Nat),
        HonestProposal P₀ Unit {w₀} trS₀ p j Y Pr ∧ (trS₀.store w₀ 3).Anc Y Bs ∧ w ≤ Y.slot ∧
        Y.slot ≤ w + 1 - 1 ∧
        (g₀.slot + 1 ≤ Y.slot →
          P₀.fg.q ≤ (((trS₀.store p j).atts.filter fun x =>
            x.h = ((trS₀.store w₀ 3).σ g₀.root).h ∧ x.T = g₀.root).map FG.Att.val).toFinset.card)) ∧
    (∃ X ∈ (trS₀.store w₀ 3).tree, (trS₀.store w₀ 3).Anc g₀ X ∧ (trS₀.store w₀ 3).Anc X Bs ∧
      ((trS₀.store w₀ 3).σ g₀.root).h < ((trS₀.store w₀ 3).σ X.root).h ∧
      X.slot ≤ g₀.slot + max P₀.δt 1 + 1 - 1) ∧
    ∀ X ∈ (trS₀.store w₀ 3).tree,
      ((trS₀.store w₀ 3).σ g₀.root).h < ((trS₀.store w₀ 3).σ X.root).h → X = Bs ∧ X.slot = 1 := by
  obtain ⟨hC, hT, hTC⟩ := trS₀_premises
  have hb : g₀.slot + max P₀.δt 1 + 1 - 1 ≤ Bs.slot := by decide
  refine ⟨trS₀_localRun, rfl, hC, hT, hTC, le_rfl, le_rfl, hb, trS₀_window 1,
    crossing P₀ Unit () {w₀} {g₀, Bs} trS₀ trS₀_localRun w₀ rfl 3 Bs g₀ 1 1 hC hT hTC le_rfl
      le_rfl hb (trS₀_window 1), fun X hX hh => ?_⟩
  obtain rfl := trS₀_leaves_height_eq_Bs X hX hh
  exact ⟨rfl, rfl⟩

end Consensus.Goldilocks.Store.Test.DeltaZero

end
