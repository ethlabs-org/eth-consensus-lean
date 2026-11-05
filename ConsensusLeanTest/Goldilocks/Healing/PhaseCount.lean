module
public import ConsensusLeanTest.Goldilocks.FGStore.TimeoutEntry
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
@[expose] public section

/-! # Witness for HR.2 (b), (c), the phase count, with a phase change at a fixed frontier

`PhaseCount` (`Statements/Healing/Run`, HR.2) over an FG trace with an actual change of the
effective phase while the frontier stays fixed. The earlier witness
(`Goldilocks/Healing/Statements`, `idle_phaseAt`) is the idle trace, whose phase never changes, so
(b) held there only with equal ranks and (c) counted an empty set. Labelled by kind (CONTRIBUTING
"Statements").

**The trace `trP`** (`P₁`: `Δ = 1`, `δ_t = 2`, `q = 1`; one node `w₀`, honest; so
`f = 0 < 2q − n = 1`). Cuts `0`–`10` are those of the timeout-entry trace `trT`
(`Goldilocks/FGStore/TimeoutEntry`): `w₀` justifies genesis with `Bs`, justifies `Bs` with `Bf`
(frontier `3`, `(h_j, J) = (2, Bs)`), accepts its fork proposal `Bk` on genesis (state height `2`),
signs the timeout `aK` at `(2, Bk)` and the target row `aF` for `Bf`. Then, instead of `trT`'s `Bc`:
* cut `11`, time `5`: accept the own proposal `Bt` (root `7`, slot `5`, on `Bk`, payload `[aK]`):
  `aK` is a progress quorum for `Bk`'s entry and `5 ≥ 3 + δ_t`, so `σ[Bt]` times out into height
  `3` (entry `Bt`); `Bt` does not extend `Bs`.

The effective phase at frontier `3` is **top `Bs`** before cut `11` and **contest `Bs`** after it.

* (a) `trP_localRun`, `phaseCount_premises`: `trP` is an `FGLocalRun` with `f < 2q − n`.
* (a) `phase_top_11`, `phase_contest_12`: the two phases.
* (a) `phaseCount_b_witness`: (b) at `i = 11`, `j = 12`, `m = 3`: the rank rises `1 → 2` and the
  top `J = Bs` is kept; `phaseCount_c_witness`: (c)'s counted set at `m = 3` is nonempty (it holds
  cut `11`).
* (r) `phaseCount_b_needs_fixed_frontier`: on `trT`, across the frontier rise `3 → 4` (cut `11`,
  `Bc` timing out into height `4` with no justification at `3`), the phase goes from top `Bs` to
  gap, so the rank falls: (b)'s monotonicity is only for a fixed frontier.
* `phaseCount_applies`: `PhaseCount`, assumed, applies to `trP` with these premises, and gives
  (b) and (c) at `m = 3`. -/

namespace Consensus.Goldilocks.Store.Test

open Consensus.Goldilocks.Healing

/-! ## The block `Bt` -/

/-- The fork-side proposal of slot `5` on `Bk` carrying the timeout `aK`: root `7`. -/
def Bt : NodeBlock P₁ Unit := ⟨7, some 3, 5, w₀, 0, [aK], ()⟩

/-- The chain state of `Bt`: `aK` sets the finality bit of `(1, genesis)` and the progress bit of
`Bk`'s entry; the finality step finalizes genesis at `1` and prunes; no target quorum, so a
timeout (`3 + δ_t ≤ 5`) into height `3` with entry `Bt`. -/
def σBt : FG.ChainState P₁.n where
  L := 7
  s := 5
  h := 3
  Th := 7
  ThSlot := 5
  target := ∅
  prog := ∅
  pending := []
  fin := Function.update (Function.update (fun _ => ∅) 1 ∅) 1 (insert w₀ ∅)
  J := 0
  hj := 1
  F := 0
  hF := 1

theorem stateTransition_Bt : P₁.fg.stateTransition (stKb.σ 3) Bt.fgView = some σBt := rfl

/-- The FG state after accepting `Bt` on `stKb`. -/
def stT : Store P₁ Unit :=
  { stKb with
    blocks := Function.update stKb.blocks 7 (some Bt)
    σ := Function.update stKb.σ 7 σBt }

theorem mem_tree_stT {X : NodeBlock P₁ Unit} (h : X ∈ stT.tree) :
    X = g₁ ∨ X = Bs ∨ X = Bf ∨ X = Bk ∨ X = Bt := by
  change Function.update stK.blocks 7 (some Bt) X.root = some X at h
  rcases eq_or_of_update h with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact (mem_tree_stK h).imp_right (Or.imp_right (Or.imp_right Or.inl))

open Classical in
/-- The finality update of `Bt` changes nothing: `(1, genesis)` is lex-below the cache
`(2, Bs)`, and `σ[Bt].F` is genesis, the current `Σ.F`. -/
theorem updateFinality_stT : stT.updateFinality σBt = stT := by
  unfold updateFinality
  extract_lets st₁ st₂
  have h2 : st₂ = stT := by
    change (match st₁.blocks 0 with
      | some X => if st₁.Anc st₁.F X ∧ LexLt (st₁.hj, st₁.J.root) (1, 0) then
          { st₁ with J := X, hj := 1 } else st₁
      | none => st₁) = stT
    rw [show st₁.blocks 0 = some g₁ from rfl]
    dsimp only
    rw [ite_eq_right fun h => by
      have h' : LexLt (2, 1) (1, 0) := h.2
      simp [LexLt] at h']
    rfl
  rw [h2, show stT.blocks σBt.F = some g₁ from rfl]
  dsimp only
  rw [ite_eq_right (fun h => h.2.1 rfl)]

/-- `stKb` accepts `Bt`, with post-state `stT` (`aK` is pooled already). -/
theorem onBlock_stKb_Bt : stKb.onBlock Bt = some stT := by
  have hanc : Goldilocks.Anc (insert Bt stKb.tree) stKb.F Bt := by
    have hk : Bk ∈ insert Bt stKb.tree := Or.inr (show stKb.blocks 3 = some Bk from rfl)
    have hg : g₁ ∈ insert Bt stKb.tree := Or.inr (show stKb.blocks 0 = some g₁ from rfl)
    exact (Relation.ReflTransGen.single ⟨hg, hk, rfl⟩).tail ⟨hk, Or.inl rfl, rfl⟩
  have hneg : ¬ ((stKb.blocks Bt.root).isSome = true ∨ (stKb.blocks 3).isNone = true ∨
      ¬ Goldilocks.Anc (insert Bt stKb.tree) stKb.F Bt) := by
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
  · next h => rw [stateTransition_Bt] at h; cases h
  next σ' h =>
  rw [stateTransition_Bt] at h; cases h
  change some ((updateFinality stT σBt).addAtts [aK]) = some stT
  rw [updateFinality_stT]
  rfl

/-! ## The trace `trP` -/

/-- `trT`'s cuts `0`–`10`, then `w₀` accepts its own proposal `Bt` at time `5`. -/
def trP : FGTrace P₁ Unit where
  init _ := (Store.init (), FG.Record.empty)
  node _ := w₀
  time i := if i < 2 then 0 else if i < 5 then 1 else if i < 6 then 2 else if i < 9 then 3
    else if i < 11 then 4 else 5
  event i := if i < 2 then 0 else if i < 5 then 1 else if i < 6 then 2 else if i < 9 then 3
    else if i < 11 then 4 else 5
  pos
    | 1 => 1
    | 3 => 1
    | 4 => 2
    | 7 => 1
    | 8 => 2
    | 10 => 1
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
    | 11 => some (.block Bt true)
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
    | _ => (stT, ΛF)
  awake _ _ := True

theorem trP_agree (i : Nat) (hi : i ≤ 10) :
    trP.label i = trT.label i ∧ trP.post i = trT.post i := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    first | exact ⟨rfl, rfl⟩ | omega

theorem trP_time (i : Nat) (hi : i < 11) : trP.time i = trT.time i := by
  simp only [trP, trT]
  split_ifs <;> rfl

theorem trP_label (i : Nat) (ℓ : FGLabel P₁ Unit) (h : trP.label i = some ℓ) :
    (i ≤ 10 ∧ trT.label i = some ℓ) ∨ (i = 11 ∧ ℓ = .block Bt true) := by
  by_cases hi : i ≤ 10
  · exact Or.inl ⟨hi, (trP_agree i hi).1 ▸ h⟩
  · obtain rfl | h12 : i = 11 ∨ 12 ≤ i := by omega
    · exact Or.inr ⟨rfl, (Option.some.inj h).symm⟩
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h12
      simp [trP] at h

theorem trP_state_succ (i : Nat) (hi : i ≤ 11) : trP.state w₀ (i + 1) = trP.post i := by
  have h : trP.node i = w₀ ∧ trP.label i ≠ none := by
    refine ⟨rfl, ?_⟩
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
      first | omega | simp [trP]
  rw [Trace.state, ite_eq_left h]

theorem trP_state_eq (i : Nat) (hi : i ≤ 11) : trP.state w₀ i = trT.state w₀ i := by
  rcases i with _ | i
  · rfl
  · rw [trP_state_succ i (by omega), trT_state_succ i (by omega)]
    exact (trP_agree i (by omega)).2

theorem trP_state_late (i : Nat) : trP.state w₀ (i + 12) = (stT, ΛF) := by
  induction i with
  | zero => exact trP_state_succ 11 le_rfl
  | succ i ih => rw [Trace.state, ite_eq_right (by simp [trP])]; exact ih

/-- The FG states of `w₀` before cuts `11` and `12` of `trP`. -/
theorem trP_store : trP.store w₀ 11 = stKb ∧ trP.store w₀ 12 = stT :=
  ⟨(congrArg Prod.fst (trP_state_eq 11 le_rfl)).trans
      (congrArg Prod.fst trT_state.2.2.2.2.2.2.2.2.2.2.2.1),
    congrArg Prod.fst (trP_state_late 0)⟩

/-- `U` of `trP`: `trT`'s blocks and `Bt`. -/
abbrev UP : Set (NodeBlock P₁ Unit) := {g₁, Bs, Bf, Bk, Bc, Bx, Bt}

theorem trP_coherent : Coherent UP := by
  refine ⟨?_, ?_⟩
  · rintro X (rfl | rfl | rfl | rfl | rfl | rfl | rfl) Y (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      h <;> first | rfl | exact absurd h (by decide)
  · rintro X (rfl | rfl | rfl | rfl | rfl | rfl | rfl) Y (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      h <;> first | decide | exact absurd h (by decide)

theorem trP_exec (i : Nat) (ℓ : FGLabel P₁ Unit) (h : trP.label i = some ℓ) :
    FGLabel.Step (trP.node i) (trP.state (trP.node i) i) ℓ (trP.post i) := by
  rcases trP_label i ℓ h with ⟨hi, h'⟩ | ⟨rfl, rfl⟩
  · change FGLabel.Step w₀ (trP.state w₀ i) ℓ (trP.post i)
    rw [trP_state_eq i (by omega), (trP_agree i hi).2]
    exact trT_exec i ℓ h'
  · change FGLabel.Step w₀ (trP.state w₀ 11) _ (stT, ΛF)
    rw [trP_state_eq 11 le_rfl, trT_state.2.2.2.2.2.2.2.2.2.2.2.1]
    exact Or.inl ⟨rfl, onBlock_stKb_Bt, rfl⟩

theorem trP_tree_subset (y : Fin P₁.n) (i : Nat) : (trP.store y i).tree ⊆ UP := by
  intro X hX
  obtain rfl := eq_w₀ y
  by_cases hi : i ≤ 11
  · rw [FGTrace.store, trP_state_eq i hi] at hX
    exact (trT_tree_subset w₀ i hX).imp_right (Or.imp_right (Or.imp_right (Or.imp_right
      (Or.imp_right Or.inl))))
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (show 12 ≤ i by omega)
    rw [FGTrace.store, trP_state_late] at hX
    rcases mem_tree_stT hX with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

theorem trP_own_first (y : Fin P₁.n) (i : Nat) (B : NodeBlock P₁ Unit)
    (h : trP.CallAt y i (.block B true)) (k : Nat) (hk : k < i) : trP.time k < trP.time i := by
  rcases trP_label i _ h.2 with ⟨hi, h'⟩ | ⟨rfl, -⟩
  · rw [trP_time k (by omega), trP_time i (by omega)]
    exact trT_own_first y i B ⟨h.1, h'⟩ k hk
  · change trP.time k < 5
    simp only [trP]
    split_ifs <;> decide

theorem trP_attest_order (y : Fin P₁.n) (j : Nat) (src : NodeBlock P₁ Unit)
    (signed : Option (FG.Att P₁.n)) (h : trP.CallAt y j (.attest src signed)) (i : Nat)
    (ℓ : FGLabel P₁ Unit) (hij : i < j) (hi : trP.CallAt y i ℓ) (ht : trP.time i = trP.time j) :
    ∃ B acc, ℓ = .block B acc ∧ B.proposer = y ∧ P₁.slotTime B.slot = trP.time j := by
  rcases trP_label j _ h.2 with ⟨hj, h'⟩ | ⟨rfl, h'⟩
  · rw [trP_time i (by omega), trP_time j (by omega)] at ht
    rw [trP_time j (by omega)]
    exact trT_attest_order y j src signed ⟨h.1, h'⟩ i ℓ hij
      ⟨hi.1, (trP_agree i (by omega)).1 ▸ hi.2⟩ ht
  · cases h'

theorem trP_own_payload (y : Fin P₁.n) (i : Nat) (X : NodeBlock P₁ Unit)
    (h : trP.CallAt y i (.block X true)) (a : FG.Att P₁.n) (ha : a ∈ X.fgPayload) :
    a ∈ (trP.store y i).atts := by
  obtain rfl := eq_w₀ y
  rcases trP_label i _ h.2 with ⟨hi, h'⟩ | ⟨rfl, h'⟩
  · rw [FGTrace.store, trP_state_eq i (by omega)]
    exact trT_own_payload w₀ i X ⟨rfl, h'⟩ a ha
  · cases h'
    rw [List.mem_singleton.mp ha, trP_store.1]
    decide

theorem trP_unforgeable (y : Fin P₁.n) (i : Nat) (a : FG.Att P₁.n) (h : trP.ProcessAt y i a) :
    ∃ j < i, trP.SignAt a.val j a := by
  obtain ⟨ℓ, hℓ, ha⟩ := h
  rcases trP_label i ℓ hℓ.2 with ⟨hi, h'⟩ | ⟨rfl, rfl⟩
  · obtain ⟨j, hj, src, hs⟩ := trT_unforgeable y i a ⟨ℓ, ⟨hℓ.1, h'⟩, ha⟩
    exact ⟨j, hj, src, hs.1, (trP_agree j (by omega)).1.trans hs.2⟩
  · rw [List.mem_singleton.mp ha]; exact ⟨7, by omega, Bk, rfl, rfl⟩

/-- (a) `trP` is an `FGLocalRun` for the honest set `{w₀}` inside `UP`. -/
theorem trP_localRun : FGLocalRun () {w₀} UP trP where
  coherent := trP_coherent
  init _ _ := rfl
  exec i ℓ h _ := trP_exec i ℓ h
  tree_subset y _ i := trP_tree_subset y i
  time_nonneg i := by simp only [trP]; split_ifs <;> decide
  time_mono i j hij := by simp only [trP]; split_ifs <;> first | decide | omega
  attest_public _ _ _ _ _ _ := one_dvd _
  own_first y _ i X h _ _ k hk _ _ := trP_own_first y i X h k hk
  attest_order y _ j src signed h i ℓ hij hi ht := trP_attest_order y j src signed h i ℓ hij hi ht
  own_payload y _ i X h _ _ a ha := trP_own_payload y i X h a ha
  unforgeable y _ i a h _ := trP_unforgeable y i a h

/-- (a) The premises of `PhaseCount` on `trP`: an `FGLocalRun` with `f = 0 < 2q − n = 1`. -/
theorem phaseCount_premises :
    FGLocalRun () {w₀} UP trP ∧ ({w₀} : Set (Fin P₁.n))ᶜ.ncard < 2 * P₁.fg.q - P₁.n := by
  refine ⟨trP_localRun, ?_⟩
  rw [show ({w₀} : Set (Fin P₁.n))ᶜ = ∅ from
    Set.eq_empty_of_forall_notMem fun y hy => hy (eq_w₀ y), Set.ncard_empty]
  decide

/-! ## The phases at frontier `3` -/

/-- Ancestry inside a tree whose roots name distinct blocks of `UP`: every ancestor of `Bt` is
`Bt`, `Bk` or genesis. -/
theorem anc_Bt_cases {T : Set (NodeBlock P₁ Unit)} (hT : T ⊆ UP) {X Y : NodeBlock P₁ Unit}
    (h : Goldilocks.Anc T X Y) (hY : Y = Bt ∨ Y = Bk ∨ Y = g₁) : X = Bt ∨ X = Bk ∨ X = g₁ := by
  induction h with
  | refl => exact hY
  | @tail Z W _ e ih =>
    apply ih
    obtain ⟨hZ, -, hp⟩ := e
    have hZU := hT hZ
    rcases hY with rfl | rfl | rfl
    · exact Or.inr (Or.inl (trP_coherent.1 hZU (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        (Option.some.inj hp).symm))
    · exact Or.inr (Or.inr (trP_coherent.1 hZU (Or.inl rfl) (Option.some.inj hp).symm))
    · cases hp

/-- The state heights of the blocks of `stKb`: genesis `1`, `Bs` `2`, `Bf` `3`, `Bk` `2`. -/
theorem stKb_heights {X : NodeBlock P₁ Unit} (hX : X ∈ stKb.tree) (h : (stKb.σ X.root).h = 3) :
    X = Bf := by
  rcases mem_tree_stK hX with rfl | rfl | rfl | rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rfl
  · exact absurd h (by decide)

/-- `Bf` extends `Bs` in `stKb`. -/
theorem anc_Bs_Bf_stKb : stKb.Anc Bs Bf :=
  Relation.ReflTransGen.single ⟨show stKb.blocks 1 = some Bs from rfl,
    show stKb.blocks 2 = some Bf from rfl, rfl⟩

/-- (a) Before cut `11` of `trP`, the effective phase is top `Bs` at frontier `3`. -/
theorem phase_top_11 : PhaseAt trP {w₀} 11 3 (.top Bs) := by
  have hst := trP_store.1
  refine ⟨⟨⟨w₀, rfl, by rw [hst]; rfl⟩, fun y hy => by rw [hy, hst]; decide⟩,
    ⟨w₀, rfl, by rw [hst]; exact (show stKb.blocks 1 = some Bs from rfl), Bf,
      by rw [hst]; exact (show stKb.blocks 2 = some Bf from rfl), by rw [hst]; rfl,
      by rw [hst]; rfl⟩, ?_⟩
  rintro ⟨y, hy, B, hB, hh, hn⟩
  rw [hy, hst] at *
  rw [stKb_heights hB hh] at hn
  exact hn anc_Bs_Bf_stKb

/-- (a) After cut `11` (before cut `12`), the effective phase is contest `Bs` at frontier `3`:
`Bt` has state height `3` and does not extend `Bs`. -/
theorem phase_contest_12 : PhaseAt trP {w₀} 12 3 (.contest Bs) := by
  have hst := trP_store.2
  refine ⟨⟨⟨w₀, rfl, by rw [hst]; rfl⟩, fun y hy => by rw [hy, hst]; decide⟩,
    ⟨w₀, rfl, by rw [hst]; exact (show stT.blocks 1 = some Bs from rfl), Bf,
      by rw [hst]; exact (show stT.blocks 2 = some Bf from rfl), by rw [hst]; rfl,
      by rw [hst]; rfl⟩,
    ⟨w₀, rfl, Bt, by rw [hst]; exact (show stT.blocks 7 = some Bt from rfl),
      by rw [hst]; rfl, ?_⟩⟩
  rw [hst]
  intro h
  have hsub : stT.tree ⊆ UP := hst ▸ trP_tree_subset w₀ 12
  rcases anc_Bt_cases hsub h (Or.inl rfl) with h | h | h <;> exact absurd (congrArg Block.root h)
    (by decide)

/-- (a) **HR.2 (b) witness.** At the fixed frontier `3`, from cut `11` to cut `12`, the phase
moves forward from top `Bs` (rank `1`) to contest `Bs` (rank `2`), keeping the top `J = Bs`. -/
theorem phaseCount_b_witness :
    PhaseAt trP {w₀} 11 3 (.top Bs) ∧ PhaseAt trP {w₀} 12 3 (.contest Bs) ∧
      (PhaseCase.top Bs).rank < (PhaseCase.contest Bs).rank ∧
      ∀ J, (PhaseCase.top Bs).topJ = some J → (PhaseCase.contest Bs).topJ = some J :=
  ⟨phase_top_11, phase_contest_12, by decide, fun _ h => h⟩

/-- (a) **HR.2 (c) witness.** The counted set of phase changes at frontier `3` holds cut `11`. -/
theorem phaseCount_c_witness :
    11 ∈ {i | ∃ c c', PhaseAt trP {w₀} i 3 c ∧ PhaseAt trP {w₀} (i + 1) 3 c' ∧ c ≠ c'} :=
  ⟨.top Bs, .contest Bs, phase_top_11, phase_contest_12, fun h => by cases h⟩

/-! ## Rejection: the frontier must stay fixed -/

/-- No block of `stC` has a state justifying height `3`. -/
theorem stC_no_hj3 {X : NodeBlock P₁ Unit} (hX : X ∈ stC.tree) : (stC.σ X.root).hj ≠ 3 := by
  rcases mem_tree_stC hX with rfl | rfl | rfl | rfl | rfl <;> decide

/-- (r) **(b) needs a fixed frontier.** On `trT`, across cut `11` (`Bc` times out into height
`4`; nothing is justified at `3`), the phase goes from top `Bs` at `3` to gap at `4`: the rank
falls from `1` to `0`. -/
theorem phaseCount_b_needs_fixed_frontier :
    PhaseAt trT {w₀} 11 3 (.top Bs) ∧ PhaseAt trT {w₀} 12 4 .gap ∧
      ¬ (PhaseCase.top Bs).rank ≤ (PhaseCase.gap : PhaseCase (NodeBlock P₁ Unit)).rank := by
  have h11 : trT.store w₀ 11 = stKb := congrArg Prod.fst trT_state.2.2.2.2.2.2.2.2.2.2.2.1
  have h12 : trT.store w₀ 12 = stC := congrArg Prod.fst trT_state.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨⟨⟨⟨w₀, rfl, by rw [h11]; rfl⟩, fun y hy => by rw [hy, h11]; decide⟩,
      ⟨w₀, rfl, by rw [h11]; exact (show stKb.blocks 1 = some Bs from rfl), Bf,
        by rw [h11]; exact (show stKb.blocks 2 = some Bf from rfl), by rw [h11]; rfl,
        by rw [h11]; rfl⟩, ?_⟩,
    ⟨⟨⟨w₀, rfl, by rw [h12]; rfl⟩, fun y hy => by rw [hy, h12]; decide⟩, ?_⟩, by decide⟩
  · rintro ⟨y, hy, B, hB, hh, hn⟩
    rw [hy, h11] at *
    rw [stKb_heights hB hh] at hn
    exact hn anc_Bs_Bf_stKb
  · rintro J ⟨y, hy, -, B, hB, hj, -⟩
    rw [hy, h12] at hB hj
    exact stC_no_hj3 hB hj

/-! ## The statement reaches the witness -/

/-- `PhaseCount`, assumed, applies to `trP` with the premises above: (b) at cuts `11`, `12` and
(c) at frontier `3` (whose counted set is nonempty by `phaseCount_c_witness`). -/
theorem phaseCount_applies (h : PhaseCount P₁ Unit) :
    ((PhaseCase.top Bs).rank ≤ (PhaseCase.contest Bs).rank ∧
      ∀ J, (PhaseCase.top Bs).topJ = some J → (PhaseCase.contest Bs).topJ = some J) ∧
    {i | ∃ c c', PhaseAt trP {w₀} i 3 c ∧ PhaseAt trP {w₀} (i + 1) 3 c' ∧ c ≠ c'}.encard ≤ 2 :=
  ⟨(h () {w₀} UP trP trP_localRun phaseCount_premises.2).2.1 3 11 12 _ _ (by decide)
      phase_top_11 phase_contest_12,
    (h () {w₀} UP trP trP_localRun phaseCount_premises.2).2.2 3⟩

end Consensus.Goldilocks.Store.Test
