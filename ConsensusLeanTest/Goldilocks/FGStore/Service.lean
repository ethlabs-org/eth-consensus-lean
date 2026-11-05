module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGStore.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service
public import ConsensusLeanTest.Goldilocks.FGStore.Statements
@[expose] public section

/-! # Witnesses for the Goldilocks FGStore statements (part 3, the FG service lemmas)

On `Statements/FGStore/Service`, labelled by kind (CONTRIBUTING "Statements"):

* (a) `cacheAcceptance_holds`: G1.9 (a) holds at every parameter and AC payload type (viability
  after the `h_max` step carries over to the state after the justification step, which the
  finalization step of `update_finality` reads).
* (a) `trS_localRun`, `trS_goodWindow`: an n = 1 FG trace (`P₁`: `Δ = 1`, `δ_t = 2`, so `q = 1`)
  that is an `FGLocalRun` and has a good window for the genesis entry, whose previous height is not
  justified (`a = 0`, `c_F = 1`, `k_F = 0`): `w₀` signs the target row `a₀` for genesis at time `0`,
  pools it, and proposes `Bs` of slot `1` carrying it at time `1`.
* (a) `trS_previousHeightNotJustifiedEntry_first`: on that trace the first conclusion of G1.7 holds
  with `X = Bs` (a sanity check of the reading).
* (r) `trE_not_goodWindow`: the same run with a proposal `Be` that omits the pooled row is an
  `FGLocalRun` (`trE_localRun`) but serves no good window (the inclusion rule P5). -/

namespace Consensus.Goldilocks.Store.Test

/-- (a) G1.9 (a), cache acceptance, holds (`cache_acceptance`). -/
theorem cacheAcceptance_holds (P : Params) (ACP : Type) : CacheAcceptance P ACP :=
  cache_acceptance P ACP

/-- The only validator of `P₁`. -/
def w₀ : Fin P₁.n := ⟨0, Nat.one_pos⟩

/-- Every validator of `P₁` is `w₀`. -/
theorem eq_w₀ (y : Fin P₁.n) : y = w₀ := Fin.ext (Nat.lt_one_iff.mp y.isLt)

/-- Genesis of `P₁` (root `0`, slot `0`). -/
abbrev g₁ : NodeBlock P₁ Unit := P₁.genesisBlock ()

/-- `w₀`'s attestation with source genesis: the target vote for genesis at height `1`, no
finality pair. -/
def a₀ : FG.Att P₁.n := ⟨w₀, 1, 0, false, none⟩

/-- `w₀`'s record after signing `a₀`. -/
def Λ₀ : FG.Record := FG.Record.empty.recordAtt a₀

/-- On the initial state and the empty record, `fg_attest` with source genesis signs `a₀`. -/
theorem attest_init : (Store.init (P := P₁) ()).attest FG.Record.empty w₀ g₁ = some (a₀, Λ₀) :=
  rfl

/-- The initial state with `a₀` pooled. -/
def stA : Store P₁ Unit := { Store.init () with atts := [a₀] }

/-- Processing `a₀` on the initial state gives `stA`. -/
theorem onAttestation_init : (Store.init (P := P₁) ()).onAttestation a₀ = stA := rfl

/-- Genesis is held in `stA`. -/
theorem g₁_mem_stA : g₁ ∈ stA.tree := rfl

/-- `w₀`'s proposal of slot `1` on genesis carrying `a₀`: root `1`. -/
def Bs : NodeBlock P₁ Unit := ⟨1, some 0, 1, w₀, 0, [a₀], ()⟩

/-- The chain state of `Bs`: `a₀` is a target quorum (`q = 1`) for genesis at the height whose
previous height is not justified `1`, so `Bs` justifies genesis (`J = 0`, `h_j = 1`, pending `[(1,
0)]`) and enters height `2` with entry `Bs`. -/
def σBs : FG.ChainState P₁.n where
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

/-- `state_transition` of `Bs` from the genesis state gives `σBs`. -/
theorem stateTransition_Bs : P₁.fg.stateTransition (stA.σ 0) Bs.fgView = some σBs := rfl

/-- `stA` with `Bs` and its chain state added (before the finality update). -/
def stBs₀ : Store P₁ Unit :=
  { stA with
    blocks := Function.update stA.blocks 1 (some Bs)
    σ := Function.update stA.σ 1 σBs }

/-- The FG state after accepting `Bs` on `stA`: `Bs` and `σBs` added, `h_max = 2`, and the
justification cache at genesis with height `1`; `F` stays at genesis. -/
def stBs : Store P₁ Unit := { stBs₀ with hj := 1, hmax := 2 }


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
    rw [show st₁.blocks 0 = some g₁ from rfl]
    dsimp only
    rw [ite_eq_left ⟨Relation.ReflTransGen.refl, Or.inl Nat.one_pos⟩]
    rfl
  rw [h2, show stBs.blocks σBs.F = some g₁ from rfl]
  dsimp only
  rw [ite_eq_right (fun h => h.2.1 rfl)]

/-- `stA` accepts `Bs`, with post-state `stBs` (`a₀` is pooled already). -/
theorem onBlock_stA_Bs : stA.onBlock Bs = some stBs := by
  have hanc : Goldilocks.Anc (insert Bs stA.tree) stA.F Bs :=
    Relation.ReflTransGen.single ⟨Or.inr g₁_mem_stA, Or.inl rfl, rfl⟩
  have hneg : ¬ ((stA.blocks Bs.root).isSome = true ∨ (stA.blocks 0).isNone = true ∨
      ¬ Goldilocks.Anc (insert Bs stA.tree) stA.F Bs) := by
    rintro (h | h | h)
    · simp [stA, Store.init, Bs, P₁] at h
    · simp [stA, Store.init, P₁] at h
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

/-- The n = 1 trace with proposal `B`: `w₀` attests with source genesis at time `0` and signs
`a₀` (cut `0`), processes `a₀` (cut `1`, same tick), and accepts its own proposal `B` of slot
`1` at time `1` with post-state `st` (cut `2`); then it stutters. -/
def trOf (B : NodeBlock P₁ Unit) (st : Store P₁ Unit) : FGTrace P₁ Unit where
  init _ := (Store.init (), FG.Record.empty)
  node _ := w₀
  time i := if i < 2 then 0 else 1
  event i := if i < 2 then 0 else 1
  pos i := if i = 1 then 1 else 0
  label
    | 0 => some (.attest g₁ (some a₀))
    | 1 => some (.attestation a₀)
    | 2 => some (.block B true)
    | _ => none
  post
    | 0 => (Store.init (), Λ₀)
    | 1 => (stA, Λ₀)
    | _ => (st, Λ₀)
  awake _ _ := True

/-- The states of `trOf B st`: the initial one, then after `a₀` is signed, after it is
processed, and after `B` is accepted. -/
theorem trOf_state (B : NodeBlock P₁ Unit) (st : Store P₁ Unit) (y : Fin P₁.n) :
    (trOf B st).state y 0 = (Store.init (), FG.Record.empty) ∧
      (trOf B st).state y 1 = (Store.init (), Λ₀) ∧ (trOf B st).state y 2 = (stA, Λ₀) ∧
      ∀ i, (trOf B st).state y (i + 3) = (st, Λ₀) := by
  obtain rfl := eq_w₀ y
  refine ⟨rfl, by simp [Trace.state, trOf], by simp [Trace.state, trOf], fun i => ?_⟩
  induction i with
  | zero => simp [Trace.state, trOf]
  | succ i ih => rw [Trace.state, ite_eq_right (by simp [trOf])]; exact ih

/-- The trees of `trOf B st`: the initial one before `B` is accepted, `st`'s after. -/
theorem trOf_blocks (B : NodeBlock P₁ Unit) (st : Store P₁ Unit) (y : Fin P₁.n) (i : Nat) :
    ((trOf B st).store y i).blocks = (Store.init ()).blocks ∨
      ((trOf B st).store y i).blocks = st.blocks := by
  obtain ⟨h0, h1, h2, h3⟩ := trOf_state B st y
  rcases i with _ | _ | _ | i
  · exact Or.inl (by rw [FGTrace.store, h0])
  · exact Or.inl (by rw [FGTrace.store, h1])
  · exact Or.inl (by rw [FGTrace.store, h2]; rfl)
  · exact Or.inr (by rw [FGTrace.store, h3])

/-- The labelled cuts of `trOf B st`. -/
theorem trOf_label (B : NodeBlock P₁ Unit) (st : Store P₁ Unit) (i : Nat)
    (ℓ : FGLabel P₁ Unit) (h : (trOf B st).label i = some ℓ) :
    (i = 0 ∧ ℓ = .attest g₁ (some a₀)) ∨ (i = 1 ∧ ℓ = .attestation a₀) ∨
      (i = 2 ∧ ℓ = .block B true) := by
  rcases i with _ | _ | _ | i <;> simp [trOf] at h <;> simp [h]

/-- (a) `trOf B st` is an `FGLocalRun` for the honest set `{w₀}` inside `{genesis, B}` when `B`
is `w₀`'s proposal of slot `1` on genesis (root `1`) carrying at most `a₀`, which `stA` accepts
with post-state `st`, adding only `B` to the tree. -/
theorem trOf_localRun (B : NodeBlock P₁ Unit) (st : Store P₁ Unit) (hr : B.root = 1)
    (hp : B.parent = some 0) (hs : B.slot = 1) (hpr : B.proposer = w₀)
    (hpay : ∀ a ∈ B.fgPayload, a = a₀) (hon : stA.onBlock B = some st)
    (hbl : st.blocks = Function.update stA.blocks 1 (some B)) :
    FGLocalRun () {w₀} {g₁, B} (trOf B st) where
  coherent := by
    refine ⟨?_, ?_⟩
    · rintro X (rfl | rfl) Y (rfl | rfl) h <;> first | rfl | simp_all [Params.genesisBlock, P₁]
    · rintro X (rfl | rfl) Y (rfl | rfl) h <;> simp_all [Params.genesisBlock, P₁]
  init _ _ := rfl
  exec i ℓ h _ := by
    obtain ⟨h0, h1, h2, -⟩ := trOf_state B st w₀
    rcases trOf_label B st i ℓ h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · change FGLabel.Step w₀ ((trOf B st).state w₀ 0) _ (Store.init (), Λ₀)
      rw [h0]
      exact ⟨rfl, by rw [attest_init]; exact ⟨rfl, rfl⟩⟩
    · change FGLabel.Step w₀ ((trOf B st).state w₀ 1) _ (stA, Λ₀)
      rw [h1]
      rfl
    · change FGLabel.Step w₀ ((trOf B st).state w₀ 2) _ (st, Λ₀)
      rw [h2]
      exact Or.inl ⟨rfl, hon, rfl⟩
  tree_subset y _ i := by
    intro X hX
    change ((trOf B st).store y i).blocks X.root = some X at hX
    have hg : ∀ r, (Store.init (P := P₁) ()).blocks r = some X → X = g₁ := by
      intro r hr
      simp only [Store.init] at hr
      split at hr
      · exact (Option.some_inj.mp hr).symm
      · cases hr
    rcases trOf_blocks B st y i with h | h <;> rw [h] at hX
    · exact Or.inl (hg _ hX)
    · rw [hbl] at hX
      by_cases h1 : X.root = 1
      · rw [h1, Function.update_self, Option.some.injEq] at hX
        exact Or.inr hX.symm
      · rw [Function.update_of_ne h1] at hX
        exact Or.inl (hg _ hX)
  time_nonneg i := by simp only [trOf]; split <;> decide
  time_mono i j hij := by simp only [trOf]; split <;> split <;> first | decide | omega
  attest_public _ _ _ _ _ _ := one_dvd _
  own_first y _ i X h _ _ k hk ℓ _ := by
    obtain ⟨rfl, -⟩ := (trOf_label B st i _ h.2).resolve_left (by simp)
      |>.resolve_left (by simp)
    simp only [trOf]
    rw [ite_eq_left hk]
    decide
  attest_order y _ j src signed h i ℓ hij _ _ := by
    obtain ⟨rfl, -⟩ := (trOf_label B st j _ h.2).elim id fun h' => by
      rcases h' with ⟨-, h'⟩ | ⟨-, h'⟩ <;> cases h'
    omega
  own_payload y _ i X h _ _ a ha := by
    obtain ⟨rfl, h'⟩ := (trOf_label B st i _ h.2).resolve_left (by simp)
      |>.resolve_left (by simp)
    cases h'
    rw [hpay a ha, FGTrace.store, (trOf_state B st y).2.2.1]
    exact List.mem_singleton_self _
  unforgeable y _ i a h _ := by
    obtain ⟨ℓ, hℓ, ha⟩ := h
    have ha₀ : a = a₀ := by
      rcases trOf_label B st i ℓ hℓ.2 with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · cases ha
      · exact List.mem_singleton.mp ha
      · exact hpay a ha
    subst ha₀
    refine ⟨0, ?_, g₁, rfl, rfl⟩
    rcases trOf_label B st i ℓ hℓ.2 with ⟨rfl, rfl⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · cases ha
    · omega
    · omega

/-- The good-window trace: `w₀` signs and pools `a₀`, then proposes `Bs` carrying it. -/
abbrev trS : FGTrace P₁ Unit := trOf Bs stBs

/-- (a) The good-window trace is an `FGLocalRun` for `{w₀}` inside `{genesis, Bs}`. -/
theorem trS_localRun : FGLocalRun () {w₀} {g₁, Bs} trS :=
  trOf_localRun Bs stBs rfl rfl rfl rfl (fun _ ha => List.mem_singleton.mp ha) onBlock_stA_Bs rfl

/-- (a) Non-vacuity of `GoodWindow`: on `trS`, the genesis entry (height `1`, slot `0`; its previous
height is not justified) has a good window with `a = 0`, `c_F = 1`, `k_F = 0`, served by `w₀`'s
proposal `Bs` of slot `1` at cut `2` on genesis, with the rows `{a₀}` (signed at time `0`, pooled at
cut `1`). -/
theorem trS_goodWindow : GoodWindow P₁ Unit {w₀} trS 1 g₁ 0 0 w₀ 2 Bs g₁ {a₀} := by
  have hst : trS.store w₀ 2 = stA := by rw [FGTrace.store, (trOf_state Bs stBs w₀).2.2.1]
  refine ⟨⟨rfl, ⟨rfl, rfl⟩, rfl, rfl, ?_, rfl, ?_⟩, ?_, ?_, ⟨le_rfl, le_rfl⟩, by decide, ?_, ?_,
    ?_, ⟨by decide, by decide⟩⟩ <;> rw [hst]
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

/-- (a) Sanity check of G1.7's reading on `trS`: the genesis entry does not have its previous height
justified at cut `2`, and the first conclusion of `PreviousHeightNotJustifiedEntry` holds after cut
`2` with `X = Bs`: `Bs` justifies the genesis entry at height `1`, appends `(1, genesis)` to the
pending pairs, and enters the height whose previous height is justified `2` with entry `Bs`. -/
theorem trS_previousHeightNotJustifiedEntry_first :
    ¬ ((trS.store w₀ 2).σ g₁.root).previousHeightJustified ∧
    ∃ X, JustifiesEntry P₁ Unit (trS.store w₀ (2 + 1)) g₁ ((trS.store w₀ 2).σ g₁.root).h X ∧
      (trS.store w₀ (2 + 1)).Anc X Bs ∧
      (((trS.store w₀ 2).σ g₁.root).h, g₁.root) ∈ ((trS.store w₀ (2 + 1)).σ X.root).pending ∧
      ((trS.store w₀ (2 + 1)).σ X.root).h = ((trS.store w₀ 2).σ g₁.root).h + 1 ∧
      ((trS.store w₀ (2 + 1)).σ X.root).Th = X.root ∧
      ((trS.store w₀ (2 + 1)).σ X.root).previousHeightJustified := by
  have h2 : trS.store w₀ 2 = stA := by rw [FGTrace.store, (trOf_state Bs stBs w₀).2.2.1]
  have h3 : trS.store w₀ (2 + 1) = stBs := by
    rw [FGTrace.store, (trOf_state Bs stBs w₀).2.2.2 0]
  rw [h2, h3]
  have hBs : Bs ∈ stBs.tree := rfl
  refine ⟨by decide, Bs, ⟨hBs, Relation.ReflTransGen.single ⟨rfl, hBs, rfl⟩, rfl, rfl, ?_⟩,
    Relation.ReflTransGen.refl, List.mem_singleton_self _, rfl, rfl, by decide⟩
  intro Y hY _ _ hne
  have h1 : Y.root ≠ 1 := fun h1 => by
    change stBs.blocks Y.root = some Y at hY
    rw [h1] at hY
    exact hne (Option.some_inj.mp hY).symm
  change (Function.update stA.σ 1 σBs Y.root).h = 1 ∧ (Function.update stA.σ 1 σBs Y.root).Th = 0
  rw [Function.update_of_ne h1]
  exact ⟨rfl, rfl⟩

/-- `w₀`'s proposal of slot `1` on genesis without attestations: root `1`. -/
def Be : NodeBlock P₁ Unit := ⟨1, some 0, 1, w₀, 0, [], ()⟩

/-- The chain state of `Be`: the initial one at slot `1` with latest block `Be` (no row, so no
height event). -/
def σBe : FG.ChainState P₁.n := { FG.ChainState.init P₁.fg with s := 1, L := 1 }

/-- `state_transition` of `Be` from the genesis state gives `σBe`. -/
theorem stateTransition_Be : P₁.fg.stateTransition (stA.σ 0) Be.fgView = some σBe := rfl

/-- The FG state after accepting `Be` on `stA`: `Be` and `σBe` added, nothing else changes. -/
def stBe : Store P₁ Unit :=
  { stA with
    blocks := Function.update stA.blocks 1 (some Be)
    σ := Function.update stA.σ 1 σBe }

open Classical in
/-- The finality update of `Be` on `stBe` changes nothing. -/
theorem updateFinality_stBe : stBe.updateFinality σBe = stBe := by
  unfold updateFinality
  extract_lets st₁ st₂
  have h2 : st₂ = stBe := by
    change (match st₁.blocks 0 with
      | some X => if st₁.Anc st₁.F X ∧ LexLt (st₁.hj, st₁.J.root) (0, 0) then
          { st₁ with J := X, hj := 0 } else st₁
      | none => st₁) = stBe
    rw [show st₁.blocks 0 = some g₁ from rfl]
    dsimp only
    rw [ite_eq_right (fun h => by simp [LexLt, st₁, stBe, stA, Store.init, P₁] at h)]
    rfl
  rw [h2, show stBe.blocks σBe.F = some g₁ from rfl]
  dsimp only
  rw [ite_eq_right (fun h => h.2.1 rfl)]

/-- `stA` accepts `Be`, with post-state `stBe`. -/
theorem onBlock_stA_Be : stA.onBlock Be = some stBe := by
  have hanc : Goldilocks.Anc (insert Be stA.tree) stA.F Be :=
    Relation.ReflTransGen.single ⟨Or.inr g₁_mem_stA, Or.inl rfl, rfl⟩
  have hneg : ¬ ((stA.blocks Be.root).isSome = true ∨ (stA.blocks 0).isNone = true ∨
      ¬ Goldilocks.Anc (insert Be stA.tree) stA.F Be) := by
    rintro (h | h | h)
    · simp [stA, Store.init, Be, P₁] at h
    · simp [stA, Store.init, P₁] at h
    · exact h hanc
  unfold onBlock
  split
  · next h => cases h
  next pr h =>
  cases h
  simp only [hneg, ↓reduceIte]
  split
  · next h => rw [stateTransition_Be] at h; cases h
  next σ' h =>
  rw [stateTransition_Be] at h; cases h
  change some ((updateFinality stBe σBe).addAtts []) = some stBe
  rw [updateFinality_stBe]
  rfl

/-- The trace in which `w₀` signs and pools `a₀` but proposes `Be` without it. -/
abbrev trE : FGTrace P₁ Unit := trOf Be stBe

/-- (a) The trace without the row in the proposal is still an `FGLocalRun` for `{w₀}` inside
`{genesis, Be}` (the FG contract lets a proposal omit a pooled row). -/
theorem trE_localRun : FGLocalRun () {w₀} {g₁, Be} trE :=
  trOf_localRun Be stBe rfl rfl rfl rfl (fun _ ha => by cases ha) onBlock_stA_Be rfl

/-- (r) The inclusion rule (P5) has teeth: on `trE`, `w₀`'s proposal `Be` at cut `2` serves no
good window, for any entry, slack, window, parent and rows, since `a₀` is pooled, valid against
genesis's state and on no chain, yet not in `Be`. -/
theorem trE_not_goodWindow (cF : Nat) (T : NodeBlock P₁ Unit) (a kF : Nat)
    (Pr : NodeBlock P₁ Unit) (R : Finset (FG.Att P₁.n)) :
    ¬ GoodWindow P₁ Unit {w₀} trE cF T a kF w₀ 2 Be Pr R := by
  intro hw
  have h2 : trE.store w₀ 2 = stA := by rw [FGTrace.store, (trOf_state Be stBe w₀).2.2.1]
  have hP5 := hw.proposal.2.2.2.2.2.2
  rw [h2] at hP5
  refine absurd (hP5 a₀ (List.mem_singleton_self _) (Or.inl ⟨rfl, rfl⟩) ?_) List.not_mem_nil
  rintro ⟨X, hX, -, ha⟩
  change (Store.init (P := P₁) ()).blocks X.root = some X at hX
  simp only [Store.init] at hX
  split at hX
  · cases (Option.some_inj.mp hX); cases ha
  · cases hX

end Consensus.Goldilocks.Store.Test

end
