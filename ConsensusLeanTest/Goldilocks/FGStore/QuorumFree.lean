module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries
public import ConsensusLeanTest.Goldilocks.FGStore.TimeoutEntry
@[expose] public section

/-! # Witness and quiet-window rejection for G1.10's core (FGStore)

`QuorumFreeEntries` on the timeout-entry trace `trT` (`P₁`: `Δ = 1`, `δ_t = 2`, `q = 1`; one
node `w₀`, honest; every time is public). The only signatures of `trT` are `a₀` (cut `0`, time
`0`, naming root `0`), `a₁` (cut `3`, time `1`, root `1`), `aK` (cut `7`, time `3`, root `3`),
`aF` (cut `9`, time `4`, root `2`) and `aC` (cut `12`, time `5`, root `4 = Bc.root`). Labelled by
kind (CONTRIBUTING "Statements"):

* (a) `trT_namers_Bc`: no validator names the timeout entry `Bc` at or before time `4`.
* (a) `trT_quorumFreeEntries_premises`: every premise of `QuorumFreeEntries` holds together at
  `𝓔 = {Bc}`, `T₀ = T = 4`, `y = w₀`, `X = Bc` accepted at cut `11` (time `5 = T + Δ`, `w₀`'s own
  proposal of slot `5`: the boundary disjunct), `E = A = Bc`, `h = 4`; the quiet window `(4, 4]`
  is empty.
* (a) `trT_quorumFreeEntries_Bc`: `quorum_free_entries` applied there; `trT_entry_state_Bc`
  checks its conclusion directly (`σ[Bc]` has height `4`, entry `Bc`, empty progress set).
* (r) `trT_quorumFreeEntries_needs_quietWindow`: at `T₀ = 4`, `T = 5`, `X = Bx` accepted at cut
  `14` (time `6 = T + Δ`, own proposal of slot `6`), `A = E = Bc`, `h = 4`, every premise holds
  except the quiet window (`aC`, signed by `w₀` at time `5 ∈ (4, 5]`, names `Bc`), and the
  conclusion fails: `Bx` justifies `Bc` and `σ[Bx]` has height `5 ≠ 4`. -/

namespace Consensus.Goldilocks.Store.Test

/-- (a) In `trT`, no validator is a namer of `Bc` at time `4`: `w₀` is honest, and of its
signatures at or before time `4` (`a₀`, `a₁`, `aK`, `aF`) none names root `4`; `aC` is signed at
time `5`. -/
theorem trT_namers_Bc : namers P₁ Unit {w₀} trT 4 Bc = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun v hv => ?_
  rw [namers, Set.mem_ofPred_eq] at hv
  rcases hv with hv | ⟨j, a, ⟨src, -, hj⟩, ht, hT⟩
  · exact hv (eq_w₀ v)
  · rcases trT_label j _ hj with ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ |
      ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ |
      ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ <;>
      cases h' <;> first | exact absurd hT (by decide) | exact absurd ht (by decide)

/-- (K1) at `T₀ = 4` for `𝓔 = {Bc}`: no namers, so weight `0 < q = 1`. -/
theorem trT_namers_lt :
    ∀ E ∈ ({Bc} : Set (NodeBlock P₁ Unit)), (namers P₁ Unit {w₀} trT 4 E).ncard < P₁.fg.q := by
  intro E hE
  rw [Set.mem_singleton_iff.mp hE, trT_namers_Bc, Set.ncard_empty]
  decide

/-- The FG state of `w₀` after cut `11` of `trT` (the acceptance of `Bc`). -/
theorem trT_store_twelve : trT.store w₀ (11 + 1) = stC :=
  congrArg Prod.fst (trT_state_succ 11 (by omega))

/-- (a) Every premise of `QuorumFreeEntries` holds on `trT` at `𝓔 = {Bc}`, `T₀ = T = 4`,
`y = w₀`, `X = Bc` accepted at cut `11` (time `5 = T + Δ`, `w₀`'s own proposal of slot `5`),
`E = A = Bc` and `h = 4`. The quiet window `(4, 4]` is empty. -/
theorem trT_quorumFreeEntries_premises :
    FGLocalRun () {w₀} {g₁, Bs, Bf, Bk, Bc, Bx} trT ∧ P₁.IsPublic 4 ∧ P₁.IsPublic 4 ∧
      w₀ ∈ ({w₀} : Set (Fin P₁.n)) ∧
      (∀ E ∈ ({Bc} : Set (NodeBlock P₁ Unit)), (namers P₁ Unit {w₀} trT 4 E).ncard < P₁.fg.q) ∧
      (∀ v ∈ ({w₀} : Set (Fin P₁.n)), ∀ j a, trT.SignAt v j a → 4 < trT.time j →
        trT.time j ≤ 4 → ∀ E ∈ ({Bc} : Set (NodeBlock P₁ Unit)), a.T ≠ E.root) ∧
      trT.AcceptAt w₀ 11 Bc ∧
      (trT.time 11 < 4 + P₁.Δ ∨
        (trT.time 11 = 4 + P₁.Δ ∧ Bc.proposer = w₀ ∧ P₁.slotTime Bc.slot = 4 + P₁.Δ)) ∧
      Bc ∈ ({Bc} : Set (NodeBlock P₁ Unit)) ∧ Bc ∈ (trT.store w₀ (11 + 1)).tree ∧
      (trT.store w₀ (11 + 1)).Anc Bc Bc ∧ ((trT.store w₀ (11 + 1)).σ Bc.root).h = 4 ∧
      ((trT.store w₀ (11 + 1)).σ Bc.root).Th = Bc.root := by
  rw [trT_store_twelve]
  exact ⟨trT_localRun, one_dvd _, one_dvd _, rfl, trT_namers_lt,
    fun _ _ _ _ _ h₁ h₂ => absurd (h₁.trans_le h₂) (lt_irrefl _), ⟨rfl, rfl⟩,
    Or.inr ⟨by decide, rfl, by decide⟩, rfl, (rfl : stC.blocks 4 = some Bc),
    Relation.ReflTransGen.refl, rfl, rfl⟩

/-- (a) `quorum_free_entries` applied at `trT_quorumFreeEntries_premises`: `Bc`'s state after
cut `11` has height `4`, entry `Bc`, and a progress set below `q`. -/
theorem trT_quorumFreeEntries_Bc :
    ((trT.store w₀ (11 + 1)).σ Bc.root).h = 4 ∧
      ((trT.store w₀ (11 + 1)).σ Bc.root).Th = Bc.root ∧
      ((trT.store w₀ (11 + 1)).σ Bc.root).prog.card < P₁.fg.q := by
  obtain ⟨hr, hT₀, hT, hy, hK, hK', hX, ht, hE, hA, hAX, hAh, hATh⟩ :=
    trT_quorumFreeEntries_premises
  exact quorum_free_entries P₁ Unit () {w₀} _ trT {Bc} 4 4 w₀ hr hT₀ hT hy hK hK' 11 Bc hX ht
    Bc hE 4 Bc hA hAX hAh hATh

/-- (a) The conclusion of `trT_quorumFreeEntries_Bc`, checked directly: `σ[Bc]` has height `4`,
entry `Bc` and an empty progress set. -/
theorem trT_entry_state_Bc :
    ((trT.store w₀ (11 + 1)).σ Bc.root).h = 4 ∧
      ((trT.store w₀ (11 + 1)).σ Bc.root).Th = Bc.root ∧
      ((trT.store w₀ (11 + 1)).σ Bc.root).prog = ∅ := by
  rw [trT_store_twelve]
  exact ⟨rfl, rfl, rfl⟩

/-- (r) The quiet window of (K1_𝓔) is needed: on `trT` at `𝓔 = {Bc}`, `T₀ = 4`, `T = 5`,
`y = w₀`, `X = Bx` accepted at cut `14` (time `6 = T + Δ`, `w₀`'s own proposal of slot `6`),
`E = A = Bc` and `h = 4`, every premise of `QuorumFreeEntries` but the quiet window holds; that
one fails (`aC`, signed by `w₀` at cut `12`, time `5 ∈ (4, 5]`, names `Bc`), and so does the
conclusion: `aC` in `Bx` is a quorum for `Bc`, and `σ[Bx]` has height `5 ≠ 4`. -/
theorem trT_quorumFreeEntries_needs_quietWindow :
    FGLocalRun () {w₀} {g₁, Bs, Bf, Bk, Bc, Bx} trT ∧ P₁.IsPublic 4 ∧ P₁.IsPublic 5 ∧
      w₀ ∈ ({w₀} : Set (Fin P₁.n)) ∧
      (∀ E ∈ ({Bc} : Set (NodeBlock P₁ Unit)), (namers P₁ Unit {w₀} trT 4 E).ncard < P₁.fg.q) ∧
      ¬ (∀ v ∈ ({w₀} : Set (Fin P₁.n)), ∀ j a, trT.SignAt v j a → 4 < trT.time j →
        trT.time j ≤ 5 → ∀ E ∈ ({Bc} : Set (NodeBlock P₁ Unit)), a.T ≠ E.root) ∧
      trT.AcceptAt w₀ 14 Bx ∧
      (trT.time 14 < 5 + P₁.Δ ∨
        (trT.time 14 = 5 + P₁.Δ ∧ Bx.proposer = w₀ ∧ P₁.slotTime Bx.slot = 5 + P₁.Δ)) ∧
      Bc ∈ ({Bc} : Set (NodeBlock P₁ Unit)) ∧ Bc ∈ (trT.store w₀ (14 + 1)).tree ∧
      (trT.store w₀ (14 + 1)).Anc Bc Bx ∧ ((trT.store w₀ (14 + 1)).σ Bc.root).h = 4 ∧
      ((trT.store w₀ (14 + 1)).σ Bc.root).Th = Bc.root ∧
      ¬ (((trT.store w₀ (14 + 1)).σ Bx.root).h = 4 ∧
        ((trT.store w₀ (14 + 1)).σ Bx.root).Th = Bc.root ∧
        ((trT.store w₀ (14 + 1)).σ Bx.root).prog.card < P₁.fg.q) := by
  rw [trT_store.2]
  have hBc : Bc ∈ stX.tree := (rfl : stX.blocks 4 = some Bc)
  have hBx : Bx ∈ stX.tree := (rfl : stX.blocks 5 = some Bx)
  exact ⟨trT_localRun, one_dvd _, one_dvd _, rfl, trT_namers_lt,
    fun h => h w₀ rfl 12 aC ⟨Bc, rfl, rfl⟩ (by decide) (by decide) Bc rfl rfl, ⟨rfl, rfl⟩,
    Or.inr ⟨by decide, rfl, by decide⟩, rfl, hBc, Relation.ReflTransGen.single ⟨hBc, hBx, rfl⟩,
    rfl, rfl, fun h => absurd h.1 (by decide)⟩

end Consensus.Goldilocks.Store.Test

end
