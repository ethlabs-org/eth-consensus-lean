module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service
public import ConsensusLeanTest.Goldilocks.FGStore.TimeoutEntry
@[expose] public section

/-! # Witness for G1.8 (a), the crossing bound (FGStore)

`Crossing` applied on the timeout-entry trace `trT` (`P₁`: `Δ = 1`, `δ_t = 2`, `q = 1`; one node
`w₀`, honest), with every premise realized, and the crossing block identified. Labelled by kind
(CONTRIBUTING "Statements"): (a) `trT_crossing_premises`, `trT_crossing`, `trT_crossing_block`,
with `trT_proposal_Bc` and `trT_quorum_Bc`.

**The instance.** At `y = w₀`, cut `k = 15` (the final store `stX`), the entry `T = Bf` (height
`3`, slot `2`), `C = Bx` (slot `6`) on the chain genesis – `Bs` – `Bf` – `Bc` – `Bx`, `g = 3` and
`r = 1`: the bound is `Bf.slot + max δ_t r + g − 1 = 2 + 2 + 2 = 6 ≤ Bx.slot`. The windows are
`w ∈ {3, 4}` (`w + g − 1 ≤ 6`), both served by `Bc` (slot `5`), `w₀`'s honest proposal at cut
`11` on `Bf`: the pool `[a₀, a₁, aK, aF]` of `w₀` there has `aF` as its only row valid against
`σ[Bf]`, and `aF` is `Bc`'s payload; since `Bc.slot = 5 ≥ Bf.slot + r`, the pool must hold a
progress quorum of current-entry rows (height `3`, root `Bf`): `aF` alone (`q = 1`). The crossing
block is `Bc`, which leaves height `3` by timeout (`σ[Bc].h = 4`, `σ[Bc].h_j = 2`: `Bf` is not
justified) at slot `5 ≤ 6`; every crossing block within the bound is `Bc` or `Bx`, so `Bc` is the
first.

**Remarks.** `g = 3` is minimal for `T = Bf` here: at `g = 2` the window `w = 3` covers slots
`3`–`4`, which carry no block of `Bx`'s chain (`Bk`, of slot `3`, is a fork off genesis). The
docstring of `Crossing` motivates `r ≥ 1` by the case `max(δ_t, r) = 0`; this fixture cannot
exhibit it, since `δ_t = 2` gives `max(δ_t, r) = 2` for every `r ≤ 2`, so no `r = 0` rejection is
stated here. -/

namespace Consensus.Goldilocks.Store.Test

/-- The FG state of `w₀` before cut `11` of `trT` (the pool `[a₀, a₁, aK, aF]`) and after cut
`14`. -/
theorem trT_store_crossing : trT.store w₀ 11 = stKb ∧ trT.store w₀ 15 = stX :=
  ⟨congrArg Prod.fst (trT_state_succ 10 (by omega)), trT_store.2⟩

/-- (a) `Bc` is `w₀`'s honest proposal at cut `11` on `Bf`: of the pool `[a₀, a₁, aK, aF]`, only
`aF` is valid against `σ[Bf]` (height `3`, entry `Bf`, pending `[(2, Bs)]`), and it is `Bc`'s
payload. -/
theorem trT_proposal_Bc : HonestProposal P₁ Unit {w₀} trT w₀ 11 Bc Bf := by
  refine ⟨rfl, ⟨rfl, rfl⟩, rfl, rfl, ?_, rfl, ?_⟩ <;> rw [trT_store_crossing.1]
  · exact (rfl : stKb.blocks 2 = some Bf)
  · intro r hr hv _
    change r ∈ [a₀, a₁, aK, aF] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact List.mem_singleton_self _

/-- (a) Before cut `11`, the pool of `w₀` holds a progress quorum (`q = 1`) of current-entry rows
for `Bf` (height `σ[Bf].h = 3` at cut `15`, root `Bf`): `aF`. -/
theorem trT_quorum_Bc :
    P₁.fg.q ≤ (((trT.store w₀ 11).atts.filter fun x =>
      x.h = ((trT.store w₀ 15).σ Bf.root).h ∧ x.T = Bf.root).map FG.Att.val).toFinset.card := by
  rw [trT_store_crossing.1, trT_store_crossing.2]
  decide

/-- (a) The premises of `Crossing` on `trT` at `y = w₀`, `k = 15`, `C = Bx`, `T = Bf`, `g = 3`,
`r = 1`: the local run, `Bx` held, `Bf` an entry below `Bx`, `1 ≤ g`, `1 ≤ r`, the bound
`2 + max 2 1 + 3 − 1 ≤ 6`, and for every window `w` (so `w ∈ {3, 4}`) the honest proposal `Bc`
of slot `5` on `Bx`'s chain with the current-entry quorum in its proposer's pool. -/
theorem trT_crossing_premises :
    FGLocalRun () {w₀} {g₁, Bs, Bf, Bk, Bc, Bx} trT ∧ w₀ ∈ ({w₀} : Set (Fin P₁.n)) ∧
      Bx ∈ (trT.store w₀ 15).tree ∧ IsEntry P₁ Unit (trT.store w₀ 15) Bf ∧
      (trT.store w₀ 15).Anc Bf Bx ∧ 1 ≤ 3 ∧ 1 ≤ 1 ∧ Bf.slot + max P₁.δt 1 + 3 - 1 ≤ Bx.slot ∧
      ∀ w, Bf.slot < w → w + 3 - 1 ≤ Bx.slot →
        ∃ (Y Pr : NodeBlock P₁ Unit) (p : Fin P₁.n) (j : Nat),
          HonestProposal P₁ Unit {w₀} trT p j Y Pr ∧ (trT.store w₀ 15).Anc Y Bx ∧
          w ≤ Y.slot ∧ Y.slot ≤ w + 3 - 1 ∧
          (Bf.slot + 1 ≤ Y.slot →
            P₁.fg.q ≤ (((trT.store p j).atts.filter fun x => x.h =
              ((trT.store w₀ 15).σ Bf.root).h ∧ x.T = Bf.root).map FG.Att.val).toFinset.card) := by
  have hBcBx : (trT.store w₀ 15).Anc Bc Bx := by
    rw [trT_store_crossing.2]
    exact Relation.ReflTransGen.single ⟨rfl, rfl, rfl⟩
  refine ⟨trT_localRun, rfl, ?_, ?_, ?_, by decide, le_rfl, by decide, fun w hw hw' => ?_⟩
  · rw [trT_store_crossing.2]; exact (rfl : stX.blocks 5 = some Bx)
  · rw [trT_store_crossing.2]; exact ⟨rfl, rfl⟩
  · rw [trT_store_crossing.2] at hBcBx ⊢
    exact (Relation.ReflTransGen.single ⟨rfl, rfl, rfl⟩).trans hBcBx
  · change 2 < w at hw
    change w + 3 - 1 ≤ 6 at hw'
    exact ⟨Bc, Bf, w₀, 11, trT_proposal_Bc, hBcBx, show w ≤ 5 by omega,
      show 5 ≤ w + 3 - 1 by omega, fun _ => trT_quorum_Bc⟩

/-- (a) G1.8 (a) applied on `trT` with `trT_crossing_premises`: within `max(δ_t, r) + g − 1 = 4`
slots of `Bf.slot = 2`, the chain of `Bx` leaves `Bf`'s height `3`. -/
theorem trT_crossing :
    ∃ X ∈ (trT.store w₀ 15).tree, (trT.store w₀ 15).Anc Bf X ∧ (trT.store w₀ 15).Anc X Bx ∧
      ((trT.store w₀ 15).σ Bf.root).h < ((trT.store w₀ 15).σ X.root).h ∧
      X.slot ≤ Bf.slot + max P₁.δt 1 + 3 - 1 := by
  obtain ⟨hr, hy, hC, hT, hTC, hg, hr1, hb, hw⟩ := trT_crossing_premises
  exact crossing P₁ Unit () {w₀} {g₁, Bs, Bf, Bk, Bc, Bx} trT hr w₀ hy 15 Bx Bf 3 1 hC hT hTC hg
    hr1 hb hw

/-- (a) The crossing block of `trT_crossing` is `Bc`: it lies between `Bf` and `Bx`, has height
`4 > 3` and slot `5 ≤ 6`, and crosses by timeout (`σ[Bc].h_j = 2`: `Bf` is not justified). Every
block `X` with `trT_crossing`'s properties is `Bc` or `Bx` and extends `Bc`: `Bc` is the first. -/
theorem trT_crossing_block :
    Bc ∈ (trT.store w₀ 15).tree ∧ (trT.store w₀ 15).Anc Bf Bc ∧ (trT.store w₀ 15).Anc Bc Bx ∧
      ((trT.store w₀ 15).σ Bf.root).h = 3 ∧ ((trT.store w₀ 15).σ Bc.root).h = 4 ∧
      ((trT.store w₀ 15).σ Bc.root).hj = 2 ∧ Bc.slot = 5 ∧
      Bc.slot ≤ Bf.slot + max P₁.δt 1 + 3 - 1 ∧
      ∀ X ∈ (trT.store w₀ 15).tree, (trT.store w₀ 15).Anc Bf X → (trT.store w₀ 15).Anc X Bx →
        ((trT.store w₀ 15).σ Bf.root).h < ((trT.store w₀ 15).σ X.root).h →
        X.slot ≤ Bf.slot + max P₁.δt 1 + 3 - 1 →
          (X = Bc ∨ X = Bx) ∧ (trT.store w₀ 15).Anc Bc X := by
  rw [trT_store_crossing.2]
  have hBc : stX.Anc Bc Bx := Relation.ReflTransGen.single ⟨rfl, rfl, rfl⟩
  refine ⟨rfl, Relation.ReflTransGen.single ⟨rfl, rfl, rfl⟩, hBc, rfl, rfl, rfl, rfl, by decide,
    fun X hX _ _ hh _ => ?_⟩
  rcases mem_tree_stX hX with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hh (by decide)
  · exact absurd hh (by decide)
  · exact absurd hh (by decide)
  · exact absurd hh (by decide)
  · exact ⟨Or.inl rfl, Relation.ReflTransGen.refl⟩
  · exact ⟨Or.inr rfl, hBc⟩

end Consensus.Goldilocks.Store.Test

end
