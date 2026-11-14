module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.WindowAnchors
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Healed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.OperationalReports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalCrosses
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeMature
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs

public section

/-! # Goldilocks Obligations: the store side of the anchor route to window coverage (fixed `δt`)

`δt` is a fixed constant, independent of the honest-proposer gap `g`. Honest proposers are used
only at the four anchors `P₀ ⪯ … ⪯ P₃`; the slots between anchors may be faulty.

* `Store.slot_lt_ThSlot_of_anc`: a held `Z ⪰ A` strictly above the height of `A` has its entry
  slot strictly above `A.slot`.
* `Store.anchor_window_hs`: with `X` the first crossing after `A` and `W.slot ≤ A.slot + δt`,
  every crossing `D ⪯ W` constrained by `finalized_covers_of_window''` is early. The bound is
  exact for this argument: the entry of height `σ[A].h + 1` can be at slot `A.slot + 1`.
* `Store.coverage_of_anchor_window`: coverage for `P₃` at a store holding three anchor steps. -/

namespace Consensus.Goldilocks

namespace Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}

/-- Slots grow along a store ancestry. -/
theorem slot_le_of_anc (hr : st.Reachable acp₀) {A Z : NodeBlock P ACP} (h : st.Anc A Z) :
    A.slot ≤ Z.slot := by
  induction h with
  | refl => exact le_rfl
  | @tail Y Y' _ hYY' ih =>
    obtain ⟨hY, hY', hp⟩ := hYY'
    have := (accepted_tree P ACP acp₀ st hr).2.1.2 Y hY Y' hY' hp
    omega

/-- **(a) The entry slot above an anchor.** In a reachable store, for a held `A ⪯ Z` with
`σ[A].h < σ[Z].h`, `A.slot < σ[Z].ThSlot`. -/
theorem slot_lt_ThSlot_of_anc (hr : st.Reachable acp₀) {A Z : NodeBlock P ACP}
    (h : st.Anc A Z) (hh : (st.σ A.root).h < (st.σ Z.root).h) :
    A.slot < (st.σ Z.root).ThSlot := by
  suffices key : (st.σ A.root).h < (st.σ Z.root).h → A.slot < (st.σ Z.root).ThSlot from key hh
  clear hh
  induction h with
  | refl => exact fun h => absurd h (lt_irrefl _)
  | @tail Y Y' hAY hYY' ih =>
    intro hlt
    obtain ⟨hY, hY', hp⟩ := hYY'
    obtain ⟨-, -, -, ht⟩ := Healing.Store.step_σ hr hY' hp
    have hsl := (accepted_tree P ACP acp₀ st hr).2.1.2 Y hY Y' hY' hp
    have hAs := slot_le_of_anc hr hAY
    rcases P.fg.stateTransition_ThSlot ht with ⟨e, e', -⟩ | ⟨-, e', -⟩
    · rw [e']; exact ih (e ▸ hlt)
    · rw [e']; change A.slot < Y'.slot; omega

/-- **The `hs` discharge of the anchor window.** In a reachable store, let `X ⪰ A` be at height
`σ[A].h + 1` and `W.slot ≤ A.slot + δt`. Every held `D ⪯ W` with held parent `Z ⪰ X` at height
`σ[X].h` or `σ[X].h + 1` that enters the next height is early (first disjunct), since
`D.slot ≤ W.slot ≤ A.slot + δt < σ[Z].ThSlot + δt`. -/
theorem anchor_window_hs (hr : st.Reachable acp₀) {A X W : NodeBlock P ACP}
    (hAX : st.Anc A X) (hXh : (st.σ X.root).h = (st.σ A.root).h + 1)
    (hsl : W.slot ≤ A.slot + P.fg.δt) :
    ∀ D ∈ st.tree, ∀ Z ∈ st.tree, D.parent = some Z.root → st.Anc X Z → st.Anc D W →
      ((st.σ Z.root).h = (st.σ X.root).h ∨ (st.σ Z.root).h = (st.σ X.root).h + 1) →
      (st.σ D.root).h = (st.σ Z.root).h + 1 →
      D.slot < (st.σ Z.root).ThSlot + P.fg.δt ∨ (st.σ D.root).hj = (st.σ Z.root).h := by
  intro D _ Z _ _ hXZ hDW _ _
  have hle := Healing.h_le_of_store_anc hr hXZ
  have hlt := slot_lt_ThSlot_of_anc hr (hAX.trans hXZ) (by omega)
  have hD := slot_le_of_anc hr hDW
  exact Or.inl (by omega)

/-- **Window coverage from an anchor window (store form).** In a reachable store, for held
`A ⪯ B₃` with `σ[A].h + 3 ≤ σ[B₃].h` and `B₃.slot ≤ A.slot + δt`, the block `F` of root
`σ[B₃].F` is held and `A ⪯ F` (`finalized_covers_of_window''` with `X` the first crossing after
`A` and `W := B₃`). -/
theorem coverage_of_anchor_window (hr : st.Reachable acp₀) {A B₃ : NodeBlock P ACP}
    (hB₃ : B₃ ∈ st.tree) (hAB : st.Anc A B₃) (hadv : (st.σ A.root).h + 3 ≤ (st.σ B₃.root).h)
    (hsl : B₃.slot ≤ A.slot + P.fg.δt) :
    ∃ F, st.blocks (st.σ B₃.root).F = some F ∧ st.Anc A F := by
  obtain ⟨X, hX, hAX, hXB, hXh, hXT⟩ := first_crossing_of_anc hr hAB (by omega)
  exact finalized_covers_of_window'' hr hX hB₃ hXB Relation.ReflTransGen.refl (by omega)
    (anchor_window_hs hr hAX hXh hsl) (entry_anc_of_self hr hX hXT hAX)

end Store

namespace Obligations
open AsChainShape Simulation

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

end Obligations

end Consensus.Goldilocks

end
