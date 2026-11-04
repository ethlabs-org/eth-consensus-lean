module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.WindowEntry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealedC4
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows

public section

/-! # Goldilocks Obligations: window coverage from the anchor facts S1–S4 (WI-20)

consensus-lean#135 WI-20, #137; workbench `notes/fg-liveness/r14-end-to-end/window-delta-t-4.md`
§1 (S1–S4, Steps 1–3). The four anchors `A = block 0 ⪯ … ⪯ B₃ = block 3` are given; the facts
of the note are split as follows.

* S3 (one surviving chain), anchor part, PROVED: `anchors_chain_upTo`,
  `window_anchors_chain_upTo` (C4: `honest_proposal_below_next_upTo`,
  `honest_proposal_below_later_upTo`). At the store of an honest
  holder of `B₃` the chain is store ancestry (`store_anc_of_honest_anc`).
* Step 1, structural part, PROVED: `Store.first_crossing_of_anc`. On `A ⪯ B₃` with a higher
  height at `B₃`, the first crossing `T_B` after `A` is held, `A ⪯ T_B ⪯ B₃`, it is at height
  `σ[A].h + 1`, and it is its own entry block. So `A ⪯` the entry block of `T_B`
  (`Store.entry_anc_of_self`).

S1, S2 and S4 (the outcome of the tables and the late crossings) are not stated here; the final
window takes its coverage from `cacheCoverage_of_anchor_window_upTo` (`WindowAnchorRoute`). -/

namespace Consensus.Goldilocks

namespace Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}

/-- **The first crossing after `A` (window-delta-t-4.md §1, Step 1, structural part).** In a
reachable store, on a held `A ⪯ B` with `σ[A].h < σ[B].h`, a held `X` with `A ⪯ X ⪯ B` enters
height `σ[A].h + 1` and is its own entry block (`σ[X].Th = X.root`). -/
theorem first_crossing_of_anc (hr : st.Reachable acp₀) {A B : NodeBlock P ACP}
    (hAB : st.Anc A B) (hh : (st.σ A.root).h < (st.σ B.root).h) :
    ∃ X ∈ st.tree, st.Anc A X ∧ st.Anc X B ∧ (st.σ X.root).h = (st.σ A.root).h + 1 ∧
      (st.σ X.root).Th = X.root := by
  suffices key : (st.σ A.root).h ≤ (st.σ B.root).h ∧ ((st.σ A.root).h < (st.σ B.root).h →
      ∃ X ∈ st.tree, st.Anc A X ∧ st.Anc X B ∧ (st.σ X.root).h = (st.σ A.root).h + 1 ∧
        (st.σ X.root).Th = X.root) from key.2 hh
  clear hh
  induction hAB with
  | refl => exact ⟨le_rfl, fun h => absurd h (lt_irrefl _)⟩
  | @tail W W' hAW hWW' ih =>
    obtain ⟨hle, ih⟩ := ih
    obtain ⟨hW, hW', hp⟩ := hWW'
    obtain ⟨-, -, -, ht⟩ := Healing.Store.step_σ hr hW' hp
    have hst : st.Anc W W' := .single ⟨hW, hW', hp⟩
    rcases P.fg.stateTransition_ThSlot ht with ⟨e, -, -⟩ | ⟨e, -, eT⟩
    · refine ⟨e ▸ hle, fun hlt => ?_⟩
      obtain ⟨X, hX, hAX, hXW, h1, h2⟩ := ih (e ▸ hlt)
      exact ⟨X, hX, hAX, hXW.trans hst, h1, h2⟩
    · refine ⟨by omega, fun hlt => ?_⟩
      rcases Nat.lt_or_ge (st.σ A.root).h (st.σ W.root).h with hl | hl
      · obtain ⟨X, hX, hAX, hXW, h1, h2⟩ := ih hl
        exact ⟨X, hX, hAX, hXW.trans hst, h1, h2⟩
      · exact ⟨W', hW', hAW.trans hst, Relation.ReflTransGen.refl, by omega, eT⟩

/-- **The entry block of a self entry.** If `X` is its own entry block and `B₀ ⪯ X`, then
`B₀ ⪯ T` for every held `T` of root `σ[X].Th` (roots of held blocks are unique). This is the
premise `hB₀` of `finalized_covers_of_window''`. -/
theorem entry_anc_of_self (hr : st.Reachable acp₀) {B₀ X : NodeBlock P ACP} (hX : X ∈ st.tree)
    (hXT : (st.σ X.root).Th = X.root) (hB : st.Anc B₀ X) :
    ∀ T ∈ st.tree, T.root = (st.σ X.root).Th → st.Anc B₀ T := by
  intro T hT he
  obtain rfl : T = X := (accepted_tree P ACP acp₀ st hr).2.1.1 hT hX (he.trans hXT)
  exact hB

end Store

namespace Obligations
open AsChainShape Simulation

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a : Time}

end Obligations

end Consensus.Goldilocks

end
