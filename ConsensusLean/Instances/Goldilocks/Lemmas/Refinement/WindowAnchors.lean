module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowEntry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedC4
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows

public section

/-! # Goldilocks Refinement: window coverage from the anchor facts S1–S4 (WI-20)

consensus-lean#135 WI-20, #137; workbench `notes/fg-liveness/r14-end-to-end/window-delta-t-4.md`
§1 (S1–S4, Steps 1–3). The four anchors `A = block 0 ⪯ … ⪯ B₃ = block 3` are given; the facts
of the note are split as follows.

* S3 (one surviving chain), anchor part, PROVED: `anchors_chain`, `window_anchors_chain`
  (C4: `honest_proposal_below_next`, `honest_proposal_below_later`). At the store of an honest
  holder of `B₃` the chain is store ancestry (`store_anc_of_honest_anc`).
* Step 1, structural part, PROVED: `Store.first_crossing_of_anc`. On `A ⪯ B₃` with a higher
  height at `B₃`, the first crossing `T_B` after `A` is held, `A ⪯ T_B ⪯ B₃`, it is at height
  `σ[A].h + 1`, and it is its own entry block. So `A ⪯` the entry block of `T_B`
  (`Store.entry_anc_of_self`).
* S1 + S2 + S4, outcome of the tables (CONDITIONAL, premise): `Store.WindowAdvance`. The last
  anchor is three heights above `A` (E, B and C crossed).
* S1 + S4 at the late crossings (CONDITIONAL, premise): `Store.WindowService`. A crossing at
  height `σ[A].h + 1` or `σ[A].h + 2` at age `≥ δt` has a target quorum in its counted state, and
  a finality quorum at `h_j` when the pair `(h_j, J)` is pending. By F4 it justifies
  (`Store.crossing_of_service`, through `justify_of_target_chain`).

`Store.window_premises_of_anchors` gives exactly the premises of
`Store.finalized_covers_of_window''` with `X := T_B` and `W := B₃`, and
`Store.coverage_of_anchors`, `coverage_of_anchors`, `coverage_of_window_anchors` give the
`CacheCoverage` premise shape, the last two with ancestry in `HonestBlocks`. -/

namespace Consensus.Goldilocks

namespace Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}

/-- **S1 + S2 + S4, outcome (window-delta-t-4.md §1, Steps 1–3).** The last anchor `B₃` is three
heights above the first anchor `A`: the entry `E` current after `A`, its successor `B` and the
successor `C` of `B` crossed on the chain to `B₃`. CONDITIONAL on L5.1/L6.A in the note. -/
def WindowAdvance (st : Store P ACP) (A B₃ : NodeBlock P ACP) : Prop :=
  (st.σ A.root).h + 3 ≤ (st.σ B₃.root).h

/-- **S1 + S4 at the late crossings (window-delta-t-4.md §1, Steps 2–3).** Every held `D ⪯ B₃`
with a held parent `Z ⪰ A` at height `σ[A].h + 1` or `σ[A].h + 2` that enters the next height at
age `≥ δt` (`σ[Z].ThSlot + δt ≤ D.slot`) has a target quorum in its counted state (S1 service,
S4 honest rows are target rows), and a finality quorum at `h_j` if `σ[Z]` is bound and
`(h_j, J)` is pending (S1: the rows name the exact predecessor pair). CONDITIONAL on L5.1/L6.A
and record usability in the note. -/
def WindowService (st : Store P ACP) (A B₃ : NodeBlock P ACP) : Prop :=
  ∀ D ∈ st.tree, ∀ Z ∈ st.tree, D.parent = some Z.root → st.Anc A Z → st.Anc D B₃ →
    ((st.σ Z.root).h = (st.σ A.root).h + 1 ∨ (st.σ Z.root).h = (st.σ A.root).h + 2) →
    (st.σ D.root).h = (st.σ Z.root).h + 1 →
    (st.σ Z.root).ThSlot + P.fg.δt ≤ D.slot →
    P.fg.q ≤ (D.fgView.atts.foldl FG.ChainState.processAtt
        { st.σ Z.root with s := D.fgView.slot }).target.card ∧
      ((st.σ Z.root).bound → ((st.σ Z.root).hj, (st.σ Z.root).J) ∈ (st.σ Z.root).pending →
        P.fg.q ≤ ((D.fgView.atts.foldl FG.ChainState.processAtt
          { st.σ Z.root with s := D.fgView.slot }).fin (st.σ Z.root).hj).card)

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

/-- **Service gives the crossing premise (F4: justification before timeout).** Under
`WindowService st A B₃`, for `X ⪰ A` at height `σ[A].h + 1`, every held `D ⪯ B₃` with held
parent `Z ⪰ X` at height `σ[X].h` or `σ[X].h + 1` that enters the next height is early or
justifies: this is the premise `hs` of `finalized_covers_of_window''` with `W := B₃`. -/
theorem crossing_of_service (hr : st.Reachable acp₀) {A X B₃ : NodeBlock P ACP}
    (hAX : st.Anc A X) (hXh : (st.σ X.root).h = (st.σ A.root).h + 1)
    (hsv : WindowService st A B₃) :
    ∀ D ∈ st.tree, ∀ Z ∈ st.tree, D.parent = some Z.root → st.Anc X Z → st.Anc D B₃ →
      ((st.σ Z.root).h = (st.σ X.root).h ∨ (st.σ Z.root).h = (st.σ X.root).h + 1) →
      (st.σ D.root).h = (st.σ Z.root).h + 1 →
      D.slot < (st.σ Z.root).ThSlot + P.fg.δt ∨ (st.σ D.root).hj = (st.σ Z.root).h := by
  intro D hD Z hZ hpar hXZ hDB hZh hDh
  rcases Nat.lt_or_ge D.slot ((st.σ Z.root).ThSlot + P.fg.δt) with hl | hl
  · exact Or.inl hl
  refine Or.inr ?_
  obtain ⟨hq, hf⟩ := hsv D hD Z hZ hpar (hAX.trans hXZ) hDB (by omega) hDh hl
  obtain ⟨c, -, -, -, hc⟩ := chain_state_of_chain P ACP acp₀ st hr Z hZ
  obtain ⟨-, -, -, ht⟩ := Healing.Store.step_σ hr hD hpar
  exact (P.fg.justify_of_target_chain hc ht hq hf).1

/-- **The premises of `finalized_covers_of_window''` from the anchors.** In a reachable store,
for held `A ⪯ B₃` with `WindowAdvance` and `WindowService`, the first crossing `X = T_B` after
`A` meets every premise of `finalized_covers_of_window''` with `W := B₃`. -/
theorem window_premises_of_anchors (hr : st.Reachable acp₀) {A B₃ : NodeBlock P ACP}
    (hAB : st.Anc A B₃) (hadv : WindowAdvance st A B₃) (hsv : WindowService st A B₃) :
    ∃ X ∈ st.tree, st.Anc A X ∧ (st.σ X.root).Th = X.root ∧
      st.Anc X B₃ ∧ st.Anc B₃ B₃ ∧ (st.σ X.root).h + 1 < (st.σ B₃.root).h ∧
      (∀ D ∈ st.tree, ∀ Z ∈ st.tree, D.parent = some Z.root → st.Anc X Z → st.Anc D B₃ →
        ((st.σ Z.root).h = (st.σ X.root).h ∨ (st.σ Z.root).h = (st.σ X.root).h + 1) →
        (st.σ D.root).h = (st.σ Z.root).h + 1 →
        D.slot < (st.σ Z.root).ThSlot + P.fg.δt ∨ (st.σ D.root).hj = (st.σ Z.root).h) ∧
      (∀ T ∈ st.tree, T.root = (st.σ X.root).Th → st.Anc A T) := by
  unfold WindowAdvance at hadv
  obtain ⟨X, hX, hAX, hXB, hXh, hXT⟩ := first_crossing_of_anc hr hAB (by omega)
  exact ⟨X, hX, hAX, hXT, hXB, Relation.ReflTransGen.refl, by omega,
    crossing_of_service hr hAX hXh hsv, entry_anc_of_self hr hX hXT hAX⟩

/-- **Window coverage from the anchors (store form).** In a reachable store, for held
`A ⪯ B₃` with `WindowAdvance` and `WindowService`, the block `F` of root `σ[B₃].F` is held and
`A ⪯ F`. -/
theorem coverage_of_anchors (hr : st.Reachable acp₀) {A B₃ : NodeBlock P ACP}
    (hB₃ : B₃ ∈ st.tree) (hAB : st.Anc A B₃) (hadv : WindowAdvance st A B₃)
    (hsv : WindowService st A B₃) :
    ∃ F, st.blocks (st.σ B₃.root).F = some F ∧ st.Anc A F := by
  obtain ⟨X, hX, -, -, hXB, hBB, hh, hs, hB₀⟩ := window_premises_of_anchors hr hAB hadv hsv
  exact finalized_covers_of_window'' hr hX hB₃ hXB hBB hh hs hB₀

end Store

namespace Refinement

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a : Time}

/-- **S3, anchor part: two honest proposals lie on one chain (C4).** Under the reset and
Catch(2Δ), the honest proposal `P₀` of a post-drain slot `s₀` is an ancestor (in the honest
blocks) of the honest proposal `P₁` of every slot `s₁ > s₀`. -/
theorem anchors_chain (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {s₀ s₁ : Nat}
    {P₀ P₁ : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP₀ : Healing.HonestProposalRun tr H proposer s₀ P₀)
    (hR : Healing.drainTime sp a ≤ sp.ts s₀)
    (hP₁ : Healing.HonestProposalRun tr H proposer s₁ P₁) (hs : s₀ < s₁) :
    Anc (tr.HonestBlocks H) P₀ P₁ := by
  rcases Nat.lt_or_ge s₁ (s₀ + 2) with hl | hl
  · obtain rfl : s₁ = s₀ + 1 := by omega
    exact honest_proposal_below_next hp hc hP₀ hR hP₁
  · exact honest_proposal_below_later hp hc hP₀ (proposesAt_of_honestProposalRun hp.run hP₀)
      hR hP₁ hl

/-- **S3, anchor part, for a window of four anchors.** Honest proposals `P a` at strictly
increasing slots `s a`, the first one post-drain, lie on one chain of honest blocks (the
`chain` field shape of `FinalWindowData`). -/
theorem window_anchors_chain (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {s : Fin 4 → Nat}
    {P : Fin 4 → SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ∀ i, Healing.HonestProposalRun tr H proposer (s i) (P i)) (hs : StrictMono s)
    (hR : Healing.drainTime sp a ≤ sp.ts (s 0)) :
    ∀ i j, i ≤ j → Anc (tr.HonestBlocks H) (P i) (P j) := by
  intro i j hij
  rcases hij.lt_or_eq with hlt | rfl
  · have hRi : Healing.drainTime sp a ≤ sp.ts (s i) :=
      hR.trans ((SA.ts_le_iff sp).2 (by exact_mod_cast hs.monotone (Fin.zero_le i)))
    exact anchors_chain hp hc (hP i) hRi (hP j) (hs hlt)
  · exact Relation.ReflTransGen.refl

/-- **Window coverage from the anchors (run form).** For an honest `y` that holds `B₃` at cut
`k`, an anchor `A ⪯ B₃` in the honest blocks, and `WindowAdvance`, `WindowService` at the store
of `y`, the block `F` of root `σ[B₃].F` is held by `y` and `A ⪯ F` in the honest blocks. -/
theorem coverage_of_anchors (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {A B₃ : SA.Blk sp.n (List (FG.Att sp.n))} (hAB : Anc (tr.HonestBlocks H) A B₃)
    (hB₃ : B₃ ∈ (tr.state y k).fg.tree)
    (hadv : Store.WindowAdvance (tr.state y k).fg A B₃)
    (hsv : Store.WindowService (tr.state y k).fg A B₃) :
    ∃ F, (tr.state y k).fg.blocks ((tr.state y k).fg.σ B₃.root).F = some F ∧
      Anc (tr.HonestBlocks H) A F := by
  obtain ⟨F, hF, hAF⟩ := Store.coverage_of_anchors (Compose.fg_reachable hrun.toLocalRun hy k)
    hB₃ (Healing.store_anc_of_honest_anc hrun hnc hy hAB hB₃) hadv hsv
  exact ⟨F, hF, Healing.honest_anc_of_store_anc hy hAF⟩

/-- **Window coverage from four honest anchors.** `coverage_of_anchors` with S3 proved: the
anchors `P a` are honest proposals at strictly increasing slots, the first one post-drain, under
the reset and Catch(2Δ), and the last one is held by the honest `y` at cut `k`. The remaining
premises are `WindowAdvance` and `WindowService` from `P 0` to `P 3` at the store of `y`. -/
theorem coverage_of_window_anchors (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {s : Fin 4 → Nat}
    {P : Fin 4 → SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ∀ i, Healing.HonestProposalRun tr H proposer (s i) (P i)) (hs : StrictMono s)
    (hR : Healing.drainTime sp a ≤ sp.ts (s 0)) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    (hB₃ : P 3 ∈ (tr.state y k).fg.tree)
    (hadv : Store.WindowAdvance (tr.state y k).fg (P 0) (P 3))
    (hsv : Store.WindowService (tr.state y k).fg (P 0) (P 3)) :
    ∃ F, (tr.state y k).fg.blocks ((tr.state y k).fg.σ (P 3).root).F = some F ∧
      Anc (tr.HonestBlocks H) (P 0) F :=
  coverage_of_anchors hp.run hp.noColl hy
    (window_anchors_chain hp hc hP hs hR 0 3 (by decide)) hB₃ hadv hsv

end Refinement

end Consensus.Goldilocks

end
