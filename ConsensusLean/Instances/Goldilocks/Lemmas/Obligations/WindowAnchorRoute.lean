module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.WindowAnchorsUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.WindowAnchorStep

public section

/-! # Goldilocks Obligations: the anchor route to window coverage (fixed `δt`)

`δt` is a fixed constant, independent of the
honest-proposer gap `g`. Honest proposers are used only at the four anchors `P₀ ⪯ … ⪯ P₃`; the
slots between anchors may be faulty. No density premise (`hM4`) and no
window advance or window service premise.

* `Store.slot_lt_ThSlot_of_anc`: a held `Z ⪰ A` strictly above the height of `A` has its entry
  slot strictly above `A.slot`.
* `Store.anchor_window_hs`: with `X` the first crossing after `A` and `W.slot ≤ A.slot + δt`,
  every crossing `D ⪯ W` constrained by `finalized_covers_of_window''` is early. The bound is
  exact for this argument: the entry of height `σ[A].h + 1` can be at slot `A.slot + 1`.
* `anchor_window_advance`: three anchor steps (`anchor_height_step*`) give
  `σ[P₀].h + 3 ≤ σ[P₃].h` at every honest store that holds the anchors.
* `Store.coverage_of_anchor_window`, `cacheCoverage_of_anchor_window_upTo`: coverage for `P₃`. -/

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

/-- One anchor step between honest stores: `σ[A].h + 1 ≤ σ[X].h`, read at two honest stores
that hold `A` and `X`. This is the form `anchor_height_step*` gives. -/
def AnchorStep (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (A X : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∃ z ∈ H, ∃ j j' : Nat, A ∈ (tr.state z j).fg.tree ∧ X ∈ (tr.state z j').fg.tree ∧
    ((tr.state z j).fg.σ A.root).h + 1 ≤ ((tr.state z j').fg.σ X.root).h

/-- **An anchor step from `anchor_height_step_or_crossed`.** With its premises and `A ⪯ Pr` in
the proposer's store at the cut, `AnchorStep tr H A X`. -/
theorem anchorStep_of_or_crossed (hrun : GoldilocksRun proposer dg H tr) {g ΔF v b : Time}
    (hs : Healing.HSSharedUpTo tr H dg g ΔF b) (hv : gbar g ≤ v)
    {p : Fin sp.n} (hp : p ∈ H) {kX : Nat} {A X Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : tr.ProposesAt p kX X) (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b)
    (hpar : X.parent = some Pr.root) (hPr : Pr ∈ (tr.state p kX).fg.tree)
    (hAPr : (tr.state p kX).fg.Anc A Pr)
    (hrows : ((tr.state p kX).fg.σ Pr.root).h = ((tr.state p kX).fg.σ A.root).h →
      ∃ S : Finset (Fin sp.n), (∀ v ∈ S, v ∈ H) ∧ sp.toParams.fg.q ≤ S.card ∧
      ∀ y ∈ S, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧
        att.h = ((tr.state p kX).fg.σ Pr.root).h ∧
        att.T = ((tr.state p kX).fg.σ Pr.root).Th ∧ att.timeout = false ∧
        (((tr.state p kX).fg.σ Pr.root).previousHeightJustified →
          (((tr.state p kX).fg.σ Pr.root).hj, ((tr.state p kX).fg.σ Pr.root).J) ∈
            ((tr.state p kX).fg.σ Pr.root).pending →
          att.fin = some (((tr.state p kX).fg.σ Pr.root).hj,
            ((tr.state p kX).fg.σ Pr.root).J))) :
    AnchorStep tr H A X := by
  have hst := anchor_height_step_or_crossed hrun hs hv hp hX hvx hkb hpar hPr hAPr hrows
  obtain ⟨-, hXm, he⟩ := Healing.accept_of_proposesAt hrun hs.noColl hp hX
  have hA := Healing.mem_of_honest_anc hrun hs.noColl hp
    (Healing.honest_anc_of_store_anc hp hAPr) hPr
  rw [he] at hst
  exact ⟨p, hp, kX, kX + 1, hA, hXm, hst⟩

/-- **The anchor window advance.** Three anchor steps `P i → P (i+1)` give
`σ[P₀].h + 3 ≤ σ[P₃].h` at every honest store that holds the four anchors. -/
theorem anchor_window_advance (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {P : Fin 4 → SA.Blk sp.n (List (FG.Att sp.n))}
    (hmem : ∀ i, P i ∈ (tr.state y k).fg.tree)
    (hstep : ∀ i : Fin 3, AnchorStep tr H (P i.castSucc) (P i.succ)) :
    ((tr.state y k).fg.σ (P 0).root).h + 3 ≤ ((tr.state y k).fg.σ (P 3).root).h := by
  have key : ∀ i : Fin 3, ((tr.state y k).fg.σ (P i.castSucc).root).h + 1 ≤
      ((tr.state y k).fg.σ (P i.succ).root).h := by
    intro i
    obtain ⟨z, hz, j, j', hA, hX, hle⟩ := hstep i
    rw [Healing.σ_eq_honest hrun hnc hy hz (hmem _) hA,
      Healing.σ_eq_honest hrun hnc hy hz (hmem _) hX]
    exact hle
  have h0 : ((tr.state y k).fg.σ (P 0).root).h + 1 ≤ ((tr.state y k).fg.σ (P 1).root).h :=
    key 0
  have h1 : ((tr.state y k).fg.σ (P 1).root).h + 1 ≤ ((tr.state y k).fg.σ (P 2).root).h :=
    key 1
  have h2 : ((tr.state y k).fg.σ (P 2).root).h + 1 ≤ ((tr.state y k).fg.σ (P 3).root).h :=
    key 2
  omega

/-- **Window coverage from an anchor window, through a horizon.** Four honest anchors `P i` at
strictly increasing slots `s i` (guards of `window_anchors_chain_upTo`), three anchor steps, and
`(P 3).slot ≤ (P 0).slot + δt`. For an honest `y` holding the four anchors at cut `k`, the block
`F` of root `σ[P₃].F` is held by `y` and `P₀ ⪯ F` in the honest blocks. No window service,
window advance or density premise. -/
theorem cacheCoverage_of_anchor_window_upTo {g ΔF a b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {s : Fin 4 → Nat}
    {P : Fin 4 → SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ∀ i, Healing.HonestProposalRun tr H proposer (s i) (P i)) (hs : StrictMono s)
    (hR : Healing.drainTime sp a ≤ sp.ts (s 0)) (hb : sp.ts (s 3) ≤ b)
    (hadj : s 3 = s 2 + 1 → sp.ts (s 2) + 6 * sp.Δ ≤ b)
    (hstep : ∀ i : Fin 3, AnchorStep tr H (P i.castSucc) (P i.succ))
    (hsl : (P 3).slot ≤ (P 0).slot + sp.toParams.fg.δt) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    (hB₃ : P 3 ∈ (tr.state y k).fg.tree) :
    ∃ F, (tr.state y k).fg.blocks ((tr.state y k).fg.σ (P 3).root).F = some F ∧
      Anc (tr.HonestBlocks H) (P 0) F := by
  have hch := window_anchors_chain_upTo hp hc hP hs hR hb hadj
  have hmem : ∀ i, P i ∈ (tr.state y k).fg.tree := fun i =>
    Healing.mem_of_honest_anc hp.run hp.noColl hy (hch i 3 (Fin.le_last i)) hB₃
  obtain ⟨F, hF, hAF⟩ := Store.coverage_of_anchor_window
    (Compose.fg_reachable hp.run.toLocalRun hy k) hB₃
    (Healing.store_anc_of_honest_anc hp.run hp.noColl hy (hch 0 3 (by decide)) hB₃)
    (anchor_window_advance hp.run hp.noColl hy hmem hstep) hsl
  exact ⟨F, hF, Healing.honest_anc_of_store_anc hy hAF⟩

end Obligations

end Consensus.Goldilocks

end
