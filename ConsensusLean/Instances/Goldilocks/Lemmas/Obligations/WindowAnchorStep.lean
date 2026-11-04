module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalSignedUpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum

public section

/-! # Goldilocks Obligations: the anchor height step (#137, fixed `δt`)

consensus-lean#137, corrected owner intent (2026-11-02): `δt` is a fixed constant, independent
of the honest-proposer gap. Honest proposers are used only at the window anchors; the slots
between anchors may all be faulty. No density premise (`hM4`) is used here.

* `anchor_height_step`: an honest anchor `X` whose parent `Pr` is above the previous anchor `A`
  (in the proposer's store at the proposal cut), with a quorum of honest target rows for the
  entry of `σ[Pr]` signed by `v` (`v + Δ_F ≤ t_{kX}`), is one height above `A` on its post-store.
  The anchor justifies `σ[Pr].h` (`justify_of_signed_rows'_upTo`), and `h_j < h`.
* `anchor_height_step_or_crossed`: the same, with the rows needed only when `σ[Pr]` is still at
  the height of `A`; if a block between `A` and `Pr` already crossed, the step holds by
  monotonicity.

The row premise (`hsig`) is the explicit availability premise at the anchor: record usability
and inclusion of the entry's target rows. Its timing content is that the entry is younger than
`δt` while the rows are signed (honest validators sign target rows, not timeouts). -/

namespace Consensus.Goldilocks.Obligations

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The anchor height step.** An honest anchor `X` (proposal cut `kX`, parent `Pr`) with
`A ⪯ Pr` in the proposer's store and a quorum of honest target rows for `σ[Pr]`'s entry signed by
`v`: `σ[A].h + 1 ≤ σ[X].h` on the post-store of the cut. -/
theorem anchor_height_step (hrun : GoldilocksRun proposer dg H tr) {g ΔF v b : Time}
    (hs : Healing.HSSharedUpTo tr H dg g ΔF b) (hv : gbar g ≤ v)
    {p : Fin sp.n} (hp : p ∈ H) {kX : Nat} {A X Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : tr.ProposesAt p kX X) (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b)
    (hpar : X.parent = some Pr.root) (hAPr : (tr.state p kX).fg.Anc A Pr)
    (S : Finset (Fin sp.n)) (hSH : ∀ v ∈ S, v ∈ H) (hS : sp.toParams.fg.q ≤ S.card)
    (hsig : ∀ y ∈ S, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧
      att.h = ((tr.state p kX).fg.σ Pr.root).h ∧
      att.T = ((tr.state p kX).fg.σ Pr.root).Th ∧ att.timeout = false ∧
      (((tr.state p kX).fg.σ Pr.root).previousHeightJustified →
        (((tr.state p kX).fg.σ Pr.root).hj, ((tr.state p kX).fg.σ Pr.root).J) ∈
          ((tr.state p kX).fg.σ Pr.root).pending →
        att.fin = some (((tr.state p kX).fg.σ Pr.root).hj, ((tr.state p kX).fg.σ Pr.root).J))) :
    ((tr.state p kX).fg.σ A.root).h + 1 ≤ ((tr.post kX).fg.σ X.root).h := by
  have hj := (Healing.justify_of_signed_rows'_upTo hrun hs hv hp hX hvx hkb hpar S hSH hS hsig).1
  have hle := Healing.h_le_of_store_anc (Compose.fg_reachable hrun.toLocalRun hp kX) hAPr
  obtain ⟨-, hXm, he⟩ := Healing.accept_of_proposesAt hrun hs.noColl hp hX
  have hlt := Healing.Store.hj_lt_h (Compose.fg_reachable hrun.toLocalRun hp (kX + 1)) hXm
  rw [← he] at hlt
  omega

/-- **The anchor height step, rows only at the old height.** As `anchor_height_step`, but the
rows are needed only when `σ[Pr]` is still at the height of `A`: otherwise a block between `A`
and `Pr` already crossed, and `σ[A].h + 1 ≤ σ[Pr].h ≤ σ[X].h`. -/
theorem anchor_height_step_or_crossed (hrun : GoldilocksRun proposer dg H tr) {g ΔF v b : Time}
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
    ((tr.state p kX).fg.σ A.root).h + 1 ≤ ((tr.post kX).fg.σ X.root).h := by
  have hr := Compose.fg_reachable hrun.toLocalRun hp kX
  have hle := Healing.h_le_of_store_anc hr hAPr
  by_cases heq : ((tr.state p kX).fg.σ Pr.root).h = ((tr.state p kX).fg.σ A.root).h
  · obtain ⟨S, hSH, hS, hsig⟩ := hrows heq
    exact anchor_height_step hrun hs hv hp hX hvx hkb hpar hAPr S hSH hS hsig
  · obtain ⟨-, hXm, he⟩ := Healing.accept_of_proposesAt hrun hs.noColl hp hX
    have hXH : X ∈ tr.HonestBlocks H := ⟨_, hp, kX + 1, hXm⟩
    have hPrX : Anc (tr.HonestBlocks H) Pr X := .single ⟨⟨_, hp, kX, hPr⟩, hXH, hpar⟩
    have hPrm := Healing.mem_of_honest_anc hrun hs.noColl hp hPrX hXm
    have hle' := Healing.h_le_of_store_anc (Compose.fg_reachable hrun.toLocalRun hp (kX + 1))
      (.single ⟨hPrm, hXm, hpar⟩)
    rw [← Healing.σ_eq_honest hrun hs.noColl hp hp hPr hPrm] at hle'
    rw [he]
    omega

end Consensus.Goldilocks.Obligations

end
