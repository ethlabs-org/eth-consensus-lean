module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AnchorPrefix
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FreshLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Source
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.PreAdvanceFacts
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Finite drain reports

`report_kind_of_floor`: the kind of an actual drain report at the window floor. This is not a
reset-time or joint coefficient-envelope theorem. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A floor-height source above the fork-choice root satisfies the kind alternative (kind F, or
kind J with `Σ.J ⪯` the source), including Contest and the equal-height kind-J case. -/
theorem report_kind_of_floor
    (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hh : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ R.root).h)
    (hroot : (tr.state y i).fg.Anc (tr.state y i).fg.fcRoot R) :
    (tr.state y i).fg.hj < ((tr.state y i).fg.σ R.root).h ∨
      ((tr.state y i).fg.hj = ((tr.state y i).fg.σ R.root).h ∧
        (tr.state y i).fg.Anc (tr.state y i).fg.J R) := by
  have hj := hj_lt_hmax hrun hy i
  by_cases hc : (tr.state y i).fg.Contest
  · have he := hc.1
    rw [Store.headHeightFloor, ite_eq_left hc] at hh
    exact Or.inl (by omega)
  · rw [Store.headHeightFloor, ite_eq_right hc] at hh
    by_cases he : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1
    · have hr : (tr.state y i).fg.fcRoot = (tr.state y i).fg.J :=
        ite_eq_left ⟨he, hc⟩
      rw [hr] at hroot
      by_cases hlt : (tr.state y i).fg.hj < ((tr.state y i).fg.σ R.root).h
      · exact Or.inl hlt
      · exact Or.inr ⟨by omega, hroot⟩
    · exact Or.inl (by omega)

end Consensus.Goldilocks.Healing

end
