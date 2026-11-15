module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Healing
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.RiseWindow
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache

public section

/-! # Generic healing rounds

The healing leaves over any healing supplier: for any node AC `A`, run predicate
`runs : ACRun A sg` and supplier `O : ACHealing A sg runs`, each theorem's type is the generic leaf
Prop over `O` (Milestones/Statements/Generic/Healing.lean). The proofs read the node run through
`ACRun.run_local` and apply the run-level leaves of `HealingLeaves`.

Leaves 8 and 9 (`rounds_le_warm_proposal_at_of_healing`, `report_kind_of_warm_at_of_healing`)
are proved over any `ACHealing`: its `proposal_floor` puts a warm honest proposal at or above the
window floor. At a constant merged key `v ≥ 2HZ` the proposer's store has
`HZ + 1 ≤ floor + r(v)` (`Healing.le_floor_add_riseRounds`); a report at the proposal's height
above it is at or above the reader's floor, so above `h_j`, or at it with `J` below the report
(`ACHealing.report_in_frame`).
-/

namespace Consensus.Goldilocks.Generic

/-! ## Leaves 8 and 9, warm proposals in a frame window -/

section WarmProposal

variable {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n} {runs : ACRun A sg}

open Healing.Growing (HZ)

/-- An honest proposal below a block held at an honest reader is in the reader's tree, below that
block in the reader's store, with the proposer's replay state after its proposal. -/
private theorem proposal_below_held_at {cm proposer dg H tr}
    (hrun : runs.Run cm proposer dg H tr) (hnc : Compose.NoCollRun dg tr) {z : Fin P.n}
    {kB : Nat} {B : A.Blk} (hz : z ∈ H (tr.time kB)) (hB : tr.ProposesAt z kB B) {y : Fin P.n}
    {i : Nat} {R : A.Blk} (hy : y ∈ H (tr.time i)) (hBR : Anc (tr.HonestBlocksAt H) B R)
    (hR : R ∈ (tr.state y i).fg.tree) :
    B ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc B R ∧
      (tr.state z (kB + 1)).fg.σ B.root = (tr.state y i).fg.σ B.root := by
  have hrl := runs.run_local hrun
  have hle : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrl.time_mono hq.le
  have hi0 := hrl.time_nonneg i
  have hBm := proposal_mem_at_from hrl (runs.run_requirements hrun) (runs.run_root hrun) hnc hz hB
  have hBy := mem_of_honest_anc_at_from hrl hnc hi0 hle hy hBR hR
  exact ⟨hBy, store_anc_of_honest_anc_at_from hrl hnc hi0 hle hy hBR hR,
    σ_eq_honest_at_from hrl hnc (hrl.time_nonneg kB) (fun q hq => hrl.time_mono (by omega)) hz
      hi0 hle hy hBm hBy⟩

/-- Leaf 8: a warm proposal at a constant merged key `v ≥ 2HZ` is at most `r(v)` rounds below
`HZ + 1`. The supplier's `proposal_floor` puts it at or above the window floor, and the proposer's
store has `HZ + 1 ≤ floor + r(v)` (`Healing.le_floor_add_riseRounds`). -/
theorem rounds_le_warm_proposal_at_of_healing (O : ACHealing A sg runs) :
    rounds_le_warm_proposal_at A sg O := by
  intro cm proposer dg H tr g af len u floor v kindJ J B z kB hrun hnc hwin hK hv hlo hhi hz
    hdes hB hBs hf
  have hfl := O.proposal_floor hrun hnc hwin hz hdes hB hBs hlo hhi hf
  have hrl := runs.run_local hrun
  have ht : tr.time kB = P.slotTime u := by rw [hB.2.2, hBs]
  have hzk : z ∈ H (tr.time kB) := ht ▸ hz
  have hkey := hK z kB hzk (ht ▸ hlo) (ht ▸ hhi)
  have hpos := Healing.Store.hj_lt_hmax_of_reachable
    (fg_reachable_at_from hrl (hrl.time_nonneg kB) (fun q hq => hrl.time_mono hq.le) hzk)
  rw [frameKey'_eq] at hkey
  have h := Healing.le_floor_add_riseRounds (tr.state z kB).fg (by omega) (HZ := HZ tr H g)
    (by rw [hkey]; exact hv)
  rw [hkey, hwin.floor_eq z kB hzk (ht ▸ hlo) (ht ▸ hhi)] at h
  have hrr : riseRounds (HZ tr H g) v = Healing.riseRounds (HZ tr H g) v := by
    rw [Healing.riseRounds_eq]
    rfl
  rw [hrr]
  omega

/-- Leaf 9: a report in the window at the height of a warm honest proposal below it is above the
reader's `h_j`, or at it with `J` below the report. The supplier's `proposal_floor`, read in the
reader's store, puts the report at or above the head-height floor; the root kind and
`ACHealing.report_in_frame` decide the case. -/
theorem report_kind_of_warm_at_of_healing (O : ACHealing A sg runs) :
    report_kind_of_warm_at A sg O := by
  intro cm proposer dg H tr lo hi floor u kindJ J B R z kB y i hrun hnc hframe hz hdes hB hBs
    hlo hhi hf hy hR hBR hil hih heq
  have hrl := runs.run_local hrun
  have hfl := O.proposal_floor hrun hnc hframe hz hdes hB hBs hlo hhi hf
  have ht : tr.time kB = P.slotTime u := by rw [hB.2.2, hBs]
  obtain ⟨hRm, hroot⟩ := O.report_in_frame hrun hy hR
  obtain ⟨-, -, hσ⟩ := proposal_below_held_at hrun hnc (ht ▸ hz) hB hy hBR hRm
  rw [hσ] at hfl
  have hfloor : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ R.root).h := by
    rw [hframe.floor_eq y i hy hil hih, heq]
    exact hfl
  have hj := Healing.Store.hj_lt_hmax_of_reachable
    (fg_reachable_at_from hrl (hrl.time_nonneg i) (fun q hq => hrl.time_mono hq.le) hy)
  rw [← heq]
  by_cases hc : (tr.state y i).fg.Contest
  · have he := hc.1
    rw [Store.headHeightFloor, ite_eq_left hc] at hfloor
    exact Or.inl (by omega)
  · rw [Store.headHeightFloor, ite_eq_right hc] at hfloor
    by_cases he : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1
    · have hr' : (tr.state y i).fg.fcRoot = (tr.state y i).fg.J := ite_eq_left ⟨he, hc⟩
      rw [hr'] at hroot
      by_cases hlt : (tr.state y i).fg.hj < ((tr.state y i).fg.σ R.root).h
      · exact Or.inl hlt
      · exact Or.inr ⟨by omega, hroot⟩
    · exact Or.inl (by omega)

end WarmProposal

end Consensus.Goldilocks.Generic
