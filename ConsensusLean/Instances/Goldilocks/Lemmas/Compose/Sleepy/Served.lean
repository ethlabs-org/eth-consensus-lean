module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Sleepy

public section

/-! # Goldilocks under `Sleepy`: the served head (S4) and the record step (G3)

workbench#11 §5, the facts the Service milestone reads (`ServedFacts`, in
`Lemmas/Compose/Service/Sleepy`), from `SleepyInvariant`:

* **The record step** (`record_step`, G3, at every honest cut): a record write takes an origin
  `C` of the frame, compatible with the old record (genesis or an origin, in the node's tree);
  it keeps the record when `C` is below it in the frame, and otherwise the old record is below
  `C` (below `Σ.F ⪯ C` when it left the frame). Restarts keep the record.
* **The served head** (`served_head_support`, G1, G2, at a cut after the update of slot
  `slot(t) − 2` or `slot(t) − 1` with no restart since, awake and joined): the anchor (the
  deepest of the live lock blocks and `fc_root`, all on the origin chain) is compatible with the
  record `R`. If `R` was
  written by an optimistic check of the current slot, or of the previous one before its
  `t_s + 2Δ`, its fast lock is still live at `R` (full viability keeps it there), so `R ⪯` the
  anchor. Otherwise `R`'s label is below the latest view's slot: every honest vote of that slot
  extends `R` (S2), the more than `f` cast by the validators awake and joined at its `t + Δ`
  reach the served node and are resolved (no restart since the update), and only faulty seats
  remain, so the supporters are a strict majority of the voters; `R` is fully viable (S3). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time}

/-- **G3, the record step**: at every cut of an honest node, the record moves to a descendant
(inside the honest blocks). -/
theorem record_step (hinv : SleepyInvariant tr H) (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    ∀ E ∈ tr.HonestBlocks H, E.root = (tr.state y i).ac.latestConfirmed →
      ∃ E' ∈ tr.HonestBlocks H, E'.root = (tr.state y (i + 1)).ac.latestConfirmed ∧
        Anc (tr.HonestBlocks H) E E' := by
  sorry

/-- **G1, G2 at a served cut**: at a cut of an honest node awake and joined at its time that has
run the update of slot `slot(t) − 2` or `slot(t) − 1` with no restart since (A1.6's condition,
and A1.7's in the slot after the proposal's), the record's block has `HeadSupport`. -/
theorem served_head_support (hinv : SleepyInvariant tr H) (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    (hc : tr.IsCall y i) (hw : tr.awake y (tr.time i)) (hj : tr.JoinedAt y (tr.time i))
    {s' : Nat} (hs' : sp.slot (tr.time i) ≤ s' + 2) (hu : UpdatedNoRestart tr y i s')
    {R : SA.Blk sp.n (List (FG.Att sp.n))} (hR : RecordAt tr y i R) :
    HeadSupport tr y i R := by
  sorry

/-- **The served-cut facts under `Sleepy`** (`ServedFacts`, the target of the Service
milestone's `served_facts`). -/
theorem sleepy_served_facts (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {y : Fin sp.n} (hy : y ∈ H) {i : Nat} (hs : ServedAt tr y i) :
    ServedFacts tr H y i :=
  have hinv := sleepy_invariant hrun hnc hsl
  have ⟨hc, hw, hj, _, hs', hu⟩ := hs
  ⟨fun _ hR => served_head_support hinv hrun hnc hsl hy hc hw hj hs'.ge hu hR,
    record_step hinv hrun hnc hy i⟩

end Consensus.Goldilocks.Compose

end
