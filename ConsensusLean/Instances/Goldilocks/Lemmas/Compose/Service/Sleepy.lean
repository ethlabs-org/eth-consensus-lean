module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Service

public section

/-! # Goldilocks runs under `Sleepy`: the facts the Service milestone reads (interface)

The Sleepy safety induction from time `0` (claims A1.6, its "own induction from time 0"; the same
induction is R.1, `sleepySafe`; workbench#11, `Lemmas/Compose/Sleepy`). This file holds what A1.6
and A1.7 read of it, node-local at one cut of `y`:

* `HeadSupport R` (G1, G2): the anchor is compatible with `R`, and `R` is at or below the anchor,
  or `R` is in the viable tree with a strict majority of the latest view's voters as supporters
  (with `SA.anc_acHead`, the head extends `R`, and `ac_confirmed` is the record's block);
* `ServedFacts` at a cut where `y` is served (`ServedAt`): `HeadSupport` of the record's block,
  and the record step (G3: across the cut the record moves to a descendant); supplied by
  `sleepy_served_facts` (`Lemmas/Compose/Sleepy/Served`, which imports this file);
* `included_facts` at the cuts of A1.7: the record's block extends the honest proposal and has
  `HeadSupport`, or, when the record has left the frame, `Σ.F` extends the proposal. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **G1, G2 for `R` at cut `i` of `y`**: the anchor is compatible with `R`; `R` is at or below
it, or `R` is viable and supported by a strict majority of the latest view's voters. -/
structure HeadSupport (tr : GoldilocksTrace sp ro) (y : Fin sp.n) (i : Nat)
    (R : SA.Blk sp.n (List (FG.Att sp.n))) : Prop where
  /-- G1: the anchor is compatible with `R`. -/
  anchor_compatible : Compatible (Node.frame (tr.state y i)).tree
    (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) (tr.time i)) R
  /-- G2: `R` is at or below the anchor, or viable with a strict supporter majority. -/
  support : (Node.frame (tr.state y i)).Anc R
      (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) (tr.time i)) ∨
    (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
      (SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
          (tr.time i)).1.votes).ncard <
        2 * (SA.supporters (Node.frame (tr.state y i))
          (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) (tr.time i)).1
          (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) (tr.time i)).2
          R).ncard)

/-- **The served-cut facts** of `y` at cut `i`: G1/G2 for the record's block, and the record
step (G3). -/
structure ServedFacts (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (y : Fin sp.n) (i : Nat) :
    Prop where
  /-- G1, G2 for the record's block. -/
  head : ∀ R, RecordAt tr y i R → HeadSupport tr y i R
  /-- G3: across the cut, the record moves to a descendant (inside the honest blocks). -/
  record_step : ∀ E ∈ tr.HonestBlocks H, E.root = (tr.state y i).ac.latestConfirmed →
    ∃ E' ∈ tr.HonestBlocks H, E'.root = (tr.state y (i + 1)).ac.latestConfirmed ∧
      Anc (tr.HonestBlocks H) E E'

/-- **The inclusion facts under `Sleepy`** (open: workbench#12, the adoption of an honest
proposal `P` of slot `s` by the update of slot `s`, over the Sleepy invariant). At a cut of A1.7,
every record block in the frame extends `P` and has `HeadSupport`; when the record has left the
frame, `Σ.F` extends `P`. -/
theorem included_facts {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF)
    (hg : (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k))
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} (hc : tr.IsCall y i) (ht : sp.ts s + 6 * sp.Δ ≤ tr.time i)
    (hyw : tr.awake y (tr.time i)) (hyj : tr.JoinedAt y (tr.time i))
    (hyw₀ : tr.awake y (sp.ts s + 6 * sp.Δ)) (hyj₀ : tr.JoinedAt y (sp.ts s + 6 * sp.Δ))
    (hnr : ∀ k', tr.RestartAt y k' → sp.ts s + 6 * sp.Δ < tr.time k' → tr.time k' ≤ tr.time i →
      False)
    (hu : UpdatedNoRestart tr y i s) :
    (∀ R, RecordAt tr y i R → Anc (tr.HonestBlocks H) P R ∧ HeadSupport tr y i R) ∧
      ((¬ ∃ R, RecordAt tr y i R) → Anc (tr.HonestBlocks H) P (Node.frame (tr.state y i)).F) := by
  sorry

end Consensus.Goldilocks.Compose

end
