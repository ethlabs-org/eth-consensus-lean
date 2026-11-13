module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Service
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing

@[expose] public section

/-! # Goldilocks milestone Service under growing faults (statements)

A1.6 and A1.7 (`Statements/Compose/Service`) for a time-indexed honest set `H`, over
`Growing.GoldilocksRun` under `Sleepy` with look-ahead `Regimes.Growing.ahead`:

* **A1.6**: at a cut of a node honest at its time, served as in `ServedAt`, the head extends the
  record and `ac_confirmed` is it; while the node stays served and honest, its record only moves to
  a descendant inside the blocks held while honest.
* **A1.7**: an honest proposal of slot `s` by a proposer joined at its proposal and still honest
  `hold` after it is in the confirmed tip of every node honest at a later served cut, as in the
  static statement.

At `H := fun _ => H₀` each implies its static counterpart (`Lemmas/Growing/Statements/Regimes`).

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)
open Regimes.Growing (ahead hold)

/-- **A1.6 under growing faults, head extends the record.** -/
def HeadExtendsRecord : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (ΔF : Time),
    sp.committeeSize = sp.n →
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → NoCollRun dg tr →
    tr.SleepyRunAt H ΔF (ahead sp) →
    ∀ y i, y ∈ H (tr.time i) → ServedAt tr y i → ∀ R, RecordAt tr y i R →
      ((Node.frame (tr.state y i)).Anc R (tr.headAt y i) ∧ tr.confirmedAt y i = R) ∧
      ∀ i', i ≤ i' → y ∈ H (tr.time i') → (∀ k, i ≤ k → k ≤ i' → tr.IsCall y k → ServedAt tr y k) →
        ∀ R', RecordAt tr y i' R' → Anc (tr.HonestBlocksAt H) R R'

/-- **A1.7 under growing faults, inclusion.** The proposer is honest through `hold` after its
proposal; the reader is honest at its cut. -/
def Inclusion : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (ΔF : Time),
    sp.committeeSize = sp.n →
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → NoCollRun dg tr →
    tr.SleepyRunAt H ΔF (ahead sp) →
    ∀ p k (P : SA.Blk sp.n (List (FG.Att sp.n))) (s : Nat), p ∈ H (tr.time k + hold sp) →
      tr.ProposesAt p k P → P.slot = s → SA.joined sp (tr.state p k).ac (tr.time k) →
      ∀ y i, y ∈ H (tr.time i) → tr.IsCall y i → tr.JoinedAt y (tr.time i) →
        (∀ k', tr.RestartAt y k' → sp.ts s + 6 * sp.Δ < tr.time k' → tr.time i < tr.time k') →
        UpdatedNoRestart tr y i s →
        Anc (tr.HonestBlocksAt H) P (tr.confirmedAt y i)

end Consensus.Goldilocks.Compose.Growing

end
