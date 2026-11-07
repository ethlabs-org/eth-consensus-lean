module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Interface

public section

/-! # Pending healing interface of the growing network transport

Definitions the growing network transport consumes whose home modules are not on this branch
yet, under their agreed names:

* the healing target `Healing.Growing.Pending.ResetService` of the reset-service supplier (in a
  namespace of its own, a copy of the agreed definition of
  `Lemmas/Growing/Healing/Retention/Defs`).

Each definition here is a copy of the agreed one; this module is deleted when the home module
lands. -/

namespace Consensus.Goldilocks.Healing.Growing.Pending

section Reset
variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- The service of a healthy run from GST `g` under growing faults: messages, blocks and
acceptance relay at the protocol delay, and signed attestations at `ΔF` at calls by `b`. Senders
are honest at their event, recipients at their call. -/
structure ResetService (g ΔF b : Time) : Prop where
  deltaF : 0 < ΔF
  message : ∀ x i m, x ∈ H (tr.time i) → tr.SendOrAdmitAt x i m →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      tr.MsgDeliveredBy y j (tr.time i) (max (tr.time i) g) m
  block : ∀ x i B, x ∈ H (tr.time i) → (tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B) →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      tr.BlockDeliveredBy y j (tr.time i) (max (tr.time i) g) B
  relay : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → g ≤ tr.time i →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j (max (tr.time i) g) B
  signedRow : ∀ x i att, x ∈ H (tr.time i) → tr.SignAt x i att →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.time j ≤ b →
      tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
      ∃ k ≤ j, tr.ProcessAttAt y k att ∧
        tr.time k < tr.deadline y k (max (tr.time i) g) ΔF

end Reset

end Consensus.Goldilocks.Healing.Growing.Pending

end
