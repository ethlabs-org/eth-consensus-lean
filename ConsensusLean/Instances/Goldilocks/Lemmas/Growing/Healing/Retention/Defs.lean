module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Run

public section

/-! # Finite healing service and reset premises under growing faults

Delivery remains owed after its sender is compromised. A receiver is required to be honest
at its receiving call; only signed-row service is restricted to the finite horizon.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- GST service, with signed rows consumed by the finite horizon. -/
structure ResetService (g ΔF b : Time) : Prop where
  deltaF : 0 < ΔF
  message : ∀ x i m, x ∈ H (tr.time i) → tr.SendOrAdmitAt x i m →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      tr.MsgDeliveredBy y j (tr.time i) (max (tr.time i) g) m
  block : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B →
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

/-- The shared HS premises through a finite observation horizon. -/
structure HSSharedUpTo
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g ΔF b : Time) : Prop where
  noColl : Compose.NoCollRun dg tr
  genesisRoot : (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg
  sync : ResetService tr H g ΔF b
  awake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t
  faults : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1
  noRestart : ∀ y k, y ∈ H (tr.time k) → tr.RestartAt y k →
    tr.time k ≤ b → tr.time k ≤ gbar g
  timeoutDelay : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.δt : Time)

/-- A finite reset and service, with node honesty read separately at each cut. -/
structure ResetPremisesUpTo (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g ΔF a b : Time) : Prop where
  run : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
  noColl : Compose.NoCollRun dg tr
  sync : ResetService tr H g ΔF b
  awake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t
  faults : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1
  reset : IsReset tr H g a
  reset_le : a ≤ b
  snapshot : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g) ∧ tr.time k ≤ b

end Consensus.Goldilocks.Healing.Growing

end
