module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Query
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Reader
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.S5Step
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageGateSlot
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage under growing faults: the repair of a ready reader's read

`Compose.Growing.outage_lock_protected`: on a node trace, from the lock module's premise package
`D` and post-stop service, a block below the protected block `P` is below the read of every
reader ready at a strict read point from `b₁ + 9Δ`. The lock invariant comes from the restored-vote
step (`outage_lock_inv_at`, `outage_s5_step_at`, the receiver service from post-stop service), the
reader's latest gate from E0–E4 (`outage_reader_gate_at`), and the read from the reader bridge
(`outage_reader_bridge_at`).

`outage_protected_at`: from the recovery point, the confirmed read of every source ready at `T` is
a prefix of the read of every reader ready at `t`. The source is armed (`outage_arming_at`), the
package is `outageLockPremises_of_arming_at`, and ancestry of the two read tips is the engine read
prefix (`outage_reader_prefix_at`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- **Protection on a node trace**: from the premise package `D` and post-stop service, every
block below `P` is below the read of a reader ready at a strict read point from `b₁ + 9Δ`, with
the population count at the read time and the committee counts up to it. -/
theorem outage_lock_protected (D : OutageLockPremises tr H proposer dg ini)
    (hpost : Consensus.Goldilocks.Generic.PostStopService tr H D.b₁)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : Anc (tr.HonestBlocksAt H) B D.P)
    {b c t : Time} (hc : Regimes.catchUp sp ≤ c) (hrec : D.b₁ + 9 * sp.Δ ≤ t)
    {y : Fin sp.n} {j : Nat} (hR : Consensus.Goldilocks.Generic.ReadyReadPoint tr H b c y j t)
    (hstrict : t < tr.time j) (hBt : SleepyBoundsFrom tr H 0 t)
    (hBK : ∀ d ≤ t, CommitteeBoundsFrom tr H D.K 0 d) :
    Anc (tr.HonestBlocksAt H) B (Regimes.readAfter tr y j t) := by
  have hb₁ : 0 ≤ D.b₁ := by
    have := ts_natCast_nonneg (sp := sp) D.j₀
    have := sp.toParams.hΔ
    linarith [D.hj₀.1, D.hb₀]
  obtain ⟨G⟩ := outage_reader_gate_at D.hrun hb₁ hc hrec hR hstrict
  have hinv := outage_lock_inv_at D (outage_s5_step_at D fun y =>
    Simulation.receiverServiceAfterAt_of_postStop D.hrun hpost y)
  exact outage_reader_bridge_at D hpost hinv hB hR.1.1 hR.1.2.2.1 G hBt hBK

end Consensus.Goldilocks.Compose.Growing

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Blocks Shape

variable {S : Setup} {A : ContractAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

/-- **Slow-only recovery for ready readers under growing faults**: from the recovery point, the
read of every source ready at `T` is a prefix of the read of every reader ready at `t`. -/
theorem outage_protected_at (Q : OutageQueryAt S A V) :
    (chainTrace Q.run.2).ProtectedReadyFrom Q.duration .confirmed
      (resilienceTarget schema .confirmed) Q.T
      ((Sys (goldilocks S) V).recoveryAt (K S A) Q.stop Q.run) := by
  intro v hv t ht hth w hw
  have hTs : Q.T ≤ Q.start := by
    obtain ⟨-, hlag, -, -⟩ := Q.outage.times
    have : (0 : Time) ≤ ((K S A).params.lag : Time) * Q.run.1.ΔAC := by
      have := Q.run.1.ΔAC_pos; positivity
    change Q.T + _ * Q.run.1.ΔAC ≤ Q.start at hlag
    linarith
  have hst : Q.start ≤ Q.stop := Q.outage.times.2.2.1
  have hrec : Q.stop + 9 * Q.run.1.ΔAC ≤ t := by
    change Q.stop + ((9 : Nat) : Time) * Q.run.1.ΔAC ≤ t at ht
    push_cast at ht
    exact ht
  have hΔ := Q.run.1.ΔAC_pos
  have hst' : Q.stop ≤ t := by linarith
  have hsh : Q.start ≤ Q.run.2.horizon := hst.trans (hst'.trans hth)
  have hTh : Q.T ≤ Q.run.2.horizon := hTs.trans hsh
  have ht0 : 0 ≤ t := by linarith [outage_stop_nonneg Q.outage]
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have service := outage_pre_service_at Q
  obtain ⟨ar⟩ := outage_arming_at Q service v hv hTh
  obtain ⟨hR, hstrict⟩ := outage_readyReadPoint_at Q ht0 hth hw
  have h := Compose.Growing.outage_lock_protected
    (outageLockPremises_of_arming_at Q service hsh ar)
    (by rw [outageLockPremises_of_arming_at_b₁]; exact outage_postStopService_at Q)
    (by rw [outageLockPremises_of_arming_at_P]; exact ar.tip_anc) (outage_duration_supply_at Q)
    (by rw [outageLockPremises_of_arming_at_b₁]; exact hrec) hR hstrict (Q.bounds hth)
    (fun d hd => by
      rw [outageLockPremises_of_arming_at_K]; exact Q.boundsK hrun (hd.trans hth))
  refine outage_reader_prefix_at Q hv (hTs.trans (hst.trans hst')) hth hw ?_
  rw [← ar.tip_eq]
  exact h

end Consensus.Goldilocks.Obligations.Growing

end
