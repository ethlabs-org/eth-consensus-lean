module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageSuppliers

public section

/-! # Goldilocks outage: the repair of a ready reader's read (slow-only recovery)

`outage_repair` and its consumer `outage_protected`, moved unchanged from `OutageSuppliers.lean`
so that the assembly can import the arming, the lock module, the S5 suppliers and the reader
bridge, which all import `OutageSuppliers.lean`. -/

namespace Consensus.Goldilocks.Refinement
open Blocks Shape
variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- OPEN slow-only recovery for ready readers from the recovery point
`b₁ + recovery·Δe` (`recovery = 18`). Open obligations (workbench
`outage_slow_only_delta.md`; O3 from 9f5d6a3 `outage_recovery_delay-readback-opus.md`
§2, §4):
* O1, slow lock formation at labels `j₀ − 1` (armed by `b₀` under the lag
  `8k + 12`) and `j₀ = coverLabel b₀`, for the honest validators awake at the
  no-sleep window start;
* O2, effective lock retention of both locks, including the base handoff at
  slots `j₀ + 1` (pre-`b₀` votes) and `j₀ + 2` (votes under the live `j₀ − 1`
  lock), VA for the `j₀ − 1` anchor, and both unlock paths;
* O3, the recovery at the reader gates: (i) the `k − 1` conflicting-label
  count, with O2/VA, S-vote and η-sleepy participation at `j₀`; (ii) the
  cohort count of `System.Outage` at the reader gates; (iii) a veto is
  harmless: it implies the record extends the proposal (from
  `lockInv_of_reachable`, the live-lock chain and OB-F; this replaces a false
  no-veto comparability lemma); (iv) S5: restored heads `⪰` the record at
  every later `t`;
* O4, the reader bridge: `Ready` at `t` gives the post-recovery gate and view.
An armed record alone is not a proof of protection. -/
theorem outage_repair (Q : OutageQuery S A V)
    (service : Compose.SleepyServiceBefore Q.trace (honestKeys S Q.run.2) Q.params.Δ Q.start)
    (v : V) (hv : Q.run.2.point.Ready Q.duration v Q.T)
    (armed : OutageArmedRead S A V Q v)
    (t : Time) (ht : (Sys (family S) V).recoveryAt (K S A) Q.stop Q.run ≤ t)
    (hth : t ≤ Q.run.2.horizon)
    (w : V) (reader : Q.run.2.point.Ready Q.duration w t) :
    (chainTrace Q.run.2).readAt .confirmed v Q.T <+:
      (chainTrace Q.run.2).readAt (resilienceTarget schema .confirmed) w t := by
  sorry

/-- Assembly preserves the reader and time quantifiers of persists. -/
theorem outage_protected (Q : OutageQuery S A V) :
    (chainTrace Q.run.2).ProtectedReadyFrom Q.duration .confirmed
      (resilienceTarget schema .confirmed) Q.T
      ((Sys (family S) V).recoveryAt (K S A) Q.stop Q.run) := by
  intro v hv t ht hth w hw
  have service := outage_pre_service S A V Q
  obtain ⟨armed⟩ := outage_arm S A V Q service v hv
  exact outage_repair S A V Q service v hv armed t ht hth w hw


end Consensus.Goldilocks.Refinement
end
