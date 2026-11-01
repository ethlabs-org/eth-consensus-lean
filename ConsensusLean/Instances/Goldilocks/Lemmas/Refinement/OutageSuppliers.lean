module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NonfinalSuppliers

public section
namespace Consensus.Goldilocks.Refinement
open Blocks Shape
variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

structure OutageQuery where
  run : (Sys (family S) V).Run
  hn : 1 ≤ Fintype.card V
  T : Time
  start : Time
  stop : Time
  valid : (Sys (family S) V).Valid run
  noCollision : ¬ run.2.HashCollision
  outage : (Sys (family S) V).Outage (K S A) T start stop run

namespace OutageQuery
variable {S A V}
abbrev params (Q : OutageQuery S A V) := S.params (Model.pubOf Q.run.1) Q.hn
noncomputable abbrev trace (Q : OutageQuery S A V) := simTrace S Q.run.2 Q.hn
noncomputable abbrev duration (Q : OutageQuery S A V) :=
  (Sys (family S) V).cDur (K S A) Q.run
end OutageQuery

/-- Exact two alternatives, retaining engine cDur and the closed awake windows.
This is a definitional reader split, NOT node catch-up or service transport. -/
theorem outage_reader_windows (Q : OutageQuery S A V) (w : V) (t : Time)
    (hr : (chainTrace Q.run.2).ResilienceReader Q.duration Q.start Q.stop w t) :
    Q.run.2.point.AwakeOnClosed w (max 0 (Q.start - Q.duration - 1)) t ∨
      (Q.stop ≤ t - Q.duration - 1 ∧
        Q.run.2.point.AwakeOnClosed w (t - Q.duration - 1) t) := hr

/-- OPEN pre-outage service only for recipient deadlines through start.
Fresh processing or retained stamped SA evidence replaces duplicate-processing synchrony.
Engine holdings alone do not establish this supplier; admission/retention remains OPEN.
No late-wake unrestricted SyncRun is inferred. -/
theorem outage_pre_service (Q : OutageQuery S A V) :
    Compose.SleepyServiceBefore Q.trace (honestKeys S Q.run.2) Q.params.Δ Q.start := by
  sorry

/-- Concrete source read and record witness at the exact end-of-time T cut.
Arming must handle each ready source, including an inherited confirmed record.
The witness itself does not assert its protection through the outage. -/
structure OutageArmedRead (Q : OutageQuery S A V) (v : V) where
  block : SA.Blk Q.params.n (List (FG.Att Q.params.n))
  held : block ∈ (Node.frame (Q.trace.state (Q.run.2.ownKey v)
    (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T)))).tree
  record :
    let st := Q.trace.state (Q.run.2.ownKey v)
      (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T))
    SA.lookup (Node.frame st) st.ac.latestConfirmed = some block ∨
      (SA.lookup (Node.frame st) st.ac.latestConfirmed = none ∧ block = (Node.frame st).F)
  read : (chainTrace Q.run.2).readAt .confirmed v Q.T <+:
    chainTo (Q.trace.state (Q.run.2.ownKey v)
      (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T))).fg.blocks
      (block.slot + 1) block

/-- OPEN old output/record arming using finite pre-outage service. -/
theorem outage_arm (Q : OutageQuery S A V)
    (service : Compose.SleepyServiceBefore Q.trace (honestKeys S Q.run.2) Q.params.Δ Q.start)
    (v : V) (hv : Q.run.2.point.Ready Q.duration v Q.T) :
    Nonempty (OutageArmedRead S A V Q v) := by
  sorry

/-- OPEN continuation/repair for the exact eligible reader alternatives.
This join still owes lifetime, old-record compatibility, first-arrival and
actual repair production; an armed record alone is not a proof of protection.
No all-node or continuously-awake-only replacement of ResilienceReader. -/
theorem outage_repair (Q : OutageQuery S A V)
    (service : Compose.SleepyServiceBefore Q.trace (honestKeys S Q.run.2) Q.params.Δ Q.start)
    (v : V) (hv : Q.run.2.point.Ready Q.duration v Q.T)
    (armed : OutageArmedRead S A V Q v)
    (t : Time) (ht : Q.start ≤ t) (hth : t ≤ Q.run.2.horizon)
    (w : V) (hw : w ∈ Q.run.2.honest)
    (reader : Q.run.2.point.AwakeOnClosed w (max 0 (Q.start - Q.duration - 1)) t ∨
      (Q.stop ≤ t - Q.duration - 1 ∧
        Q.run.2.point.AwakeOnClosed w (t - Q.duration - 1) t)) :
    (chainTrace Q.run.2).readAt .confirmed v Q.T <+:
      (chainTrace Q.run.2).readAt (resilienceTarget schema .confirmed) w t := by
  sorry

/-- Assembly preserves the unchanged reader and time quantifiers of persists. -/
theorem outage_protected (Q : OutageQuery S A V) :
    (chainTrace Q.run.2).ProtectedThrough Q.duration .confirmed
      (resilienceTarget schema .confirmed) Q.T Q.start Q.stop := by
  intro v hv t ht hth w hw hr
  have service := outage_pre_service S A V Q
  obtain ⟨armed⟩ := outage_arm S A V Q service v hv
  exact outage_repair S A V Q service v hv armed t ht hth w hw
    (outage_reader_windows S A V Q w t hr)

end Consensus.Goldilocks.Refinement
end
