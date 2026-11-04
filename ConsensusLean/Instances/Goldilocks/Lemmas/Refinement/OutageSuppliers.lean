module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NonfinalSuppliers

import ConsensusLean.Lemmas.Model.SysLog

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

/-- Pre-outage service through start, saturating at the finite engine horizon.
Only labelled recipient cuts require service; no unrestricted SyncRun is inferred. -/
theorem outage_pre_service (Q : OutageQuery S A V) :
    Compose.SleepyServiceBefore Q.trace (honestKeys S Q.run.2) Q.params.Δ Q.start := by
  let b := min Q.start Q.run.2.horizon
  have h0 : Q.run.2.log.SyncUntil Q.run.2.point Q.start :=
    (Model.sysOf_delivers_iff _ _ _ _).mp Q.outage.2.1.1
  have hnet : Q.run.2.log.SyncUntil Q.run.2.point b :=
    CommLog.Delivers.reindex h0 (f := id) (fun _ => le_rfl) (fun _ => rfl) (fun _ => rfl)
      (min_le_left _ _)
  have service := sleepyServiceBefore_of_syncUntil S Q.run.2 Q.hn Q.valid
    (noCollRun_simTrace S Q.run.2 Q.hn Q.valid Q.noCollision)
    (min_le_right Q.start Q.run.2.horizon) hnet
  have bound {y j} (hj : Q.trace.IsCall y j) : Q.trace.time j ≤ Q.run.2.horizon := by
    obtain ⟨l, hl⟩ := hj
    exact simTrace_labelled_time_le S Q.run.2 Q.hn Q.valid (by rw [hl.2]; simp)
  refine ⟨service.deltaF, ⟨?_, ?_⟩, ?_⟩
  · intro x hx i m hi h0 y hy j l hj hb hd
    exact service.ac.message x hx i m hi h0 y hy j l hj
      (le_min hb (hd.trans (bound ⟨_, Compose.projAC_callAt.mp hj⟩))) hd
  · intro x hx i B hi h0 y hy j l hj hb hd hF
    exact service.ac.relay x hx i B hi h0 y hy j l hj
      (le_min hb (hd.trans (bound ⟨_, Compose.projAC_callAt.mp hj⟩))) hd hF
  · intro x hx i B hi h0 y hy j hj hb hd hF
    exact service.relay x hx i B hi h0 y hy j hj
      (le_min hb (hd.trans (bound hj))) hd hF

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

set_option linter.unusedVariables false in
/-- Structural arming at the original end-of-time cut: the confirmed DCA extends
neither beyond the effective record nor beyond the head. This needs no recency
of the record and proves no subsequent protection. The service argument remains
for compatibility with the outage assembly. -/
theorem outage_arm (Q : OutageQuery S A V)
    (service : Compose.SleepyServiceBefore Q.trace (honestKeys S Q.run.2) Q.params.Δ Q.start)
    (v : V) (hv : Q.run.2.point.Ready Q.duration v Q.T) :
    Nonempty (OutageArmedRead S A V Q v) := by
  let i := (chainTrace Q.run.2).endCut Q.T
  let j := cutMap S Q.run.2 Q.hn i
  let st := Q.trace.state (Q.run.2.ownKey v) j
  let Φ := Node.frame st
  have hi : i ≤ Q.run.2.events.length := Nat.findGreatest_le _
  have hrun := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hy := honest_ownKey (S := S) hv.1
  have hr := Compose.fg_reachable hrun.toLocalRun hy j
  have hΦ : FrameOK Φ := (Store.frame_realization _ _ _ _ hr).1
  let R := (SA.lookup Φ st.ac.latestConfirmed).getD Φ.F
  have hR : R ∈ Φ.tree := by
    dsimp [R]
    cases he : SA.lookup Φ st.ac.latestConfirmed with
    | none => exact hΦ.rooted.1
    | some B => exact (SA.lookup_eq_some he).1
  have hrecord : SA.lookup Φ st.ac.latestConfirmed = some R ∨
      (SA.lookup Φ st.ac.latestConfirmed = none ∧ R = Φ.F) := by
    dsimp [R]
    cases he : SA.lookup Φ st.ac.latestConfirmed <;> simp
  have hanc (t : Time) : Φ.Anc (SA.acConfirmed Q.params st.ac Φ t) R := by
    unfold SA.acConfirmed
    dsimp only
    cases hd : SA.deepest Φ {X | X ∈ Φ.tree ∧ Φ.Anc X R ∧
        Φ.Anc X (SA.acHead Q.params st.ac Φ t)} with
    | none => exact hΦ.rooted.2 R hR
    | some D => exact (SA.deepest_mem hd).1.2.1
  refine ⟨⟨R, hR, hrecord, ?_⟩⟩
  change (chainTrace Q.run.2).read .confirmed v i <+: _
  rw [read_eq_out S Q.run.2 Q.hn, outOf,
    simTrace_state S Q.run.2 Q.hn Q.valid v hv.1 i hi]
  exact chainTo_prefix hr ((hanc (stateAt S Q.run.2 Q.hn v i).now).mono (fun _ h => h.1))

end Consensus.Goldilocks.Refinement
end
