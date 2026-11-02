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

/-- Pre-outage service through start, saturating at the finite engine horizon.
Only labelled recipient cuts require service; no unrestricted SyncRun is inferred. -/
theorem outage_pre_service (Q : OutageQuery S A V) :
    Compose.SleepyServiceBefore Q.trace (honestKeys S Q.run.2) Q.params.Δ Q.start := by
  let b := min Q.start Q.run.2.horizon
  have hnet : Q.run.2.log.SyncUntil Q.run.2.point b := by
    constructor
    · intro x hx m t hs y hy a hta hcut hhor haw
      have hh := Q.outage.2.1.1.msgs x hx ⟨Q.run.1, m⟩ t ⟨m, rfl, hs⟩
        y hy a hta (hcut.trans (min_le_left _ _)) hhor haw
      obtain ⟨u, hu, hsent | hrecv, hnw⟩ := hh
      · obtain ⟨o, he, ho⟩ := hsent
        cases he
        exact ⟨u, hu, Or.inl ho, hnw⟩
      · obtain ⟨o, he, ho⟩ := hrecv
        cases he
        exact ⟨u, hu, Or.inr ho, hnw⟩
    · intro x hx tx t ht ha hs y hy a hta hcut hhor haw
      exact Q.outage.2.1.1.txs x hx tx t ht ha hs y hy a hta
        (hcut.trans (min_le_left _ _)) hhor haw
  have service := sleepyServiceBefore_of_syncUntil S Q.run.2 Q.hn Q.valid
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)
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
  rw [readIsOut V S Q.run.1 Q.run.2 Q.hn, outOf,
    simTrace_state S Q.run.2 Q.hn Q.valid v hv.1 i hi]
  exact chainTo_prefix hr ((hanc (stateAt S Q.run.2 Q.hn v i).now).mono (fun _ h => h.1))

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
