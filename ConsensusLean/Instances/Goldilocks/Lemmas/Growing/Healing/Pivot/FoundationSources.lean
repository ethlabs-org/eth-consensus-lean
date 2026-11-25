module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ResultAnc
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Result support counted at the result writer's observation -/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open AC (ACParams ReplayOrder Payload Vote)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
variable {hold : Time}

/-- A bounded result has a supporter still honest when the result is read. -/
theorem result_supporter_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {r s : Nat}
    (hx : x ∈ H (tr.time r))
    {B C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : AC.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocksAt H) B C)
    (hrb : tr.time r ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts s) :
    ∃ z ∈ H (tr.time r), ∃ q < r, ∃ e, AC.VoteAt tr.projAC z q e ∧ e.msg ∈ CV ∧
      e.msg.slot = s ∧ AC.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have ht0 := hp.run.time_nonneg r
  have hm := hp.run.time_mono
  have hpre := hp.run.upTo ht0
  have hS := healthy_base_of_reset_catch_before_at hp ht0 hrb
  have hΔ := sp.toParams.hΔ
  obtain ⟨ell, hu, hconf, hCV⟩ := hres
  have ht : tr.time r = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have hsb : sp.ts s + sp.Δ ≤ tr.time r := by linarith
  have hgs : AC.gbar g ≤ sp.ts s := by
    have := lt_cutZ sp g
    linarith
  have hsl : sp.slot (sp.ts s + sp.Δ) = s :=
    AC.slot_of_mem sp s (by linarith) (by simp only [ACParams.ts]; push_cast; linarith)
  have hs3 : sp.slot (AC.gbar g) + 3 ≤ s := by
    have h := (AC.ts_le_iff sp).mp ((cutZ_eq sp g) ▸ hts)
    exact_mod_cast h
  have hready : ∀ y ∈ H (tr.time r),
      (tr.upTo (tr.time r)).awake y (sp.ts s + sp.Δ) ∧
        (tr.upTo (tr.time r)).JoinedAt y (sp.ts s + sp.Δ) := by
    intro y hy
    refine ⟨(Trace.upTo_awake _ _ _).mpr
      ⟨hp.awake y _ (hp.run.antitone hsb hy) (by linarith) (hsb.trans hrb), hsb⟩, ?_⟩
    intro k hk hkt
    have hk₀ := (RunTrace.upTo_restartAt tr).mp hk |>.2
    have hyt := hp.run.antitone (hkt.trans hsb) hy
    change 0 < sp.slot (sp.ts s + sp.Δ) ∧
      tr.time k ≤ sp.toParams.slotTime (sp.slot (sp.ts s + sp.Δ) - 1)
    rw [hsl, sp.slotTime_eq]
    exact ⟨by omega, (hp.restart_le_before_at hyt hk₀
      ((hkt.trans hsb).trans hrb)).trans ((AC.ts_le_iff sp).mpr (by
        exact_mod_cast (show sp.slot (AC.gbar g) + 1 ≤ s - 1 by omega)))⟩
  have hu' := (AC.upTo_updateAt hm).mpr (And.intro le_rfl hu)
  have hparts := Compose.honest_participants_window_before hpre (hp.noColl.upTo _)
    (K := Generic.dictOfTime sp cm)
    (by rw [RunTrace.upTo_projAC]; exact AC.serviceWindowBefore_of_sync hS.sync)
    hgs hx (by rwa [RunTrace.upTo_projAC]) le_rfl hready
    (fun y hy hyK i => by
      rw [← Compose.projAC_state hpre.toLocalRun hy i]
      exact (AC.trace_mayVote_iff (Compose.goldilocks_ac_projection_from hpre
        (hp.noColl.upTo _)).localRun hy i s).2 hyK)
    (fun v hv => hp.committeeFacts.hP.1 _ x hx r (fun _ hk => hm hk.le) s v (by
      rwa [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC x (fun _ hk => hm hk.le)] at hv))
    (by
      rw [hp.committeeFacts.hsize s]
      exact hp.committee_cs2_at hgs (by linarith) (hp.run.time_nonneg r) hrb)
  rw [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC x (fun _ hk => hm hk.le)] at hparts
  have hac := Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl
  have hres' := (AC.upTo_resultAt hm).mpr (And.intro le_rfl
    (show AC.ResultAt tr.projAC x r s C CV from ⟨ell, hu, hconf, hCV⟩))
  obtain ⟨z, hz, q, hqr, e, hv, hev, hes, hVB⟩ :=
    AC.result_honest_supporter_of_participants sp (hac.upTo ht0) hx hres' hBC
      (by rw [Trace.upTo_state tr.projAC x (fun _ hk => hm hk.le)]; exact hparts.le)
  exact ⟨z, hz, q, hqr, e, (AC.upTo_voteAt.mp hv).2, hev, hes, hVB⟩

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
