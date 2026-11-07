module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.ProposalReceipt
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Windows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ResultAnc
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Result support counted at the result writer's observation -/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- A bounded result has a supporter still honest when the result is read. -/
theorem result_supporter_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x : Fin sp.n} {r s : Nat}
    (hx : x ∈ H (tr.time r))
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocksAt H) B C)
    (hrb : tr.time r ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts s) :
    ∃ z ∈ H (tr.time r), ∃ q < r, ∃ e, SA.VoteAt tr.projAC z q e ∧ e.msg ∈ CV ∧
      e.msg.slot = s ∧ SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have ht0 := hp.run.time_nonneg r
  have hm := hp.run.time_mono
  have hpre := hp.run.upTo ht0
  have hS := healthy_base_of_reset_catch_before_at hp hc ht0 hrb
  have hΔ := sp.toParams.hΔ
  obtain ⟨ell, hu, hconf, hCV⟩ := hres
  have ht : tr.time r = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have hsb : sp.ts s + sp.Δ ≤ tr.time r := by linarith
  have hgs : SA.gbar g ≤ sp.ts s := by
    have := lt_cutZ sp g
    linarith
  have hsl : sp.slot (sp.ts s + sp.Δ) = s :=
    SA.slot_of_mem sp s (by linarith) (by simp only [SAParams.ts]; push_cast; linarith)
  have hs3 : sp.slot (SA.gbar g) + 3 ≤ s := by
    have h := (SA.ts_le_iff sp).mp ((cutZ_eq sp g) ▸ hts)
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
    exact ⟨by omega, (restart_le_before_at hp hyt hk₀
      ((hkt.trans hsb).trans hrb)).trans ((SA.ts_le_iff sp).mpr (by
        exact_mod_cast (show sp.slot (SA.gbar g) + 1 ≤ s - 1 by omega)))⟩
  have hf : 3 * (H (tr.time r))ᶜ.ncard < sp.n := by
    have := hp.faults (tr.time r) ht0 hrb
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    omega
  have hu' := (SA.upTo_updateAt hm).mpr (And.intro le_rfl hu)
  have hparts := Compose.honest_participants_window_before hpre (hp.noColl.upTo _)
    (by rw [RunTrace.upTo_projAC]; exact SA.serviceWindowBefore_of_sync hS.sync)
    hgs hx (by rwa [RunTrace.upTo_projAC]) le_rfl hready hf
  rw [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC x (fun _ hk => hm hk.le)] at hparts
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hres' := (SA.upTo_resultAt hm).mpr (And.intro le_rfl
    (show SA.ResultAt tr.projAC x r s C CV from ⟨ell, hu, hconf, hCV⟩))
  obtain ⟨z, hz, q, hqr, e, hv, hev, hes, hVB⟩ :=
    SA.result_honest_supporter_of_participants sp (hac.upTo ht0) hx hres' hBC
      (by rw [Trace.upTo_state tr.projAC x (fun _ hk => hm hk.le)]; exact hparts.le)
  exact ⟨z, hz, q, hqr, e, (SA.upTo_voteAt.mp hv).2, hev, hes, hVB⟩

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
