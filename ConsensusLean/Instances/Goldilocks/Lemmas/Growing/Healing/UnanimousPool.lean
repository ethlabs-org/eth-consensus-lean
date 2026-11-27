module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalReports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.RootBound
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginLabel
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.SameSlot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.OperationalReports
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Unanimous pools at honest reading cuts -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
variable {hold : Time}

/-- Read the unanimous pool through the caller's horizon. Historical senders remain
accountable at their emission cuts, while counted voters are honest at the read. -/
private theorem unanimous_pool_core_at {K : AC.CommitteeDict sp.n} {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {y : Fin sp.n} {j : Nat} {ell : ACLabel (goldilocksNode sp)}
    (hy : y ∈ H (tr.time j)) (hcall : tr.projAC.CallAt y j ell)
    (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j) (hjb : tr.time j ≤ b)
    (hPt : P ∈ ell.frame.tree)
    (hS : AC.HealthyBaseUpTo K (tr.projAC.upTo (tr.time j)) (H (tr.time j))
      ((tr.upTo (tr.time j)).HonestBlocks (H (tr.time j))) proposer g (tr.time j))
    (hrst : ∀ k ≤ j, tr.RestartAt y k → tr.time k < sp.ts u)
    (hvote : ∀ x, x ∈ H (tr.time j) → x ∈ K.committee u → ∃ q e, AC.VoteAt tr.projAC x q e ∧
      e.msg.slot = u ∧ tr.time q ≤ sp.ts u + sp.Δ) :
    ∀ x, x ∈ H (tr.time j) → x ∈ K.committee u → ∃ v ∈ (tr.projAC.state y j).pool u,
      v.val = x ∧ v.head = P.root ∧
      AC.resolutionTime (tr.projAC.state y j) ell.frame v < AC.ETime.of (sp.ts u + 2 * sp.Δ) ∧
      ∀ v' ∈ (tr.projAC.state y j).pool u, v'.val = x → v' = v := by
  have hstate : (tr.projAC.upTo (tr.time j)).state y j = tr.projAC.state y j :=
    Trace.upTo_state _ _ (fun _ hk => hrun.time_mono hk.le)
  have hc' : (tr.projAC.upTo (tr.time j)).CallAt y j ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hcall⟩
  have hrestart : ∀ k ≤ j, ACTrace.RestartAt (tr.projAC.upTo (tr.time j)) y k →
      (tr.projAC.upTo (tr.time j)).time k < sp.ts u := by
    intro k hkj hk
    obtain ⟨ellk, hck, hrk⟩ := hk
    obtain ⟨hkt, hck⟩ := (Trace.upTo_callAt _).mp hck
    exact hrst k hkj (Compose.projAC_restartAt.mp ⟨ellk, hck, hrk⟩)
  have hpool := AC.unanimous_pool_before hS hy hc' hgu ht le_rfl
    (fun k hkj t _ => Compose.ac_deadline_le_of_restarts
      (fun r hr hrs => (hrestart r (hr.trans hkj) hrs).le) t)
    hrestart hPt (by
      intro x hx hxK
      have hud : sp.ts u + sp.Δ ≤ tr.time j := by linarith [sp.toParams.hΔ]
      obtain ⟨q, e, hv, hs, hq⟩ := hvote x hx hxK
      have hxq := hrun.antitone (hq.trans hud) hx
      obtain ⟨ellq, hcq, heq⟩ := hv
      exact ⟨q, e, ⟨ellq, (Trace.upTo_callAt _).mpr ⟨hq.trans hud, hcq⟩, heq⟩, hs,
        hun x q e hxq ⟨ellq, hcq, heq⟩ (by linarith) hs⟩)
  simpa only [hstate] using hpool

/-- Reset premises discharge the core's prefix service, restart and actual-vote duties. -/
theorem unanimous_pool_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    {y : Fin sp.n} {j : Nat} {ell : ACLabel (goldilocksNode sp)}
    (hy : y ∈ H (tr.time j)) (hcall : tr.projAC.CallAt y j ell)
    (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j) (hjb : tr.time j ≤ b)
    (hPt : P ∈ ell.frame.tree) :
    ∀ x, x ∈ H (tr.time j) → x ∈ (Generic.dictOfTime sp cm).committee u →
      ∃ v ∈ (tr.projAC.state y j).pool u, v.val = x ∧ v.head = P.root ∧
      AC.resolutionTime (tr.projAC.state y j) ell.frame v < AC.ETime.of (sp.ts u + 2 * sp.Δ) ∧
      ∀ v' ∈ (tr.projAC.state y j).pool u, v'.val = x → v' = v := by
  apply unanimous_pool_core_at hp.run hun hgu hy hcall ht hjb hPt
    (healthy_base_of_reset_catch_before_at hp (hp.run.time_nonneg j) hjb)
  · intro k hkj hr
    exact (restart_before_unanimous_slot_at hp hR
      (hp.run.antitone (hp.run.time_mono hkj) hy) hr
      ((hp.run.time_mono hkj).trans hjb)).trans_lt ((AC.ts_lt_iff sp).2 (by omega))
  · intro x hx hxK
    have hud : sp.ts u + sp.Δ ≤ tr.time j := by linarith [sp.toParams.hΔ]
    exact honest_votes_in_slot_at hp hgu hR (hud.trans hjb) x (hp.run.antitone hud hx) hxK

end Consensus.Goldilocks.Healing.Growing

end
