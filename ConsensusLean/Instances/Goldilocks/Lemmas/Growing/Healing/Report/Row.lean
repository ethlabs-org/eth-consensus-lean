module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AcquireClient
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase

public section

/-! # A report supplies a historical honest row or a higher height

This proves the frozen report-row interface without importing its placeholder. All
client execution is read through the report time, including its same-time attestation.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- An actual report by a reporter honest at it and at `c_z` either supplies a row signed while
honest or is strictly higher (`Generic.row_or_high_of_report_at_from` at the Goldilocks run, with
the report held by `Healing.toFG_mem_tree`). -/
theorem row_or_high_of_report_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g T : Time}
    (hf : ∀ t, 0 ≤ t → t < T → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hna : ∀ v k att, v ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    {y : Fin sp.n} {i : Nat} (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time i)))
    {ell : ACLabel (goldilocksNode sp ro)} {R P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hR : AC.ToFGAt tr.projAC y i ell R) (hiT : tr.time i < T)
    (hPR : Anc (tr.HonestBlocksAt H) P R)
    (hkind : ((tr.state y i).fg.σ R.root).h = ((tr.state y i).fg.σ P.root).h →
      ((tr.state y i).fg.σ P.root).h = HZ tr H g ∨
      (tr.state y i).fg.hj < ((tr.state y i).fg.σ P.root).h ∨
      ((tr.state y i).fg.hj = ((tr.state y i).fg.σ P.root).h ∧
        (tr.state y i).fg.Anc (tr.state y i).fg.J R)) :
    P ∈ (tr.state y i).fg.tree ∧ R ∈ (tr.state y i).fg.tree ∧
      ((∃ k att, y ∈ H (tr.time k) ∧ tr.SignAt y k att ∧ tr.time k ≤ tr.time i ∧
        att.h = ((tr.state y i).fg.σ P.root).h ∧
        att.T = ((tr.state y i).fg.σ P.root).Th) ∨
        ((tr.state y i).fg.σ P.root).h < ((tr.state y i).fg.σ R.root).h) := by
  have hy := hrun.antitone (le_max_right _ _) hyz
  have hle : ∀ k < i, tr.time k ≤ tr.time i := fun k hk => hrun.time_mono hk.le
  have hr := hrun.upTo (hrun.time_nonneg i)
  obtain ⟨hc, hto, hres⟩ := hR
  have hacstate : (tr.upTo (tr.time i)).projAC.state y i = tr.projAC.state y i := by
    rw [RunTrace.upTo_projAC]
    exact Trace.upTo_state tr.projAC y hle
  have hRm : R ∈ (tr.state y i).fg.tree := by
    have hreport : AC.ToFGAt (tr.upTo (tr.time i)).projAC y i ell R :=
      ⟨Compose.projAC_callAt.mpr ((Trace.upTo_callAt tr).mpr ⟨le_rfl,
        Compose.projAC_callAt.mp hc⟩), hto, by rw [hacstate]; exact hres⟩
    simpa only [Trace.upTo_state tr y hle] using Healing.toFG_mem_tree hr hy hreport
  refine Generic.row_or_high_of_report_at_from hrun.toLocalRun hnc hf hna hyz
    ⟨ell, Compose.projAC_callAt.mp hc, hto, ?_⟩ hiT hRm hPR hkind
  have hstate := Compose.projAC_state hr.toLocalRun hy i
  rw [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC y hle,
    Trace.upTo_state tr y hle] at hstate
  rwa [hstate] at hres

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
