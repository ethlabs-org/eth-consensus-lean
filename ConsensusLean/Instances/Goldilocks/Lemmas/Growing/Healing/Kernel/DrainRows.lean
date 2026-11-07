module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Historical row delivery under growing faults

An honest signature remains owed after compromise. The receiver's honesty at the proposal
cut supplies honesty at its earlier restart cuts, without fixing an honest cohort.
-/

namespace Consensus.Goldilocks.Healing.Growing

namespace KernelProof

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- An honestly signed row is processed strictly before a sufficiently late honest proposal,
even if the signer has been compromised by then. -/
theorem rows_delivered_service_at {g ΔF b v : Time}
    (hsvc : ResetService tr H g ΔF b) (hnr : NoRestartAfter tr H (gbar g))
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hv : gbar g ≤ v) {p : Fin sp.n} {kX : Nat} (hp : p ∈ H (tr.time kX))
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : tr.ProposesAt p kX X)
    (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b) {y : Fin sp.n} {k : Nat}
    (hy : y ∈ H (tr.time k)) {att : FG.Att sp.n} (hsig : tr.SignAt y k att)
    (hk : tr.time k ≤ v) : ∃ k' < kX, tr.ProcessAttAt p k' att := by
  have hdl0 : ∀ j ≤ kX, ∀ τ : Time,
      tr.deadline p j τ ΔF ≤ max τ (gbar g) + ΔF := by
    intro j hj τ
    have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := j)
      (fun k' hk' hr => hnr p k'
        (hrun.antitone (hrun.time_mono (hk'.trans hj)) hp)
        (Compose.projAC_restartAt.1 hr)) τ
    simp only [ACTrace.deadline, RunTrace.deadline, Compose.projAC_lastWake] at h ⊢
    linarith
  have hg : max (tr.time k) g ≤ v := max_le hk ((le_gbar g).trans hv)
  have hdl : ∀ j ≤ kX,
      tr.deadline p j (max (tr.time k) g) ΔF ≤ v + ΔF := by
    intro j hj
    have := hdl0 j hj (max (tr.time k) g)
    have := max_le hg hv
    linarith
  obtain ⟨acc, hcall⟩ := hX.1.1
  obtain ⟨k', hk', hproc, hlt⟩ := hsvc.signedRow y k att hy hsig p kX hp
    ⟨_, hcall⟩ hkb (by linarith [hdl kX le_rfl])
  refine ⟨k', lt_of_le_of_ne hk' fun h => ?_, hproc⟩
  subst h
  linarith only [hdl k' le_rfl, hlt, hvx]

end KernelProof

end Consensus.Goldilocks.Healing.Growing

end
