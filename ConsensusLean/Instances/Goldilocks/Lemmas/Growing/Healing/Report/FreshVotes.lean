module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesAnchor
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Warm vote unanimity with honesty at each cast -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Warm unanimity follows the actual proposal walk, by strict induction on cast cuts. -/
theorem honest_vote_heads_eq_at
    {g ΔF b : Time} {s₀ u floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts u + sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hmb : sp.ts u + sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hstock : sp.committeeSize = sp.n) :
    ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e → e.msg.slot = u →
      e.msg.head = P.root := by
  have hk := sp.two_le_k
  have hu : 0 < u := by omega
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hu)
  have hr := hrun.toLocalRun
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hsp : s₀ ≤ s + 1 := by omega
  have hms : gbar g + 2 * sp.Δ ≤ sp.ts s := by
    have ht : sp.ts s₀ ≤ sp.ts s := (SA.ts_le_iff sp).2 (by omega)
    linarith [sp.toParams.hΔ]
  have htime : tr.time kP = sp.ts (s + 1 : Nat) := by
    simpa only [sp.slotTime_eq, hPs, SAParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) :=
    hr.antitone (by rw [htime]; linarith [sp.toParams.hΔ]) hz
  have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2⟩
  obtain ⟨_, ip, ellp, d, pay, hcp, hcall, hpay, hti, hparent, _, _, hpayload, _⟩ :=
    Healing.honestProposalRun_of_proposesAt (hrun.upTo (hr.time_nonneg kP))
      (hnc.upTo _) hzk hdes hP' hPs
  rw [← hdes] at hcp hpay
  have hip : tr.time ip = sp.ts (s + 1 : Nat) := hti
  have hcp0 : tr.projAC.CallAt z ip ellp := by
    rw [RunTrace.upTo_projAC] at hcp
    exact ((Trace.upTo_callAt _).mp hcp).2
  have hpay0 : (SA.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 =
      some (d, pay) := by
    have hs := Trace.upTo_state tr.projAC z (d := tr.time kP) (i := ip)
      (fun q hq => (hr.time_mono hq.le).trans (by rw [hip, htime]))
    simp only [RunTrace.upTo_projAC, hs, Trace.upTo_time] at hpay
    exact hpay
  suffices hall : ∀ i y e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e →
      e.msg.slot = s + 1 → e.msg.head = P.root by
    exact fun y i e hy hv hs => hall i y e hy hv hs
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro y e hy hv hes
    obtain ⟨ell, hc, he⟩ := hv
    have hcast : SA.CastAt tr.projAC y i ell e := ⟨hc, he⟩
    have hci : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
      (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
    have hri := (hac.upTo (hr.time_nonneg i)).localRun
    have hcast' : SA.CastAt (tr.projAC.upTo (tr.time i)) y i ell e := ⟨hci, he⟩
    have hhigh := SA.vote_time_le hri hy ⟨ell, hcast'⟩
    have hslot := (SA.castAt_spec hri hy hcast').2.1.symm.trans hes
    change sp.slot (tr.time i) = s + 1 at hslot
    change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at hhigh
    rw [hslot] at hhigh
    obtain ⟨hvP, hPv⟩ := proposal_viable_at_cast_at hframe hrun hnc hsvc hawake hf hcatch hnr
      (by linarith [sp.toParams.hΔ]) hsp (by omega) hmb hz hdes hP hPs hy hcast hes hstock
    have haP := hframe.vote_anchor_below_of_earlier_heads_at hrun hnc hsvc hawake hf hcatch
      hnr hm hsp (by omega) hmb hz hdes hP hPs hy hcast hes hwarm
      (fun x j ev hji hx hv hs => ih j hji x ev hx hv hs) hstock
    apply hframe.vote_head_eq_of_start_prefix_at hrun hnc hsvc hawake hf hcatch hnr hms hsp
      hz hdes hP hPs hcp0 hcall hip hpay0 hpayload hparent hy hcast hes hhigh
      (hhigh.trans hmb) hPv haP ?_ hstock
    exact fun haS => hframe.proposal_start_prefix_at hrun hnc hsvc hawake hf hcatch hnr
      hm (by omega) hwarm hmb hz hdes hcp0 hcall hip hpay0 hparent hy hcast hes hPv hvP haS
      hstock

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
