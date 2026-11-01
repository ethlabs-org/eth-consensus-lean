module
public import AvailableChainFGSAClaims.Statements.LiveDC
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionCarrier
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthProposal

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

private theorem liveDC_finality_restore (p : Params) {In : Type} (c : AppCodec In)
    (X : FGBlock (Fin p.n)) (nd : Node p) (t : Time)
    (h : FGBlock.Preceq X nd.st.fg.F) :
    FGBlock.Preceq X ((fgsa p c).restore ((fgsa p c).durable nd) t).st.fg.F := by
  change FGBlock.Preceq X (acRestart p nd.st t).fg.F
  rwa [acRestart_fg]

private theorem liveDC_acceptsFinalBefore_mono (p : Params) {In V : Type}
    [DecidableEq V] (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hs : V2.D.ScheduleWellFormed E rho)
    {x : V} {X : FGBlock (Fin p.n)} {d d' : Time} (hdd : d ≤ d')
    (h : AcceptsFinalBefore p c E rho x X d) :
    AcceptsFinalBefore p c E rho x X d' := by
  have hm := fgsa_monoAlong_preceq_F p c X
  have hr := liveDC_finality_restore p c X
  obtain ⟨i, hi, hbefore, hX⟩ :=
    (Gen.V2.Duty.holdsBefore_iff_exists_idx_restore hs hm hr).mp h
  apply (Gen.V2.Duty.holdsBefore_iff_exists_idx_restore hs hm hr).mpr
  refine ⟨i, hi, ?_, hX⟩
  intro k hk
  obtain ⟨e, he, ht⟩ := hbefore k hk
  exact ⟨e, he, ht.trans_le hdd⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
LIVE-DC; DC Generic/Properties.lean:99–112. SAME later honest proposal;
INTENTIONAL compose local FF5 and FF6 at the raw gap G. No aligned-gap premise. -/
theorem healing_liveDCFromWindows (p : Params) : LiveDCFromWindowsStatement p := by
  rw [LiveDCFromWindowsStatement_def]
  intro V _ _ In c E rho G ΔF g t hrec hgst hfinal hproposal hhor
  have hs := hrec.base.valid.toScheduleWellFormed
  have hW : 0 ≤ W_W p ΔF g := by
    rw [W_W_def, betaF_def]
    change 0 ≤ ((g : Time) + 2) * (4 * (p.R : Time) * p.Δ) +
      4 * (kappaF p ΔF : Time) * p.Δ + p.Δ
    have := p.deltaPos
    positivity
  have hD : t + (2 * W_W p ΔF g + G) ≤ rho.horizon := by
    rwa [liveDCDeadline_W_def] at hhor
  obtain ⟨s, hafter, hgap, hslot, hjoined⟩ := hrec.joinedGap (t + W_W p ΔF g)
    (by linarith) (by linarith)
  have hst : t ≤ V2.D.proposalTime (fgsaInterface p c) s := by linarith
  have hsh : V2.D.proposalTime (fgsaInterface p c) s ≤ rho.horizon := by linarith
  obtain ⟨X, hp, _⟩ := fgsa_honestProposal_exists_of_awake_slot E rho hs
    hrec.base.delta hslot hjoined.1 hjoined.2.2 hsh
  obtain ⟨U, hstrict, hU⟩ := hfinal
  obtain ⟨j, N, _, hj, _, _, _, hX, _⟩ :=
    healing_promotion_proposal_read p c E rho hs hp
  let y := V2.D.proposerOf rho (fgsaInterface p c) s
  let st := FGSA.clock p (V2.D.Run.stateBefore E rho j y).st
    (SA.proposalTime p.toParams s)
  have hUF : FGBlock.Preceq U (V2.D.Run.stateBefore E rho j y).st.fg.F := by
    obtain ⟨i, _, hbefore, hi⟩ :=
      (Gen.V2.Duty.holdsBefore_iff_exists_idx_restore hs
        (fgsa_monoAlong_preceq_F p c U) (liveDC_finality_restore p c U)).mp (hU y hslot.2)
    have hij : i ≤ j := by
      by_contra hnot
      obtain ⟨e, he, ht⟩ := hbefore j (Nat.lt_of_not_ge hnot)
      have heq := Option.some.inj (he.symm.trans hj)
      subst e
      change SA.proposalTime p.toParams s < t + W_W p ΔF g at ht
      change t + W_W p ΔF g < SA.proposalTime p.toParams s at hafter
      exact (not_lt_of_ge hafter.le) ht
    have hm := fgsa_monoAlong_preceq_F p c U
    rw [Gen.V2.Duty.MonoAlong_def] at hm
    exact V2.D.Engine.stateBefore_stable_restore _ hm.1 hm.2.1 hm.2.2 E rho hij y
      (liveDC_finality_restore p c U) hi
  have hUX : Block.Preceq (eraseFG U) X := by
    have hi : CStoreInv p st :=
      cstoreInv_clock p _ (cstoreInv_stateBefore E rho j y) _
    have hUF' : Block.Preceq (eraseFG U) (eraseFG st.fg.F) := by
      rw [show st.fg = (V2.D.Run.stateBefore E rho j y).st.fg from clock_fg p _ _]
      exact eraseFG_preceq hUF
    have hparent : Block.Preceq (eraseFG U) (proposerHead p st s) := by
      rw [proposerHead_def]
      exact preceq_getHead_of_preceq_F p st hi hUF' _ _
    rw [hX]
    exact block_preceq_trans hparent (Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl _)))
  obtain ⟨Xfg, heX, hacc⟩ := hproposal s X hp hst (by linarith)
  rw [LiveDCConcl_W_def]
  refine ⟨Xfg, ⟨s, by linarith, heX ▸ hp⟩, ?_, ?_⟩
  · intro x hx
    rw [heX]
    have hS := hstrict x hx
    change (!decide (_ = eraseFG U) && Block.preceq _ (eraseFG U)) = true at hS
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hS
    obtain ⟨hne, hSU⟩ := hS
    have hne' : (V2.D.Run.readAt E rho t x).st.base.stableRecord ≠ X := by
      intro he
      have hUS : Block.Preceq (eraseFG U)
          (V2.D.Run.readAt E rho t x).st.base.stableRecord := he ▸ hUX
      have heq := block_preceq_antisymm hSU hUS
      exact hne heq
    change (!decide (_ = X) && Block.preceq _ X) = true
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨hne', block_preceq_trans hSU hUX⟩
  · intro x hx
    apply liveDC_acceptsFinalBefore_mono p c E rho hs _ (hacc x hx)
    rw [liveDCDeadline_W_def]
    linarith

end AvailableChain.FGSA.Run
end
