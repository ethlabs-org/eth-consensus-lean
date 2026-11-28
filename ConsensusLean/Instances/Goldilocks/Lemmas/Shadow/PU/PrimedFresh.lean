module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ProposalViable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshUpdate
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshLocks
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Fresh locks under the primed frame window -/

namespace Consensus.Goldilocks.Healing.Growing.Shadow

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {hold : Time}
  {K : AC.CommitteeDict sp.n} {g ΔF b : Time} {u M : Nat} {isTop : Prop}
  {J P : AC.Blk sp.n (List (FG.Att sp.n))}
  (hframe : Generic.FrameWindow tr H (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) M isTop J)
  (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
    (AC.committeeStart sp.genesisRoot K))
  (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
  (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
  (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
  (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
  (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
  (hjoin : ∀ x, x ∈ H (sp.ts u + sp.Δ) → AC.JoinedAt tr.projAC x (sp.ts u + sp.Δ))
  (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
  {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
  {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
  (hun : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e →
    e.msg.slot = u → e.msg.head = P.root)
  (hK : CommitteeHalfUpTo tr H K g b)

include hframe hrun hnc hsvc hf hnr hmargin hTb hz hdes hP hPs in
/-- Late honest calls retain the primed proposal's full-frame geometry. -/
theorem proposal_viable_after_votes_primed_at'
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y k ell)
    (hlo : sp.ts u + 2 * sp.Δ ≤ tr.time k)
    (hhi : tr.time k ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ) :
    P ∈ ell.frame.viableTree ell.frame.tree ∧ ell.frame.viableAncestor P = P ∧
      P ∈ ell.frame.viableHeads := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨hPt, hroot, hv⟩ := KernelProof.proposal_viable_at_call_primed_at'
    hframe hrun hnc hsvc hf hnr (by linarith)
    (by simp only [ACParams.ts]; push_cast; linarith) hTb hz hdes hP hPs hy hc
    (by linarith) hhi
  exact Healing.Growing.proposal_viable_after_votes_at hrun hnc hy hc hPt hroot hv

include hframe hrun hnc hsvc hawake hf hcatch hnr hmargin hjoin hTb hz hdes hP hPs hun hK in
/-- Primed geometry supplies the window-free unanimous selection proof. -/
theorem unanimous_update_selection_primed_at'
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} (hu : AC.UpdateAt tr.projAC y k u ell) :
    P ∈ ell.frame.viableTree ell.frame.tree ∧
      AC.getConfirmation sp (tr.projAC.state y k) ell.frame u = some P ∧
      AC.fastSelect sp (tr.projAC.state y k) ell.frame u P = some P ∧
      ell.frame.viableAncestor P = P := by
  have ht : tr.time k = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ = sp.ts u + 6 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  obtain ⟨hvi, hva, _⟩ := proposal_viable_after_votes_primed_at' hframe hrun hnc hsvc hf hnr
    hmargin hTb hz hdes hP hPs hy hu.1
    (by rw [ht]; linarith [sp.toParams.hΔ]) (by rw [ht, hT])
  exact Healing.Growing.unanimous_update_selection_at hrun hnc hsvc hawake hf hcatch hnr
    hmargin hjoin hTb hz hdes hP hPs hun hy hu hK hvi hva

include hframe hrun hnc hsvc hawake hf hcatch hnr hmargin hjoin hTb hz hdes hP hPs hun hK in
/-- The next honest votes extend the unanimous proposal under the primed window. -/
theorem unanimous_next_votes_primed_at' :
    ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
  refine unanimous_next_votes_at hrun hnc hsvc hawake hf hcatch hnr
    hmargin hjoin hTb hz hdes hP hPs hun hK ?_
  intro y j ell e hy hc hs hjb
  have hΔ := sp.toParams.hΔ
  have hr := Compose.Growing.acRun_upTo hrun hnc (hrun.time_nonneg j)
  have hc' : AC.CastAt (tr.projAC.upTo (tr.time j)) y j ell e := AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hsl := (AC.castAt_specU hr.localRun.toU hy hc').2.1
  change e.msg.slot = sp.slot (tr.time j) at hsl
  have hlo : sp.ts (u + 1 : Nat) ≤ tr.time j :=
    (AC.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).2 (by omega)
  have hhi : tr.time j ≤ sp.ts (u + 1 : Nat) + sp.Δ := by
    have ht := (Compose.cast_head_fcRoot hr.localRun hr.vstart hy hc').2
    rwa [hs] at ht
  obtain ⟨hvi, _, hv⟩ := proposal_viable_after_votes_primed_at' hframe hrun hnc hsvc hf hnr
    hmargin hTb hz hdes hP hPs hy hc.1
    (by simp only [ACParams.ts] at hlo ⊢; push_cast at hlo; linarith) (by linarith)
  exact ⟨hvi.2.1.mono (fun Q hQ => Compose.Growing.upTo_subset hrun (hrun.time_nonneg j)
    ((AC.frameIn_of_callAt hr.localRun hy hc'.1).2 hQ)), hv⟩

include hframe hrun hnc hsvc hawake hf hcatch hnr hmargin hjoin hTb hz hdes hP hPs hun hK in
/-- Primed selection and geometry discharge the shared lock-veto proof. -/
theorem unanimous_update_no_veto_primed_at'
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} (hu : AC.UpdateAt tr.projAC y k u ell) :
    ¬ AC.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) P := by
  apply Core.unanimous_update_no_veto_at hrun hnc hsvc hawake hf hcatch
    hmargin hTb hun hy hu hK
  · intro x i hx elli hui
    obtain ⟨hv, hc, _⟩ := unanimous_update_selection_primed_at' hframe hrun hnc hsvc hawake hf
      hcatch hnr hmargin hjoin hTb hz hdes hP hPs hun hK hx hui
    exact ⟨hv, hc⟩
  · exact unanimous_next_votes_primed_at' hframe hrun hnc hsvc hawake hf hcatch hnr
      hmargin hjoin hTb hz hdes hP hPs hun hK
  · exact Healing.Growing.older_locks_compatible_at_update_at
      (fun hy' hc' hlo hhi => (proposal_viable_after_votes_primed_at' hframe hrun hnc hsvc hf hnr
        hmargin hTb hz hdes hP hPs hy' hc' hlo hhi).1)
      hrun hnc hsvc hawake hf hcatch hnr hmargin hjoin hTb hz hdes hP hPs hun hy hu hK

include hframe hrun hnc hsvc hawake hf hcatch hnr hmargin hjoin hTb hz hdes hP hPs hun hK in
/-- An awake honest update installs the fresh unanimous lock over the primed window. -/
theorem fresh_fast_lock_update_at
    {y : Fin sp.n} (hy : y ∈ H (sp.ts (u + 1 : Nat) + 2 * sp.Δ)) :
    ∃ k ell, AC.UpdateAt tr.projAC y k u ell ∧
      AC.getConfirmation sp (tr.projAC.state y k) ell.frame u = some P ∧
      ¬ AC.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) P ∧
      AC.fastSelect sp (tr.projAC.state y k) ell.frame u P = some P ∧
      ell.frame.viableAncestor P = P ∧
      P ∈ ell.frame.viableTree ell.frame.tree ∧
      ∃ e, u + 2 ≤ e ∧ (⟨P.root, u, true, e⟩ : AC.Lock) ∈ (tr.projAC.post k).locks ∧
        (⟨P.root, u, true, e⟩ : AC.Lock) ∈ (tr.projAC.state y (k + 1)).locks := by
  obtain ⟨k, ell, hu⟩ := Healing.Growing.update_call_of_awake_at hrun hnc hawake hnr hmargin hTb hy
  have hyk : y ∈ H (tr.time k) := by
    have ht : tr.time k = sp.ts u + 6 * sp.Δ := hu.2.2.1
    have hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ = sp.ts u + 6 * sp.Δ := by
      simp only [ACParams.ts]; push_cast; ring
    rwa [ht, ← hT]
  obtain ⟨hvi, hconf, hfast, hva⟩ := unanimous_update_selection_primed_at' hframe hrun hnc hsvc
    hawake hf hcatch hnr hmargin hjoin hTb hz hdes hP hPs hun hK hyk hu
  have hnv := unanimous_update_no_veto_primed_at' hframe hrun hnc hsvc hawake hf hcatch hnr
    hmargin hjoin hTb hz hdes hP hPs hun hK hyk hu
  obtain ⟨e, he, hlock⟩ := Healing.Growing.fresh_fast_lock_of_selection_at hrun hnc hyk hu hvi.1
    hconf hnv hfast hva
  refine ⟨k, ell, hu, hconf, hnv, hfast, hva, hvi, e, he, hlock, ?_⟩
  simpa only [Trace.state_succ_of_call tr.projAC hu.1] using hlock

end Consensus.Goldilocks.Healing.Growing.Shadow

end
