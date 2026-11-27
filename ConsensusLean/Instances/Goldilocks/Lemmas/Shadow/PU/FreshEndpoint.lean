module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FreshLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.SignedTick
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Driven
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshUpdate
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Fresh update calls over the shadow run -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp}

/-- Wakefulness supplies the actual update tick, independently of its signing bit. -/
theorem update_call_of_awake_at'
    {ini : Fin sp.n → (goldilocksNode' sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g b : Time}
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hnr : NoRestartAfter tr H (gbar g)) {u : Nat}
    (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H (sp.ts (u + 1 : Nat) + 2 * sp.Δ)) :
    ∃ k ell, AC.UpdateAt tr.projAC y k u ell := by
  let T := sp.ts (u + 1 : Nat) + 2 * sp.Δ
  have hT : T = sp.ts u + 6 * sp.Δ := by
    dsimp only [T, ACParams.ts]; push_cast; ring
  have hΔ := sp.toParams.hΔ
  have ht0 : 0 ≤ T := by
    have hu0 : 0 ≤ sp.ts u := by simp only [ACParams.ts]; positivity
    rw [hT]; linarith
  obtain ⟨k, hk⟩ := hrun.tick_of_awake y T hy ht0
    ⟨4 * (u : Int) + 6, by rw [hT]; simp only [ACParams.ts]; ring⟩
    (hawake y T hy (by rw [hT]; linarith) hTb)
  obtain ⟨x, fgDue, hg⟩ := (RunTrace.tickAt'_iff ..).1 hk
  obtain ⟨hc, ht⟩ := Healing.tick_first_cut' hg
  have hj := Core.joined_of_restart_le_at hrun.toCore hnc hy
    (by rw [hT]; linarith : sp.ts u + 4 * sp.Δ ≤ T)
    (fun r _ hyr hrs => (hnr y r hyr hrs).trans (by linarith)) ht
  simp only [Node.acCall'_eq] at hc
  exact ⟨k, _, Compose.projAC_callAt.2 hc, rfl, ht.trans hT, hj⟩

variable {hold : Time}

/-- Honest unanimous slot votes yield the stock fresh-lock conclusion over the shadow window. -/
theorem fresh_fast_lock_update_at' {K : AC.CommitteeDict sp.n}
    {g ΔF b : Time} {u floor : Nat} {kindJ : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hjoin : ∀ y, y ∈ H (sp.ts u + sp.Δ) →
      AC.JoinedAt tr.projAC y (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    (hframe : FrameWindow tr H (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ)
      floor kindJ J)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hun : ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e →
      e.msg.slot = u → e.msg.head = P.root)
    {y : Fin sp.n} (hy : y ∈ H (sp.ts (u + 1 : Nat) + 2 * sp.Δ))
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ k ell, AC.UpdateAt tr.projAC y k u ell ∧
      AC.getConfirmation sp (tr.projAC.state y k) ell.frame u = some P ∧
      ¬ AC.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) P ∧
      AC.fastSelect sp (tr.projAC.state y k) ell.frame u P = some P ∧
      ell.frame.viableAncestor P = P ∧
      P ∈ ell.frame.viableTree ell.frame.tree ∧
      ∃ e, u + 2 ≤ e ∧ (⟨P.root, u, true, e⟩ : AC.Lock) ∈ (tr.projAC.post k).locks ∧
        (⟨P.root, u, true, e⟩ : AC.Lock) ∈ (tr.projAC.state y (k + 1)).locks := by
  obtain ⟨k, ell, hu⟩ := update_call_of_awake_at' hrun hnc hawake hnr hmargin hTb hy
  have hkt : tr.time k = sp.ts (u + 1 : Nat) + 2 * sp.Δ := by
    have hk := hu.2.2.1
    change tr.time k = sp.ts u + 6 * sp.Δ at hk
    rw [hk]
    simp only [ACParams.ts]; push_cast; ring
  have hyk : y ∈ H (tr.time k) := hkt ▸ hy
  obtain ⟨hvi, hconf, hfast, hva⟩ := Shadow.unanimous_update_selection_at' hframe hrun hnc hsvc
    hawake hf hcatch hnr hmargin hjoin hTb hz hdes hP hPs hun hyk hu hK
  have hnv := Shadow.unanimous_update_no_veto_at' hframe hrun hnc hsvc hawake hf hcatch hnr
    hmargin hjoin hTb hz hdes hP hPs hun hyk hu hK
  obtain ⟨e, he, hlock⟩ := Core.fresh_fast_lock_of_selection_at hrun.toCore hnc hyk hu hvi.1
    hconf hnv hfast hva
  refine ⟨k, ell, hu, hconf, hnv, hfast, hva, hvi, e, he, hlock, ?_⟩
  simpa only [Trace.state_succ_of_call tr.projAC hu.1] using hlock

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
