module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshLocks

public section

/-! # The fresh fast lock at the adjacent update and report read -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The actual adjacent update and to-FG call retain the proposal's fresh fast lock, at the slot
committees `K` of a run from `K`'s committee start. -/
theorem fresh_fast_lock_update_toFG_at {K : AC.CommitteeDict sp.n}
    {g ΔF b : Time} {u floor : Nat} {kindJ : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
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
    ∃ k ell ell', AC.UpdateAt tr.projAC y k u ell ∧
      tr.projAC.CallAt y (k + 1) ell' ∧ ell'.call = .toFG ∧
      tr.time (k + 1) = sp.ts (u + 1 : Nat) + 2 * sp.Δ ∧
      ell'.frame = ell.frame ∧
      AC.getConfirmation sp (tr.projAC.state y k) ell.frame u = some P ∧
      ¬ AC.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) P ∧
      AC.fastSelect sp (tr.projAC.state y k) ell.frame u P = some P ∧
      ell'.frame.viableAncestor P = P ∧
      P ∈ ell'.frame.viableTree ell'.frame.tree ∧
      ∃ e, u + 2 ≤ e ∧ (⟨P.root, u, true, e⟩ : AC.Lock) ∈ (tr.projAC.post k).locks ∧
        (⟨P.root, u, true, e⟩ : AC.Lock) ∈ (tr.projAC.state y (k + 1)).locks := by
  obtain ⟨k, ell, ell', hu, hc, hto, ht, hframes⟩ :=
    update_toFG_calls_of_awake_at hrun hnc hawake hnr hmargin hTb hy
  have hkt : tr.time k = sp.ts (u + 1 : Nat) + 2 * sp.Δ := by
    have hk := hu.2.2.1
    change tr.time k = sp.ts u + 6 * sp.Δ at hk
    rw [hk]
    simp only [ACParams.ts]; push_cast; ring
  have hyk : y ∈ H (tr.time k) := hkt ▸ hy
  obtain ⟨hvi, hconf, hfast, hva⟩ := hframe.unanimous_update_selection_at hrun hnc hsvc hawake
    hf hcatch hnr hmargin hjoin hTb hz hdes hP hPs hun hyk hu hK
  have hnv := hframe.unanimous_update_no_veto_at hrun hnc hsvc hawake hf hcatch hnr hmargin
    hjoin hTb hz hdes hP hPs hun hyk hu hK
  obtain ⟨e, he, hlock⟩ := fresh_fast_lock_of_selection_at hrun hnc hyk hu hvi.1
    hconf hnv hfast hva
  refine ⟨k, ell, ell', hu, hc, hto, ht, hframes, hconf, hnv, hfast,
    hframes.symm ▸ hva, hframes.symm ▸ hvi, e, he, hlock, ?_⟩
  simpa only [Trace.state_succ_of_call tr.projAC hu.1] using hlock

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
