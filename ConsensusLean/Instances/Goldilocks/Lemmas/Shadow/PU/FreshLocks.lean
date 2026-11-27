module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FreshNext
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FreshSupport
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore

public section

/-! # Compatibility of lock labels at the shadow warm update -/

namespace Consensus.Goldilocks.Healing.Growing.Shadow

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro} {hold : Time}

/-- Selection, next-slot extension and old-lock compatibility discharge the shared no-veto proof. -/
theorem unanimous_update_no_veto_at' {K : AC.CommitteeDict sp.n}
    {g ΔF b : Time} {u floor : Nat} {kindJ : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
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
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode' sp ro)} (hu : AC.UpdateAt tr.projAC y k u ell)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ¬ AC.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) P := by
  apply Core.unanimous_update_no_veto_at hrun.toCore hnc hsvc hawake hf hcatch
    hmargin hTb hun hy hu hK
  · intro x i hx elli hui
    obtain ⟨hv, hc, _⟩ := unanimous_update_selection_at' hframe hrun hnc hsvc hawake hf hcatch
      hnr hmargin hjoin hTb hz hdes hP hPs hun hx hui hK
    exact ⟨hv, hc⟩
  · exact unanimous_next_votes_at' hframe hrun hnc hsvc hawake hf hcatch hnr
      hmargin hjoin hTb hz hdes hP hPs hun hK
  · exact FrameWindow.older_locks_compatible_at_update_at' hframe hrun hnc hsvc hawake hf hcatch hnr
      hmargin hjoin hTb hz hdes hP hPs hun hy hu hK

end Consensus.Goldilocks.Healing.Growing.Shadow

end
