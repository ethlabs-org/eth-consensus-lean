module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift

public section

/-! # Vote-head classification on the casting node's honest prefix -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Classify the cast head locally, retaining the honesty of its optimistic write at that cut. -/
theorem vote_head_classification_of_service_at {s₀ floor : Nat} {hi : Time}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) hi floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hihi : tr.time i ≤ hi) (hib : tr.time i ≤ b)
    (hwarm : s₀ + sp.k ≤ e.msg.slot) (hpos : 0 < e.msg.slot)
    (hs₀ : s₀ ≤ e.msg.slot - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts ((e.msg.slot - 1 : Nat) : Int))
    (hgf : gbar g < SA.freeze sp e.msg.slot) (hstock : sp.committeeSize = sp.n) :
    ∃ Hd ∈ ell.frame.tree, Hd.root = e.msg.head ∧
      ((Hd ∈ SA.voteDomain sp e.readPoint ell.frame e.msg.slot ∧ Hd ∈ ell.frame.viableHeads) ∨
      (kindJ ∧ Hd = J) ∨
      (Hd = SA.getAnchor sp e.readPoint ell.frame (tr.time i) ∧
        ∃ l ∈ e.readPoint.locks, l.slot = e.msg.slot ∧
        ∃ a ≤ i, ∃ D CV, y ∈ H (tr.time a) ∧
          SA.OptimisticLockAt tr.projAC y a e.msg.slot D CV ∧
          sp.ts e.msg.slot ≤ tr.time a ∧ tr.time a < sp.ts e.msg.slot + 2 * sp.Δ ∧
          3 * sp.n ≤ 4 * (SA.voters CV).ncard ∧ ell.frame.Anc Hd D)) := by
  have hd := hrun.time_nonneg i
  have hS := healthy_base_of_service_catch_before_at hrun hnc hsvc hawake hf hcatch hd hib hstock
  have hr := hrun.upTo hd
  have hframe' : Healing.FrameWindow (tr := tr.upTo (tr.time i)) (H := H (tr.time i))
      (sp.ts s₀) (tr.time i) floor kindJ J := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz j hlo hhi
      rw [RunTrace.upTo_state_of_le hrun.time_mono hhi]
      exact hframe.floor_eq z j (hrun.antitone hhi hz) hlo (hhi.trans hihi)
    · intro z hz j hlo hhi
      rw [RunTrace.upTo_state_of_le hrun.time_mono hhi]
      exact hframe.kind_iff z j (hrun.antitone hhi hz) hlo (hhi.trans hihi)
    · intro z hz j hlo hhi hk
      rw [RunTrace.upTo_state_of_le hrun.time_mono hhi]
      exact hframe.root_eq z j (hrun.antitone hhi hz) hlo (hhi.trans hihi) hk
  have hc' : SA.CastAt (tr.upTo (tr.time i)).projAC y i ell e := by
    rw [RunTrace.upTo_projAC]
    exact SA.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hS' : SA.HealthyBaseUpTo (tr.upTo (tr.time i)).projAC (H (tr.time i))
      ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) proposer g (tr.time i) := by
    rwa [RunTrace.upTo_projAC]
  have hmargin : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hbound := hf _ hd hib
    have hn : 0 < sp.n := sp.toParams.hn
    change (H (tr.time i))ᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hprev : sp.ts ((e.msg.slot - 1 : Nat) : Int) + sp.Δ ≤ tr.time i := by
    have hslot := (Compose.Growing.castAt_spec_at hrun hnc hy hc).2.1
    have hti := (SA.ts_le_iff_le_slot sp hd (e.msg.slot : Int)).mpr (by rw [hslot])
    have hpred : ((e.msg.slot - 1 : Nat) : Int) = (e.msg.slot : Int) - 1 := by omega
    rw [hpred, SA.ts_sub_one]
    linarith only [hti, sp.toParams.hΔ]
  obtain ⟨Hd, hHd, hroot, hv | hj | ⟨hA, l, hl, hs, a, hai, D, CV, ho, ht, htop, hcount, hanc⟩⟩ :=
    Healing.FrameWindow.vote_head_classification_of_service hframe' hr (hnc.upTo _) hmargin hS'
      (fun z hz j hj => by
        obtain ⟨hjt, hj⟩ := (RunTrace.upTo_restartAt tr).mp hj
        exact hnr z j (hrun.antitone hjt hz) hj)
      hy hc' le_rfl hwarm hpos hs₀ hm hprev hgf
  · exact ⟨Hd, hHd, hroot, Or.inl hv⟩
  · exact ⟨Hd, hHd, hroot, Or.inr (Or.inl hj)⟩
  rw [RunTrace.upTo_projAC] at ho
  obtain ⟨hat, ho⟩ := (SA.upTo_optimisticLockAt hrun.time_mono).mp ho
  exact ⟨Hd, hHd, hroot, Or.inr (Or.inr ⟨hA, l, hl, hs, a, hai, D, CV,
    hrun.antitone hat hy, ho, ht, htop, hcount, hanc⟩)⟩

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
