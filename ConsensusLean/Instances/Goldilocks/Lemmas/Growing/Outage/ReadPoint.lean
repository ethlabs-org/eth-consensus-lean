module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Window
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Repair
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The Goldilocks outage read point (L9)

`goldilocks_outageReadPoint`: every local supplier at the Goldilocks data equations
(`GoldilocksLocalData`) meets `OutageReadPoint`. Every input comes from L9's own antecedents and
the data equations, on the run's own trace: the run, its committee facts, the call bound and the
pre-start service at `Δ` (`outage_inputs_of_local`); the counts through the horizon
(`outage_bounds_of_local`); the window numbers and the restored label
(`outage_window_numbers`, `outageRestoredLabel_spec`); the holders and opponents at the window
end, read on the retained point (`Population`). The source is armed (`outage_arming_at`), the
lock module's package is built from the arming (`outageLockPremises_of_arming`), and the reader's
read extends the armed tip (`outage_lock_protected`). -/

namespace Consensus.Goldilocks.Generic

open AC (ACParams ReplayOrder)
open Compose.Growing

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **L9 at the Goldilocks data equations.** -/
theorem goldilocks_outageReadPoint (C : ACCorrectLocal (goldilocksNode sp ro) (fun v => v.val))
    {sign : Fin sp.n → Time → Bool} {G : Nat}
    (hC : GoldilocksLocalData sp ro C sign G) : OutageReadPoint C where
  protection cm proposer dg H tr p ΔF T b₀ b₁ R hrun hnc hb hT hlag hb01 hbud hb1R hrec hs hpost
      hp hK x i y j t hRx _ _ hRt hRy _ htj := by
    classical
    have hΔ := sp.toParams.hΔ
    have hk2 : (2 : Time) ≤ sp.k := by exact_mod_cast sp.two_le_k
    obtain ⟨hcu, hη, hL, hbudg, hrecov⟩ := outage_durations_of_local hC
    rw [hL] at hlag
    rw [hbudg] at hbud
    rw [hrecov] at hrec
    obtain ⟨⟨ini, hgr⟩, hKB, hcall, service⟩ := outage_inputs_of_local hC hrun hnc hb hs
    have hθ : C.θ = 1 / 2 := hC.θ
    have hpos : 0 < sp.committeeSize := by
      have h := hrun
      rw [hC.healing.1.1] at h
      exact h.2.1
    have hth : t ≤ p.horizon := hRy.1.2.2.2
    have hhor : 0 ≤ p.horizon := hRy.1.2.2.1.trans hth
    have hsh : b₀ ≤ p.horizon := by linarith
    obtain ⟨hnum, ⟨ha0, haj, hzj⟩, hlook⟩ :=
      outage_window_numbers (hor := p.horizon) hT hlag hb01 hbud hhor
    rw [← hη] at hlook
    set j₀ := Compose.coverLabel sp b₀
    set a := outageWinStart sp b₀ p.horizon
    set z := outageWinEnd sp b₁ p.horizon
    set c := max C.catchUp (C.outageEta - 1)
    have hzh : z ≤ p.horizon := outageWinEnd_le_horizon sp b₁ p.horizon
    have hzdef : z = min (b₁ + (4 * sp.k + 6) * sp.Δ) p.horizon := outageWinEnd_eq sp b₁ _
    have hz0 : 0 ≤ z := by
      have : (0 : Time) ≤ (4 * sp.k + 6) * sp.Δ := by positivity
      rw [hzdef]
      exact le_min (by linarith) hhor
    have hzb : z ≤ b₁ + (4 * sp.k + 6) * sp.Δ := hzdef ▸ min_le_left _ _
    have hBB := fun b (hb' : b ≤ p.horizon) => outage_bounds_of_local hC hrun hb hp hK hb'
    -- the holders and opponents at the window end
    have hclass : ∀ x u, a ≤ u → u ≤ z → x ∈ H z → tr.awake x u →
        x ∈ outageHolders p c z ∪ outageOpponents p C.outageEta c z :=
      fun _ _ hau huz hx haw => outage_classify hb hlook hau huz hx haw
    have hawake : ∀ x ∈ outageHolders p c z, ∀ u, a ≤ u → u ≤ z → tr.awake x u :=
      fun _ hx _ hau huz => outage_holder_awake hb
        (le_trans (max_le_max le_rfl (by linarith [le_max_right C.catchUp (C.outageEta - 1)]))
          hlook) hx hau huz
    have hne : ∀ s : Nat, (cm (sp.ts s)).Nonempty := by
      intro s
      have hs : (cm (sp.ts s) : Set (Fin sp.n)).ncard = sp.committeeSize := by
        simpa only [dictOfTime, sp.slotTime_eq, AC.ACParams.ts] using hKB.hsize s
      exact Finset.card_pos.mp (by simpa using (hpos.trans_eq hs.symm))
    have hKθ : ∀ δ, 0 ≤ δ → δ ≤ C.outageEta →
        p.CommitteeSleepyOn (fun t => cm (max 0 (t - δ))) (1 / 2) C.outageEta c
          C.committeeLook 0 p.horizon := by
      simpa only [hθ] using hK
    have hcl : 0 ≤ C.committeeLook := by
      rw [hC.committeeLook]; positivity
    have hη0 : 0 < C.outageEta := by
      rw [hη]; positivity
    have hopp : ∀ m, j₀ ≤ m → m ≤ j₀ + sp.k → sp.ts m ≤ p.horizon →
        ((dictOfTime sp cm).committee m ∩ ((H z)ᶜ ∪ outageOpponents p C.outageEta c z)).ncard <
          ((dictOfTime sp cm).committee m ∩ outageHolders p c z).ncard := by
      intro m h₁ h₂ hq
      obtain ⟨hg₁, hg₂, -, -, -, hj₁, -⟩ := hnum
      have hm₁ : sp.ts (j₀) ≤ sp.ts m :=
        (AC.ts_le_iff sp).2 (by exact_mod_cast h₁)
      have hm₂ : sp.ts m ≤ sp.ts (j₀) + 4 * sp.k * sp.Δ := by
        have := (AC.ts_le_iff sp).2
          (show (m : Int) ≤ ((j₀ + sp.k : Nat) : Int) by exact_mod_cast h₂)
        simp only [AC.ACParams.ts] at this ⊢
        push_cast at this
        linarith
      have hts1 : sp.ts (j₀ + 1 : Nat) = sp.ts (j₀) + 4 * sp.Δ := by
        simp only [AC.ACParams.ts]; push_cast; ring
      rw [hts1] at hg₂
      refine outage_opponents_lt_committee hb hη0 hcl hz0 hzh hKθ (hne m) ?_ ?_
      · refine max_le (ts_natCast_nonneg m) ?_
        rw [hη]
        linarith [mul_nonneg (show (0 : Time) ≤ sp.k by linarith) hΔ.le]
      · rw [hzdef]
        exact le_min (by linarith) hq
    have hopp2 : ∀ m, j₀ ≤ m → m ≤ j₀ + sp.k →
        sp.ts m ≤ p.horizon → b₀ ≤ p.horizon →
        2 * ((dictOfTime sp cm).committee m ∩
          ((H z)ᶜ ∪ outageOpponents p C.outageEta c z)).ncard < sp.committeeSize :=
      fun m h₁ h₂ hq _ => by
        rw [← hKB.hsize m]
        exact outage_two_mul_opponents_lt hb (hopp m h₁ h₂ hq)
    -- the armed source, the package and the reader's read
    obtain ⟨ar⟩ := outage_arming_at hgr hnc hKB hlag hcall service (fun b hb' => (hBB b hb').1)
      (fun b hb' => (hBB b hb').2) haj hzj hzh (outageHolders_subset hb) hawake hclass hopp2
      hRx.1
    have hcatch : Regimes.catchUp sp ≤ C.catchUp := by rw [hcu]; exact le_refl _
    have h := outage_lock_protected
      (outageLockPremises_of_arming hgr hnc hKB hT hlag hsh hcall service hpost
        (fun b hb' => (hBB b hb').1) (fun b hb' => (hBB b hb').2) hnum
        (outageRestoredLabel_spec hT hlag hb01 hbud) ha0 haj (outageHolders_subset hb)
        (outageOpponents_subset hb) outageHolders_disjoint hawake hclass hopp ar)
      (by rw [outageLockPremises_of_arming_b₁]; exact hpost)
      (by rw [outageLockPremises_of_arming_P]; exact ar.tip_anc) hcatch
      (by rw [outageLockPremises_of_arming_b₁]; linarith) hRy htj ((hBB t hth).1)
      (fun d hd => by rw [outageLockPremises_of_arming_K]; exact (hBB d (hd.trans hth)).2)
    rw [ar.tip_eq] at h
    exact h

end Consensus.Goldilocks.Generic

end
