module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay

public section

/-! # Owed reset service on the AC projection

The source and recipient are retained at separate horizons. A sender's later
compromise never discharges a message or block already owed to the reader.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF b lo hi : Time}

/-- Reset service projected with source honesty at release and reader honesty at its call. -/
theorem ResetService.ac_service_at (hs : ResetService tr H g ΔF b)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hg : g ≤ lo) :
    SA.Growing.ServiceWindowBefore H (tr.HonestBlocksAt H) lo hi tr.projAC := by
  have hm := hrun.time_mono
  constructor
  · intro x i m hx hsa hai y j ell hy hc _ hdl
    obtain ⟨ell₀, hc₀, hmsg⟩ := hsa
    have hpre := hrun.upTo (hrun.time_nonneg i)
    have hstate : tr.projAC.state x i = (tr.state x i).ac := by
      have h := Compose.projAC_state hpre.toLocalRun hx i
      rwa [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC x (fun _ hk => hm hk.le),
        RunTrace.upTo_state_of_le hm le_rfl] at h
    have hsa' : tr.SendOrAdmitAt x i m := ⟨ell₀, Compose.projAC_callAt.mp hc₀, by
      rwa [hstate] at hmsg⟩
    have he : max (tr.time i) g = tr.time i := max_eq_left (hg.trans hai)
    obtain ⟨k, hkj, htk, hp, hlt⟩ := hs.message x i m hx hsa' y j hy
      ⟨_, Compose.projAC_callAt.mp hc⟩ (by rw [he, ← Compose.projAC_deadline]; exact hdl)
    apply (SA.messageServedBefore_iff _ _ _ _).mpr
    refine Or.inl ⟨k, hkj, htk, ?_, ?_⟩
    · rcases hp with ⟨ell', hc', hm'⟩ | ⟨ell', hc', hm'⟩
      exacts [⟨ell', Compose.projAC_callAt.mpr hc', Or.inl hm'⟩,
        ⟨ell', Compose.projAC_callAt.mpr hc', Or.inr hm'⟩]
    · rw [Compose.projAC_deadline]
      change tr.time k < tr.deadline y k (tr.time i) sp.Δ
      simpa only [he] using hlt
  · intro x i B hx hacc hai y j ell hy hc _ hdl hanc
    obtain ⟨ell₀, hc₀, hb⟩ := hacc
    have hpre := hrun.upTo (hrun.time_nonneg i)
    have hc₀' : (tr.upTo (tr.time i)).CallAt x i (.ac ell₀) :=
      (Trace.upTo_callAt tr).mpr ⟨le_rfl, Compose.projAC_callAt.mp hc₀⟩
    obtain ⟨i', rfl, hi', hti⟩ := Compose.acBlock_prev hpre.toLocalRun hx hc₀' hb
    change tr.time i' = tr.time (i' + 1) at hti
    obtain ⟨hi't, hi'⟩ := (Trace.upTo_callAt tr).mp hi'
    have hpy := hrun.upTo (hrun.time_nonneg j)
    have hc' : (tr.upTo (tr.time j)).CallAt y j (.ac ell) :=
      (Trace.upTo_callAt tr).mpr ⟨le_rfl, Compose.projAC_callAt.mp hc⟩
    have hfr : ell.frame.F = (tr.state y j).fg.F := by
      have h := (hpy.toLocalRun.cutLaw y hy j _ hc').1
      rw [RunTrace.upTo_state_of_le hm le_rfl] at h
      rw [h]
      rfl
    have hgi : g ≤ tr.time i' := hti ▸ hg.trans hai
    have he : max (tr.time i') g = tr.time i' := max_eq_left hgi
    obtain ⟨k, hkj, hk, hlt⟩ := hs.relay x i' B (hrun.antitone hi't hx) hi' hgi y j hy
      ⟨_, Compose.projAC_callAt.mp hc⟩
      (by rw [he, hti, ← Compose.projAC_deadline]; exact hdl) (hfr ▸ hanc)
    have hk' := (RunTrace.upTo_acceptAt tr).mpr ⟨hm hkj, hk⟩
    obtain ⟨ell', hc'', hb', htk⟩ := Compose.accept_next hpy.toLocalRun hy hk'
    change tr.time (k + 1) = tr.time k at htk
    have hkj' : k + 1 ≤ j := by
      rcases Nat.lt_or_eq_of_le hkj with hlt' | rfl
      · omega
      · cases Option.some.inj (hk.2.symm.trans (Compose.projAC_callAt.mp hc).2)
    have hc₁ := (Trace.upTo_callAt tr).mp hc'' |>.2
    have hnr : ¬ tr.RestartAt y (k + 1) := fun ⟨ellr, hcr, hr⟩ => by
      cases Option.some.inj (hc₁.2.symm.trans hcr.2)
      rw [hb'] at hr
      cases hr
    refine ⟨k + 1, hkj', ⟨ell', Compose.projAC_callAt.mpr hc₁, hb'⟩, ?_⟩
    rw [Compose.projAC_deadline]
    change tr.time (k + 1) < tr.deadline y (k + 1) (tr.time (i' + 1)) sp.Δ
    rw [htk, ← hti]
    rw [he] at hlt
    simpa only [RunTrace.deadline, RunTrace.lastWake, hnr, ite_false] using hlt

end Consensus.Goldilocks.Healing.Growing

end
