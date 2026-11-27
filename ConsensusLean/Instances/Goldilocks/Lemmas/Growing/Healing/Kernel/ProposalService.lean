module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Relay

public section

/-! # Owed reset service on the AC projection

The source and recipient are retained at separate horizons. A sender's later
compromise never discharges a message or block already owed to the reader.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF b lo hi : Time}
variable {hold : Time}

/-- The AC part of the reset service projected with source honesty at release and reader
honesty at its call. -/
theorem ACResetService.ac_service_at (hs : ACResetService tr H g ΔF)
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) (hg : g ≤ lo) :
    AC.Growing.ServiceWindowBefore H (tr.HonestBlocksAt H) lo hi tr.projAC := by
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
    apply (AC.messageServedBefore_iff _ _ _ _).mpr
    refine Or.inl ⟨k, hkj, htk, ?_, ?_⟩
    · rcases hp with ⟨ell', hc', hm'⟩ | ⟨ell', hc', hm'⟩
      exacts [⟨ell', Compose.projAC_callAt.mpr hc', Or.inl hm'⟩,
        ⟨ell', Compose.projAC_callAt.mpr hc', Or.inr hm'⟩]
    · rw [Compose.projAC_deadline]
      change tr.time k < tr.deadline y k (tr.time i) sp.Δ
      simpa only [he] using hlt
  · intro x i B hx hacc hai y j ell hy hc _ hdl hanc
    apply hrun.toLocalRun.acRelayAt (σ := tr.time i) hx hacc hy hc hanc
    intro k hki hx' hk hj hF
    have hgi : g ≤ tr.time k := hki ▸ hg.trans hai
    have he : max (tr.time k) g = tr.time i := (max_eq_left hgi).trans hki
    simpa only [he] using hs.relay x k B hx' hk hgi y j hy hj
      (by rw [he, ← Compose.projAC_deadline]; exact hdl) hF

/-- Reset service projected with source honesty at release and reader honesty at its call. -/
theorem ResetService.ac_service_at (hs : ResetService tr H g ΔF b hold)
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) (hg : g ≤ lo) :
    AC.Growing.ServiceWindowBefore H (tr.HonestBlocksAt H) lo hi tr.projAC :=
  hs.toAC.ac_service_at hrun hg

end Consensus.Goldilocks.Healing.Growing

end
