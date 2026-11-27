module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Inclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Lift
public import ConsensusLean.Instances.Goldilocks.Results.Spec.SleepyGrowth
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Sleepy strict growth (R.2) at a committee: the finite inputs from the rows' premises

The rows `IncludeSleepy` and `GrowSleepy` (`Results/Statements/SleepyGrowth`, proved in
`Proofs/Growing/SleepyGrowth/Main` from `include_sleepy_at` and `grow_sleepy_at`) read the finite
inputs of those rows through `b = t` and `b = t + D`; they are derived from the rows' premises,
not assumed:

* `sleepyBoundsFrom_of_sleepyRunAt`: `SleepyRunAt` with look-ahead `5Δ` gives the count shapes
  `SleepyBoundsFrom 0 b` at every `b`. The slot and late counts follow from the counts at
  `t_s + Δ` and `t_s + 2Δ` charged `5Δ` later by monotonicity of the charge; `2 f_d < n` at a time
  `d ≥ 0` follows from the count at the start `t_s ≤ d` of its slot, charged at `t_s + 5Δ`, since
  `d < t_s + 4Δ` and the honest set only shrinks.
* `sleepyServiceBefore_of_syncOnAt`: the synchrony of `SleepyRunAt` (`Sync[0, ∞)`) gives the finite
  service `SleepyServiceBefore` through every `b`;
* `CommitteeSleepy.boundsFrom`: the committee support gives the committee count shapes
  `CommitteeBoundsFrom K 0 b` at every `b`. -/

namespace Consensus.Goldilocks.Regimes.Growing

open AC (ACParams Payload)
open Compose.Growing

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **The count shapes from `Sleepy`** with look-ahead `5Δ`, through every `b`, for an antitone
honest set. -/
theorem sleepyBoundsFrom_of_sleepyRunAt (hanti : Antitone H)
    (hsl : tr.SleepyRunAt H ΔF (5 * sp.Δ)) (b : Time) : SleepyBoundsFrom tr H 0 b := by
  have hΔ := sp.toParams.hΔ
  have hpt : ∀ (s : Nat) (d : Time), d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time) →
      tr.FaultBoundAt H (sp.ts s + d) (sp.ts s + d + 5 * sp.Δ) := fun s d hd => by
    simpa only [sp.slotTime_eq, AC.ACParams.ts] using hsl.2 s d hd
  refine ⟨fun d h0 _ => ?_, fun s d _ h1 _ h6 => ?_, fun s d _ h1 _ h7 => ?_⟩
  · set s := sp.slot d
    have hts : sp.ts s ≤ d := (AC.ts_le_iff_le_slot sp h0 (s : Int)).2 le_rfl
    have hlt : d < sp.ts s + 4 * sp.Δ := by
      have h := (AC.ts_le_iff_le_slot sp h0 ((s : Int) + 1)).not.2 (by omega)
      simp only [AC.ACParams.ts] at h hts ⊢
      linarith
    have h := RunTrace.FaultBoundAt.mono_right hanti (d' := d) (by linarith)
      (hpt s 0 (by simp))
    have hle : {y | y ∈ H d ∧ tr.awake y (sp.ts s + 0) ∧ tr.JoinedAt y (sp.ts s + 0)}.ncard ≤
        (H d).ncard := Set.ncard_le_ncard fun x hx => hx.1
    have hn : (H d).ncard + (H d)ᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    have : (H d)ᶜ.ncard <
        {y | y ∈ H d ∧ tr.awake y (sp.ts s + 0) ∧ tr.JoinedAt y (sp.ts s + 0)}.ncard := h
    omega
  · exact RunTrace.FaultBoundAt.mono_right hanti (by linarith) (hpt s sp.Δ (by simp))
  · exact RunTrace.FaultBoundAt.mono_right hanti (by linarith) (hpt s (2 * sp.Δ) (by simp))

/-- **The finite service from the synchrony of `Sleepy`** (`Sync[0, ∞)`), through every `b`:
AC message service from the processing of each message before its deadline, and node acceptance
relay; the AC acceptance relay follows (`sleepyServiceBefore_of_message_relay_at`). -/
theorem sleepyServiceBefore_of_syncOnAt {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hs : tr.SyncOnAt H ΔF (fun τ => 0 ≤ τ) (fun τ => 0 ≤ τ) id) (b : Time) :
    SleepyServiceBefore tr H sp.Δ b := by
  have hm := hrun.time_mono
  apply Obligations.Growing.sleepyServiceBefore_of_message_relay_at hrun
  · intro x i m hx hsa hai y j ell hy hc _ hdl
    obtain ⟨ell₀, hc₀, hmsg⟩ := hsa
    have hpre := hrun.upTo (hrun.time_nonneg i)
    have hstate : tr.projAC.state x i = (tr.state x i).ac := by
      have h := Compose.projAC_state hpre.toLocalRun hx i
      rwa [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC x (fun _ hk => hm hk.le),
        RunTrace.upTo_state_of_le hm le_rfl] at h
    have hsa' : tr.SendOrAdmitAt x i m := ⟨ell₀, Compose.projAC_callAt.mp hc₀, by
      rwa [hstate] at hmsg⟩
    obtain ⟨k, hkj, htk, hp, hlt⟩ := hs.message x i m hx hsa' hai y j hy
      ⟨_, Compose.projAC_callAt.mp hc⟩ (by rw [← Compose.projAC_deadline]; exact hdl)
    apply (AC.messageServedBefore_iff _ _ _ _).mpr
    refine Or.inl ⟨k, hkj, htk, ?_, ?_⟩
    · rcases hp with ⟨ell', hc', hm'⟩ | ⟨ell', hc', hm'⟩
      exacts [⟨ell', Compose.projAC_callAt.mpr hc', Or.inl hm'⟩,
        ⟨ell', Compose.projAC_callAt.mpr hc', Or.inr hm'⟩]
    · rw [Compose.projAC_deadline]
      exact hlt
  · intro x i B hx hB hai y j hy hj _ hdl hanc
    exact hs.relay x i B hx hB hai y j hy hj hdl hanc

/-- **The committee count shapes from the committee support**, through every `b`. -/
theorem CommitteeSleepy.boundsFrom {K : AC.CommitteeDict sp.n} (h : CommitteeSleepy tr H K)
    (b : Time) : CommitteeBoundsFrom tr H K 0 b :=
  ⟨fun s d _ h1 _ h6 => h.1 s d h1 h6, fun s d _ h0 _ h2 => h.2 s d h0 h2⟩

end Consensus.Goldilocks.Regimes.Growing

end
