module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularSlowWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularSlowBoundary
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Next-slot votes after a historical regular slow selection -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)
open Compose.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The actual slow selection constrains next-slot voters honest at their own casts. -/
theorem regular_slow_next_votes_at {s₀ s floor : Nat}
    {kindJ : Prop} {J D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts s + 6 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hwarm : s₀ + sp.k ≤ s) (hpos : 0 < s) (hs₀ : s₀ ≤ s - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hmb : sp.ts s + 6 * sp.Δ ≤ b)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c))
    (hsl : SA.SlowLockAt tr.projAC x c s D) :
    ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg D := by
  have hΔ := sp.toParams.hΔ
  have hslow : gbar g ≤ sp.ts ((s : Int) - sp.k + 1) := by
    have hts : sp.ts s₀ ≤ sp.ts ((s : Int) - sp.k + 1) :=
      (SA.ts_le_iff sp).mpr (by omega)
    linarith
  have hm' : gbar g + 4 * sp.Δ ≤ sp.ts ((s - 1 : Nat) : Int) :=
    hm.trans ((SA.ts_le_iff sp).mpr (by exact_mod_cast hs₀))
  have hprev : sp.ts ((s - 1 : Nat) : Int) = sp.ts s - 4 * sp.Δ := by
    rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one, SA.ts_sub_one]
  have hms : gbar g + 4 * sp.Δ ≤ sp.ts s := by linarith
  obtain ⟨ellx, C, hu, hconf, hsel⟩ := hsl
  have hsl : SA.SlowLockAt tr.projAC x c s D := ⟨ellx, C, hu, hconf, hsel⟩
  have hres : SA.ResultAt tr.projAC x c s C
      (SA.fastCounted sp (tr.projAC.state x c) ellx.frame s C) := ⟨ellx, hu, hconf, rfl⟩
  obtain ⟨z, q, hz, hqc, e, ⟨ell, hc, he⟩, -, hes, Q, hQU, hQr, hCQ⟩ :=
    result_honest_supporter_before_at hrun hnc hsvc hawake hf hcatch hnr hms hx hres
      (hu.2.2.1.trans_le hmb)
  have hDC := ((SA.deepest_mem hsel).1.1.2.2).mono (frameIn_at hrun hnc hx hu.1).2
  have hDQ := hDC.trans hCQ
  have hr := (acRun_upTo hrun hnc (hrun.time_nonneg q)).localRun
  have hc' := SA.upTo_castAt.mpr ⟨le_rfl, hc, he⟩
  have htq := SA.vote_time_le hr hz ⟨ell, hc'.1, he⟩
  have hslot := (SA.castAt_spec hr hz hc').2.1.symm.trans hes
  change sp.slot (tr.time q) = s at hslot
  change tr.time q ≤ sp.ts (sp.slot (tr.time q)) + sp.Δ at htq
  rw [hslot] at htq
  apply hframe.next_votes_of_supporter_at hrun hnc hsvc hawake hf hcatch hnr
    hwarm hpos hs₀ hm' hmb hz ⟨hc, he⟩ hes hQU hQr hDQ
  · intro hQ hh hJD
    have hs₀s : s₀ ≤ s := by omega
    have hrestrict : FrameWindow tr H (sp.ts s) (sp.ts s + 6 * sp.Δ) floor kindJ J :=
      ⟨fun y i hy hlo hhi => hframe.floor_eq y i hy
          (((SA.ts_le_iff sp).mpr (by exact_mod_cast hs₀s)).trans hlo) hhi,
       fun y i hy hlo hhi => hframe.kind_iff y i hy
          (((SA.ts_le_iff sp).mpr (by exact_mod_cast hs₀s)).trans hlo) hhi,
       fun y i hy hlo hhi => hframe.root_eq y i hy
          (((SA.ts_le_iff sp).mpr (by exact_mod_cast hs₀s)).trans hlo) hhi⟩
    exact regular_slow_next_votes_of_early_witness_at hrun hnc hsvc hawake hf hcatch
      (by linarith) hslow hmb hrestrict hx hsl hres hCQ hz (by linarith) hc hQ hh hJD
  · intro hA a D' CV' hza hop hQD
    have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := SA.ts_succ s
    have hnext : FrameWindow tr H (sp.ts s₀)
        (sp.ts (s + 1 : Nat) + sp.Δ) floor kindJ J :=
      ⟨fun y i hy hlo hhi => hframe.floor_eq y i hy hlo (by linarith),
       fun y i hy hlo hhi => hframe.kind_iff y i hy hlo (by linarith),
       fun y i hy hlo hhi => hframe.root_eq y i hy hlo (by linarith)⟩
    exact (hnext.optimistic_supporter_later_heads_at hrun hnc hsvc hawake hf hcatch hnr
      (by linarith) (by omega) (by omega) (by linarith)
      hz hza ⟨hc, he⟩ hes hA hop hQD (s + 1) le_rfl le_rfl).1

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
