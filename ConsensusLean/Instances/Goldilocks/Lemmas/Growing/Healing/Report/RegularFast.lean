module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularFastWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularSupporter
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.SupporterLater
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Next-slot votes after a regular fast selection at its own honest cut -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)
open Compose.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Actual result provenance supplies the early supporter for the fast next-vote route. -/
theorem regular_fast_next_votes_at {s₀ s floor : Nat}
    {kindJ : Prop} {J X D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts s + 6 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hwarm : s₀ + sp.k ≤ s) (hpos : 0 < s) (hs₀ : s₀ ≤ s - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts ((s - 1 : Nat) : Int))
    (hmb : sp.ts s + 6 * sp.Δ ≤ b)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (SA.Vote sp.n)}
    (hfast : SA.FastUpdateAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocksAt H) X D) (hstock : sp.committeeSize = sp.n) :
    ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨ellx, C, hu, hconf, hsel, hCV⟩ := hfast
  have hfast : SA.FastUpdateAt tr.projAC x c s D CV :=
    ⟨ellx, C, hu, hconf, hsel, hCV⟩
  have hres : SA.ResultAt tr.projAC x c s C
      (SA.fastCounted sp (tr.projAC.state x c) ellx.frame s C) := ⟨ellx, hu, hconf, rfl⟩
  have hprev : sp.ts ((s - 1 : Nat) : Int) = sp.ts s - 4 * sp.Δ := by
    rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one, SA.ts_sub_one]
  have hms : gbar g + 4 * sp.Δ ≤ sp.ts s := by linarith
  obtain ⟨z, q, hz, hqc, e, ⟨ell, hc, he⟩, -, hes, Q, hQU, hQr, hCQ⟩ :=
    result_honest_supporter_before_at hrun hnc hsvc hawake hf hcatch hnr hms hx hres
      (hu.2.2.1.trans_le hmb) hstock
  have hDC := ((SA.deepest_mem hsel).1.1.2.2).mono (frameIn_at hrun hnc hx hu.1).2
  have hr := (acRun_upTo hrun hnc (hrun.time_nonneg q)).localRun
  have hc' := SA.upTo_castAt.mpr ⟨le_rfl, hc, he⟩
  have htq := SA.vote_time_le hr hz ⟨ell, hc'.1, he⟩
  have hslot := (SA.castAt_spec hr hz hc').2.1.symm.trans hes
  change sp.slot (tr.time q) = s at hslot
  change tr.time q ≤ sp.ts (sp.slot (tr.time q)) + sp.Δ at htq
  rw [hslot] at htq
  apply KernelProof.FrameWindow.next_votes_of_supporter_at hframe hrun hnc hsvc hawake hf hcatch hnr
    hwarm hpos hs₀ hm hmb hz ⟨hc, he⟩ hes hQU hQr (hXD.trans (hDC.trans hCQ)) ?_ ?_ hstock
  · intro hQ hh hJX
    have hs₀s : s₀ ≤ s := by omega
    have hrestrict : FrameWindow tr H (sp.ts s) (sp.ts s + 6 * sp.Δ) floor kindJ J :=
      ⟨fun y i hy hlo hhi => hframe.floor_eq y i hy
          (((SA.ts_le_iff sp).mpr (by exact_mod_cast hs₀s)).trans hlo) hhi,
       fun y i hy hlo hhi => hframe.kind_iff y i hy
          (((SA.ts_le_iff sp).mpr (by exact_mod_cast hs₀s)).trans hlo) hhi,
       fun y i hy hlo hhi => hframe.root_eq y i hy
          (((SA.ts_le_iff sp).mpr (by exact_mod_cast hs₀s)).trans hlo) hhi⟩
    exact regular_fast_next_votes_of_early_witness_at hrun hnc hsvc hawake hf hcatch hnr
      (by linarith) hmb hrestrict hx hfast hres hXD hCQ hz (by linarith) hc hQ hh hJX hstock
  · intro hA a D' CV' hza hop hQD
    have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := SA.ts_succ s
    have hnext : FrameWindow tr H (sp.ts s₀)
        (sp.ts (s + 1 : Nat) + sp.Δ) floor kindJ J :=
      ⟨fun y i hy hlo hhi => hframe.floor_eq y i hy hlo (by linarith),
       fun y i hy hlo hhi => hframe.kind_iff y i hy hlo (by linarith),
       fun y i hy hlo hhi => hframe.root_eq y i hy hlo (by linarith)⟩
    exact (optimistic_supporter_later_heads_at hnext hrun hnc hsvc hawake hf hcatch hnr
      (by linarith) (by omega) (by omega) (by linarith)
      hz hza ⟨hc, he⟩ hes hA hop hQD hstock (s + 1) le_rfl le_rfl).1

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
