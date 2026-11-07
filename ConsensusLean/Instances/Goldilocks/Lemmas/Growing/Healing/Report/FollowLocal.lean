module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AnchorPrefix
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Local report facts before compromise

Candidate compatibility is retained only through the reporter's own call. Warm joinedness
uses honesty at the vote deadline and antitonicity at each earlier restart.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A warm node is joined at the vote deadline, even if it is compromised afterwards. -/
theorem joined_voteTime_of_warm_frame_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {g : Time} {s₀ u : Nat} (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hs : s₀ + 1 ≤ u)
    {y : Fin sp.n} (hy : y ∈ H (sp.ts u + sp.Δ)) :
    SA.JoinedAt tr.projAC y (sp.ts u + sp.Δ) := by
  have hΔ := sp.toParams.hΔ
  have hslot : sp.slot (sp.ts u + sp.Δ) = u := by
    apply SA.slot_of_mem sp u
    all_goals simp only [SAParams.ts]; push_cast; linarith
  intro i hi hit
  change tr.time i ≤ sp.ts ((sp.slot (sp.ts u + sp.Δ) : Int) - 1)
  rw [hslot]
  have hiy : y ∈ H (tr.time i) := hrun.toLocalRun.antitone hit hy
  have hrestart := hnr y i hiy (Compose.projAC_restartAt.mp hi)
  have ht := (SA.ts_le_iff sp).2 (show (s₀ : Int) ≤ (u : Int) - 1 by omega)
  exact hrestart.trans (by linarith)

/-- Candidates at one honest call are compatible in the historical block universe. -/
theorem toFG_candidates_compatible_at_call_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ell) {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ SA.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i)) :
    ∀ C ∈ SA.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i),
      Compatible (tr.HonestBlocksAt H) C P := by
  have hr := hrun.toLocalRun
  have hd := hr.time_nonneg i
  have hs := Trace.upTo_state tr.projAC y (d := tr.time i) (i := i)
    (fun k hk => hr.time_mono hk.le)
  have hc' : (tr.upTo (tr.time i)).projAC.CallAt y i ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  have hp' : P ∈ SA.toFGCandidates sp ((tr.upTo (tr.time i)).projAC.state y i)
      ell.frame ((tr.upTo (tr.time i)).time i) := by
    simpa only [RunTrace.upTo_projAC, hs, Trace.upTo_time] using hP
  intro C hC
  have hcand : C ∈ SA.toFGCandidates sp ((tr.upTo (tr.time i)).projAC.state y i)
      ell.frame ((tr.upTo (tr.time i)).time i) := by
    simpa only [RunTrace.upTo_projAC, hs, Trace.upTo_time] using hC
  rcases Healing.toFG_candidates_compatible_at_call (hrun.upTo hd)
    (hnc.upTo (tr.time i)) hy hc' hp' C hcand with h | h
  · exact Or.inl (h.mono (RunTrace.honestBlocks_upTo_subset hr.time_mono hd))
  · exact Or.inr (h.mono (RunTrace.honestBlocks_upTo_subset hr.time_mono hd))

/-- An actual report above a slot-`u` block cannot precede slot `u`.
Only the reporter's honesty and fault bound at the report cut are used. -/
theorem toFG_time_ge_of_ancestor_slot_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i u : Nat}
    (hy : y ∈ H (tr.time i)) (hf : 3 * (H (tr.time i))ᶜ.ncard ≤ sp.n - 1)
    {ell : ACLabel (goldilocksNode sp ro)} {P R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : SA.ToFGAt tr.projAC y i ell R) (hPs : P.slot = u)
    (hPR : Anc (tr.HonestBlocksAt H) P R) : sp.ts u ≤ tr.time i := by
  have hr := hrun.toLocalRun
  have hd := hr.time_nonneg i
  have hp := hrun.upTo hd
  have hn := hnc.upTo (tr.time i)
  have hs := Trace.upTo_state tr.projAC y (d := tr.time i) (i := i)
    (fun k hk => hr.time_mono hk.le)
  have hR' : SA.ToFGAt (tr.upTo (tr.time i)).projAC y i ell R := by
    refine ⟨?_, hR.2.1, ?_⟩
    · rw [RunTrace.upTo_projAC]
      exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hR.1⟩
    · simpa only [RunTrace.upTo_projAC, hs, Trace.upTo_time] using hR.2.2
  have hac := Compose.goldilocks_ac_projection sp ro dg (H (tr.time i))
    (tr.upTo (tr.time i)) proposer hp hn
  have hPhi := SA.frameIn_of_callAt hac.localRun hy hR'.1
  have hRc := SA.toFG_candidate hR'.2.2
  have hRh : R ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) :=
    hPhi.2 hRc.1.1
  have hPR' := RunTrace.anc_upTo_of_right hr hnc hd hRh hPR
  obtain ⟨a, _, j, D, CV, ho, hRD, hj⟩ := Healing.toFG_fast_origin hp hn hy hR'
  have hPD := (Anc.slot_le hac.localRun.coherent (hPR'.trans hRD)).1
  have hDj := Healing.fast_selection_slot_le hp hn hf hy ho
  have hu : u ≤ sp.slot (tr.time i) := by
    simp only [Trace.upTo_time] at hj
    omega
  exact (SA.ts_le_iff_le_slot sp hd _).2 (by exact_mod_cast hu)

end Consensus.Goldilocks.Healing.Growing

end
