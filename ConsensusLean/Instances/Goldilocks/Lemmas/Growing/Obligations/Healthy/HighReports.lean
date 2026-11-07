module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase

public section

/-! # High origins and the heights above them, under growing faults

The growing forms of the high-origin lemmas of `Healing/Retention/High`, with each node honest at
its own cut and a held-state reader honest at an observation time after the state's cuts:

* `frame_tree_subset_at`: an AC call frame of a node honest at the call is well formed and lies in
  the node's held tree;
* `highOrigin_mem_at`: a high origin's block is held at its write;
* `ResetPremisesUpTo.high_of_anc_at`: a held descendant of a high origin has height above `H_z`. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a : Time}

/-! ### Prefix transport of call-local SA events -/

/-- A fast-lock write at a cut by `d` is one of the prefix through `d`. -/
theorem fastLockAt_upTo_iff (hmono : Monotone tr.time) {d : Time} {x : Fin sp.n} {i s : Nat}
    (hi : tr.time i ≤ d) {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)} :
    SA.FastLockAt (tr.upTo d).projAC x i s B CV ↔ SA.FastLockAt tr.projAC x i s B CV := by
  have hs : (tr.projAC.upTo d).state x i = tr.projAC.state x i :=
    Trace.upTo_state tr.projAC x (fun k hk => (hmono hk.le).trans hi)
  have hc : ∀ ℓ, (tr.projAC.upTo d).CallAt x i ℓ ↔ tr.projAC.CallAt x i ℓ := fun _ =>
    Trace.upTo_callAt_of_le tr.projAC hi
  rw [RunTrace.upTo_projAC]
  simp only [SA.FastLockAt, SA.FastUpdateAt, SA.OptimisticLockAt, SA.OptimisticPoint,
    SA.UpdateAt, hs, hc, Trace.upTo_time]

/-- An `ac_to_fg` call at a cut by `d` is one of the prefix through `d`. -/
theorem toFGAt_upTo_iff (hmono : Monotone tr.time) {d : Time} {x : Fin sp.n} {i : Nat}
    (hi : tr.time i ≤ d) {ℓ : ACLabel (goldilocksNode sp ro)}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} :
    SA.ToFGAt (tr.upTo d).projAC x i ℓ C ↔ SA.ToFGAt tr.projAC x i ℓ C := by
  have hs : (tr.projAC.upTo d).state x i = tr.projAC.state x i :=
    Trace.upTo_state tr.projAC x (fun k hk => (hmono hk.le).trans hi)
  rw [RunTrace.upTo_projAC]
  simp only [SA.ToFGAt, hs, Trace.upTo_callAt_of_le tr.projAC hi, Trace.upTo_time]

/-- Joinedness at a time `t ≤ d` reads only restarts by `t`, which the prefix through `d` keeps. -/
theorem joinedAt_upTo_iff {d t : Time} (htd : t ≤ d) {y : Fin sp.n} :
    (tr.upTo d).JoinedAt y t ↔ tr.JoinedAt y t := by
  unfold RunTrace.JoinedAt
  simp only [RunTrace.upTo_restartAt, Trace.upTo_time]
  exact ⟨fun h k hk hkt => h k ⟨hkt.trans htd, hk⟩ hkt, fun h k hk hkt => h k hk.2 hkt⟩

/-- The frame of an AC call of a node honest at it is well formed and lies in its held tree (the
static `frameIn_of_callAt` and `frame_tree_subset` on the prefix through the call). -/
theorem frame_tree_subset_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y k ℓ) :
    FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ (tr.state y k).fg.tree := by
  have hd := hrun.time_nonneg k
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time k)) (tr.upTo (tr.time k))
    proposer (hrun.upTo hd) (hnc.upTo _)).localRun
  have hc' : (tr.upTo (tr.time k)).projAC.CallAt y k ℓ := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hc
  refine ⟨(SA.frameIn_of_callAt hr hy hc').1, ?_⟩
  rw [Compose.frame_of_projAC (hrun.upTo hd) hy hc',
    RunTrace.upTo_state_of_le hrun.time_mono le_rfl]
  exact fun B hB => hB.1

/-- A high origin's block is held by its writer at the write. -/
theorem highOrigin_mem_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) :
    B ∈ (tr.state x i).fg.tree := by
  obtain ⟨hx, -, ⟨CV, ℓ, D, hc, hfl, rfl⟩, -⟩ := ho
  obtain ⟨ℓ', hc', hD⟩ := Healing.fastLock_mem hfl
  obtain rfl : ℓ = ℓ' := Option.some.inj (hc.2.symm.trans hc'.2)
  obtain ⟨hok, hsub⟩ := frame_tree_subset_at hrun hnc hx hc
  exact hsub (SA.viableAncestor_anc hok hD).1

/-- A report's block is held in the reporter's tree, for a reporter honest at the report (the
static `toFG_mem_tree` on the prefix through the report). -/
theorem toFG_mem_tree_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {y : Fin sp.n} {k : Nat}
    (hy : y ∈ H (tr.time k)) {ℓ : ACLabel (goldilocksNode sp ro)}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hto : SA.ToFGAt tr.projAC y k ℓ C) :
    C ∈ (tr.state y k).fg.tree := by
  have h := Healing.toFG_mem_tree (hrun.upTo (hrun.time_nonneg k)) hy
    ((toFGAt_upTo_iff hrun.time_mono le_rfl).mpr hto)
  rwa [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h

namespace ResetPremisesUpTo

variable {b : Time}

/-- A held descendant of a high origin has high state height, at a holder honest at an
observation time after the held state's cuts. -/
theorem high_of_anc_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {x : Fin sp.n}
    {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B)
    {z : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hz : z ∈ H t) {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state z k).fg.tree) (hBW : Anc (tr.HonestBlocksAt H) B W) :
    HZ tr H g + 1 ≤ ((tr.state z k).fg.σ W.root).h := by
  have hBx := highOrigin_mem_at hp.run hp.noColl ho
  have hBz := mem_of_honest_anc_at hp.run hp.noColl ht hle hz hBW hW
  have h₁ := Healing.h_le_of_store_anc (fg_reachable_at hp.run ht hle hz)
    (store_anc_of_honest_anc_at hp.run hp.noColl ht hle hz hBW hW)
  rw [← σ_eq_honest_at hp.run hp.noColl (hp.run.time_nonneg i)
    (fun _ hq => hp.run.time_mono hq.le) ho.1 ht hle hz hBx hBz] at h₁
  exact ho.2.2.2.trans h₁

/-- **A high report has a stored high origin written before it**, under growing faults: the
report's block `C` of a node honest at its report is below the stored viable image `O` of an
earlier fast-lock write of the same node, and `O` is high as `C ⪯ O` is. -/
theorem high_report_origin_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} {r : Nat} (hz : z ∈ H (tr.time r)) {ell : ACLabel (goldilocksNode sp ro)}
    {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hrep : SA.ToFGAt tr.projAC z r ell C) (hrb : tr.time r ≤ b)
    (hhC : HZ tr H g + 1 ≤ ((tr.state z r).fg.σ C.root).h) :
    ∃ io < r, ∃ jo O D CV, HighOrigin tr H g z io jo O ∧ tr.time io ≤ b ∧
      SA.FastLockAt tr.projAC z io jo D CV ∧ Anc (tr.HonestBlocksAt H) C O ∧
      Anc (tr.HonestBlocksAt H) O D := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hd := hrun.time_nonneg r
  have hrun' := hrun.upTo hd
  have hU' := RunTrace.honestBlocks_upTo_subset hrun.time_mono (H := H) hd
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time r)) (tr.upTo (tr.time r))
    proposer hrun' (hnc.upTo _)).localRun
  have hrep' := (toFGAt_upTo_iff hrun.time_mono le_rfl).mpr hrep
  obtain ⟨hpc, _, hC'⟩ := hrep'
  obtain ⟨hCv, l, hl, hlb, hlf, _⟩ := SA.toFG_candidate hC'
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, _, rfl⟩ := hl
  obtain ⟨io, hio, CV, ellw, D, hcw, hfl, L, hL, hLr, hLO⟩ :=
    Healing.stored_fast_lock_provenance hr hz r l₀ hl₀ hlf
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hz hpc
  obtain ⟨hPhiw, hPhiwU⟩ := SA.frameIn_of_callAt hr hz hcw
  obtain ⟨hvat, hva⟩ := SA.viableAncestor_anc hPhi hB₀
  obtain rfl : C = ell.frame.viableAncestor B₀ :=
    hr.coherent.1 (hPhiU hCv.1) (hPhiU hvat) hlb.symm
  obtain rfl : L = B₀ := hr.coherent.1 hL (hPhiU hB₀) (hLr.trans hB₀r.symm)
  have hior : tr.time io ≤ tr.time r := hrun.time_mono hio.le
  have hcwt : tr.projAC.CallAt z io ellw := by
    rw [RunTrace.upTo_projAC] at hcw
    exact ((Trace.upTo_callAt _).mp hcw).2
  have hflt : SA.FastLockAt tr.projAC z io l₀.slot D CV :=
    (fastLockAt_upTo_iff hrun.time_mono hior).mp hfl
  let O := ellw.frame.viableAncestor D
  have hCO : Anc (tr.HonestBlocksAt H) (ell.frame.viableAncestor L) O :=
    Anc.mono hU' ((hva.mono hPhiU).trans hLO)
  have hzi : z ∈ H (tr.time io) := hrun.antitone hior hz
  have hDw : D ∈ ellw.frame.tree := by
    obtain ⟨ℓ', hc', hD⟩ := Healing.fastLock_mem hflt
    obtain rfl : ellw = ℓ' := Option.some.inj (hcwt.2.symm.trans hc'.2)
    exact hD
  have hOD := SA.viableAncestor_anc hPhiw hDw
  have hOt : O ∈ (tr.state z io).fg.tree :=
    (frame_tree_subset_at hrun hnc hzi hcwt).2 hOD.1
  have hle : ∀ q < r, tr.time q ≤ tr.time r := fun _ hq => hrun.time_mono hq.le
  have hlei : ∀ q < io, tr.time q ≤ tr.time io := fun _ hq => hrun.time_mono hq.le
  have hOr : O ∈ (tr.state z r).fg.tree := by
    have h := Compose.tree_mono hrun'.toLocalRun hz hio.le
      (show O ∈ ((tr.upTo (tr.time r)).state z io).fg.tree by
        rwa [RunTrace.upTo_state_of_le hrun.time_mono hior])
    rwa [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h
  have hOh : HZ tr H g + 1 ≤ ((tr.state z io).fg.σ O.root).h := by
    rw [← σ_eq_honest_at hrun hnc hd hle hz (hrun.time_nonneg io) hlei hzi hOr hOt]
    exact hhC.trans (Healing.h_le_of_store_anc (fg_reachable_at hrun hd hle hz)
      (store_anc_of_honest_anc_at hrun hnc hd hle hz hCO hOr))
  have hj : tr.JoinedAt z (tr.time io) := by
    exact (joinedAt_upTo_iff hior).mp (Healing.joinedAt_of_fastLockAt hrun' (hnc.upTo _) hz hfl)
  refine ⟨io, hio, l₀.slot, O, D, CV, ?_, hior.trans hrb, hflt, hCO,
    Anc.mono hU' (hOD.2.mono hPhiwU)⟩
  exact ⟨hzi, hj, ⟨CV, ellw, D, hcwt, hflt, rfl⟩, hOh⟩

end ResetPremisesUpTo

end Consensus.Goldilocks.Healing.Growing

end
