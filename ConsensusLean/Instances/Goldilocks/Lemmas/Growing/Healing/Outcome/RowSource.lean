module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.DeepQuarantine
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Lift

public section

/-! # Local provenance of an attestation's replay entry

The extraction uses only the signer's local execution. No reset, cache invariant,
or service premise is reconstructed for a retained cohort.
-/

namespace Consensus.Goldilocks.Healing.Growing.Outcome

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}

private theorem fastLock_frame_mem {x : Fin sp.n} {i s : Nat}
    {D : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (h : AC.FastLockAt tr.projAC x i s D CV) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt x i ell) : D ∈ ell.frame.tree := by
  rcases h with ⟨ell', C, ⟨hc', -⟩, -, hD, -⟩ | ⟨ell', A, ⟨hc', -⟩, -, hsel, -⟩
  · obtain rfl : ell' = ell := Option.some.inj (hc'.2.symm.trans hc.2)
    exact (AC.deepest_mem hD).1.1.1
  · obtain rfl : ell' = ell := Option.some.inj (hc'.2.symm.trans hc.2)
    unfold AC.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    exact (AC.deepest_mem hsel).1.1

/-- The signed entry comes from a prior stored fast lock of the signer, when the source call is a
fast-lock candidate (`hfast`, needed only at sources at least as high as the row): a deep source
need not sit below a fast lock. This local extraction does not mention a reset or a snapshot
height. -/
theorem signed_entry_source
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    {v : Fin sp.n} (hv : v ∈ H) {d : Nat} {att : FG.Att sp.n}
    (hs : tr.SignAt v d att)
    (hfast : ∀ d' ell C, d' < d → AC.ToFGAt tr.projAC v d' ell C →
      att.h ≤ ((tr.state v d').fg.σ C.root).h →
      C ∈ AC.toFGCandidates sp (tr.projAC.state v d') ell.frame (tr.time d')) :
    ∃ r < d, ∃ l O, tr.JoinedAt v (tr.time r) ∧
      (∃ CV, Compose.StoredFastLockAt tr v r l O CV) ∧
      att.h ≤ ((tr.state v r).fg.σ O.root).h ∧
      ∃ E ∈ (tr.state v r).fg.tree, (tr.state v r).fg.Anc E O ∧
        E.root = att.T ∧ ((tr.state v r).fg.σ E.root).h = att.h ∧
        ((tr.state v r).fg.σ E.root).Th = E.root := by
  have hr := (Compose.goldilocks_ac_projection_from hrun hnc).localRun
  have hU := hr.coherent
  obtain ⟨C, hcall⟩ := hs
  obtain ⟨d', rfl, ell, hc', hto, -, hC, hfgeq⟩ :=
    Compose.attest_source hrun.toLocalRun hv hcall
  have hpc : tr.projAC.CallAt v d' ell := Compose.projAC_callAt.mpr hc'
  have hC' : (AC.acToFG sp (tr.projAC.state v d') ell.frame (tr.time d')).2 = some C := by
    rw [Compose.projAC_state hrun.toLocalRun hv]
    exact hC
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hv hpc
  have hCt : C ∈ ell.frame.tree := (AC.toFG_source hC').1.1
  let st := (tr.state v (d' + 1)).fg
  have hreach := Compose.fg_reachable hrun.toLocalRun hv (d' + 1)
  have hCst : C ∈ st.tree := by
    change C ∈ (tr.state v (d' + 1)).fg.tree
    rw [hfgeq]
    exact Healing.mem_tree_of_frame hrun hv hpc hCt
  have hcut := (hrun.cutLaw v hv (d' + 1) _ hcall).1
  obtain ⟨hah, haT⟩ := Store.createAtt_eq hcut
  obtain ⟨⟨E, hE, hEr, hEC, hEh, hETh⟩, -⟩ :=
    Store.entry_state_of_source sp.toParams (Payload sp.n) _ st hreach _ hCst
  have hEh' : (st.σ E.root).h = att.h := by rw [hah, hEr]
  have hETh' : (st.σ E.root).Th = E.root := by rw [hETh, hEr]
  have hEr' : E.root = att.T := by
    rw [haT]
    change E.root = (st.σ (st.σ _).Th).Th
    rw [← hEr, hETh']
  -- the source is a fast-lock candidate: it is at least as high as the row
  have hCh : att.h ≤ ((tr.state v d').fg.σ C.root).h := by
    have := Healing.h_le_of_store_anc hreach hEC
    rw [hEh'] at this
    change _ ≤ ((tr.state v (d' + 1)).fg.σ C.root).h at this
    rwa [← hfgeq]
  obtain ⟨hCv, l, hl, hlb, hlf, -⟩ := hfast d' ell C (by omega) ⟨hpc, hto, hC'⟩ hCh
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := hl
  obtain ⟨r, hrd, CV, ellw, D, hcw, hfl, L, hL, hLr, hLO⟩ :=
    Healing.stored_fast_lock_provenance hr hrun.vstart hv d' l₀ hl₀ hlf
  obtain ⟨hPhiw, -⟩ := AC.frameIn_of_callAt hr hv hcw
  obtain ⟨hvat, hva⟩ := AC.viableAncestor_anc hPhi hB₀
  obtain rfl : C = ell.frame.viableAncestor B₀ := hU.1 (hPhiU hCt) (hPhiU hvat) hlb.symm
  obtain rfl : L = B₀ := hU.1 hL (hPhiU hB₀) (hLr.trans hB₀r.symm)
  set O := ellw.frame.viableAncestor D
  have hCO : Anc (tr.HonestBlocks H) (ell.frame.viableAncestor L) O :=
    (hva.mono hPhiU).trans hLO
  have hOt : O ∈ (tr.state v r).fg.tree :=
    Healing.mem_tree_of_frame hrun hv hcw
      (AC.viableAncestor_anc hPhiw (fastLock_frame_mem hfl hcw)).1
  have hOst : O ∈ st.tree := Compose.tree_mono hrun.toLocalRun hv (by omega) hOt
  have hCOst := Healing.store_anc_of_honest_anc hrun hnc hv hCO hOst
  have hσO := Healing.σ_eq_honest hrun hnc hv hv hOst hOt
  have hOh : att.h ≤ ((tr.state v r).fg.σ O.root).h := by
    rw [← hσO]
    have := Healing.h_le_of_store_anc hreach hCOst
    rw [← hEh] at this
    omega
  have hsub : st.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨v, hv, d' + 1, hX⟩
  have hEO : Anc (tr.HonestBlocks H) E O := (hEC.mono hsub).trans hCO
  have hEt := Healing.mem_of_honest_anc hrun hnc hv hEO hOt
  have hσE := Healing.σ_eq_honest hrun hnc hv hv hEt hE
  refine ⟨r, by omega, l₀.slot, O, Healing.joinedAt_of_fastLockAt hrun hnc hv hfl,
    ⟨CV, ellw, D, hcw, hfl, rfl⟩, hOh, E, hEt,
    Healing.store_anc_of_honest_anc hrun hnc hv hEO hOt,
    hEr', ?_, ?_⟩
  · rw [hσE, hEh']
  · rw [hσE, hETh']

/-- A high signed row by a signer honest at it and at `c_z` has an earlier high origin, honest at
its own write and at `c_z`. The snapshot height is used only as a numerical lower bound. The row
is signed before the deep quarantine ends (`hq`), so its high source is a fast-lock candidate
(`KernelProof.high_toFG_fast_at`). -/
theorem high_row_source_at
    {H : Time → Set (Fin sp.n)}
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g : Time}
    {v : Fin sp.n} {d : Nat} {att : FG.Att sp.n}
    (hvz : v ∈ H (max (cutZ sp.toParams g) (tr.time d))) (hs : tr.SignAt v d att)
    (hh : HZ tr H g + 1 ≤ att.h) (hsnap : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g))
    (hq : ∀ D, sp.deepDepth = some D → tr.time d ≤ cutZ sp.toParams g + 4 * D * sp.Δ) :
    ∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧
      ∃ E ∈ (tr.state v r).fg.tree, (tr.state v r).fg.Anc E O ∧
        E.root = att.T ∧ ((tr.state v r).fg.σ E.root).h = att.h ∧
        ((tr.state v r).fg.σ E.root).Th = E.root := by
  have ht := hrun.time_nonneg d
  have hv := hrun.antitone (le_max_right _ _) hvz
  have hs' := (RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩
  obtain ⟨r, hrd, l, O, hj, hstored, hOh, E, hE, hEO, hEr, hEh, hETh⟩ :=
    signed_entry_source (hrun.upTo ht) (hnc.upTo _) hv hs' fun d' ell C hd' hto hCh => by
      have hd't : tr.time d' ≤ tr.time d := hrun.time_mono hd'.le
      have hto' := (toFGAt_upTo_iff hrun.time_mono hd't).mp hto
      rw [RunTrace.upTo_state_of_le hrun.time_mono hd't] at hCh
      have hv' : v ∈ H (max (cutZ sp.toParams g) (tr.time d')) :=
        hrun.antitone (max_le_max le_rfl hd't) hvz
      have hc := KernelProof.high_toFG_fast_at hrun hnc hsnap hv' hto' (hh.trans hCh)
        (fun D hD => hd't.trans (hq D hD))
      rw [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC v
        (fun _ hk => (hrun.time_mono hk.le).trans hd't),
        Compose.Growing.projAC_state_at hrun (hrun.antitone (le_max_right _ _) hv'),
        Trace.upTo_time]
      exact hc
  have hrt : tr.time r ≤ tr.time d := hrun.time_mono hrd.le
  have he : (tr.upTo (tr.time d)).state v r = tr.state v r :=
    Trace.upTo_state tr v (fun k hk => hrun.time_mono (by omega))
  rw [he] at hOh hE hEO hEh hETh
  have hj' : tr.JoinedAt v (tr.time r) := by
    intro k hk hkr
    exact hj k ((RunTrace.upTo_restartAt tr).mpr ⟨hkr.trans hrt, hk⟩) hkr
  obtain ⟨CV, ell, D, hc, hfl, hO⟩ := hstored
  have hc' : tr.projAC.CallAt v r ell := by
    rw [RunTrace.upTo_projAC] at hc
    exact ((Trace.upTo_callAt tr.projAC).mp hc).2
  have hfl' : AC.FastLockAt tr.projAC v r l D CV := by
    rw [RunTrace.upTo_projAC] at hfl
    have heAC := Trace.upTo_state tr.projAC v
      (fun k (hk : k < r) => hrun.time_mono (show k ≤ d by omega))
    rcases hfl with ⟨ell, C, hupd, hC, hD, hCV⟩ | ⟨ell, A, hop, hA, hsel, hCV⟩
    · obtain ⟨hc, hrest⟩ := hupd
      rw [heAC] at hrest hC hD hCV
      exact Or.inl ⟨ell, C, ⟨((Trace.upTo_callAt tr.projAC).mp hc).2, hrest⟩,
        hC, hD, hCV⟩
    · obtain ⟨hc, hrest⟩ := hop
      rw [heAC] at hrest
      exact Or.inr ⟨ell, A, ⟨((Trace.upTo_callAt tr.projAC).mp hc).2, hrest⟩,
        hA, hsel, hCV⟩
  exact ⟨r, hrd, l, O, ⟨hrun.antitone (max_le_max le_rfl hrt) hvz, hj',
    ⟨CV, ell, D, hc', hfl', hO⟩, hh.trans hOh⟩, E, hE, hEO, hEr, hEh, hETh⟩

end Consensus.Goldilocks.Healing.Growing.Outcome

end
