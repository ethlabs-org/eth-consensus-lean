module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Provenance

public section

/-! # Goldilocks Healing, HR.4: the sources of the high rows

**Temporal source provenance** (`hr4-cut-scope.md` §4, `high_row_source`). An honest row signed
at cut `d` names the entry `E` of its source `Q`, the block that the node's `ac_to_fg` returned at
the cut before (`Compose.attest_source`): `Q` is the viable ancestor of a live fast lock's block,
which sits below the stored block `O` of a fast-lock write of the same node at a cut `r < d`
(`stored_fast_lock_provenance`), so `E ⪯ Q ⪯ O`. A high row (`att.h ≥ H_z + 1`) has a high
source, so `O` is high (heights do not decrease along ancestry), the write is joined
(`joined_of_fastLockAt`, `JoinedProjection`), and `(O, l)` is a high origin written by the signer
before the signing. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}
  {proposer : Nat → Fin sp.n}

/-! ## Store facts at the honest nodes -/

/-- Along ancestry in a reachable store the state height does not decrease. -/
theorem h_le_of_store_anc {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) {A W : NodeBlock P ACP} (h : st.Anc A W) :
    (st.σ A.root).h ≤ (st.σ W.root).h := by
  induction h with
  | refl => exact le_rfl
  | tail _ hYW ih =>
    obtain ⟨-, -, -, ht⟩ := Store.step_σ hr hYW.2.1 hYW.2.2
    rcases stateTransition_bits ht with ⟨hh, -⟩ | ⟨hh, -⟩ <;> omega

/-- Ancestry inside the honest blocks below a block of an honest tree is ancestry in that tree
(honest trees are parent-closed down to genesis). -/
theorem store_anc_of_honest_anc (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {A C : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : Anc (tr.HonestBlocks H) A C) (hC : C ∈ (tr.state y k).fg.tree) :
    (tr.state y k).fg.Anc A C := by
  have hr := Compose.fg_reachable hrun.toLocalRun hy k
  have hU := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  induction h with
  | refl => exact .refl
  | tail _ hYC ih =>
    rcases ((Store.accepted_tree _ _ _ _ hr).2.2.2 _ hC).cases_tail with hg | ⟨Z, -, hZ⟩
    · exact absurd hYC.2.2 (by rw [hg]; simp [Params.genesisBlock])
    obtain rfl : Z = _ := hU.1 ⟨y, hy, k, hZ.1⟩ hYC.1
      (Option.some.inj (hZ.2.2.symm.trans hYC.2.2))
    exact (ih hZ.1).tail hZ

/-- Ancestry in an honest tree is ancestry inside the honest blocks (the tree is a subset of
them; the converse of `store_anc_of_honest_anc`). -/
theorem honest_anc_of_store_anc {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {A C : SA.Blk sp.n (List (FG.Att sp.n))} (h : (tr.state y k).fg.Anc A C) :
    Anc (tr.HonestBlocks H) A C :=
  Anc.mono (fun _ hZ => ⟨y, hy, k, hZ⟩) h

/-- A block below (inside the honest blocks) a block of an honest tree is in that tree. -/
theorem mem_of_honest_anc (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {A C : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : Anc (tr.HonestBlocks H) A C) (hC : C ∈ (tr.state y k).fg.tree) :
    A ∈ (tr.state y k).fg.tree := by
  by_cases he : A = C
  · exact he ▸ hC
  · exact (Anc.mem (store_anc_of_honest_anc hrun hnc hy h hC) he).1

/-- One state per block across the honest stores of a run. -/
theorem σ_eq_honest (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBy : B ∈ (tr.state y i).fg.tree) (hBz : B ∈ (tr.state z j).fg.tree) :
    (tr.state y i).fg.σ B.root = (tr.state z j).fg.σ B.root :=
  Store.σ_eq_of_mem (Compose.fg_reachable hrun.toLocalRun hy i)
    (Compose.fg_reachable hrun.toLocalRun hz j)
    (Compose.honest_blocks_coherent hrun.toLocalRun hnc).1 (fun _ hX => ⟨y, hy, i, hX⟩)
    (fun _ hX => ⟨z, hz, j, hX⟩) hBy hBz

/-- The block of a frame of an honest call is in the node's FG tree. -/
theorem mem_tree_of_frame (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y k ℓ)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree) :
    B ∈ (tr.state y k).fg.tree := by
  rw [Compose.frame_of_projAC hrun hy hc] at hB
  exact hB.1

/-- The selection of a fast-lock write is in the frame of its call. -/
private theorem fastLockAt_frame_mem {x : Fin sp.n} {i s : Nat}
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (h : SA.FastLockAt tr.projAC x i s D CV) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt x i ℓ) : D ∈ ℓ.frame.tree := by
  sorry

/-- The stored block of a fast-lock write is in the writer's FG tree, below its selection. -/
theorem storedFastLock_mem (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {x : Fin sp.n} (hx : x ∈ H) {i s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (h : Compose.StoredFastLockAt tr x i s B CV) :
    B ∈ (tr.state x i).fg.tree ∧ ∃ D, SA.FastLockAt tr.projAC x i s D CV ∧
      Anc (tr.HonestBlocks H) B D := by
  unfold Compose.StoredFastLockAt at h
  obtain ⟨ℓ, D, hc, hfl, rfl⟩ := h
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hx hc
  obtain ⟨hvt, hva⟩ := SA.viableAncestor_anc hΦ (fastLockAt_frame_mem hfl hc)
  exact ⟨mem_tree_of_frame hrun hx hc hvt, D, hfl, hva.mono hΦU⟩

/-- **A fast-lock write is joined** (run level): `JoinedAt` at the write's time. -/
theorem joinedAt_of_fastLockAt (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {x : Fin sp.n} (hx : x ∈ H) {i s : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (h : SA.FastLockAt tr.projAC x i s D CV) :
    tr.JoinedAt x (tr.time i) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨hj, ℓ, hc, hnr⟩ := joined_of_fastLockAt hr hx h
  have hnr' : ¬ tr.RestartAt x i := by
    rintro ⟨ℓk, hck, hkr⟩
    obtain rfl : ℓk = ℓ := Option.some.inj ((Compose.projAC_callAt.mpr hck).2.symm.trans hc.2)
    exact hnr hkr
  refine ((Compose.joined_projection sp ro dg H tr proposer hrun x hx (tr.time i)).2.1 i
    ⟨_, Compose.projAC_callAt.mp hc⟩ hnr' rfl).mpr ?_
  rw [← Compose.projAC_state hrun.toLocalRun hx]
  exact hj

/-! ## The source of an honest row -/

/-- A block that `ac_to_fg` returns is a candidate. -/
private theorem mem_toFGCandidates' {FGP : Type} {A : SA.SAState sp.n} {Φ : SA.Frm sp.n FGP}
    {t : Time} {C : SA.Blk sp.n FGP} (h : (SA.acToFG sp A Φ t).2 = some C) :
    C ∈ SA.toFGCandidates sp A Φ t := by
  unfold SA.acToFG at h
  split_ifs at h
  split at h
  · cases h
  · rename_i C' hC'
    split_ifs at h
    cases h
    exact (SA.deepest_mem hC').1

/-- **Temporal source provenance of a high row** (`hr4-cut-scope.md` §4). An honest row of height
`≥ H_z + 1` signed at cut `d` names the entry `E` (at its height) of the chain of a high origin
`(O, l)` written by the signer at a cut `r < d`: `E ⪯ Q ⪯ O` for the row's source `Q`. -/
theorem ResetPremisesUpTo.high_row_source {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {v : Fin sp.n} (hv : v ∈ H)
    {d : Nat} {att : FG.Att sp.n} (hs : tr.SignAt v d att) (hh : HZ tr H g + 1 ≤ att.h) :
    ∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧ ∃ E ∈ (tr.state v r).fg.tree,
      (tr.state v r).fg.Anc E O ∧ E.root = att.T ∧ ((tr.state v r).fg.σ E.root).h = att.h ∧
      ((tr.state v r).fg.σ E.root).Th = E.root := by
  have hacr := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hacr.localRun
  have hU := hr.coherent
  obtain ⟨C, hcall⟩ := hs
  obtain ⟨d', rfl, ℓ, hc', hto, -, hC, hfgeq⟩ :=
    Compose.attest_source hp.run.toLocalRun hv hcall
  have hpc : tr.projAC.CallAt v d' ℓ := Compose.projAC_callAt.mpr hc'
  have hC' : (SA.acToFG sp (tr.projAC.state v d') ℓ.frame (tr.time d')).2 = some C := by
    rw [Compose.projAC_state hp.run.toLocalRun hv]
    exact hC
  obtain ⟨hCv, l, hl, hlb, hlf, -⟩ := mem_toFGCandidates' hC'
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := hl
  obtain ⟨r, hrd, CV, ℓw, D, hcw, hfl, L, hL, hLr, hLO⟩ :=
    stored_fast_lock_provenance hr hv d' l₀ hl₀ hlf
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hv hpc
  obtain ⟨hΦw, -⟩ := SA.frameIn_of_callAt hr hv hcw
  -- the source is the viable ancestor of the live lock's block, below the stored block
  have hCt : C ∈ ℓ.frame.tree := hCv.1
  obtain ⟨hvat, hva⟩ := SA.viableAncestor_anc hΦ hB₀
  obtain rfl : C = ℓ.frame.viableAncestor B₀ := hU.1 (hΦU hCt) (hΦU hvat) hlb.symm
  obtain rfl : L = B₀ := hU.1 hL (hΦU hB₀) (hLr.trans hB₀r.symm)
  set O := ℓw.frame.viableAncestor D with hO
  have hCO : Anc (tr.HonestBlocks H) (ℓ.frame.viableAncestor L) O := (hva.mono hΦU).trans hLO
  have hOt : O ∈ (tr.state v r).fg.tree :=
    mem_tree_of_frame hp.run hv hcw (SA.viableAncestor_anc hΦw (fastLockAt_frame_mem hfl hcw)).1
  -- the entry of the source, in the store at the signing
  set st := (tr.state v (d' + 1)).fg with hst
  have hreach := Compose.fg_reachable hp.run.toLocalRun hv (d' + 1)
  have hCst : ℓ.frame.viableAncestor L ∈ st.tree := by
    rw [hfgeq]
    exact mem_tree_of_frame hp.run hv hpc hCt
  have hcut := (hp.run.cutLaw v hv (d' + 1) _ hcall).1
  obtain ⟨hah, haT⟩ := Store.createAtt_eq hcut
  obtain ⟨⟨E, hE, hEr, hEC, hEh, hETh⟩, -⟩ :=
    Store.entry_state_of_source sp.toParams (Payload sp.n) _ st hreach _ hCst
  have hEh' : (st.σ E.root).h = att.h := by rw [hah, hEr]
  have hETh' : (st.σ E.root).Th = E.root := by rw [hETh, hEr]
  have hEr' : E.root = att.T := by
    rw [haT]
    change E.root = (st.σ (st.σ _).Th).Th
    rw [← hEr, hETh']
  -- the stored block is high
  have hOst : O ∈ st.tree := Compose.tree_mono hp.run.toLocalRun hv (by omega) hOt
  have hCOst := store_anc_of_honest_anc hp.run hp.noColl hv hCO hOst
  have hσO := σ_eq_honest hp.run hp.noColl hv hv hOst hOt
  have hOh : HZ tr H g + 1 ≤ ((tr.state v r).fg.σ O.root).h := by
    rw [← hσO]
    have := h_le_of_store_anc hreach hCOst
    rw [← hEh] at this
    omega
  -- the entry in the writer's store
  have hsub : st.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨v, hv, d' + 1, hX⟩
  have hEO : Anc (tr.HonestBlocks H) E O := (hEC.mono hsub).trans hCO
  have hEt := mem_of_honest_anc hp.run hp.noColl hv hEO hOt
  have hσE := σ_eq_honest hp.run hp.noColl hv hv hEt hE
  have hoO : HighOrigin tr H g v r l₀.slot O := by
    unfold HighOrigin Compose.StoredFastLockAt
    exact ⟨hv, joinedAt_of_fastLockAt hp.run hp.noColl hv hfl, ⟨CV, ℓw, D, hcw, hfl, rfl⟩, hOh⟩
  refine ⟨r, by omega, l₀.slot, O, hoO, E, hEt, store_anc_of_honest_anc hp.run hp.noColl hv hEO hOt,
    hEr', by rw [hσE, hEh'], by rw [hσE, hETh']⟩

/-- Whole-run specialization of actual signed-row provenance. -/
theorem high_row_source (hp : ResetPremises tr H proposer dg g ΔF a) {v : Fin sp.n} (hv : v ∈ H)
    {d : Nat} {att : FG.Att sp.n} (hs : tr.SignAt v d att) (hh : HZ tr H g + 1 ≤ att.h) :
    ∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧ ∃ E ∈ (tr.state v r).fg.tree,
      (tr.state v r).fg.Anc E O ∧ E.root = att.T ∧ ((tr.state v r).fg.σ E.root).h = att.h ∧
      ((tr.state v r).fg.σ E.root).Th = E.root :=
  (hp.toUpTo tr H (le_refl a)).high_row_source hv hs hh

end Consensus.Goldilocks.Healing

end
