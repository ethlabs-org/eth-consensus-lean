module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.OperationalReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Head
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Effective-record preservation

Generic guarded-write and frame-change lemmas preserve an exposed prefix in the effective
record. Start with `effective_record_writes_of_compatible` for one call and
`effective_record_of_interval` for a sequence of cuts. Operational selection and report
coverage are supplied separately by `Healing/OperationalReports`, under the same namespace.
-/

namespace Consensus.Goldilocks.Obligations

variable {sp : SA.SAParams} {FGP : Type} {U : Set (SA.Blk sp.n FGP)}

/-- A conflicting candidate above a prefix can only be vetoed by a compatible lock
that covers that prefix. -/
theorem cover_of_veto {U : Set (SA.Blk sp.n FGP)} (_hU : Coherent U)
    {B C L : SA.Blk sp.n FGP} (hBC : Anc U B C) (hLB : Compatible U L B)
    (hLC : ¬ Compatible U C L) : Anc U B L := by
  rcases hLB with hLB | hBL
  · exact False.elim (hLC (Or.inr (hLB.trans hBC)))
  · exact hBL

/-- An exposed prefix survives exactly when both inputs to the new LCA extend it. -/
theorem exposed_prefix_preserved_of_record_head (hU : Coherent U)
    {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {A : SA.SAState sp.n} {t : Time} {O : SA.Blk sp.n FGP} :
    Anc U O (SA.acConfirmed sp A Φ t) ↔
      Anc U O ((SA.lookup Φ A.latestConfirmed).getD Φ.F) ∧
      Anc U O (SA.acHead sp A Φ t) := by
  constructor
  · intro h
    have hC : (SA.lookup Φ A.latestConfirmed).getD Φ.F ∈ Φ.tree := by
      cases he : SA.lookup Φ A.latestConfirmed with
      | none => exact hΦ.rooted.1
      | some C => exact (SA.lookup_eq_some he).1
    have hH : SA.acHead sp A Φ t ∈ Φ.tree :=
      SA.getHead_mem hΦ (T := Φ.viableTree Φ.tree) (fun _ h => h.1) _ _ _ _
    unfold SA.acConfirmed at h
    cases hd : SA.deepest Φ {X | X ∈ Φ.tree ∧
        Φ.Anc X ((SA.lookup Φ A.latestConfirmed).getD Φ.F) ∧
        Φ.Anc X (SA.acHead sp A Φ t)} with
    | none =>
      simp only [hd, Option.getD_none] at h
      exact ⟨h.trans ((hΦ.rooted.2 _ hC).mono hΦU),
        h.trans ((hΦ.rooted.2 _ hH).mono hΦU)⟩
    | some D =>
      simp only [hd, Option.getD_some] at h
      exact ⟨h.trans ((SA.deepest_mem hd).1.2.1.mono hΦU),
        h.trans ((SA.deepest_mem hd).1.2.2.mono hΦU)⟩
  · exact fun h => SA.anc_acConfirmed_of_frame hU hΦ hΦU h.1 h.2

/-- Compatibility with a write candidate preserves a prefix, even when the old record
and the candidate themselves need not be comparable. -/
theorem effective_record_update_of_compatible (hU : Coherent U)
    {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {A : SA.SAState sp.n} {O D : SA.Blk sp.n FGP}
    (hO : Anc U O ((SA.lookup Φ A.latestConfirmed).getD Φ.F))
    (hD : D ∈ Φ.tree) (hcomp : Compatible U O D) :
    Anc U O ((SA.lookup Φ (SA.updateLatestConfirmed sp A Φ D).latestConfirmed).getD Φ.F) := by
  classical
  unfold SA.updateLatestConfirmed
  split_ifs with hguard
  · exact hO
  have hOD : Anc U O D := by
    rcases hcomp with h | h
    · exact h
    cases he : SA.lookup Φ A.latestConfirmed with
    | none =>
      simp only [he, Option.getD_none] at hO
      exact hO.trans ((hΦ.rooted.2 _ hD).mono hΦU)
    | some C =>
      simp only [he, Option.getD_some] at hO
      obtain ⟨hC, hr⟩ := SA.lookup_eq_some he
      exact False.elim (hguard ⟨C, hC, hr,
        SA.anc_tree_of_anc_U hU hΦ hΦU hD (h.trans hO) hC⟩)
  change Anc U O ((SA.lookup Φ D.root).getD Φ.F)
  cases he : SA.lookup Φ D.root with
  | none => exact False.elim (SA.lookup_eq_none he ⟨D, hD, rfl⟩)
  | some C =>
    obtain ⟨hC, hr⟩ := SA.lookup_eq_some he
    have : C = D := hU.1 (hΦU hC) (hΦU hD) hr
    simpa [this] using hOD

/-- A fixed archival record survives a frame change when blocks above the new floor
remain available. The retention premise concerns membership, not viable heads. -/
theorem effective_record_frame_of_compatible (hU : Coherent U)
    {Φ Ψ : SA.Frm sp.n FGP} (hΨ : FrameOK Ψ) (hΦU : Φ.tree ⊆ U) (hΨU : Ψ.tree ⊆ U)
    {r : Nat} {O : SA.Blk sp.n FGP} (hFF : Anc U Φ.F Ψ.F)
    (hFO : Compatible U Ψ.F O)
    (hretain : ∀ C ∈ Φ.tree, Anc U Ψ.F C → C ∈ Ψ.tree)
    (hO : Anc U O ((SA.lookup Φ r).getD Φ.F)) :
    Anc U O ((SA.lookup Ψ r).getD Ψ.F) := by
  have floor : Anc U Ψ.F ((SA.lookup Ψ r).getD Ψ.F) := by
    cases he : SA.lookup Ψ r with
    | none => exact .refl
    | some C => exact (hΨ.rooted.2 _ (SA.lookup_eq_some he).1).mono hΨU
  rcases hFO with hFO | hOF
  swap
  · exact hOF.trans floor
  cases he : SA.lookup Φ r with
  | none =>
    simp only [he, Option.getD_none] at hO
    exact hO.trans (hFF.trans floor)
  | some C =>
    simp only [he, Option.getD_some] at hO
    obtain ⟨hC, hr⟩ := SA.lookup_eq_some he
    have hC' := hretain C hC (hFO.trans hO)
    cases he' : SA.lookup Ψ r with
    | none => exact False.elim (SA.lookup_eq_none he' ⟨C, hC', hr⟩)
    | some D =>
      obtain ⟨hD, hrD⟩ := SA.lookup_eq_some he'
      have : D = C := hU.1 (hΨU hD) (hΦU hC) (hrD.trans hr.symm)
      simpa [this] using hO

/-- The frame adapter instantiated on actual states of one honest node. -/
theorem effective_record_frame_of_run
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i j r : Nat} (hij : i ≤ j)
    {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hFO : Compatible (tr.HonestBlocks H) (tr.state y j).fg.F O)
    (hO : Anc (tr.HonestBlocks H) O
      ((SA.lookup (Node.frame (tr.state y i)) r).getD (tr.state y i).fg.F)) :
    Anc (tr.HonestBlocks H) O
      ((SA.lookup (Node.frame (tr.state y j)) r).getD (tr.state y j).fg.F) := by
  have hU := (Compose.goldilocks_ac_projection_from hrun hnc).localRun.coherent
  have hreach := Compose.fg_reachable hrun.toLocalRun hy j
  have hΨ := (Store.frame_realization _ _ _ _ hreach).1
  apply effective_record_frame_of_compatible hU (Φ := Node.frame (tr.state y i)) hΨ
    (fun X hX => ⟨y, hy, i, hX.1⟩) (fun X hX => ⟨y, hy, j, hX.1⟩)
    (Healing.run_F_mono hrun.toLocalRun hy hij) hFO ?_ hO
  intro C hC hFC
  have hCj := Compose.tree_mono hrun.toLocalRun hy hij hC.1
  obtain ⟨hfin, htc, hgm, hgen⟩ := Store.accepted_tree _ _ _ _ hreach
  have hfull : FrameOK (⟨(tr.state y j).fg.tree, _, _, ∅⟩ :
      Frame sp.n (List (FG.Att sp.n)) (SA.Payload sp.n)) :=
    { finite := hfin, coherent := htc, rooted := ⟨hgm, hgen⟩, fcRoot_mem := hgm
      F_anc_fcRoot := .refl, viableHeads_subset := Set.empty_subset _
      fcRoot_anc_viableHeads := fun _ h => h.elim }
  exact ⟨hCj, SA.anc_tree_of_anc_U hU hfull (fun X hX => ⟨y, hy, j, hX⟩)
    hΨ.rooted.1.1 hFC hCj⟩

/-- Every guarded write in a call preserves a prefix compatible with its candidates. -/
theorem effective_record_writes_of_compatible (hU : Coherent U)
    {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {New : SA.Blk sp.n FGP → Prop} {r r' : Nat} {O : SA.Blk sp.n FGP}
    (hw : Compose.Writes Φ New r r')
    (hnew : ∀ D, New D → Compatible U O D)
    (hO : Anc U O ((SA.lookup Φ r).getD Φ.F)) :
    Anc U O ((SA.lookup Φ r').getD Φ.F) := by
  have hw' := Compose.writes_iff.1 hw
  clear hw
  induction hw' with
  | refl => exact hO
  | @tail r' r'' _ hs ih =>
    obtain ⟨D, hD, hn, hk | ⟨hg, rfl⟩⟩ := hs
    · simpa only [hk.2] using ih
    let A : SA.SAState sp.n := SA.SAState.initial r'
    have h := effective_record_update_of_compatible hU hΦ hΦU (A := A) ih hD (hnew D hn)
    simpa only [SA.updateLatestConfirmed, A, SA.SAState.initial, hg, ↓reduceIte] using h

/-- An update tick runs exactly the preceding slot's update, without a vote attempt. -/
theorem post_of_update
    {ro : SA.ReplayOrder sp FGP} {H : Set (Fin sp.n)} {tr : SA.SATrace sp FGP ro}
    {ini} (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {c s : Nat}
    {ell : ACLabel (SA.goldilocksSA sp FGP ro)} (hu : SA.UpdateAt tr y c s ell) :
    tr.post c = SA.updateConfirmation sp (tr.state y c) ell.frame (tr.time c) s := by
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SA.SAParams.ts]; push_cast; ring
  have hslot : sp.slot (tr.time c) = s + 1 := SA.slot_of_mem sp (s + 1)
    (by rw [hu.2.2.1, hts]; linarith)
    (by rw [hu.2.2.1, show sp.ts (s + 1 + 1 : Nat) =
      sp.ts (s + 1 : Nat) + 4 * sp.Δ by simp only [SA.SAParams.ts]; push_cast; ring, hts]; linarith)
  have he := hr.exec c ell hu.1.2 (hu.1.1 ▸ hy)
  rw [hu.1.1, hu.2.1] at he
  have hpost : tr.post c = (SA.acOnTick sp y (tr.state y c) ell.frame (tr.time c)).1 :=
    (congrArg Prod.fst he).symm
  rw [hpost]
  unfold SA.acOnTick
  dsimp only
  rw [hslot]
  have ht1 : ¬ tr.time c = sp.ts (s + 1 : Nat) + sp.Δ := by
    rw [hu.2.2.1, hts]; linarith
  have ht2 : tr.time c = sp.ts (s + 1 : Nat) + 2 * sp.Δ := by
    rw [hu.2.2.1, hts]; ring
  rw [ite_eq_right (not_not.mpr hu.2.2.2), ite_eq_right ht1,
    ite_eq_left ⟨ht2, Nat.succ_pos s⟩]
  simp only [Nat.add_sub_cancel]

/-- A non-vetoed update covers its result in the effective post-call record. -/
theorem effective_record_after_update
    {ro : SA.ReplayOrder sp FGP} {H : Set (Fin sp.n)} {tr : SA.SATrace sp FGP ro}
    {ini} (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {c s : Nat}
    {ell : ACLabel (SA.goldilocksSA sp FGP ro)} (hu : SA.UpdateAt tr y c s ell)
    {C : SA.Blk sp.n FGP} {CV : Set (SA.Vote sp.n)} (hR : SA.ResultAt tr y c s C CV)
    (hnv : ¬ SA.conflictsWithLock sp (tr.state y c).locks ell.frame (tr.time c) C) :
    ell.frame.Anc C ((SA.lookup ell.frame (tr.post c).latestConfirmed).getD ell.frame.F) := by
  obtain ⟨hΦ, -⟩ := SA.frameIn_of_callAt hr hy hu.1
  obtain ⟨ell', hu', hC, -⟩ := hR
  have heq : ell' = ell := Option.some.inj (hu'.1.2.symm.trans hu.1.2)
  subst ell'
  rw [post_of_update hr hy hu]
  unfold SA.updateConfirmation
  simp only [hC]
  rw [ite_eq_right hnv]
  exact (effective_record_update_slot_growth (sp := sp) hΦ (SA.deepest_mem hC).1.1).1

/-- Fixed-call-frame ancestry after an AC call is ancestry in the actual next
state: AC execution changes neither FG nor its frame. -/
theorem effective_record_after_ac_call
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {j : Nat} {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y j ell)
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Anc (tr.HonestBlocks H) P
      ((SA.lookup ell.frame (tr.projAC.post j).latestConfirmed).getD ell.frame.F)) :
    Anc (tr.HonestBlocks H) P
      ((SA.lookup (Node.frame (tr.state y (j + 1)))
        (tr.state y (j + 1)).ac.latestConfirmed).getD (tr.state y (j + 1)).fg.F) := by
  have hc' := Compose.projAC_callAt.mp hc
  have hlaw := hrun.toLocalRun.cutLaw y hy j _ hc'
  have hframe : Node.frame (tr.state y (j + 1)) = ell.frame := by
    rw [tr.state_succ_of_call hc', hlaw.1]
    exact congrArg Store.toFrame hlaw.2.2.1
  have hstate := Compose.projAC_state hrun.toLocalRun hy (j + 1)
  rw [tr.projAC.state_succ_of_call hc] at hstate
  change Anc (tr.HonestBlocks H) P
    ((SA.lookup (Node.frame (tr.state y (j + 1)))
      (tr.state y (j + 1)).ac.latestConfirmed).getD (Node.frame (tr.state y (j + 1))).F)
  rw [hframe, ← hstate]
  exact hP

/-- A head certificate is checked at the actual read clock. Floor coverage also
allows the prefix to lie outside the current frame. -/
theorem anc_acHead_of_current_certificate
    {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {A : SA.SAState sp.n} {O : SA.Blk sp.n FGP} {t : Time}
    (hhead : Anc U O Φ.F ∨ (O ∈ Φ.tree ∧
      Compatible Φ.tree (SA.getAnchor sp A Φ t) O ∧
      (Φ.Anc O (SA.getAnchor sp A Φ t) ∨ (O ∈ Φ.viableTree Φ.tree ∧
        (SA.voters (SA.latestView sp A Φ t).1.votes).ncard <
          2 * (SA.supporters Φ (SA.latestView sp A Φ t).1
            (SA.latestView sp A Φ t).2 O).ncard)))) :
    Anc U O (SA.acHead sp A Φ t) := by
  rcases hhead with hF | ⟨hO, hcomp, hsup⟩
  · have hH : SA.acHead sp A Φ t ∈ Φ.tree :=
      SA.getHead_mem hΦ (T := Φ.viableTree Φ.tree) (fun _ h => h.1) _ _ _ _
    exact hF.trans ((hΦ.rooted.2 _ hH).mono hΦU)
  · exact (SA.anc_acHead hΦ hO hcomp hsup).mono hΦU

variable {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a : Time}

/-- Explicit interval producer contract for one earlier output. Each transition either
decomposes into guarded writes in the old frame followed by a compatible floor change,
or supplies a replacement effective record extending the prefix (including restarts).
The write predicate must include every actual write. No such provenance,
restart preservation, or floor compatibility is inferred from a lock at one read. -/
structure EffectiveRecordInterval (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (y : Fin sp.n) (i j : Nat) (O : SA.Blk sp.n (List (FG.Att sp.n))) : Prop where
  step : ∀ q, i ≤ q → q < j →
    (∃ New : SA.Blk sp.n (List (FG.Att sp.n)) → Prop,
      Compose.Writes (Node.frame (tr.state y q)) New
        (tr.state y q).ac.latestConfirmed (tr.state y (q + 1)).ac.latestConfirmed ∧
      (∀ D, New D → Compatible (tr.HonestBlocks H) O D) ∧
      Compatible (tr.HonestBlocks H) (tr.state y (q + 1)).fg.F O) ∨
    Anc (tr.HonestBlocks H) O
      ((SA.lookup (Node.frame (tr.state y (q + 1)))
        (tr.state y (q + 1)).ac.latestConfirmed).getD (tr.state y (q + 1)).fg.F)

/-- Finite actual-source comparison supplies the interval without manufacturing later
votes. Candidate and floor comparisons remain local producer obligations. -/
theorem effectiveRecordInterval_of_candidates_before {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {i j : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hy : y ∈ H)
    (hcandidates : ∀ q, i ≤ q → q < j → ∀ D s CV,
      SA.ResultAt tr.projAC y q s D CV ∨ SA.OptimisticLockAt tr.projAC y q s D CV →
      Compatible (tr.HonestBlocks H) O D)
    (hframes : ∀ q, i ≤ q → q < j →
      Compatible (tr.HonestBlocks H) (tr.state y (q + 1)).fg.F O) :
    EffectiveRecordInterval tr H y i j O := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hst := Compose.projAC_state hp.run.toLocalRun hy
  refine ⟨fun q hiq hqj => Or.inl ?_⟩
  refine ⟨(fun D => ∃ s CV, SA.ResultAt tr.projAC y q s D CV ∨
    SA.OptimisticLockAt tr.projAC y q s D CV), ?_, ?_, hframes q hiq hqj⟩
  · by_cases hcall : ∃ ell, tr.projAC.CallAt y q ell
    · obtain ⟨ell, hcall⟩ := hcall
      have hw := Compose.call_writes hac.localRun hy hcall
      rw [← tr.projAC.state_succ_of_call hcall, hst, hst,
        Compose.frame_of_projAC hp.run hy hcall] at hw
      exact hw
    · have he : (tr.state y (q + 1)).ac.latestConfirmed = (tr.state y q).ac.latestConfirmed := by
        rw [← hst, tr.projAC.state_succ_of_not (fun ell h => hcall ⟨ell, h⟩), hst]
      rw [he]
      exact Compose.writes_iff.mpr .refl
  · rintro D ⟨s, CV, hD⟩
    exact hcandidates q hiq hqj D s CV hD

/-- The interval contract preserves the effective record across every intervening cut. -/
theorem effective_record_of_interval
    {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i j : Nat} (hij : i ≤ j)
    {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hint : EffectiveRecordInterval tr H y i j O)
    (hO : Anc (tr.HonestBlocks H) O ((SA.lookup (Node.frame (tr.state y i))
      (tr.state y i).ac.latestConfirmed).getD (tr.state y i).fg.F)) :
    Anc (tr.HonestBlocks H) O ((SA.lookup (Node.frame (tr.state y j))
      (tr.state y j).ac.latestConfirmed).getD (tr.state y j).fg.F) := by
  have hU := (Compose.goldilocks_ac_projection_from hrun hnc).localRun.coherent
  have step : ∀ q, i ≤ q → q ≤ j → Anc (tr.HonestBlocks H) O
      ((SA.lookup (Node.frame (tr.state y q)) (tr.state y q).ac.latestConfirmed).getD
        (tr.state y q).fg.F) := by
    intro q hiq
    induction q, hiq using Nat.le_induction with
    | base => exact fun _ => hO
    | succ q hiq ih =>
      intro hqj
      rcases hint.step q hiq (by omega) with ⟨New, hw, hnew, hF⟩ | hreset
      · have hwritten := effective_record_writes_of_compatible hU
          (Compose.frameOK_state hrun.toLocalRun hy q)
          (fun X hX => ⟨y, hy, q, hX.1⟩) hw hnew (ih (by omega))
        exact effective_record_frame_of_run hrun hnc hy (Nat.le_succ q) hF hwritten
      · exact hreset
  exact step j hij le_rfl

end Consensus.Goldilocks.Obligations
end
