module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Service
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Head
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Strict
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FastExpiry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Update

-- Whole-run consumers and their finite-horizon counterparts share this endpoint layer.
public section
namespace Consensus.Goldilocks.Refinement

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
      SA.getHead_mem' hΦ (T := Φ.viableTree Φ.tree) (fun _ h => h.1) _ _ _ _
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
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i j r : Nat} (hij : i ≤ j)
    {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hFO : Compatible (tr.HonestBlocks H) (tr.state y j).fg.F O)
    (hO : Anc (tr.HonestBlocks H) O
      ((SA.lookup (Node.frame (tr.state y i)) r).getD (tr.state y i).fg.F)) :
    Anc (tr.HonestBlocks H) O
      ((SA.lookup (Node.frame (tr.state y j)) r).getD (tr.state y j).fg.F) := by
  have hU := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun.coherent
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

/-- Writing a held candidate leaves that candidate or a strictly later descendant.
The guard can retain a record only above the candidate, never an older fork. -/
theorem effective_record_update_slot_growth
    {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) {A : SA.SAState sp.n}
    {P : SA.Blk sp.n FGP} (hP : P ∈ Φ.tree) :
    let C := (SA.lookup Φ (SA.updateLatestConfirmed sp A Φ P).latestConfirmed).getD Φ.F
    Φ.Anc P C ∧ (C = P ∨ P.slot < C.slot) := by
  classical
  dsimp only
  have lookup_self : ∀ D ∈ Φ.tree, SA.lookup Φ D.root = some D := by
    intro D hD
    cases he : SA.lookup Φ D.root with
    | none => exact False.elim (SA.lookup_eq_none he ⟨D, hD, rfl⟩)
    | some C =>
      obtain ⟨hC, hr⟩ := SA.lookup_eq_some he
      exact congrArg some (hΦ.coherent.1 hC hD hr)
  have hanc : Φ.Anc P
      ((SA.lookup Φ (SA.updateLatestConfirmed sp A Φ P).latestConfirmed).getD Φ.F) := by
    unfold SA.updateLatestConfirmed
    split_ifs with hg
    · obtain ⟨C, hC, hr, hPC⟩ := hg
      rw [← hr, lookup_self C hC]
      exact hPC
    · change Φ.Anc P ((SA.lookup Φ P.root).getD Φ.F)
      rw [lookup_self P hP]
      exact .refl
  refine ⟨hanc, ?_⟩
  by_cases he : (SA.lookup Φ (SA.updateLatestConfirmed sp A Φ P).latestConfirmed).getD Φ.F = P
  · exact Or.inl he
  · exact Or.inr ((hanc.slot_le hΦ.coherent).2 (Ne.symm he))

/-- An update tick runs exactly the preceding slot's update, without a vote attempt. -/
theorem post_of_update
    {ro : SA.ReplayOrder sp FGP} {H : Set (Fin sp.n)} {tr : SA.SATrace sp FGP ro}
    (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr)
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
    (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr)
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
      SA.getHead_mem' hΦ (T := Φ.viableTree Φ.tree) (fun _ h => h.1) _ _ _ _
    exact hF.trans ((hΦ.rooted.2 _ hH).mono hΦU)
  · exact (SA.anc_acHead hΦ hO hcomp hsup).mono hΦU

section CoveredPrefix

variable {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a : Time}

end CoveredPrefix

section CoveredEndpoint

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
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i j : Nat} (hij : i ≤ j)
    {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hint : EffectiveRecordInterval tr H y i j O)
    (hO : Anc (tr.HonestBlocks H) O ((SA.lookup (Node.frame (tr.state y i))
      (tr.state y i).ac.latestConfirmed).getD (tr.state y i).fg.F)) :
    Anc (tr.HonestBlocks H) O ((SA.lookup (Node.frame (tr.state y j))
      (tr.state y j).ac.latestConfirmed).getD (tr.state y j).fg.F) := by
  have hU := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun.coherent
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

namespace UpTo

/-- Reset and drain timing put every bounded honest restart before the preceding
slot's join threshold; no last-wake bound at GST is assumed. -/
theorem restart_before_unanimous_slot {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {u : Nat} (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    {y : Fin sp.n} (hy : y ∈ H) {r : Nat} (hr : tr.RestartAt y r)
    (hrb : tr.time r ≤ b) : tr.time r ≤ sp.ts ((u : Int) - 1) := by
  have hca := Healing.cutZ_lt_reset_of_snapshot hp.run
    (by obtain ⟨k, hk, -⟩ := hp.snapshot; exact ⟨k, hk⟩) hp.reset
  have ha0 : 0 ≤ a := by
    have := Healing.lt_cutZ sp g
    have := SA.gbar_nonneg g
    linarith [sp.toParams.hΔ]
  rw [Healing.cutZ_eq] at hca
  have hqa := (SA.ts_le_iff_le_slot sp ha0 _).1 hca.le
  rw [Healing.drainTime_eq] at hR
  have hAu := (SA.ts_le_iff sp).1 hR
  apply (Healing.restart_le_before hp hy hr hrb).trans
  apply (SA.ts_le_iff sp).2
  push_cast at hqa hAu ⊢
  omega

/-- Finite reset service supplies actual votes from every honest validator by the
slot deadline. These witnesses also seed the old-origin ancestry argument. -/
theorem honest_votes_in_slot {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b) :
    ∀ y ∈ H, ∃ j e, SA.VoteAt tr.projAC y j e ∧ e.msg.slot = u ∧
      tr.time j ≤ sp.ts u + sp.Δ := by
  apply SA.honest_votes_in_slot_before (Healing.healthy_base_of_reset_catch_before hp hc)
    hgu hub
  intro y hy r hr hrs
  exact restart_before_unanimous_slot hp hR hy
    (Compose.projAC_restartAt.mp hrs) (hr.trans hub)

/-- An actual unanimous vote bounds every pre-slot high origin, by finite retention.
The origin need not precede the vote in cut order. -/
theorem old_origin_below_unanimous {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b)
    {x : Fin sp.n} {r m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : Healing.HighOrigin tr H g x r m B) (ht : tr.time r < sp.ts u) :
    Anc (tr.HonestBlocks H) B P := by
  have hmu : m < u := by
    obtain ⟨_, _, _, _, hfl, _⟩ := hp.highOrigin_mem ho
    rcases hfl with ⟨ell, C, hu, _⟩ | ⟨ell, A, _, hs, _⟩
    · have htime : tr.time r = sp.ts m + 6 * sp.Δ := hu.2.2.1
      have hts : sp.ts m < sp.ts u := by linarith [sp.toParams.hΔ]
      have := (SA.ts_lt_iff sp).1 hts
      omega
    · have hs' : sp.slot (tr.time r) = m := hs
      have hlt := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg r) (u : Int)).not.mp
        (not_le.mpr ht)
      omega
  obtain ⟨q, e, hv, hs, hq⟩ := honest_votes_in_slot hp hc hgu hR hub x ho.1
  obtain ⟨ell, hcast⟩ := hv
  have hrb : tr.time r ≤ b := by linarith [sp.toParams.hΔ]
  obtain ⟨Hd, hHd, he, hBH⟩ :=
    hp.high_origin_votes_before q (hq.trans hub) x r m B ho hrb x ho.1 ell e hcast (by omega)
  have heq : Hd = P := hp.honest_coherent.1 hHd hP
    (he.trans (hun x ho.1 q e ⟨ell, hcast⟩ (hq.trans hub) hs))
  exact heq ▸ hBH

/-- Finite writer service carries the previous honest vote batch to a bounded
next-slot cast. Only actual previous votes, bounded by this cast, are consulted. -/
theorem unanimous_carry_votes {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcast : SA.CastAt tr.projAC y i ell e)
    (hs : e.msg.slot = u + 1) (hib : tr.time i ≤ b)
    (hFP : Anc (tr.HonestBlocks H) ell.frame.F P) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e u (Compose.honestVotes tr H u) := by
  have hS := Healing.healthy_base_of_reset_catch_before hp hc
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  apply SA.carryAt_of_each (hr.awake_of_call y hy i ell hcast.1)
    (SA.castAt_spec hr hy hcast).2.2.1
  rintro v ⟨z, hz, q, e', ⟨ell', hc'⟩, rfl, hsl⟩
  have hqi : q < i := by
    by_contra hn
    have := SA.slot_mono sp (hr.time_nonneg i) (hr.time_mono (Nat.le_of_not_gt hn))
    have := (SA.castAt_spec hr hz hc').2.1
    have := (SA.castAt_spec hr hy hcast).2.1
    omega
  obtain ⟨⟨Hd, hHd, hHdr, _⟩, hqt⟩ := Compose.cast_head_fcRoot hr hz hc'
  have hHdP : Hd = P := hr.coherent.1 ((SA.frameIn_of_callAt hr hz hc'.1).2 hHd) hP
    (hHdr.trans (hun z hz q e' ⟨ell', hc'⟩ ((hp.run.time_mono hqi.le).trans hib) hsl))
  subst Hd
  apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hS.sync)
    (by linarith : SA.gbar g ≤ sp.ts u) hS.catchUp (by linarith) hz hy hcast hs hib
  rintro v rfl
  have ht : tr.projAC.time q < sp.ts u + 2 * sp.Δ := by rw [hsl] at hqt; linarith
  refine ⟨hsl, ⟨q, ⟨ell', hc'.1, Or.inl ⟨e', hc'.2, rfl⟩⟩,
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg q) u).mpr
      (by rw [← (SA.castAt_spec hr hz hc').2.1, hsl]), ht⟩, P, hP, hHdr, hFP, ?_⟩
  rcases Compose.frame_anc_accepted hr hz q ell' hc'.1 P hHd P .refl with hg | ⟨k, hk, ha⟩
  · exact Or.inl hg
  · exact Or.inr ⟨k, ha, (hr.time_mono hk).trans_lt ht⟩

/-- Finite unanimity bounds all origins written before the following slot, including
same-label optimistic writes. The old-origin bound is derived, not supplied. -/
theorem high_origins_before_next_slot_below {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b)
    {x : Fin sp.n} {r m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : Healing.HighOrigin tr H g x r m B)
    (ht : tr.time r < sp.ts (u + 1 : Nat)) (hrb : tr.time r ≤ b) :
    Anc (tr.HonestBlocks H) B P := by
  have hr := (Healing.healthy_base_of_reset_catch_before hp hc).run.localRun
  obtain ⟨ell, D, CV, hcall, hfl, _, _, _, hBD, _⟩ := hp.highOrigin_mem ho
  have hmu : m ≤ u := by
    rcases hfl with ⟨ell, C, hu, _⟩ | ⟨ell, A, _, hs, _⟩
    · have htime : tr.time r = sp.ts m + 6 * sp.Δ := hu.2.2.1
      have hts : sp.ts m < sp.ts (u + 1 : Nat) := by linarith [sp.toParams.hΔ]
      have := (SA.ts_lt_iff sp).1 hts
      omega
    · have hs' : sp.slot (tr.time r) = m := hs
      have := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg r) ((u + 1 : Nat) : Int)).not.mp
        (not_le.mpr ht)
      omega
  rcases lt_or_eq_of_le hmu with hmu | rfl
  · obtain ⟨q, e, ⟨ellv, hv⟩, hs, hq⟩ := honest_votes_in_slot hp hc hgu hR hub x ho.1
    obtain ⟨Hd, hHd, he, hBH⟩ := hp.high_origin_votes_before q (hq.trans hub)
      x r m B ho hrb x ho.1 ellv e hv (by omega)
    have heq : Hd = P := hr.coherent.1 hHd hP
      (he.trans (hun x ho.1 q e ⟨ellv, hv⟩ (hq.trans hub) hs))
    exact heq ▸ hBH
  · exact (hBD.mono (SA.frameIn_of_callAt hr ho.1 hcall).2).trans
      (hp.same_slot_source_below_unanimous hc ho.1 (Or.inl ⟨CV, hfl⟩) hrb
        (hp.cutZ_le_ts_of_highOrigin ho) hP hun)

/-- Actual bounded unanimity admits P into every next-slot frozen viable tree. -/
theorem unanimous_next_vote_viable {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcast : SA.CastAt tr.projAC y j ell e)
    (hs : e.msg.slot = u + 1) (hjb : tr.time j ≤ b) :
    Anc (tr.HonestBlocks H) ell.frame.F P ∧
      P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (u + 1)) := by
  have hS := Healing.healthy_base_of_reset_catch_before hp hc
  have hbound := fun x r m B ho ht hrb =>
    high_origins_before_next_slot_below hp hc hP hun hgu hR hub
      (x := x) (r := r) (m := m) (B := B) ho ht hrb
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hS.run.localRun hy hcast.1
  have hroot := hp.reset_vote_root_below_bound hR hP hbound hy hcast hs hjb
  have hFP := (hPhi.F_anc_fcRoot.mono hPhiU).trans hroot
  obtain ⟨q, v, ⟨ellv, hv⟩, hvs, hq⟩ := honest_votes_in_slot hp hc hgu hR hub y hy
  obtain ⟨⟨Hd, hHd, he, _⟩, _⟩ := Compose.cast_head_fcRoot hS.run.localRun hy hv
  have heq : Hd = P := hS.run.localRun.coherent.1
    ((SA.frameIn_of_callAt hS.run.localRun hy hv.1).2 hHd) hP
    (he.trans (hun y hy q v ⟨ellv, hv⟩ (hq.trans hub) hvs))
  subst Hd
  have hacc : SA.AcceptedBefore tr.projAC y P (sp.ts u + 3 * sp.Δ) := by
    rcases SA.frame_genesis_or_accepted sp hS.run.localRun hy hv.1 P hHd with hz | ⟨k, hk, ha⟩
    · omega
    · refine Or.inr ⟨k, ha, ?_⟩
      have := hp.run.time_mono hk
      change tr.time k < _
      linarith [sp.toParams.hΔ]
  have hPt := Compose.accepted_voter_tree hp.run hp.noColl hy hcast hs hP hacc hFP
  have hstore : P ∈ (tr.state y j).fg.tree := by
    have hm := hPt.1
    rw [Compose.frame_of_projAC hp.run hy hcast.1] at hm
    exact hm.1
  have hfloor := hp.reset_vote_floor_above_old hy hR hcast hs hjb hstore hbound
  have hroot' := SA.anc_tree_of_anc_U hS.run.localRun.coherent hPhi hPhiU
    hPhi.fcRoot_mem hroot hPt.1
  refine ⟨hFP, hPt, hroot', P, hPt, ?_, .refl⟩
  have hm := hPt.1
  rw [Compose.frame_of_projAC hp.run hy hcast.1] at hm hroot' ⊢
  exact ⟨hm.1, hm.2, hroot'.mono (fun X hX => hX.1), hfloor⟩

/-- Bounded actual unanimity propagates through every next-slot cast by finite
retention and writer service, without a supplied old-origin or viability duty. -/
theorem unanimous_next_votes_extend {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b) :
    ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b → e.msg.slot = u + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg P := by
  have hS := Healing.healthy_base_of_reset_catch_before hp hc
  have hr := hS.run.localRun
  have hhalf : sp.n ≤ 2 * {y | y ∈ H ∧ ∃ j e, SA.VoteAt tr.projAC y j e ∧
      e.msg.slot = u}.ncard := by
    have h := SA.honest_voters_half_before hS hgu hub (by
      intro y hy r ht hrs
      exact restart_before_unanimous_slot hp hR hy (Compose.projAC_restartAt.mp hrs)
        (ht.trans hub))
    have hm := Set.ncard_le_ncard (s := {y | y ∈ H ∧ ∃ j e, SA.VoteAt tr.projAC y j e ∧
      e.msg.slot = u ∧ tr.time j ≤ sp.ts u + sp.Δ})
      (t := {y | y ∈ H ∧ ∃ j e, SA.VoteAt tr.projAC y j e ∧ e.msg.slot = u})
      (by rintro y ⟨hy, j, e, hv, hs, _⟩; exact ⟨hy, j, e, hv, hs⟩)
    exact h.trans (Nat.mul_le_mul_left 2 hm)
  have all : ∀ j, tr.time j ≤ b → ∀ y ∈ H, ∀ e,
      SA.VoteAt tr.projAC y j e → e.msg.slot = u + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg P := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      rintro hjb y hy e ⟨ell, hcast⟩ hs
      obtain ⟨hFP, hvi⟩ := unanimous_next_vote_viable hp hc hP hslot hu hun hgu hR hub
        hy hcast hs hjb
      have htime : sp.ts (u + 1 : Nat) ≤ tr.time j :=
        (SA.ts_le_iff_le_slot sp (hr.time_nonneg j) _).2
          (by rw [← (SA.castAt_spec hr hy hcast).2.1, hs])
      obtain ⟨v, r, l, O, ho, _, hl, _⟩ := hp.reset_seed_before_slot hR
      have hcut : Healing.cutZ sp.toParams g ≤ tr.time j :=
        (hp.cutZ_le_ts_of_highOrigin ho).trans
          (((SA.ts_le_iff sp).2 (by omega)).trans htime)
      have hfault : SA.FaultBound tr.projAC H (tr.time j) := by
        have h := Healing.fault_bound_late_before hp hcut hjb
        unfold RunTrace.FaultBound RunTrace.honestAwakeJoined at h
        unfold SA.FaultBound SA.honestAwakeJoined
        convert h using 1
        congr 1
        ext z
        exact and_congr_right fun hz => and_congr_right fun _ =>
          (Compose.joined_projection sp ro dg H tr proposer hp.run z hz (tr.time j)).1.symm
      apply SA.next_vote_extends_before hS.run hy hcast hs ?_ hhalf
        (unanimous_carry_votes hp hc hP hun hgu hy hcast hs hjb hFP) hfault
        (hp.sync.syncAC hp.run (by have := SA.le_gbar g; linarith [sp.toParams.hΔ]))
        (Or.inl hvi)
      intro z hz q hq e' hv hsl
      have hqb := (hp.run.time_mono hq.le).trans hjb
      rcases hsl with hsl | hsl
      · exact ⟨P, hP, (hun z hz q e' hv hqb hsl).symm, .refl⟩
      · exact ih q hq hqb z hz e' hv hsl
  exact fun y hy j e hv hjb hs => all j hjb y hy e hv hs

/-- A bounded next-slot optimistic source compares with P through an actual honest
supporter, whose cast is no later than the source. -/
theorem unanimous_next_optimistic_compatible {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (hopt : SA.OptimisticLockAt tr.projAC y j (u + 1) D CV)
    (hjb : tr.time j ≤ b) : Compatible (tr.HonestBlocks H) D P := by
  obtain ⟨_, z, hz, q, hq, e, hv, hs, Hd, hHd, he, hDH⟩ := hp.optimistic_supporter hy hopt
  obtain ⟨Hd', hHd', he', hPH⟩ := unanimous_next_votes_extend hp hc hP hslot hu hun hgu hR hub
    z hz q e hv ((hp.run.time_mono hq).trans hjb) hs
  obtain rfl : Hd' = Hd := hp.honest_coherent.1 hHd' hHd (he'.trans he.symm)
  exact SA.anc_total hp.honest_coherent hDH hPH

/-- Every high origin written through the update deadline compares with P. The
next-slot optimistic arm uses finite vote extension; later raw writes cannot occur. -/
theorem high_origin_compatible_before_update {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {x : Fin sp.n} {r m : Nat} (ho : Healing.HighOrigin tr H g x r m B)
    (ht : tr.time r ≤ sp.ts u + 6 * sp.Δ) : Compatible (tr.HonestBlocks H) B P := by
  have hr := (Healing.healthy_base_of_reset_catch_before hp hc).run.localRun
  have hub : sp.ts u + sp.Δ ≤ b := by linarith [sp.toParams.hΔ]
  have hrb := ht.trans hTb
  obtain ⟨ell, D, CV, hcall, hfl, _, _, _, hBD, _⟩ := hp.highOrigin_mem ho
  have hBDU := hBD.mono (SA.frameIn_of_callAt hr ho.1 hcall).2
  by_cases hmu : m < u
  · obtain ⟨q, e, ⟨ellv, hv⟩, hs, hq⟩ := honest_votes_in_slot hp hc hgu hR hub x ho.1
    obtain ⟨Hd, hHd, he, hBH⟩ := hp.high_origin_votes_before q (hq.trans hub)
      x r m B ho hrb x ho.1 ellv e hv (by omega)
    have heq : Hd = P := hr.coherent.1 hHd hP
      (he.trans (hun x ho.1 q e ⟨ellv, hv⟩ (hq.trans hub) hs))
    exact Or.inl (heq ▸ hBH)
  by_cases heq : m = u
  · subst m
    exact Or.inl (hBDU.trans (hp.same_slot_source_below_unanimous hc ho.1
      (Or.inl ⟨CV, hfl⟩) hrb (hp.cutZ_le_ts_of_highOrigin ho) hP hun))
  have hgt : u < m := by omega
  have hDP : Compatible (tr.HonestBlocks H) D P := by
    rcases hfl with ⟨ellr, C, hupd, _⟩ | hop
    · have ht' : tr.time r = sp.ts m + 6 * sp.Δ := hupd.2.2.1
      have := (SA.ts_lt_iff sp).2 (show (u : Int) < m by omega)
      exfalso; linarith
    · have hs : sp.slot (tr.time r) = m := hop.choose_spec.choose_spec.2.1
      have hdeadline : sp.slot (sp.ts u + 6 * sp.Δ) = u + 1 :=
        SA.slot_of_mem sp (u + 1)
          (by simp only [SA.SAParams.ts]; push_cast; linarith [sp.toParams.hΔ])
          (by simp only [SA.SAParams.ts]; push_cast; linarith [sp.toParams.hΔ])
      have hm := SA.slot_mono sp (hp.run.time_nonneg r) ht
      rw [hs, hdeadline] at hm
      have heq : m = u + 1 := by omega
      exact unanimous_next_optimistic_compatible hp hc hP hslot hu hun hgu hR hub
        ho.1 (heq ▸ hop) hrb
  rcases hDP with h | h
  · exact Or.inl (hBDU.trans h)
  · exact SA.anc_total hr.coherent hBDU h

/-- Finite finality compatibility through the update deadline, derived from actual
unanimous votes rather than an update-selection or high-origin compatibility duty. -/
theorem finalized_compatible_before_update {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} (ha : a ≤ tr.time k)
    (ht : tr.time k ≤ sp.ts u + 6 * sp.Δ) :
    Compatible (tr.HonestBlocks H) (tr.state y k).fg.F P := by
  obtain ⟨x, r, m, B, ho, hrk, _, hFB⟩ := hp.finalized_below_high_origin hy ha
    (fun q hq => (hp.run.time_mono hq.le).trans (ht.trans hTb))
  rcases high_origin_compatible_before_update hp hc hP hslot hu hun hgu hR hTb ho
      (hrk.trans ht) with h | h
  · exact Or.inl (hFB.trans h)
  · exact SA.anc_total hp.honest_coherent hFB h

/-- Finite deadline alternative: finality is below P, or an actual earlier report
extends P with strictly greater height at that reporter's own cut. -/
theorem finality_alternative_before_update {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} (ha : a ≤ tr.time k)
    (ht : tr.time k ≤ sp.ts u + 6 * sp.Δ) :
    Anc (tr.HonestBlocks H) (tr.state y k).fg.F P ∨
      ∃ z ∈ H, ∃ r ell C, r < k ∧ SA.ToFGAt tr.projAC z r ell C ∧
        tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C ∧
        ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h := by
  rcases hp.finality_below_or_higher_report hy
      (finalized_compatible_before_update hp hc hP hslot hu hun hgu hR hTb hy ha ht) with
    h | ⟨z, hz, r, ell, C, hrk, hto, hPC, hlt⟩
  · exact Or.inl h
  · exact Or.inr ⟨z, hz, r, ell, C, hrk, hto, (hp.run.time_mono hrk.le).trans ht, hPC, hlt⟩

/-- Every honest unanimous vote is uniquely present and early-resolved in a
bounded post-service call holding P. Restart and deadline duties are derived. -/
theorem unanimous_pool {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b) (hPt : P ∈ ell.frame.tree) :
    ∀ x ∈ H, ∃ v ∈ (tr.projAC.state y j).pool u, v.val = x ∧ v.head = P.root ∧
      SA.resolutionTime (tr.projAC.state y j) ell.frame v < SA.ETime.of (sp.ts u + 2 * sp.Δ) ∧
      ∀ v' ∈ (tr.projAC.state y j).pool u, v'.val = x → v' = v := by
  have hS := Healing.healthy_base_of_reset_catch_before hp hc
  have hrestart : ∀ k ≤ j, tr.projAC.RestartAt y k → tr.projAC.time k < sp.ts u := by
    intro k hkj hk
    have h := restart_before_unanimous_slot hp hR hy (Compose.projAC_restartAt.mp hk)
      ((hp.run.time_mono hkj).trans hjb)
    exact h.trans_lt ((SA.ts_lt_iff sp).2 (by omega))
  refine SA.unanimous_pool_before hS hy hcall hgu ht hjb ?_ hrestart hPt ?_
  · intro k hkj t _
    exact Compose.ac_deadline_le_of_restarts
      (fun r hr hrs => (hrestart r (hr.trans hkj) hrs).le) t
  · intro x hx
    have hub : sp.ts u + sp.Δ ≤ b := by linarith [sp.toParams.hΔ]
    obtain ⟨q, e, hv, hs, hq⟩ := honest_votes_in_slot hp hc hgu hR hub x hx
    exact ⟨q, e, hv, hs, hun x hx q e hv (hq.trans hub) hs⟩

/-- At an exact update, strict finalization turns compatibility into ancestry below
the unanimous proposal: a strict finalizer can have slot at most `u + 1`. -/
theorem finalized_below_unanimous_at_update {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPU : P ∈ tr.HonestBlocks H) (hPs : P.slot = u) (hu : 0 < u)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell) (ha : a ≤ tr.time j) :
    Anc (tr.HonestBlocks H) ell.frame.F P := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have ht : tr.time j = sp.ts u + 6 * sp.Δ := hup.2.2.1
  have hFR := finalized_compatible_before_update hp hc hPU hPs hu hun hgu hR hTb hy ha ht.le
  have hreach := Compose.fg_reachable hp.run.toLocalRun hy j
  have hFt := (Store.cache_invariants _ _ _ _ hreach).1
  rw [Compose.frame_of_projAC hp.run hy hup.1]
  change Anc (tr.HonestBlocks H) (tr.state y j).fg.F P
  by_cases hg : (tr.state y j).fg.F =
      sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload
  · exact Compose.honest_genesis_root_anc hp.run hr.coherent ⟨y, hy, j, hFt⟩
      (by rw [hg]; rfl) hPU
  obtain ⟨B, hBt, _, hFB, hne⟩ := Store.F_lt_finalizer hreach hg
  have hBf : B ∈ ell.frame.tree := by
    rw [Compose.frame_of_projAC hp.run hy hup.1]
    exact ⟨hBt, hFB⟩
  have hsl : sp.slot (tr.projAC.time j) = u + 1 := by
    change sp.slot (tr.time j) = u + 1
    rw [ht, (SA.slot_arithmetic sp u).2.2]
    simpa using (SA.slot_arithmetic sp (u + 1)).1 2 (by omega)
  have hBs : B.slot ≤ u + 1 := hsl ▸ SA.frame_slot_le sp hr hy hup.1 B hBf
  have hFs : (tr.state y j).fg.F.slot < B.slot :=
    (Anc.slot_le hr.coherent (hFB.mono (fun X hX => ⟨y, hy, j, hX⟩))).2 hne
  rcases hFR with h | hPF
  · exact h
  by_cases he : P = (tr.state y j).fg.F
  · exact he ▸ .refl
  have := (Anc.slot_le hr.coherent hPF).2 he
  omega

/-- An actual post-drain honest proposal is selected at every bounded honest update.
Current-frame heldness and live-lock compatibility are conclusions of the assembly. -/
theorem operational_update_selection {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell) :
    P ∈ ell.frame.tree ∧
      SA.getConfirmation sp (tr.projAC.state y j) ell.frame u = some P ∧
      ¬ SA.conflictsWithLock sp (tr.projAC.state y j).locks ell.frame (tr.time j) P ∧
      SA.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P ∧
      tr.projAC.post j = SA.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u ∧
      (tr.projAC.post j).latestConfirmed =
        (SA.updateLatestConfirmed sp (tr.projAC.state y j) ell.frame P).latestConfirmed := by
  have hDelta := sp.toParams.hΔ
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have ht : tr.time j = sp.ts u + 6 * sp.Δ := hup.2.2.1
  have hjb : tr.time j ≤ b := ht ▸ hTb
  have hub : sp.ts u + sp.Δ ≤ b := by linarith
  have hun : ∀ z ∈ H, ∀ q e, SA.VoteAt tr.projAC z q e → tr.time q ≤ b →
      e.msg.slot = u → e.msg.head = P.root := fun z hz q e hv hqb hs =>
    hp.operational_unanimous hc hpH hdesignated hactual hPs hR (by linarith)
      z hz q e hv hs hqb
  have hRnext := hR.trans ((SA.ts_le_iff sp).2 (show (u : Int) ≤ (u + 1 : Nat) by omega))
  have hu : 0 < u := by
    rw [Healing.drainTime_eq] at hR
    have := (SA.ts_le_iff sp).1 hR
    push_cast at this
    omega
  have hacc := Compose.proposal_accepted hp.run hp.noColl hpH hactual
  have hPU : P ∈ tr.HonestBlocks H := by
    refine ⟨p, hpH, k + 1, ?_⟩
    rw [tr.state_succ_of_call hacc,
      (Store.tree_grows _ _ _ _ (Compose.fg_reachable hp.run.toLocalRun hpH _)).1 P _
        (hp.run.toLocalRun.cutLaw p hpH _ _ hacc).2.1]
    exact Set.mem_insert _ _
  have hca := Healing.cutZ_lt_reset_of_snapshot hp.run
    (by obtain ⟨q, hq, _⟩ := hp.snapshot; exact ⟨q, hq⟩) hp.reset
  have ha0 : 0 ≤ a := by
    have := Healing.lt_cutZ sp g
    have := SA.gbar_nonneg g
    linarith
  have haR : a ≤ Healing.drainTime sp a := by
    have ha' : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
      omega
    apply ha'.le.trans
    rw [Healing.drainTime_eq]
    exact (SA.ts_le_iff sp).2 (by push_cast; omega)
  have hFP := finalized_below_unanimous_at_update hp hc hPU hPs hu hun hgu hRnext hTb hy hup
    (by rw [ht]; linarith [haR.trans hR])
  obtain ⟨q, e, ⟨ellv, hv⟩, hs, hq⟩ := honest_votes_in_slot hp hc hgu hRnext hub y hy
  obtain ⟨⟨Hd, hHd, he, _⟩, _⟩ := Compose.cast_head_fcRoot hr hy hv
  have hPsiU := (SA.frameIn_of_callAt hr hy hv.1).2
  have heq : Hd = P := hr.coherent.1 (hPsiU hHd) hPU
    (he.trans (hun y hy q e ⟨ellv, hv⟩ (hq.trans hub) hs))
  subst Hd
  obtain ⟨ka, hka, haccept⟩ := (SA.frame_genesis_or_accepted sp hr hy hv.1 P hHd).resolve_left
    (by omega)
  have hqj : q ≤ j := by
    by_contra hn
    have hm := hp.run.time_mono (Nat.le_of_not_ge hn)
    rw [ht] at hm
    linarith
  have hPt := SA.mem_tree_of_acceptAt sp hr hy haccept (hka.trans hqj) hup.1 hFP
  have hPg : P.root ≠ sp.genesisRoot := by
    intro he
    have hG := Healing.Store.genesis_mem (Compose.fg_reachable hp.run.toLocalRun hpH k)
    have heq := hr.coherent.1 hPU ⟨p, hpH, k, hG⟩ he
    have hz : P.slot = 0 := by rw [heq]; rfl
    omega
  have hpool := unanimous_pool hp hc hun hgu hRnext hy hup.1
    (by rw [ht]; linarith) hjb hPt
  have hts : Healing.cutZ sp.toParams g ≤ sp.ts u := hca.le.trans (haR.trans hR)
  have hvote : ∃ z ∈ H, ∃ q ell e, SA.CastAt tr.projAC z q ell e ∧
      tr.time q ≤ b ∧ e.msg.slot = u := ⟨y, hy, q, ellv, e, hv, hq.trans hub, hs⟩
  have hlocks := hp.call_locks_compatible_of_unanimous hc hPU hts hun hvote hy hup.1 hjb
    (by rw [ht]; linarith) ht.le (fun r hr B CV ho =>
      unanimous_next_optimistic_compatible hp hc hPU hPs hu hun hgu hRnext hub hy ho
        ((hp.run.time_mono hr.le).trans hjb))
  exact ⟨hPt, hp.ready_update_selection_of_pool hy hup hPt hPg hpool hlocks⟩

/-- The effective post-update record extends the actual operational proposal in
the update's frame, including when the raw record keeps a later optimistic source. -/
theorem operational_update_effective_record {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell) :
    Anc (tr.HonestBlocks H) P
      ((SA.lookup ell.frame (tr.projAC.post j).latestConfirmed).getD ell.frame.F) := by
  obtain ⟨hPt, _, _, _, _, hrecord⟩ :=
    operational_update_selection hp hc hpH hdesignated hactual hPs hR hgu hTb hy hup
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hup.1
  rw [hrecord]
  exact (effective_record_update_slot_growth (sp := sp) hPhi hPt).1.mono hPhiU

/-- Selection repairs source recency even if it retains a strict descendant of
the proposal. The source precedes the actual update's post-state. -/
theorem operational_update_recent_source {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell)
    {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hlookup : SA.lookup (Node.frame (tr.state y (j + 1)))
      (tr.state y (j + 1)).ac.latestConfirmed = some R) :
    ∃ x ∈ H, ∃ q s CV, q ≤ j ∧ tr.time q ≤ tr.time j ∧ u ≤ s ∧
      (SA.ResultAt tr.projAC x q s R CV ∨ SA.OptimisticLockAt tr.projAC x q s R CV) := by
  obtain ⟨hPt, hconf, _, _, _, hrecord⟩ :=
    operational_update_selection hp hc hpH hdesignated hactual hPs hR hgu hTb hy hup
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hc' := Compose.projAC_callAt.mp hup.1
  have hlaw := hp.run.toLocalRun.cutLaw y hy j _ hc'
  have hframe : Node.frame (tr.state y (j + 1)) = ell.frame := by
    rw [tr.state_succ_of_call hc', hlaw.1]
    exact congrArg Store.toFrame hlaw.2.2.1
  have hstate := Compose.projAC_state hp.run.toLocalRun hy (j + 1)
  rw [tr.projAC.state_succ_of_call hup.1] at hstate
  have hgrowth := (effective_record_update_slot_growth (sp := sp) (A := tr.projAC.state y j)
    (SA.frameIn_of_callAt hr hy hup.1).1 hPt).2
  rw [← hrecord, hstate, ← hframe, hlookup] at hgrowth
  simp only [Option.getD_some] at hgrowth
  rcases hgrowth with rfl | hlt
  · exact ⟨y, hy, j, u, _, le_rfl, le_rfl, le_rfl, Or.inl ⟨ell, hup, hconf, rfl⟩⟩
  obtain ⟨C, hC, hCr, hsource⟩ := Compose.record_origin_before hp.run hp.noColl hy (j + 1)
  obtain ⟨hRm, hRr⟩ := SA.lookup_eq_some hlookup
  have heq : C = R := hp.honest_coherent.1 ⟨y, hy, j + 1, hC⟩
    ⟨y, hy, j + 1, hRm.1⟩ (hCr.trans hRr.symm)
  subst C
  rcases hsource with hz | ⟨s, hs⟩
  · have he := Compose.honest_eq_genesis hp.run hp.honest_coherent
      (show R ∈ tr.HonestBlocks H from ⟨y, hy, j + 1, hC⟩) hz
    rw [he] at hlt
    exact False.elim (Nat.not_lt_zero _ hlt)
  obtain ⟨x, hx, q, hq, CV, hsrc⟩ := Compose.originBefore_iff.mp hs
  refine ⟨x, hx, q, s, CV, by omega, hp.run.time_mono (by omega), ?_, hsrc⟩
  rw [hPs] at hlt
  rcases hsrc with ⟨e, hu, hsel, _⟩ | ⟨e, A, ho, hslot, hsel, _⟩
  · have hRs := SA.frame_slot_le sp hr hx hu.1 R (SA.deepest_mem hsel).1.1
    have hsl : sp.slot (tr.projAC.time q) = s + 1 := by
      rw [hu.2.2.1]
      apply SA.slot_of_mem sp (s + 1) <;>
        simp only [SA.SAParams.ts] <;> push_cast <;> linarith [sp.toParams.hΔ]
    rw [hsl] at hRs
    omega
  · have hm : R ∈ e.frame.tree := by
      unfold SA.optimisticSelect at hsel
      dsimp only at hsel
      split_ifs at hsel
      exact (SA.deepest_mem hsel).1.1
    have hRs := SA.frame_slot_le sp hr hx ho.1 R hm
    change sp.slot (tr.projAC.time q) = s at hslot
    omega

/-- Retaining the local entry at the height floor gives a candidate, without a
remote-report alternative, at a state with a bounded completed prefix. -/
theorem held_target_ancestor_candidate_at_state {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y v : Fin sp.n} (hy : y ∈ H) {i q m : Nat}
    (hib : ∀ r < i, tr.time r ≤ b) {P S : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ (Node.frame (tr.state y i)).tree)
    (hseed : Healing.HighOrigin tr H g v q m S)
    (hqb : tr.time q ≤ b) (hSP : Anc (tr.HonestBlocks H) S P)
    (hcompare : ∀ x r l B, r < i → Healing.HighOrigin tr H g x r l B →
      Compatible (tr.HonestBlocks H) P B) :
    (Node.frame (tr.state y i)).AncestorCandidate P := by
  have hreach := Compose.fg_reachable hp.run.toLocalRun hy i
  have hPhi := (Store.frame_realization _ _ _ _ hreach).1
  have hPhiU : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocks H :=
    fun X hX => ⟨y, hy, i, hX.1⟩
  have hPy := hPt.1
  have hSy := hp.mem_tree_of_anc hy hSP hPy
  have hroot : Compatible (tr.HonestBlocks H) (Node.frame (tr.state y i)).fcRoot P := by
    by_cases hlow : (tr.state y i).fg.hj ≤ Healing.HZ tr H g
    · exact hp.low_root_of_held_seed_at_state hy hPy hy hseed hSy hlow
        (Or.inr hSP) (fun _ => hPy)
    · exact hp.high_J_root_of_held_at_state_before hy hPy hy (by omega) hcompare
  rcases hroot with hroot | hroot
  swap
  · exact Or.inl (SA.anc_tree_of_anc_U hp.honest_coherent hPhi hPhiU hPt hroot hPhi.fcRoot_mem)
  have hrootf := SA.anc_tree_of_anc_U hp.honest_coherent hPhi hPhiU
    hPhi.fcRoot_mem hroot hPt
  have witness : ∃ E ∈ (tr.state y i).fg.tree,
      Anc (tr.HonestBlocks H) P E ∧
      (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ E.root).h := by
    by_cases hfloor : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ P.root).h
    · exact ⟨P, hPy, .refl, hfloor⟩
    obtain ⟨-, -, -, -, -, -, -, -, -, hSs⟩ := hp.highOrigin_mem hseed
    have hSh := Healing.σ_h_le_of_anc hreach (hp.anc_tree_of_anc hy hSP hPy)
    have hSf : ((tr.state v q).fg.σ S.root).h < (tr.state y i).fg.headHeightFloor := by
      rw [hp.σ_eq_run hseed.1 hy hSs hSy]
      omega
    obtain ⟨x, r, l, B, E, hri, ho, -, hE, hEB, -, hEf, -⟩ :=
      hp.high_floor_signed_source_of_row_bound hseed hy (u := sp.slot (tr.time i) + 1)
        (fun W hW att ha z hz d hd hdi r' l O hrd ho => by
          obtain ⟨-, D, CV, -, hfl, -⟩ := hp.highOrigin_mem ho
          have ht : sp.ts l ≤ tr.time r' := by
            rcases hfl with ⟨ell, C, ⟨-, -, ht, -⟩, -⟩ | ⟨ell, A, -, hsl, -⟩
            · change tr.time r' = sp.ts l + 6 * sp.Δ at ht
              linarith [sp.toParams.hΔ]
            · change sp.slot (tr.time r') = l at hsl
              exact (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg r') l).2 (by omega)
          have := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg i) l).1
            (ht.trans (hp.run.time_mono (by omega)))
          omega)
        (fun x r l B hri ho x' r' l' B' hr'i ho' => hp.origins_compatible ho
          (hib r hri) ho' (hib r' hr'i))
        (fun x r l B hri ho => hp.origins_compatible hseed hqb ho
          (hib r hri)) hSf
    have hPE : Compatible (tr.HonestBlocks H) P E := by
      rcases hcompare x r l B hri ho with h | h
      · exact SA.anc_total hp.honest_coherent h hEB
      · exact Or.inr (hEB.trans h)
    rcases hPE with hPE | hEP
    · exact ⟨E, hE, hPE, hEf⟩
    · have := Healing.σ_h_le_of_anc hreach (hp.anc_tree_of_anc hy hEP hPy)
      omega
  obtain ⟨E, hE, hPE, hEf⟩ := witness
  have hPEs := hp.anc_tree_of_anc hy hPE hE
  have hEt : E ∈ (Node.frame (tr.state y i)).tree := ⟨hE, hPt.2.trans hPEs⟩
  have hPEf := SA.anc_tree_of_anc_U hp.honest_coherent hPhi hPhiU hPt hPE hEt
  refine Or.inr ⟨hPt, hrootf, E, hEt, ?_, hPEf⟩
  have hRE := hrootf.trans hPEf
  exact ⟨hE, hPt.2.trans hPEs, Anc.mono (fun _ h => h.1) hRE, hEf⟩

/-- At a bounded call holding a target above a bounded high seed, compatible
causal origins give full viability or an actual earlier strictly higher report. -/
theorem held_target_viable_or_higher_report {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y v : Fin sp.n} (hy : y ∈ H) {i q m : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} (hcall : tr.projAC.CallAt y i ell)
    (hib : tr.time i ≤ b) {P S : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ ell.frame.tree) (hseed : Healing.HighOrigin tr H g v q m S)
    (hqb : tr.time q ≤ b) (hSP : Anc (tr.HonestBlocks H) S P)
    (hcompare : ∀ x r l B, r < i → Healing.HighOrigin tr H g x r l B →
      Compatible (tr.HonestBlocks H) P B) :
    P ∈ ell.frame.viableTree ell.frame.tree ∨
      ∃ x ∈ H, ∃ r ell' C, r < i ∧ SA.ToFGAt tr.projAC x r ell' C ∧
        Anc (tr.HonestBlocks H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hcall
  have hPy := hp.frame_tree_subset hy hcall hPt
  have hfr := Compose.frame_of_projAC hp.run hy hcall
  have hroot : Compatible (tr.HonestBlocks H) ell.frame.fcRoot P := by
    by_cases hlow : (tr.state y i).fg.hj ≤ Healing.HZ tr H g
    · exact hp.low_root_of_held_seed_at_call hy hPy hy hseed hcall
        (hp.mem_tree_of_anc hy hSP hPy) hlow (Or.inr hSP) (fun _ => hPt)
    · exact hp.high_J_root_of_held_at_call_before hy hPy hy hcall (by omega) hcompare
  by_cases hrootP : Anc (tr.HonestBlocks H) ell.frame.fcRoot P
  · by_cases hfloor : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ P.root).h
    · have hrootf := SA.anc_tree_of_anc_U hp.honest_coherent hPhi hPhiU
        hPhi.fcRoot_mem hrootP hPt
      refine Or.inl ⟨hPt, hrootf, P, hPt, ?_, .refl⟩
      have hPt' := hPt
      rw [hfr] at hPt' hrootf ⊢
      exact ⟨hPy, hPt'.2, hrootf.mono (fun X hX => hX.1), hfloor⟩
    · exact Or.inr (hp.held_target_high_floor_report_before hy hPy hseed hSP
        (fun x r l B hri ho x' r' l' B' hr'i ho' => hp.origins_compatible ho
          ((hp.run.time_mono hri.le).trans hib) ho' ((hp.run.time_mono hr'i.le).trans hib))
        (fun x r l B hri ho => hp.origins_compatible hseed hqb ho
          ((hp.run.time_mono hri.le).trans hib)) hcompare (lt_of_not_ge hfloor))
  · have hPR := hroot.resolve_left hrootP
    have hne : P ≠ ell.frame.fcRoot := fun he => hrootP (he ▸ .refl)
    have hJ : ell.frame.fcRoot = (tr.state y i).fg.J := by
      have hFP := (hPhi.rooted.2 P hPt).mono hPhiU
      rw [hfr] at hrootP hFP ⊢
      change ¬ Anc (tr.HonestBlocks H) (tr.state y i).fg.fcRoot P at hrootP
      change Anc (tr.HonestBlocks H) (tr.state y i).fg.F P at hFP
      change (tr.state y i).fg.fcRoot = _
      unfold Store.fcRoot at hrootP ⊢
      split_ifs at hrootP ⊢ with hactive
      · rfl
      · exact False.elim (hrootP hFP)
    have hf : Hᶜ.ncard < sp.toParams.fg.q := by
      have hf := hp.faults
      have hn : 0 < sp.n := sp.toParams.hn
      change 3 * Hᶜ.ncard ≤ sp.n - 1 at hf
      change Hᶜ.ncard < (2 * sp.n + 2) / 3
      omega
    obtain ⟨x, hx, r, hri, d, _, att, ell', C, _, _, _, _, hto, _, hJx, hJC, _, hCh, hPh⟩ :=
      Healing.cache_ahead_report hp.run hp.noColl hf hy (Or.inr hJ) hPy hPR hne
    have hPx := hp.mem_tree_of_anc hx hPR hJx
    have hσ := hp.σ_eq_run hy hx hPy hPx
    exact Or.inr ⟨x, hx, r, ell', C, hri, hto, hPR.trans hJC, by
      rw [← hσ, hCh]
      exact hPh⟩

/-- Bounded nonunanimous next-update selection: the finalized-floor guard is
explicit, while actual votes, their pool membership and resolution are produced. -/
theorem optimistic_next_result_of_floor {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r s j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hop : SA.OptimisticLockAt tr.projAC x r s B CV)
    (hs : Healing.cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC y j (s + 1) ell)
    (hjb : tr.time j ≤ b) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts (s + 1 : Nat))
    (hR : Healing.drainTime sp a ≤ sp.ts (s + 1 + 1 : Nat))
    (hFB : Anc (tr.HonestBlocks H) ell.frame.F B) :
    ∃ D DV, SA.ResultAt tr.projAC y j (s + 1) D DV ∧ Anc (tr.HonestBlocks H) B D := by
  have hS := Healing.healthy_base_of_reset_catch_before hp hc
  have hr := hS.run.localRun
  have htime : tr.time j = sp.ts (s + 1 : Nat) + 6 * sp.Δ := hu.2.2.1
  have hd := sp.toParams.hΔ
  have hrs : ∀ k ≤ j, tr.projAC.RestartAt y k → tr.time k < sp.ts (s + 1 : Nat) := by
    intro k hkj hk
    have hh := restart_before_unanimous_slot hp hR hy (Compose.projAC_restartAt.mp hk)
      ((hp.run.time_mono hkj).trans hjb)
    have hlt := (SA.ts_lt_iff sp).mpr (show ((s + 1 : Nat) : Int) - 1 < (s + 1 : Nat) by omega)
    exact hh.trans_lt hlt
  have hext : ∀ z ∈ H, ∀ q e, SA.VoteAt tr.projAC z q e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
    intro z hz q e hv hes
    have hqb : tr.time q ≤ b := by
      have ht := SA.vote_time_le hr hz hv
      obtain ⟨ellq, hcast⟩ := hv
      rw [← (SA.castAt_spec hr hz hcast).2.1, hes] at ht
      exact ht.trans (by linarith)
    obtain ⟨ellq, hcast⟩ := hv
    exact hp.fast_source_votes_before hc hx (Or.inr hop)
      (by have := sp.two_le_k; omega) hrb q hqb z hz ellq e hcast (by omega)
  obtain ⟨hpool, hres⟩ := hp.extending_votes_resolved_before hc hy hu.1 hgu
    (by linarith) hjb
    (fun k hkj t _ => Healing.deadline_le_restarts
      (fun k' hk' hk => (hrs k' (hk'.trans hkj) hk).le) t) hrs hFB hext
  have hall := honest_votes_in_slot hp hc hgu hR (show sp.ts (s + 1 : Nat) + sp.Δ ≤ b by linarith)
  have hH : H ⊆ {v | v ∈ H ∧ ∃ vote ∈ (tr.projAC.state y j).pool (s + 1), vote.val = v} := by
    intro z hz
    obtain ⟨q, e, hv, hes, _⟩ := hall z hz
    obtain ⟨ellq, hcast⟩ := hv
    exact ⟨hz, e.msg, hpool z hz q e ⟨ellq, hcast⟩ hes, (SA.castAt_spec hr hz hcast).1⟩
  have hcount := Set.ncard_le_ncard hH
  have hsum : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hf := hp.faults
  have hn : 0 < sp.n := sp.toParams.hn
  obtain ⟨D, hconf, hBD, _⟩ := SA.update_extends_of_resolved_votes hS.run
    (by omega) hext hy hu (by omega) hres
  exact ⟨D, _, ⟨ell, hu, hconf, rfl⟩, hBD⟩

/-- A deepest block of `T` lying in `S ⊆ T` is the deepest block of `S`. -/
private theorem deepest_of_subset {FGP : Type} {Φ : SA.Frm sp.n FGP}
    {S T : Set (SA.Blk sp.n FGP)} {D : SA.Blk sp.n FGP} (hT : SA.deepest Φ T = some D)
    (hST : S ⊆ T) (hD : D ∈ S) : SA.deepest Φ S = some D := by
  have h : SA.IsDeepest Φ S D := ⟨hD, fun C hC hne => (SA.deepest_mem hT).2 C (hST hC) hne⟩
  cases hd : SA.deepest Φ S with
  | none =>
    unfold SA.deepest at hd
    simp only [show ∃ B, SA.IsDeepest Φ S B from ⟨D, h⟩, ↓reduceDIte, reduceCtorEq] at hd
  | some D' =>
    have h' := SA.deepest_mem hd
    by_contra hne
    have hne' : D' ≠ D := fun h => hne (congrArg some h)
    rcases h.2 D' h'.1 hne' with h₁ | ⟨h₁, h₂⟩ <;>
      rcases h'.2 D h.1 (Ne.symm hne') with h₃ | ⟨h₃, h₄⟩ <;> omega

/-- Full viability makes the newly selected fast lock an exact toFG candidate,
including the second normalization by liveLocks at the adjacent call. -/
theorem candidate_after_fast_update {A : SA.SAState sp.n} {Phi : SA.Frm sp.n FGP}
    (hPhi : FrameOK Phi) {t : Time} {u : Nat} {P : SA.Blk sp.n FGP}
    (hPv : P ∈ Phi.viableTree Phi.tree)
    (hconf : SA.getConfirmation sp A Phi u = some P)
    (hnv : ¬ SA.conflictsWithLock sp A.locks Phi t P)
    (hfast : SA.fastSelect sp A Phi u P = some P)
    (_hlive : sp.slot t ≤ u + sp.k) (hage : sp.slot t ≤ u + 2) :
    P ∈ SA.toFGCandidates sp (SA.updateConfirmation sp A Phi t u) Phi t := by
  have hself : Phi.viableAncestor P = P := SA.viableAncestor_self hPhi hPv.1 (Or.inl hPv)
  -- unvetoed, so the filtered fast selection is the raw one; its expiry is `fastExpiry ≥ u + 2`
  have hD := deepest_of_subset (S := {B | B ∈ {B | B ∈ SA.confirmationPath sp Phi P ∧
      ¬ SA.conflictsWithLock sp A.locks Phi t B} ∧ SA.FastTest sp A Phi u B}) hfast
    (fun B hB => ⟨hB.1.1, hB.2⟩)
    ⟨⟨(SA.deepest_mem hfast).1.1, hnv⟩, (SA.deepest_mem hfast).1.2⟩
  have hlock : ∃ e, sp.slot t ≤ e ∧ (⟨P.root, u, true, e⟩ : SA.Lock) ∈
      (SA.updateConfirmation sp A Phi t u).locks := by
    unfold SA.updateConfirmation
    simp only [hconf]
    rw [ite_eq_right hnv]
    exact ⟨_, hage.trans (SA.le_fastExpiry sp _ _ _ _), ⟨P.root, u, true, _⟩,
      Or.inr ⟨_, Or.inl ⟨P, hD, rfl⟩, rfl⟩, P, hPv.1, rfl,
      hage.trans (SA.le_fastExpiry sp _ _ _ _), by rw [hself]⟩
  obtain ⟨e, he, hlock⟩ := hlock
  exact ⟨hPv, ⟨P.root, u, true, e⟩, ⟨⟨P.root, u, true, e⟩, hlock, P, hPv.1, rfl, he,
    by rw [hself]⟩, rfl, rfl, hage⟩

/-- The exact fast candidate persists into an adjacent call with the same frame
and timestamp; these are the equalities supplied by `update_toFG_calls`. -/
theorem candidate_at_adjacent_call
    {y : Fin sp.n} {j u : Nat} {ell ell' : ACLabel (goldilocksNode sp ro)}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hc : tr.projAC.CallAt y j ell) (hPhi : FrameOK ell.frame)
    (hframe : ell'.frame = ell.frame) (htime : tr.time (j + 1) = tr.time j)
    (hPv : P ∈ ell.frame.viableTree ell.frame.tree)
    (hconf : SA.getConfirmation sp (tr.projAC.state y j) ell.frame u = some P)
    (hnv : ¬ SA.conflictsWithLock sp (tr.projAC.state y j).locks ell.frame (tr.time j) P)
    (hfast : SA.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P)
    (hpost : tr.projAC.post j =
      SA.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u)
    (hlive : sp.slot (tr.time j) ≤ u + sp.k) (hage : sp.slot (tr.time j) ≤ u + 2) :
    P ∈ SA.toFGCandidates sp (tr.projAC.state y (j + 1)) ell'.frame (tr.time (j + 1)) := by
  rw [tr.projAC.state_succ_of_call hc, hpost, hframe, htime]
  exact candidate_after_fast_update hPhi hPv hconf hnv hfast hlive hage

/-- A full viable unanimous pool at an actual update produces an actual report
at or before the adjacent toFG call, not merely a selected candidate. -/
theorem report_of_viable_unanimous_pool {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat}
    {ell ell' : ACLabel (goldilocksNode sp ro)}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hu : SA.UpdateAt tr.projAC y j u ell)
    (hc : tr.projAC.CallAt y (j + 1) ell') (hto : ell'.call = .toFG)
    (hframe : ell'.frame = ell.frame) (htime : tr.time (j + 1) = tr.time j)
    (hjoin : SA.joined sp (tr.projAC.state y (j + 1)) (tr.time (j + 1)))
    (hPg : P.root ≠ sp.genesisRoot) (hPv : P ∈ ell.frame.viableTree ell.frame.tree)
    (hpool : ∀ v ∈ H, ∃ vote ∈ (tr.projAC.state y j).pool u,
      vote.val = v ∧ vote.head = P.root ∧
      SA.resolutionTime (tr.projAC.state y j) ell.frame vote < SA.ETime.of (sp.ts u + 2 * sp.Δ) ∧
      ∀ vote' ∈ (tr.projAC.state y j).pool u, vote'.val = v → vote' = vote)
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp (tr.projAC.state y j).locks ell.frame (tr.time j),
      Compatible (tr.HonestBlocks H) L P)
    (hnext : ∀ C ∈ SA.toFGCandidates sp (tr.projAC.state y (j + 1)) ell'.frame (tr.time (j + 1)),
      Compatible (tr.HonestBlocks H) C P)
    (hlive : sp.slot (tr.time j) ≤ u + sp.k) (hage : sp.slot (tr.time j) ≤ u + 2) :
    ∃ r e R, SA.ToFGAt tr.projAC y r e R ∧ tr.time r ≤ tr.time (j + 1) ∧
      Anc (tr.HonestBlocks H) P R := by
  obtain ⟨hconf, hnv, hfast, hpost, _⟩ :=
    hp.ready_update_selection_of_pool hy hu hPv.1 hPg hpool hlocks
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hPc := candidate_at_adjacent_call hu.1 (SA.frameIn_of_callAt hr hy hu.1).1
    hframe htime hPv hconf hnv hfast hpost hlive hage
  exact Healing.report_of_compatible_candidate_of_run hp.run hp.noColl hy hc hto hjoin hPg hPc hnext

/-- An honest node retains its unanimous vote head at a later call whenever
that call's finality is still below the head. -/
theorem unanimous_head_held_at_call {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) (ht : sp.ts u + sp.Δ < tr.time j)
    (hjb : tr.time j ≤ b) (hFP : Anc (tr.HonestBlocks H) (tr.state y j).fg.F P) :
    P ∈ ell.frame.tree := by
  have hr := (Healing.healthy_base_of_reset_catch_before hp hc).run.localRun
  have hub : sp.ts u + sp.Δ ≤ b := ht.le.trans hjb
  obtain ⟨q, e, ⟨ellv, hv⟩, hs, hq⟩ := honest_votes_in_slot hp hc hgu hR hub y hy
  obtain ⟨⟨Hd, hHd, he, _⟩, _⟩ := Compose.cast_head_fcRoot hr hy hv
  obtain rfl : Hd = P := hr.coherent.1 ((SA.frameIn_of_callAt hr hy hv.1).2 hHd) hP
    (he.trans (hun y hy q e ⟨ellv, hv⟩ (hq.trans hub) hs))
  have hqj : q ≤ j := by
    by_contra hn
    have := hp.run.time_mono (show j ≤ q by omega)
    linarith
  have hPy := (Compose.fg_grows hp.run hy hqj).1
    (Healing.mem_tree_of_frame hp.run hy hv.1 hHd)
  rw [Compose.frame_of_projAC hp.run hy hcall]
  exact ⟨hPy, Healing.store_anc_of_honest_anc hp.run hp.noColl hy hFP hPy⟩

/-- At the update deadline, finality below the unanimous head gives full
viability or an actual higher report. Holding and the high seed are derived. -/
theorem unanimous_viable_or_higher_report {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) (ht : tr.time j = sp.ts u + 6 * sp.Δ)
    (hFP : Anc (tr.HonestBlocks H) (tr.state y j).fg.F P) :
    P ∈ ell.frame.viableTree ell.frame.tree ∨
      ∃ x ∈ H, ∃ r e C, r < j ∧ SA.ToFGAt tr.projAC x r e C ∧
        tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  have hjb : tr.time j ≤ b := ht ▸ hTb
  have hPt := unanimous_head_held_at_call hp hc hP hun hgu hR hy hcall
    (by rw [ht]; linarith [sp.toParams.hΔ]) hjb hFP
  obtain ⟨v, q, m, S, ho, hqb, _, hqt⟩ := hp.reset_seed_before_slot hR
  have hSP := high_origins_before_next_slot_below hp hc hP hun hgu hR
    (by linarith [sp.toParams.hΔ]) ho hqt hqb
  have hcompare : ∀ x r l B, r < j → Healing.HighOrigin tr H g x r l B →
      Compatible (tr.HonestBlocks H) P B := by
    intro x r l B hrj horig
    exact (high_origin_compatible_before_update hp hc hP hslot hu hun hgu hR hTb
      horig ((hp.run.time_mono hrj.le).trans ht.le)).symm
  rcases held_target_viable_or_higher_report hp hy hcall hjb hPt ho hqb hSP hcompare with
    hv | ⟨x, hx, r, e, C, hrj, hto, hPC, hh⟩
  · exact Or.inl hv
  · exact Or.inr ⟨x, hx, r, e, C, hrj, hto, (hp.run.time_mono hrj.le).trans ht.le, hPC, hh⟩

/-- Finite report duty from actual unanimity: each honest node reports above P
by the update deadline, unless an honest strict-higher report already exists. -/
theorem report_cover_of_unanimous {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b) :
    (∀ y ∈ H, ∃ r e R, SA.ToFGAt tr.projAC y r e R ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P R) ∨
    (∃ x ∈ H, ∃ r e C, SA.ToFGAt tr.projAC x r e C ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h) := by
  classical
  by_cases hescape : ∃ x ∈ H, ∃ r e C, SA.ToFGAt tr.projAC x r e C ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h
  · exact Or.inr hescape
  left
  intro y hy
  have hd := sp.toParams.hΔ
  have hub : sp.ts u + sp.Δ ≤ b := by linarith
  have hjoin : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) ≤ sp.ts u := by
    have hbase := (SA.ts_le_iff_le_slot sp (SA.gbar_nonneg g) (sp.slot (SA.gbar g))).2 (by rfl)
    simp only [SA.SAParams.ts] at hbase ⊢
    simp only [SA.SAParams.ts] at hgu
    push_cast at *
    linarith
  obtain ⟨j, ell, ell', hup, hto, htoeq, hnexttime, hframe, hjoined⟩ :=
    hp.update_toFG_calls hy hjoin hTb
  have hjtime : tr.time j = sp.ts u + 6 * sp.Δ := hup.2.2.1
  have hjb : tr.time j ≤ b := hjtime ▸ hTb
  have hnextb : tr.time (j + 1) ≤ b := hnexttime ▸ hTb
  have hRT : Healing.drainTime sp a ≤ sp.ts u + 6 * sp.Δ := by
    simp only [SA.SAParams.ts] at hR ⊢
    push_cast at *
    linarith
  have hca := Healing.cutZ_lt_reset_of_snapshot hp.run
    (by obtain ⟨k, hk, -⟩ := hp.snapshot; exact ⟨k, hk⟩) hp.reset
  have ha0 : 0 ≤ a := by
    have := Healing.lt_cutZ sp g
    have := SA.gbar_nonneg g
    linarith
  have haT : a ≤ sp.ts u + 6 * sp.Δ := by
    have hanext : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
      omega
    have hle : sp.ts ((sp.slot a : Int) + 1) ≤ Healing.drainTime sp a := by
      rw [Healing.drainTime_eq]
      exact (SA.ts_le_iff sp).2 (by push_cast; omega)
    exact (hanext.le.trans hle).trans hRT
  have hFP : Anc (tr.HonestBlocks H) (tr.state y j).fg.F P := by
    rcases finality_alternative_before_update hp hc hP hslot hu hun hgu hR hTb hy
        (hjtime ▸ haT) hjtime.le with h | ⟨x, hx, r, e, C, _, hto, ht, hPC, hh⟩
    · exact h
    · exact False.elim (hescape ⟨x, hx, r, e, C, hto, ht, hPC, hh⟩)
  have hPv : P ∈ ell.frame.viableTree ell.frame.tree := by
    rcases unanimous_viable_or_higher_report hp hc hP hslot hu hun hgu hR hTb hy
        hup.1 hjtime hFP with h | ⟨x, hx, r, e, C, _, hto, ht, hPC, hh⟩
    · exact h
    · exact False.elim (hescape ⟨x, hx, r, e, C, hto, ht, hPC, hh⟩)
  have hpool := unanimous_pool hp hc hun hgu hR hy hup.1
    (by rw [hjtime]; linarith) hjb hPv.1
  have hts : Healing.cutZ sp.toParams g ≤ sp.ts u := by
    have hk := sp.two_le_k
    apply hp.clean_window_timing (s := u) ?_ u (by omega)
    rw [Healing.cleanLabel_eq]
    rw [Healing.drainTime_eq] at hR
    have := (SA.ts_le_iff sp).1 hR
    push_cast at this
    omega
  obtain ⟨q, e, ⟨ellv, hv⟩, hs, hq⟩ := honest_votes_in_slot hp hc hgu hR hub y hy
  have hvote : ∃ z ∈ H, ∃ q ell e, SA.CastAt tr.projAC z q ell e ∧
      tr.time q ≤ b ∧ e.msg.slot = u := ⟨y, hy, q, ellv, e, hv, hq.trans hub, hs⟩
  have hlocks := hp.call_locks_compatible_of_unanimous hc hP hts hun hvote hy hup.1 hjb
    (hjtime ▸ hRT) hjtime.le (fun r hr B CV ho =>
      unanimous_next_optimistic_compatible hp hc hP hslot hu hun hgu hR hub hy ho
        ((hp.run.time_mono hr.le).trans hjb))
  have hnextlocks := hp.call_locks_compatible_of_unanimous hc hP hts hun hvote hy hto hnextb
    (hnexttime ▸ hRT) hnexttime.le (fun r hr B CV ho =>
      unanimous_next_optimistic_compatible hp hc hP hslot hu hun hgu hR hub hy ho
        ((hp.run.time_mono hr.le).trans hnextb))
  have hsl : sp.slot (tr.time j) = u + 1 := by
    rw [hjtime]
    apply SA.slot_of_mem sp (u + 1)
    · simp only [SA.SAParams.ts]; push_cast; linarith
    · simp only [SA.SAParams.ts]; push_cast; linarith
  obtain ⟨r, e, R, hr, ht, hPR⟩ := report_of_viable_unanimous_pool hp hy hup hto htoeq
    hframe (hnexttime.trans hjtime.symm) hjoined hPg hPv hpool hlocks
    (fun C hC => by
      obtain ⟨hCv, l, hl, he, _⟩ := hC
      exact hnextlocks C ⟨hCv.1, l, hl, he⟩)
    (by rw [hsl]; have := sp.two_le_k; omega) (by rw [hsl]; omega)
  exact ⟨r, e, R, hr, ht.trans hnexttime.le, hPR⟩

/-- Operational C2 discharges the unanimous-vote input of finite report coverage. -/
theorem report_cover_of_proposal {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P)
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hTb : sp.ts u + 6 * sp.Δ ≤ b) :
    (∀ y ∈ H, ∃ r e R, SA.ToFGAt tr.projAC y r e R ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P R) ∨
    (∃ x ∈ H, ∃ r e C, SA.ToFGAt tr.projAC x r e C ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h) := by
  have hun := hp.operational_unanimous hc hpH hdesignated hactual hslot hR
    (show sp.ts u ≤ b by linarith [sp.toParams.hΔ])
  exact report_cover_of_unanimous hp hc hP hslot hu hPg
    (fun y hy j e hv hjb hs => hun y hy j e hv hs hjb) hgu
    (hR.trans ((SA.ts_le_iff sp).2 (by push_cast; omega))) hTb

end UpTo

end CoveredEndpoint

end Consensus.Goldilocks.Refinement
end
