module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier

public section
namespace Consensus.Goldilocks.Refinement

variable {sp : SA.SAParams} {FGP : Type} {U : Set (SA.Blk sp.n FGP)}

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

/-- Endpoint head compatibility transports back along the monotone floor chain. -/
theorem intermediate_F_compatible_of_endpoint_head (hU : Coherent U)
    {Fq Fk H O : SA.Blk sp.n FGP} (hqk : Anc U Fq Fk) (hkH : Anc U Fk H)
    (hOH : Compatible U O H) : Compatible U Fq O := by
  rcases hOH with h | h
  · exact SA.anc_total hU (hqk.trans hkH) h
  · exact Or.inl (hqk.trans (hkH.trans h))

/-- Retention covers every ancestor of a high origin at later-label votes. -/
theorem covered_vote_suffix
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a : Time}
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    {x y : Fin sp.n} {r l k : Nat} {B C : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : Healing.HighOrigin tr H g x r l B) (hCB : Anc (tr.HonestBlocks H) C B)
    (hy : y ∈ H) {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y k ell e)
    (hl : l < e.msg.slot) :
    Compatible (tr.HonestBlocks H) ell.frame.F C ∧
      Compatible (tr.HonestBlocks H) ell.frame.fcRoot C ∧
      SA.VoteExtends (tr.HonestBlocks H) e.msg C ∧
      (C ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot) ∨
        Anc (tr.HonestBlocks H) C ell.frame.fcRoot) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  obtain ⟨hv, hvi⟩ := Healing.voteInv_iff.1 (Healing.retention_inv hp k).1
    x r l B ho y hy ell e hc hl
  have hroot : Compatible (tr.HonestBlocks H) ell.frame.fcRoot B := by
    rcases hvi with hvi | hvi
    · exact Or.inl (hvi.2.1.mono hΦU)
    · exact Or.inr hvi
  have hrootC : Compatible (tr.HonestBlocks H) ell.frame.fcRoot C := by
    rcases hroot with h | h
    · exact SA.anc_total hr.coherent h hCB
    · exact Or.inr (hCB.trans h)
  refine ⟨intermediate_F_compatible_of_endpoint_head hr.coherent
    (hΦ.F_anc_fcRoot.mono hΦU) (.refl) ?_, hrootC, ?_, ?_⟩
  · exact hrootC.symm
  · obtain ⟨Hd, hHd, he, hBH⟩ := hv
    exact ⟨Hd, hHd, he, hCB.trans hBH⟩
  rcases hvi with hvi | hvi
  swap
  · exact Or.inr (hCB.trans hvi)
  rcases hrootC with hfC | hCf
  swap
  · exact Or.inr hCf
  have hCt := SA.frame_mem_of_between sp hr.coherent hΦ hΦU hvi.1.1 hCB
    ((hΦ.F_anc_fcRoot.mono hΦU).trans hfC)
  have hCB' := SA.anc_tree_of_anc_U hr.coherent hΦ hΦU hCt hCB hvi.1.1
  obtain ⟨D, hD, hvD, hBD⟩ := hvi.2.2
  exact Or.inl ⟨SA.voterBlockTree_anc hr hy hc B hvi.1 C hCB',
    SA.anc_tree_of_anc_U hr.coherent hΦ hΦU hΦ.fcRoot_mem hfC hCt,
    D, hD, hvD, hCB'.trans hBD⟩

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

/-- At an actual call, compatibility with each actual write candidate suffices. -/
theorem effective_record_call_of_compatible
    {ro : SA.ReplayOrder sp FGP} {H : Set (Fin sp.n)} {tr : SA.SATrace sp FGP ro}
    (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ell : ACLabel (SA.goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y k ell) {O : SA.Blk sp.n FGP}
    (hO : Anc U O ((SA.lookup ell.frame (tr.state y k).latestConfirmed).getD ell.frame.F))
    (hnew : ∀ D s CV, SA.ResultAt tr y k s D CV ∨ SA.OptimisticLockAt tr y k s D CV →
      Compatible U O D) :
    Anc U O ((SA.lookup ell.frame (tr.post k).latestConfirmed).getD ell.frame.F) := by
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc
  exact effective_record_writes_of_compatible hr.coherent hΦ hΦU (Compose.call_writes hr hy hc)
    (fun D ⟨s, CV, h⟩ => hnew D s CV h) hO

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

/-- The conditional ready update flushes every non-descendant record. The post-state
is read in the actual call frame; frame evolution is handled by the separate adapter. -/
theorem ready_update_effective_record
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a : Time}
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.ReadyProposal tr H proposer p k u P)
    (hR : Healing.drainTime sp a ≤ sp.ts u) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y j u ell) (hPt : P ∈ ell.frame.tree)
    (hnext : ∀ r < j, ∀ B CV, SA.OptimisticLockAt tr.projAC y r (u + 1) B CV →
      Compatible (tr.HonestBlocks H) B P) :
    Anc (tr.HonestBlocks H) P
      ((SA.lookup ell.frame (tr.projAC.post j).latestConfirmed).getD ell.frame.F) ∧
      SA.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P := by
  have hS := Healing.healthy_base_of_reset_catch hp hc
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hS.run.localRun hy hu.1
  obtain ⟨-, -, hfast⟩ := Healing.ready_update_selection hp hc hP hR hgu hy hu hPt hnext
  obtain ⟨hconf, hnv, -, hpost⟩ := SA.first_update_post hS hgu
    (Healing.ready_unanimous hp hc hP hR) hy hu.1 hu.2.1 hu.2.2.1 hPt
    (Healing.ready_update_locks_compatible hp hc hP hR hgu hy hu hnext)
  refine ⟨?_, hfast⟩
  rw [hpost]
  unfold SA.updateConfirmation
  simp only [hconf]
  rw [ite_eq_right hnv]
  exact (effective_record_update_slot_growth (sp := sp) hΦ hPt).1.mono hΦU

end Consensus.Goldilocks.Refinement
end
