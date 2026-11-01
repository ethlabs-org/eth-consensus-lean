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

-- Whole-run consumers and their finite-horizon counterparts share this endpoint layer.
set_option linter.style.longFile 2100

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

/-- A covering live lock protects the prefix from regular writes through the actual
non-veto guard. Optimistic checks retain their separate compatibility obligation. -/
theorem effective_record_call_of_covering_live_lock
    {ro : SA.ReplayOrder sp FGP} {H : Set (Fin sp.n)} {tr : SA.SATrace sp FGP ro}
    (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ell : ACLabel (SA.goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y k ell) {O L : SA.Blk sp.n FGP}
    (hO : Anc U O ((SA.lookup ell.frame (tr.state y k).latestConfirmed).getD ell.frame.F))
    (hL : L ∈ SA.liveLockBlocks sp (tr.state y k).locks ell.frame (tr.time k))
    (hOL : Anc U O L)
    (hopt : ∀ D s CV, SA.OptimisticLockAt tr y k s D CV → Compatible U O D) :
    Anc U O ((SA.lookup ell.frame (tr.post k).latestConfirmed).getD ell.frame.F) := by
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc
  apply effective_record_writes_of_compatible hr.coherent hΦ hΦU
    (Compose.call_writes_guarded hr hy hc) _ hO
  rintro D ⟨s, CV, ⟨_, hnv⟩ | hop⟩
  · have hDL : Compatible ell.frame.tree D L := by
      by_contra hn
      exact hnv ⟨L, hL, hn⟩
    rcases hDL with h | h
    · exact SA.anc_total hr.coherent hOL (h.mono hΦU)
    · exact Or.inl (hOL.trans (h.mono hΦU))
  · exact hopt D s CV hop

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

/-- A raw result lies below a unanimous head when its pool has enough participants.
No fast test or absence of veto is required. -/
theorem raw_result_below_unanimous
    {ro : SA.ReplayOrder sp FGP} {H : Set (Fin sp.n)} {tr : SA.SATrace sp FGP ro}
    {proposer : Nat → Fin sp.n} (hr : SA.ACRun proposer tr H U)
    {x : Fin sp.n} (hx : x ∈ H) {r l : Nat} {C P : SA.Blk sp.n FGP}
    {CV : Set (SA.Vote sp.n)} (hres : SA.ResultAt tr x r l C CV)
    (hparticipants : 2 * Hᶜ.ncard ≤ (SA.voters {v | v ∈ (tr.state x r).pool l}).ncard)
    (hP : P ∈ U)
    (hvotes : ∀ z ∈ H, ∀ q e, SA.VoteAt tr z q e → e.msg.slot = l → e.msg.head = P.root) :
    Anc U C P := by
  obtain ⟨z, hz, q, -, e, hv, -, hs, Hd, hHd, he, hCH⟩ :=
    SA.result_honest_supporter_of_participants sp hr hx hres (B := C) .refl hparticipants
  have : Hd = P := hr.localRun.coherent.1 hHd hP (he.trans (hvotes z hz q e hv hs))
  exact this ▸ hCH

/-- Conditional later-label transfer compares the raw result with the prefix extended
by that same honest counted vote. It does not orient the result below the prefix. -/
theorem raw_result_compatible_of_votes
    {ro : SA.ReplayOrder sp FGP} {H : Set (Fin sp.n)} {tr : SA.SATrace sp FGP ro}
    {proposer : Nat → Fin sp.n} (hr : SA.ACRun proposer tr H U)
    {x : Fin sp.n} (hx : x ∈ H) {r l : Nat} {C P : SA.Blk sp.n FGP}
    {CV : Set (SA.Vote sp.n)} (hres : SA.ResultAt tr x r l C CV)
    (hparticipants : 2 * Hᶜ.ncard ≤ (SA.voters {v | v ∈ (tr.state x r).pool l}).ncard)
    (hvotes : ∀ z ∈ H, ∀ q e, SA.VoteAt tr z q e → e.msg.slot = l → SA.VoteExtends U e.msg P) :
    Compatible U C P := by
  obtain ⟨z, hz, q, -, e, hv, -, hs, Hd, hHd, he, hCH⟩ :=
    SA.result_honest_supporter_of_participants sp hr hx hres (B := C) .refl hparticipants
  obtain ⟨Hp, hHp, hep, hPH⟩ := hvotes z hz q e hv hs
  obtain rfl : Hp = Hd := hr.localRun.coherent.1 hHp hHd (hep.trans he.symm)
  exact SA.anc_total hr.localRun.coherent hCH hPH

/-- Healthy late updates need no separately supplied participant bound. -/
theorem raw_result_compatible_of_healthy_votes
    {ro : SA.ReplayOrder sp FGP} {H : Set (Fin sp.n)} {tr : SA.SATrace sp FGP ro}
    {proposer : Nat → Fin sp.n} {g : Time} (hS : SA.HealthyBase tr H U proposer g)
    {x : Fin sp.n} (hx : x ∈ H) {r l : Nat} {C P : SA.Blk sp.n FGP}
    {CV : Set (SA.Vote sp.n)} (hres : SA.ResultAt tr x r l C CV)
    (hgl : SA.gbar g + 4 * sp.Δ ≤ sp.ts l)
    (hvotes : ∀ z ∈ H, ∀ q e, SA.VoteAt tr z q e → e.msg.slot = l → SA.VoteExtends U e.msg P) :
    Compatible U C P := by
  obtain ⟨ell, hu, hC, -⟩ := hres
  obtain ⟨z, hz, q, e, hv, hs, Hd, hHd, he, hCH⟩ := SA.result_extended hS hgl hx hu.1
    (by rw [hu.2.2.1]; linarith [sp.toParams.hΔ]) hC
  obtain ⟨Hp, hHp, hep, hPH⟩ := hvotes z hz q e hv hs
  obtain rfl : Hp = Hd := hS.run.localRun.coherent.1 hHp hHd (hep.trans he.symm)
  exact SA.anc_total hS.run.localRun.coherent hCH hPH

/-- A raw result of the ready proposal's own label is below that proposal, including
vetoed or sub-fast results. Later labels require their own vote-extension premise. -/
theorem raw_result_below_ready
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a : Time}
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.ReadyProposal tr H proposer p k u P)
    (hR : Healing.drainTime sp a ≤ sp.ts u) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {x : Fin sp.n} (hx : x ∈ H) {r : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (hres : SA.ResultAt tr.projAC x r u C CV) :
    Anc (tr.HonestBlocks H) C P := by
  have hS := Healing.healthy_base_of_reset_catch hp hc
  obtain ⟨ell, hu, hC, -⟩ := hres
  obtain ⟨z, hz, q, e, hv, hs, Hd, hHd, he, hCH⟩ := SA.result_extended hS hgu hx hu.1
    (by rw [hu.2.2.1]; linarith [sp.toParams.hΔ]) hC
  obtain ⟨-, -, _, _, _, _, _, _, _, _, _, _, _, ja, _, hacc, _⟩ :=
    Healing.honestProposalRun_of_ready hp.run hp.noColl hP
  rw [← hP.2.1] at hacc
  obtain ⟨ellp, hcp, hblock⟩ := hacc
  have hPm := (SA.accept_new sp hS.run.localRun hP.1 ⟨ellp, hcp, hblock⟩).1 ellp hcp
  have hPU := (SA.frameIn_of_callAt hS.run.localRun hP.1 hcp).2 hPm
  have : Hd = P := hS.run.localRun.coherent.1 hHd hPU
    (he.trans (Healing.ready_unanimous hp hc hP hR z hz q e hv hs))
  exact this ▸ hCH

/-- When the floor has passed a covering high origin, its crossing supplies a frozen
viable descendant of the target. Mere high state height is not an origin premise. -/
theorem covered_target_frozen_witness_of_high_floor
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a : Time}
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    {x y : Fin sp.n} {i j k : Nat} {B C : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : Healing.HighOrigin tr H g x i j B) (hy : y ∈ H)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) (hj : j < e.msg.slot)
    (hCB : Anc (tr.HonestBlocks H) C B)
    (hFC : Anc (tr.HonestBlocks H) ell.frame.F C)
    (hpair : ∀ v r l O, r < k → Healing.HighOrigin tr H g v r l O →
      ∀ v' r' l' O', r' < k → Healing.HighOrigin tr H g v' r' l' O' →
      Compatible (tr.HonestBlocks H) O O')
    (hcomp : ∀ v r l O, r < k → Healing.HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocks H) B O)
    (hfloor : ((tr.state x i).fg.σ B.root).h < (tr.state y k).fg.headHeightFloor) :
    ∃ D ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
      Anc (tr.HonestBlocks H) C D ∧ (tr.state y k).fg.IsViable D := by
  obtain ⟨v, r, l, O, E, -, hO, hl, hE, hEO, hBO, hf⟩ :=
    Healing.high_floor_source_core hp ho hy hc hj hpair hcomp hfloor
  exact Healing.raw_target_frozen_witness hp hO hy hc hl hFC (hCB.trans hBO) hE hEO hf

/-- An actual earlier-label high cover gives a floor-reaching frozen witness or
root coverage. No claim is made for a merely high-height held block. -/
theorem covered_target_frozen_witness
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a : Time}
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    {x y : Fin sp.n} {i j k : Nat} {B C : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : Healing.HighOrigin tr H g x i j B) (hCB : Anc (tr.HonestBlocks H) C B)
    (hy : y ∈ H) {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y k ell e)
    (hj : j < e.msg.slot) :
    (∃ D ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
      Anc (tr.HonestBlocks H) C D ∧ (tr.state y k).fg.IsViable D) ∨
      Anc (tr.HonestBlocks H) C ell.frame.fcRoot := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hΦU := (SA.frameIn_of_callAt hr hy hc.1).2
  rcases (covered_vote_suffix hp ho hCB hy hc hj).2.2.2 with hv | hf
  · obtain ⟨D, hD, hvD, hCD⟩ := hv.2.2
    rw [Compose.frame_of_projAC hp.run hy hc.1] at hvD
    exact Or.inl ⟨D, hD, hCD.mono hΦU, hvD.2.2.2⟩
  · exact Or.inr hf

/-- Normalizing a held lock preserves any ancestor that remains a candidate. -/
theorem anc_viableAncestor_of_candidate {n : Nat} {FGP : Type} {Φ : SA.Frm n FGP}
    (hΦ : FrameOK Φ) {O B : SA.Blk n FGP} (hB : B ∈ Φ.tree)
    (hOB : Φ.Anc O B) (hO : Φ.AncestorCandidate O) :
    Φ.Anc O (Φ.viableAncestor B) :=
  (SA.viableAncestor_spec hΦ hB).2.2 O hOB hO

/-- An actual stored fast lock covering a high held prefix supplies an earlier high
origin. The source label is exactly the stored lock's label; no liveness is needed. -/
theorem high_cover_of_stored_fast_lock
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a : Time}
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {l : SA.Lock}
    (hl : l ∈ (tr.state y k).ac.locks) (hf : l.fast = true)
    {O L : SA.Blk sp.n (List (FG.Att sp.n))}
    (hL : L ∈ (tr.state y k).fg.tree)
    (hrL : L.root = l.block) (hOL : Anc (tr.HonestBlocks H) O L)
    (hh : Healing.HZ tr H g + 1 ≤ ((tr.state y k).fg.σ O.root).h) :
    ∃ r < k, ∃ B, Healing.HighOrigin tr H g y r l.slot B ∧
      Anc (tr.HonestBlocks H) O B := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hl' : l ∈ (tr.projAC.state y k).locks := by
    rw [Compose.projAC_state hp.run.toLocalRun hy]; exact hl
  obtain ⟨r, hrk, CV, ell, D, hc, hfl, L', hL', hrL', hLB⟩ :=
    Healing.stored_fast_lock_provenance hr hy k l hl' hf
  obtain rfl : L' = L := hr.coherent.1 hL' ⟨y, hy, k, hL⟩ (hrL'.trans hrL.symm)
  obtain ⟨ell', hc', hD⟩ := Healing.fastLock_mem hfl
  have he : ell' = ell := Option.some.inj (hc'.2.symm.trans hc.2)
  rw [he] at hD
  have hBt := (SA.viableAncestor_anc (SA.frameIn_of_callAt hr hy hc).1 hD).1
  have hBr := Healing.frame_tree_subset hp hy hc hBt
  have hBk := Compose.tree_mono hp.run.toLocalRun hy hrk.le hBr
  have hOB := hOL.trans hLB
  have hhB := Healing.σ_h_le_of_anc (Compose.fg_reachable hp.run.toLocalRun hy k)
    (Healing.anc_tree_of_anc hp hy hOB hBk)
  have hhBr : Healing.HZ tr H g + 1 ≤
      ((tr.state y r).fg.σ (ell.frame.viableAncestor D).root).h := by
    rw [← Healing.σ_eq_run hp hy hy hBk hBr]
    exact hh.trans hhB
  exact ⟨r, hrk, ell.frame.viableAncestor D, ⟨hy,
    Healing.joinedAt_of_fastLockAt hp.run hp.noColl hy hfl,
    ⟨CV, ell, D, hc, hfl, rfl⟩, hhBr⟩, hOB⟩

/-- A real high report supplies an earlier high cover of every prefix below it.
The report's existence is a premise, not a consequence of heldness. -/
theorem high_cover_of_report
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a : Time}
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {O R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hrep : SA.ToFGAt tr.projAC y k ell R)
    (hOR : Anc (tr.HonestBlocks H) O R)
    (hh : Healing.HZ tr H g + 1 ≤ ((tr.state y k).fg.σ O.root).h) :
    ∃ r < k, ∃ l B, Healing.HighOrigin tr H g y r l B ∧ Anc (tr.HonestBlocks H) O B := by
  have hhR := hh.trans (Healing.σ_h_le_of_anc (Compose.fg_reachable hp.run.toLocalRun hy k)
    (Healing.anc_tree_of_anc hp hy hOR (Healing.toFG_mem_tree hp.run hy hrep)))
  obtain ⟨r, hr, l, B, ho, hRB⟩ := Healing.high_report_origin hp hy hrep hhR
  exact ⟨r, hr, l, B, ho, hOR.trans hRB⟩

/-- A prefix with fewer than half opponents lies below the unlock target. -/
theorem anc_unlockTarget_of_opponents
    {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) {O B : SA.Blk sp.n FGP}
    (hO : O ∈ Φ.tree) (_hB : B ∈ Φ.tree) (hOB : Φ.Anc O B)
    (V : SA.View sp.n) (s : Int)
    (hopp : 2 * (SA.opponents sp Φ V s O).ncard < sp.n) :
    Φ.Anc O (SA.unlockTarget sp Φ V s B) := by
  obtain ⟨D, hD⟩ := SA.exists_deepest hΦ
    (S := {X | X ∈ Φ.tree ∧ Φ.Anc X B ∧ 2 * (SA.opponents sp Φ V s X).ncard < sp.n})
    (fun X h => h.1) ⟨O, hO, hOB, hopp⟩
  unfold SA.unlockTarget
  rw [hD]
  exact SA.anc_deepest hΦ (fun X h => h.1)
    (fun X hX Y hY => SA.anc_total hΦ.coherent hX.2.1 hY.2.1) hD O ⟨hO, hOB, hopp⟩

/-- Unlock preserves a prefix of an already-live normalized lock when its label is
not challenged, or the prefix has fewer than half opponents. -/
theorem unlock_preserves_prefix
    {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) {L : Set SA.Lock} {t : Time}
    {V : SA.View sp.n} {s : Int} {l : SA.Lock} {O B : SA.Blk sp.n FGP}
    (hl : l ∈ SA.liveLocks sp L Φ t) (hB : B ∈ Φ.tree) (hr : B.root = l.block)
    (hO : O ∈ Φ.tree) (hOB : Φ.Anc O B)
    (hguard : s ≤ (l.slot : Int) ∨ 2 * (SA.opponents sp Φ V s O).ncard < sp.n) :
    ∃ l' ∈ SA.unlock sp L Φ t s V, ∃ B' ∈ Φ.tree,
      B'.root = l'.block ∧ Φ.Anc O B' ∧ l'.slot = l.slot ∧ l'.fast = l.fast := by
  classical
  by_cases hs : (l.slot : Int) < s
  · have hopp := hguard.resolve_left (not_le.mpr hs)
    obtain ⟨hT, -⟩ := SA.unlockTarget_anc sp hΦ V s hB
    refine ⟨⟨(SA.unlockTarget sp Φ V s B).root, l.slot, l.fast⟩,
      ⟨l, hl, B, hB, hr, by simp only [hs, ↓reduceIte]⟩,
      SA.unlockTarget sp Φ V s B, hT, rfl, ?_, rfl, rfl⟩
    exact anc_unlockTarget_of_opponents hΦ hO hB hOB V s hopp
  · exact ⟨l, ⟨l, hl, B, hB, hr, by simp only [hs, ↓reduceIte]⟩,
      B, hB, hr, hOB, rfl, rfl⟩

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

/-- Fixed-record reads preserve the prefix with a fresh head certificate, even if
the old lock expired. This supplies no certificate from an earlier view or clock. -/
theorem exposed_prefix_preserved_at_clock (hU : Coherent U)
    {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {A : SA.SAState sp.n} {O : SA.Blk sp.n FGP} {t : Time}
    (hE : Anc U O ((SA.lookup Φ A.latestConfirmed).getD Φ.F))
    (hhead : Anc U O Φ.F ∨ (O ∈ Φ.tree ∧
      Compatible Φ.tree (SA.getAnchor sp A Φ t) O ∧
      (Φ.Anc O (SA.getAnchor sp A Φ t) ∨ (O ∈ Φ.viableTree Φ.tree ∧
        (SA.voters (SA.latestView sp A Φ t).1.votes).ncard <
          2 * (SA.supporters Φ (SA.latestView sp A Φ t).1
            (SA.latestView sp A Φ t).2 O).ncard)))) :
    Anc U O (SA.acConfirmed sp A Φ t) :=
  (exposed_prefix_preserved_of_record_head hU hΦ hΦU).mpr
    ⟨hE, anc_acHead_of_current_certificate hΦ hΦU hhead⟩

section CoveredPrefix

variable {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a : Time}

/-- An actual earlier-label high cover makes later raw and optimistic candidates comparable
with the exposed prefix. This gives compatibility, not a direction or a read-head certificate. -/
theorem covered_candidates_compatible
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    {x : Fin sp.n} {r b : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : Healing.HighOrigin tr H g x r b B) (hOB : Anc (tr.HonestBlocks H) O B)
    {y : Fin sp.n} (hy : y ∈ H) {k s : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (hbs : b < s)
    (hD : (SA.ResultAt tr.projAC y k s D CV ∧ SA.gbar g + 4 * sp.Δ ≤ sp.ts s ∧
        Healing.CatchRun tr H g (2 * sp.Δ)) ∨ SA.OptimisticLockAt tr.projAC y k s D CV) :
    Compatible (tr.HonestBlocks H) D O := by
  have hvotes : ∀ z ∈ H, ∀ q e, SA.VoteAt tr.projAC z q e → e.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) e.msg O := by
    intro z hz q e hv hs
    obtain ⟨ell, hcast⟩ := hv
    exact (covered_vote_suffix hp ho hOB hz hcast (hs ▸ hbs)).2.2.1
  rcases hD with ⟨hres, hlate, hc⟩ | hopt
  · exact raw_result_compatible_of_healthy_votes
      (Healing.healthy_base_of_reset_catch hp hc) hy hres hlate hvotes
  · have hf : 2 * Hᶜ.ncard < sp.n := by
      have := hp.healthy.2.2
      have := Fin.pos y
      have hn : sp.n = sp.toParams.n := rfl
      omega
    exact SA.optimisticLock_compatible
      (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl) hf hy hopt hvotes

/-- Same-label candidates compare with an actual high cover using healthy same-slot
compatibility. Regular results require the stronger late-label bound. -/
theorem covered_equal_candidates_compatible
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} {r b : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : Healing.HighOrigin tr H g x r b B) (hOB : Anc (tr.HonestBlocks H) O B)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)}
    (hD : (SA.ResultAt tr.projAC y k b D CV ∧ SA.gbar g + 4 * sp.Δ ≤ sp.ts b) ∨
      (SA.OptimisticLockAt tr.projAC y k b D CV ∧ SA.gbar g ≤ sp.ts b)) :
    Compatible (tr.HonestBlocks H) O D := by
  have hS := Healing.healthy_base_of_reset_catch hp hc
  have hU := hS.run.localRun.coherent
  obtain ⟨ell, D₀, CV₀, hcall, hfl, _, _, _, hBD, _⟩ := Healing.highOrigin_mem hp ho
  have hOD := hOB.trans (hBD.mono (SA.frameIn_of_callAt hS.run.localRun ho.1 hcall).2)
  rcases hD with ⟨hres, hlate⟩ | ⟨hopt, hlate⟩
  · rcases hfl with ⟨ell₀, C, hupd, hconf, _, hsel, _⟩ | hopt
    · have hDC := (SA.deepest_mem hsel).1.1.2.2
      have hOC := hOD.trans (hDC.mono (SA.frameIn_of_callAt hS.run.localRun ho.1 hupd.1).2)
      have hcmp := SA.result_result_compatible hS hy hres ho.1
        (show SA.ResultAt tr.projAC x r b C _ from ⟨ell₀, hupd, hconf, rfl⟩) hlate
      rcases hcmp with h | h
      · exact SA.anc_total hU hOC h
      · exact Or.inl (hOC.trans h)
    · rcases SA.result_optimistic_compatible hS hy hres ho.1 hopt hlate with h | h
      · exact SA.anc_total hU hOD h
      · exact Or.inl (hOD.trans h)
  · rcases SA.fastLock_fastLock_compatible hS ho.1 hfl hy (Or.inr hopt) hlate with h | h
    · exact Or.inl (hOD.trans h)
    · exact SA.anc_total hU hOD h

/-- A stored fast lock covering a high exposed prefix supplies both historic vote geometry
and later candidate compatibility. Only labels are ordered: the queried cast may precede
the cut at which the stored lock is observed. Liveness of that lock is not required. -/
theorem stored_fast_lock_covers_exposed_prefix
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    {x : Fin sp.n} (hx : x ∈ H) {k : Nat} {lock : SA.Lock}
    (hl : lock ∈ (tr.state x k).ac.locks) (hf : lock.fast = true)
    {O L : SA.Blk sp.n (List (FG.Att sp.n))} (hL : L ∈ (tr.state x k).fg.tree)
    (hrL : L.root = lock.block) (hOL : Anc (tr.HonestBlocks H) O L)
    (hh : Healing.HZ tr H g + 1 ≤ ((tr.state x k).fg.σ O.root).h) :
    (∀ y ∈ H, ∀ q ell v, SA.CastAt tr.projAC y q ell v → lock.slot < v.msg.slot →
      Compatible (tr.HonestBlocks H) ell.frame.F O ∧
      Compatible (tr.HonestBlocks H) ell.frame.fcRoot O ∧
      SA.VoteExtends (tr.HonestBlocks H) v.msg O ∧
      (O ∈ ell.frame.viableTree (SA.voterBlockTree sp v.readPoint ell.frame v.msg.slot) ∨
        Anc (tr.HonestBlocks H) O ell.frame.fcRoot)) ∧
    (∀ y ∈ H, ∀ q s D CV, lock.slot < s →
      ((SA.ResultAt tr.projAC y q s D CV ∧ SA.gbar g + 4 * sp.Δ ≤ sp.ts s ∧
        Healing.CatchRun tr H g (2 * sp.Δ)) ∨ SA.OptimisticLockAt tr.projAC y q s D CV) →
      Compatible (tr.HonestBlocks H) D O) := by
  obtain ⟨r, -, B, ho, hOB⟩ := high_cover_of_stored_fast_lock hp hx hl hf hL hrL hOL hh
  constructor
  · intro y hy q ell v hv hs
    exact covered_vote_suffix hp ho hOB hy hv hs
  · intro y hy q s D CV hs hD
    exact covered_candidates_compatible hp ho hOB hy hs hD

end CoveredPrefix

/-- The literal ready-reader endpoint, conditional only on cross-read input compatibility
and preservation of the earlier output in both inputs of each later read. The producer
scopes match `ReadySafeOn`, including boundary cuts and the actual read clocks. -/
theorem readySafeOn_of_read_producers
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (c t₀ t₁ : Time)
    (hagree : ∀ y z i j t t',
      Regimes.ReadPoint tr i t → Regimes.ReadPoint tr j t' →
      Regimes.Boundary tr y i → Regimes.Boundary tr z j →
      t₀ ≤ t → t ≤ t₁ → t₀ ≤ t' → t' ≤ t₁ →
      Regimes.ReadyAt tr H c y t → Regimes.ReadyAt tr H c z t' →
      let Φ := Node.frame (tr.state y i)
      let Ψ := Node.frame (tr.state z j)
      let E := (SA.lookup Φ (tr.state y i).ac.latestConfirmed).getD Φ.F
      let E' := (SA.lookup Ψ (tr.state z j).ac.latestConfirmed).getD Ψ.F
      let head := SA.acHead sp (tr.state y i).ac Φ t
      let head' := SA.acHead sp (tr.state z j).ac Ψ t'
      ∃ X Y, (X = E ∨ X = head) ∧ (Y = E' ∨ Y = head') ∧
        Compatible (tr.HonestBlocks H) X Y)
    (hmono : ∀ y i j t t',
      Regimes.ReadPoint tr i t → Regimes.ReadPoint tr j t' →
      Regimes.Boundary tr y i → Regimes.Boundary tr y j →
      i ≤ j → t ≤ t' → t₀ ≤ t → t' ≤ t₁ →
      Regimes.ReadyAt tr H c y t → Regimes.ReadyAt tr H c y t' →
      let Ψ := Node.frame (tr.state y j)
      Anc (tr.HonestBlocks H) (Regimes.readAfter tr y i t)
        ((SA.lookup Ψ (tr.state y j).ac.latestConfirmed).getD Ψ.F) ∧
      Anc (tr.HonestBlocks H) (Regimes.readAfter tr y i t)
        (SA.acHead sp (tr.state y j).ac Ψ t')) :
    Regimes.ReadySafeOn tr H c t₀ t₁ := by
  have hU := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun.coherent
  have hsub : ∀ y ∈ H, ∀ i, (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocks H :=
    fun y hy i _ hX => ⟨y, hy, i, hX.1⟩
  have hinputs : ∀ y ∈ H, ∀ i t,
      Anc (tr.HonestBlocks H) (Regimes.readAfter tr y i t)
        ((SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed).getD
          (Node.frame (tr.state y i)).F) ∧
      Anc (tr.HonestBlocks H) (Regimes.readAfter tr y i t)
        (SA.acHead sp (tr.state y i).ac (Node.frame (tr.state y i)) t) := by
    intro y hy i t
    exact (exposed_prefix_preserved_of_record_head hU
      (Compose.frameOK_state hrun.toLocalRun hy i) (hsub y hy i)).mp .refl
  constructor
  · intro y z i j t t' hi hj hbi hbj ht ht₁ ht' ht₁' hy hz
    obtain ⟨X, Y, hX, hY, hXY⟩ := hagree y z i j t t' hi hj hbi hbj ht ht₁ ht' ht₁' hy hz
    have hOX : Anc (tr.HonestBlocks H) (Regimes.readAfter tr y i t) X := by
      rcases hX with rfl | rfl
      · exact (hinputs y hy.1 i t).1
      · exact (hinputs y hy.1 i t).2
    have hOY : Anc (tr.HonestBlocks H) (Regimes.readAfter tr z j t') Y := by
      rcases hY with rfl | rfl
      · exact (hinputs z hz.1 j t').1
      · exact (hinputs z hz.1 j t').2
    rcases hXY with h | h
    · exact SA.anc_total hU (hOX.trans h) hOY
    · exact SA.anc_total hU hOX (hOY.trans h)
  · intro y i j t t' hi hj hbi hbj hij htt ht ht₁ hy hy'
    exact (exposed_prefix_preserved_of_record_head hU
      (Compose.frameOK_state hrun.toLocalRun hy'.1 j) (hsub y hy'.1 j)).mpr
        (hmono y i j t t' hi hj hbi hbj hij htt ht ht₁ hy hy')

section CoveredEndpoint

variable {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a : Time}

/-- Covered outputs agree directly; their effective records and heads need not agree. -/
theorem covered_outputs_compatible (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    {O O' B B' : SA.Blk sp.n (List (FG.Att sp.n))} {x x' : Fin sp.n} {r r' b b' : Nat}
    (ho : Healing.HighOrigin tr H g x r b B) (ho' : Healing.HighOrigin tr H g x' r' b' B')
    (hOB : Anc (tr.HonestBlocks H) O B) (hOB' : Anc (tr.HonestBlocks H) O' B') :
    Compatible (tr.HonestBlocks H) O O' := by
  have hU :=
    (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun.coherent
  have hBB : Compatible (tr.HonestBlocks H) B B' := by
    rcases le_total b b' with h | h
    · exact Healing.origins_compatible hp ho ho' h fun k _ => (Healing.retention_inv hp k).1
    · exact (Healing.origins_compatible hp ho' ho h
        fun k _ => (Healing.retention_inv hp k).1).symm
  rcases hBB with h | h
  · exact SA.anc_total hU (hOB.trans h) hOB'
  · exact SA.anc_total hU hOB (hOB'.trans h)

/-- Explicit interval producer contract for one earlier output. Each transition either
decomposes into guarded writes in the old frame followed by a compatible floor change,
or supplies a replacement effective record extending the prefix (including restarts).
The write predicate must include every actual write; qualifying high-cover candidates
can discharge its compatibility using `covered_candidates_compatible`. No such provenance,
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

/-- Endpoint variant with direct output agreement and an explicit interval producer.
Head certificates are required at the actual later clock, not inherited from an old vote. -/
theorem readySafeOn_of_output_agreement_interval
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (c t₀ t₁ : Time)
    (hagree : ∀ y z i j t t',
      Regimes.ReadPoint tr i t → Regimes.ReadPoint tr j t' →
      Regimes.Boundary tr y i → Regimes.Boundary tr z j →
      t₀ ≤ t → t ≤ t₁ → t₀ ≤ t' → t' ≤ t₁ →
      Regimes.ReadyAt tr H c y t → Regimes.ReadyAt tr H c z t' →
      Compatible (tr.HonestBlocks H) (Regimes.readAfter tr y i t) (Regimes.readAfter tr z j t'))
    (hpreserve : ∀ y i j t t',
      Regimes.ReadPoint tr i t → Regimes.ReadPoint tr j t' →
      Regimes.Boundary tr y i → Regimes.Boundary tr y j →
      i ≤ j → t ≤ t' → t₀ ≤ t → t' ≤ t₁ →
      Regimes.ReadyAt tr H c y t → Regimes.ReadyAt tr H c y t' →
      EffectiveRecordInterval tr H y i j (Regimes.readAfter tr y i t) ∧
      Anc (tr.HonestBlocks H) (Regimes.readAfter tr y i t)
        (SA.acHead sp (tr.state y j).ac (Node.frame (tr.state y j)) t')) :
    Regimes.ReadySafeOn tr H c t₀ t₁ := by
  refine ⟨hagree, ?_⟩
  intro y i j t t' hi hj hbi hbj hij htt ht ht₁ hy hy'
  obtain ⟨hint, hhead⟩ := hpreserve y i j t t' hi hj hbi hbj hij htt ht ht₁ hy hy'
  have hU := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun.coherent
  have hsub : ∀ q, (Node.frame (tr.state y q)).tree ⊆ tr.HonestBlocks H :=
    fun q _ hX => ⟨y, hy.1, q, hX.1⟩
  have hstart := (exposed_prefix_preserved_of_record_head hU
    (Compose.frameOK_state hrun.toLocalRun hy.1 i) (hsub i)
    (O := Regimes.readAfter tr y i t) (A := (tr.state y i).ac) (t := t)).mp .refl
  exact (exposed_prefix_preserved_of_record_head hU
    (Compose.frameOK_state hrun.toLocalRun hy'.1 j) (hsub j)).mpr
      ⟨effective_record_of_interval hrun hnc hy.1 hij hint hstart.1, hhead⟩

/-- Actual high covers discharge agreement; the interval and read-head producers remain
explicit. Stored fast locks may supply each cover via `high_cover_of_stored_fast_lock`. -/
theorem readySafeOn_of_high_covers_interval
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a) (c t₀ t₁ : Time)
    (hcover : ∀ y i t, Regimes.ReadPoint tr i t → Regimes.Boundary tr y i →
      t₀ ≤ t → t ≤ t₁ → Regimes.ReadyAt tr H c y t →
      ∃ x r b B, Healing.HighOrigin tr H g x r b B ∧
        Anc (tr.HonestBlocks H) (Regimes.readAfter tr y i t) B)
    (hpreserve : ∀ y i j t t',
      Regimes.ReadPoint tr i t → Regimes.ReadPoint tr j t' →
      Regimes.Boundary tr y i → Regimes.Boundary tr y j →
      i ≤ j → t ≤ t' → t₀ ≤ t → t' ≤ t₁ →
      Regimes.ReadyAt tr H c y t → Regimes.ReadyAt tr H c y t' →
      EffectiveRecordInterval tr H y i j (Regimes.readAfter tr y i t) ∧
      Anc (tr.HonestBlocks H) (Regimes.readAfter tr y i t)
        (SA.acHead sp (tr.state y j).ac (Node.frame (tr.state y j)) t')) :
    Regimes.ReadySafeOn tr H c t₀ t₁ := by
  refine readySafeOn_of_output_agreement_interval hp.run hp.noColl c t₀ t₁ ?_ hpreserve
  intro y z i j t t' hi hj hbi hbj ht ht₁ ht' ht₁' hy hz
  obtain ⟨x, r, b, B, ho, hOB⟩ := hcover y i t hi hbi ht ht₁ hy
  obtain ⟨x', r', b', B', ho', hOB'⟩ := hcover z j t' hj hbj ht' ht₁' hz
  exact covered_outputs_compatible hp ho ho' hOB hOB'

/-- Actual AC calls, including restart, supply guarded record transitions. A high cover
discharges strictly later candidates; equal/earlier labels and unserved raw windows remain
explicit compatibility obligations. Activated cache retention supplies the new floor. -/
theorem effectiveRecordInterval_of_high_cover
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    {x y : Fin sp.n} {r b i j : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : Healing.HighOrigin tr H g x r b B) (hOB : Anc (tr.HonestBlocks H) O B)
    (hy : y ∈ H)
    (hcandidates : ∀ q, i ≤ q → q < j → ∀ D s CV,
      SA.ResultAt tr.projAC y q s D CV ∨ SA.OptimisticLockAt tr.projAC y q s D CV →
      Compatible (tr.HonestBlocks H) O D ∨
        (b < s ∧ (SA.ResultAt tr.projAC y q s D CV →
          SA.gbar g + 4 * sp.Δ ≤ sp.ts s ∧ Healing.CatchRun tr H g (2 * sp.Δ))))
    (hframes : ∀ q, i ≤ q → q < j →
      Compatible (tr.HonestBlocks H) (tr.state y (q + 1)).fg.F O ∨
        (tr.IsCall y q ∧ a ≤ tr.time q ∧ (r ≤ q ∨ sp.ts (b + 1 : Nat) ≤ tr.time q))) :
    EffectiveRecordInterval tr H y i j O := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hst := Compose.projAC_state hp.run.toLocalRun hy
  refine ⟨fun q hiq hqj => Or.inl ?_⟩
  refine ⟨(fun D => ∃ s CV, SA.ResultAt tr.projAC y q s D CV ∨
    SA.OptimisticLockAt tr.projAC y q s D CV), ?_, ?_, ?_⟩
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
    rcases hcandidates q hiq hqj D s CV hD with h | ⟨hbs, hlate⟩
    · exact h
    apply Or.symm
    apply covered_candidates_compatible hp ho hOB hy hbs
    rcases hD with h | h
    · exact Or.inl ⟨h, hlate h⟩
    · exact Or.inr h
  · rcases hframes q hiq hqj with h | ⟨hcall, ha, hact⟩
    · exact h
    have hFB := (Healing.cacheInv_iff.mp (Healing.retention_inv hp q).2)
      y hy hcall ha x r b B ho hact |>.1
    obtain ⟨call, hcall⟩ := hcall
    rw [← tr.state_succ_of_call hcall] at hFB
    rcases hFB with h | h
    · exact SA.anc_total hac.localRun.coherent h hOB
    · exact Or.inr (hOB.trans h)

/-- Covered intervals admit equal-label candidates and need no frame activation premise.
Earlier-label candidates still require independent compatibility. -/
theorem effectiveRecordInterval_of_healthy_high_cover
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r b i j : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : Healing.HighOrigin tr H g x r b B) (hOB : Anc (tr.HonestBlocks H) O B)
    (hy : y ∈ H) (hb : SA.gbar g ≤ sp.ts b)
    (hcandidates : ∀ q, i ≤ q → q < j → ∀ D s CV,
      SA.ResultAt tr.projAC y q s D CV ∨ SA.OptimisticLockAt tr.projAC y q s D CV →
      Compatible (tr.HonestBlocks H) O D ∨
        (b ≤ s ∧ (SA.ResultAt tr.projAC y q s D CV →
          SA.gbar g + 4 * sp.Δ ≤ sp.ts s))) :
    EffectiveRecordInterval tr H y i j O := by
  apply effectiveRecordInterval_of_high_cover hp ho hOB hy
  · intro q hiq hqj D s CV hD
    rcases hcandidates q hiq hqj D s CV hD with h | ⟨hbs, hlate⟩
    · exact Or.inl h
    rcases lt_or_eq_of_le hbs with hlt | rfl
    · exact Or.inr ⟨hlt, fun hr => ⟨hlate hr, hc⟩⟩
    apply Or.inl
    apply covered_equal_candidates_compatible hp hc ho hOB hy
    rcases hD with h | h
    · exact Or.inl ⟨h, hlate h⟩
    · exact Or.inr ⟨h, hb⟩
  · intro q _ _
    apply Or.inl
    rcases Healing.finalized_compatible_high_origin_at_any_cut hp hy (c := q + 1) ho with h | h
    · exact SA.anc_total (Healing.honest_coherent hp) h hOB
    · exact Or.inr (hOB.trans h)

/-- An origin written during a unanimous slot is below its unanimous head. Older-label
origins use retention at an actual vote, even when that vote precedes the origin write. -/
theorem high_origin_in_unanimous_slot_below
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hun : Healing.Unanimous tr H u P)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {x : Fin sp.n} {r b : Nat} (ho : Healing.HighOrigin tr H g x r b B)
    (hlo : sp.ts u ≤ tr.time r) (hhi : tr.time r < sp.ts (u + 1 : Nat)) :
    Anc (tr.HonestBlocks H) B P := by
  have hS := Healing.healthy_base_of_reset_catch hp hc
  obtain ⟨ell, D, CV, hcall, hfl, _, _, _, hBD, _⟩ := Healing.highOrigin_mem hp ho
  have hPhi := (SA.frameIn_of_callAt hS.run.localRun ho.1 hcall).2
  have hbu : b ≤ u := by
    rcases hfl with ⟨ell, C, hu, _⟩ | ⟨ell, A, _, hs, _⟩
    · have ht : tr.time r = sp.ts b + 6 * sp.Δ := hu.2.2.1
      have hΔ := sp.toParams.hΔ
      simp only [SA.SAParams.ts] at hhi ht
      push_cast at hhi
      by_contra hn
      have hb : (u : Int) + 1 ≤ b := by omega
      nlinarith
    · have hs' : sp.slot (tr.time r) = b := hs
      rw [SA.slot_of_mem sp u hlo hhi] at hs'
      omega
  by_cases hbu' : b < u
  · obtain ⟨q, e, hv, hs⟩ := SA.honest_votes_in_slot hS hgu x ho.1
    obtain ⟨ellv, hcast⟩ := hv
    obtain ⟨Hd, hHd, he, hBH⟩ :=
      (covered_vote_suffix hp ho (.refl) ho.1 hcast (by omega)).2.2.1
    have heq : Hd = P := hS.run.localRun.coherent.1 hHd hP
      (he.trans (hun x ho.1 q e ⟨ellv, hcast⟩ hs))
    exact heq ▸ hBH
  have heq : b = u := by omega
  subst b
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have := hp.healthy.2.2
    have := Fin.pos x
    have hn : sp.n = sp.toParams.n := rfl
    omega
  obtain ⟨z, hz, q, e, hv, hs, Hd, hHd, he, hDH⟩ :=
    SA.fastLock_honest_vote hS.run hf ho.1 hfl
  have heq : Hd = P := hS.run.localRun.coherent.1 hHd hP (he.trans (hun z hz q e hv hs))
  exact (hBD.mono hPhi).trans (heq ▸ hDH)

/-- Extend the old-origin cutoff through the fresh unanimous slot. -/
theorem high_origins_before_next_slot_below
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hun : Healing.Unanimous tr H u P)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hold : ∀ x r b B, Healing.HighOrigin tr H g x r b B → tr.time r < sp.ts u →
      Anc (tr.HonestBlocks H) B P) :
    ∀ x r b B, Healing.HighOrigin tr H g x r b B → tr.time r < sp.ts (u + 1 : Nat) →
      Anc (tr.HonestBlocks H) B P := by
  intro x r b B ho ht
  by_cases hbefore : tr.time r < sp.ts u
  · exact hold x r b B ho hbefore
  · exact high_origin_in_unanimous_slot_below hp hc hP hun hgu ho (le_of_not_gt hbefore) ht

/-- Unanimity and the pre-slot origin bound admit the previous proposal to the next
vote's frozen viable tree. The receiver's own previous vote supplies strict acceptance. -/
theorem unanimous_next_vote_viable
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : Healing.Unanimous tr H u P) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hold : ∀ x r b B, Healing.HighOrigin tr H g x r b B → tr.time r < sp.ts u →
      Anc (tr.HonestBlocks H) B P)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcast : SA.CastAt tr.projAC y j ell e)
    (hs : e.msg.slot = u + 1) :
    Anc (tr.HonestBlocks H) ell.frame.F P ∧
      P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (u + 1)) := by
  have hS := Healing.healthy_base_of_reset_catch hp hc
  have hbound := high_origins_before_next_slot_below hp hc hP hun hgu hold
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hS.run.localRun hy hcast.1
  have hroot := Healing.reset_vote_root_below_bound hp hR hP hbound hy hcast hs
  have hFP := (hPhi.F_anc_fcRoot.mono hPhiU).trans hroot
  obtain ⟨q, v, hvote, hvs⟩ := SA.honest_votes_in_slot hS hgu y hy
  obtain ⟨ellv, hv⟩ := hvote
  obtain ⟨⟨Hd, hHd, he, _⟩, ht⟩ := Compose.cast_head_fcRoot hS.run.localRun hy hv
  have hPsiU := (SA.frameIn_of_callAt hS.run.localRun hy hv.1).2
  have heq : Hd = P := hS.run.localRun.coherent.1 (hPsiU hHd) hP
    (he.trans (hun y hy q v ⟨ellv, hv⟩ hvs))
  subst Hd
  have hacc : SA.AcceptedBefore tr.projAC y P (sp.ts u + 3 * sp.Δ) := by
    rcases SA.frame_genesis_or_accepted sp hS.run.localRun hy hv.1 P hHd with hz | ⟨k, hk, ha⟩
    · omega
    · refine Or.inr ⟨k, ha, ?_⟩
      have htime := hp.run.time_mono hk
      rw [hvs] at ht
      change tr.time q ≤ sp.ts u + sp.Δ at ht
      change tr.time k < _
      linarith [sp.toParams.hΔ]
  have hPt := Compose.accepted_voter_tree hp.run hp.noColl hy hcast hs hP hacc hFP
  have hstore : P ∈ (tr.state y j).fg.tree := by
    have hm := hPt.1
    rw [Compose.frame_of_projAC hp.run hy hcast.1] at hm
    exact hm.1
  have hfloor := Healing.reset_vote_floor_above_old hp hy hR hcast hs hstore hbound
  have hroot' := SA.anc_tree_of_anc_U hS.run.localRun.coherent hPhi hPhiU
    hPhi.fcRoot_mem hroot hPt.1
  refine ⟨hFP, hPt, hroot', P, hPt, ?_, .refl⟩
  have hm := hPt.1
  rw [Compose.frame_of_projAC hp.run hy hcast.1] at hm hroot' ⊢
  exact ⟨hm.1, hm.2, hroot'.mono (fun X hX => hX.1), hfloor⟩

/-- The ready proposal's actual parent walk supplies the old bound, so admission at
next-slot casts needs no new high-cover or higher-report hypothesis. -/
theorem ready_next_vote_viable
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.ReadyProposal tr H proposer p k u P)
    (hPU : P ∈ tr.HonestBlocks H) (hu : 0 < u)
    (hR : Healing.drainTime sp a ≤ sp.ts u) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {i : Nat} {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (SA.Payload sp.n)} {pay : SA.Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hPQ : P.parent = some d.head.root)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcast : SA.CastAt tr.projAC y j ell e)
    (hs : e.msg.slot = u + 1) :
    Anc (tr.HonestBlocks H) ell.frame.F P ∧
      P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (u + 1)) := by
  have hS := Healing.healthy_base_of_reset_catch hp hc
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hS.run.localRun hP.1 hci
  obtain ⟨hst, hsh⟩ := Compose.acProposal_start_anc_head hPhi hd
  have hhead : d.head ∈ ellp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem hsh he).2
  apply unanimous_next_vote_viable hp hc hPU hP.2.2.2.2.1 hu
    (Healing.ready_unanimous hp hc hP hR) hgu
    (hR.trans ((SA.ts_le_iff sp).2 (by omega))) ?_ hy hcast hs
  intro x r b B ho ht
  exact (Healing.crossing_below_proposal_parent hp hc hP hR hci hcall hd hti hPQ ho ht
    (.refl)).trans (.single ⟨hPhiU hhead, hPU, hPQ⟩)

/-- A strict post-update start excludes the equal-label update even at a later cut
with the same timestamp. The separate `10Δ` bound supplies the raw service window. -/
theorem effectiveRecordInterval_after_cover_update
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r b i j : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : Healing.HighOrigin tr H g x r b B) (hOB : Anc (tr.HonestBlocks H) O B)
    (hy : y ∈ H) (hstart : sp.ts b + 6 * sp.Δ < tr.time i)
    (hlate : SA.gbar g + 10 * sp.Δ ≤ tr.time i)
    (hframes : ∀ q, i ≤ q → q < j →
      Compatible (tr.HonestBlocks H) (tr.state y (q + 1)).fg.F O ∨
        (tr.IsCall y q ∧ a ≤ tr.time q ∧ (r ≤ q ∨ sp.ts (b + 1 : Nat) ≤ tr.time q))) :
    EffectiveRecordInterval tr H y i j O := by
  apply effectiveRecordInterval_of_high_cover hp ho hOB hy ?_ hframes
  intro q hiq _ D s CV hD
  have htime := hp.run.time_mono hiq
  have hΔ := sp.toParams.hΔ
  have rawtime : SA.ResultAt tr.projAC y q s D CV → tr.time q = sp.ts s + 6 * sp.Δ := by
    rintro ⟨ell, hu, _⟩
    exact hu.2.2.1
  refine Or.inr ⟨?_, fun h => ⟨?_, hc⟩⟩
  · rcases hD with h | ⟨ell, A, _, hs, _⟩
    · have ht := rawtime h
      have hbs : sp.ts b < sp.ts s := by linarith
      have := (SA.ts_lt_iff sp).1 hbs
      omega
    · have hs' : sp.slot (tr.time q) = s := hs
      have ht : sp.ts (b + 1 : Nat) ≤ tr.time q := by
        simp only [SA.SAParams.ts] at hstart ⊢
        push_cast
        linarith
      have := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg q) (↑(b + 1 : Nat))).1 ht
      omega
  · have ht := rawtime h
    linarith

/-- Frozen admission and healthy carry propagate a unanimous slot through every
next-slot cast, by strong induction on the cast cut. -/
theorem unanimous_next_votes_extend
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : Healing.Unanimous tr H u P) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hold : ∀ x r b B, Healing.HighOrigin tr H g x r b B → tr.time r < sp.ts u →
      Anc (tr.HonestBlocks H) B P) :
    ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → e.msg.slot = u + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg P := by
  have hS := Healing.healthy_base_of_reset_catch hp hc
  have hprev : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → e.msg.slot = u →
      SA.VoteExtends (tr.HonestBlocks H) e.msg P := by
    intro y hy j e hv hs
    exact ⟨P, hP, (hun y hy j e hv hs).symm, .refl⟩
  have all : ∀ j y, y ∈ H → ∀ e, SA.VoteAt tr.projAC y j e → e.msg.slot = u + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg P := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro y hy e hv hs
      obtain ⟨ell, hcast⟩ := hv
      obtain ⟨hFP, hvi⟩ := unanimous_next_vote_viable hp hc hP hslot hu hun hgu hR hold hy hcast hs
      have hsl := (SA.castAt_spec hS.run.localRun hy hcast).2.1
      have hT : SA.gbar g ≤ sp.ts ((sp.slot (tr.projAC.time j) : Int) - 1) := by
        rw [← hsl, hs]
        simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
        linarith [sp.toParams.hΔ]
      apply SA.next_vote_extends_before hS.run hy hcast hs ?_
        (SA.honest_voters_half hS hgu)
        (SA.healthy_carry_votes hS hgu hprev hy hcast hs hFP)
        (hS.faultBound (hS.run.localRun.time_nonneg j) hT)
        (hS.syncAC (by linarith [sp.toParams.hΔ]) (tr.projAC.time j)) (Or.inl hvi)
      intro z hz q hq v hv hvs
      rcases hvs with hvs | hvs
      · exact hprev z hz q v hv hvs
      · exact ih q hq z hz v hv hvs
  exact fun y hy j e hv hs => all j y hy e hv hs

/-- Next-slot optimistic candidates are comparable with the unanimous prefix. -/
theorem unanimous_next_optimistic_compatible
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : Healing.Unanimous tr H u P) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hold : ∀ x r b B, Healing.HighOrigin tr H g x r b B → tr.time r < sp.ts u →
      Anc (tr.HonestBlocks H) B P)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (hopt : SA.OptimisticLockAt tr.projAC y j (u + 1) D CV) :
    Compatible (tr.HonestBlocks H) D P := by
  have hS := Healing.healthy_base_of_reset_catch hp hc
  exact SA.optimisticLock_compatible hS.run hS.two_faulty_lt hy hopt
    (unanimous_next_votes_extend hp hc hP hslot hu hun hgu hR hold)

/-- Every high origin written by the update deadline is comparable with the unanimous
proposal. The next-slot optimistic case uses the actual next-vote transfer theorem. -/
theorem high_origin_compatible_before_update
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : Healing.Unanimous tr H u P) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hold : ∀ x r b B, Healing.HighOrigin tr H g x r b B → tr.time r < sp.ts u →
      Anc (tr.HonestBlocks H) B P)
    {x : Fin sp.n} {r b : Nat} (ho : Healing.HighOrigin tr H g x r b B)
    (ht : tr.time r ≤ sp.ts u + 6 * sp.Δ) : Compatible (tr.HonestBlocks H) B P := by
  have hS := Healing.healthy_base_of_reset_catch hp hc
  obtain ⟨ell, D, CV, hcall, hfl, _, _, _, hBD, _⟩ := Healing.highOrigin_mem hp ho
  have hBDU := hBD.mono (SA.frameIn_of_callAt hS.run.localRun ho.1 hcall).2
  by_cases hbu : b < u
  · obtain ⟨q, e, hv, hs⟩ := SA.honest_votes_in_slot hS hgu x ho.1
    obtain ⟨ellv, hcast⟩ := hv
    obtain ⟨Hd, hHd, he, hBH⟩ :=
      (covered_vote_suffix hp ho (.refl) ho.1 hcast (by omega)).2.2.1
    have heq : Hd = P := hS.run.localRun.coherent.1 hHd hP
      (he.trans (hun x ho.1 q e ⟨ellv, hcast⟩ hs))
    exact Or.inl (heq ▸ hBH)
  by_cases heq : b = u
  · subst b
    obtain ⟨z, hz, q, e, hv, hs, Hd, hHd, he, hDH⟩ :=
      SA.fastLock_honest_vote hS.run hS.two_faulty_lt ho.1 hfl
    have heq : Hd = P := hS.run.localRun.coherent.1 hHd hP
      (he.trans (hun z hz q e hv hs))
    exact Or.inl (hBDU.trans (heq ▸ hDH))
  have hgt : u < b := by omega
  have hDP : Compatible (tr.HonestBlocks H) D P := by
    rcases hfl with ⟨ellr, C, hupd, _⟩ | hop
    · have ht' : tr.time r = sp.ts b + 6 * sp.Δ := hupd.2.2.1
      have hs := (SA.ts_lt_iff sp).2 (show (u : Int) < b by omega)
      exfalso; linarith
    · have hs : sp.slot (tr.time r) = b := hop.choose_spec.choose_spec.2.1
      have hb : b ≤ u + 1 := by
        have hm := SA.slot_mono sp (hp.run.time_nonneg r) ht
        have hdeadline : sp.slot (sp.ts u + 6 * sp.Δ) = u + 1 :=
          SA.slot_of_mem sp (u + 1)
            (by simp only [SA.SAParams.ts]; push_cast; linarith [sp.toParams.hΔ])
            (by simp only [SA.SAParams.ts]; push_cast; linarith [sp.toParams.hΔ])
        rw [hs, hdeadline] at hm
        exact hm
      have hb' : b = u + 1 := by omega
      exact unanimous_next_optimistic_compatible hp hc hP hslot hu hun hgu hR hold
        ho.1 (hb' ▸ hop)
  rcases hDP with h | h
  · exact Or.inl (hBDU.trans h)
  · exact SA.anc_total hS.run.localRun.coherent hBDU h

/-- Through the update deadline, finality is compatible with the unanimous proposal. -/
theorem finalized_compatible_before_update
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : Healing.Unanimous tr H u P) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hold : ∀ x r b B, Healing.HighOrigin tr H g x r b B → tr.time r < sp.ts u →
      Anc (tr.HonestBlocks H) B P)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} (ha : a ≤ tr.time k)
    (ht : tr.time k ≤ sp.ts u + 6 * sp.Δ) :
    Compatible (tr.HonestBlocks H) (tr.state y k).fg.F P := by
  obtain ⟨x, r, b, B, ho, hrk, hFB⟩ := Healing.finalized_below_high_origin hp hy ha
  rcases high_origin_compatible_before_update hp hc hP hslot hu hun hgu hR hold ho
      (hrk.trans ht) with h | h
  · exact Or.inl (hFB.trans h)
  · exact SA.anc_total (Healing.honest_coherent hp) hFB h

/-- The deadline finality alternative, with compatibility derived rather than assumed.
The report is actual and its strict height comparison is at its own cut. -/
theorem finality_alternative_before_update
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : Healing.Unanimous tr H u P) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hold : ∀ x r b B, Healing.HighOrigin tr H g x r b B → tr.time r < sp.ts u →
      Anc (tr.HonestBlocks H) B P)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} (ha : a ≤ tr.time k)
    (ht : tr.time k ≤ sp.ts u + 6 * sp.Δ) :
    Anc (tr.HonestBlocks H) (tr.state y k).fg.F P ∨
      ∃ z ∈ H, ∃ r ℓ C, r < k ∧ SA.ToFGAt tr.projAC z r ℓ C ∧
        tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C ∧
        ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h := by
  rcases Healing.finality_below_or_higher_report hp hy
      (finalized_compatible_before_update hp hc hP hslot hu hun hgu hR hold hy ha ht) with
    h | ⟨z, hz, r, ℓ, C, hrk, hto, hPC, hlt⟩
  · exact Or.inl h
  · exact Or.inr ⟨z, hz, r, ℓ, C, hrk, hto, (hp.run.time_mono hrk.le).trans ht, hPC, hlt⟩

/-- At an actual update, the only additional admission obligation is its floor bound.
The receiver's prior unanimous vote supplies acceptance; next-slot optimism is derived. -/
theorem ready_update_of_floor_bound
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.ReadyProposal tr H proposer p k u P)
    (hPU : P ∈ tr.HonestBlocks H) (hupos : 0 < u)
    (hR : Healing.drainTime sp a ≤ sp.ts u) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hold : ∀ x r b B, Healing.HighOrigin tr H g x r b B → tr.time r < sp.ts u →
      Anc (tr.HonestBlocks H) B P)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hupd : SA.UpdateAt tr.projAC y j u ell)
    (hFP : Anc (tr.HonestBlocks H) ell.frame.F P) :
    Anc (tr.HonestBlocks H) P
      ((SA.lookup ell.frame (tr.projAC.post j).latestConfirmed).getD ell.frame.F) ∧
      SA.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P := by
  have hS := Healing.healthy_base_of_reset_catch hp hc
  have hun := Healing.ready_unanimous hp hc hP hR
  obtain ⟨q, v, hvote, hvs⟩ := SA.honest_votes_in_slot hS hgu y hy
  obtain ⟨ellv, hv⟩ := hvote
  obtain ⟨⟨Hd, hHd, he, _⟩, ht⟩ := Compose.cast_head_fcRoot hS.run.localRun hy hv
  have hPsiU := (SA.frameIn_of_callAt hS.run.localRun hy hv.1).2
  have heq : Hd = P := hS.run.localRun.coherent.1 (hPsiU hHd) hPU
    (he.trans (hun y hy q v ⟨ellv, hv⟩ hvs))
  subst Hd
  obtain ⟨ka, hka, hacc⟩ :=
    (SA.frame_genesis_or_accepted sp hS.run.localRun hy hv.1 P hHd).resolve_left
    (by have := hP.2.2.2.2.1; omega)
  have hqj : q ≤ j := by
    by_contra hn
    have hm := hp.run.time_mono (Nat.le_of_not_ge hn)
    have hupdate : tr.time j = sp.ts u + 6 * sp.Δ := hupd.2.2.1
    rw [hvs] at ht
    change tr.time q ≤ sp.ts u + sp.Δ at ht
    linarith [sp.toParams.hΔ]
  have hPt := SA.mem_tree_of_acceptAt sp hS.run.localRun hy hacc (hka.trans hqj) hupd.1 hFP
  apply ready_update_effective_record hp hc hP hR hgu hy hupd hPt
  intro r _ D CV hop
  exact unanimous_next_optimistic_compatible hp hc hPU hP.2.2.2.2.1 hupos hun hgu
    (hR.trans ((SA.ts_le_iff sp).2 (by omega))) hold hy hop

/-- Ready-update assembly from the actual proposal walk. Only the update-floor bound
remains as a loss-prevention premise; an alternative higher report is not manufactured. -/
theorem ready_update_of_proposal_floor_bound
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.ReadyProposal tr H proposer p k u P)
    (hPU : P ∈ tr.HonestBlocks H) (hu : 0 < u)
    (hR : Healing.drainTime sp a ≤ sp.ts u) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {i : Nat} {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (SA.Payload sp.n)} {pay : SA.Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hPQ : P.parent = some d.head.root)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hupd : SA.UpdateAt tr.projAC y j u ell)
    (hFP : Anc (tr.HonestBlocks H) ell.frame.F P) :
    Anc (tr.HonestBlocks H) P
      ((SA.lookup ell.frame (tr.projAC.post j).latestConfirmed).getD ell.frame.F) ∧
      SA.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P := by
  have hS := Healing.healthy_base_of_reset_catch hp hc
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hS.run.localRun hP.1 hci
  obtain ⟨hst, hsh⟩ := Compose.acProposal_start_anc_head hPhi hd
  have hhead : d.head ∈ ellp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem hsh he).2
  apply ready_update_of_floor_bound hp hc hP hPU hu hR hgu ?_ hy hupd hFP
  intro x r b B ho ht
  exact (Healing.crossing_below_proposal_parent hp hc hP hR hci hcall hd hti hPQ ho ht
    (.refl)).trans (.single ⟨hPhiU hhead, hPU, hPQ⟩)

/-- Ready report coverage with only the below-floor report duty left explicit.
The actual proposal supplies old-origin domination; healthy service supplies every
reader's deadline update, and finality compatibility is derived at that cut. -/
theorem report_cover_of_ready_floor_duty
    (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.ReadyProposal tr H proposer p k u P)
    (hPU : P ∈ tr.HonestBlocks H) (hu : 0 < u)
    (hR : Healing.drainTime sp a ≤ sp.ts u) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {i : Nat} {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (SA.Payload sp.n)} {pay : SA.Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hPQ : P.parent = some d.head.root)
    (hduty : ∀ z ∈ H, ∀ j ell, SA.UpdateAt tr.projAC z j u ell →
      Anc (tr.HonestBlocks H) ell.frame.F P →
        ∃ r ell' C, SA.ToFGAt tr.projAC z r ell' C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
          Anc (tr.HonestBlocks H) P C) :
    (∀ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C) ∨
    ∃ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C ∧
      ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h := by
  have hS := Healing.healthy_base_of_reset_catch hp hc
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hS.run.localRun hP.1 hci
  obtain ⟨hst, hsh⟩ := Compose.acProposal_start_anc_head hPhi hd
  have hhead : d.head ∈ ellp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem hsh he).2
  have hold : ∀ x r b B, Healing.HighOrigin tr H g x r b B → tr.time r < sp.ts u →
      Anc (tr.HonestBlocks H) B P := by
    intro x r b B ho ht
    exact (Healing.crossing_below_proposal_parent hp hc hP hR hci hcall hd hti hPQ ho ht
      (.refl)).trans (.single ⟨hPhiU hhead, hPU, hPQ⟩)
  have hau : a ≤ sp.ts u := by
    have ha0 : 0 ≤ a := by
      linarith [Healing.cutZ_lt_reset hp.run hp.healthy hp.reset,
        Healing.lt_cutZ sp g, SA.gbar_nonneg g, sp.toParams.hΔ]
    have hnext : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
      omega
    have hnextR : sp.ts ((sp.slot a : Int) + 1) ≤ Healing.drainTime sp a := by
      rw [Healing.drainTime_eq]
      exact (SA.ts_le_iff sp).2 (by push_cast; omega)
    exact hnext.le.trans (hnextR.trans hR)
  apply Healing.report_cover_of_compatible_floors hp
  intro z hz
  obtain ⟨j, ell, ell', hupd, _, _, _, _, _⟩ :=
    Healing.reset_update_toFG_calls hp hc hz (u := u) (by linarith [sp.toParams.hΔ])
  have ht : tr.time j = sp.ts u + 6 * sp.Δ := hupd.2.2.1
  refine ⟨j, ht.le, ?_, ?_⟩
  · exact finalized_compatible_before_update hp hc hPU hP.2.2.2.2.1 hu
      (Healing.ready_unanimous hp hc hP hR) hgu
      (hR.trans ((SA.ts_le_iff sp).2 (by omega))) hold hz
      (by rw [ht]; linarith [sp.toParams.hΔ]) ht.le
  · intro hF
    apply hduty z hz j ell hupd
    rw [Compose.frame_of_projAC hp.run hz hupd.1]
    exact hF

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

end UpTo

end CoveredEndpoint

end Consensus.Goldilocks.Refinement
end
