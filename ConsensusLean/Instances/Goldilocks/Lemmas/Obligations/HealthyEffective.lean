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

variable {sp : AC.ACParams} {FGP : Type} {U : Set (AC.Blk sp.n FGP)}

/-- A conflicting candidate above a prefix can only be vetoed by a compatible lock
that covers that prefix. -/
theorem cover_of_veto {U : Set (AC.Blk sp.n FGP)} (_hU : Coherent U)
    {B C L : AC.Blk sp.n FGP} (hBC : Anc U B C) (hLB : Compatible U L B)
    (hLC : ¬ Compatible U C L) : Anc U B L := by
  rcases hLB with hLB | hBL
  · exact False.elim (hLC (Or.inr (hLB.trans hBC)))
  · exact hBL

/-- An exposed prefix survives exactly when both inputs to the new LCA extend it. -/
theorem exposed_prefix_preserved_of_record_head (hU : Coherent U)
    {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {A : AC.ACState sp.n} {t : Time} {O : AC.Blk sp.n FGP} :
    Anc U O (AC.acConfirmed sp A Φ t) ↔
      Anc U O ((AC.lookup Φ A.latestConfirmed).getD Φ.F) ∧
      Anc U O (AC.acHead sp A Φ t) := by
  constructor
  · intro h
    have hC : (AC.lookup Φ A.latestConfirmed).getD Φ.F ∈ Φ.tree := by
      cases he : AC.lookup Φ A.latestConfirmed with
      | none => exact hΦ.rooted.1
      | some C => exact (AC.lookup_eq_some he).1
    have hH : AC.acHead sp A Φ t ∈ Φ.tree :=
      AC.getHead_mem hΦ (T := Φ.viableTree Φ.tree) (fun _ h => h.1) _ _ _ _
    unfold AC.acConfirmed at h
    cases hd : AC.deepest Φ {X | X ∈ Φ.tree ∧
        Φ.Anc X ((AC.lookup Φ A.latestConfirmed).getD Φ.F) ∧
        Φ.Anc X (AC.acHead sp A Φ t)} with
    | none =>
      simp only [hd, Option.getD_none] at h
      exact ⟨h.trans ((hΦ.rooted.2 _ hC).mono hΦU),
        h.trans ((hΦ.rooted.2 _ hH).mono hΦU)⟩
    | some D =>
      simp only [hd, Option.getD_some] at h
      exact ⟨h.trans ((AC.deepest_mem hd).1.2.1.mono hΦU),
        h.trans ((AC.deepest_mem hd).1.2.2.mono hΦU)⟩
  · exact fun h => AC.anc_acConfirmed_of_frame hU hΦ hΦU h.1 h.2

/-- Compatibility with a write candidate preserves a prefix, even when the old record
and the candidate themselves need not be comparable. -/
private theorem effective_record_update_of_compatible (hU : Coherent U)
    {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {A : AC.ACState sp.n} {O D : AC.Blk sp.n FGP}
    (hO : Anc U O ((AC.lookup Φ A.latestConfirmed).getD Φ.F))
    (hD : D ∈ Φ.tree) (hcomp : Compatible U O D) :
    Anc U O ((AC.lookup Φ (AC.updateLatestConfirmed sp A Φ D).latestConfirmed).getD Φ.F) := by
  classical
  unfold AC.updateLatestConfirmed
  split_ifs with hguard
  · exact hO
  have hOD : Anc U O D := by
    rcases hcomp with h | h
    · exact h
    cases he : AC.lookup Φ A.latestConfirmed with
    | none =>
      simp only [he, Option.getD_none] at hO
      exact hO.trans ((hΦ.rooted.2 _ hD).mono hΦU)
    | some C =>
      simp only [he, Option.getD_some] at hO
      obtain ⟨hC, hr⟩ := AC.lookup_eq_some he
      exact False.elim (hguard ⟨C, hC, hr,
        AC.anc_tree_of_anc_U hU hΦ hΦU hD (h.trans hO) hC⟩)
  change Anc U O ((AC.lookup Φ D.root).getD Φ.F)
  cases he : AC.lookup Φ D.root with
  | none => exact False.elim (AC.lookup_eq_none he ⟨D, hD, rfl⟩)
  | some C =>
    obtain ⟨hC, hr⟩ := AC.lookup_eq_some he
    have : C = D := hU.1 (hΦU hC) (hΦU hD) hr
    simpa [this] using hOD

/-- A fixed archival record survives a frame change when blocks above the new floor
remain available. The retention premise concerns membership, not viable heads. -/
theorem effective_record_frame_of_compatible (hU : Coherent U)
    {Φ Ψ : AC.Frm sp.n FGP} (hΨ : FrameOK Ψ) (hΦU : Φ.tree ⊆ U) (hΨU : Ψ.tree ⊆ U)
    {r : Nat} {O : AC.Blk sp.n FGP} (hFF : Anc U Φ.F Ψ.F)
    (hFO : Compatible U Ψ.F O)
    (hretain : ∀ C ∈ Φ.tree, Anc U Ψ.F C → C ∈ Ψ.tree)
    (hO : Anc U O ((AC.lookup Φ r).getD Φ.F)) :
    Anc U O ((AC.lookup Ψ r).getD Ψ.F) := by
  have floor : Anc U Ψ.F ((AC.lookup Ψ r).getD Ψ.F) := by
    cases he : AC.lookup Ψ r with
    | none => exact .refl
    | some C => exact (hΨ.rooted.2 _ (AC.lookup_eq_some he).1).mono hΨU
  rcases hFO with hFO | hOF
  swap
  · exact hOF.trans floor
  cases he : AC.lookup Φ r with
  | none =>
    simp only [he, Option.getD_none] at hO
    exact hO.trans (hFF.trans floor)
  | some C =>
    simp only [he, Option.getD_some] at hO
    obtain ⟨hC, hr⟩ := AC.lookup_eq_some he
    have hC' := hretain C hC (hFO.trans hO)
    cases he' : AC.lookup Ψ r with
    | none => exact False.elim (AC.lookup_eq_none he' ⟨C, hC', hr⟩)
    | some D =>
      obtain ⟨hD, hrD⟩ := AC.lookup_eq_some he'
      have : D = C := hU.1 (hΨU hD) (hΦU hC) (hrD.trans hr.symm)
      simpa [this] using hO

/-- The frame adapter instantiated on actual states of one honest node. -/
private theorem effective_record_frame_of_run
    {tr : GoldilocksTrace sp}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)}
    {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i j r : Nat} (hij : i ≤ j)
    {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (hFO : Compatible (tr.HonestBlocks H) (tr.state y j).fg.F O)
    (hO : Anc (tr.HonestBlocks H) O
      ((AC.lookup (Node.frame (tr.state y i)) r).getD (tr.state y i).fg.F)) :
    Anc (tr.HonestBlocks H) O
      ((AC.lookup (Node.frame (tr.state y j)) r).getD (tr.state y j).fg.F) := by
  have hU := (Compose.goldilocks_ac_projection_from hrun hnc).localRun.coherent
  have hreach := Compose.fg_reachable hrun.toLocalRun hy j
  have hΨ := Store.frame_realization _ _ _ _ hreach
  apply effective_record_frame_of_compatible hU (Φ := Node.frame (tr.state y i)) hΨ
    (fun X hX => ⟨y, hy, i, hX.1⟩) (fun X hX => ⟨y, hy, j, hX.1⟩)
    (Healing.run_F_mono hrun.toLocalRun hy hij) hFO ?_ hO
  intro C hC hFC
  have hCj := Compose.tree_mono hrun.toLocalRun hy hij hC.1
  obtain ⟨hfin, htc, hgm, hgen⟩ := Store.accepted_tree _ _ _ _ hreach
  have hfull : FrameOK (⟨(tr.state y j).fg.tree, _, ∅⟩ :
      Frame sp.n (List (FG.Att sp.n)) (AC.Payload sp.n)) :=
    { finite := hfin, coherent := htc, rooted := ⟨hgm, hgen⟩
      viableHeads_subset := Set.empty_subset _ }
  exact ⟨hCj, AC.anc_tree_of_anc_U hU hfull (fun X hX => ⟨y, hy, j, hX⟩)
    hΨ.rooted.1.1 hFC hCj⟩

/-- Every guarded write in a call preserves a prefix compatible with its candidates. -/
theorem effective_record_writes_of_compatible (hU : Coherent U)
    {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {New : AC.Blk sp.n FGP → Prop} {r r' : Nat} {O : AC.Blk sp.n FGP}
    (hw : Compose.Writes Φ New r r')
    (hnew : ∀ D, New D → Compatible U O D)
    (hO : Anc U O ((AC.lookup Φ r).getD Φ.F)) :
    Anc U O ((AC.lookup Φ r').getD Φ.F) := by
  have hw' := Compose.writes_iff.1 hw
  clear hw
  induction hw' with
  | refl => exact hO
  | @tail r' r'' _ hs ih =>
    obtain ⟨D, hD, hn, hk | ⟨hg, rfl⟩⟩ := hs
    · simpa only [hk.2] using ih
    let A : AC.ACState sp.n := AC.ACState.initial r'
    have h := effective_record_update_of_compatible hU hΦ hΦU (A := A) ih hD (hnew D hn)
    simpa only [AC.updateLatestConfirmed, A, AC.ACState.initial, hg, ↓reduceIte] using h

/-- An update tick runs exactly the preceding slot's update, without a vote attempt. -/
theorem post_of_update
    {H : Set (Fin sp.n)} {tr : AC.GTrace sp FGP}
    {ini} (hr : ACLocalRun (AC.goldilocksAC sp FGP) H U tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {c s : Nat}
    {ell : ACLabel (AC.goldilocksAC sp FGP)} (hu : AC.UpdateAt tr y c s ell) :
    tr.post c = AC.updateConfirmation sp (tr.state y c) ell.frame (tr.time c) s := by
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [AC.ACParams.ts]; push_cast; ring
  have hslot : sp.slot (tr.time c) = s + 1 := AC.slot_of_mem sp (s + 1)
    (by rw [hu.2.2.1, hts]; linarith)
    (by rw [hu.2.2.1, show sp.ts (s + 1 + 1 : Nat) =
      sp.ts (s + 1 : Nat) + 4 * sp.Δ by simp only [AC.ACParams.ts]; push_cast; ring, hts]; linarith)
  have he := hr.exec c ell hu.1.2 (hu.1.1 ▸ hy)
  rw [hu.1.1, hu.2.1] at he
  have hpost : tr.post c = (AC.acOnTick sp y (tr.state y c) ell.frame (tr.time c)).1 :=
    (congrArg Prod.fst he).symm
  rw [hpost]
  unfold AC.acOnTick
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
    {H : Set (Fin sp.n)} {tr : AC.GTrace sp FGP}
    {ini} (hr : ACLocalRun (AC.goldilocksAC sp FGP) H U tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {c s : Nat}
    {ell : ACLabel (AC.goldilocksAC sp FGP)} (hu : AC.UpdateAt tr y c s ell)
    {C : AC.Blk sp.n FGP} {CV : Set (AC.Vote sp.n)} (hR : AC.ResultAt tr y c s C CV)
    (hnv : ¬ AC.conflictsWithLock sp (tr.state y c).locks ell.frame (tr.time c) C) :
    ell.frame.Anc C ((AC.lookup ell.frame (tr.post c).latestConfirmed).getD ell.frame.F) := by
  obtain ⟨hΦ, -⟩ := AC.frameIn_of_callAt hr hy hu.1
  obtain ⟨ell', hu', hC, -⟩ := hR
  have heq : ell' = ell := Option.some.inj (hu'.1.2.symm.trans hu.1.2)
  subst ell'
  rw [post_of_update hr hy hu]
  unfold AC.updateConfirmation
  simp only [hC]
  rw [ite_eq_right hnv]
  exact (effective_record_update_slot_growth (sp := sp) hΦ (AC.deepest_mem hC).1.1).1

/-- A head certificate is checked at the actual read clock. Floor coverage also
allows the prefix to lie outside the current frame. -/
theorem anc_acHead_of_current_certificate
    {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {A : AC.ACState sp.n} {O : AC.Blk sp.n FGP} {t : Time}
    (hhead : Anc U O Φ.F ∨ (O ∈ Φ.tree ∧
      Compatible Φ.tree (AC.getAnchor sp A Φ t) O ∧
      (Φ.Anc O (AC.getAnchor sp A Φ t) ∨ (O ∈ Φ.viableTree Φ.tree ∧
        (AC.voters (AC.latestView sp A Φ t).1.votes).ncard <
          2 * (AC.supporters Φ (AC.latestView sp A Φ t).1
            (AC.latestView sp A Φ t).2 O).ncard)))) :
    Anc U O (AC.acHead sp A Φ t) := by
  rcases hhead with hF | ⟨hO, hcomp, hsup⟩
  · have hH : AC.acHead sp A Φ t ∈ Φ.tree :=
      AC.getHead_mem hΦ (T := Φ.viableTree Φ.tree) (fun _ h => h.1) _ _ _ _
    exact hF.trans ((hΦ.rooted.2 _ hH).mono hΦU)
  · exact (AC.anc_acHead hΦ hO hcomp hsup).mono hΦU

variable {tr : GoldilocksTrace sp}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)} {g ΔF a : Time}

/-- Explicit interval producer contract for one earlier output. Each transition either
decomposes into guarded writes in the old frame followed by a compatible floor change,
or supplies a replacement effective record extending the prefix (including restarts).
The write predicate must include every actual write. No such provenance,
restart preservation, or floor compatibility is inferred from a lock at one read. -/
structure EffectiveRecordInterval (tr : GoldilocksTrace sp) (H : Set (Fin sp.n))
    (y : Fin sp.n) (i j : Nat) (O : AC.Blk sp.n (List (FG.Att sp.n))) : Prop where
  step : ∀ q, i ≤ q → q < j →
    (∃ New : AC.Blk sp.n (List (FG.Att sp.n)) → Prop,
      Compose.Writes (Node.frame (tr.state y q)) New
        (tr.state y q).ac.latestConfirmed (tr.state y (q + 1)).ac.latestConfirmed ∧
      (∀ D, New D → Compatible (tr.HonestBlocks H) O D) ∧
      Compatible (tr.HonestBlocks H) (tr.state y (q + 1)).fg.F O) ∨
    Anc (tr.HonestBlocks H) O
      ((AC.lookup (Node.frame (tr.state y (q + 1)))
        (tr.state y (q + 1)).ac.latestConfirmed).getD (tr.state y (q + 1)).fg.F)

/-- The interval contract preserves the effective record across every intervening cut. -/
theorem effective_record_of_interval
    {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i j : Nat} (hij : i ≤ j)
    {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (hint : EffectiveRecordInterval tr H y i j O)
    (hO : Anc (tr.HonestBlocks H) O ((AC.lookup (Node.frame (tr.state y i))
      (tr.state y i).ac.latestConfirmed).getD (tr.state y i).fg.F)) :
    Anc (tr.HonestBlocks H) O ((AC.lookup (Node.frame (tr.state y j))
      (tr.state y j).ac.latestConfirmed).getD (tr.state y j).fg.F) := by
  have hU := (Compose.goldilocks_ac_projection_from hrun hnc).localRun.coherent
  have step : ∀ q, i ≤ q → q ≤ j → Anc (tr.HonestBlocks H) O
      ((AC.lookup (Node.frame (tr.state y q)) (tr.state y q).ac.latestConfirmed).getD
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
