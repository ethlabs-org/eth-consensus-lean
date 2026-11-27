module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.FloorCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Prot
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Update
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FastExpiry
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Frame-independent fast-update facts over the run core -/

namespace Consensus.Goldilocks.Healing.Growing.Core

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

private theorem anc_of_isDeepest {FGP : Type} {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ)
    {S : Set (AC.Blk sp.n FGP)} {D X : AC.Blk sp.n FGP} (hD : AC.IsDeepest Φ S D) (hX : X ∈ S)
    (hXt : X ∈ Φ.tree) (h : Compatible Φ.tree X D) : Φ.Anc X D := by
  refine h.elim id fun hDX => ?_
  by_cases hne : D = X
  · exact hne ▸ Relation.ReflTransGen.refl
  · have := AC.depth_lt_of_anc hΦ hDX hne hXt
    rcases hD.2 X hX (Ne.symm hne) with h | h <;> omega

/-- The deepest unvetoed fast block extends every compatible unvetoed fast ancestor. -/
theorem fast_update_of_unvetoed_at
    {y : Fin sp.n} {k s : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hy : y ∈ H (tr.time k))
    (hrun : GoldilocksRunCore u frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hu : AC.UpdateAt tr.projAC y k s ell)
    {C P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hconf : AC.getConfirmation sp (tr.projAC.state y k) ell.frame s = some C)
    (hPt : P ∈ ell.frame.tree) (hPg : P.root ≠ sp.genesisRoot) (hPC : ell.frame.Anc P C)
    (hnv : ¬ AC.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) P)
    (hfast : AC.FastTest sp (tr.projAC.state y k) ell.frame s P) :
    ∃ D CV, AC.FastUpdateAt tr.projAC y k s D CV ∧ Anc (tr.HonestBlocksAt H) P D := by
  have hPhi := hrun.frameIn_at hnc hy hu.1
  set S := {X | X ∈ AC.confirmationPath sp ell.frame C ∧
    ¬ AC.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) X ∧
    AC.FastTest sp (tr.projAC.state y k) ell.frame s X}
  have hPS : P ∈ S := ⟨⟨hPt, hPg, hPC⟩, hnv, hfast⟩
  obtain ⟨D, hD⟩ := AC.exists_deepest hPhi.1 (fun X hX => hX.1.1) ⟨P, hPS⟩
  have hDd := AC.deepest_mem hD
  have hPD : ell.frame.Anc P D := anc_of_isDeepest hPhi.1 hDd hPS hPt
    (AC.anc_total hPhi.1.coherent hPC hDd.1.1.2.2)
  exact ⟨D, _, ⟨ell, C, hu, hconf, hD, rfl⟩, hPD.mono hPhi.2⟩

/-- The raw fast selection writes a live fast lock through the second following slot. -/
theorem fastLock_mem_updateConfirmation_of_select {FGP : Type} {A : AC.ACState sp.n}
    {Φ : AC.Frm sp.n FGP} {t : Time} {s : Nat} {C D : AC.Blk sp.n FGP}
    (hconf : AC.getConfirmation sp A Φ s = some C)
    (hD : AC.deepest Φ {X | X ∈ AC.confirmationPath sp Φ C ∧
      ¬ AC.conflictsWithLock sp A.locks Φ t X ∧ AC.FastTest sp A Φ s X} = some D)
    (hDt : D ∈ Φ.tree) (hlive : sp.slot t ≤ s + 2) :
    ∃ e, s + 2 ≤ e ∧ (⟨(Φ.viableAncestor D).root, s, true, e⟩ : AC.Lock) ∈
      (AC.updateConfirmation sp A Φ t s).locks := by
  have hD' : AC.deepest Φ {B | B ∈ {B | B ∈ AC.confirmationPath sp Φ C ∧
      ¬ AC.conflictsWithLock sp A.locks Φ t B} ∧ AC.FastTest sp A Φ s B} = some D := by
    rw [← hD]
    congr 1
    ext X
    simp only [Set.mem_ofPred_eq, and_assoc]
  unfold AC.updateConfirmation
  simp only [hconf]
  exact ⟨_, AC.le_fastExpiry sp _ Φ t s, ⟨D.root, s, true, _⟩,
    Or.inr ⟨_, Or.inl ⟨D, hD', rfl⟩, rfl⟩, D, hDt, rfl,
    hlive.trans (AC.le_fastExpiry sp _ Φ t s), rfl⟩

/-- The AC post-state of an honest update is the update-confirmation result. -/
theorem post_of_updateAt
    (hrun : GoldilocksRunCore u frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {k s : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} (hu : AC.UpdateAt tr.projAC y k s ell) :
    tr.projAC.post k =
      AC.updateConfirmation sp (tr.projAC.state y k) ell.frame (tr.time k) s := by
  have hr := (hrun.acRun_upTo hnc (hrun.time_nonneg k)).localRun
  have hc : (tr.projAC.upTo (tr.time k)).CallAt y k ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hu.1⟩
  have hs := Trace.upTo_state tr.projAC y (i := k)
    (fun q hq => hrun.time_mono hq.le)
  have he := hr.exec k ell hc.2 (hc.1 ▸ hy)
  rw [hc.1, hu.2.1, hs, Trace.upTo_post, Trace.upTo_time] at he
  have hkt : tr.time k = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have hslot : sp.slot (tr.time k) = s + 1 := by
    rw [hkt]
    apply AC.slot_of_mem sp (s + 1)
    all_goals simp only [ACParams.ts]; push_cast; linarith [sp.toParams.hΔ]
  rw [show tr.projAC.post k =
    (AC.acOnTick sp y (tr.projAC.state y k) ell.frame (tr.time k)).1 from
      (congrArg Prod.fst he).symm]
  unfold AC.acOnTick
  dsimp only
  rw [hslot]
  have ht1 : ¬ tr.time k = sp.ts (s + 1 : Nat) + sp.Δ := by
    rw [hkt]; simp only [ACParams.ts]; push_cast; linarith [sp.toParams.hΔ]
  have ht2 : tr.time k = sp.ts (s + 1 : Nat) + 2 * sp.Δ := by
    rw [hkt]; simp only [ACParams.ts]; push_cast; ring
  have hj : AC.joined sp (tr.projAC.state y k) (tr.time k) := hu.2.2.2
  rw [ite_eq_right (not_not.mpr hj), ite_eq_right ht1,
    ite_eq_left ⟨ht2, Nat.succ_pos s⟩]
  simp only [Nat.add_sub_cancel]

/-- The fast floor survives a cut of a growing run at its supplied frame. -/
theorem fastFloor_step_at
    (hrun : GoldilocksRunCore u frameOf proposer dg H tr ini)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {P : AC.Blk sp.n (List (FG.Att sp.n))} {j m : Nat}
    (hfl : Compose.FastFloorAtWith frameOf tr y k P j m) (hk : sp.slot (tr.time k) ≤ m)
    (hP : P ∈ (frameOf (tr.state y k)).tree)
    (hP' : P ∈ (frameOf (tr.state y (k + 1))).tree)
    (hva : (frameOf (tr.state y k)).viableAncestor P = P)
    (hu : (sp.slot (tr.time k) : Int) - 1 ≤ j ∨ Compose.UnlockKeepsWith frameOf tr y k P) :
    Compose.FastFloorAtWith frameOf tr y (k + 1) P j m := by
  have hd := hrun.time_nonneg k
  have hst : (tr.upTo (tr.time k)).state y k = tr.state y k :=
    RunTrace.upTo_state_of_le hrun.time_mono le_rfl
  have hst1 : (tr.upTo (tr.time k)).state y (k + 1) = tr.state y (k + 1) :=
    Trace.upTo_state tr y fun _ hk' => hrun.time_mono (Nat.lt_succ_iff.1 hk')
  have h := Compose.fastFloor_run_view_core (hrun.upTo hd) hy k (B₀ := P) (j := j) (m := m)
    (by simp only [Compose.FastFloorAtWith, hst]; exact hfl) hk (by rw [hst]; exact hP)
    (by rw [hst1]; exact hP') (by rw [hst]; exact hva) fun ell hc => by
      rw [hst]
      rcases hu with hs | hu
      · exact Or.inl hs
      · exact Or.inr (hu ell ((Trace.upTo_callAt_of_le _ le_rfl).mp hc))
  simp only [Compose.FastFloorAtWith, hst1] at h
  exact h

/-- A fresh fast lock remains a candidate while its two-slot lifetime lasts. -/
theorem toFG_candidate_of_viable_head_at {K : AC.CommitteeDict sp.n}
    (hrun : GoldilocksRunCore u frameOf proposer dg H tr (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g b : Time}
    (hK : CommitteeHalfUpTo tr H K g b)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} {r : Nat} (hgr : gbar g ≤ sp.ts (r + 1 : Nat))
    {y : Fin sp.n} {j : Nat} {D : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (hfu : AC.FastUpdateAt tr.projAC y j r D CV) (hPD : Anc (tr.HonestBlocksAt H) P D)
    {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ell) (hji : j < i)
    (hext : ∀ x k e, x ∈ H (tr.time k) → AC.VoteAt tr.projAC x k e → e.msg.slot = r + 1 →
      tr.time k ≤ tr.time i → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    (hPk : ∀ k, j ≤ k → k ≤ i → P ∈ (frameOf (tr.state y k)).tree ∧
      (frameOf (tr.state y k)).Anc (frameOf (tr.state y k)).fcRoot P ∧
      P ∈ (frameOf (tr.state y k)).viableHeads)
    (hib : tr.time i ≤ b) (hslot : sp.slot (tr.time i) ≤ r + 2) :
    ∃ B ∈ AC.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i),
      Anc (tr.HonestBlocksAt H) P B := by
  have hmono := hrun.time_mono
  have hU := hrun.coherent hnc
  obtain ⟨ellj, C, hu, hconf, hD, -⟩ := hfu
  have hji' := hmono hji.le
  have hyj : y ∈ H (tr.time j) := hrun.antitone hji' hy
  have hfrj := hrun.frame_of_projAC_at hyj hu.1
  obtain ⟨hΦj, hΦjU⟩ := hrun.frameIn_at hnc hyj hu.1
  have hDt := (AC.deepest_mem hD).1.1.1
  have hPj : P ∈ ellj.frame.tree := by rw [hfrj]; exact (hPk j le_rfl hji.le).1
  have hΦk (k : Nat) (hki : k ≤ i) : FrameOK (frameOf (tr.state y k)) :=
    hrun.frameOK_at (hrun.time_nonneg k) (hrun.antitone (hmono hki) hy)
      (fun q hq => hmono hq.le)
  have hvak (k : Nat) (hjk : j ≤ k) (hki : k ≤ i) :
      (frameOf (tr.state y k)).viableAncestor P = P := by
    obtain ⟨hPt, hroot, hv⟩ := hPk k hjk hki
    exact AC.viableAncestor_self (hΦk k hki) hPt (Or.inl ⟨hPt, hroot, P, hPt, hv, .refl⟩)
  have hjslot : sp.slot (tr.time j) = r + 1 := by
    have hjt : tr.time j = sp.ts r + 6 * sp.Δ := hu.2.2.1
    rw [hjt]
    apply AC.slot_of_mem sp (r + 1)
    all_goals simp only [ACParams.ts]; push_cast; linarith [sp.toParams.hΔ]
  obtain ⟨e, he, hl⟩ := fastLock_mem_updateConfirmation_of_select (t := tr.time j) hconf hD hDt
    (by omega)
  rw [← post_of_updateAt hrun hnc hyj hu] at hl
  have hyj1 : y ∈ H (tr.time (j + 1)) := hrun.antitone (hmono hji) hy
  have hl1 : (⟨(ellj.frame.viableAncestor D).root, r, true, e⟩ : AC.Lock) ∈
      (tr.state y (j + 1)).ac.locks := by
    rw [← hrun.projAC_state_at hyj1, Trace.state_succ_of_call tr.projAC hu.1]
    exact hl
  have hPDj : ellj.frame.Anc P D := AC.anc_tree_of_anc_U hU hΦj hΦjU hPj hPD hDt
  have hvaj : ellj.frame.viableAncestor P = P := by rw [hfrj]; exact hvak j le_rfl hji.le
  have hbase : Compose.FastFloorAtWith frameOf tr y (j + 1) P r (r + 2) := by
    have hB := (AC.viableAncestor_anc hΦj hDt).1
    have hPB := AC.anc_viableAncestor_of_floor hΦj hPj hvaj hDt hPDj
    rw [hfrj] at hB hPB
    have hst (k : Nat) (hk : k ≤ j + 1) :
        (tr.upTo (tr.time (j + 1))).state y k = tr.state y k :=
      Trace.upTo_state tr y fun q hq => hmono (by omega)
    obtain ⟨hB', hPB'⟩ := Compose.floor_frame_transport_core
      (hrun.upTo (hrun.time_nonneg (j + 1))) hyj1 (Nat.le_succ j)
      (by rw [hst _ le_rfl]; exact (hPk (j + 1) (Nat.le_succ j) hji).1)
      (by rw [hst j (Nat.le_succ j)]; exact hB)
      (by rw [hst j (Nat.le_succ j)]; exact hPB)
    rw [hst _ le_rfl] at hB' hPB'
    exact ⟨_, hl1, rfl, rfl, he, _, hB', by rw [hfrj], hPB'⟩
  have hfloor : ∀ k, j + 1 ≤ k → k ≤ i →
      Compose.FastFloorAtWith frameOf tr y k P r (r + 2) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact fun _ => hbase
    | succ k hjk ih =>
      intro hki
      have hkt := hmono (show k ≤ i by omega)
      have hyk := hrun.antitone hkt hy
      have hk0 := hrun.time_nonneg k
      have hsk : sp.slot (tr.time k) ≤ r + 2 :=
        (AC.slot_mono sp hk0 hkt).trans hslot
      refine fastFloor_step_at hrun hyk (ih (by omega)) hsk (hPk k (by omega) (by omega)).1
        (hPk (k + 1) (by omega) hki).1 (hvak k (by omega) (by omega)) ?_
      by_cases hs : (sp.slot (tr.time k) : Int) - 1 ≤ r
      · exact Or.inl hs
      have hslk : sp.slot (tr.time k) = r + 2 := by omega
      have hkb := hkt.trans hib
      refine Or.inr (Compose.Growing.unlockKeeps_of_voteCompat_at_core hrun hnc hK.facts hyk
        subset_rfl ?_ (hPk k (by omega) (by omega)).1 ?_)
      · rw [hslk, show r + 2 - 1 = r + 1 by omega]
        exact hK.cs2 (r + 1) hgr (by
          have := (AC.ts_le_iff_le_slot sp hk0 ((r + 1 : Nat) : Int)).2 (by omega)
          linarith) (tr.time k) hk0 hkb
      · intro x hx k' hk' e' hv hes
        obtain ⟨hx', hv'⟩ := Compose.Growing.hVoteAt_iff.1 hv
        exact (hext x k' e' hx' hv' (by omega) (hmono (by omega))).voteCompat
  obtain ⟨l, hl, hls, hlf, hle, B, hB, hBr, hPB⟩ := hfloor i hji le_rfl
  have hfri := hrun.frame_of_projAC_at hy hc
  obtain ⟨hΦi, hΦiU⟩ := hrun.frameIn_at hnc hy hc
  obtain ⟨hPti, hrooti, hvi⟩ := hPk i hji.le le_rfl
  rw [← hfri] at hPti hrooti hvi
  have hB' : B ∈ ell.frame.tree := by rw [hfri]; exact hB
  have hPB' : ell.frame.Anc P B := by rw [hfri]; exact hPB
  have hPv : P ∈ ell.frame.viableTree ell.frame.tree := ⟨hPti, hrooti, P, hPti, hvi, .refl⟩
  have hvaP := AC.viableAncestor_self hΦi hPti (Or.inl hPv)
  have hPV := AC.anc_viableAncestor_of_floor hΦi hPti hvaP hB' hPB'
  have hVv : ell.frame.viableAncestor B ∈ ell.frame.viableTree ell.frame.tree := by
    rcases (AC.viableAncestor_spec hΦi hB').2.1 with hroot | hvt
    · rw [Anc.antisymm hΦi.coherent (hroot.trans hrooti) hPV]
      exact hPv
    · exact hvt
  have hl' : l ∈ (tr.projAC.state y i).locks := by
    rw [hrun.projAC_state_at hy]; exact hl
  refine ⟨_, ⟨hVv, { l with block := (ell.frame.viableAncestor B).root },
    ⟨l, hl', B, hB', hBr, ?_, rfl⟩, rfl, hlf, ?_⟩, hPV.mono hΦiU⟩
  · change sp.slot (tr.time i) ≤ l.expiry
    omega
  · change sp.slot (tr.time i) ≤ l.slot + 2
    omega

end Consensus.Goldilocks.Healing.Growing.Core

end
