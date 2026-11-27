module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Update
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FastExpiry
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Frame-independent fast-update facts over the run core -/

namespace Consensus.Goldilocks.Healing.Growing.Core

open AC (ACParams ReplayOrder Payload)

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

end Consensus.Goldilocks.Healing.Growing.Core

end
