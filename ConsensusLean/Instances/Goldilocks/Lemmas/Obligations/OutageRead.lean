module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyEffective
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record

public section

/-! # Conditional outage read-prefix and record coverage -/

namespace Consensus.Goldilocks.Obligations

variable {sp : AC.ACParams} {FGP : Type} {U : Set (AC.Blk sp.n FGP)}

variable {ro : AC.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)}

/-- An update above the prefix establishes record cover whether it is accepted or vetoed
by a compatible live lock. One explicit interval then preserves the post-update cover. -/
theorem late_reader_record_cover
    {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {B : AC.Blk sp.n (List (FG.Att sp.n))} {c i : Nat}
    (hci : c < i) {s : Nat}
    {ell : ACLabel (AC.goldilocksAC sp (List (FG.Att sp.n)) ro)}
    (hu : AC.UpdateAt tr.projAC y c s ell)
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (hR : AC.ResultAt tr.projAC y c s C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hlocksB : ∀ L ∈ AC.liveLockBlocks sp (tr.state y c).ac.locks ell.frame (tr.time c),
      Compatible (tr.HonestBlocks H) L B)
    (hint : EffectiveRecordInterval tr H y (c + 1) i B) :
    Anc (tr.HonestBlocks H) B ((AC.lookup (Node.frame (tr.state y i))
      (tr.state y i).ac.latestConfirmed).getD (tr.state y i).fg.F) := by
  have hr := (Compose.goldilocks_ac_projection_from hrun hnc).localRun
  obtain ⟨hΦ, hΦU⟩ := AC.frameIn_of_callAt hr hy hu.1
  have hst := Compose.projAC_state hrun.toLocalRun hy
  have hframe := Compose.frame_of_projAC hrun hy hu.1
  obtain ⟨ellR, huR, hCR, -⟩ := hR
  have heqR : ellR = ell := Option.some.inj (huR.1.2.symm.trans hu.1.2)
  subst ellR
  have hCt : C ∈ ell.frame.tree := (AC.deepest_mem hCR).1.1
  have hpost : Anc (tr.HonestBlocks H) B
      ((AC.lookup ell.frame (tr.projAC.post c).latestConfirmed).getD ell.frame.F) := by
    by_cases hnv : AC.conflictsWithLock sp (tr.projAC.state y c).locks ell.frame (tr.time c) C
    · obtain ⟨L, hL, hCL⟩ := AC.exists_of_conflictsWithLock hnv
      have hconflict : ¬ Compatible (tr.HonestBlocks H) C L := by
        rintro (h | h)
        · exact hCL (Or.inl (AC.anc_tree_of_anc_U hr.coherent hΦ hΦU hCt h hL.1))
        · exact hCL (Or.inr (AC.anc_tree_of_anc_U hr.coherent hΦ hΦU hL.1 h hCt))
      have hBL := cover_of_veto hr.coherent hBC (hlocksB L (by simpa only [hst] using hL))
        hconflict
      obtain ⟨Φp, tp, hreach, -, hok⟩ := Compose.pre_reachable hr hy hu.1
      obtain ⟨hin, -, hinv⟩ := AC.lockInv_of_reachable hr.coherent (hrun.vstart _) hreach
      have hinv' := hinv.callOK hr.coherent hin hok
      obtain ⟨E, hE, hEr, hLE⟩ := hinv'.liveBlock_anc hr.coherent hΦ hΦU hL
      have hlookup : AC.lookup ell.frame (tr.projAC.state y c).latestConfirmed = some E := by
        cases he : AC.lookup ell.frame (tr.projAC.state y c).latestConfirmed with
        | none => exact False.elim (AC.lookup_eq_none he ⟨E, hE, hEr⟩)
        | some E' => exact congrArg some (hΦ.coherent.1 (AC.lookup_eq_some he).1 hE
            ((AC.lookup_eq_some he).2.trans hEr.symm))
      rw [post_of_update hr hy hu]
      unfold AC.updateConfirmation
      simp only [hCR]
      change AC.conflictsWithLock sp (tr.projAC.state y c).locks ell.frame
        (tr.projAC.time c) C at hnv
      rw [ite_eq_left hnv]
      change Anc (tr.HonestBlocks H) B
        ((AC.lookup ell.frame (tr.projAC.state y c).latestConfirmed).getD ell.frame.F)
      rw [hlookup]
      exact hBL.trans (hLE.mono hΦU)
    · exact hBC.trans ((effective_record_after_update hr hy hu ⟨ell, huR, hCR, rfl⟩ hnv).mono hΦU)
  have hwritten := hpost
  rw [← tr.projAC.state_succ_of_call hu.1, hst, hframe] at hwritten
  have hcall : tr.CallAt y c (.ac ell) := Compose.projAC_callAt.mp hu.1
  have hfg : (tr.state y (c + 1)).fg = (tr.state y c).fg := by
    rw [tr.state_succ_of_call hcall]
    exact (hrun.cutLaw y hy c (.ac ell) hcall).2.2.1
  apply effective_record_of_interval hrun hnc hy (Nat.succ_le_of_lt hci) hint
  change Anc (tr.HonestBlocks H) B
    ((AC.lookup (Node.frame (tr.state y (c + 1)))
      (tr.state y (c + 1)).ac.latestConfirmed).getD (Node.frame (tr.state y (c + 1))).F)
  simpa only [Node.frame, hfg] using hwritten

end Consensus.Goldilocks.Obligations
