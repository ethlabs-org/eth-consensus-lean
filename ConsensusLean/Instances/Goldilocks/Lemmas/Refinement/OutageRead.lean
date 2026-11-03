module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyEffective
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record

public section

/-! # Conditional outage read-prefix and record coverage -/

namespace Consensus.Goldilocks.Refinement

variable {sp : SA.SAParams} {FGP : Type} {U : Set (SA.Blk sp.n FGP)}

variable {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}

/-- An update above the prefix establishes record cover whether it is accepted or vetoed
by a compatible live lock. One explicit interval then preserves the post-update cover. -/
theorem late_reader_record_cover
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {B : SA.Blk sp.n (List (FG.Att sp.n))} {c i : Nat}
    (hci : c < i) {s : Nat}
    {ell : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC y c s ell)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hR : SA.ResultAt tr.projAC y c s C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hlocksB : ∀ L ∈ SA.liveLockBlocks sp (tr.state y c).ac.locks ell.frame (tr.time c),
      Compatible (tr.HonestBlocks H) L B)
    (hint : EffectiveRecordInterval tr H y (c + 1) i B) :
    Anc (tr.HonestBlocks H) B ((SA.lookup (Node.frame (tr.state y i))
      (tr.state y i).ac.latestConfirmed).getD (tr.state y i).fg.F) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hu.1
  have hst := Compose.projAC_state hrun.toLocalRun hy
  have hframe := Compose.frame_of_projAC hrun hy hu.1
  obtain ⟨ellR, huR, hCR, -⟩ := hR
  have heqR : ellR = ell := Option.some.inj (huR.1.2.symm.trans hu.1.2)
  subst ellR
  have hCt : C ∈ ell.frame.tree := (SA.deepest_mem hCR).1.1
  have hpost : Anc (tr.HonestBlocks H) B
      ((SA.lookup ell.frame (tr.projAC.post c).latestConfirmed).getD ell.frame.F) := by
    by_cases hnv : SA.conflictsWithLock sp (tr.projAC.state y c).locks ell.frame (tr.time c) C
    · obtain ⟨L, hL, hCL⟩ := hnv
      have hconflict : ¬ Compatible (tr.HonestBlocks H) C L := by
        rintro (h | h)
        · exact hCL (Or.inl (SA.anc_tree_of_anc_U hr.coherent hΦ hΦU hCt h hL.1))
        · exact hCL (Or.inr (SA.anc_tree_of_anc_U hr.coherent hΦ hΦU hL.1 h hCt))
      have hBL := cover_of_veto hr.coherent hBC (hlocksB L (by simpa only [hst] using hL))
        hconflict
      obtain ⟨Φp, tp, hreach, -, hok⟩ := Compose.pre_reachable hr hy hu.1
      obtain ⟨hin, -, hinv⟩ := SA.lockInv_of_reachable hr.coherent hreach
      have hinv' := hinv.callOK hr.coherent hin hok
      obtain ⟨E, hE, hEr, hLE⟩ := hinv'.liveBlock_anc hr.coherent hΦ hΦU hL
      have hlookup : SA.lookup ell.frame (tr.projAC.state y c).latestConfirmed = some E := by
        cases he : SA.lookup ell.frame (tr.projAC.state y c).latestConfirmed with
        | none => exact False.elim (SA.lookup_eq_none he ⟨E, hE, hEr⟩)
        | some E' => exact congrArg some (hΦ.coherent.1 (SA.lookup_eq_some he).1 hE
            ((SA.lookup_eq_some he).2.trans hEr.symm))
      rw [post_of_update hr hy hu]
      unfold SA.updateConfirmation
      simp only [hCR]
      rw [ite_eq_left ⟨L, hL, hCL⟩]
      change Anc (tr.HonestBlocks H) B
        ((SA.lookup ell.frame (tr.projAC.state y c).latestConfirmed).getD ell.frame.F)
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
    ((SA.lookup (Node.frame (tr.state y (c + 1)))
      (tr.state y (c + 1)).ac.latestConfirmed).getD (Node.frame (tr.state y (c + 1))).F)
  simpa only [Node.frame, hfg] using hwritten

end Consensus.Goldilocks.Refinement
