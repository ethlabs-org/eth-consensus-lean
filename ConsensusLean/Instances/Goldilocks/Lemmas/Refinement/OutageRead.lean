module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyEffective
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutageRead
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record

public section

/-! # Conditional outage read-prefix and record coverage -/

namespace Consensus.Goldilocks.Refinement

variable {sp : SA.SAParams} {FGP : Type} {U : Set (SA.Blk sp.n FGP)}

/-- Record and head coverage suffice at the read clock, even for a prefix below the frame. -/
theorem read_prefix_of_certificate (hU : Coherent U)
    {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {A : SA.SAState sp.n} {t : Time} {B : SA.Blk sp.n FGP}
    (hrec : Anc U B ((SA.lookup Φ A.latestConfirmed).getD Φ.F))
    (hhead : Anc U B (SA.acHead sp A Φ t)) :
    Anc U B (SA.acConfirmed sp A Φ t) :=
  SA.anc_acConfirmed_of_frame hU hΦ hΦU hrec hhead

/-- A covering live lock supplies both halves of the read certificate through the lock
invariant; no independent effective-record premise or heldness of the prefix is needed. -/
theorem read_prefix_of_live_lock (hU : Coherent U)
    {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {A : SA.SAState sp.n} (hinv : SA.LockInv U A Φ) {t : Time}
    {B C : SA.Blk sp.n FGP} (hBC : Anc U B C)
    (hC : C ∈ SA.liveLockBlocks sp A.locks Φ t) :
    Anc U B (SA.acConfirmed sp A Φ t) := by
  obtain ⟨E, hE, hEr, hCE⟩ := hinv.liveBlock_anc hU hΦ hΦU hC
  have hlookup : SA.lookup Φ A.latestConfirmed = some E := by
    cases he : SA.lookup Φ A.latestConfirmed with
    | none => exact False.elim (SA.lookup_eq_none he ⟨E, hE, hEr⟩)
    | some E' => exact congrArg some (hΦ.coherent.1 (SA.lookup_eq_some he).1 hE
        ((SA.lookup_eq_some he).2.trans hEr.symm))
  apply read_prefix_of_certificate hU hΦ hΦU
  · rw [hlookup]; exact hBC.trans (hCE.mono hΦU)
  · have hanchor := SA.anc_getAnchor hΦ (hinv.liveBlocks_chain hU hΦ hΦU (t := t))
    have hCH : Φ.Anc C (SA.acHead sp A Φ t) := by
      exact (hanchor.2 C (Or.inl hC)).trans
        (SA.anc_ghost (fun _ h => h.1) Φ.tree.ncard hanchor.1)
    exact hBC.trans (hCH.mono hΦU)

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

/-- A delivered honest batch supplies the head half of a late read; an update and its
record interval supply the other half. All service and compatibility duties are explicit. -/
theorem late_reader_prefix (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {w : Fin sp.n} (hw : w ∈ H) {i : Nat} {t : Time}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hs : (SA.latestView sp (tr.state w i).ac (Node.frame (tr.state w i)) t).2 = s)
    (hall : ∀ x ∈ H, ∀ k e, SA.VoteAt tr.projAC x k e → e.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B)
    (hBt : B ∈ (Node.frame (tr.state w i)).tree)
    (hdeliv : ∀ x ∈ H, ∀ k e, SA.VoteAt tr.projAC x k e → e.msg.slot = s →
      e.msg ∈ (tr.state w i).ac.pool s ∧
      ∃ Hd ∈ (Node.frame (tr.state w i)).tree, Hd.root = e.msg.head ∧
        (tr.state w i).ac.blockStamp Hd.root < ⊤)
    (hfb : tr.FaultBound H (sp.ts s + sp.Δ))
    (hanchor : Compatible (Node.frame (tr.state w i)).tree
      (SA.getAnchor sp (tr.state w i).ac (Node.frame (tr.state w i)) t) B)
    (hviab : B ∈ (Node.frame (tr.state w i)).viableTree (Node.frame (tr.state w i)).tree)
    {c : Nat} (hci : c < i) {s' : Nat}
    {ell : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC w c s' ell)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hR : SA.ResultAt tr.projAC w c s' C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hlocksB : ∀ L ∈ SA.liveLockBlocks sp (tr.state w c).ac.locks ell.frame (tr.time c),
      Compatible (tr.HonestBlocks H) L B)
    (hint : EffectiveRecordInterval tr H w (c + 1) i B) :
    Anc (tr.HonestBlocks H) B
      (SA.acConfirmed sp (tr.state w i).ac (Node.frame (tr.state w i)) t) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hΦ := Compose.frameOK_state hrun.toLocalRun hw i
  have hΦU : (Node.frame (tr.state w i)).tree ⊆ tr.HonestBlocks H := by
    intro X hX
    exact Compose.fg_tree_subset_honest hw i hX.1
  apply read_prefix_of_certificate hr.coherent hΦ hΦU
  · simpa only [Node.frame, Store.toFrame] using
      late_reader_record_cover hrun hnc hw hci hu hR hBC hlocksB hint
  · exact anc_acHead_of_current_certificate hΦ hΦU
      (Or.inr ⟨hBt, hanchor, Or.inr ⟨hviab,
        Compose.read_majority_of_honest_batch hrun hnc hw hs hall hBt hdeliv hfb⟩⟩)

end Consensus.Goldilocks.Refinement
