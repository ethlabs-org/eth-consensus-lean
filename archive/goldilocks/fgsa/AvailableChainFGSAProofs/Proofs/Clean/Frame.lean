module
public import AvailableChainFGSA.Proofs.StoreLaws
public import AvailableChainFGSAProofs.Proofs.Clean.Chain
public import AvailableChainFGSAProofs.Proofs.Shared.Channels

public section

/-! P3 §8.7 F2.2; bp02 §§3.1–3.4. The Clean frame core takes the current
history and state as premises. It does not assemble a state from history. -/

namespace AvailableChain.FGSA.Run

variable {ΔF : Time}
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- ROOT-DIGEST W2b. P3 §8.7 F2.2; bp02 §§3.1–3.4. Class B, given-state Clean frame core.
DC counterparts: ChainState/FGRootWitness.lean:327,493 (root origins) and
ChainState/Chain.lean:414,447,460,475 (invariant pattern). DC has no exact
contest/domain bundle. The differences are intentional: the FJ band prevents
root descent (TS/spec/fgsa-protocol.tex:2557–2571), and the given state avoids
the action/state cycle (TS/log.md:1622,1653; lead Q4, 2026-10-01).
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanFrame_of_state (b₀ : Time) :
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i, i ≤ timeIdx rho b₀ → CleanHist p c E rho i → CleanState p c E rho i →
  ∀ v, v ∈ rho.honest →
    let st := storeAt p c E rho i v
    (FGSA.controls p st).contest = false ∧
    BelowLabel p c E rho i (labelBoundAt p c rho i) (eraseFG (FGSA.controls p st).Z) ∧
    (∀ B ∈ st.fg.TF,
      BelowLabel p c E rho i (labelBoundAt p c rho i) (eraseFG B) →
      Block.Preceq (eraseFG B) (eraseFG (FGSA.controls p st).Z) ∨
      Block.Preceq (eraseFG B) (eraseFG st.fg.F) ∨
      (FGBlock.Preceq st.fg.F (FGSA.controls p st).Z ∧
        FGBlock.Preceq (FGSA.controls p st).Z B ∧ B ∈ FGSA.fullTree p st)) := by
  intro hbase _ hf _hsrc i _ hh hs v hv
  let st := storeAt p c E rho i v
  have hinv := (hs.store v hv).fg
  have liftCompat : ∀ A B : FGBlock (Fin p.n),
      Block.Compatible (eraseFG A) (eraseFG B) →
      FGBlock.Preceq A B ∨ FGBlock.Preceq B A := by
    intro A B hab
    rcases Bool.or_eq_true_iff.mp hab with hab | hab
    · exact Or.inl (eraseFG_preceq_iff.mp hab)
    · exact Or.inr (eraseFG_preceq_iff.mp hab)
  have hcert := hs.sources.2
  rw [CleanCertSources_def] at hcert
  simp only [certified_def, heightView_eq_simplex p,
    KitFG.simplexHeightView_def, KitFG.heightOf_def] at hcert
  have hnOld : (KitFG.storeControlsView (heightView p) st.fg).contest = false := by
    apply KitFG.storeFrameView_noContest_of_crossed_of_inv
      p.E (heightView p) (fgCertificateLaws p).height (finalityView p) st.fg hinv
        (fgJustificationLaws p)
    intro W hW U hU hlt
    simp only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def] at hlt ⊢
    let e := (derive p.E p.cfg U).T_h
    by_cases hg : e = .genesis
    · right
      change FGBlock.Preceq e st.fg.J
      rw [hg]
      exact KitFG.genesis_preceq st.fg.J
    obtain ⟨j, y, r, a, C, _, _, _, _, heC, hC⟩ :=
      hcert v W e hv hW ⟨U, hU, Or.inr (Or.inr ⟨rfl, hlt⟩)⟩ hg
    exact liftCompat st.fg.J e (cleanHist_belowLabel_compatible hh (hs.fOrigin v).2
      (belowLabel_of_preceq (eraseFG_preceq heC) hC))
  have hn : (FGSA.controls p st).contest = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    have ho := KitFG.treeStoreControlsView_contest_imp (heightView p) st.fg ht
    rw [hnOld] at ho
    cases ho
  have hZ : BelowLabel p c E rho i (labelBoundAt p c rho i)
      (eraseFG (FGSA.controls p st).Z) := by
    change BelowLabel p c E rho i _
      (eraseFG (if (FGSA.controls p st).rootIsJ then st.fg.J else st.fg.F))
    cases (FGSA.controls p st).rootIsJ
    · exact (hs.fOrigin v).1
    · exact (hs.fOrigin v).2
  refine ⟨hn, hZ, ?_⟩
  intro B hB hb
  have hrows := hs.sources.1
  rw [CleanRowSources_def] at hrows
  have hcp := fgsa_cpCompat_of_scopedFrame p c E rho hf.store hf.strat i v B hv (by
    intro y r a e ha he heScope
    obtain ⟨j, hj, hrow⟩ := ha
    obtain ⟨C, hSource, heq, hpre, hc⟩ := hrows j y r a _ hj hrow he
    have heC : e = (derive p.E p.cfg C).T_h :=
      rootScope_eq hbase.base.idealization heScope
        (rootScope_ancestor (rootScope_source hrow.1 hSource) (KitFG.entry_preceq p.E p.cfg C))
        (congrArg Prod.snd heq)
    exact liftCompat e B (cleanHist_belowLabel_compatible hh
      (belowLabel_of_preceq (eraseFG_preceq (heC ▸ hpre)) hc) hb))
  rcases hcp.2.1 with hFB | hBF
  · rcases hcp.2.2.2.1 hB hFB with hBZ | hD
    · exact Or.inl (eraseFG_preceq hBZ)
    · right; right
      have hd := (KitFG.mem_filteredFromView
        (heightView p) (FGSA.controls p st) st.fg.TF B).1 hD
      refine ⟨?_, hd.2.2.1, ?_⟩
      · change FGBlock.Preceq st.fg.F
          (if (FGSA.controls p st).rootIsJ then st.fg.J else st.fg.F)
        cases (FGSA.controls p st).rootIsJ
        · exact KitFG.preceq_refl _
        · exact hinv.FJ
      · exact hD
  · exact Or.inr (Or.inl (eraseFG_preceq hBF))

end AvailableChain.FGSA.Run
end
