module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Interfaces -- shake: keep (companion interface export)
public import AvailableChainFGSARun.Proofs.NamedDelivery -- shake: keep (source declarations)
public import AvailableChainKitFG.StoreSafety -- shake: keep (no-evidence finality API)
public import AvailableChainGeneric.Proofs.Pure.BlockOrder

public section

namespace AvailableChain.FGSA.Run

open SimplexFG KitFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- Named scope has a delivery witness except for genesis. Genesis can be
held in the initial store without any emitted or delivered proposal. -/
theorem wcg_finalityBlock_of_scope {D : FGBlock (Fin p.n)}
    (hscope : RootBlockInRun p c E rho (eraseFG D)) (hne : D ≠ .genesis) :
    FinalityBlock p c E rho D := by
  obtain ⟨A, hA_scope, hA⟩ := hscope
  obtain ⟨B, hB, hAB⟩ := hA_scope
  have hDB : Block.Preceq (eraseFG D) B.erase := by
    rw [← hA]
    exact named_preceq_erase hAB
  rcases hB with ⟨x, o, t, hd, ho⟩ | ⟨x, _, i, hB⟩
  · exact ⟨o, B, ho, Or.inr ⟨x, t, hd⟩, hDB⟩
  · have hBg : B ≠ .genesis := by
      intro hg
      subst B
      have he : eraseFG D = .genesis := by
        cases hd : eraseFG D with
        | genesis => rfl
        | node P s b =>
          rw [hd] at hDB
          change false = true at hDB
          exact Bool.noConfusion hDB
      exact hne (eraseFG_eq_genesis.mp he)
    obtain ⟨j, o, t, _, hd, ho⟩ := stored_named_body_delivery E rho i x hB hBg
    exact ⟨o, B, ho, Or.inr ⟨x, t, List.mem_of_getElem? hd⟩, hDB⟩

/-- Whole-run accountability covers named scope. Empty genesis evidence is
excluded arithmetically; every other scoped carrier has a public witness. -/
theorem wcg_scope_no_evidence
    (ha : FinalitySlashableBound p c E rho)
    (D W : FGBlock (Fin p.n))
    (hD : RootBlockInRun p c E rho (eraseFG D))
    (hW : RootBlockInRun p c E rho (eraseFG W)) :
    ¬ HasSlashableWeightBetween p.E (chainRows D) (chainRows W) := by
  have hcap : p.E.weightOf ∅ + p.E.totalWeight < 2 * p.E.q := by
    have hz : p.E.weightOf ∅ = 0 := by change (∑ _ ∈ (∅ : Finset (Fin p.n)), (1 : Nat)) = 0; simp
    have ht : p.E.totalWeight = p.n := by change (∑ _ : Fin p.n, (1 : Nat)) = _; simp
    have hq : p.E.q = (2 * p.n + 2) / 3 := by
      change (2 * p.E.totalWeight + 2) / 3 = _
      rw [ht]
    rw [hz, ht, hq]
    have hn := p.nPos
    omega
  by_cases hd : D = .genesis
  · subst D
    apply no_slashableWeight_of_fault_bound p.E ∅ _ _ hcap
    intro a ha
    change a ∈ (∅ : Finset (Row (Fin p.n))) at ha
    exact (Finset.notMem_empty a ha).elim
  by_cases hw : W = .genesis
  · subst W
    apply no_slashableWeight_of_fault_bound p.E ∅ _ _ hcap
    intro a _ b hb
    change b ∈ (∅ : Finset (Row (Fin p.n))) at hb
    exact (Finset.notMem_empty b hb).elim
  exact ha D W (wcg_finalityBlock_of_scope hD hd) (wcg_finalityBlock_of_scope hW hw)

/-- Review finding 3: the directional no-evidence premise is sufficient.
There is no continuation fault-count premise in this argument. -/
theorem wcg_lowFinalized_of_no_evidence {w : HealingWitness} {iStar : Nat}
    (hroots : NamedRootCollisionFree p c E rho)
    (hs : WCSeed p c E rho w iStar)
    (hno : ∀ D W : FGBlock (Fin p.n),
      RootBlockInRun p c E rho (eraseFG D) →
      RootBlockInRun p c E rho (eraseFG W) →
      (finalityView p D).h_F ≤ w.M → (heightView p W).h = w.M + 1 →
      ¬ HasSlashableWeightBetween p.E (chainRows D) (chainRows W))
    (D : FGBlock (Fin p.n)) (hD : RootBlockInRun p c E rho (eraseFG D))
    (hlow : (finalityView p D).h_F ≤ w.M) :
    Block.Preceq (eraseFG (finalityView p D).F) w.CStar ∧
      Block.Preceq (eraseFG (finalityView p D).F) w.QStar := by
  obtain ⟨W, hW, hheight, hscope, _⟩ := hs.carrier
  have hf := finalized_preceq_of_no_evidence p.E (heightView p) (finalityView p)
    (fgCertificateLaws p) D W (rootInjectiveOn_run E rho hroots hD hscope)
    (by rw [hheight]; exact Nat.lt_succ_of_le hlow)
    (hno D W hD hscope hlow hheight)
  have hC : Block.Preceq (eraseFG (finalityView p D).F) w.CStar :=
    hW ▸ eraseFG_preceq hf
  exact ⟨hC, Gen.Pure.block_preceq_trans hC hs.sourcePrefix⟩

/-- Low finalizations lie below the healing path under the public slashing
bound. No continuation one-third or honest-intersection bound is used. -/
theorem wcg_lowFinalized {w : HealingWitness} {iStar : Nat}
    (hroots : NamedRootCollisionFree p c E rho)
    (ha : FinalitySlashableBound p c E rho)
    (hs : WCSeed p c E rho w iStar)
    (D X : FGBlock (Fin p.n)) (h : Height)
    (hf : WCFinalizedOccurrence p c E rho D X h) (hlow : h ≤ w.M) :
    Block.Preceq (eraseFG X) w.CStar ∧ Block.Preceq (eraseFG X) w.QStar := by
  have hlow' : (finalityView p D).h_F ≤ w.M := hf.height.trans_le hlow
  have result := wcg_lowFinalized_of_no_evidence hroots hs
    (fun D W hD hW _ _ => wcg_scope_no_evidence ha D W hD hW) D hf.scope hlow'
  rwa [hf.value] at result

/-- WC plan §§5, 6.3; DC the historical carrier keeps the exact finality key. -/
theorem wcg_finalizedOccurrence : WCFinalizedOccurrenceStatement p c E rho := by
  intro hscopeRows hnoslash D X h hscope hF hh
  refine ⟨hF, hh, hscope, ?_, ?_, hscopeRows D hscope, hnoslash⟩
  · intro hz
    exact hF.symm.trans ((fgCertificateLaws p).finalized_zero D (hh.trans hz))
  · intro hn
    simpa only [hF, hh] using
      (fgCertificateLaws p).finality_origin D (fun hz => hn (hh.symm.trans hz))

end AvailableChain.FGSA.Run
end
