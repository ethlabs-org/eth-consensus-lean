module
public import AvailableChainFGCompose.Proofs.SafetyStore
public import AvailableChainFGCompose.Statements.SafetyClaims
public import AvailableChainKitFG.AccountableCore

public section

/-! Generic accountable finality and agreement (fields 3, 4 and 5). Root
identity comes only from the scoped-roots premise and scope memberships. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In}
variable {n : Nat} {Base Proposal Wire : Type}
variable {R : FGCoreReads P n Base Proposal Wire} {S : FGSafetyReads P n Wire}
variable {Ef : Electorate (Fin n)} {H : FGHeightView (Fin n)} {f : FGFinalityView (Fin n)}
variable [DecidableEq V] {E : Generic.Env V} {rho : V2.D.Run V P}
variable {Good : P.State → Prop} {Q : Block → Prop}

/-- A block with a non-genesis finalized target has a non-genesis parent. -/
private theorem safety_parent_ne (K : FGCertificateLaws Ef H f) {B : FGBlock (Fin n)}
    (h : (f B).F ≠ .genesis) : B.parent ≠ .genesis := by
  intro hg
  have hp := finalized_preceq_parent_of_certificate Ef H f K B
  rw [hg] at hp
  exact h (preceq_genesis.mp hp)

/-- Two run blocks give slashable weight or compatible finalized targets. -/
theorem safety_runBlock_accountable (K : FGCertificateLaws Ef H f)
    (N : FGSafetyScopeLaws R S E rho Q) (hr : safetyScopedRoots R Q)
    {A B : FGBlock (Fin n)} (hA : safetyRunBlock R S E rho A)
    (hB : safetyRunBlock R S E rho B) :
    HasSlashableWeightBetween Ef (chainRows A) (chainRows B) ∨
      FGBlock.compatible (f A).F (f B).F = true := by
  by_cases ha : (f A).F = .genesis
  · right
    rw [ha]
    exact Bool.or_eq_true_iff.mpr (Or.inl (genesis_preceq _))
  by_cases hb : (f B).F = .genesis
  · right
    rw [hb]
    exact Bool.or_eq_true_iff.mpr (Or.inr (genesis_preceq _))
  exact slashableWeight_or_finalized_compatible_of_parent_roots Ef H f K A B
    (hr A.parent B.parent (N.parent_scope A hA (safety_parent_ne K ha))
      (N.parent_scope B hB (safety_parent_ne K hb)))

/-- Two stores in scope give slashable weight between their row pools or
compatible finalized values. -/
theorem safety_store_accountable (K : FGCertificateLaws Ef H f) (hr : safetyScopedRoots R Q)
    {st st' : Store (Fin n)} (hs : FGStoreInvariant H f st) (hs' : FGStoreInvariant H f st')
    (hQ : ∀ B ∈ st.TF, Q (R.erase B)) (hQ' : ∀ B ∈ st'.TF, Q (R.erase B)) :
    HasSlashableWeightBetween Ef (st.TF.biUnion chainRows) (st'.TF.biUnion chainRows) ∨
      FGBlock.compatible st.F st'.F = true := by
  obtain ⟨A, hA, hAF⟩ := hs.Fcar
  obtain ⟨B, hB, hBF⟩ := hs'.Fcar
  rcases slashableWeight_or_finalized_compatible_of_certificate Ef H f K A B
      (hr A B (hQ A hA) (hQ' B hB)) with hev | hc
  · obtain ⟨T, hw, he⟩ := hev
    refine Or.inl ⟨T, hw, fun i hi => ?_⟩
    obtain ⟨a, ha, b, hb, hai, hbi, hab⟩ := he i hi
    exact ⟨a, Finset.mem_biUnion.mpr ⟨A, hA, ha⟩,
      b, Finset.mem_biUnion.mpr ⟨B, hB, hb⟩, hai, hbi, hab⟩
  · exact Or.inr (hAF ▸ hBF ▸ hc)

/-- Under the run bound, two stores whose blocks are run blocks agree. -/
theorem safety_store_agreement (K : FGCertificateLaws Ef H f)
    (N : FGSafetyScopeLaws R S E rho Q) (hr : safetyScopedRoots R Q)
    (hb : safetyBound R S Ef E rho)
    {st st' : Store (Fin n)} (hs : FGStoreInvariant H f st) (hs' : FGStoreInvariant H f st')
    (hc : ∀ B ∈ st.TF, B ≠ .genesis → safetyRunBlock R S E rho B)
    (hc' : ∀ B ∈ st'.TF, B ≠ .genesis → safetyRunBlock R S E rho B) :
    FGBlock.compatible st.F st'.F = true := by
  obtain ⟨A, hA, hAF⟩ := hs.Fcar
  obtain ⟨B, hB, hBF⟩ := hs'.Fcar
  by_cases ha : (f A).F = .genesis
  · rw [← hAF, ha]
    exact Bool.or_eq_true_iff.mpr (Or.inl (genesis_preceq _))
  by_cases hb' : (f B).F = .genesis
  · rw [← hBF, hb']
    exact Bool.or_eq_true_iff.mpr (Or.inr (genesis_preceq _))
  have hA' : A ≠ .genesis := fun h => safety_parent_ne K ha (by rw [h]; rfl)
  have hB' : B ≠ .genesis := fun h => safety_parent_ne K hb' (by rw [h]; rfl)
  have hrA := hc A hA hA'
  have hrB := hc' B hB hB'
  have hcomp := (safety_runBlock_accountable K N hr hrA hrB).resolve_left (hb A B hrA hrB)
  exact hAF ▸ hBF ▸ hcomp

variable (R S Ef H f E rho Good Q)

/-- Field 3. All three accountable observation clauses. -/
theorem safety_run_accountable
    (C : FGCoreLaws R) (L : FGSafetyStoreLaws R S H f Good)
    (K : FGCertificateLaws Ef H f) (N : FGSafetyScopeLaws R S E rho Q)
    (hr : safetyScopedRoots R Q) : SafetyWholeAccountable R S Ef f E rho := by
  refine ⟨fun A B T T' _ _ hA hB hfA hfB => ?_, fun x hx y hy i j => ?_,
    fun x hx y hy t t' => ?_⟩
  · exact (safety_runBlock_accountable K N hr hA hB).imp id (fun hc => hfA.1 ▸ hfB.1 ▸ hc)
  · exact safety_store_accountable K hr (safety_invariant_stateBefore L E rho i x)
      (safety_invariant_stateBefore L E rho j y)
      (fun B hB => safety_stored_scope C L N i x hx B hB)
      (fun B hB => safety_stored_scope C L N j y hy B hB)
  · exact safety_store_accountable K hr (safety_invariant_readAt L E rho t x)
      (safety_invariant_readAt L E rho t' y)
      (fun B hB => safety_read_scope C L N t x hx B hB)
      (fun B hB => safety_read_scope C L N t' y hy B hB)

/-- Field 4. Agreement of run blocks and of honest time reads. -/
theorem safety_run_agreement
    (C : FGCoreLaws R) (L : FGSafetyStoreLaws R S H f Good)
    (K : FGCertificateLaws Ef H f) (N : FGSafetyScopeLaws R S E rho Q)
    (hr : safetyScopedRoots R Q) (hb : safetyBound R S Ef E rho) :
    SafetyWholeAgreement R S f E rho := by
  refine ⟨fun A B T T' _ _ hA hB hfA hfB => ?_, fun x _ y _ t t' => ?_⟩
  · exact hfA.1 ▸ hfB.1 ▸
      (safety_runBlock_accountable K N hr hA hB).resolve_left (hb A B hA hB)
  · exact safety_store_agreement K N hr hb (safety_invariant_readAt L E rho t x)
      (safety_invariant_readAt L E rho t' y)
      (fun B hB hne => safety_read_runBlock C L E rho t x B hB hne)
      (fun B hB hne => safety_read_runBlock C L E rho t' y B hB hne)

/-- Field 5. Agreement of any two event prefixes, at all nodes. -/
theorem safety_event_agreement
    (C : FGCoreLaws R) (L : FGSafetyStoreLaws R S H f Good)
    (K : FGCertificateLaws Ef H f) (N : FGSafetyScopeLaws R S E rho Q)
    (hr : safetyScopedRoots R Q) (hb : safetyBound R S Ef E rho)
    (i j : Nat) (x y : V) :
    FGBlock.compatible (R.core (V2.D.Run.stateBefore E rho i x)).fg.F
      (R.core (V2.D.Run.stateBefore E rho j y)).fg.F = true :=
  safety_store_agreement K N hr hb (safety_invariant_stateBefore L E rho i x)
    (safety_invariant_stateBefore L E rho j y)
    (fun B hB hne => safety_stored_runBlock C L E rho i x B hB hne)
    (fun B hB hne => safety_stored_runBlock C L E rho j y B hB hne)

end AvailableChain.FGCompose
end
