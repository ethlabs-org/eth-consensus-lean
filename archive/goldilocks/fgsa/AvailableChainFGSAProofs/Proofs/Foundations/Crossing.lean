module
public import AvailableChainFGSAProofs.Proofs.Foundations.Accountable

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- ROOT-DIGEST W2b. The strict finality comparison uses observed parent scope. -/
theorem fgsa_finalLock_of_bound (hroots : NamedRootCollisionFree p c E rho)
    (hb : FGSASlashableBound p c E rho) (K W : FGBlock (Fin p.n))
    (hK : FinalityRunBlock p c E rho K) (hW : FinalityRunBlock p c E rho W)
    (hh : (finalityView p K).h_F < (derive p.E p.cfg W).h) :
    FGBlock.Preceq (finalityView p K).F W := by
  by_cases hg : (finalityView p K).F = .genesis
  · rw [hg]; exact KitFG.genesis_preceq _
  have hKP : RootBlockInRun p c E rho (eraseFG K.parent) := by
    apply finalityRun_parent_scope p c E rho hK
    intro he
    have hp := KitFG.finalized_preceq_parent_of_certificate
      p.E (heightView p) (finalityView p) (fgCertificateLaws p) K
    rw [he] at hp
    exact hg (KitFG.preceq_genesis.mp hp)
  have hWP : RootBlockInRun p c E rho (eraseFG W.parent) := by
    by_cases he : W.parent = .genesis
    · rw [he]; exact rootScope_ancestor hKP (KitFG.genesis_preceq _)
    · exact finalityRun_parent_scope p c E rho hW he
  have he := KitFG.e1Weight_or_finalized_preceq_of_parent_roots
    p.E (heightView p) (finalityView p) (fgCertificateLaws p) K W
    (rootInjectiveOn_run E rho hroots hKP hWP)
    (by simpa only [heightView_eq_simplex, KitFG.simplexHeightView_def,
      KitFG.heightOf_def] using hh)
  exact (he.imp KitFG.hasSlashableWeightBetween_of_hasE1WeightBetween id).resolve_left
    ((FGSASlashableBound_def p c E rho).mp hb K W hK hW)

/-- ROOT-DIGEST W2b. Strict R-XING (01 §1.3), the run form of `fg.finalLock.v2`.
The height is that of an accepted certificate: `h_F` of a carrier `K` held by
`x` at `e` whose finalized checkpoint is the store's F (01:212). The claim holds
for EVERY such carrier; one F can have carriers of different `h_F` (genesis at
0 and at 1). The store invariant (`Fcar`) supplies one carrier. The held block
can be outside the active view. Identity transport precedes `FaultX`.
The retained _hee binder is unused: the proof compares any two event prefixes. -/
theorem fgsa_finalLock [Fintype V]
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hX : Gen.Pure.FaultX p.n (Gen.V2.Duty.faulty rho).card)
    (hU : V2.D.UnforgeableSignatures E rho)
    (x : V) (hx : x ∈ rho.honest) (e e' : Nat) (_hee : e ≤ e')
    (K : FGBlock (Fin p.n)) (hKe : K ∈ (storeAt p c E rho e x).fg.TF)
    (hKF : (finalityView p K).F = (storeAt p c E rho e x).fg.F)
    (y : V) (W : FGBlock (Fin p.n)) (hW : HeldAt p c E rho e' y W)
    (hheight : (finalityView p K).h_F < hOf p.E p.cfg W)
    (hroots : NamedRootCollisionFree p c E rho) :
    FGBlock.Preceq (storeAt p c E rho e x).fg.F W := by
  rcases fgsa_finalLock_ev (hroots := hroots) p c E rho e e' x y hx K W hKe hKF hW hheight with h
    | hev
  · exact h
  · have hc := fgsa_slashable_faulty_count p c E rho hL hU e e' x y K W ⟨hx, hKe⟩ hW hev
    have ht := hX.lt
    omega

/-- ROOT-DIGEST W2b. Erasure of strict R-XING to the base block order. -/
theorem fgsa_finalLock_erased [Fintype V]
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hX : Gen.Pure.FaultX p.n (Gen.V2.Duty.faulty rho).card)
    (hU : V2.D.UnforgeableSignatures E rho)
    (x : V) (hx : x ∈ rho.honest) (e e' : Nat) (hee : e ≤ e')
    (K : FGBlock (Fin p.n)) (hKe : K ∈ (storeAt p c E rho e x).fg.TF)
    (hKF : (finalityView p K).F = (storeAt p c E rho e x).fg.F)
    (y : V) (W : FGBlock (Fin p.n)) (hW : HeldAt p c E rho e' y W)
    (hheight : (finalityView p K).h_F < hOf p.E p.cfg W)
    (hroots : NamedRootCollisionFree p c E rho) :
    Block.Preceq (eraseFG (storeAt p c E rho e x).fg.F) (eraseFG W) :=
  eraseFG_preceq
    (fgsa_finalLock (hroots := hroots) p c E rho hL hX hU x hx e e' hee K hKe hKF y W hW hheight)

/-- ROOT-DIGEST W2b. R-XING with exactly the premises of `fgsa_finalLock (hroots := hroots)`.
The certificate laws give the crossing evidence directly on the active height view. -/
theorem fgsa_rXing [Fintype V] (hroots : NamedRootCollisionFree p c E rho)
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hX : Gen.Pure.FaultX p.n (Gen.V2.Duty.faulty rho).card)
    (hU : V2.D.UnforgeableSignatures E rho) : RXing p c E rho := by
  intro i i' x y K W hx hii hK hKF hW hh
  rcases KitFG.slashableWeight_or_finalized_preceq_of_certificate
    p.E (heightView p) (finalityView p) (fgCertificateLaws p) K W
      (rootInjectiveOn_run E rho hroots (rootScope_store hx hK) (rootScope_store hW.1 hW.2))
      hh with hev | h
  · have hc := fgsa_slashable_faulty_count p c E rho hL hU i i' x y K W ⟨hx, hK⟩ hW hev
    have ht := hX.lt
    omega
  · exact hKF ▸ h

end AvailableChain.FGSA.Run
end
