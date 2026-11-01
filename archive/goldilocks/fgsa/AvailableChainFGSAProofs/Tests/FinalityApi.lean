module
public import AvailableChainFGSAProofs.Proofs.Foundations.FinalityApi
-- shake: keep (adapter examples)

public section

namespace AvailableChain.FGSA.Run.Tests.FinalityApi

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)

-- Each example applies one proved body with exactly its d35 premises on W.
example (K W T₁ T₂ : SimplexFG.FGBlock (Fin p.n)) (h₁ h₂ : Nat) (hroot : KitFG.RootInjectiveOn K W)
    (hK : FinalityFinalizedAt p K T₁ h₁) (hW : FinalityFinalizedAt p W T₂ h₂) :
    SimplexFG.HasSlashableWeightBetween p.E (SimplexFG.chainRows K) (SimplexFG.chainRows W) ∨
      SimplexFG.FGBlock.compatible T₁ T₂ = true :=
  fgsa_apiPureAccountableClaim_body p K W T₁ T₂ h₁ h₂ hroot hK hW

example (K W T₁ T₂ : SimplexFG.FGBlock (Fin p.n)) (h₁ h₂ : Nat) (hroot : KitFG.RootInjectiveOn K W)
    (hK : FinalityFinalizedAt p K T₁ h₁) (hW : FinalityFinalizedAt p W T₂ h₂)
    (hb : ¬ SimplexFG.HasSlashableWeightBetween p.E
      (SimplexFG.chainRows K) (SimplexFG.chainRows W)) :
    SimplexFG.FGBlock.compatible T₁ T₂ = true :=
  fgsa_apiPureAgreementClaim_body p K W T₁ T₂ h₁ h₂ hroot hK hW hb

example (hs : FinalityExecution p c rho) : WholeRunAccountable p c E rho :=
  fgsa_apiWholeRunAccountableClaim_body p c E rho hroots hs

example (hs : FinalityExecution p c rho) (hb : FinalitySlashableBound p c E rho) :
    WholeRunAgreement p c E rho :=
  fgsa_apiWholeRunAgreementClaim_body p c E rho hroots hs hb

example (hs : FinalityExecution p c rho) (hb : FinalitySlashableBound p c E rho)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) (i j : Nat) :
    SimplexFG.FGBlock.compatible (storeAt p c E rho i x).fg.F
      (storeAt p c E rho j y).fg.F = true :=
  fgsa_apiEventPrefixAgreementClaim_body p c E rho hroots hs hb x hx y hy i j

example (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hcar : ∀ K, FinalityBlock p c E rho K →
      FinalityRowCarriage p c E rho (SimplexFG.chainRows K))
    (hC : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
    (hbot : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3) :
    FinalitySlashableBound p c E rho :=
  fgsa_apiFaultCountSlashableBoundClaim_body p c E rho hL hcar hC hbot

example (hs : rho.events.Pairwise (fun a b => a.key ≤ b.key))
    (x : V) (hx : x ∈ rho.honest) (t t' : Time) (htt : t ≤ t') :
    Block.Preceq (finalizedOut (V2.D.Run.readAt E rho t x))
      (finalizedOut (V2.D.Run.readAt E rho t' x)) :=
  fgsa_apiFinalizedMonotonicityRestartClaim_body p c E rho hs x hx t t' htt

example (hp : FinalizedSafetyPrem p c E rho ()) :
    Gen.Pure.CompatOn (· ∈ rho.honest) (F_at p c E rho) (· ≤ rho.events.length) ∧
    Gen.Pure.MonoOn (· ∈ rho.honest) (F_at p c E rho) (· ≤ rho.events.length) :=
  fgsa_apiFinalizedSafetyClaim_body p c E rho () hp

example (hp : FinalizedSafetyPrem p c E rho ()) : RXing p c E rho :=
  fgsa_apiFinalLockClaim_body p c E rho () hp

end AvailableChain.FGSA.Run.Tests.FinalityApi
end
