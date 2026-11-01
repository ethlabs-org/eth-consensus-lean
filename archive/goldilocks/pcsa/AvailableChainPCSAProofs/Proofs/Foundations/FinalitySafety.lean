module
public import AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyBridge

public section

/-! PC-SA finality safety bodies over the frozen PC observation reads. -/

namespace AvailableChain.PCSA.Run
open AvailableChain.SimplexFG

variable (m : FGMode) (p : Params) {V : Type} [DecidableEq V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))

/-- All run blocks, honest event prefixes, and honest time reads are accountable. -/
theorem pcsa_safety_wholeRunAccountable_body (hr : NamedRootCollisionFree p c E rho) :
    PCWholeRunAccountable p c E rho := pcsa_safety_accountable_supply m p c E rho hr

/-- Run blocks and honest time reads agree under the all-run bound. -/
theorem pcsa_safety_wholeRunAgreement_body (hr : NamedRootCollisionFree p c E rho)
    (hb : PCFinalitySlashableBound p c E rho) : PCWholeRunAgreement p c E rho :=
  pcsa_safety_agreement_supply m p c E rho hr hb

/-- Any two honest event prefixes agree under the all-run bound. -/
theorem pcsa_safety_eventPrefixAgreement_body (hr : NamedRootCollisionFree p c E rho)
    (hb : PCFinalitySlashableBound p c E rho) :
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ i j : Nat,
      FGBlock.compatible (storeBefore p c E rho i x).fg.F
        (storeBefore p c E rho j y).fg.F = true :=
  fun x _ y _ i j => pcsa_safety_eventAgreement_supply m p c E rho hr hb i j x y

/-- Sorted time reads are monotone when there is no restart. -/
theorem pcsa_safety_finalizedMonotone_body (hs : PCFinalityExecution p c rho)
    (hnr : V2.D.NoRestart rho) :
    ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
      Block.Preceq (pcsaFinalizedOut (V2.D.Run.readAt E rho t x))
        (pcsaFinalizedOut (V2.D.Run.readAt E rho t' x)) :=
  pcsa_safety_monotone_supply m p c E rho hs hnr

/-- The fault bound excludes slashable weight with all-run carriage and safe emission. -/
theorem pcsa_safety_faultCountSlashableBound_body [Fintype V]
    (hl : V2.D.Linked (pcsaFamilies p c).linked rho)
    (hc : ∀ K, PCFinalityBlock p c E rho K →
      PCFinalityRowCarriage p c E rho (chainRows K))
    (he : ∀ x ∈ rho.honest, PCEmittedRowsNoSlash p c E rho x)
    (hf : FGSafetyBound p c rho) : PCFinalitySlashableBound p c E rho :=
  pcsa_safety_count_supply m p c E rho hl hc he hf

/-- Honest holders are never slashed under unforgeable signatures and Linked. -/
theorem pcsa_safety_honestNeverSlashed_body (m : FGMode) (p : Params) {In : Type}
    (c : AppCodec In) (E : Generic.Env (Fin p.n))
    (rho : V2.D.Run (Fin p.n) (pcsaWith m p c))
    (hu : V2.D.UnforgeableSignatures E rho)
    (hl : V2.D.Linked (pcsaFamilies p c).linked rho) :
    Gen.V2.Duty.HonestNeverSlashed (pcsaSlashing p c E) rho :=
  pcsa_safety_nonSlashing_supply m p c E rho hu hl

end AvailableChain.PCSA.Run
end
