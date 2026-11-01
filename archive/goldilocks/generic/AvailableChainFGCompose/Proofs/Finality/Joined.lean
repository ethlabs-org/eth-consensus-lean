module
public import AvailableChainFGCompose.Statements.Finality

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

/-- Paper 00:1119–1134, 22:1171–1305: build the W kernel premise from the joined premise.
DC-CS/W4FKChainSecondCheckpoint.lean:43: INTENTIONAL same-point join. One service point
supplies the service facts and the start; the FG quorum stays independent. -/
theorem finality_kernel_prem_W_of_joined {T : FGTiming} {deltaF horizon : Time} {r : Nat}
    {honestSlot : Slot → Prop} {fgQuorum fgHonestWeight timeoutSlots capacity : Nat}
    {Service : FGServicePoint → Prop}
    (h : KernelJoinedPrem T deltaF horizon r honestSlot fgQuorum fgHonestWeight
      timeoutSlots capacity Service) :
    ∃ sp, Service sp ∧ KernelPrem_W T deltaF horizon sp ⟨r⟩ honestSlot fgQuorum
      fgHonestWeight timeoutSlots capacity := by
  obtain ⟨sp, service, start⟩ := h.start
  exact ⟨sp, service, {
    bound := h.bound
    window := h.window
    start := start
    hhor := h.hhor
    honest_quorum := h.honest_quorum
    timeout_eq := h.timeout_eq
    capacity_ge := h.capacity_ge }⟩

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (O : FGObservationReads R) (T : FGTiming)
variable (E : Generic.Env V) (rho : V2.D.Run V P) (I : V2.D.Interface P)
variable (decodeProposal : P.Object → Option (Slot × Body))
variable (bodyErase : Body → Block) (bodyRows : Body → List Wire)
variable (parentFG : P.State → Block → Option (FGBlock (Fin n)))
variable (makeFG : FGBlock (Fin n) → Block → List Wire → FGBlock (Fin n))

/-- Paper 00:1119–1134, 22:1171–1305: join the W kernel. The kernel is applied at the one
service point of the joined premise; the round is unchanged.
DC-CS/W4FKChainSecondCheckpoint.lean:43: INTENTIONAL W retention and receipt. -/
theorem finality_kernel_joined_W_of {deltaF : Time} {r : Nat}
    {honestSlot : Slot → Prop} {fgQuorum fgHonestWeight timeoutSlots capacity : Nat}
    {Service : FGServicePoint → Prop}
    (kernel : ∀ sp, Service sp →
      KernelPrem_W T deltaF rho.horizon sp ⟨r⟩ honestSlot fgQuorum fgHonestWeight
        timeoutSlots capacity →
      KernelConclusion_W R E rho O T I decodeProposal bodyErase bodyRows parentFG makeFG
        deltaF r)
    (h : KernelJoinedPrem T deltaF rho.horizon r honestSlot fgQuorum fgHonestWeight
      timeoutSlots capacity Service) :
    KernelConclusion_W R E rho O T I decodeProposal bodyErase bodyRows parentFG makeFG
      deltaF r := by
  obtain ⟨sp, service, hK⟩ := finality_kernel_prem_W_of_joined h
  exact kernel sp service hK

end AvailableChain.FGCompose
end
