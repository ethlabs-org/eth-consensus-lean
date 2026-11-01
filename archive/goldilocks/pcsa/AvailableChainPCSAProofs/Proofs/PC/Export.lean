module
public import AvailableChainPCSAClaims.Claims.PC
public import AvailableChainPCSAProofs.Proofs.Foundations.Duties
public import AvailableChainPCSAProofs.Proofs.Foundations.Run
public import AvailableChainPCSAProofs.Proofs.PC.Uniqueness

public section

/-! PC claim exports (pcsa34-r4.3 §3.2, §5.1, A6; proof plan C1, C2, C4). -/

namespace AvailableChain.PCSA.Run

/-- C1: two held PCs of one slot have the same full target block. -/
theorem pcsa_pcUniqueness (p : Params) : PCUniquenessClaim p := by
  intro V _ _ In c m E rho h hf x hx y hy t u a ha b hb hs
  exact held_pc_target_unique E rho h hf x y hx hy t u a b ha hb hs

/-- C2: an honest seat emits one ack root, at the slot's early time. -/
theorem pcsa_oneAckPerSlot (p : Params) : OneAckPerSlotClaim p := by
  intro V _ _ In c m E rho hv x _ s i r r' t t' h h'
  exact ack_emission_unique p c m E rho hv.nodup x s i r r' t t' h h'

/-- C4: strong and finalized outputs are below the available output. -/
theorem pcsa_outputNesting (p : Params) : OutputNestingClaim p := by
  intro V _ _ In c m E rho _ x _ t
  exact reachable_outputNesting p _ (reachable_storeAt E rho t x)

end AvailableChain.PCSA.Run
end
