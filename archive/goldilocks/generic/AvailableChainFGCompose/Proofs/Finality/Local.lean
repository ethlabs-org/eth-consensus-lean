module
public import AvailableChainFGCompose.Proofs.Finality.Forward
public import AvailableChainFGCompose.Proofs.Finality.RestoreReads
public import AvailableChainGeneric.Proofs.Pure.BlockOrder

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (O : FGObservationReads R) (T : FGTiming) (L : FGTimingLaws T)
variable (E : Generic.Env V) (rho : V2.D.Run V P) (I : V2.D.Interface P)
variable (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))
variable (decodeProposal : P.Object → Option (Slot × Body))
variable (bodyErase : Body → Block) (bodyRows : Body → List Wire)
variable (parentFG : P.State → Block → Option (FGBlock (Fin n)))
variable (makeFG : FGBlock (Fin n) → Block → List Wire → FGBlock (Fin n))

/-- A finality certificate height is at most the height of its finalized block. -/
private theorem finality_certificate_le (hc : FGCertificateLaws Ef O.height O.finality)
    (K : FGBlock (Fin n)) : (O.finality K).h_F ≤ (O.height (O.finality K).F).h := by
  by_cases hz : (O.finality K).h_F = 0
  · rw [hz]
    exact Nat.zero_le _
  · obtain ⟨C, _, _, _, birth, _⟩ := hc.finality_origin K hz
    rw [JustificationBirth_def] at birth
    have he := hc.height.entry_same_height C.parent
    rw [birth.2.2.1, birth.2.1] at he
    exact he.ge

/-- Paper 22:1371–1380: local liveness from the forward witness. The output read below the
opening and the stored finality below the output are the protocol's two read leaves.
DC-CS/W4FKChainSecondCheckpoint.lean:43: INTENTIONAL strict extension and certificate
height; the comparisons use the inclusive read, acceptance stays strict-before. -/
theorem finality_liveness_of_forward_W {deltaF t : Time} {g : Nat} {sp : FGServicePoint}
    {honestSlot : Slot → Prop} (output : P.State → Block)
    (CL : FGCoreLaws R) (durable : FGFinalityDurableLaws R)
    (hs : V2.D.ScheduleWellFormed E rho)
    (hc : FGCertificateLaws Ef O.height O.finality)
    (reflect : ∀ A B, Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B)
    (eraseMono : ∀ A B, FGBlock.Preceq A B → Block.Preceq (R.erase A) (R.erase B))
    (outputBelow : ∀ (r : Nat) A, t ≤ (r : Time) * FGCompose.P T →
      HonestProposal E rho I (r * T.roundSlots) A →
      kernelDeadlineW T deltaF (r + 2) ≤ rho.horizon →
      ∀ x ∈ rho.honest, Block.Preceq (output (V2.D.Run.readAt E rho t x)) A)
    (finalBelow : ∀ x ∈ rho.honest,
      Block.Preceq (R.erase (R.core (V2.D.Run.readAt E rho t x)).fg.F)
        (output (V2.D.Run.readAt E rho t x)))
    (hf : ForwardWitness_W R E rho O T I decodeProposal bodyErase bodyRows parentFG makeFG
      honestSlot deltaF g sp t) :
    FinalityLivenessConcl_W R E rho O output t (t + W_W T deltaF g) := by
  obtain ⟨_, r, A, Afg, U, d, Dl, _, _, _, _, htr, hA, heA, _, hd, _,
    hAU, hne, hU, hDeq, hD, hDhor, hacc⟩ := hf
  have hSA := outputBelow r A htr hA (hDeq ▸ hDhor)
  have hstrict : R.erase Afg ≠ R.erase U := fun he => hne (CL.erase_inj he)
  refine ⟨U, ?_, ?_, ?_⟩
  · intro x hx
    have hSU := Gen.Pure.block_preceq_trans (hSA x hx) (heA ▸ eraseMono _ _ hAU)
    have hneSU : output (V2.D.Run.readAt E rho t x) ≠ R.erase U := by
      intro he
      have hUA : Block.Preceq (R.erase U) (R.erase Afg) := by
        simpa only [he, ← heA] using hSA x hx
      exact hstrict (Gen.Pure.block_preceq_antisymm (eraseMono _ _ hAU) hUA)
    change (!decide (output (V2.D.Run.readAt E rho t x) = R.erase U) &&
      Block.preceq (output (V2.D.Run.readAt E rho t x)) (R.erase U)) = true
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨hneSU, hSU⟩
  · intro x hx K _ hKF
    have hFA : Block.Preceq (R.erase (R.core (V2.D.Run.readAt E rho t x)).fg.F)
        (R.erase Afg) := by
      rw [heA]
      exact Gen.Pure.block_preceq_trans (finalBelow x hx) (hSA x hx)
    have hheight := hc.height.h_mono (reflect _ _ hFA)
    have hcert := finality_certificate_le R O Ef hc K
    rw [hKF] at hcert
    rw [hU, ← hd]
    exact Nat.lt_succ_of_le (hcert.trans hheight)
  · intro x hx
    exact finality_acceptsFinalBefore_mono_deadline R E rho durable hs hD.le (hacc x hx)

include L in
/-- Paper 22:1371–1400: local W liveness from the recurrence, one service point and the
kernel at that point. DC-CS/W4FKChainSecondCheckpoint.lean:43: INTENTIONAL local W
liveness; recurrence start and finite horizon are explicit. -/
theorem finality_liveness_FE_W_of {deltaF recurStart t : Time} {g : Nat} {Jst : Time}
    (sp : FGServicePoint) (honestSlot : Slot → Prop)
    (fgQuorum fgHonestWeight timeoutSlots capacity : Nat)
    (bound : LivenessBoundW T deltaF) (hF0 : 0 ≤ deltaF)
    (recur : FE_W T deltaF honestSlot recurStart rho.horizon g)
    (hrecur : recurStart ≤ t) (ht : 0 < t)
    (start : sp.serviceStart ≤ t) (hhor : t + W_W T deltaF g ≤ rho.horizon)
    (hreset : T.proposal (sp.reset.sStar + 2) ≤ sp.serviceStart)
    (hGSTstart : E.t_GST ≤ sp.serviceStart)
    (honest_quorum : fgQuorum ≤ fgHonestWeight)
    (timeout_eq : timeoutSlots = 2 * T.roundSlots) (capacity_ge : 2 ≤ capacity)
    (kernel : ∀ r, KernelPrem_W T deltaF rho.horizon sp ⟨r⟩ honestSlot fgQuorum
        fgHonestWeight timeoutSlots capacity →
      KernelConclusion_W R E rho O T I decodeProposal bodyErase bodyRows parentFG makeFG
        deltaF r)
    (opening : ∀ r : Nat, honestSlot (r * T.roundSlots) →
      t ≤ (r : Time) * FGCompose.P T → T.proposal (r * T.roundSlots) ≤ rho.horizon →
      ∃ A, HonestProposal E rho I (r * T.roundSlots) A)
    (reset : H0Reset R S E rho O T (fun a => namedEntry (D.heightPair a)) Jst sp.reset)
    (history : FGHistoricalHighTransfer R O T E rho I sp rho.horizon)
    (output : P.State → Block)
    (CL : FGCoreLaws R) (durable : FGFinalityDurableLaws R)
    (hs : V2.D.ScheduleWellFormed E rho)
    (hc : FGCertificateLaws Ef O.height O.finality)
    (reflect : ∀ A B, Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B)
    (parent : ∀ B, R.erase B.parent = (R.erase B).parent)
    (eraseMono : ∀ A B, FGBlock.Preceq A B → Block.Preceq (R.erase A) (R.erase B))
    (outputBelow : ∀ (r : Nat) A, t ≤ (r : Time) * FGCompose.P T →
      HonestProposal E rho I (r * T.roundSlots) A →
      kernelDeadlineW T deltaF (r + 2) ≤ rho.horizon →
      ∀ x ∈ rho.honest, Block.Preceq (output (V2.D.Run.readAt E rho t x)) A)
    (finalBelow : ∀ x ∈ rho.honest,
      Block.Preceq (R.erase (R.core (V2.D.Run.readAt E rho t x)).fg.F)
        (output (V2.D.Run.readAt E rho t x))) :
    FinalityLivenessConcl_W R E rho O output t (t + W_W T deltaF g) :=
  finality_liveness_of_forward_W R O T E rho I Ef decodeProposal bodyErase bodyRows parentFG
    makeFG output CL durable hs hc reflect eraseMono outputBelow finalBelow
    (forward_witness_FE_of R S O T L E rho I D Ef decodeProposal bodyErase bodyRows parentFG
      makeFG sp honestSlot fgQuorum fgHonestWeight timeoutSlots capacity bound hF0 recur
      hrecur ht start hhor hreset hGSTstart honest_quorum timeout_eq capacity_ge kernel
      opening reset history hc.height reflect parent)

end AvailableChain.FGCompose
end
