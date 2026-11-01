module
public import AvailableChainFGCompose.Statements.Finality
public import AvailableChainFGCompose.Proofs.Finality.Middle
public import AvailableChainGeneric.Proofs.Pure.ScheduleW

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

/-- The local finality window has nonnegative length. -/
theorem finality_window_nonneg (T : FGTiming) (L : FGTimingLaws T) (deltaF : Time)
    (g : Nat) : 0 ≤ W_W T deltaF g := by
  have hΔ : 0 ≤ T.delta := L.delta_pos.le
  unfold W_W betaF FGCompose.P
  positivity

/-- Paper 22:1371–1400: the recurrence from its start gives one aligned good round whose
kernel deadline is inside the local window and the finite horizon.
DC: INTENTIONAL full FE guard; the recurrence start is explicit. -/
theorem forward_round_FE (T : FGTiming) (L : FGTimingLaws T) {deltaF start horizon t : Time}
    {g : Nat} {honestSlot : Slot → Prop}
    (recur : FE_W T deltaF honestSlot start horizon g) (ht : 0 < t) (hstart : start ≤ t)
    (hhor : t + W_W T deltaF g ≤ horizon) :
    ∃ q r : Nat, t ≤ (q : Time) * FGCompose.P T ∧
      (q : Time) * FGCompose.P T < t + FGCompose.P T ∧ Gen.Pure.InWindow q g r ∧
      Gen.Pure.FGoodE_W honestSlot T.roundSlots (kappaF T deltaF) r ∧
      t ≤ (r : Time) * FGCompose.P T ∧
      kernelDeadlineW T deltaF (r + 2) < t + W_W T deltaF g ∧
      kernelDeadlineW T deltaF (r + 2) ≤ horizon := by
  have hP : 0 < FGCompose.P T := by
    have hR : 0 < T.roundSlots := by have := L.rounds; omega
    exact mul_pos (mul_pos (by decide) (Int.natCast_pos.mpr hR)) L.delta_pos
  obtain ⟨q, r, htq, hqt, hr, hgood⟩ := Gen.Pure.recFE_W_extract recur hP ht hstart
    (by
      have h := hhor
      unfold W_W at h
      linarith)
  have htr : t ≤ (r : Time) * FGCompose.P T := htq.trans
    (mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr hr.1) hP.le)
  have hD : kernelDeadlineW T deltaF (r + 2) < t + W_W T deltaF g := by
    have h := Gen.Pure.recFE_W_receipt_lt (Δ := T.delta) (β := betaF T deltaF) hP hqt hr
    unfold kernelDeadlineW W_W
    push_cast
    linarith
  exact ⟨q, r, htq, hqt, hr, hgood, htr, hD, hD.le.trans hhor⟩

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

include L in
/-- Paper 22:1371–1400: the forward witness. The kernel is applied once at the selected
round and the same service point; its carrier and fresh extension are kept, with the
opening above the reset frontier. DC-CS/W4FKChainSecondCheckpoint.lean:43: INTENTIONAL
full FE guard, explicit recurrence start and finite horizon. -/
theorem forward_witness_FE_of {deltaF recurStart t : Time} {g : Nat} {Jst : Time}
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
    (height : FGHeightLaws Ef O.height)
    (reflect : ∀ A B, Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B)
    (parent : ∀ B, R.erase B.parent = (R.erase B).parent) :
    ForwardWitness_W R E rho O T I decodeProposal bodyErase bodyRows parentFG makeFG
      honestSlot deltaF g sp t := by
  obtain ⟨q, r, htq, hqt, hr, hgood, htr, hD, hDhor⟩ :=
    forward_round_FE T L recur ht hrecur hhor
  have hK : KernelPrem_W T deltaF rho.horizon sp ⟨r⟩ honestSlot fgQuorum fgHonestWeight
      timeoutSlots capacity := {
    bound := bound, window := hgood, start := start.trans htr, hhor := hDhor
    honest_quorum := honest_quorum, timeout_eq := timeout_eq, capacity_ge := capacity_ge }
  obtain ⟨_, _, _, _, hgap, _, hhorA⟩ :=
    kmid_kernel_bounds T L hK.bound hK.start hK.hhor hF0 hreset hGSTstart
  have hwin := hgood
  rw [Gen.Pure.FGoodE_W_def] at hwin
  have hprop := (kmid_slot_horizon T L hhorA
    (Nat.mul_le_mul_right T.roundSlots (show r ≤ r + 2 by omega))).1
  obtain ⟨A, hA⟩ := opening r hwin.1 htr hprop
  obtain ⟨Afg, heA, hcA, _, U, hAU, hne, hU, hacc⟩ := kernel r hK A hA
  have highA : sp.reset.M + 1 ≤ (O.height Afg).h :=
    middle_reset_opening_height R S O T L E rho I D Ef sp rho.horizon Jst reset history
      height reflect parent r Afg (heA ▸ hA) hprop hgap
  exact ⟨q, r, A, Afg, U, (O.height Afg).h, kernelDeadlineW T deltaF (r + 2),
    htq, hqt, hr, hgood, htr, hA, heA, hcA, rfl, highA, hAU, hne, hU, rfl, hD, hDhor, hacc⟩

end AvailableChain.FGCompose
end
