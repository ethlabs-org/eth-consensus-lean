module
public import AvailableChainFGCompose.Statements.Finality
public import AvailableChainFGCompose.Statements.FinalityReceipts -- shake: keep (re-export)

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (O : FGObservationReads R)
variable (T : FGTiming) (E : Generic.Env V) (rho : V2.D.Run V P)
variable (I : V2.D.Interface P)

/-- Historical transfer depends on the reset, not on the selected service start. -/
theorem historical_transfer_reseed (sp sp' : FGServicePoint)
    (hreset : sp.reset = sp'.reset) (horizon : Time) :
    FGHistoricalHighTransfer R O T E rho I sp horizon ↔
      FGHistoricalHighTransfer R O T E rho I sp' horizon := by
  unfold FGHistoricalHighTransfer
  rw [hreset]

/-- The complete historical chain proposition has the same reset-only dependency. -/
theorem historical_chain_reseed (sp sp' : FGServicePoint)
    (hreset : sp.reset = sp'.reset) (horizon : Time) :
    FGHistoricalHighChain R O T E rho sp horizon ↔
      FGHistoricalHighChain R O T E rho sp' horizon := by
  unfold FGHistoricalHighChain
  rw [hreset]

/-- Restrict only the upper horizon. Historical sources keep their original scope. -/
theorem historical_transfer_horizon {sp : FGServicePoint} {a b : Time} (hab : a ≤ b)
    (h : FGHistoricalHighTransfer R O T E rho I sp b) :
    FGHistoricalHighTransfer R O T E rho I sp a := by
  intro x r C hx hC hh hr v Q hQ hv hgap
  exact h x r C hx hC hh (hr.trans hab) v Q hQ (hv.trans hab) hgap

theorem historical_chain_horizon {sp : FGServicePoint} {a b : Time} (hab : a ≤ b)
    (h : FGHistoricalHighChain R O T E rho sp b) :
    FGHistoricalHighChain R O T E rho sp a := by
  intro x y r q C D hx hy hC hD hc hd hr hq
  exact h x y r q C D hx hy hC hD hc hd (hr.trans hab) (hq.trans hab)

omit [DecidableEq V] in
/-- Later-label coverage uses the actual read at the supplied label. -/
theorem service_head_coverage {A : FGACServiceReads V} {Q : Block} {i : Slot}
    (heads : ∀ x, A.honest x → ∃ H, A.headAtLabel x i = some H)
    (readers : ∀ x, A.honest x → A.headScope x i)
    (transfer : ∀ x H, A.honest x → A.headScope x i →
      A.headAtLabel x i = some H → A.below Q H) :
    ∀ x, A.honest x → ∃ H, A.headScope x i ∧
      A.headAtLabel x i = some H ∧ A.below Q H := by
  intro x hx
  obtain ⟨H, hH⟩ := heads x hx
  exact ⟨H, readers x hx, hH, transfer x H hx (readers x hx) hH⟩

omit [DecidableEq V] in
/-- This projection supplies coverage at either label, with separate label premises. -/
theorem service_proposal_coverage {A : FGACServiceReads V} {sp : FGServicePoint}
    {start horizon : Time} (laws : FGACServiceLaws A sp start horizon)
    {s i : Slot} {Q : Block} (hq : A.proposal s Q) (hs : A.proposalScope s Q)
    (ht : sp.serviceStart ≤ A.proposalTime s) (hi : s + 1 ≤ i)
    (hh : A.voteTime i ≤ horizon)
    (heads : ∀ x, A.honest x → ∃ H, A.headAtLabel x i = some H)
    (readers : ∀ x, A.honest x → A.headScope x i) :
    ∀ x, A.honest x → ∃ H, A.headScope x i ∧
      A.headAtLabel x i = some H ∧ A.below Q H :=
  service_head_coverage heads readers
    (fun x H hx hr hH => laws.proposal_later_head s Q x i H hq hs ht hx hr hi hh hH)

omit [DecidableEq V] in
/-- The next-label vote can precede the source action. No causal-time premise is used. -/
theorem service_source_next {A : FGACServiceReads V} {sp : FGServicePoint}
    {start horizon : Time} (laws : FGACServiceLaws A sp start horizon)
    {y x : V} {r i : Nat} {C H : Block} (hy : A.honest y)
    (hc : A.sourceScope y r C) (hsource : A.source y r = some (some C))
    (ht : InSuffix sp horizon (A.actionTime r)) (hx : A.honest x)
    (hr : A.headScope x i) (hi : A.gateLabel r + 1 ≤ i)
    (hh : A.voteTime i ≤ horizon) (hH : A.headAtLabel x i = some H) : A.below C H :=
  laws.source_next_head y r C x i H hy hc hsource ht hx hr hi hh hH

/-- A late service start cannot satisfy the opening premise. -/
theorem service_start_before_opening {deltaF horizon : Time} {sp : FGServicePoint}
    {pt : KernelPt} {honestSlot : Slot → Prop} {quorum weight timeout capacity : Nat}
    (h : KernelPrem_W T deltaF horizon sp pt honestSlot quorum weight timeout capacity) :
    sp.serviceStart ≤ (pt.r : Time) * FGCompose.P T := h.start

end AvailableChain.FGCompose
end
