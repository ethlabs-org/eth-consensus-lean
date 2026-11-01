module
public import AvailableChainPCSAProofs.Proofs.Recovery.LockTransport
public import AvailableChainPCSAClaims.Claims.Recovery
public import AvailableChainPCSAProofs.Proofs.Recovery.Suffix
public import AvailableChainPCSAProofs.Proofs.Recovery.CleanSaved
public import AvailableChainPCSAProofs.Proofs.Recovery.AnchorBase
public import AvailableChainPCSAProofs.Proofs.Recovery.FirstSlot
public import AvailableChainPCSAProofs.Proofs.Recovery.LongFirstSlot

public section

/-! Conditional short-break recovery export (pcsa34-r4.3b §5.6.1).
The named producers are in RecoverySuffixInputs; no unconditional C11 is claimed. -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- The clean anchor is below the first recovered proposer base. -/
theorem pcsa_recovery_anchor_proposer_base (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time} {cA s₁ : Slot}
    (h : ShortBreakPrem p c E rho G ΔF cA s₁)
    (N : NamedProposal p.n)
    (hStamp : ∀ y ∈ rho.honest,
      PCStampedBefore p c E rho y (SA.freezeTime p.toParams cA) cA N.erase)
    (hArm : ArmConcl p c E rho cA N.erase (cA + 1)) :
    ∀ nd, pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s₁)
      (SA.proposalTime p.toParams s₁) = some nd →
      Block.Preceq N.erase (walkBase p nd.st (proposerPC p nd.st)) := by
  intro nd hnd
  apply recovery_base_of_arm E rho h.recovery.base.valid.toScheduleWellFormed
    h.recovery.base.noRestart h.frame cA N.erase _ h.firstProposer.1
    (hStamp _ h.firstProposer.1)
    (fun t t' htt hpc => (hArm.2.2 _ h.firstProposer.1 t t' htt hpc).1) _ _ nd hnd
  have hd := p.deltaPos
  have horder : (cA : Int) + 1 ≤ (s₁ : Int) := by exact_mod_cast h.order
  change 4 * p.Δ * (cA : Int) + 3 * p.Δ < 4 * p.Δ * (s₁ : Int)
  nlinarith

/-- C8 supplies initial coverage; restarted CI supplies the healed suffix. -/
theorem recovery_healed_of_inputs (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s₁ : Slot) (ΔF : Time)
    (inputs : RecoverySuffixInputs p c E rho s₁ ΔF) :
    ∃ P, Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho s₁ P ∧
      HealedFrom p c E rho s₁ P := by
  obtain ⟨N, hN, hroot⟩ := inputs.firstSlot
  have hs := inputs.formation N hN hroot
  have stampRead (x : V) (hx : x ∈ rho.honest) (B : Block)
      (hPC : PCStampedBefore p c E rho x (SA.freezeTime p.toParams s₁) s₁ B) :
      ∃ pc ∈ (storeAt p c E rho x (SA.freezeTime p.toParams s₁)).pcs,
        pc.slot = s₁ ∧ pc.target = B :=
    recovery_stampRead E rho hN.base.valid.toScheduleWellFormed hN.base.noRestart hN.frame
      x hx _ s₁ B hPC
  have ha := arm_next_of_common_stamp E rho s₁ N.erase hs
  have hp := inputs.persistence N.erase ha
  have hi := inputs.ciRestart N hN hroot hp
  refine ⟨N.erase, honestProposal_of_named E rho s₁ N hN.proposal, ?_⟩
  rw [HealedFrom_def]
  refine ⟨?_, ?_, hi.chain, hi.mono, hi.inclusion⟩
  · intro x hx t ht _
    have hfg : SA.freezeTime p.toParams s₁ ≤ SA.gateTime p.toParams s₁ := by
      change 4 * p.Δ * (s₁ : Int) + 3 * p.Δ ≤ 4 * p.Δ * (s₁ : Int) + 6 * p.Δ
      have hd : (0 : Int) < p.Δ := p.deltaPos
      linarith
    exact (hp.2.2 x hx _ t (hfg.trans ht) (stampRead x hx _ (hs x hx))).2
  · intro x hx t ht _
    exact (hp.2.2 x hx _ t ht (stampRead x hx _ (hs x hx))).1

/-- The unchanged C11 statement follows when the named recovery producers are supplied. -/
theorem pcsa_fastRecoveredClaim_of_inputs (p : Params)
    (recoveryInputs : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (m : FGMode) (E : Generic.Env V)
      (rho : V2.D.Run V (pcsaWith m p c)) (G ΔF : Time) (cA s₁ : Slot),
      ShortBreakPrem p c E rho G ΔF cA s₁ → RecoverySuffixInputs p c E rho s₁ ΔF) :
    FastRecoveredClaim p := by
  intro V _ _ In c m E rho G ΔF cA s₁ h
  obtain ⟨P, hp, hh⟩ := recovery_healed_of_inputs E rho s₁ ΔF
    (recoveryInputs c m E rho G ΔF cA s₁ h)
  exact ⟨P, hp, recovery_first_gate_bound E rho h.recovery s₁ h.firstMin h.horizon, hh⟩

/-- The long-break claim follows when the named producers hold after the mix time. -/
theorem pcsa_longBreakRecoveredClaim_of_inputs (p : Params)
    (recoveryInputs : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (m : FGMode) (E : Generic.Env V)
      (rho : V2.D.Run V (pcsaWith m p c)) (G ΔF : Time),
      Recovery₂ p c E rho G ΔF → StageOneFrame p c E rho →
      ∀ g s : Slot,
      E.t_GST ≤ SA.voteTime p.toParams g →
      (∀ j : Slot, j < g → SA.voteTime p.toParams j < E.t_GST) →
      SA.voteTime p.toParams (g + 2 * p.k - 1) ≤ SA.proposalTime p.toParams s →
      E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s →
      Gen.V2.Duty.HonestAwakeProposer E (pcsaInterface p c (m := m)).toInterface rho s →
      SA.gateTime p.toParams s ≤ rho.horizon → RecoverySuffixInputs p c E rho s ΔF) :
    LongBreakRecoveredClaim p := by
  intro V _ _ In c m E rho G ΔF h hf hh
  obtain ⟨g, s, hg, hm, hs, ha, hp, hb⟩ := long_recovery_slot E rho h hh
  obtain ⟨P, hP, heal⟩ := recovery_healed_of_inputs E rho s ΔF
    (recoveryInputs c m E rho G ΔF h hf g s hg hm hs.le ha hp (hb.trans hh))
  exact ⟨s, P, hP, hb, heal⟩

/-- The long-break transport facts supply the exact first-slot predicates. -/
theorem recovery_firstSlot_long (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho)
    (g s : Slot) (transport : RecoveryLockTransport p c E rho g)
    (hgst : E.t_GST ≤ SA.voteTime p.toParams g)
    (hmix : SA.voteTime p.toParams (g + 2 * p.k - 1) ≤ SA.proposalTime p.toParams s)
    (hafter : E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s)
    (hprop : Gen.V2.Duty.HonestAwakeProposer E
      (pcsaInterface p c (m := m)).toInterface rho s)
    (horizon : SA.gateTime p.toParams s ≤ rho.horizon) :
    ∃ N : NamedProposal p.n,
      FormationPrem p c E rho s N ΔF ∧ RecoveryRootReachable p c E rho s := by
  obtain ⟨N, hN, hroot⟩ := recovery_firstSlot_long_body E rho h hF g s transport
    hgst hmix hafter hprop horizon
  exact ⟨N, hN, (RecoveryRootReachable_def p c E rho s).mpr hroot⟩

end AvailableChain.PCSA.Run
end
