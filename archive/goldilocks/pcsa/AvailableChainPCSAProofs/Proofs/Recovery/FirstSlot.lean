module
public import AvailableChainPCSAProofs.Proofs.Recovery.AnchorBase
public import AvailableChainPCSAProofs.Proofs.Recovery.CleanSaved
public import AvailableChainPCSAProofs.Proofs.Recovery.Suffix
public import AvailableChainPCSAProofs.Proofs.Recovery.View
public import AvailableChainPCSAProofs.Proofs.Shared.Proposal

public section

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- An armed anchor and its saved-result bound supply both first-slot root clauses. -/
theorem recovery_firstSlot_of_anchor (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hf : StageOneFrame p c E rho)
    (cA s : Slot) (P : Block) (horder : cA < s)
    (hwindow : s - 1 - cA ≤ p.k - 1)
    (hafter : E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s)
    (hprop : Gen.V2.Duty.HonestAwakeProposer E
      (pcsaInterface p c (m := m)).toInterface rho s)
    (horizon : SA.gateTime p.toParams s ≤ rho.horizon)
    (hStamp : ∀ y ∈ rho.honest,
      PCStampedBefore p c E rho y (SA.freezeTime p.toParams cA) cA P)
    (hArm : ArmConcl p c E rho cA P (cA + 1))
    (hSaved : ∀ x ∈ rho.honest, ∀ (i : Nat) (r : Slot) (C : Block), r < cA →
      GridCO.savedGenuine (V2.D.Run.stateBefore E rho i x).st.base r = some (some C) →
      Block.Preceq C P) :
    ∃ N : NamedProposal p.n,
      FormationPrem p c E rho s N ΔF ∧ RecoveryRootReachable p c E rho s := by
  have hpos : 0 < s := Nat.zero_le cA |>.trans_lt horder
  have hd := p.deltaPos
  have htime : SA.proposalTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  obtain ⟨N, hN⟩ := recovery_named_proposal_exists E rho h.base hf s hpos hprop
    (htime.trans horizon)
  have hlocks := recovery_anchor_locks_of_clean_saved E rho
    h.base.valid.toScheduleWellFormed cA s P hwindow horder hSaved
  have hbase : ∀ nd, pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (SA.proposalTime p.toParams s) = some nd →
      Block.Preceq P (walkBase p nd.st (proposerPC p nd.st)) := by
    intro nd hnd
    apply recovery_base_of_arm E rho h.base.valid.toScheduleWellFormed h.base.noRestart
      hf cA P _ hprop.1 (hStamp _ hprop.1)
      (fun t t' htt hpc => (hArm.2.2 _ hprop.1 t t' htt hpc).1) _ _ nd hnd
    have hcs : (cA : Int) + 1 ≤ (s : Int) := by exact_mod_cast horder
    change 4 * p.Δ * (cA : Int) + 3 * p.Δ < 4 * p.Δ * (s : Int)
    nlinarith
  have hparent : Block.Preceq P N.erase.parent := by
    obtain ⟨nd, hnd, _, hparent, _⟩ := pcsa_honest_proposal_state E rho h.base s N hN
    rw [hparent]
    exact Gen.Pure.block_preceq_trans (hbase nd hnd)
      (Gen.Pure.block_preceq_trans (pcsa_liveRoot_extends_base p nd.st _)
        (pcsa_headInTree_extends_root p nd.st _ _ _ _))
  have hroot : RecoveryRootReachable p c E rho s := by
    apply recovery_root_reachable p c E rho s P
    intro nd hnd
    exact ⟨recovery_proposer_base p nd.st, hbase nd hnd,
      hlocks _ hprop.1 _ (Or.inl rfl) nd hnd⟩
  refine ⟨N, ?_, hroot⟩
  · exact {
      base := h.base
      quarterCap := h.quarterCap
      frame := hf
      slotPos := hpos
      horizon := horizon
      deltaF := h.deltaF
      proposal := hN
      delivery := recovery_delivery_from_run E rho h s hpos hafter horizon
      participation := (recovery_participation E rho h s hafter horizon).1
      commonView := recovery_commonView E rho h hf s hpos hafter horizon N hN
      leases := fun y hy _ nd hnd B hB _ _ =>
        Gen.Pure.block_preceq_trans (hlocks y hy _ (Or.inr rfl) nd hnd B hB) hparent
      proposerRootReachable :=
        (pcsa_recovery_rootReachable_iff_formation p c E rho s).mp hroot }

end AvailableChain.PCSA.Run
end
