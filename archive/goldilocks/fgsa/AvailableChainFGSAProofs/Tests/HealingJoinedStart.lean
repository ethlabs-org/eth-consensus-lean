module
-- shake keep reason: test environment
public import AvailableChainFGSAProofs.Proofs.Healing.SupportRecovery -- shake: keep

public section

namespace AvailableChain.FGSA.Run.Tests.JoinedStart

-- These check the four stated run clocks. ExecutionValid replay remains OPEN/P-H1.
abbrev k3 : Params :=
  ⟨⟨1, 4, 3, 64, by decide, by decide, by decide, by decide⟩,
    2, 4, by decide, 2, by decide, fun d => ⟨d.slot + 1⟩⟩
abbrev k4 : Params :=
  ⟨⟨1, 4, 4, 64, by decide, by decide, by decide, by decide⟩,
    2, 4, by decide, 2, by decide, fun d => ⟨d.slot + 1⟩⟩
abbrev n7 : Params :=
  ⟨⟨1, 7, 2, 4096, by decide, by decide, by decide, by decide⟩,
    2, 4, by decide, 2, by decide, fun d => ⟨d.slot + 1⟩⟩
abbrev split : Params :=
  ⟨⟨2, 7, 2, 4096, by decide, by decide, by decide, by decide⟩,
    5, 10, by decide, 2, by decide, fun d => ⟨d.slot + 1⟩⟩
abbrev env1 : Generic.Env (Fin 4) := ⟨1, by decide, 21, by decide, fun _ _ => true⟩
abbrev env7 : Generic.Env (Fin 7) := ⟨1, by decide, 1001, by decide, fun _ _ => true⟩
abbrev envSplit : Generic.Env (Fin 7) :=
  ⟨2, by decide, 2002, by decide, fun _ _ => true⟩

theorem stale_k3 : recoveryStart k3 env1 = 30 ∧
    SA.voteTime k3.toParams 5 < recoveryStart k3 env1 ∧
    recoveryStart k3 env1 ≤ SA.voteTime k3.toParams 8 ∧
    SA.gateTime k3.toParams 3 + SA.lifetime k3.toParams = 29 := by decide

theorem stale_k4 : recoveryStart k4 env1 = 30 ∧
    SA.voteTime k4.toParams 5 < recoveryStart k4 env1 ∧
    SA.proposalTime k4.toParams 7 < recoveryStart k4 env1 ∧
    SA.gateTime k4.toParams 3 + SA.lifetime k4.toParams = 33 := by decide

theorem slow_n7 : recoveryStart n7 env7 = 1010 ∧
    SA.voteTime n7.toParams 251 < recoveryStart n7 env7 ∧
    SA.gateTime n7.toParams 251 = recoveryStart n7 env7 ∧
    recoveryStart n7 env7 ≤ SA.voteTime n7.toParams 253 ∧
    254 ≤ 253 + n7.k := by decide

theorem split_batch : recoveryStart split envSplit = 2020 ∧
    SA.voteTime split.toParams 251 < recoveryStart split envSplit ∧
    SA.gateTime split.toParams 251 + SA.lifetime split.toParams = 2034 ∧
    SA.proposalTime split.toParams 254 < 2034 ∧
    254 ≤ 253 + split.k ∧
    SA.gateTime split.toParams 256 < recoveryStart split envSplit + ρ₁ split 16 ∧
    SA.gateTime split.toParams 258 ≤ recoveryStart split envSplit + ρΓ split 16 := by decide

-- N4 is an expiry regression only; it does not assign a stored live lease.
abbrev longK : Params :=
  ⟨⟨1, 4, 8, 64, by decide, by decide, by decide, by decide⟩,
    2, 4, by decide, 2, by decide, fun d => ⟨d.slot + 1⟩⟩

theorem pre_gst_expiry_after_ready_releases : 2 * longK.R + 3 < longK.k ∧
    SA.gateTime longK.toParams 3 < env1.t_GST ∧
    recoveryStart longK env1 ≤ SA.voteTime longK.toParams 8 ∧
    SA.releaseTime longK.toParams 8 <
      SA.gateTime longK.toParams 3 + SA.lifetime longK.toParams ∧
    SA.releaseTime longK.toParams 9 <
      SA.gateTime longK.toParams 3 + SA.lifetime longK.toParams := by decide

-- The exact production cut proves prior-batch readiness at the admitted proposal.
example : envSplit.t_GST ≤ slotStartZ split ((253 : Int) - 2) :=
  healing_ready_proposal_cutoff envSplit (by decide)

end AvailableChain.FGSA.Run.Tests.JoinedStart
end

#print axioms AvailableChain.FGSA.Run.Tests.JoinedStart.stale_k3
#print axioms AvailableChain.FGSA.Run.Tests.JoinedStart.stale_k4
#print axioms AvailableChain.FGSA.Run.Tests.JoinedStart.slow_n7
#print axioms AvailableChain.FGSA.Run.Tests.JoinedStart.split_batch

#print axioms AvailableChain.FGSA.Run.Tests.JoinedStart.pre_gst_expiry_after_ready_releases
