module
public import AvailableChainPCSAClaims.Claims.Outage
public import AvailableChainPCSAProofs.Proofs.Outage.CutBoundary
public import AvailableChainPCSAProofs.Proofs.Outage.RelayRun
public import AvailableChainPCSAProofs.Proofs.Outage.BlockReceipt
public import AvailableChainPCSAProofs.Proofs.Outage.SlowRun

public section

/-! Outage claim exports (pcsa34-r4.3 §5.4.1, §5.4.2, §5.5; proof plan C8, C10). -/

namespace AvailableChain.PCSA.Run

/-- C8: PC persistence under ARM, stage 1. -/
theorem pcsa_armPersistence (p : Params) : ArmPersistenceClaim p := by
  rw [ArmPersistenceClaim_def]
  intro V _ _ In c m E rho s B j₀ h hf hfr hsj harm
  exact pcsa_arm_concl E rho h hf hfr hsj harm

/-- C8, ARM-healthy (§5.4.2): the stage-1 companion persistence, given the
two Clean-lane ARM items `CleanArmItems` (relay of a held PC within `Δ`, and
CI 5.2.2 (d) on the acks of the later labels before `b₀`). `hitems` is supplied by the
Outage assembly: it proves the relay item and builds the acks item from M3
and the vote-time HEAD cone `CleanVoteConeItems` (`pcsa_armHealthyClaim`). -/
theorem pcsa_armHealthy (p : Params) (hitems : CleanArmItems p) : ArmHealthyClaim p := by
  rw [ArmHealthyClaim_def]
  rw [CleanArmItems_def] at hitems
  intro V _ _ In c m E rho T b₀ ΔF hC hf hfr hT0 _ hT3
  obtain ⟨hrelay, hacks⟩ := hitems c m E rho b₀ ΔF hC hf hfr
  exact pcsa_armHealthy_of E rho hC hf hfr hT0 hT3 hrelay hacks

/-- C10, slow P1 (§5.5): the PC case by ARM-healthy, the S case by the lock
induction after `b₀`, given the Clean-lane ARM items and the Clean-lane
boundary facts at `b₀` (`CleanSlowItems`: `S ⪰ S_u(T)`, the locks, the saved
results and the pending result at every honest node, and the honest acks and
HEADs of the labels before `b₀`). `hitems` and `hslow` are supplied by the
Outage assembly, which builds them from the Clean claims and the HEAD cone
`CleanConeItems` (`pcsa_slowP1Claim`). -/
theorem pcsa_slowP1 (p : Params) (hitems : CleanArmItems p) (hslow : CleanSlowItems p) :
    PCSASlowP1Claim p := by
  rw [PCSASlowP1Claim_def]
  rw [CleanArmItems_def] at hitems
  have hS := pcsa_slowStableItems p hslow
  rw [SlowStableItems_def] at hS
  intro V _ _ In c m E rho T b₀ b₁ ΔF hO hf hfr u hu X hX w hw t hbt htb
  obtain ⟨hrelay, hacks⟩ := hitems c m E rho b₀ ΔF hO.pre hf hfr
  exact pcsa_slowP1_of E rho hO hf hfr hrelay hacks (hS c m E rho T b₀ b₁ ΔF hO hf hfr)
    u hu X hX w hw t hbt htb

end AvailableChain.PCSA.Run
end
