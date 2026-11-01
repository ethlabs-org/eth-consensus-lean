module
public import AvailableChainFGSAProofs.Proofs.Finality.Joined -- shake: keep (examples)

public section

namespace AvailableChain.FGSA.Run.Tests.Joined

/-- Pure/model, paper 00:1119–1134, 22:1171–1305; plan §4.
DC-CS/W4FKChainSecondCheckpoint.lean:43: INTENTIONAL same-witness join.
Two different candidates can satisfy separate predicates but cannot be mixed. -/
example (w₀ w₁ : HealingWitness) (hne : w₀ ≠ w₁) :
    (∃ w : HealingWitness, w = w₀) ∧ (∃ w : HealingWitness, w = w₁) ∧
      ¬ (∃ w : HealingWitness, w = w₀ ∧ w = w₁) := by
  refine ⟨⟨w₀, rfl⟩, ⟨w₁, rfl⟩, ?_⟩
  rintro ⟨w, h₀, h₁⟩
  exact hne (h₀.symm.trans h₁)

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {G ΔF : Time} {pt : PtR}

/-- Conditional package, paper 00:1119–1134, 22:1171–1305; plan §4.
DC-CS/W4FKChainSecondCheckpoint.lean:43: INTENTIONAL same-witness join.
One extraction supplies input, start and services, with the deadline at r+2. -/
example (h : KernelJoinedPrem p c G ΔF E rho pt) :
    ∃ w : HealingWitness,
      KernelPrem_W p c G ΔF E rho ⟨w, pt.r⟩ ∧
        kernelDeadlineW p ΔF ((⟨w, pt.r⟩ : KernelPt).r + 2) =
          kernelDeadlineW p ΔF (pt.r + 2) := by
  obtain ⟨w, hK⟩ := finality_kernel_prem_W_of_joined p c E rho G ΔF pt h
  exact ⟨w, hK, rfl⟩

/-- Conditional package, paper 00:1119–1134, 22:1171–1305; plan §4.
DC-CS/W4FKChainSecondCheckpoint.lean:43: INTENTIONAL strict W receipt.
The kernel conclusion retains the actual acceptance deadline at r+2. -/
example (h : KernelConclusion_W p c E rho ΔF pt.r) (A : Block)
    (hA : HonestProposal E rho (fgsaInterface p c) (pt.r * p.R) A) :
    ∃ U, ∀ x ∈ rho.honest,
      AcceptsFinalBefore p c E rho x U (kernelDeadlineW p ΔF (pt.r + 2)) := by
  rw [KernelConclusion_W_def] at h
  obtain ⟨_, _, _, _, U, _, _, _, accepts⟩ := h A hA
  exact ⟨U, accepts⟩

end AvailableChain.FGSA.Run.Tests.Joined
end
