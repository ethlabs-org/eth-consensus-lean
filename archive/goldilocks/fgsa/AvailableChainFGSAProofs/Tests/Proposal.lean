module
public import AvailableChainFGSAProofs.Proofs.Assembly.Finality -- shake: keep (F-PROP fixtures)

set_option linter.privateModule false

public section

namespace AvailableChain.FGSA.Run.Tests.Proposal
open AvailableChain.SimplexFG AvailableChain.KitFG

private abbrev p : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide, R := 4, δt := 8, RLarge := by decide, digest :=
        fun d => ⟨d.slot + 1⟩ }

private def X : FGBlock (Fin 4) := .node .genesis 4 ⟨1⟩ 0 []
private def A : FGBlock (Fin 4) := .node X 8 ⟨2⟩ 0 []
private def F : FGBlock (Fin 4) := .node A 12 ⟨3⟩ 0 []
private def modelOutput (t : Time) : Block :=
  if t < SA.gateTime p.toParams 4 then .genesis
  else if t < SA.gateTime p.toParams 8 then eraseFG X else eraseFG A

/-- Pure/model, paper 22:1421–1430; firstfin plan §6.
DC: INTENTIONAL equal opening: proposal at T_1, exact output at its later gate.
These model blocks and outputs are not an execution witness. -/
example : SA.proposalTime p.toParams 4 = (1 : Time) * P p ∧
    SA.gateTime p.toParams 4 = 22 ∧ modelOutput 22 = eraseFG X := by
  decide +kernel

/-- Pure/model, paper 22:1424–1428; firstfin plan §6.
DC: SAME equal-gate identity: two exact outputs at the same gate determine X=A. -/
example (Q B S : Block) (hQ : S = Q) (hB : S = B) : Q = B :=
  hQ.symm.trans hB

/-- Pure/model, paper 22:1424–1428; firstfin plan §6.
DC: INTENTIONAL later opening in the same FE search range. X is a strict ancestor
of the eventual F and differs from the selected checkpoint A. -/
example : Gen.Pure.InWindow 1 2 2 ∧
    SA.gateTime p.toParams 4 < SA.gateTime p.toParams 8 ∧
    modelOutput 38 = eraseFG A ∧ FGBlock.Preceq X A ∧ X ≠ A ∧
    FGBlock.Preceq X F ∧ X ≠ F := by
  constructor
  · exact ⟨by decide, by decide⟩
  · decide +kernel

/-- Pure/model, paper 22:1424–1428; firstfin plan §6.
DC: INTENTIONAL proposal-time output does not contain X; its later gate serves X. -/
example : ¬ Block.Preceq (eraseFG X) (modelOutput (SA.proposalTime p.toParams 4)) ∧
    modelOutput (SA.gateTime p.toParams 4) = eraseFG X := by
  decide +kernel

/-- Pure/model, paper 22:1421–1430; firstfin plan §6.
DC: INTENTIONAL late proposal: its deadline moves with its own proposal time. -/
example : SA.proposalTime p.toParams 1000 + W_W p 2 2 = 4073 ∧
    ¬ SA.proposalTime p.toParams 1000 + W_W p 2 2 ≤ (100 : Time) := by
  decide +kernel

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {G ΔF : Time} {g : Nat} {w : HealingWitness} {pt : PtSX}

/-- Conditional package, paper 22:1421–1430; firstfin plan §6.
DC: INTENTIONAL supplied Forward record, retaining its one Afg/U selection.
This fixture assumes the package and record; it is not a complete execution. -/
example (h : ProposalFinalPrem_W p c G ΔF .recFE g w E rho pt)
    (hf : ForwardWitness_W p c E rho ΔF g w
      (V2.D.proposalTime (fgsaInterface p c) pt.s)) :
    ProposalFinalConcl_W p c E rho pt.X
      (V2.D.proposalTime (fgsaInterface p c) pt.s + W_W p ΔF g) :=
  proposal_final_of_forward_W p c E rho h hf

/-- Conditional package, paper 22:1421–1430; firstfin plan §6.
DC: INTENTIONAL FE closure from the frozen package, with no kernel suppliers.
This fixture is not a complete execution. -/
example (hδ : p.δt = 2 * p.R)
    (h : ProposalFinalPrem_W p c G ΔF .recFE g w E rho pt) :
    ProposalFinalConcl_W p c E rho pt.X
      (V2.D.proposalTime (fgsaInterface p c) pt.s + W_W p ΔF g) :=
  fgsa_proposalFinalRecFE_W p G ΔF g w hδ c E rho pt h

/-- Conditional package, paper 22:1421–1430; firstfin plan §6.
DC: INTENTIONAL F4 closure through the FE conversion with the same local deadline.
This fixture is not a complete execution. -/
example (hδ : p.δt = 2 * p.R)
    (h : ProposalFinalPrem_W p c G ΔF .recF4 g w E rho pt) :
    ProposalFinalConcl_W p c E rho pt.X
      (V2.D.proposalTime (fgsaInterface p c) pt.s + W_W p ΔF g) :=
  fgsa_proposalFinalRecF4_W p G ΔF g w hδ c E rho pt h

/-- Conditional package, paper 22:1424–1428; firstfin plan §6.
DC: INTENTIONAL missing X in every honest proposal-time output is compatible
with applying the frozen FE package. This fixture does not construct a run. -/
example (hδ : p.δt = 2 * p.R)
    (h : ProposalFinalPrem_W p c G ΔF .recFE g w E rho pt)
    (hmiss : ∀ x ∈ rho.honest, ¬ Block.Preceq pt.X
      (V2.D.Run.readAt E rho (V2.D.proposalTime (fgsaInterface p c) pt.s) x).st.base.stableRecord) :
    ProposalFinalConcl_W p c E rho pt.X
      (V2.D.proposalTime (fgsaInterface p c) pt.s + W_W p ΔF g) ∧
    ∀ x ∈ rho.honest, ¬ Block.Preceq pt.X
      (V2.D.Run.readAt E rho (V2.D.proposalTime (fgsaInterface p c) pt.s) x).st.base.stableRecord :=
  ⟨fgsa_proposalFinalRecFE_W p G ΔF g w hδ c E rho pt h, hmiss⟩

end AvailableChain.FGSA.Run.Tests.Proposal
end
