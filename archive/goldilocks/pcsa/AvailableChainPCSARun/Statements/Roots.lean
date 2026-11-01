module
public import AvailableChainPCSARun.Model.Protocol
public import AvailableChainEngineV2.Engine.Duty.Run

@[expose] public section

/-! [PC-SA claims; FG-SA Run/Statements/Roots.lean] The run-level root
collision freedom premise of the PC-SA claims (review C1, 2026-10-06): a
mechanical port over the PC-SA named proposals. -/

namespace AvailableChain.PCSA.Run

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    {m : FGMode} (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))

/-- [PC-SA M1; DC NamedRun.directBlockInRun] Exact delivered or held bodies. -/
def DirectNamedProposalInRun (N : NamedProposal p.n) : Prop :=
  (∃ x o t, V2.Event.deliver x o t ∈ rho.events ∧ o.payload = Msg.proposal N) ∨
  (∃ x ∈ rho.honest, ∃ i : Nat,
    N ∈ (V2.D.Run.stateBefore E rho i x).st.namedBodies)

/-- [PC-SA M1; DC NamedRun.blockInRun] Close the exact named seeds under ancestry. -/
def NamedProposalInRun (A : NamedProposal p.n) : Prop :=
  ∃ B : NamedProposal p.n,
    DirectNamedProposalInRun p c E rho B ∧ NamedProposal.Preceq A B

/-- [PC-SA M1; DC NamedRootCollisionFree] The single full-identity run premise:
two named proposals in the run with one root are equal. -/
structure NamedRootCollisionFree : Prop where
  root_injective : ∀ B C : NamedProposal p.n,
    NamedProposalInRun p c E rho B → NamedProposalInRun p c E rho C →
    ∀ A D : NamedProposal p.n,
      (NamedProposal.Preceq A B ∨ NamedProposal.Preceq A C) →
      (NamedProposal.Preceq D B ∨ NamedProposal.Preceq D C) →
      A.root = D.root → A = D

/-- [PC-SA M1; DC NamedRun.directBlockInRun] Project the direct named scope. -/
def DirectRootBlockInRun (b : Block) : Prop :=
  ∃ N : NamedProposal p.n, DirectNamedProposalInRun p c E rho N ∧ N.erase = b

/-- [PC-SA M1; DC NamedRun.blockInRun] Project the ancestor-closed named scope. -/
def RootBlockInRun (b : Block) : Prop :=
  ∃ N : NamedProposal p.n, NamedProposalInRun p c E rho N ∧ N.erase = b

end AvailableChain.PCSA.Run
end
