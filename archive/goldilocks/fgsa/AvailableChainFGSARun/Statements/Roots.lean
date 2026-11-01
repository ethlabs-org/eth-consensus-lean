module
public import AvailableChainFGSARun.Model.Protocol
public import AvailableChainEngineV2.Engine.Duty.Run

@[expose] public section

namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W1; DC NamedRun.directBlockInRun] Exact delivered or held bodies. -/
def DirectNamedProposalInRun (N : NamedProposal p.n) : Prop :=
  (∃ x o t, V2.Event.deliver x o t ∈ rho.events ∧ o.payload = Msg.proposal N) ∨
  (∃ x ∈ rho.honest, ∃ i : Nat,
    N ∈ (V2.D.Run.stateBefore E rho i x).st.namedBodies)

/-- [ROOT-DIGEST-2 W1; DC NamedRun.blockInRun] Close the exact named seeds under ancestry. -/
def NamedProposalInRun (A : NamedProposal p.n) : Prop :=
  ∃ B : NamedProposal p.n,
    DirectNamedProposalInRun p c E rho B ∧ NamedProposal.Preceq A B

/-- [ROOT-DIGEST-2 W1; DC NamedRootCollisionFree] The single full-identity run premise. -/
structure NamedRootCollisionFree : Prop where
  root_injective : ∀ B C : NamedProposal p.n,
    NamedProposalInRun p c E rho B → NamedProposalInRun p c E rho C →
    ∀ A D : NamedProposal p.n,
      (NamedProposal.Preceq A B ∨ NamedProposal.Preceq A C) →
      (NamedProposal.Preceq D B ∨ NamedProposal.Preceq D C) →
      A.root = D.root → A = D

/-- [P23-A] Delivered or held bodies, honest emitted bodies, and their named ancestors.
This is a run-scoped idealization under valid execution. A global form over all
values is false: root is a free field of NamedProposal. -/
def NamedProposalReceiptScope (A : NamedProposal p.n) : Prop :=
  NamedProposalInRun p c E rho A ∨
  ∃ v, v ∈ rho.honest ∧ ∃ o t N,
    V2.D.Run.emits E rho v o t ∧ o.payload = Msg.proposal N ∧
    NamedProposal.Preceq A N

/-- [P23-A] Root equality identifies exact bodies in the receipt scope.
A global form over all values is false: root is a free field. This premise
is an idealization under valid execution, not injectivity for every Params. -/
def NamedReceiptRootCollisionFree : Prop :=
  ∀ A B : NamedProposal p.n,
    NamedProposalReceiptScope p c E rho A →
    NamedProposalReceiptScope p c E rho B → A.root = B.root → A = B

/-- [ROOT-DIGEST-2 W1; DC NamedRun.directBlockInRun] Project the direct named scope. -/
def DirectRootBlockInRun (b : Block) : Prop :=
  ∃ N : NamedProposal p.n, DirectNamedProposalInRun p c E rho N ∧ N.erase = b

/-- [ROOT-DIGEST-2 W1; DC NamedRun.blockInRun] Project the ancestor-closed named scope. -/
def RootBlockInRun (b : Block) : Prop :=
  ∃ N : NamedProposal p.n, NamedProposalInRun p c E rho N ∧ N.erase = b

end AvailableChain.FGSA.Run
end
