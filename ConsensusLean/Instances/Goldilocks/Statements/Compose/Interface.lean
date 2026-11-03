module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Interface

@[expose] public section

/-! # Goldilocks milestone Compose/AnyAC: the interface (statements)

What the node and the FG may conclude about **any** AC that meets requirements 1–5
(`ACInterface.Requirements`, claims A0.6 with A0.9), at its reachable states with the frame of
its last call (decomposition §2 D, "the FG input contract derived from A0.6/A0.9"; claims C0.1,
C0.5 (c)): the parent of a proposal, the source `fg_confirmed`, the head of every emitted duty
and the two AC tips are blocks of the frame's tree that extend its root `Φ.F`, and the tips are
nested. These are the frame-level consequences of the requirements under a well-formed frame
(`FrameIn`: `FrameOK` inside `U`, so `fc_root ∈ Φ.tree` and the tree is rooted at `Φ.F`); they
mention no node and no particular AC. `Statements/Compose/Node` instantiates them at the node's
AC states (C0.5).

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Compose

variable {P : Params} {FGP : Type} (A : ACInterface P FGP)

/-- **The tips are nested (C0.1 at the AC).** At a reachable AC state with frame `Φ`, at any
time not before its last call, `ac_confirmed` and `ac_head` are blocks of `Φ.tree`, and
`Φ.F ⪯ ac_confirmed ⪯ ac_head` inside `Φ.tree`. -/
def TipsNested : Prop :=
  A.Requirements → A.AtReachable fun _ _ s Φ t₀ => ∀ t, t₀ ≤ t →
    A.confirmed s Φ t ∈ Φ.tree ∧ A.head s Φ t ∈ Φ.tree ∧
      Φ.Anc Φ.F (A.confirmed s Φ t) ∧ Φ.Anc (A.confirmed s Φ t) (A.head s Φ t)

/-- **The parent of a proposal is held.** At a reachable AC state with frame `Φ`, the parent
that `ac_proposal` returns at a slot start not before its last call is a block of `Φ.tree`
that extends `Φ.F` (requirement 1, `Φ.Anc Φ.fcRoot d.head`, under a well-formed frame;
requirement 5 says the rest about a proposal, directly). -/
def ProposalParentHeld : Prop :=
  A.Requirements → A.AtReachable fun _ _ s Φ t₀ => ∀ σ : Nat, t₀ ≤ P.slotTime σ → ∀ d p,
    (A.proposal s Φ (P.slotTime σ)).2 = some (d, p) →
      d.head ∈ Φ.tree ∧ Φ.Anc Φ.F d.head

/-- **The source is held.** At a reachable AC state with frame `Φ`, a block `fg_confirmed ≠ ⊥`
that `ac_to_fg` returns at a time not before its last call is a block of `Φ.tree` that
extends `Φ.F` (requirement 2 under a well-formed frame). -/
def SourceHeld : Prop :=
  A.Requirements → A.AtReachable fun _ _ s Φ t₀ => ∀ t, t₀ ≤ t → ∀ C,
    (A.toFG s Φ t).2 = some C → C ∈ Φ.tree ∧ Φ.Anc Φ.F C

/-- **Duty heads are held.** The head of every emission of a lawful call from a reachable AC
state is a block of the call's frame that extends its root (requirement 1 under a well-formed
frame). -/
def DutyHeadsHeld : Prop :=
  A.Requirements → A.AtReachable fun self U s Φ t₀ => ∀ t (c : A.Call) Φ', t₀ ≤ t →
    A.CallOK U Φ t c Φ' → ∀ e ∈ (A.step self s Φ' t c).2, ∀ d, e.head = some d →
      d.head ∈ Φ'.tree ∧ Φ'.Anc Φ'.F d.head

/-- The Compose/AnyAC interface statements, for one AC. -/
structure InterfaceStatements : Prop where
  tipsNested : TipsNested A
  proposalParentHeld : ProposalParentHeld A
  sourceHeld : SourceHeld A
  dutyHeadsHeld : DutyHeadsHeld A

/-- The Compose/AnyAC interface statements, for every AC of every parameter set and FG
payload. -/
def ComposeInterfaceStatements : Prop :=
  ∀ (P : Params) (FGP : Type) (A : ACInterface P FGP), InterfaceStatements A

end Consensus.Goldilocks.Compose

end
