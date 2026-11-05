module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.View
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.Label
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Client
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Trace

@[expose] public section

/-! # Goldilocks node: the node state and the component calls

The node composed with an AC (`specs/goldilocks/tex/shared/composition.tex` §"State",
§"Node"): parametric in `A : ACInterface P (List (FG.Att P.n))`,
the AC whose blocks carry the FG's attestation list. The node keeps the FG state `Σ`
(`Store P A.Payload`), the AC state `𝒜` and the validator's durable record `Λ`; the clock is
an argument of every handler that calls the AC (`Spec/Node/Reachable` carries it). Only the FG
functions read and write `Σ`, only the AC functions read and write `𝒜`, and only `fg_attest`
reads and writes `Λ`.

A node handler is a finite sequence of **component calls**, each exactly one FG call or one AC
call, with the frame `fg_to_ac(Σ)` recomputed before each AC call. The
calls are the **cuts** of a run (`Spec/Trace`, claims C0.4, C0.5): `Cut` records each with its
observations, an AC call by its `ACLabel` (call, frame, emissions), an FG call by `FGLabel`
(`Spec/FG/Store/Label`: the block and whether it was accepted; the attestation processed;
the source given to `fg_attest` and the attestation it signed, if any). A refused
`fg_on_block` is a call with no write, so it is a cut (`accepted := false`); the AC does not
see it. -/

namespace Consensus.Goldilocks

/-- An AC for the node: its blocks carry the FG payload, the attestation list. -/
abbrev NodeAC (P : Params) := ACInterface P (List (FG.Att P.n))

variable {P : Params}

/-- The node state: the FG state `Σ`, the AC state `𝒜` and the record `Λ`. -/
structure NodeState (A : NodeAC P) where
  /-- The FG state `Σ`. -/
  fg : Store P A.Payload
  /-- The AC state `𝒜`. -/
  ac : A.State
  /-- The anti-slashing record `Λ` of the validator. -/
  record : FG.Record

/-- A cut of the node: one component call with its observations. -/
inductive Cut (A : NodeAC P) where
  /-- An FG call. -/
  | fg (ℓ : FGLabel P A.Payload)
  /-- An AC call, with the frame it was given and its emissions. -/
  | ac (ℓ : ACLabel A)

namespace Node

variable {A : NodeAC P}

/-- The initial node state: the initial FG state with the AC's genesis payload, the initial
AC state, the empty record (composition.tex §"State"). -/
def init (A : NodeAC P) : NodeState A :=
  ⟨Store.init A.genesisPayload, A.initial, FG.Record.empty⟩

/-- The frame the node gives the AC: `fg_to_ac(Σ)` of the current FG state. -/
noncomputable def frame (st : NodeState A) : A.Frm := st.fg.toFrame

/-- One AC call `c` of validator `self` at time `t`, with the frame recomputed: the new node
state (only `𝒜` changes) and the cut, labelled with the call, that frame and the emissions. -/
noncomputable def acCall (self : Fin P.n) (st : NodeState A) (t : Time) (c : A.Call) :
    NodeState A × Cut A :=
  let Φ := frame st
  let r := A.step self st.ac Φ t c
  ({ st with ac := r.1 }, .ac ⟨c, Φ, r.2⟩)

/-- `ac_proposal(𝒜, Φ, t)` as a cut (no emissions), with its returned value: the parent (a duty
head) and the AC payload, or `⊥`. -/
noncomputable def acProposal (st : NodeState A) (t : Time) :
    NodeState A × Cut A × Option (DutyHead P.n (List (FG.Att P.n)) A.Payload × A.Payload) :=
  let Φ := frame st
  let r := A.proposal st.ac Φ t
  ({ st with ac := r.1 }, .ac ⟨.proposal, Φ, []⟩, r.2)

/-- `ac_to_fg(𝒜, Φ, t)` as a cut (no emissions), with its returned value `fg_confirmed`. -/
noncomputable def acToFG (st : NodeState A) (t : Time) :
    NodeState A × Cut A × Option A.Blk :=
  let Φ := frame st
  let r := A.toFG st.ac Φ t
  ({ st with ac := r.1 }, .ac ⟨.toFG, Φ, []⟩, r.2)

end Node

end Consensus.Goldilocks

end
