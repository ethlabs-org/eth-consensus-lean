module
public import ConsensusLean.Instances.Goldilocks.Spec.Node.Handlers
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Common.Block

@[expose] public section

/-! # Goldilocks milestone vocabulary: duties, tick steps and event execution

The part of `Spec/Node/Handlers` that no Challenge statement reaches (docs/decisions.md,
2026-11-04): the milestone statements use it; it is not on the trusted surface. Names and bodies are
unchanged.

* `propose_block(H, p)`: the block with parent `H`, slot `slot(t)`, proposer `self`, the
  attestations `proposal_attestations(Σ, H)` and the AC payload `p`, its root the digest of its
  content; then the own `on_block(B)` (the broadcast is the acceptance, which a run observes);
* `attest(C)`: `fg_attest(Σ, Λ, C)`; when it signs, the record is replaced and the own
  attestation is processed at once by `on_attestation`;
* `on_tick(t)`, with the tick's input (the encoded transactions of a proposal): the tick steps
  `tickSteps` in order (claims C0.4): the AC's tick; at `t_s` with `s > 0`, for the slot's
  proposer, `ac_proposal`, then `propose_block` when it returns a proposal; the FG update,
  `ac_to_fg` and then `attest(fg_confirmed)` when it is not `⊥`.

`Event` is a top-level event of a node and `exec` runs its handler; `WireOK` is the input
contract of a delivery (composition.tex §"Blocks": the root is the digest of the content, the
carried attestations and a received attestation have the forms of fg.tex, the AC payload
passes `ac_valid_payload`, an AC message passes the AC's checks). -/

namespace Consensus.Goldilocks.Node

variable {P : Params} {A : NodeAC P}

/-- The block `propose_block` makes at validator `self` and time `t` from the FG state `Σ`, the
parent `H`, the AC payload `p` and the input `x` (the tick's; `Block.input`): slot `slot(t)`,
the attestations `proposal_attestations(Σ, H)`, its root the digest `dg` of its content. -/
noncomputable def mkBlock (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (fg : Store P A.Payload) (t : Time) (x : Nat) (H : A.Blk) (p : A.Payload) : A.Blk :=
  let atts := fg.proposalAttestations H
  { root := dg (some H.root) (P.slotOf t) x atts p, parent := some H.root, slot := P.slotOf t,
    proposer := self, input := x, fgPayload := atts, acPayload := p }

/-- `propose_block(H, p)`: the block (with the tick's input `x`), then the own `on_block`. -/
noncomputable def proposeBlock (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) (H : A.Blk) (p : A.Payload) :
    NodeState A × List (Cut A) :=
  onBlock self st t (mkBlock dg self st.fg t x H p)

/-- `attest(C)` at validator `self`: `fg_attest(Σ, Λ, C)`; when it signs `a`, the new record
and the own `on_attestation(a)`. -/
def attest (self : Fin P.n) (st : NodeState A) (C : A.Blk) : NodeState A × List (Cut A) :=
  match st.fg.attest st.record self C with
  | none => (st, [.fg (.attest C none)])
  | some (a, Λ') =>
      let r := onAttestation { st with record := Λ' } a
      (r.1, .fg (.attest C (some a)) :: r.2)

/-- The steps of a tick (claims C0.4). -/
inductive TickStep where
  /-- `ac_on_tick`. -/
  | acTick
  /-- At `t_s` with `s > 0`, for the slot's proposer: `ac_proposal`, then `propose_block`. -/
  | proposal
  /-- The FG update: `ac_to_fg`, then `attest(fg_confirmed)` when it is not `⊥`. -/
  | fgUpdate

/-- The order of the steps of a tick: the AC's tick, the proposal duty, the FG update
(composition.tex §"Node"; claims C0.4). -/
def tickSteps : List TickStep := [.acTick, .proposal, .fgUpdate]

/-- Whether validator `self` proposes at time `t`: `t = t_s` for a slot `s > 0` whose proposer
is `self`. -/
def Proposes (proposer : Nat → Fin P.n) (self : Fin P.n) (t : Time) : Prop :=
  0 < P.slotOf t ∧ t = P.slotTime (P.slotOf t) ∧ proposer (P.slotOf t) = self

instance (proposer : Nat → Fin P.n) (self : Fin P.n) (t : Time) :
    Decidable (Proposes (P := P) proposer self t) :=
  inferInstanceAs (Decidable (0 < P.slotOf t ∧ t = P.slotTime (P.slotOf t) ∧
    proposer (P.slotOf t) = self))

/-- One tick step at validator `self` and time `t`, with the tick's input `x` (the encoded
transactions a proposal carries; only the proposal step reads it). -/
noncomputable def tickStep (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) : TickStep → NodeState A × List (Cut A)
  | .acTick =>
      let r := acCall self st t .tick
      (r.1, [r.2])
  | .proposal =>
      if Proposes proposer self t then
        let r := acProposal st t
        match r.2.2 with
        | none => (r.1, [r.2.1])
        | some (d, p) =>
            let r' := proposeBlock dg self r.1 t x d.head p
            (r'.1, r.2.1 :: r'.2)
      else (st, [])
  | .fgUpdate =>
      let r := acToFG st t
      match r.2.2 with
      | none => (r.1, [r.2.1])
      | some C =>
          let r' := attest self r.1 C
          (r'.1, r.2.1 :: r'.2)

/-- The tick steps `steps` in order from `st`: each reads the state the earlier ones left; the
cuts are concatenated. -/
noncomputable def runSteps (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) (steps : List TickStep) :
    NodeState A × List (Cut A) :=
  steps.foldl (fun acc step =>
    let r := tickStep proposer dg self acc.1 t x step
    (r.1, acc.2 ++ r.2)) (st, [])

/-- `on_tick(t)` at validator `self` with the input `x`: `tickSteps` in order. -/
noncomputable def onTick (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) : NodeState A × List (Cut A) :=
  runSteps proposer dg self st t x tickSteps

/-- The handler of an event at validator `self` and time `t`. -/
noncomputable def exec (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) : Event A → NodeState A × List (Cut A)
  | .tick x => onTick proposer dg self st t x
  | .block B => onBlock self st t B
  | .message m => onMessage self st t m
  | .attestation a => onAttestation st a
  | .restart => restart self st t

/-- The wire checks of a delivery (composition.tex §"Blocks"): a block's root is the digest
of its content, its attestations have the forms of fg.tex and its payload passes
`ac_valid_payload`; an AC message passes the AC's checks; an attestation has the forms of
fg.tex. A tick and a restart carry no object. -/
def WireOK (dg : Digest (List (FG.Att P.n)) A.Payload) : Event A → Prop
  | .block B => B.RootOk dg ∧ (∀ a ∈ B.fgPayload, a.WellFormed) ∧ A.validPayload B
  | .message m => A.validMsg m
  | .attestation a => a.WellFormed
  | .tick _ => True
  | .restart => True

end Consensus.Goldilocks.Node

end
