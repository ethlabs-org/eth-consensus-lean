module
public import Mathlib.Data.Set.Card
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Common.Tree
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Trace
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.Label
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Handlers
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.Duties
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.State

@[expose] public section

/-! # Goldilocks FG store: FG traces

The FG component trace (decomposition §2 D, `FG.LocalRun`): a `Trace` over the FG state and the
client record `Σ × Λ` (the record is not part of `Σ`, fg.tex §"Validator client"), whose labelled
cuts are FG calls (`FGLabel`): `fg_on_block` (accepted or refused), `fg_on_attestation`, and
`fg_attest` with the attestation it signed. AC cuts and the other nodes' cuts are stutters. A
restart keeps `Σ` and `Λ` (composition.tex §"State"), so it is no FG call.

`FGLocalRun P ACP acp₀ H U tr` is the contract a node run's projection satisfies (claims C0.5
(c)), for the honest validators `H`, inside the coherent set `U`:

* each honest node starts from the initial FG state and the empty record, and each of its calls
  **executes** the FG on the pre-state (`FGLabel.Step`);
* every block that an honest node's FG state holds lies in `U` (at a node, the accepted blocks
  of the run: F.2, F.3);
* the cuts are in the run's order, by time, from time `0`; an honest node signs only in `attest`
  calls, at public times;
* **the tick order through the FG's own calls** (claims C0.4): at an honest node, the
  acceptance of its own proposal is its first FG cut at that time, and the only FG cut at the
  time of an `attest` call before it (no object received at that time is processed before the
  tick's FG update);
* the own proposal's attestations come from the node's pool;
* **unforgeability**: an attestation with an honest signer that an honest node processes (on the
  wire or in an accepted block) was signed by that validator at an earlier `attest` cut.

The network premise `Sync` over FG traces comes with the statements that need it. -/

namespace Consensus.Goldilocks

variable {P : Params} {ACP : Type}

/-- The FG state of a node: `Σ` and the client record `Λ`. -/
abbrev FGState (P : Params) (ACP : Type) := Store P ACP × FG.Record

/-- The execution law of an FG call of validator `v`: the post-state of the call `ℓ` from `s`.
`fg_on_block` writes only when it accepts; `fg_on_attestation` writes only the pool;
`fg_attest` writes only the record and reports what it signed (the node then processes its own
attestation at once, a separate `fg_on_attestation` cut). -/
def FGLabel.Step (v : Fin P.n) (s : FGState P ACP) : FGLabel P ACP → FGState P ACP → Prop
  | .block B accepted, s' =>
      (accepted = true ∧ s.1.onBlock B = some s'.1 ∧ s'.2 = s.2) ∨
      (accepted = false ∧ s.1.onBlock B = none ∧ s' = s)
  | .attestation a, s' => s' = (s.1.onAttestation a, s.2)
  | .attest src signed, s' =>
      s'.1 = s.1 ∧
      match s.1.attest s.2 v src with
      | some (a, Λ') => signed = some a ∧ s'.2 = Λ'
      | none => signed = none ∧ s'.2 = s.2

/-- The attestations that an FG call processes: the attestation of `fg_on_attestation`, and
those of a block that `fg_on_block` accepts. -/
def FGLabel.processed : FGLabel P ACP → List (FG.Att P.n)
  | .block B true => B.fgPayload
  | .block _ false => []
  | .attestation a => [a]
  | .attest _ _ => []

/-- An FG trace: per validator, the FG state and the record; labelled cuts are FG calls. -/
abbrev FGTrace (P : Params) (ACP : Type) := Trace (Fin P.n) (FGState P ACP) (FGLabel P ACP)

namespace FGTrace

variable (tr : FGTrace P ACP)

/-- `y` signs the attestation `a` at cut `i`. -/
def SignAt (y : Fin P.n) (i : Nat) (a : FG.Att P.n) : Prop :=
  ∃ src, tr.CallAt y i (.attest src (some a))

/-- `y` accepts the block `B` at cut `i`. -/
def AcceptAt (y : Fin P.n) (i : Nat) (B : NodeBlock P ACP) : Prop := tr.CallAt y i (.block B true)

/-- `y` processes the attestation `a` at cut `i` (on the wire, or in a block it accepts). -/
def ProcessAt (y : Fin P.n) (i : Nat) (a : FG.Att P.n) : Prop :=
  ∃ ℓ, tr.CallAt y i ℓ ∧ a ∈ ℓ.processed

/-- The FG state of `y` before cut `i`. -/
noncomputable abbrev store (y : Fin P.n) (i : Nat) : Store P ACP := (tr.state y i).1

end FGTrace

/-- The FG trace contract (claims C0.5 (c), C0.4) for the honest validators `H`, genesis AC
payload `acp₀`, inside the coherent set `U`. -/
structure FGLocalRun (acp₀ : ACP) (H : Set (Fin P.n)) (U : Set (NodeBlock P ACP))
    (tr : FGTrace P ACP) : Prop where
  /-- `U` is coherent: roots injective, slots increasing along parent edges. -/
  coherent : Coherent U
  /-- Each honest node starts from the initial FG state and the empty record. -/
  init : ∀ y ∈ H, tr.init y = (Store.init acp₀, FG.Record.empty)
  /-- Each call of an honest node executes the FG on its pre-state. -/
  exec : ∀ i ℓ, tr.label i = some ℓ → tr.node i ∈ H →
    FGLabel.Step (tr.node i) (tr.state (tr.node i) i) ℓ (tr.post i)
  /-- Every block of an honest node's tree lies in `U`. -/
  tree_subset : ∀ y ∈ H, ∀ i, (tr.store y i).tree ⊆ U
  /-- Cuts are at times from `0` on. -/
  time_nonneg : ∀ i, 0 ≤ tr.time i
  /-- The cut order is by time. -/
  time_mono : Monotone tr.time
  /-- An honest node signs only at public times. -/
  attest_public : ∀ y ∈ H, ∀ i src signed, tr.CallAt y i (.attest src signed) →
    P.IsPublic (tr.time i)
  /-- The tick order through the FG calls (C0.4), (a): an honest node's acceptance of its own
  proposal (a block with that node as proposer, at its slot's start) is its first FG cut at that
  time, before every object received at that time. (Only the acceptance: the node can receive
  its own block back at that time, a refused duplicate, after accepting it.) -/
  own_first : ∀ y ∈ H, ∀ i B, tr.CallAt y i (.block B true) → B.proposer = y →
    P.slotTime B.slot = tr.time i → ∀ k < i, ∀ ℓ, tr.CallAt y k ℓ → tr.time k < tr.time i
  /-- The tick order, (b): an FG cut of an honest node at the time of one of its `attest` calls
  and before it is the acceptance of its own proposal of that slot (the tick's step 3); no
  object received at that time is processed before the tick's FG update. -/
  attest_order : ∀ y ∈ H, ∀ j src signed, tr.CallAt y j (.attest src signed) →
    ∀ i ℓ, i < j → tr.CallAt y i ℓ → tr.time i = tr.time j →
      ∃ B acc, ℓ = .block B acc ∧ B.proposer = y ∧ P.slotTime B.slot = tr.time j
  /-- The own proposal's payload comes from the pool (C0.5 (c), `proposal_attestations`): every
  attestation of an honest node's own proposal is in its pool when it accepts the proposal. (True
  of the node because the proposer's slot key signs a block, composition.tex §"Blocks", so no other
  node makes a block with an honest proposer.) -/
  own_payload : ∀ y ∈ H, ∀ i B, tr.CallAt y i (.block B true) → B.proposer = y →
    P.slotTime B.slot = tr.time i → ∀ a ∈ B.fgPayload, a ∈ (tr.store y i).atts
  /-- Unforgeability: an attestation of an honest signer that an honest node processes was
  signed by that validator at an earlier cut. -/
  unforgeable : ∀ y ∈ H, ∀ i a, tr.ProcessAt y i a → a.val ∈ H →
    ∃ j < i, tr.SignAt a.val j a

end Consensus.Goldilocks

end
