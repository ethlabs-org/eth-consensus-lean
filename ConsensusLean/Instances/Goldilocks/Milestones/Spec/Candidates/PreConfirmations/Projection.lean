module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Candidates.PreConfirmations.Actions
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Events

@[expose] public section

/-! # ½ pre-confirmations: the forgotten trace and the honest acks

The forgetful map from an AC trace of the ½-PC SA (`preConfSAM`) to an AC trace of the parent's
SA (`SATrace`), and the run facts about honest acks.

* `projCallPC`: a call of the PC SA as the parent's call; an ack receipt has none;
* `projEmPC`: a vote emission as the parent's emission at the core of its read point; an ack
  emission has none;
* `projTracePC`: the parent's states (the core's parent state), calls and emissions; an ack
  receipt is an unlabelled cut (a stutter), so the forgotten state of a node changes only at its
  other calls. That an honest node's forgotten state is the core of its state, because an ack
  receipt leaves the core unchanged, is a statement (`Candidates/PreConfirmations/Statements`).
  The forgotten trace is **not** a run of the parent's SA with the unlock given (`ACLocalRunU`):
  the PC moves the start of the head walks, so the votes, proposals and reads differ from the
  parent's on the same state;
* `HonestObjectsPC`: the honest-object facts of the forgotten trace (the votes), and ack
  authenticity: an ack of an honest validator that an honest node holds, or receives, was emitted
  by that validator's node at an earlier cut.

Definitions only. -/

namespace Consensus.Goldilocks.PreConfirmations

open SA EvidenceRelease

variable {sp : SAParams} {FGP : Type} {σ : Type} {E : UnlockStage sp wlockStore σ} {c : σ}
  {m : WriteMode} {ro : ReplayOrder sp FGP}

variable (E c m ro) in
/-- The parent's call of a call of the PC SA; an ack receipt has none. -/
abbrev projCallPC : (preConfSAM sp E c m FGP ro).Call → Option (goldilocksSA sp FGP ro).Call
  | .tick => some .tick
  | .proposal => some .proposal
  | .toFG => some .toFG
  | .message (.inl v) => some (.message v)
  | .message (.inr _) => none
  | .block B => some (.block B)
  | .restart => some .restart

/-- The parent's emission of a vote emission of the PC SA, at the core of its read point; an ack
emission has none. -/
def projEmPC (e : EmPC sp FGP) : Option (Em sp FGP) :=
  match e.msg with
  | .inl v => some ⟨v, e.readPoint.core.ac, e.head⟩
  | .inr _ => none

/-- The parent's label of a label of the PC SA: its call, frame and vote emissions; an ack receipt
has none. -/
abbrev projLabelPC (ℓ : ACLabel (preConfSAM sp E c m FGP ro)) :
    Option (ACLabel (goldilocksSA sp FGP ro)) :=
  (projCallPC E c m ro ℓ.call).map fun k => ⟨k, ℓ.frame, ℓ.emits.filterMap projEmPC⟩

/-- **The forgotten trace**: the parent's states, calls and vote emissions of an AC trace of the
PC SA; ack receipts are unlabelled cuts. -/
abbrev projTracePC (tr : ACTrace (preConfSAM sp E c m FGP ro)) : SATrace sp FGP ro where
  init y := (tr.init y).core.ac
  node := tr.node
  time := tr.time
  event := tr.event
  pos := tr.pos
  label i := (tr.label i).bind projLabelPC
  post i := (tr.post i).core.ac
  awake := tr.awake
  observationHorizon := tr.observationHorizon

/-- **Honest objects of a PC run**: the honest-object facts of the forgotten trace, and ack
authenticity (unforgeable ack signatures). -/
structure HonestObjectsPC (selectedProposer : Nat → Fin sp.n)
    (tr : ACTrace (preConfSAM sp E c m FGP ro)) (H : Set (Fin sp.n)) : Prop where
  /-- The honest-object facts of the votes and blocks, on the forgotten trace. -/
  core : HonestObjects selectedProposer (projTracePC tr) H
  /-- An ack of an honest validator held by an honest node before cut `i` was emitted by that
  validator's node at an earlier cut. -/
  held_ack : ∀ y ∈ H, ∀ i (a : Ack sp.n), a.val ∈ (tr.state y i).store.acks a.slot a.target a.j →
    a.val ∈ H → ∃ k < i, ∃ ℓ, tr.CallAt a.val k ℓ ∧ ∃ e ∈ ℓ.emits, e.msg = .inr a
  /-- An ack of an honest validator that an honest node receives at cut `i` was emitted by that
  validator's node at an earlier cut. -/
  message_ack : ∀ y ∈ H, ∀ i ℓ (a : Ack sp.n), tr.CallAt y i ℓ → ℓ.call = .message (.inr a) →
    a.val ∈ H → ∃ k < i, ∃ ℓ', tr.CallAt a.val k ℓ' ∧ ∃ e ∈ ℓ'.emits, e.msg = .inr a

end Consensus.Goldilocks.PreConfirmations

end
