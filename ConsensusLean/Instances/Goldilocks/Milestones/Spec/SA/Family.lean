module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Events

@[expose] public section

/-! # Forgetful AC trace families

The projection preserves cut indices and observation metadata. A candidate call may disappear
from the projection, for example an acknowledgement receipt; the converse is forbidden.
This trace-only interface does not relate full node states or engine executions.
-/

namespace Consensus.Goldilocks.SA

/-- Candidate operations with the SA's payload and block types, but arbitrary state and
messages. A message view may forget acknowledgements without casting votes or blocks. -/
structure SAOperations (sp : SAParams) (FGP S M : Type) where
  /-- Stateless payload validity. -/
  validPayload : Blk sp.n FGP → Prop
  /-- Stateless message validity. -/
  validMsg : M → Prop
  /-- Message admission. -/
  holdsMsg : S → M → Prop
  /-- Genesis uses the SA payload type. -/
  genesisPayload : Payload sp.n
  /-- Initial candidate state. -/
  initial : S
  /-- Message transition. -/
  onMessage : Fin sp.n → S → Frm sp.n FGP → Time → M →
    S × List (Emission sp.n FGP (Payload sp.n) S M)
  /-- Accepted-block transition. -/
  onBlock : Fin sp.n → S → Frm sp.n FGP → Time → Blk sp.n FGP →
    S × List (Emission sp.n FGP (Payload sp.n) S M)
  /-- Tick transition. -/
  onTick : Fin sp.n → S → Frm sp.n FGP → Time →
    S × List (Emission sp.n FGP (Payload sp.n) S M)
  /-- Proposal transition. -/
  proposal : S → Frm sp.n FGP → Time → S × Option (DutyHead sp.n FGP (Payload sp.n) × Payload sp.n)
  /-- FG-source transition. -/
  toFG : S → Frm sp.n FGP → Time → S × Option (Blk sp.n FGP)
  /-- Confirmed read. -/
  confirmed : S → Frm sp.n FGP → Time → Blk sp.n FGP
  /-- Head read. -/
  head : S → Frm sp.n FGP → Time → Blk sp.n FGP
  /-- Restart transition. -/
  restart : Fin sp.n → S → Frm sp.n FGP → Time →
    S × List (Emission sp.n FGP (Payload sp.n) S M)

/-- Build an AC whose payload and blocks are definitionally the SA's, not merely equal. -/
abbrev SAOperations.toAC {sp : SAParams} {FGP S M : Type} (A : SAOperations sp FGP S M) :
    ACInterface sp.toParams FGP :=
  ⟨S, M, Payload sp.n, A.validPayload, A.validMsg, A.holdsMsg, A.genesisPayload,
    A.initial, A.onMessage, A.onBlock, A.onTick, A.proposal, A.toFG, A.confirmed, A.head,
    A.restart⟩

/-- An AC trace viewed in SA vocabulary, without assuming the SA's transition law. -/
structure SAFamily (sp : SAParams) (FGP : Type) (ro : ReplayOrder sp FGP)
    {S M : Type} (A : SAOperations sp FGP S M) where
  /-- Forget candidate-specific state and calls. -/
  proj : ACTrace A.toAC → SATrace sp FGP ro
  /-- A candidate message is a vote or an extra message that is forgotten. -/
  voteView : M → Option (Vote sp.n)
  /-- Nodes keep their cut indices. -/
  node : ∀ tr, (proj tr).node = tr.node
  /-- Observation times are unchanged. -/
  time : ∀ tr, (proj tr).time = tr.time
  /-- Event identities are unchanged. -/
  event : ∀ tr, (proj tr).event = tr.event
  /-- Positions within events are unchanged, even when a call is forgotten. -/
  pos : ∀ tr, (proj tr).pos = tr.pos
  /-- Wakefulness is unchanged. -/
  awake : ∀ tr, (proj tr).awake = tr.awake
  /-- The observation horizon is unchanged. -/
  horizon : ∀ tr, (proj tr).observationHorizon = tr.observationHorizon
  /-- A projected call must come from a candidate call; candidate calls may stutter. -/
  labelled : ∀ tr i, (proj tr).label i ≠ none → tr.label i ≠ none
  /-- A retained call reads exactly the candidate call's frame. -/
  frame : ∀ tr i ℓ, (proj tr).label i = some ℓ →
    ∃ ℓ', tr.label i = some ℓ' ∧ ℓ.frame = ℓ'.frame
  /-- Vote emissions, ignoring candidate-only messages, keep their signer and cut. -/
  votes : ∀ tr y i v, (∃ e, VoteAt (proj tr) y i e ∧ e.msg = v) ↔
    ∃ ℓ, tr.CallAt y i ℓ ∧ ∃ e ∈ ℓ.emits, voteView e.msg = some v
  /-- Accepted block calls keep their payload, caller and cut. -/
  blocks : ∀ tr y i B, (proj tr).AcceptAt y i B ↔ tr.AcceptAt y i B

/-- The SA's operations packaged with definitionally fixed payload and block types. -/
noncomputable def goldilocksOperations (sp : SAParams) (FGP : Type)
    (ro : ReplayOrder sp FGP) : SAOperations sp FGP (SAState sp.n) (Vote sp.n) where
  validPayload := (goldilocksSA sp FGP ro).validPayload
  validMsg := (goldilocksSA sp FGP ro).validMsg
  holdsMsg := (goldilocksSA sp FGP ro).holdsMsg
  genesisPayload := (goldilocksSA sp FGP ro).genesisPayload
  initial := (goldilocksSA sp FGP ro).initial
  onMessage := (goldilocksSA sp FGP ro).onMessage
  onBlock := (goldilocksSA sp FGP ro).onBlock
  onTick := (goldilocksSA sp FGP ro).onTick
  proposal := (goldilocksSA sp FGP ro).proposal
  toFG := (goldilocksSA sp FGP ro).toFG
  confirmed := (goldilocksSA sp FGP ro).confirmed
  head := (goldilocksSA sp FGP ro).head
  restart := (goldilocksSA sp FGP ro).restart

/-- The SA itself forgets nothing. -/
noncomputable def goldilocksFamily (sp : SAParams) (FGP : Type) (ro : ReplayOrder sp FGP) :
    SAFamily sp FGP ro (goldilocksOperations sp FGP ro) where
  proj := id
  voteView := some
  node := fun _ => rfl
  time := fun _ => rfl
  event := fun _ => rfl
  pos := fun _ => rfl
  awake := fun _ => rfl
  horizon := fun _ => rfl
  labelled := fun _ _ h => h
  frame := fun _ _ ℓ h => ⟨ℓ, h, rfl⟩
  votes := by
    intro tr y i v
    constructor
    · rintro ⟨e, ⟨ℓ, hc, he⟩, rfl⟩
      exact ⟨ℓ, hc, e, he, rfl⟩
    · rintro ⟨ℓ, hc, e, he, hv⟩
      exact ⟨e, ⟨ℓ, hc, he⟩, Option.some.inj hv⟩
  blocks := fun _ _ _ _ => Iff.rfl

end Consensus.Goldilocks.SA

end
