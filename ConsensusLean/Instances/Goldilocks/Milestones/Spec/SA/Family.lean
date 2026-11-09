module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Events
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Observation
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Events
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.WriteModes.Writes

@[expose] public section

namespace Consensus.Goldilocks.SA

/-- AC operations with the SA payload carrier fixed by construction. State and messages
remain arbitrary; the existing AC interface supplies all derived operations. -/
structure SAOperations (sp : SAParams) (FGP S M : Type) where
  validPayload : Blk sp.n FGP → Prop
  validMsg : M → Prop
  holdsMsg : S → M → Prop
  genesisPayload : Payload sp.n
  initial : S
  onMessage : Fin sp.n → S → Frm sp.n FGP → Time → M →
    S × List (Emission sp.n FGP (Payload sp.n) S M)
  onBlock : Fin sp.n → S → Frm sp.n FGP → Time → Blk sp.n FGP →
    S × List (Emission sp.n FGP (Payload sp.n) S M)
  onTick : Fin sp.n → S → Frm sp.n FGP → Time →
    S × List (Emission sp.n FGP (Payload sp.n) S M)
  proposal : S → Frm sp.n FGP → Time →
    S × Option (DutyHead sp.n FGP (Payload sp.n) × Payload sp.n)
  toFG : S → Frm sp.n FGP → Time → S × Option (Blk sp.n FGP)
  confirmed : S → Frm sp.n FGP → Time → Blk sp.n FGP
  head : S → Frm sp.n FGP → Time → Blk sp.n FGP
  restart : Fin sp.n → S → Frm sp.n FGP → Time →
    S × List (Emission sp.n FGP (Payload sp.n) S M)

variable {sp : SAParams} {FGP S M : Type} {ro : ReplayOrder sp FGP}

/-- No carrier equality transport occurs in this constructor. -/
def SAOperations.toAC (A : SAOperations sp FGP S M) : ACInterface sp.toParams FGP :=
  ⟨S, M, Payload sp.n, A.validPayload, A.validMsg, A.holdsMsg,
   A.genesisPayload, A.initial, A.onMessage, A.onBlock, A.onTick,
   A.proposal, A.toFG, A.confirmed, A.head, A.restart⟩

/-- Forgetful observation data, independent of any execution law. -/
structure SAFamily (A : SAOperations sp FGP S M) (ro : ReplayOrder sp FGP) where
  stateView : S → SAState sp.n
  voteEmbed : Vote sp.n → M
  voteView : M → Option (Vote sp.n)
  sg : M → Fin sp.n
  vote_retract : ∀ v, voteView (voteEmbed v) = some v
  vote_signer : ∀ m v, voteView m = some v → sg m = v.val
  genesis : A.genesisPayload = (goldilocksSA sp FGP ro).genesisPayload
  initial : stateView A.initial = (goldilocksSA sp FGP ro).initial
  mode : WriteMode

namespace SAFamily

variable {A : SAOperations sp FGP S M} (F : SAFamily A ro)

/-- Retain the full read point and duty head of each projected vote. -/
def projEm (e : A.toAC.Em) : Option (Em sp FGP) :=
  (F.voteView e.msg).map fun v => ⟨v, F.stateView e.readPoint, e.head⟩

/-- Only messages outside the vote view are erased. -/
def projCall : A.toAC.Call → Option (goldilocksSA sp FGP ro).Call
  | .tick => some .tick
  | .proposal => some .proposal
  | .toFG => some .toFG
  | .message m => (F.voteView m).map ACInterface.Call.message
  | .block B => some (.block B)
  | .restart => some .restart

/-- A retained call preserves its frame and the exact ordered projected emissions. -/
def projLabel (ℓ : ACLabel A.toAC) : Option (ACLabel (goldilocksSA sp FGP ro)) :=
  (F.projCall ℓ.call).map fun c => ⟨c, ℓ.frame, ℓ.emits.filterMap F.projEm⟩

/-- Projection preserves cuts, including arbitrarily many erased calls. -/
def proj (tr : ACTrace A.toAC) : SATrace sp FGP ro :=
  { init := fun y => F.stateView (tr.init y), node := tr.node,
    time := tr.time, event := tr.event, pos := tr.pos,
    label := fun i => (tr.label i).bind F.projLabel,
    post := fun i => F.stateView (tr.post i), awake := tr.awake,
    observationHorizon := tr.observationHorizon }

end SAFamily

variable {A : SAOperations sp FGP S M}

/-- Honest state commutation and honest erased-call stuttering, not handler equality. -/
structure ObservationAgreement (F : SAFamily A ro)
    (H : Set (Fin sp.n)) (tr : ACTrace A.toAC) : Prop where
  state : ∀ y ∈ H, ∀ i, (F.proj tr).state y i = F.stateView (tr.state y i)
  erased_state : ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ →
    F.projCall ℓ.call = none →
    F.stateView (tr.post i) = F.stateView (tr.state y i)
  erased_emissions : ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ →
    F.projCall ℓ.call = none → ℓ.emits.filterMap F.projEm = []

/-- Structural correspondence to actual candidate outputs, not semantic correctness. -/
structure OutputAgreement (F : SAFamily A ro) (H : Set (Fin sp.n))
    (tr : ACTrace A.toAC) : Prop where
  toFG : ∀ x ∈ H, ∀ i ℓ C, ACToFGAt tr x i ℓ C →
    ∃ q : S, F.stateView q = (F.proj tr).state x i ∧
      q = tr.state x i ∧ (A.toFG q ℓ.frame (tr.time i)).2 = some C
  proposal : ∀ x ∈ H, ∀ i ℓ d p, ACProposalAt tr x i ℓ d p →
    ∃ q : S, F.stateView q = (F.proj tr).state x i ∧
      q = tr.state x i ∧ (A.proposal q ℓ.frame (tr.time i)).2 = some (d, p)

namespace Growing

/-- Growing honesty is checked at the actual cut, including for erased calls. -/
structure ObservationAgreement (F : SAFamily A ro)
    (H : Time → Set (Fin sp.n)) (tr : ACTrace A.toAC) : Prop where
  state : ∀ y i, y ∈ H (tr.time i) →
    (F.proj tr).state y i = F.stateView (tr.state y i)
  erased_state : ∀ y i ℓ, y ∈ H (tr.time i) → tr.CallAt y i ℓ →
    F.projCall ℓ.call = none → F.stateView (tr.post i) = F.stateView (tr.state y i)
  erased_emissions : ∀ y i ℓ, y ∈ H (tr.time i) → tr.CallAt y i ℓ →
    F.projCall ℓ.call = none → ℓ.emits.filterMap F.projEm = []

end Growing

end Consensus.Goldilocks.SA

end
