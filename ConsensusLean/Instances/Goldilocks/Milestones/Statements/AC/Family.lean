module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Family

@[expose] public section

/-! # The update seam of the AC contract

Only the update-to-effective-record slice is covered here. The projected trace need not be
a local run of the SA. The two fields replace exactly the frame and execution facts consumed
by this slice; no complete handler execution law is assumed.
-/

namespace Consensus.Goldilocks.SA

/-- At a scheduled update the projected post-state is the confirmation update's result. -/
def UpdateCharacterization {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}
    (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) : Prop :=
  ∀ y ∈ H, ∀ c s ℓ, UpdateAt tr y c s ℓ →
    tr.post c = updateConfirmation sp (tr.state y c) ℓ.frame (tr.time c) s

/-- The minimal trace contract for update-to-effective-record transport. -/
structure ACContract {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}
    {S M : Type} {A : SAOperations sp FGP S M} (F : SAFamily sp FGP ro A)
    (H : Set (Fin sp.n)) (tr : ACTrace A.toAC) : Prop where
  /-- Honest projected calls have valid frames. -/
  frame : ∀ y ∈ H, ∀ i ℓ, (F.proj tr).CallAt y i ℓ → FrameOK ℓ.frame
  /-- The scheduled update has the characterized post-state. -/
  update : UpdateCharacterization (F.proj tr) H

end Consensus.Goldilocks.SA

end
