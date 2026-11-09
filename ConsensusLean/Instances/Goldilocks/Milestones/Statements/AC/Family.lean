module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Family

@[expose] public section

/-! # Fieldwise update seams

Consumers request the record, frame or lock conjunct independently. The record formula does
not mention a write mode. No premise here says that the projected trace executes the SA.
-/

namespace Consensus.Goldilocks.SA

/-- Shared record and saved-result formula, independent of lock-write choices. -/
def UpdateRecord {sp : SAParams} {FGP : Type} (pre post : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (s : Nat) : Prop := by
  classical
  exact
    post.saved = Function.update pre.saved s ((getConfirmation sp pre Φ s).map Block.root) ∧
    post.latestConfirmed =
      (match getConfirmation sp pre Φ s with
      | none => pre.latestConfirmed
      | some C => if conflictsWithLock sp pre.locks Φ t C then pre.latestConfirmed
        else (updateLatestConfirmed sp pre Φ C).latestConfirmed)

/-- The update's unchanged fields, excluding its record, saved results and locks. -/
def UpdateFrame {sp : SAParams} (pre post : SAState sp.n) : Prop :=
  post.pool = pre.pool ∧ post.voteStamp = pre.voteStamp ∧
  post.blockStamp = pre.blockStamp ∧ post.fgReported = pre.fgReported ∧
  post.votedSlot = pre.votedSlot ∧ post.restartTime = pre.restartTime

/-- The update's locks at the selected mode, separated from its other fields. -/
def UpdateLocks {sp : SAParams} {FGP : Type} (mode : WriteMode) (pre post : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (s : Nat) : Prop :=
  post.locks = (updateConfirmationM sp mode pre Φ t s).locks

/-- The scheduled update's shared record formula. -/
def UpdateRecordAt {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}
    (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) : Prop :=
  ∀ y ∈ H, ∀ c s ℓ, UpdateAt tr y c s ℓ →
    UpdateRecord (tr.state y c) (tr.post c) ℓ.frame (tr.time c) s

/-- The minimal trace contract for update-to-effective-record transport. -/
structure ACContract {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}
    {S M : Type} {A : SAOperations sp FGP S M} (F : SAFamily sp FGP ro A)
    (H : Set (Fin sp.n)) (tr : ACTrace A.toAC) : Prop where
  /-- Honest projected calls have valid frames. -/
  frame : ∀ y ∈ H, ∀ i ℓ, (F.proj tr).CallAt y i ℓ → FrameOK ℓ.frame
  /-- The mode-independent record formula, available without the whole-state law. -/
  updateRecord : UpdateRecordAt (F.proj tr) H

end Consensus.Goldilocks.SA

end
