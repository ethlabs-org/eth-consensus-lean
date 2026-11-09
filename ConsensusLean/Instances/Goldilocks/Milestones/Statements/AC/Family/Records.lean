module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Locks

/-! # Independent record invariants, writes and read-point origins -/

@[expose] public section

namespace Consensus.Goldilocks.SA.FamilyFacts

variable {sp : SAParams} {FGP S M : Type} {ro : ReplayOrder sp FGP}

/-- The record is above every stored lock in the coherent universe. -/
def LockInvariant (U : Set (Blk sp.n FGP)) (st : SAState sp.n) (Φ : Frm sp.n FGP) : Prop :=
  ∃ E ∈ U, E.root = st.latestConfirmed ∧ (Anc U Φ.F E → E ∈ Φ.tree) ∧
    ∀ l ∈ st.locks, ∀ X ∈ U, X.root = l.block → Anc U X E

variable {A : SAOperations sp FGP S M} (F : SAFamily A ro) (tr : ACTrace A.toAC)
  (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))

/-- Independently supplied observed call-frame invariant. -/
def CallFrameInvariant : Prop :=
  ∀ y ∈ H, ∀ i ℓ, (F.proj tr).CallAt y i ℓ →
    LockInvariant U ((F.proj tr).state y i) ℓ.frame

/-- At an update the record has a frame representative above each live lock block. -/
def RecordAboveLive : Prop :=
  ∀ y ∈ H, ∀ i s ℓ, SA.UpdateAt (F.proj tr) y i s ℓ →
    ∀ L ∈ SA.liveLockBlocks sp ((F.proj tr).state y i).locks ℓ.frame ((F.proj tr).time i),
    ∃ E ∈ ℓ.frame.tree, E.root = ((F.proj tr).state y i).latestConfirmed ∧ ℓ.frame.Anc L E

/-- Record writes follow shared-formula results or enabled optimistic events. -/
def RecordWrites : Prop :=
  ∀ y ∈ H, ∀ i ℓ, (F.proj tr).CallAt y i ℓ →
    Relation.ReflTransGen
      (fun r r' => ∃ C ∈ ℓ.frame.tree,
        (∃ s CV, SA.ResultAt (F.proj tr) y i s C CV ∨
          OptimisticEvent F.mode (F.proj tr) y i s C CV) ∧
        ((SA.AncR ℓ.frame C r ∧ r' = r) ∨
         (¬ SA.AncR ℓ.frame C r ∧ r' = C.root)))
      ((F.proj tr).state y i).latestConfirmed ((F.proj tr).post i).latestConfirmed

/-- Receipt-origin witnesses precede this call's own cast strictly. -/
def ReadPointOrigin : Prop :=
  ∀ y ∈ H, ∀ i ℓ e, SA.CastAt (F.proj tr) y i ℓ e →
    0 < sp.slot ((F.proj tr).time i) → ∀ l' ∈ e.readPoint.locks,
    ∃ B' ∈ ℓ.frame.tree, B'.root = l'.block ∧
      ((∃ l ∈ ((F.proj tr).state y i).locks, ∃ B ∈ ℓ.frame.tree,
          B.root = l.block ∧ ℓ.frame.Anc B' B) ∨
       ∃ B CV, OptimisticEvent F.mode (F.proj tr) y i (sp.slot ((F.proj tr).time i)) B CV ∧
         (∀ v ∈ CV, v.val ∈ H → ∃ j < i, ∃ e',
           SA.VoteAt (F.proj tr) v.val j e' ∧ e'.msg = v) ∧ ℓ.frame.Anc B' B)

end Consensus.Goldilocks.SA.FamilyFacts

end
