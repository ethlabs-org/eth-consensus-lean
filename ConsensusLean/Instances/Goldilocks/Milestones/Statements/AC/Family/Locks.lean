module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Family

/-! # Enabled shared-policy write events and lock provenance packages -/

@[expose] public section

namespace Consensus.Goldilocks.SA.FamilyFacts

variable {sp : SAParams} {FGP S M : Type} {ro : ReplayOrder sp FGP}

/-- Enabled update formula witness, not a post-state lock-set difference. -/
def UpdateFastEvent (m : WriteMode) (o : SATrace sp FGP ro)
    (x : Fin sp.n) (i s : Nat) (B : Blk sp.n FGP) (CV : Set (Vote sp.n)) : Prop :=
  m.fastArm = true ∧ SA.FastUpdateAt o x i s B CV

/-- Enabled reconstructed-input optimistic witness. -/
def OptimisticEvent (m : WriteMode) (o : SATrace sp FGP ro)
    (x : Fin sp.n) (i s : Nat) (B : Blk sp.n FGP) (CV : Set (Vote sp.n)) : Prop :=
  m.optimistic = true ∧ SA.OptimisticLockAt o x i s B CV

/-- Either enabled fast-write formula; disabled arms cannot witness it. -/
def FastWriteEvent (m : WriteMode) (o : SATrace sp FGP ro)
    (x : Fin sp.n) (i s : Nat) (B : Blk sp.n FGP) (CV : Set (Vote sp.n)) : Prop :=
  UpdateFastEvent m o x i s B CV ∨ OptimisticEvent m o x i s B CV

variable {A : SAOperations sp FGP S M} (F : SAFamily A ro) (tr : ACTrace A.toAC)
  (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))

/-- Every stored lock descends from a result or enabled optimistic origin. -/
def LockOrigin : Prop :=
  ∀ y ∈ H, ∀ i l, l ∈ ((F.proj tr).state y i).locks →
    ∃ L ∈ U, L.root = l.block ∧ ∃ z ∈ H, ∃ j < i, ∃ C CV,
      (SA.ResultAt (F.proj tr) z j l.slot C CV ∨
        OptimisticEvent F.mode (F.proj tr) z j l.slot C CV) ∧ Anc U L C

/-- Execution suppliers must separately justify enabled witnesses and counted objects. -/
structure LockWrites : Prop where
  fastOrigin : ∀ y ∈ H, ∀ i l, l ∈ ((F.proj tr).state y i).locks → l.fast = true →
    ∃ j < i, ∃ B CV, FastWriteEvent F.mode (F.proj tr) y j l.slot B CV ∧
      ∃ L ∈ U, L.root = l.block ∧ Anc U L B
  counted : ∀ y ∈ H, ∀ i s B CV, FastWriteEvent F.mode (F.proj tr) y i s B CV →
    sp.n ≤ 2 * {u | ∃ v ∈ CV, v.val = u}.ncard ∧
      ∀ v ∈ CV, v.slot = s ∧ ∃ R ∈ U,
        R.root = v.head ∧ R.slot ≤ s ∧ Anc U B R
  authentic : ∀ y ∈ H, ∀ i s B CV, FastWriteEvent F.mode (F.proj tr) y i s B CV →
    ∀ v ∈ CV, v.val ∈ H → ∃ j ≤ i, ∃ e, SA.VoteAt (F.proj tr) v.val j e ∧ e.msg = v

/-- Slow compatibility uses the actual shared-policy saved-window width. -/
def SlowCompatibility : Prop :=
  ∀ y ∈ H, ∀ i l, l ∈ ((F.proj tr).state y i).locks → l.fast = false →
    ∀ B : Blk sp.n FGP,
    (∃ q : Int, (l.slot : Int) - F.mode.width < q ∧ q ≤ l.slot ∧ 0 ≤ q ∧
      ∀ j C CV, j < i → SA.ResultAt (F.proj tr) y j q.toNat C CV → Compatible U C B) →
    ∃ L ∈ U, L.root = l.block ∧ Compatible U L B

end Consensus.Goldilocks.SA.FamilyFacts

end
