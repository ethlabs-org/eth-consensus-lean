module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Family
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.SourceEvent

@[expose] public section

/-! # Safety vocabulary over a family's real node trace

The FG store and honest blocks belong to the node run. Only AC observations pass through
the family projection. These predicates assert no execution or retention law.
-/

namespace Consensus.Goldilocks.FamilySafety

open SA (SAParams ReplayOrder Payload SAOperations SAFamily)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {S M : Type} {A : SAOperations sp (List (FG.Att sp.n)) S M}
  (F : SAFamily sp (List (FG.Att sp.n)) ro A) (tr : RunTrace A.toAC)
  (H : Set (Fin sp.n))

/-- An origin observed within the horizon. -/
def OriginWithin (C : SA.Blk sp.n (List (FG.Att sp.n))) (s : Nat) (b : Time) : Prop :=
  ∃ x ∈ H, ∃ i CV, tr.time i ≤ b ∧
    (SA.ResultAt (F.proj tr.projAC) x i s C CV ∨
      SA.OptimisticLockAt (F.proj tr.projAC) x i s C CV)

/-- Genesis or an ancestor of an origin within the horizon. -/
def OnOriginChainWithin (B : SA.Blk sp.n (List (FG.Att sp.n))) (b : Time) : Prop :=
  B.root = sp.genesisRoot ∨ ∃ C s, OriginWithin F tr H C s b ∧ Anc (tr.HonestBlocks H) B C

/-- The prefix invariant shared by every family member. -/
structure SleepyInvariantUpTo (b : Time) : Prop where
  origins_compatible : ∀ C s C' s', OriginWithin F tr H C s b → OriginWithin F tr H C' s' b →
    Compatible (tr.HonestBlocks H) C C'
  vote_extends : ∀ C s, OriginWithin F tr H C s b → ∀ y ∈ H, ∀ i e,
    SA.VoteAt (F.proj tr.projAC) y i e → tr.time i ≤ b → s < e.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e.msg C
  record : ∀ y ∈ H, ∀ i, (∀ k < i, tr.time k ≤ b) →
    ∃ C ∈ (tr.state y i).fg.tree, C.root = ((F.proj tr.projAC).state y i).latestConfirmed ∧
      (C.root = sp.genesisRoot ∨ ∃ s, OriginWithin F tr H C s b)
  caches : ∀ y ∈ H, ∀ i, (∀ k < i, tr.time k ≤ b) →
    OnOriginChainWithin F tr H (tr.state y i).fg.F b ∧
      OnOriginChainWithin F tr H (tr.state y i).fg.J b
  locks : ∀ y ∈ H, ∀ i, (∀ k < i, tr.time k ≤ b) →
    ∀ l ∈ ((F.proj tr.projAC).state y i).locks,
      ∃ L ∈ (tr.state y i).fg.tree, L.root = l.block ∧ OnOriginChainWithin F tr H L b
  sources : ∀ y ∈ H, ∀ i, (∀ k < i, tr.time k ≤ b) → ∀ ℓ C,
    ACToFGAt tr.projAC y i ℓ C → OnOriginChainWithin F tr H C b
  viable : ∀ y ∈ H, ∀ i, (∀ k < i, tr.time k ≤ b) → ∀ C s,
    OriginWithin F tr H C s b → C ∈ (Node.frame (tr.state y i)).tree →
      (Node.frame (tr.state y i)).Anc C (Node.frame (tr.state y i)).fcRoot ∨
        C ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree

/-- A lock floor reads projected locks in the actual node's FG frame. -/
def FloorAt (y : Fin sp.n) (i : Nat) (B₀ : SA.Blk sp.n (List (FG.Att sp.n)))
    (j m : Nat) : Prop :=
  ∃ l ∈ ((F.proj tr.projAC).state y i).locks, l.slot = j ∧ m ≤ l.expiry ∧
    ∃ B ∈ (tr.state y i).fg.toFrame.tree, B.root = l.block ∧ (tr.state y i).fg.toFrame.Anc B₀ B

end Consensus.Goldilocks.FamilySafety

end
