module
public import AvailableChainKitFG.HeightLawsDef

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- Finality keeps both parts of the certificate key. -/
structure FGFinality (V : Type) where
  F : FGBlock V
  h_F : Height

abbrev FGFinalityView (V : Type) := FGBlock V → FGFinality V

def finalityOf (σ : ChainState V) : FGFinality V :=
  ⟨σ.F, σ.h_F⟩

omit [DecidableEq V] [Fintype V] [RowCodec V] in
theorem finalityOf_def (σ : ChainState V) :
    finalityOf σ = ⟨σ.F, σ.h_F⟩ := rfl

def simplexFinalityView (E : Electorate V) (cfg : FGConfig) :
    FGFinalityView V :=
  fun B => finalityOf (derive E cfg B)

theorem simplexFinalityView_def (E : Electorate V) (cfg : FGConfig) :
    simplexFinalityView E cfg =
      (fun B => finalityOf (derive E cfg B)) := rfl

def StrictPrefix (A B : FGBlock V) : Prop :=
  FGBlock.Preceq A B ∧ A ≠ B

omit [Fintype V] [RowCodec V] in
theorem StrictPrefix_def (A B : FGBlock V) :
    StrictPrefix A B = (FGBlock.Preceq A B ∧ A ≠ B) := rfl

/-- A target QC for the pair `(j, X)`, with rows on the chain of `B`. -/
def TargetQCAt (E : Electorate V)
    (B : FGBlock V) (j : Height) (X : FGBlock V) : Prop :=
  ∃ Q : Finset V, E.IsQuorum Q ∧
    ∀ i ∈ Q, ∃ carrier a,
      FGBlock.Preceq carrier B ∧
      a ∈ carrier.rows ∧ a.signer = i ∧
      a.height_pair = .vote j X.root false

theorem TargetQCAt_def (E : Electorate V)
    (B : FGBlock V) (j : Height) (X : FGBlock V) :
    TargetQCAt E B j X =
      (∃ Q : Finset V, E.IsQuorum Q ∧
        ∀ i ∈ Q, ∃ carrier a,
          FGBlock.Preceq carrier B ∧
          a ∈ carrier.rows ∧ a.signer = i ∧
          a.height_pair = .vote j X.root false) := rfl

def JustificationBirth (E : Electorate V) (H : FGHeightView V)
    (C : FGBlock V) (j : Height) (X : FGBlock V) : Prop :=
  C ≠ .genesis ∧
  (H C.parent).h = j ∧
  (H C.parent).T_h = X ∧
  (H C).h_j = j ∧
  (H C).J = X ∧
  (H C).h = j + 1 ∧
  TargetQCAt E C j X

theorem JustificationBirth_def (E : Electorate V) (H : FGHeightView V)
    (C : FGBlock V) (j : Height) (X : FGBlock V) :
    JustificationBirth E H C j X =
      (C ≠ .genesis ∧
        (H C.parent).h = j ∧
        (H C.parent).T_h = X ∧
        (H C).h_j = j ∧
        (H C).J = X ∧
        (H C).h = j + 1 ∧
        TargetQCAt E C j X) := rfl

/-- The finality QC rows occur strictly after the birth block `C`. -/
def FinalityQCAfter (E : Electorate V)
    (C D : FGBlock V) (j : Height) (X : FGBlock V) : Prop :=
  ∃ Q : Finset V, E.IsQuorum Q ∧
    ∀ i ∈ Q, ∃ carrier a,
      StrictPrefix C carrier ∧
      FGBlock.Preceq carrier D ∧
      a ∈ carrier.rows ∧ a.signer = i ∧
      a.finality_pair = some ⟨j, X.root⟩

theorem FinalityQCAfter_def (E : Electorate V)
    (C D : FGBlock V) (j : Height) (X : FGBlock V) :
    FinalityQCAfter E C D j X =
      (∃ Q : Finset V, E.IsQuorum Q ∧
        ∀ i ∈ Q, ∃ carrier a,
          StrictPrefix C carrier ∧
          FGBlock.Preceq carrier D ∧
          a ∈ carrier.rows ∧ a.signer = i ∧
          a.finality_pair = some ⟨j, X.root⟩) := rfl

structure FGCertificateLaws (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) : Prop where
  height : FGHeightLaws E H

  initial :
    f .genesis = ⟨.genesis, 0⟩

  justified_zero :
    ∀ B, (H B).h_j = 0 → (H B).J = .genesis

  finalized_zero :
    ∀ B, (f B).h_F = 0 → (f B).F = .genesis

  finalized_preceq_justified :
    ∀ B, FGBlock.Preceq (f B).F (H B).J

  heights_ordered :
    ∀ B, (f B).h_F ≤ (H B).h_j

  finalized_mono :
    ∀ {A B}, FGBlock.Preceq A B →
      (f A).h_F ≤ (f B).h_F ∧
      FGBlock.Preceq (f A).F (f B).F

  finality_origin :
    ∀ B, (f B).h_F ≠ 0 →
      ∃ C D,
        StrictPrefix C D ∧
        FGBlock.Preceq D B ∧
        JustificationBirth E H C (f B).h_F (f B).F ∧
        (f D.parent).h_F < (f D).h_F ∧
        f D = f B ∧
        FinalityQCAfter E C D (f B).h_F (f B).F

end AvailableChain.KitFG
end
