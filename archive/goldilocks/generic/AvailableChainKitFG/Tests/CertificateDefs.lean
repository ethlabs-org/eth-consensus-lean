module
public import AvailableChainKitFG.CertificateSelectionDef -- shake: keep (axioms)
public import AvailableChainKitFG.StoreSafetyDef -- shake: keep (axioms)

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.KitFG.Tests.CertificateDefs

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

#check FGFinality
#check FGFinalityView
#check finalityOf
#check finalityOf_def
#check simplexFinalityView
#check simplexFinalityView_def
#check StrictPrefix
#check StrictPrefix_def
#check TargetQCAt
#check TargetQCAt_def
#check JustificationBirth
#check JustificationBirth_def
#check FinalityQCAfter
#check FinalityQCAfter_def
#check FGCertificateLaws
#check FGCertEntry
#check FGSelectionView
#check FGSelectionLaws
#check FGChainCertificate
#check NoSlashOutside
#check NoSlashOutside_def
#check FGStoreInvariant
#check FGStoreSafety
#check acceptedThreshold
#check acceptedThreshold_def

omit [DecidableEq V] [Fintype V] [RowCodec V] in
example (σ : ChainState V) :
    finalityOf σ = ⟨σ.F, σ.h_F⟩ :=
  finalityOf_def σ

example (E : Electorate V) (cfg : FGConfig) :
    simplexFinalityView E cfg =
      (fun B => finalityOf (derive E cfg B)) :=
  simplexFinalityView_def E cfg

omit [Fintype V] [RowCodec V] in
example (A B : FGBlock V) :
    StrictPrefix A B = (FGBlock.Preceq A B ∧ A ≠ B) :=
  StrictPrefix_def A B

example (E : Electorate V)
    (B : FGBlock V) (j : Height) (X : FGBlock V) :
    TargetQCAt E B j X =
      (∃ Q : Finset V, E.IsQuorum Q ∧
        ∀ i ∈ Q, ∃ carrier a,
          FGBlock.Preceq carrier B ∧
          a ∈ carrier.rows ∧ a.signer = i ∧
          a.height_pair = .vote j X.root false) :=
  TargetQCAt_def E B j X

example (E : Electorate V) (H : FGHeightView V)
    (C : FGBlock V) (j : Height) (X : FGBlock V) :
    JustificationBirth E H C j X =
      (C ≠ .genesis ∧
        (H C.parent).h = j ∧
        (H C.parent).T_h = X ∧
        (H C).h_j = j ∧
        (H C).J = X ∧
        (H C).h = j + 1 ∧
        TargetQCAt E C j X) :=
  JustificationBirth_def E H C j X

example (E : Electorate V)
    (C D : FGBlock V) (j : Height) (X : FGBlock V) :
    FinalityQCAfter E C D j X =
      (∃ Q : Finset V, E.IsQuorum Q ∧
        ∀ i ∈ Q, ∃ carrier a,
          StrictPrefix C carrier ∧
          FGBlock.Preceq carrier D ∧
          a ∈ carrier.rows ∧ a.signer = i ∧
          a.finality_pair = some ⟨j, X.root⟩) :=
  FinalityQCAfter_def E C D j X

omit [Fintype V] [RowCodec V] in
example (faulty : Finset V)
    (A B : Finset (Row V)) :
    NoSlashOutside faulty A B =
      (∀ a ∈ A, ∀ b ∈ B,
        a.signer ∉ faulty → ¬ Slashable a b) :=
  NoSlashOutside_def faulty A B

omit [Fintype V] [RowCodec V] in
example (F : FGBlock V) (certificateHeight : Height) :
    acceptedThreshold F certificateHeight =
      (if F = .genesis then 0 else certificateHeight) :=
  acceptedThreshold_def F certificateHeight

-- The same block at two heights gives two certificate keys.
omit [DecidableEq V] [Fintype V] [RowCodec V] in
example (X : FGBlock V) :
    ((⟨1, X, ∅⟩ : FGCertEntry V).j, (⟨1, X, ∅⟩ : FGCertEntry V).X) ≠
      ((⟨2, X, ∅⟩ : FGCertEntry V).j, (⟨2, X, ∅⟩ : FGCertEntry V).X) := by
  intro h
  have hheight : (1 : Nat) = 2 := congrArg Prod.fst h
  exact (by decide : (1 : Nat) ≠ 2) hheight

-- The block is also part of the key.
omit [DecidableEq V] [Fintype V] [RowCodec V] in
example (j : Height) (X Y : FGBlock V) (hne : X ≠ Y) :
    (j, X) ≠ (j, Y) := fun h => hne (congrArg Prod.snd h)

-- Only the selected entry requires a quorum. It is read from `before`.
example (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (r : FGSelectionView V) (laws : FGSelectionLaws E H f r)
    (B : FGBlock V) (e : FGCertEntry V) (he : r.chosen B = some e) :
    e ∈ r.before B ∧ E.IsQuorum e.Q :=
  ⟨(laws.greatest B e he).1, (laws.greatest B e he).2.1⟩

-- A pruned lower entry has coverage by F even when its signer set is empty.
example (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (r : FGSelectionView V) (laws : FGSelectionLaws E H f r)
    (B X : FGBlock V) (j : Height)
    (hmem : (⟨j, X, ∅⟩ : FGCertEntry V) ∈ r.before B)
    (hj : j ≤ (f B).h_F) :
    FGBlock.Preceq X (f B).F ∧ j ≤ (f B).h_F :=
  ⟨laws.pruned_covered B ⟨j, X, ∅⟩ hmem hj, hj⟩

-- Pruning removes both the lower entry and the selected entry.
-- The entry at height 3 remains before any later capacity eviction.
example :
    ([⟨1, .genesis, ∅⟩, ⟨2, .genesis, {0}⟩, ⟨3, .genesis, ∅⟩] :
        List (FGCertEntry (Fin 1))).filter (fun e => decide (2 < e.j)) =
      [⟨3, .genesis, ∅⟩] := rfl

-- Genesis can have a certificate height of 1 and an accepted threshold of 0.
example : acceptedThreshold (FGBlock.genesis : FGBlock (Fin 1)) 1 = 0 := rfl

example :
    acceptedThreshold (FGBlock.node .genesis 1 ⟨100⟩ 0 [] : FGBlock (Fin 1)) 7 = 7 := rfl

#print axioms finalityOf_def
#print axioms simplexFinalityView_def
#print axioms StrictPrefix_def
#print axioms TargetQCAt_def
#print axioms JustificationBirth_def
#print axioms FinalityQCAfter_def
#print axioms NoSlashOutside_def
#print axioms acceptedThreshold_def

end AvailableChain.KitFG.Tests.CertificateDefs
end
