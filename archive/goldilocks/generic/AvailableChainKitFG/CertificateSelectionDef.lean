module
public import AvailableChainKitFG.CertificateCoreDef

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- The key is `(j, X)`. `Q` is a signer set; it need not be a quorum. -/
structure FGCertEntry (V : Type) where
  j : Height
  X : FGBlock V
  Q : Finset V

/-- Remove entries at or below the finalized height, before capacity eviction. -/
abbrev pruneCertEntries (h : Height) (entries : List (FGCertEntry V)) : List (FGCertEntry V) :=
  entries.filter (fun e => decide (h < e.j))

omit [DecidableEq V] [Fintype V] [RowCodec V] in
/-- The pruning equation belongs to the module that defines the operation. -/
theorem pruneCertEntries_def (h : Height) (entries : List (FGCertEntry V)) :
    pruneCertEntries h entries = entries.filter (fun e => decide (h < e.j)) := rfl

/-- `before` follows the row fold. `afterPrune` precedes target append and
capacity eviction. An eviction does not give finality coverage. -/
structure FGSelectionView (V : Type) where
  before : FGBlock V → List (FGCertEntry V)
  chosen : FGBlock V → Option (FGCertEntry V)
  afterPrune : FGBlock V → List (FGCertEntry V)

structure FGSelectionLaws (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V)
    (r : FGSelectionView V) : Prop where
  initial :
    r.before .genesis = [] ∧
    r.chosen .genesis = none ∧
    r.afterPrune .genesis = []

  ordered :
    ∀ B, (r.before B).Pairwise
      (fun e d => e.j < d.j ∧ FGBlock.Preceq e.X d.X)

  bounds :
    ∀ B e, e ∈ r.before B →
      (f B.parent).h_F < e.j ∧
      e.j ≤ (H B.parent).h_j ∧
      FGBlock.Preceq (f B.parent).F e.X ∧
      FGBlock.Preceq e.X (H B.parent).J

  entry_origin :
    ∀ B e, e ∈ r.before B →
      ∃ C,
        StrictPrefix C B ∧
        JustificationBirth E H C e.j e.X ∧
        ∀ i ∈ e.Q, ∃ carrier a,
          StrictPrefix C carrier ∧
          FGBlock.Preceq carrier B ∧
          a ∈ carrier.rows ∧ a.signer = i ∧
          a.finality_pair = some ⟨e.j, e.X.root⟩

  none_iff :
    ∀ B, r.chosen B = none ↔
      ∀ e ∈ r.before B, ¬ E.IsQuorum e.Q

  -- Read the selected QC from `before`; pruning removes this entry.
  greatest :
    ∀ B e, r.chosen B = some e →
      e ∈ r.before B ∧ E.IsQuorum e.Q ∧
      ∀ d ∈ r.before B, E.IsQuorum d.Q → d.j ≤ e.j

  write :
    ∀ B, B ≠ .genesis →
      f B =
        match r.chosen B with
        | none => f B.parent
        | some e => ⟨e.X, e.j⟩

  prune :
    ∀ B, r.afterPrune B =
      (r.before B).filter (fun e => decide ((f B).h_F < e.j))

  -- Lower entries have coverage by F, with no quorum premise for their Q.
  pruned_covered :
    ∀ B e, e ∈ r.before B → e.j ≤ (f B).h_F →
      FGBlock.Preceq e.X (f B).F

structure FGChainCertificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V)
    (r : FGSelectionView V) : Prop where
  laws : FGCertificateLaws E H f
  selection : FGSelectionLaws E H f r

end AvailableChain.KitFG
end
