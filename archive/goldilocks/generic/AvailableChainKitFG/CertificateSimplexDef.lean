module
public import AvailableChainKitFG.CertificateSelectionDef

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- Project the latest pending certificate, with its exact height and block. -/
def simplexPending (σ : ChainState V) : List (FGCertEntry V) :=
  if σ.h_F < σ.h_j then [⟨σ.h_j, σ.J, σ.finalize⟩] else []

omit [DecidableEq V] [Fintype V] [RowCodec V] in
theorem simplexPending_def (σ : ChainState V) :
    simplexPending σ =
      if σ.h_F < σ.h_j then [⟨σ.h_j, σ.J, σ.finalize⟩] else [] := rfl

/-- Read the QC before finality. The last projection precedes target append. -/
def simplexSelectionView (E : Electorate V) (cfg : FGConfig) : FGSelectionView V where
  before := fun B => match B with
    | .genesis => []
    | .node p _ _ _ rs =>
        let σ := { rs.foldl process_row { derive E cfg p with s := B.slot } with L := B }
        simplexPending σ
  chosen := fun B => match B with
    | .genesis => none
    | .node p _ _ _ rs =>
        let σ := { rs.foldl process_row { derive E cfg p with s := B.slot } with L := B }
        if finalityReady E σ then some ⟨σ.h_j, σ.J, σ.finalize⟩ else none
  afterPrune := fun B => match B with
    | .genesis => []
    | .node p _ _ _ rs =>
        let σ := { rs.foldl process_row { derive E cfg p with s := B.slot } with L := B }
        simplexPending (if finalityReady E σ then { σ with F := σ.J, h_F := σ.h_j } else σ)

theorem simplexSelectionView_def (E : Electorate V) (cfg : FGConfig) :
    simplexSelectionView E cfg =
      { before := fun B => match B with
          | .genesis => []
          | .node p _ _ _ rs =>
              let σ := { rs.foldl process_row { derive E cfg p with s := B.slot } with L := B }
              simplexPending σ
        chosen := fun B => match B with
          | .genesis => none
          | .node p _ _ _ rs =>
              let σ := { rs.foldl process_row { derive E cfg p with s := B.slot } with L := B }
              if finalityReady E σ then some ⟨σ.h_j, σ.J, σ.finalize⟩ else none
        afterPrune := fun B => match B with
          | .genesis => []
          | .node p _ _ _ rs =>
              let σ := { rs.foldl process_row { derive E cfg p with s := B.slot } with L := B }
              simplexPending
                (if finalityReady E σ then { σ with F := σ.J, h_F := σ.h_j } else σ) } := rfl

end AvailableChain.KitFG
end
