module
public import AvailableChainFGSA.Model.Window -- shake: keep (re-export)
public import AvailableChainFGSA.Statements.WindowHeight -- shake: keep (re-export)
public import AvailableChainKitFG.CertificateCoreDef -- shake: keep (re-export)
public import AvailableChainKitFG.CertificateSelectionDef

@[expose] public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding process_row derive
open AvailableChain.KitFG

def projectFinality {V : Type} (σ : State V) : FGFinality V :=
  ⟨σ.F, σ.h_F⟩

theorem projectFinality_def {V : Type} (σ : State V) :
    projectFinality σ = ⟨σ.F, σ.h_F⟩ := rfl

def projectCertEntry {V : Type} (e : Entry V) : FGCertEntry V :=
  ⟨e.j, e.X, e.Q⟩

theorem projectCertEntry_def {V : Type} (e : Entry V) :
    projectCertEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

def certificateHeight (p : Params) (K : Nat) : FGHeightView (Fin p.n) :=
  fun B => projectHeight (derive p K B)

theorem certificateHeight_def (p : Params) (K : Nat) :
    certificateHeight p K = (fun B => projectHeight (derive p K B)) := rfl

def certificateFinality (p : Params) (K : Nat) : FGFinalityView (Fin p.n) :=
  fun B => projectFinality (derive p K B)

theorem certificateFinality_def (p : Params) (K : Nat) :
    certificateFinality p K = (fun B => projectFinality (derive p K B)) := rfl

/-- [spec 1193–1220] State after the row fold, before finality. -/
def certificateFolded (p : Params) (K : Nat)
    (B : FGBlock (Fin p.n)) : State (Fin p.n) :=
  { B.rows.foldl process_row
      { derive p K B.parent with s := B.slot } with L := B }

theorem certificateFolded_def (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    certificateFolded p K B =
      { B.rows.foldl process_row
          { derive p K B.parent with s := B.slot } with L := B } := rfl

/-- [spec 1222–1227] The three finality phases precede target append. -/
def certificateSelection (p : Params) (K : Nat) : FGSelectionView (Fin p.n) where
  before := fun B => (certificateFolded p K B).W.map projectCertEntry
  chosen := fun B => (greatestReady p.E (certificateFolded p K B)).map projectCertEntry
  afterPrune := fun B => (finalizeWindow p.E (certificateFolded p K B)).W.map projectCertEntry

theorem certificateSelection_def (p : Params) (K : Nat) :
    certificateSelection p K =
      { before := fun B => (certificateFolded p K B).W.map projectCertEntry
        chosen := fun B => (greatestReady p.E (certificateFolded p K B)).map projectCertEntry
        afterPrune := fun B =>
          (finalizeWindow p.E (certificateFolded p K B)).W.map projectCertEntry } := rfl

/-- [bp §3.1–3.2] The birth can be this block; each bit has a later carrier. -/
def EntryOriginAt (p : Params) (K : Nat)
    (B : FGBlock (Fin p.n)) (e : Entry (Fin p.n)) : Prop :=
  ∃ C, FGBlock.Preceq C B ∧
    JustificationBirth p.E (certificateHeight p K) C e.j e.X ∧
    ∀ i ∈ e.Q, ∃ carrier a,
      StrictPrefix C carrier ∧ FGBlock.Preceq carrier B ∧
      a ∈ carrier.rows ∧ a.signer = i ∧
      a.finality_pair = some ⟨e.j, e.X.root⟩

theorem EntryOriginAt_def (p : Params) (K : Nat)
    (B : FGBlock (Fin p.n)) (e : Entry (Fin p.n)) :
    EntryOriginAt p K B e =
      (∃ C, FGBlock.Preceq C B ∧
        JustificationBirth p.E (certificateHeight p K) C e.j e.X ∧
        ∀ i ∈ e.Q, ∃ carrier a,
          StrictPrefix C carrier ∧ FGBlock.Preceq carrier B ∧
          a ∈ carrier.rows ∧ a.signer = i ∧
          a.finality_pair = some ⟨e.j, e.X.root⟩) := rfl

end AvailableChain.FGSA.Window
end
