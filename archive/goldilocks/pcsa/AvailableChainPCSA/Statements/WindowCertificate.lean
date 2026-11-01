module
public import AvailableChainPCSA.Model.Objects
public import AvailableChainFGSA.Model.Window
public import AvailableChainFGSA.Statements.WindowHeight
public import AvailableChainKitFG.CertificateCoreDef
public import AvailableChainKitFG.CertificateSelectionDef

@[expose] public section

/-! [PC-SA M1; FG-SA Statements/WindowCertificate.lean, mech copy] The window
certificate views over the FG-SA window module (`AvailableChainFGSA.Model.Window`,
imported; the PC-SA parameters are the FG-SA parameters). -/

namespace AvailableChain.PCSA.Window

open AvailableChain.SimplexFG hiding process_row derive
open AvailableChain.KitFG
open AvailableChain.FGSA.Window (State Entry derive process_row greatestReady finalizeWindow
  projectHeight)

def pcsa_projectFinality {V : Type} (σ : State V) : FGFinality V :=
  ⟨σ.F, σ.h_F⟩

theorem pcsa_projectFinality_def {V : Type} (σ : State V) :
    pcsa_projectFinality σ = ⟨σ.F, σ.h_F⟩ := rfl

def pcsa_projectCertEntry {V : Type} (e : Entry V) : FGCertEntry V :=
  ⟨e.j, e.X, e.Q⟩

theorem pcsa_projectCertEntry_def {V : Type} (e : Entry V) :
    pcsa_projectCertEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

def pcsa_certificateHeight (p : Params) (K : Nat) : FGHeightView (Fin p.n) :=
  fun B => projectHeight (derive p K B)

theorem pcsa_certificateHeight_def (p : Params) (K : Nat) :
    pcsa_certificateHeight p K = (fun B => projectHeight (derive p K B)) := rfl

def pcsa_certificateFinality (p : Params) (K : Nat) : FGFinalityView (Fin p.n) :=
  fun B => pcsa_projectFinality (derive p K B)

theorem pcsa_certificateFinality_def (p : Params) (K : Nat) :
    pcsa_certificateFinality p K = (fun B => pcsa_projectFinality (derive p K B)) := rfl

/-- [spec 1193–1220] State after the row fold, before finality. -/
def pcsa_certificateFolded (p : Params) (K : Nat)
    (B : FGBlock (Fin p.n)) : State (Fin p.n) :=
  { B.rows.foldl process_row
      { derive p K B.parent with s := B.slot } with L := B }

theorem pcsa_certificateFolded_def (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    pcsa_certificateFolded p K B =
      { B.rows.foldl process_row
          { derive p K B.parent with s := B.slot } with L := B } := rfl

/-- [spec 1222–1227] The three finality phases precede target append. -/
def pcsa_certificateSelection (p : Params) (K : Nat) : FGSelectionView (Fin p.n) where
  before := fun B => (pcsa_certificateFolded p K B).W.map pcsa_projectCertEntry
  chosen := fun B => (greatestReady p.E (pcsa_certificateFolded p K B)).map pcsa_projectCertEntry
  afterPrune := fun B =>
    (finalizeWindow p.E (pcsa_certificateFolded p K B)).W.map pcsa_projectCertEntry

theorem pcsa_certificateSelection_def (p : Params) (K : Nat) :
    pcsa_certificateSelection p K =
      { before := fun B => (pcsa_certificateFolded p K B).W.map pcsa_projectCertEntry
        chosen := fun B =>
          (greatestReady p.E (pcsa_certificateFolded p K B)).map pcsa_projectCertEntry
        afterPrune := fun B =>
          (finalizeWindow p.E (pcsa_certificateFolded p K B)).W.map pcsa_projectCertEntry } := rfl

/-- [bp §3.1–3.2] The birth can be this block; each bit has a later carrier. -/
def pcsa_EntryOriginAt (p : Params) (K : Nat)
    (B : FGBlock (Fin p.n)) (e : Entry (Fin p.n)) : Prop :=
  ∃ C, FGBlock.Preceq C B ∧
    JustificationBirth p.E (pcsa_certificateHeight p K) C e.j e.X ∧
    ∀ i ∈ e.Q, ∃ carrier a,
      StrictPrefix C carrier ∧ FGBlock.Preceq carrier B ∧
      a ∈ carrier.rows ∧ a.signer = i ∧
      a.finality_pair = some ⟨e.j, e.X.root⟩

theorem pcsa_EntryOriginAt_def (p : Params) (K : Nat)
    (B : FGBlock (Fin p.n)) (e : Entry (Fin p.n)) :
    pcsa_EntryOriginAt p K B e =
      (∃ C, FGBlock.Preceq C B ∧
        JustificationBirth p.E (pcsa_certificateHeight p K) C e.j e.X ∧
        ∀ i ∈ e.Q, ∃ carrier a,
          StrictPrefix C carrier ∧ FGBlock.Preceq carrier B ∧
          a ∈ carrier.rows ∧ a.signer = i ∧
          a.finality_pair = some ⟨e.j, e.X.root⟩) := rfl

end AvailableChain.PCSA.Window
end
