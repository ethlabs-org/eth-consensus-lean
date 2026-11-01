module
public import AvailableChainSimplexFG.Window
public import AvailableChainSimplexFG.Client
public import AvailableChainKitFG.FrameBridgeDef -- shake: keep (re-export)
public import AvailableChainKitFG.CertificateCoreDef -- shake: keep (re-export)
public import AvailableChainKitFG.CertificateSelectionDef

@[expose] public section

namespace AvailableChain.KitFG.Window

open AvailableChain.SimplexFG hiding derive process_row
open AvailableChain.SimplexFG.Window

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- [bp.heightBridge.v1] The eight height fields, in `heightOf` order. -/
def projectHeight (σ : State V) : KitFG.FGHeight V :=
  ⟨σ.L, σ.s, σ.h, σ.T_h, σ.target_participation, σ.progress, σ.h_j, σ.J⟩

omit [DecidableEq V] [Fintype V] [RowCodec V] in
theorem projectHeight_def (σ : State V) :
    projectHeight σ =
      ⟨σ.L, σ.s, σ.h, σ.T_h, σ.target_participation, σ.progress, σ.h_j, σ.J⟩ := rfl

/-- [spec 1186–1200] The window parent state with the child slot. -/
def parentState (E : Electorate V) (cfg : FGConfig) (K : Nat) (P : FGBlock V) (s : Slot) :
    State V :=
  { derive E cfg K P with s := s }

theorem parentState_def (E : Electorate V) (cfg : FGConfig) (K : Nat) (P : FGBlock V) (s : Slot) :
    parentState E cfg K P s = { derive E cfg K P with s := s } := rfl

/-- [spec 1603–1604] The head fields read directly from the window state. -/
def headFields (E : Electorate V) (cfg : FGConfig) (K : Nat) (Hd : FGBlock V) : HeadFields :=
  ⟨(derive E cfg K Hd).h_j, (derive E cfg K Hd).J.root, (derive E cfg K Hd).h_F⟩

theorem headFields_def (E : Electorate V) (cfg : FGConfig) (K : Nat) (Hd : FGBlock V) :
    headFields E cfg K Hd =
      ⟨(derive E cfg K Hd).h_j, (derive E cfg K Hd).J.root, (derive E cfg K Hd).h_F⟩ := rfl

def projectFinality (σ : State V) : FGFinality V :=
  ⟨σ.F, σ.h_F⟩

omit [DecidableEq V] [Fintype V] [RowCodec V] in
theorem projectFinality_def (σ : State V) :
    projectFinality σ = ⟨σ.F, σ.h_F⟩ := rfl

def projectCertEntry (e : Entry V) : FGCertEntry V :=
  ⟨e.j, e.X, e.Q⟩

omit [DecidableEq V] [Fintype V] [RowCodec V] in
theorem projectCertEntry_def (e : Entry V) :
    projectCertEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

def certificateHeight (E : Electorate V) (cfg : FGConfig) (K : Nat) : FGHeightView V :=
  fun B => projectHeight (derive E cfg K B)

theorem certificateHeight_def (E : Electorate V) (cfg : FGConfig) (K : Nat) :
    certificateHeight E cfg K = (fun B => projectHeight (derive E cfg K B)) := rfl

def certificateFinality (E : Electorate V) (cfg : FGConfig) (K : Nat) : FGFinalityView V :=
  fun B => projectFinality (derive E cfg K B)

theorem certificateFinality_def (E : Electorate V) (cfg : FGConfig) (K : Nat) :
    certificateFinality E cfg K = (fun B => projectFinality (derive E cfg K B)) := rfl

/-- [spec 1193–1220] State after the row fold, before finality. -/
def certificateFolded (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (B : FGBlock V) : State V :=
  { B.rows.foldl process_row
      { derive E cfg K B.parent with s := B.slot } with L := B }

theorem certificateFolded_def (E : Electorate V) (cfg : FGConfig) (K : Nat) (B : FGBlock V) :
    certificateFolded E cfg K B =
      { B.rows.foldl process_row
          { derive E cfg K B.parent with s := B.slot } with L := B } := rfl

/-- [spec 1222–1227] The three finality phases precede target append. -/
def certificateSelection (E : Electorate V) (cfg : FGConfig) (K : Nat) : FGSelectionView V where
  before := fun B => (certificateFolded E cfg K B).W.map projectCertEntry
  chosen := fun B => (greatestReady E (certificateFolded E cfg K B)).map projectCertEntry
  afterPrune := fun B => (finalizeWindow E (certificateFolded E cfg K B)).W.map projectCertEntry

theorem certificateSelection_def (E : Electorate V) (cfg : FGConfig) (K : Nat) :
    certificateSelection E cfg K =
      { before := fun B => (certificateFolded E cfg K B).W.map projectCertEntry
        chosen := fun B => (greatestReady E (certificateFolded E cfg K B)).map projectCertEntry
        afterPrune := fun B =>
          (finalizeWindow E (certificateFolded E cfg K B)).W.map projectCertEntry } := rfl

/-- [bp §3.1–3.2] The birth can be this block; each bit has a later carrier. -/
def EntryOriginAt (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (B : FGBlock V) (e : Entry V) : Prop :=
  ∃ C, FGBlock.Preceq C B ∧
    JustificationBirth E (certificateHeight E cfg K) C e.j e.X ∧
    ∀ i ∈ e.Q, ∃ carrier a,
      StrictPrefix C carrier ∧ FGBlock.Preceq carrier B ∧
      a ∈ carrier.rows ∧ a.signer = i ∧
      a.finality_pair = some ⟨e.j, e.X.root⟩

theorem EntryOriginAt_def (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (B : FGBlock V) (e : Entry V) :
    EntryOriginAt E cfg K B e =
      (∃ C, FGBlock.Preceq C B ∧
        JustificationBirth E (certificateHeight E cfg K) C e.j e.X ∧
        ∀ i ∈ e.Q, ∃ carrier a,
          StrictPrefix C carrier ∧ FGBlock.Preceq carrier B ∧
          a ∈ carrier.rows ∧ a.signer = i ∧
          a.finality_pair = some ⟨e.j, e.X.root⟩) := rfl

/-- The active height view reads the window fold. -/
def heightView (E : Electorate V) (cfg : FGConfig) (K : Nat) : FGHeightView V :=
  certificateHeight E cfg K

theorem heightView_def (E : Electorate V) (cfg : FGConfig) (K : Nat) :
    heightView E cfg K = certificateHeight E cfg K := rfl

/-- The active finality view reads the window fold. -/
def finalityView (E : Electorate V) (cfg : FGConfig) (K : Nat) : FGFinalityView V :=
  certificateFinality E cfg K

theorem finalityView_def (E : Electorate V) (cfg : FGConfig) (K : Nat) :
    finalityView E cfg K = certificateFinality E cfg K := rfl

end AvailableChain.KitFG.Window
end
