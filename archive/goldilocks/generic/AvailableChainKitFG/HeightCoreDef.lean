module
public import AvailableChainSimplexFG.ChainState

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

structure FGHeight (V : Type) where
  L : FGBlock V
  s : Slot
  h : Height
  T_h : FGBlock V
  target_participation : Finset V
  progress : Finset V
  h_j : Height
  J : FGBlock V

def heightOf (σ : ChainState V) : FGHeight V :=
  ⟨σ.L, σ.s, σ.h, σ.T_h,
   σ.target_participation, σ.progress, σ.h_j, σ.J⟩

omit [DecidableEq V] [Fintype V] [RowCodec V] in
theorem heightOf_def (σ : ChainState V) :
    heightOf σ =
  (⟨σ.L, σ.s, σ.h, σ.T_h,
   σ.target_participation, σ.progress, σ.h_j, σ.J⟩) := rfl

abbrev FGHeightView (V : Type) := FGBlock V → FGHeight V

def simplexHeightView (E : Electorate V) (cfg : FGConfig) :
    FGHeightView V :=
  fun B => heightOf (derive E cfg B)

theorem simplexHeightView_def (E : Electorate V) (cfg : FGConfig) :
    simplexHeightView E cfg =
  (fun B => heightOf (derive E cfg B)) := rfl

def HeightBridge (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) : Prop :=
  ∀ B, v B = heightOf (derive E cfg B)

theorem HeightBridge_def (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) :
    HeightBridge E cfg v =
  (∀ B, v B = heightOf (derive E cfg B)) := rfl

def HeightRowsEq (η : FGHeight V)
    (rs ts : List (Row V)) : Prop :=
  (∀ i : V,
    (i ∈ η.target_participation ∨
      ∃ a ∈ rs, a.signer = i ∧
        a.height_pair = .vote η.h η.T_h.root false) ↔
    (i ∈ η.target_participation ∨
      ∃ a ∈ ts, a.signer = i ∧
        a.height_pair = .vote η.h η.T_h.root false)) ∧
  (∀ i : V,
    (i ∈ η.progress ∨
      ∃ a ∈ rs, a.signer = i ∧
        a.height_pair.matchesEntry η.h η.T_h.root = true) ↔
    (i ∈ η.progress ∨
      ∃ a ∈ ts, a.signer = i ∧
        a.height_pair.matchesEntry η.h η.T_h.root = true))

omit [DecidableEq V] [Fintype V] in
theorem HeightRowsEq_def (η : FGHeight V)
    (rs ts : List (Row V)) :
    HeightRowsEq η rs ts =
  ((∀ i : V,
    (i ∈ η.target_participation ∨
      ∃ a ∈ rs, a.signer = i ∧
        a.height_pair = .vote η.h η.T_h.root false) ↔
    (i ∈ η.target_participation ∨
      ∃ a ∈ ts, a.signer = i ∧
        a.height_pair = .vote η.h η.T_h.root false)) ∧
  (∀ i : V,
    (i ∈ η.progress ∨
      ∃ a ∈ rs, a.signer = i ∧
        a.height_pair.matchesEntry η.h η.T_h.root = true) ↔
    (i ∈ η.progress ∨
      ∃ a ∈ ts, a.signer = i ∧
        a.height_pair.matchesEntry η.h η.T_h.root = true))) := rfl

def HeightSelector
    (sel : ChainState V → List (Row V) → List (Row V)) : Prop :=
  ∀ σ rs, HeightRowsEq (heightOf σ) (sel σ rs) rs

omit [DecidableEq V] [Fintype V] in
theorem HeightSelector_def
    (sel : ChainState V → List (Row V) → List (Row V)) :
    HeightSelector sel =
  (∀ σ rs, HeightRowsEq (heightOf σ) (sel σ rs) rs) := rfl

def selectHeightRows (σ : ChainState V)
    (rs : List (Row V)) : List (Row V) :=
  rs.filter
    (fun a => a.height_pair.matchesEntry σ.h σ.T_h.root)

omit [DecidableEq V] [Fintype V] in
theorem selectHeightRows_def (σ : ChainState V)
    (rs : List (Row V)) :
    selectHeightRows σ rs =
  (rs.filter
    (fun a => a.height_pair.matchesEntry σ.h σ.T_h.root)) := rfl

def deriveWithSelector (E : Electorate V) (cfg : FGConfig)
    (sel : ChainState V → List (Row V) → List (Row V)) :
    FGBlock V → ChainState V
  | .genesis => .initial
  | B@(.node p _ _ _ rs) =>
      let σ := deriveWithSelector E cfg sel p
      transition E cfg σ B (sel σ rs)

def HeightStepBridge (E : Electorate V) (cfg : FGConfig)
    {Ω : Type} (π : Ω → FGHeight V)
    (step : Ω → FGBlock V → List (Row V) → Ω) : Prop :=
  ∀ (w : Ω) (σ : ChainState V)
    (B : FGBlock V) (rs : List (Row V)),
    π w = heightOf σ →
    π (step w B rs) = heightOf (transition E cfg σ B rs)

theorem HeightStepBridge_def (E : Electorate V) (cfg : FGConfig)
    {Ω : Type} (π : Ω → FGHeight V)
    (step : Ω → FGBlock V → List (Row V) → Ω) :
    HeightStepBridge E cfg π step =
  (∀ (w : Ω) (σ : ChainState V)
    (B : FGBlock V) (rs : List (Row V)),
    π w = heightOf σ →
    π (step w B rs) = heightOf (transition E cfg σ B rs)) := rfl

structure HeightFoldRefinement
    (E : Electorate V) (cfg : FGConfig)
    {Ω : Type} (π : Ω → FGHeight V)
    (initial : Ω)
    (step : Ω → FGBlock V → List (Row V) → Ω)
    (d : FGBlock V → Ω) : Prop where
  initial_height :
    π initial = heightOf (ChainState.initial : ChainState V)
  derive_genesis :
    d .genesis = initial
  derive_node :
    ∀ (p : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V)),
      d (.node p s r_s x rs) = step (d p) (.node p s r_s x rs) rs
  step_height :
    HeightStepBridge E cfg π step

theorem deriveWithSelector_def (E : Electorate V) (cfg : FGConfig)
    (sel : ChainState V → List (Row V) → List (Row V)) (B : FGBlock V) :
    deriveWithSelector E cfg sel B =
      match B with
      | .genesis => .initial
      | .node p s r_s x rs =>
          let σ := deriveWithSelector E cfg sel p
          transition E cfg σ (.node p s r_s x rs) (sel σ rs) := by
  cases B <;> rfl

end AvailableChain.KitFG
end
