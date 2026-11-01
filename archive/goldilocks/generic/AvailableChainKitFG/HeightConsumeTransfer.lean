module
public import AvailableChainKitFG.HeightCoreDef
public import AvailableChainKitFG.HeightConsume
public import AvailableChainKitFG.HeightLaws
public import AvailableChainKitFG.RowBits

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- Target coverage transfers through the one-step height bridge. -/
theorem transition_target_of_cover_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    {Ω : Type} (π : Ω → FGHeight V)
    (step : Ω → FGBlock V → List (Row V) → Ω)
    (hb : HeightStepBridge E cfg π step)
    (w : Ω) (B : FGBlock V) (rs : List (Row V)) (S : Finset V)
    (hS : E.IsQuorum S)
    (hcover : ∀ i ∈ S, i ∈ (π w).target_participation ∨
      ∃ a ∈ rs, a.signer = i ∧
        a.height_pair = .vote (π w).h (π w).T_h.root false) :
    (π (step w B rs)).h = (π w).h + 1 ∧
    (π (step w B rs)).J = (π w).T_h ∧
    (π (step w B rs)).h_j = (π w).h := by
  let σ : ChainState V :=
    { L := (π w).L, s := (π w).s, h := (π w).h, T_h := (π w).T_h,
      target_participation := (π w).target_participation, progress := (π w).progress,
      h_j := (π w).h_j, J := (π w).J, F := .genesis, h_F := 0, finalize := ∅ }
  have hσ : π w = heightOf σ := rfl
  rw [hb w σ B rs hσ]
  exact transition_target_of_cover E cfg σ B rs S hS hcover

/-- Mature progress coverage transfers through the one-step height bridge. -/
theorem transition_progress_of_cover_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    {Ω : Type} (π : Ω → FGHeight V)
    (step : Ω → FGBlock V → List (Row V) → Ω)
    (hb : HeightStepBridge E cfg π step)
    (w : Ω) (B : FGBlock V) (rs : List (Row V)) (S : Finset V)
    (hS : E.IsQuorum S)
    (hcover : ∀ i ∈ S, i ∈ (π w).progress ∨
      ∃ a ∈ rs, a.signer = i ∧
        a.height_pair.matchesEntry (π w).h (π w).T_h.root = true)
    (hmature : (π w).T_h.slot + cfg.timeoutDelay ≤ B.slot) :
    (π (step w B rs)).h = (π w).h + 1 := by
  let σ : ChainState V :=
    { L := (π w).L, s := (π w).s, h := (π w).h, T_h := (π w).T_h,
      target_participation := (π w).target_participation, progress := (π w).progress,
      h_j := (π w).h_j, J := (π w).J, F := .genesis, h_F := 0, finalize := ∅ }
  have hσ : π w = heightOf σ := rfl
  rw [hb w σ B rs hσ]
  exact transition_progress_of_cover E cfg σ B rs S hS hcover hmature

/-- Target coverage in a child transfers through the derive bridge. -/
theorem derive_target_of_cover_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    (p : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat)
    (rs : List (Row V)) (S : Finset V)
    (hS : E.IsQuorum S)
    (hcover : ∀ i ∈ S, i ∈ (v p).target_participation ∨
      ∃ a ∈ rs, a.signer = i ∧
        a.height_pair = .vote (v p).h (v p).T_h.root false) :
    (v (.node p s r_s x rs)).h = (v p).h + 1 ∧
    (v (.node p s r_s x rs)).J = (v p).T_h ∧
    (v (.node p s r_s x rs)).h_j = (v p).h := by
  have heq : ∀ B, v B = heightOf (derive E cfg B) := hb
  simp only [heq, heightOf_def] at hcover ⊢
  exact derive_target_of_cover E cfg p s r_s x rs S hS hcover

/-- Mature progress coverage in a child transfers through the derive bridge. -/
theorem derive_progress_of_cover_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    (p : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat)
    (rs : List (Row V)) (S : Finset V)
    (hS : E.IsQuorum S)
    (hcover : ∀ i ∈ S, i ∈ (v p).progress ∨
      ∃ a ∈ rs, a.signer = i ∧
        a.height_pair.matchesEntry (v p).h (v p).T_h.root = true)
    (hmature : (v p).T_h.slot + cfg.timeoutDelay ≤ s) :
    (v (.node p s r_s x rs)).h = (v p).h + 1 := by
  have heq : ∀ B, v B = heightOf (derive E cfg B) := hb
  simp only [heq, heightOf_def] at hcover hmature ⊢
  exact derive_progress_of_cover E cfg p s r_s x rs S hS hcover hmature

/-- Equal heights keep every progress bit along a chain path. -/
theorem progress_persist_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    {B P : FGBlock V} (hBP : FGBlock.Preceq B P)
    (hh : (v B).h = (v P).h) :
    (v B).progress ⊆ (v P).progress := by
  have heq : ∀ B, v B = heightOf (derive E cfg B) := hb
  have hT := (heightLaws_of_bridge E cfg v hb).entry_plateau hBP hh
  have hk : sameBitState .progress (derive E cfg B) (derive E cfg P) := by
    simp only [heq, heightOf_def] at hh hT
    exact ⟨hh, congrArg FGBlock.root hT⟩
  simp only [heq, heightOf_def]
  exact bit_persist E cfg .progress B P hBP hk

/-- A matching row in a child keeps its progress bit while the height is equal. -/
theorem progress_from_row_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    {P W : FGBlock V} {s : Slot} {r_s : BlockId} {x : Nat} {rs : List (Row V)} {a : Row V}
    (ha : a ∈ rs)
    (hCW : FGBlock.Preceq (.node P s r_s x rs) W)
    (hm : a.height_pair.matchesEntry (v P).h (v P).T_h.root = true)
    (hh : (v P).h = (v W).h) :
    a.signer ∈ (v W).progress := by
  have heq : ∀ B, v B = heightOf (derive E cfg B) := hb
  have hT := (heightLaws_of_bridge E cfg v hb).entry_plateau
    (preceq_trans (preceq_parent_node P s r_s x rs) hCW) hh
  have hk : sameBitState .progress (derive E cfg P) (derive E cfg W) := by
    simp only [heq, heightOf_def] at hh hT
    exact ⟨hh, congrArg FGBlock.root hT⟩
  have hm' : rowMatchesBit .progress { derive E cfg P with s := s } a := by
    simp only [heq, heightOf_def] at hm
    exact hm
  simp only [heq, heightOf_def]
  exact bit_from_row E cfg .progress P W s r_s x rs a ha hCW hm' hk

end AvailableChain.KitFG
end
