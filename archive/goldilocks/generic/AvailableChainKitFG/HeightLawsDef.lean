module
public import AvailableChainKitFG.HeightCoreDef

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

structure FGHeightLaws (E : Electorate V)
    (v : FGHeightView V) : Prop where
  one_le_h :
    ∀ B, 1 ≤ (v B).h

  h_mono :
    ∀ {A B}, FGBlock.Preceq A B → (v A).h ≤ (v B).h

  node_cases :
    ∀ (p : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V)),
      let B := FGBlock.node p s r_s x rs
      ((v B).h = (v p).h ∧ (v B).T_h = (v p).T_h) ∨
      ((v B).h = (v p).h + 1 ∧ (v B).T_h = B)

  entry_preceq :
    ∀ B, FGBlock.Preceq (v B).T_h B

  entry_same_height :
    ∀ B, (v (v B).T_h).h = (v B).h

  entry_idem :
    ∀ B, (v (v B).T_h).T_h = (v B).T_h

  entry_plateau :
    ∀ {A B}, FGBlock.Preceq A B →
      (v A).h = (v B).h → (v A).T_h = (v B).T_h

  justified_preceq_entry :
    ∀ B, FGBlock.Preceq (v B).J (v B).T_h

  justified_below_height :
    ∀ B, (v B).h_j < (v B).h

  target_sub_progress :
    ∀ B, (v B).target_participation ⊆ (v B).progress

  target_origin :
    ∀ B i, i ∈ (v B).target_participation →
      ∃ (W : FGBlock V) (a : Row V),
        FGBlock.Preceq W B ∧ a ∈ W.rows ∧ a.signer = i ∧
        a.height_pair = .vote (v B).h (v B).T_h.root false

  progress_origin :
    ∀ B i, i ∈ (v B).progress →
      ∃ (W : FGBlock V) (a : Row V),
        FGBlock.Preceq W B ∧ a ∈ W.rows ∧ a.signer = i ∧
        a.height_pair.matchesEntry (v B).h (v B).T_h.root = true

  height_crossing :
    ∀ (C : FGBlock V) (y : Height),
      1 ≤ y → y < (v C).h →
      ∃ X : FGBlock V,
        FGBlock.Preceq X C ∧ (v X).h = y ∧
        ∃ Q : Finset V, E.IsQuorum Q ∧
          ∀ i ∈ Q, ∃ (W : FGBlock V) (a : Row V),
            FGBlock.Preceq W C ∧ a ∈ W.rows ∧ a.signer = i ∧
            a.height_pair.matchesEntry y X.root = true

  justification_certificate :
    ∀ D, (v D).h_j ≠ 0 →
      ∃ Q : Finset V, E.IsQuorum Q ∧
        ∀ i ∈ Q, ∃ (W : FGBlock V) (a : Row V),
          FGBlock.Preceq W D ∧ a ∈ W.rows ∧ a.signer = i ∧
          a.height_pair = .vote (v D).h_j (v D).J.root false

end AvailableChain.KitFG
end
