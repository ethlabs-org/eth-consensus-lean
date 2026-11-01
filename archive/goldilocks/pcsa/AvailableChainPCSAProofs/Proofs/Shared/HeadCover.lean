module
public import AvailableChainPCSAProofs.Proofs.Shared.Walk

public section

/-! PC-SA majority coverage (pcsa34-r4.3 §§5.0, 5.2.1 CL2–CL3). -/

namespace AvailableChain.PCSA

open Gen.Pure

/-- A majority target with lower conflicting scores is below the PC-SA head. -/
theorem pcsa_headInTree_covers_of_transfer
    (p : Params) (st : State p.n) (c : Option (PC p.n)) (tree : List Block)
    (raw support : List (GridCO.Wire p.n .root)) (B : Block)
    (hanchor : Block.Compatible (liveRoot p st c) B)
    (hpath : ∀ C, Block.Prec (liveRoot p st c) C → Block.Preceq C B → C ∈ tree)
    (hmajority : GridCO.voterCount raw <
      2 * GridCO.goldfishScore st.base.blocks raw support B)
    (hdominance : ∀ D, Block.compatible B D = false →
      GridCO.goldfishScore st.base.blocks raw support D <
        GridCO.goldfishScore st.base.blocks raw support B) :
    Block.Preceq B (headInTree p st c tree raw support) := by
  apply pcsa_headInTree_covers_path p st c tree raw support B hanchor
  intro C hac hcb
  have hm := Gen.AC.Root.goldfishScore_antitone st.base.blocks raw support C B hcb
  refine ⟨hpath C hac hcb, ?_, ?_⟩
  · unfold eligible
    have hmaj : GridCO.voterCount raw <
        2 * GridCO.goldfishScore st.base.blocks raw support C := by omega
    simp only [hmaj, decide_true, Bool.or_true, Bool.true_or]
  · intro D _ hp _ hne
    have he : D.depth = C.depth := by
      cases D with
      | genesis => cases C with
        | genesis => rfl
        | node P s r x => cases hp
      | node P s r x => cases C with
        | genesis => cases hp
        | node Q t u y =>
          have heq : P = Q := Option.some.inj hp
          subst Q
          rfl
    have hn : ¬ Block.Compatible D C := by
      intro h
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact hne (prefix_eq_of_depth D C h (Nat.le_of_eq he.symm))
      · exact hne (prefix_eq_of_depth C D h (Nat.le_of_eq he)).symm
    have hd : Block.compatible B D = false := by
      rw [block_compatible_comm]
      exact Bool.eq_false_iff.mpr (block_incompatible_of_preceq hn hcb)
    exact lt_of_lt_of_le (hdominance D hd) hm

/-- CL2 on count inputs. The forward and backward receipts are the complete
late-pool relay boundary. No pool state or clean regime is assumed. -/
theorem pcsa_cl2_head_extends_majority
    (p : Params) (dst : State p.n) (c : Option (PC p.n)) (tree sourceTree : List Block)
    (P L U V : List (GridCO.Wire p.n .root)) (B : Block)
    (hPL : P ⊆ L)
    (hclean : ∀ o ∈ P, ∀ i, GridCO.headSeat? o = some i →
      GridCO.equivocates L i = false)
    (hforward : ∀ o ∈ P, ∀ i, GridCO.headSeat? o = some i →
      Gen.AC.Root.voteSupports sourceTree B o = true →
      (o ∈ V ∧ Gen.AC.Root.voteSupports dst.base.blocks B o = true) ∨
        GridCO.equivocates U i = true)
    (hbackward : ∀ o ∈ U, ∀ i, GridCO.headSeat? o = some i →
      o ∈ L ∨ GridCO.equivocates L i = true)
    (hsupport : V ⊆ U)
    (hmajority : GridCO.voterCount L < 2 * GridCO.goldfishScore sourceTree P P B)
    (hanchor : Block.Compatible (liveRoot p dst c) B)
    (hpath : ∀ C, Block.Prec (liveRoot p dst c) C → Block.Preceq C B → C ∈ tree) :
    Block.Preceq B (headInTree p dst c tree U V) := by
  have hb := Gen.AC.Root.transfer sourceTree dst.base.blocks P L U V B
    hPL hclean hforward hbackward hsupport hmajority
  exact pcsa_headInTree_covers_of_transfer p dst c tree U V B hanchor hpath hb.2.2.2.2.2.1
    hb.2.2.2.2.2.2

end AvailableChain.PCSA
end
