module
public import AvailableChainKitFG.WindowCertificates -- shake: keep (re-export)
public import AvailableChainKitFG.ProvenanceCore
public import AvailableChainKitFG.CrossingCore

public section

namespace AvailableChain.KitFG.Window

open AvailableChain.SimplexFG hiding derive
open AvailableChain.SimplexFG.Window

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- Window views supply the height laws; all client premises stay explicit. -/
theorem window_provenance_entry (E : Electorate V) (cfg : FGConfig) (K : Nat) (hK : 2 ≤ K)
    (Λ : Record) (C : FGBlock V) (fp : Option FinalityPair)
    (h : Height) (T : BlockId) (t : Bool)
    (hemit : height_pair Λ
      (some ((certificateHeight E cfg K C).h, (certificateHeight E cfg K C).T_h.root)) fp = .vote
        h T t) :
    h = (certificateHeight E cfg K C).h ∧ T = (certificateHeight E cfg K C).T_h.root ∧
      FGBlock.Preceq (certificateHeight E cfg K C).T_h C :=
  provenance_entry_of_heightLaws E (certificateHeight E cfg K) (windowHeightLaws E cfg K hK)
    Λ C fp h T t hemit

/-- Window views supply the height laws; all client premises stay explicit. -/
theorem window_provenance_finalityRow (E : Electorate V) (cfg : FGConfig) (K : Nat) (hK : 2 ≤ K)
    (Λ : Record) (Hd : FGBlock V) (pair : FinalityPair)
    (hemit : finality_pair Λ (certificateHeadFields (certificateHeight E cfg K)
      (certificateFinality E cfg K) Hd) = some pair) :
    pair.height = (certificateHeight E cfg K Hd).h_j ∧ pair.target = (certificateHeight E cfg K
      Hd).J.root ∧
      (certificateFinality E cfg K Hd).h_F < pair.height ∧ TargetQCAt E Hd pair.height
      (certificateHeight E cfg K Hd).J :=
  provenance_finalityRow_of_heightLaws E (certificateHeight E cfg K) (certificateFinality E cfg K)
    (windowHeightLaws E cfg K hK) Λ Hd pair hemit

/-- Window views supply the height laws; all client premises stay explicit. -/
theorem window_provenance_finalityQC (E : Electorate V) (cfg : FGConfig) (K : Nat) (hK : 2 ≤ K)
    (faulty : Finset V) (hcap : E.weightOf faulty < E.q)
    (rows : Finset (Row V)) (Q : Finset V)
    (hQ : E.IsQuorum Q) (pair : FinalityPair)
    (hrows : ∀ j ∈ Q, ∃ a ∈ rows, a.signer = j ∧ a.finality_pair = some pair)
    (hemit : ∀ a ∈ rows, a.signer ∉ faulty → a.finality_pair = some pair →
      ∃ Λ Hd, finality_pair Λ (certificateHeadFields (certificateHeight E cfg K)
      (certificateFinality E cfg K) Hd) = some pair) :
    ∃ Hd, pair.height = (certificateHeight E cfg K Hd).h_j ∧
      pair.target = (certificateHeight E cfg K Hd).J.root ∧
      TargetQCAt E Hd pair.height (certificateHeight E cfg K Hd).J :=
  provenance_finalityQC_of_heightLaws E (certificateHeight E cfg K) (certificateFinality E cfg K)
    (windowHeightLaws E cfg K hK) faulty hcap rows Q hQ pair hrows hemit

/-- Window views supply the height laws; all client premises stay explicit. -/
theorem window_exists_crossing_quorum_ne_justified (E : Electorate V) (cfg : FGConfig) (K : Nat)
  (hK : 2 ≤ K)
    (B W : FGBlock V) (hroot : RootInjectiveOn B W)
    (hJ : (certificateHeight E cfg K B).h_j ≠ 0)
    (hW : (certificateHeight E cfg K B).h_j < (certificateHeight E cfg K W).h)
    (hnot : ¬ FGBlock.Preceq (certificateHeight E cfg K B).J W) :
    ∃ X : FGBlock V, X.root ≠ (certificateHeight E cfg K B).J.root ∧
      ∃ Q : Finset V, E.IsQuorum Q ∧
      ∀ i ∈ Q, ∃ b ∈ chainRows W, b.signer = i ∧
        b.height_pair.matchesEntry (certificateHeight E cfg K B).h_j X.root = true :=
  exists_crossing_quorum_ne_justified_of_heightLaws E (certificateHeight E cfg K)
    (windowHeightLaws E cfg K hK) B W hroot hJ hW hnot

/-- Window views supply the height laws; all client premises stay explicit. -/
theorem window_exists_honest_timeout_of_crossing (E : Electorate V) (cfg : FGConfig) (K : Nat) (hK
  : 2 ≤ K)
    (faulty : Finset V)
    (B W : FGBlock V) (hroot : RootInjectiveOn B W)
    (hcap : E.weightOf faulty + E.totalWeight < 2 * E.q)
    (hJ : (certificateHeight E cfg K B).h_j ≠ 0)
    (hW : (certificateHeight E cfg K B).h_j < (certificateHeight E cfg K W).h)
    (hnot : ¬ FGBlock.Preceq (certificateHeight E cfg K B).J W)
    (hhonest : ∀ a ∈ chainRows B, ∀ b ∈ chainRows W, a.signer ∉ faulty → ¬ Slashable a b) :
    ∃ i, i ∉ faulty ∧ ∃ X : BlockId, X ≠ (certificateHeight E cfg K B).J.root ∧
      (∃ a ∈ chainRows B, a.signer = i ∧
        a.height_pair =
          .vote (certificateHeight E cfg K B).h_j (certificateHeight E cfg K B).J.root false) ∧
      (∃ b ∈ chainRows W, b.signer = i ∧
        b.height_pair = .vote (certificateHeight E cfg K B).h_j X true) :=
  exists_honest_timeout_of_crossing_of_heightLaws E (certificateHeight E cfg K)
    (windowHeightLaws E cfg K hK)
    faulty B W hroot hcap hJ hW hnot hhonest

/-- An honest row names the latest pair of its signer's head at emission. On the
including chain, that pair can be an older retained entry. Such an entry gains bits
from any admitted row with that exact pair, through either R6W arm. The head read is
independent of the retained entries. Emission also checks the client record. -/
theorem window_headFields_latest (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (Hd : FGBlock V) (Λ : Record) :
    certificateHeadFields (certificateHeight E cfg K) (certificateFinality E cfg K) Hd =
      ⟨(derive E cfg K Hd).h_j, (derive E cfg K Hd).J.root, (derive E cfg K Hd).h_F⟩ ∧
    finality_pair Λ (certificateHeadFields (certificateHeight E cfg K) (certificateFinality E cfg
      K) Hd) =
      (if (derive E cfg K Hd).h_F < (derive E cfg K Hd).h_j ∧
          (Λ.target (derive E cfg K Hd).h_j = none ∨
            Λ.target (derive E cfg K Hd).h_j = some (derive E cfg K Hd).J.root) ∧
          Λ.timeout (derive E cfg K Hd).h_j = false ∧
          (Λ.lock (derive E cfg K Hd).h_j = none ∨
            Λ.lock (derive E cfg K Hd).h_j = some (derive E cfg K Hd).J.root) then
        some ⟨(derive E cfg K Hd).h_j, (derive E cfg K Hd).J.root⟩ else none) := by
  exact ⟨rfl, rfl⟩

end AvailableChain.KitFG.Window
end
