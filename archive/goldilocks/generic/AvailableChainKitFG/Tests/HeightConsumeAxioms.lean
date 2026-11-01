module
public import AvailableChainKitFG.HeightConsume -- shake: keep (axioms)

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.KitFG.Tests.HeightConsume

open AvailableChain.SimplexFG

#print axioms transition_target_of_cover
#print axioms transition_progress_of_cover
#print axioms derive_target_of_cover
#print axioms derive_progress_of_cover

-- Stored target coverage needs no rows and no timeout premise.
example {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig) (σ : ChainState V) (B : FGBlock V)
    (hS : E.IsQuorum σ.target_participation) :
    (transition E cfg σ B []).h = σ.h + 1 ∧
      (transition E cfg σ B []).J = σ.T_h ∧
      (transition E cfg σ B []).h_j = σ.h :=
  transition_target_of_cover E cfg σ B [] σ.target_participation hS
    (fun _ hi => Or.inl hi)

-- Stored progress coverage needs no rows, but still needs maturity.
example {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig) (σ : ChainState V) (B : FGBlock V)
    (hS : E.IsQuorum σ.progress)
    (hmature : σ.T_h.slot + cfg.timeoutDelay ≤ B.slot) :
    (transition E cfg σ B []).h = σ.h + 1 :=
  transition_progress_of_cover E cfg σ B [] σ.progress hS
    (fun _ hi => Or.inl hi) hmature

def emptyElectorate : Electorate (Fin 0) := ⟨fun _ => 1, fun _ => Nat.one_pos⟩

-- With no voters, the empty set is a quorum. Target consumption is immediate.
example : (transition emptyElectorate ⟨5⟩ .initial .genesis []).h = 2 ∧
    (transition emptyElectorate ⟨5⟩ .initial .genesis []).J = .genesis ∧
    (transition emptyElectorate ⟨5⟩ .initial .genesis []).h_j = 1 :=
  transition_target_of_cover emptyElectorate ⟨5⟩ .initial .genesis [] ∅
    (by unfold Electorate.IsQuorum; decide +kernel) (by simp)

example : (transition emptyElectorate ⟨0⟩ .initial .genesis []).h = 2 :=
  transition_progress_of_cover emptyElectorate ⟨0⟩ .initial .genesis [] ∅
    (by unfold Electorate.IsQuorum; decide +kernel) (by simp) (by decide +kernel)

def oneElectorate : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => Nat.one_pos⟩
def oneHeightRow (timeout : Bool) : Row (Fin 1) :=
  ⟨0, .vote 1 genesisRoot timeout, none⟩

-- One target row is a quorum. It works before timeout maturity, even at slot zero.
example : (transition oneElectorate ⟨5⟩ .initial .genesis [oneHeightRow false]).h = 2 ∧
    (transition oneElectorate ⟨5⟩ .initial .genesis [oneHeightRow false]).J = .genesis ∧
    (transition oneElectorate ⟨5⟩ .initial .genesis [oneHeightRow false]).h_j = 1 :=
  transition_target_of_cover oneElectorate ⟨5⟩ .initial .genesis [oneHeightRow false] {0}
    (by unfold Electorate.IsQuorum; decide +kernel) (by decide +kernel)

-- The target corollary applies to a child of genesis.
example : (derive oneElectorate ⟨5⟩ (.node .genesis 0 ⟨100⟩ 0 [oneHeightRow false])).h = 2 ∧
    (derive oneElectorate ⟨5⟩ (.node .genesis 0 ⟨100⟩ 0 [oneHeightRow false])).J = .genesis ∧
    (derive oneElectorate ⟨5⟩ (.node .genesis 0 ⟨100⟩ 0 [oneHeightRow false])).h_j = 1 :=
  derive_target_of_cover oneElectorate ⟨5⟩ .genesis 0 ⟨100⟩ 0 [oneHeightRow false] {0}
    (by unfold Electorate.IsQuorum; decide +kernel) (by decide +kernel)

-- A single timeout row advances at zero delay without a justification write.
example : (transition oneElectorate ⟨0⟩ .initial .genesis [oneHeightRow true]).h = 2 ∧
    (transition oneElectorate ⟨0⟩ .initial .genesis [oneHeightRow true]).h_j = 0 := by
  constructor
  · exact transition_progress_of_cover oneElectorate ⟨0⟩ .initial .genesis
      [oneHeightRow true] {0} (by unfold Electorate.IsQuorum; decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

-- Timeout coverage is consumed exactly at maturity.
example : (derive oneElectorate ⟨5⟩ (.node .genesis 5 ⟨101⟩ 0 [oneHeightRow true])).h = 2 ∧
    (derive oneElectorate ⟨5⟩ (.node .genesis 5 ⟨101⟩ 0 [oneHeightRow true])).h_j = 0 := by
  constructor
  · exact derive_progress_of_cover oneElectorate ⟨5⟩ .genesis 5 ⟨101⟩ 0 [oneHeightRow true] {0}
      (by unfold Electorate.IsQuorum; decide +kernel) (by decide +kernel) (by decide +kernel)
  · decide +kernel

-- The same timeout quorum does not advance one slot before maturity.
example : (derive oneElectorate ⟨5⟩ (.node .genesis 4 ⟨102⟩ 0 [oneHeightRow true])).h = 1 ∧
    (derive oneElectorate ⟨5⟩ (.node .genesis 4 ⟨102⟩ 0 [oneHeightRow true])).h_j = 0 := by
  decide +kernel

def storedPair : ChainState (Fin 4) :=
  { ChainState.initial with target_participation := {0, 1}, progress := {0, 1} }

-- Two stored signers plus one target row give a quorum.
example : (transition E4 ⟨5⟩ storedPair .genesis [rowT 2]).h = 2 ∧
    (transition E4 ⟨5⟩ storedPair .genesis [rowT 2]).J = .genesis ∧
    (transition E4 ⟨5⟩ storedPair .genesis [rowT 2]).h_j = 1 :=
  transition_target_of_cover E4 ⟨5⟩ storedPair .genesis [rowT 2] {0, 1, 2}
    (by unfold Electorate.IsQuorum; decide +kernel) (by decide +kernel)

-- Mixed target and timeout progress advances at maturity without justification.
example : (transition E4 ⟨5⟩ storedPair (.node .genesis 5 ⟨103⟩ 0 []) [rowX 2]).h = 2 ∧
    (transition E4 ⟨5⟩ storedPair (.node .genesis 5 ⟨103⟩ 0 []) [rowX 2]).h_j = 0 := by
  constructor
  · exact transition_progress_of_cover E4 ⟨5⟩ storedPair (.node .genesis 5 ⟨103⟩ 0 [])
      [rowX 2] {0, 1, 2} (by unfold Electorate.IsQuorum; decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

-- Irrelevant rows and duplicate signers do not remove covered target bits.
example : (transition E4 ⟨5⟩ storedPair .genesis [rowX 3, rowT 2, rowT 2, rowX 0]).h = 2 ∧
    (transition E4 ⟨5⟩ storedPair .genesis [rowX 3, rowT 2, rowT 2, rowX 0]).J = .genesis ∧
    (transition E4 ⟨5⟩ storedPair .genesis [rowX 3, rowT 2, rowT 2, rowX 0]).h_j = 1 :=
  transition_target_of_cover E4 ⟨5⟩ storedPair .genesis [rowX 3, rowT 2, rowT 2, rowX 0]
    {0, 1, 2} (by unfold Electorate.IsQuorum; decide +kernel) (by decide +kernel)

end AvailableChain.KitFG.Tests.HeightConsume
end
