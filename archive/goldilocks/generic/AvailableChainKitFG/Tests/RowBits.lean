module
public import AvailableChainKitFG.RowBits -- shake: keep (examples)

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

set_option maxRecDepth 4096

namespace AvailableChain.KitFG.Tests.RowBits

open AvailableChain.SimplexFG

def targetCarrier : FGBlock (Fin 4) := .node .genesis 1 ⟨100⟩ 0 [rowT 0, rowT 1]
def targetTail : FGBlock (Fin 4) := .node targetCarrier 2 ⟨101⟩ 0 [rowT 0]

-- An exact target occurrence survives a duplicate row and a later block.
example : 0 ∈ chainBits .target (derive E4 cfg1 targetTail) := by
  exact bit_from_row E4 cfg1 .target .genesis targetTail 1 ⟨100⟩ 0 [rowT 0, rowT 1]
    (rowT 0) (by decide +kernel) (by decide +kernel)
    (by unfold rowMatchesBit; decide +kernel) (by unfold sameBitState; decide +kernel)

example : chainBits .target (derive E4 cfg1 targetCarrier) ⊆
    chainBits .target (derive E4 cfg1 targetTail) :=
  bit_persist E4 cfg1 .target targetCarrier targetTail
    (by decide +kernel) (by unfold sameBitState; decide +kernel)

def timeoutCarrier : FGBlock (Fin 4) := .node .genesis 1 ⟨102⟩ 0 [rowX 0, rowX 1, rowX 2]
def timeoutTail : FGBlock (Fin 4) := .node timeoutCarrier 2 ⟨103⟩ 0 []

-- Timeout progress counts before maturity, without target participation.
example : 1 ∈ chainBits .progress (derive E4 ⟨5⟩ timeoutTail) := by
  exact bit_from_row E4 ⟨5⟩ .progress .genesis timeoutTail 1 ⟨102⟩ 0
    [rowX 0, rowX 1, rowX 2] (rowX 1) (by decide +kernel)
    (by decide +kernel) (by unfold rowMatchesBit; decide +kernel)
    (by unfold sameBitState; decide +kernel)

example : chainBits .progress (derive E4 ⟨5⟩ timeoutCarrier) ⊆
    chainBits .progress (derive E4 ⟨5⟩ timeoutTail) :=
  bit_persist E4 ⟨5⟩ .progress timeoutCarrier timeoutTail
    (by decide +kernel) (by unfold sameBitState; decide +kernel)

example : chainBits .target (derive E4 ⟨5⟩ timeoutTail) = ∅ := by decide +kernel

def rowF (i : Fin 4) : Row (Fin 4) := ⟨i, .empty, some ⟨1, genesisRoot⟩⟩
def finalityCarrier : FGBlock (Fin 4) := .node B1 2 ⟨104⟩ 0 [rowF 0]
def finalityConsumed : FGBlock (Fin 4) :=
  .node finalityCarrier 3 ⟨105⟩ 0 [rowF 1, rowF 2]
def finalityTail : FGBlock (Fin 4) := .node finalityConsumed 4 ⟨106⟩ 0 []

-- A finality occurrence sets the bit in its carrier.
example : (rowF 0).signer ∈ chainBits .finality (derive E4 cfg1 finalityCarrier) := by
  exact bit_from_row E4 cfg1 .finality B1 finalityCarrier 2 ⟨104⟩ 0 [rowF 0] (rowF 0)
    (List.mem_singleton_self _) (preceq_refl _)
    (by unfold rowMatchesBit; decide +kernel) (by unfold sameBitState; decide +kernel)

-- Finality consumption changes h_F but keeps finalize and the matching key.
example : chainBits .finality (derive E4 cfg1 finalityCarrier) ⊆
    chainBits .finality (derive E4 cfg1 finalityTail) :=
  bit_persist E4 cfg1 .finality finalityCarrier finalityTail
    (by decide +kernel) (by unfold sameBitState; decide +kernel)

example : (derive E4 cfg1 finalityCarrier).h_F = 0 ∧
    (derive E4 cfg1 finalityTail).h_F = 1 ∧
    chainBits .finality (derive E4 cfg1 finalityTail) = {0, 1, 2} ∧
    ¬ rowMatchesBit .finality (derive E4 cfg1 finalityTail) (rowF 0) := by
  unfold rowMatchesBit
  decide +kernel

def heightRow (i : Fin 4) (timeout : Bool) : Row (Fin 4) :=
  ⟨i, .vote 2 B1.root timeout, none⟩
def progressAdvance : FGBlock (Fin 4) :=
  .node finalityCarrier 3 ⟨107⟩ 0 [heightRow 0 true, heightRow 1 true, heightRow 2 true]
def justificationAdvance : FGBlock (Fin 4) :=
  .node finalityCarrier 3 ⟨108⟩ 0 [heightRow 0 false, heightRow 1 false, heightRow 2 false]

-- A progress height advance keeps finality. A new justification clears it.
example : chainBits .finality (derive E4 cfg1 finalityCarrier) ⊆
    chainBits .finality (derive E4 cfg1 progressAdvance) :=
  bit_persist E4 cfg1 .finality finalityCarrier progressAdvance
    (by decide +kernel) (by unfold sameBitState; decide +kernel)

example : (derive E4 cfg1 progressAdvance).h = 3 ∧
    chainBits .finality (derive E4 cfg1 progressAdvance) = {0} ∧
    chainBits .finality (derive E4 cfg1 justificationAdvance) = ∅ ∧
    ¬ sameBitState .finality (derive E4 cfg1 finalityCarrier)
      (derive E4 cfg1 justificationAdvance) := by
  unfold sameBitState
  decide +kernel

-- The endpoint-key premise also excludes target/progress consumption.
example : chainBits .target (derive E4 cfg1 B1) = ∅ ∧
    chainBits .progress (derive E4 cfg1 B1) = ∅ ∧
    ¬ sameBitState .target (derive E4 cfg1 (.genesis : FGBlock (Fin 4)))
      (derive E4 cfg1 B1) := by
  unfold sameBitState
  decide +kernel

-- This is the Counts.lean:25 fold contract, with no lane-specific induction.
example {V : Type} [DecidableEq V] [RowCodec V]
    (rows : List (Row V)) (σ : ChainState V) (i : V)
    (hi : i ∈ σ.target_participation ∨ ∃ a ∈ rows, a.signer = i ∧
      a.height_pair = .vote σ.h σ.T_h.root false) :
    i ∈ (rows.foldl process_row σ).target_participation :=
  bit_fold_covered .target rows σ i hi

end AvailableChain.KitFG.Tests.RowBits
end
