module
public import AvailableChainFGSA.Proofs.WindowLiveness -- shake: keep (axioms)

@[expose] public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.FGSA.Window.LivenessTests

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.KitFG

abbrev livenessParams : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

def livenessTargets (h : Height) (X : FGBlock (Fin 4)) : List (Row (Fin 4)) :=
  [⟨0, .vote h X.root false, none⟩, ⟨1, .vote h X.root false, none⟩,
   ⟨2, .vote h X.root false, none⟩]

def livenessFirst : FGBlock (Fin 4) := .node .genesis 1 ⟨100⟩ 0 (livenessTargets 1 .genesis)

def livenessVote (i : Fin 4) : Row (Fin 4) :=
  ⟨i, .vote 2 livenessFirst.root false, some ⟨1, genesisRoot⟩⟩

def livenessGrow : FGBlock (Fin 4) := .node livenessFirst 2 ⟨101⟩ 0 [livenessVote 0]
def livenessSecondRows : List (Row (Fin 4)) :=
  livenessTargets 2 livenessFirst ++ [livenessVote 1]
def livenessSecond : FGBlock (Fin 4) := .node livenessGrow 3 ⟨102⟩ 0 livenessSecondRows

def livenessFinalRows : List (Row (Fin 4)) :=
  [livenessVote 2, ⟨0, .empty, some ⟨2, livenessFirst.root⟩⟩,
   ⟨1, .empty, some ⟨2, livenessFirst.root⟩⟩,
   ⟨2, .empty, some ⟨2, livenessFirst.root⟩⟩]
def livenessFinish : FGBlock (Fin 4) := .node livenessSecond 4 ⟨103⟩ 0 livenessFinalRows

set_option maxRecDepth 8192
set_option exponentiation.threshold 8192

/-- Item 1: the current-height arm adds the exact finality bit. -/
example : heightMatch (derive livenessParams 2 livenessFirst) (livenessVote 0) = true ∧
    (0 : Fin 4) ∈ ({0} : Finset (Fin 4)) := by
  refine ⟨by decide +kernel, ?_⟩
  exact window_bit_add_of_row livenessParams 2 (by decide) livenessFirst 2 ⟨101⟩ 0 [livenessVote 0]
    ⟨1, .genesis, ∅⟩ ⟨1, .genesis, {0}⟩ (by decide +kernel) (by decide +kernel)
    rfl rfl (livenessVote 0) (by decide +kernel) rfl

def livenessFreshSecond : FGBlock (Fin 4) :=
  .node livenessFirst 2 ⟨104⟩ 0 (livenessTargets 2 livenessFirst)

/-- Item 1: the stale arm has the same bit effect. -/
example : heightMatch (derive livenessParams 2 livenessFreshSecond) (livenessVote 0) = false ∧
    staleUseful (derive livenessParams 2 livenessFreshSecond) (livenessVote 0) = true ∧
    (0 : Fin 4) ∈ ({0} : Finset (Fin 4)) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  exact window_bit_add_of_row livenessParams 2 (by decide) livenessFreshSecond 3 ⟨106⟩ 0
      [livenessVote 0]
    ⟨1, .genesis, ∅⟩ ⟨1, .genesis, {0}⟩ (by decide +kernel) (by decide +kernel)
    rfl rfl (livenessVote 0) (by decide +kernel) rfl

/-- Item 2: a bit from an earlier block remains after J changes. -/
example : (derive livenessParams 2 livenessFirst).J ≠ (derive livenessParams 2 livenessSecond).J ∧
    (0 : Fin 4) ∈ ({1, 0} : Finset (Fin 4)) := by
  refine ⟨by decide +kernel, ?_⟩
  exact (window_bits_accumulate livenessParams 2 (by decide) livenessFirst livenessSecond
    (by decide +kernel) ⟨1, .genesis, ∅⟩ ⟨1, .genesis, {1, 0}⟩
    (by decide +kernel) (by decide +kernel) rfl rfl).2 livenessGrow
      (by rw [StrictPrefix_def]; decide +kernel) (by decide +kernel)
      (livenessVote 0) (by decide +kernel) rfl

/-- Item 3 (m9): the parent has only two bits. C itself carries the missing
signer and completes the quorum, across a change to J. -/
example : (⟨1, .genesis, {1, 0}⟩ : Entry (Fin 4)) ∈
      (derive livenessParams 2 livenessSecond).W ∧
    (2 : Fin 4) ∉ ({1, 0} : Finset (Fin 4)) ∧
    livenessVote 2 ∈ livenessFinish.rows ∧
    FGBlock.Preceq (.genesis : FGBlock (Fin 4)) (derive livenessParams 2 livenessFinish).F ∧
    1 ≤ (derive livenessParams 2 livenessFinish).h_F := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  apply window_finalize_of_accumulated_quorum livenessParams 2 (by decide)
    livenessFirst livenessSecond (by decide +kernel) 4 ⟨103⟩ 0 livenessFinalRows
    ⟨1, .genesis, ∅⟩ ⟨1, .genesis, {1, 0}⟩ (by decide +kernel) (by decide +kernel)
    rfl rfl {0, 1, 2} (by unfold Electorate.IsQuorum; decide +kernel)
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · exact Or.inr ⟨livenessGrow, by rw [StrictPrefix_def]; decide +kernel, by decide +kernel,
      livenessVote 0, by decide +kernel, rfl, rfl⟩
  · exact Or.inr ⟨livenessSecond, by rw [StrictPrefix_def]; decide +kernel, by decide +kernel,
      livenessVote 1, by decide +kernel, rfl, rfl⟩
  · exact Or.inr ⟨livenessFinish, by rw [StrictPrefix_def]; decide +kernel, by decide +kernel,
      livenessVote 2, by decide +kernel, rfl, rfl⟩

/-- Both entries are ready. The higher entry wins, so equality for item 3
would be false. The finality rows with empty height pairs test the raw fold. -/
example : (derive livenessParams 2 livenessFinish).h_F = 2 ∧
    (derive livenessParams 2 livenessFinish).F = livenessFirst ∧
    (derive livenessParams 2 livenessFinish).F ≠ .genesis := by decide +kernel

def livenessThirdRows : List (Row (Fin 4)) := livenessTargets 3 livenessSecond
def livenessThird : FGBlock (Fin 4) := .node livenessSecond 4 ⟨105⟩ 0 livenessThirdRows

/-- Item 4: append at capacity keeps heights 2 and 3. -/
example : (derive livenessParams 2 livenessThird).W =
    [⟨2, livenessFirst, ∅⟩, ⟨3, livenessSecond, ∅⟩] := by decide +kernel

example : ∃ older, (derive livenessParams 2 livenessThird).W =
      older ++ [⟨3, livenessSecond, ∅⟩] ∧
    (∀ d ∈ older, d.j < 3) ∧ (derive livenessParams 2 livenessThird).h_F < 3 := by
  exact (window_target_appended_newest livenessParams 2 (by decide)
    livenessSecond 4 ⟨105⟩ 0 livenessThirdRows (by decide +kernel)).2

/-- Item 5: one newer entry is below capacity; the old bits remain. -/
example : ∃ d ∈ (derive livenessParams 2 livenessSecond).W,
    d.j = 1 ∧ d.X = .genesis ∧ ({0} : Finset (Fin 4)) ⊆ d.Q :=
  window_retained_of_few_newer livenessParams 2 (by decide) livenessGrow 3 ⟨102⟩ 0
      livenessSecondRows
    ⟨1, .genesis, {0}⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Item 5: both children after the first birth satisfy the retention bounds. -/
example : ∃ d ∈ (derive livenessParams 2 livenessSecond).W,
    d.j = 1 ∧ d.X = .genesis ∧ (∅ : Finset (Fin 4)) ⊆ d.Q := by
  apply window_retained_along livenessParams 2 (by decide) livenessFirst livenessSecond
    (by decide +kernel) ⟨1, .genesis, ∅⟩ (by decide +kernel)
  intro P s r_s x rs _ hPC
  have hng : FGBlock.node P s r_s x rs ≠ .genesis := by intro h; cases h
  have hc : FGBlock.node P s r_s x rs = livenessSecond ∨
      FGBlock.node P s r_s x rs = livenessGrow ∨ FGBlock.node P s r_s x rs = livenessFirst := by
    simpa only [livenessSecond, livenessGrow, livenessFirst, FGBlock.Preceq,
      FGBlock.preceq, Bool.or_eq_true, decide_eq_true_eq, hng,
      or_false] using hPC
  rcases hc with h | h | h
  all_goals rw [h]; decide +kernel

#print axioms window_bit_add_of_row
#print axioms window_bits_accumulate
#print axioms window_finalize_of_accumulated_quorum
#print axioms window_target_appended_newest
#print axioms window_retained_of_few_newer
#print axioms window_retained_along

end AvailableChain.FGSA.Window.LivenessTests
end
