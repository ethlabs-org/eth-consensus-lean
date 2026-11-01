module
public import AvailableChainFGSA.Proofs.WindowRetention -- shake: keep (examples)
public import AvailableChainFGSA.Proofs.WindowOccurrences -- shake: keep (examples)
public import AvailableChainFGSA.Proofs.WindowTerminal -- shake: keep (examples)

@[expose] public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.FGSA.Window.RetentionTests

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.KitFG

abbrev retentionParams : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

def retentionTargets (h : Height) (X : FGBlock (Fin 4)) : List (Row (Fin 4)) :=
  [⟨0, .vote h X.root false, none⟩, ⟨1, .vote h X.root false, none⟩,
   ⟨2, .vote h X.root false, none⟩]

def retentionFirst : FGBlock (Fin 4) := .node .genesis 1 ⟨100⟩ 0 (retentionTargets 1 .genesis)
def retentionSecond : FGBlock (Fin 4) :=
  .node retentionFirst 2 ⟨101⟩ 0 (retentionTargets 2 retentionFirst)
def retentionThird : FGBlock (Fin 4) :=
  .node retentionSecond 3 ⟨102⟩ 0 (retentionTargets 3 retentionSecond)

set_option maxRecDepth 8192
set_option exponentiation.threshold 8192

/-- K = 2 retains the older key after one newer justification. -/
example : (derive retentionParams 2 retentionSecond).W =
    [⟨1, .genesis, ∅⟩, ⟨2, retentionFirst, ∅⟩] := by decide +kernel

example : ∃ d ∈ (derive retentionParams 2 retentionSecond).W,
    d.j = 1 ∧ d.X = .genesis ∧ (∅ : Finset (Fin 4)) ⊆ d.Q :=
  window_retained_of_scalar retentionParams 2 (by decide) retentionFirst retentionSecond
    (by decide +kernel) ⟨1, .genesis, ∅⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- Direct use of the birth-count theorem covers the only newer birth. -/
example : ∃ d ∈ (derive retentionParams 2 retentionSecond).W,
    d.j = 1 ∧ d.X = .genesis ∧ (∅ : Finset (Fin 4)) ⊆ d.Q := by
  apply window_retained_of_few_births retentionParams 2 (by decide)
    retentionFirst retentionSecond (by decide +kernel) ⟨1, .genesis, ∅⟩
    (by decide +kernel) (by decide +kernel) {retentionSecond} (by decide +kernel)
  intro C j X hCP hj hb
  by_cases hC : C = retentionSecond
  · exact Finset.mem_singleton.mpr hC
  · have hCA : FGBlock.Preceq C retentionFirst := preceq_parent_of_preceq_node hCP hC
    have hm := window_hj_mono retentionParams 2 (by decide) C retentionFirst hCA
    have hcj : (derive retentionParams 2 C).h_j = j := hb.2.2.2.1
    rw [hcj] at hm
    have first : (derive retentionParams 2 retentionFirst).h_j = 1 := by decide +kernel
    rw [first] at hm
    exact (Nat.not_lt_of_ge hm hj).elim

/-- The birth-count corollary uses the one real child after the fresh key. -/
example : ∃ d ∈ (derive retentionParams 2 retentionSecond).W,
    d.j = 1 ∧ d.X = .genesis ∧ (∅ : Finset (Fin 4)) ⊆ d.Q := by
  apply window_retained_fresh_one_newer retentionParams 2 (by decide)
    retentionFirst retentionSecond (by decide +kernel) ⟨1, .genesis, ∅⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    {retentionSecond} (by decide +kernel)
  intro C j X hAC hCP _
  by_cases hC : C = retentionSecond
  · exact Finset.mem_singleton.mpr hC
  · have hCA : FGBlock.Preceq C retentionFirst := preceq_parent_of_preceq_node hCP hC
    exact (hAC.2 (preceq_antisymm hAC.1 hCA)).elim

/-- Capacity removes the old key with no finality coverage. -/
example : (derive retentionParams 2 retentionThird).W =
      [⟨2, retentionFirst, ∅⟩, ⟨3, retentionSecond, ∅⟩] ∧
    (¬ ∃ d ∈ (derive retentionParams 2 retentionThird).W, d.j = 1 ∧ d.X = .genesis) ∧
    (derive retentionParams 2 retentionThird).h_F = 0 := by decide +kernel

def retentionLaterRows : List (Row (Fin 4)) :=
  [⟨0, .vote 3 retentionSecond.root false, some ⟨2, retentionFirst.root⟩⟩,
   ⟨1, .vote 3 retentionSecond.root false, some ⟨2, retentionFirst.root⟩⟩,
   ⟨2, .vote 3 retentionSecond.root false, some ⟨2, retentionFirst.root⟩⟩]
def retentionLater : FGBlock (Fin 4) := .node retentionThird 4 ⟨103⟩ 0 retentionLaterRows

/-- Later finality covers the evicted key through F and h_F. The key stays absent. -/
example : (¬ ∃ d ∈ (derive retentionParams 2 retentionLater).W,
      d.j = 1 ∧ d.X = .genesis) ∧
    1 ≤ (derive retentionParams 2 retentionLater).h_F ∧
    FGBlock.Preceq (.genesis : FGBlock (Fin 4)) (derive retentionParams 2 retentionLater).F ∧
    (derive retentionParams 2 retentionLater).F = retentionFirst := by decide +kernel

def retentionCurrent : Row (Fin 4) :=
  ⟨0, .vote 3 retentionSecond.root false, some ⟨1, genesisRoot⟩⟩
def retentionStale : Row (Fin 4) :=
  ⟨1, .vote 2 retentionFirst.root false, some ⟨1, genesisRoot⟩⟩
def retentionMixed : FGBlock (Fin 4) :=
  .node retentionSecond 3 ⟨104⟩ 1 [retentionCurrent, retentionStale]

/-- Both R6W arms add bits to the same older entry. Both bodies pass R3. -/
example : heightMatch (derive retentionParams 2 retentionSecond) retentionCurrent = true ∧
    staleUseful (derive retentionParams 2 retentionSecond) retentionStale = true ∧
    (RowBody.ofRow retentionCurrent).valid = true ∧
    (RowBody.ofRow retentionStale).valid = true ∧
    (derive retentionParams 2 retentionMixed).W =
      [⟨1, .genesis, {1, 0}⟩, ⟨2, retentionFirst, ∅⟩] := by decide +kernel

private theorem retentionMixed_rowsValid : ∀ P s r_s x rs,
    FGBlock.Preceq (.node P s r_s x rs) retentionMixed → ∀ a ∈ rs,
      (RowBody.ofRow a).valid = true ∧ r6w (derive retentionParams 2 P) a = true := by
  intro P s r_s x rs hC a ha
  simp only [retentionMixed, retentionSecond, retentionFirst, FGBlock.Preceq,
    FGBlock.preceq, Bool.or_eq_true, decide_eq_true_eq] at hC
  rcases hC with hC | hC | hC | hC
  · cases hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> decide +kernel
  · cases hC
    have all : ∀ a ∈ retentionTargets 2 retentionFirst,
        (RowBody.ofRow a).valid = true ∧ r6w (derive retentionParams 2 retentionFirst) a = true :=
      by decide +kernel
    exact all a ha
  · cases hC
    have all : ∀ a ∈ retentionTargets 1 .genesis,
        (RowBody.ofRow a).valid = true ∧ r6w (derive retentionParams 2 .genesis) a = true :=
      by decide +kernel
    exact all a ha
  · cases hC

def retentionProtected : FGBlock (Fin 4) := .node retentionMixed 4 ⟨105⟩ 0 []

private theorem retentionProtected_rowsValid : ∀ P s r_s x rs,
    FGBlock.Preceq (.node P s r_s x rs) retentionProtected → ∀ a ∈ rs,
      (RowBody.ofRow a).valid = true ∧ r6w (derive retentionParams 2 P) a = true := by
  intro P s r_s x rs hC a ha
  by_cases eq : FGBlock.node P s r_s x rs = retentionProtected
  · have rows : rs = [] := congrArg FGBlock.rows eq
    exact (List.not_mem_nil (rows ▸ ha)).elim
  · exact retentionMixed_rowsValid P s r_s x rs (preceq_parent_of_preceq_node hC eq) a ha

/-- Exact rows from both R6W arms keep their bits in a later child.
Every carried row satisfies the R3 + R6W premise. -/
example : retentionCurrent.signer ∈ (⟨1, .genesis, {1, 0}⟩ : Entry (Fin 4)).Q ∧
    retentionStale.signer ∈ (⟨1, .genesis, {1, 0}⟩ : Entry (Fin 4)).Q := by
  constructor
  · exact window_exact_row_no_missing_effect retentionParams 2 (by decide) retentionProtected
      1 .genesis ⟨1, .genesis, {1, 0}⟩ (by decide +kernel) rfl rfl
      retentionProtected_rowsValid retentionSecond 3 ⟨104⟩ 1 [retentionCurrent, retentionStale]
      (preceq_parent_node _ _ _ _ _) retentionCurrent (by decide +kernel) (by decide +kernel)
  · exact window_exact_row_no_missing_effect retentionParams 2 (by decide) retentionProtected
      1 .genesis ⟨1, .genesis, {1, 0}⟩ (by decide +kernel) rfl rfl
      retentionProtected_rowsValid retentionSecond 3 ⟨104⟩ 1 [retentionCurrent, retentionStale]
      (preceq_parent_node _ _ _ _ _) retentionStale (by decide +kernel) (by decide +kernel)

/-- The scalar theorem preserves a nonempty bit set across a child. -/
example : ∃ d ∈ (derive retentionParams 2 retentionProtected).W,
    d.j = 1 ∧ d.X = .genesis ∧ ({1, 0} : Finset (Fin 4)) ⊆ d.Q :=
  window_retained_of_scalar retentionParams 2 (by decide) retentionMixed retentionProtected
    (preceq_parent_node _ _ _ _ _) ⟨1, .genesis, {1, 0}⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def retentionLastBit : Row (Fin 4) :=
  ⟨2, .vote 3 retentionSecond.root false, some ⟨1, genesisRoot⟩⟩
def retentionConsume : FGBlock (Fin 4) := .node retentionMixed 4 ⟨106⟩ 0 [retentionLastBit]

/-- K = 2 protects the older entry across one newer justification.
Identity 2 completes its finality quorum in the child and consumes it. -/
example : (derive retentionParams 2 retentionMixed).W =
      [⟨1, .genesis, {1, 0}⟩, ⟨2, retentionFirst, ∅⟩] ∧
    (RowBody.ofRow retentionLastBit).valid = true ∧
    r6w (derive retentionParams 2 retentionMixed) retentionLastBit = true ∧
    (certificateFolded retentionParams 2 retentionConsume).W =
      [⟨1, .genesis, {2, 1, 0}⟩, ⟨2, retentionFirst, ∅⟩] ∧
    (derive retentionParams 2 retentionConsume).h_F = 1 ∧
    (derive retentionParams 2 retentionConsume).F = .genesis ∧
    (derive retentionParams 2 retentionConsume).W = [⟨2, retentionFirst, ∅⟩] := by decide +kernel

/-- Retained-or-covered needs no finality-height premise in either case. -/
example : (∃ d ∈ (derive retentionParams 2 retentionProtected).W,
      d.j = 1 ∧ d.X = .genesis ∧ ({1, 0} : Finset (Fin 4)) ⊆ d.Q) ∨
    (1 ≤ (derive retentionParams 2 retentionProtected).h_F ∧
      FGBlock.Preceq (.genesis : FGBlock (Fin 4))
        (derive retentionParams 2 retentionProtected).F) :=
  window_retained_or_covered retentionParams 2 (by decide) retentionMixed retentionProtected
    (preceq_parent_node _ _ _ _ _) ⟨1, .genesis, {1, 0}⟩ (by decide +kernel) (by decide +kernel)

example : (∃ d ∈ (derive retentionParams 2 retentionConsume).W,
      d.j = 1 ∧ d.X = .genesis ∧ ({1, 0} : Finset (Fin 4)) ⊆ d.Q) ∨
    (1 ≤ (derive retentionParams 2 retentionConsume).h_F ∧
      FGBlock.Preceq (.genesis : FGBlock (Fin 4))
        (derive retentionParams 2 retentionConsume).F) :=
  window_retained_or_covered retentionParams 2 (by decide) retentionMixed retentionConsume
    (preceq_parent_node _ _ _ _ _) ⟨1, .genesis, {1, 0}⟩ (by decide +kernel) (by decide +kernel)

def retentionReadyRows : List (Row (Fin 4)) :=
  [⟨0, .vote 4 retentionThird.root false, some ⟨1, genesisRoot⟩⟩,
   ⟨1, .vote 4 retentionThird.root false, some ⟨1, genesisRoot⟩⟩,
   ⟨2, .vote 4 retentionThird.root false, some ⟨1, genesisRoot⟩⟩,
   ⟨0, .vote 4 retentionThird.root false, some ⟨3, retentionSecond.root⟩⟩,
   ⟨1, .vote 4 retentionThird.root false, some ⟨3, retentionSecond.root⟩⟩,
   ⟨2, .vote 4 retentionThird.root false, some ⟨3, retentionSecond.root⟩⟩]
def retentionReady : FGBlock (Fin 4) := .node retentionThird 4 ⟨107⟩ 0 retentionReadyRows

/-- With K = 3, entries 1 and 3 are ready. Entry 2 has no finality QC,
but the selected descendant covers it. No row names the new height-4 entry.
The separate test below checks no replay. Its row fails R3: a row that passes
R3 and R6W cannot name an entry born at or after its carrier. -/
example : (certificateFolded retentionParams 3 retentionReady).W =
      [⟨1, .genesis, {2, 1, 0}⟩, ⟨2, retentionFirst, ∅⟩,
       ⟨3, retentionSecond, {2, 1, 0}⟩] ∧
    (derive retentionParams 3 retentionReady).h_F = 3 ∧
    (derive retentionParams 3 retentionReady).F = retentionSecond ∧
    FGBlock.Preceq retentionFirst (derive retentionParams 3 retentionReady).F ∧
    (derive retentionParams 3 retentionReady).W = [⟨4, retentionThird, ∅⟩] := by decide +kernel

def retentionPremature : Row (Fin 4) :=
  ⟨3, .vote 1 genesisRoot false, some ⟨1, genesisRoot⟩⟩
def retentionBirthRows : List (Row (Fin 4)) :=
  retentionTargets 1 .genesis ++ [retentionPremature]
def retentionBirth : FGBlock (Fin 4) := .node .genesis 1 ⟨108⟩ 0 retentionBirthRows

/-- R3 is necessary: R6W alone admits a row whose entry is born after the row fold. -/
example : (∀ a ∈ retentionBirthRows, rowValidW (derive retentionParams 2 .genesis)
      ⟨.seat .fg a.signer, .vote (RowBody.ofRow a)⟩ = true) ∧
    retentionPremature ∈ retentionBirth.rows ∧
    retentionPremature.finality_pair = some ⟨1, genesisRoot⟩ ∧
    (derive retentionParams 2 retentionBirth).W = [⟨1, .genesis, ∅⟩] ∧
    retentionPremature.signer ∉ (∅ : Finset (Fin 4)) ∧
    (RowBody.ofRow retentionPremature).valid = false := by decide +kernel

private instance retainedDecidable (p : Params) (B U : FGBlock (Fin p.n)) (j : Height) :
    Decidable (RetainedW p B j U) := by
  rw [RetainedW_def]
  infer_instance

private instance coveredDecidable (p : Params) (B U : FGBlock (Fin p.n)) (j : Height) :
    Decidable (CoveredW p B j U) := by
  rw [CoveredW_def]
  infer_instance

private instance bitDecidable (p : Params) (B U : FGBlock (Fin p.n))
    (j : Height) (i : Fin p.n) : Decidable (EntryBitW p B j U i) := by
  rw [EntryBitW_def]
  infer_instance

set_option maxRecDepth 8192
set_option exponentiation.threshold 8192

/-- The model scalar wrapper retains the older key with K = 2 and one newer birth. -/
example : RetainedW retentionParams retentionSecond 1 .genesis :=
  terminal_retained_scalarW retentionParams retentionFirst retentionSecond
    (by decide +kernel) 1 .genesis (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The model birth-count wrapper uses the only newer birth. -/
example : RetainedW retentionParams retentionSecond 1 .genesis := by
  apply terminal_retained_birthsW retentionParams retentionFirst retentionSecond
    (by decide +kernel) 1 .genesis (by decide +kernel) (by decide +kernel)
    {retentionSecond} (by decide +kernel)
  intro C j X hCP hj hb
  by_cases eq : C = retentionSecond
  · exact Finset.mem_singleton.mpr eq
  · have hCA := preceq_parent_of_preceq_node hCP eq
    have hm := window_hj_mono retentionParams 2 (by decide) C retentionFirst hCA
    have hcj : (derive retentionParams 2 C).h_j = j := hb.2.2.2.1
    rw [hcj] at hm
    have first : (derive retentionParams 2 retentionFirst).h_j = 1 := by decide +kernel
    rw [first] at hm
    exact (Nat.not_lt_of_ge hm hj).elim

/-- Capacity eviction gives neither a retained key nor coverage. -/
example : ¬ RetainedW retentionParams retentionThird 1 .genesis ∧
    ¬ CoveredW retentionParams retentionThird 1 .genesis := by decide +kernel

/-- The same evicted key is covered at the later endpoint and stays absent. -/
example : ¬ RetainedW retentionParams retentionLater 1 .genesis ∧
    CoveredW retentionParams retentionLater 1 .genesis := by decide +kernel

/-- An exact row through each R6W arm inserts the older entry's bit. -/
example : heightMatch (parentState retentionParams 2 retentionSecond 3)
      retentionCurrent = true ∧
    staleUseful (parentState retentionParams 2 retentionSecond 3) retentionStale = true ∧
    EntryBitW retentionParams retentionMixed 1 .genesis retentionCurrent.signer ∧
    EntryBitW retentionParams retentionMixed 1 .genesis retentionStale.signer := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_⟩
  · exact entry_bit_insertW retentionParams retentionSecond 3 ⟨104⟩ 1
      [retentionCurrent, retentionStale] 1 .genesis (by decide +kernel)
      (by decide +kernel) retentionCurrent (by decide +kernel) (by decide +kernel)
  · exact entry_bit_insertW retentionParams retentionSecond 3 ⟨104⟩ 1
      [retentionCurrent, retentionStale] 1 .genesis (by decide +kernel)
      (by decide +kernel) retentionStale (by decide +kernel) (by decide +kernel)

example : EntryBitW retentionParams retentionProtected 1 .genesis retentionStale.signer :=
  entry_bit_occurrenceW retentionParams retentionFirst retentionMixed retentionProtected
    (by rw [StrictPrefix_def]; decide +kernel)
    (by decide +kernel) 1 .genesis
    (by decide +kernel) (by decide +kernel) retentionStale
    (by decide +kernel) (by decide +kernel)

example : EntryBitW retentionParams retentionProtected 1 .genesis retentionCurrent.signer :=
  entry_bit_persistW retentionParams retentionMixed retentionProtected
    (by decide +kernel) 1 .genesis retentionCurrent.signer
    (by decide +kernel) (by decide +kernel)

/-- The full history wrapper supplies the actual eviction step with K entries. -/
example : ∃ P s r_s x rs, FGBlock.Preceq retentionFirst P ∧
    FGBlock.Preceq (.node P s r_s x rs) retentionThird ∧
    RetainedW retentionParams P 1 .genesis ∧
    ¬ RetainedW retentionParams (.node P s r_s x rs) 1 .genesis ∧
    (derive retentionParams 2 (.node P s r_s x rs)).W.length = 2 := by
  rcases entry_historyW retentionParams retentionFirst retentionThird
      (by decide +kernel) 1 .genesis (by decide +kernel) with retained | covered | evicted
  · exact (show ¬ RetainedW retentionParams retentionThird 1 .genesis
      by decide +kernel) retained |>.elim
  · exact (show ¬ CoveredW retentionParams retentionThird 1 .genesis
      by decide +kernel) covered.2 |>.elim
  · obtain ⟨_, _, _, P, s, r_s, x, rs, hAP, hPB, hp, gone, full, _⟩ := evicted
    exact ⟨P, s, r_s, x, rs, hAP, hPB, hp, gone, full⟩

/-- The F8-W cap preserves the key after one newer justification. -/
example : RetainedW retentionParams retentionSecond 1 .genesis ∨
    CoveredW retentionParams retentionSecond 1 .genesis :=
  terminalRetentionW retentionParams retentionFirst retentionSecond 0 .genesis 0 8
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun _ => by decide +kernel)

/-- Finality deletion discharges the coverage branch of the same F8-W contract. -/
example : RetainedW retentionParams retentionConsume 1 .genesis ∨
    CoveredW retentionParams retentionConsume 1 .genesis :=
  terminalRetentionW retentionParams retentionFirst retentionConsume 0 .genesis 1 0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun _ => by decide +kernel)

end AvailableChain.FGSA.Window.RetentionTests
end
