module
public import AvailableChainFGSA.Proofs.WindowCertificates

@[expose] public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.FGSA.Window.Tests

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive

abbrev params : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

def block1 : FGBlock (Fin 4) := .node .genesis 1 ⟨100⟩ 0 []
def block2 : FGBlock (Fin 4) := .node block1 2 ⟨101⟩ 0 []
def block3 : FGBlock (Fin 4) := .node block2 3 ⟨102⟩ 0 []

def targets (h : Height) (X : FGBlock (Fin 4)) : List (Row (Fin 4)) :=
  [⟨0, .vote h X.root false, none⟩, ⟨1, .vote h X.root false, none⟩,
   ⟨2, .vote h X.root false, none⟩]

def justified1 : State (Fin 4) := transition params 2 initial block1 (targets 1 .genesis)
def justified2 : State (Fin 4) := transition params 2 justified1 block2 (targets 2 block1)
def justified3 : State (Fin 4) := transition params 2 justified2 block3 (targets 3 block2)

example : params.E.q = 3 := by decide

/-- Three justifications with capacity two evict only the oldest entry. -/
example : justified3.W = [⟨2, block1, ∅⟩, ⟨3, block2, ∅⟩] ∧
    justified3.h_j = 3 ∧ justified3.J = block2 ∧ justified3.h = 4 := by decide

/-- Capacity eviction is not finality. -/
example : justified3.h_F = 0 ∧ justified3.F = .genesis := by decide

def ready : State (Fin 4) :=
  { initial with
    h := 4, h_j := 3, J := block2
    W := [⟨1, .genesis, {0, 1, 2}⟩, ⟨2, block1, ∅⟩, ⟨3, block2, {0, 1, 2}⟩] }

/-- The greatest of two ready entries wins; the middle entry has no quorum. -/
example : (process_height_events params.E params.cfg 3 ready).F = block2 ∧
    (process_height_events params.E params.cfg 3 ready).h_F = 3 ∧
    (process_height_events params.E params.cfg 3 ready).W = [] ∧
    (process_height_events params.E params.cfg 3 ready).h_j = 3 ∧
    (process_height_events params.E params.cfg 3 ready).J = block2 := by decide

/-- Selection uses height, not position in the list. -/
example : (process_height_events params.E params.cfg 3
    { ready with W := ready.W.reverse }).h_F = 3 := by decide

def staleState : State (Fin 4) :=
  { initial with
    h := 3, T_h := block2, h_j := 2, J := block1
    W := [⟨1, .genesis, ∅⟩, ⟨2, block1, ∅⟩] }
def stale : Row (Fin 4) := ⟨0, .vote 2 block1.root false, some ⟨1, genesisRoot⟩⟩

/-- A useful stale row changes only its matching window bit. -/
example : process_row staleState stale =
    { staleState with W := [⟨1, .genesis, {0}⟩, ⟨2, block1, ∅⟩] } := by decide
example : staleUseful staleState stale = true ∧ r6w staleState stale = true ∧
    heightMatch staleState stale = false := by decide
example : projectHeight (process_row staleState stale) = projectHeight staleState := by rfl

/-- Future height and wrong current entry fail both R6-window arms. -/
example : r6w staleState { stale with height_pair := .vote 4 block2.root false } = false ∧
    r6w staleState { stale with height_pair := .vote 3 genesisRoot false } = false := by decide
example : r6w staleState { stale with height_pair := .empty } = false ∧
    r6w staleState { stale with finality_pair := some ⟨2, block1.root⟩ } = false := by decide

/-- The wire check decodes the FG seat; another authentication form fails. -/
example : rowValidW staleState
    ⟨.seat .fg 0, .vote ⟨stale.height_pair, stale.finality_pair⟩⟩ = true ∧
    rowValidW staleState
    ⟨.none, .vote ⟨stale.height_pair, stale.finality_pair⟩⟩ = false := by decide

def current : Row (Fin 4) := ⟨1, .vote 3 block2.root false, some ⟨1, genesisRoot⟩⟩

/-- A current row can set both height sets and a retained finality bit. -/
example : heightMatch staleState current = true ∧
    process_row staleState current =
      { staleState with
        target_participation := {1}, progress := {1}
        W := [⟨1, .genesis, {1}⟩, ⟨2, block1, ∅⟩] } := by decide

/-- A timeout sets progress and finality, but does not set target. -/
example : process_row staleState { current with height_pair := .vote 3 block2.root true } =
    { staleState with progress := {1}, W := [⟨1, .genesis, {1}⟩, ⟨2, block1, ∅⟩] } := by decide

def appendRows : List (Row (Fin 4)) :=
  targets 1 .genesis ++ [⟨3, .vote 2 block1.root false, some ⟨1, genesisRoot⟩⟩]

/-- The raw fold does not replay a row against the entry appended later. -/
example : (transition params 2 initial block1 appendRows).W = [⟨1, .genesis, ∅⟩] ∧
    (transition params 2 initial block1 appendRows).h_F = 0 := by decide

/-- Three timeouts wait for maturity, then advance without an append. -/
example : (process_height_events params.E ⟨2⟩ 2
    { staleState with s := 3, progress := {0, 1, 2} }).h = 3 ∧
    (process_height_events params.E ⟨2⟩ 2
    { staleState with s := 4, progress := {0, 1, 2} }).h = 4 ∧
    (process_height_events params.E ⟨0⟩ 2
    { staleState with s := 2, progress := {0, 1, 2} }).W = staleState.W := by decide

/-- A target quorum does not wait for timeout maturity. -/
example : (process_height_events params.E ⟨100⟩ 2
    { staleState with target_participation := {0, 1, 2} }).h = 4 := by decide

def derived1 : FGBlock (Fin 4) := .node .genesis 1 ⟨103⟩ 0 (targets 1 .genesis)
def derived2 : FGBlock (Fin 4) := .node derived1 2 ⟨104⟩ 0 (targets 2 derived1)
def mixed : FGBlock (Fin 4) := .node derived2 3 ⟨105⟩ 0
  [⟨0, .vote 3 derived2.root false, some ⟨1, genesisRoot⟩⟩,
   ⟨1, .vote 2 derived1.root false, some ⟨1, genesisRoot⟩⟩,
   ⟨2, .empty, some ⟨2, derived1.root⟩⟩]

set_option maxRecDepth 4096 in
set_option exponentiation.threshold 4096 in
/-- Mixed matching, stale, and finality-only rows use the original tree. -/
example : projectHeight (derive params 2 mixed) =
    KitFG.heightOf (SimplexFG.derive params.E params.cfg mixed) := by rfl

/-- Distinct windows with equal projections have equal heights after a step. -/
example : projectHeight staleState = projectHeight { staleState with W := [] } := by rfl
example : projectHeight (transition params 2 staleState block3 [stale, current]) =
    projectHeight (transition params 2 { staleState with W := [] }
      block3 [stale, current]) := by rfl

/-- The latest-pair read is empty when that pair was pruned. -/
example : latestQfin ready = {0, 1, 2} ∧
    latestQfin (process_height_events params.E params.cfg 3 ready) = ∅ := by decide

/-- W1: finality runs before target append and capacity eviction. -/
def readyAtCapacity : State (Fin 4) :=
  { staleState with
    target_participation := {0, 1, 2}
    W := [⟨1, .genesis, {0, 1, 2}⟩, ⟨2, block1, ∅⟩] }

example : (process_height_events params.E params.cfg 2 readyAtCapacity).h_F = 1 ∧
    (process_height_events params.E params.cfg 2 readyAtCapacity).W =
      [⟨2, block1, ∅⟩, ⟨3, block2, ∅⟩] := by decide

/-- W2: the row fold completes a quorum that this same block finalizes. -/
def almostReady : State (Fin 4) :=
  { staleState with W := [⟨1, .genesis, {0, 1}⟩, ⟨2, block1, ∅⟩] }

example : (transition params 2 almostReady block3
    [⟨2, .empty, some ⟨1, genesisRoot⟩⟩]).h_F = 1 ∧
    (transition params 2 almostReady block3
    [⟨2, .empty, some ⟨1, genesisRoot⟩⟩]).W = [⟨2, block1, ∅⟩] := by decide

/-- W2: a finality-only row for an evicted entry has no effect. -/
example : process_row justified3 ⟨0, .empty, some ⟨1, genesisRoot⟩⟩ = justified3 := by decide


/-- FG1b: these target rows also name the entry born after their fold. -/
def originBirth : FGBlock (Fin 4) := .node .genesis 1 ⟨106⟩ 0
  [⟨0, .vote 1 genesisRoot false, some ⟨1, genesisRoot⟩⟩,
   ⟨1, .vote 1 genesisRoot false, some ⟨1, genesisRoot⟩⟩,
   ⟨2, .vote 1 genesisRoot false, some ⟨1, genesisRoot⟩⟩]

def originLater : FGBlock (Fin 4) := .node originBirth 2 ⟨107⟩ 0
  [⟨3, .empty, some ⟨1, genesisRoot⟩⟩]

/-- Birth-block rows are not applied to the appended entry. -/
example : (derive params 2 originBirth).W = [⟨1, .genesis, ∅⟩] ∧
    (certificateFolded params 2 originBirth).W = [] := by decide

/-- The retained entry has its non-strict origin in this very block. -/
example : EntryOriginAt params 2 originBirth ⟨1, .genesis, ∅⟩ :=
  window_entry_origin params 2 (by decide) originBirth _ (by decide)

private theorem originBirth_birth :
    KitFG.JustificationBirth params.E (certificateHeight params 2)
      originBirth 1 .genesis := by
  obtain ⟨C, hc, hb, _⟩ :=
    window_entry_origin params 2 (by decide) originBirth ⟨1, .genesis, ∅⟩ (by decide)
  have heq : C = originBirth := by
    by_contra hne
    exact hb.1 (KitFG.preceq_genesis.mp (KitFG.preceq_parent_of_preceq_node hc hne))
  simpa only [heq] using hb

/-- No earlier birth can replace this block's birth witness. -/
example : ¬ ∃ C, KitFG.StrictPrefix C originBirth ∧
    KitFG.JustificationBirth params.E (certificateHeight params 2) C 1 .genesis := by
  rintro ⟨C, hc, hb⟩
  exact hb.1 (KitFG.preceq_genesis.mp (KitFG.preceq_parent_of_preceq_node hc.1 hc.2))

/-- Only the later signer is counted; the three birth-block rows stay excluded. -/
example : (derive params 2 originLater).W = [⟨1, .genesis, {3}⟩] ∧
    (certificateFolded params 2 originLater).W = [⟨1, .genesis, {3}⟩] := by decide

/-- The older retained entry has the original birth as a strict ancestor. -/
example : KitFG.StrictPrefix originBirth originLater ∧
    KitFG.JustificationBirth params.E (certificateHeight params 2) originBirth 1 .genesis ∧
    EntryOriginAt params 2 originLater ⟨1, .genesis, {3}⟩ := by
  refine ⟨⟨KitFG.preceq_parent_node _ _ _ _ _, by decide⟩, originBirth_birth, ?_⟩
  exact window_entry_origin params 2 (by decide) originLater _ (by decide)

/-- Prefinality exposes a strictly earlier birth and the exact carried pair. -/
example : ∃ C, KitFG.StrictPrefix C originLater ∧
    KitFG.JustificationBirth params.E (certificateHeight params 2) C 1 .genesis ∧
    ∀ i ∈ ({3} : Finset (Fin 4)), ∃ carrier a,
      KitFG.StrictPrefix C carrier ∧ FGBlock.Preceq carrier originLater ∧
      a ∈ carrier.rows ∧ a.signer = i ∧ a.finality_pair = some ⟨1, genesisRoot⟩ :=
  window_prefinal_entry_origin params 2 (by decide) originLater
    ⟨1, .genesis, {3}⟩ (by decide)

end AvailableChain.FGSA.Window.Tests
end
