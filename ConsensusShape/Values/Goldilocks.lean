module
public import ConsensusShape.Values.Common

@[expose] public section

/-! # Goldilocks as a value (D-16, D-17; interim)

The Goldilocks skeleton and contract: two outputs, `confirmed` (serving the
available and the stable capability: in the round model stable = confirmed)
and `finalized` (final); slot proposals by one selected key per slot on a grid
of `4·Δ` slots; polling disabled. The committee kinds `head`/`fin` and their
phases are placeholders until the FG-SA migration fixes them.

Interim contract (index: the recurrence gap `k : ℕ+`): the numbers are a
parameter `P : Params ℕ+` (pinned FG-SA numbers come with the properties
sheet); progress is one honest ready proposer in every window of `k` slots for
the available and stable capabilities, and the finality pattern `finPattern`
in every window of `k` slots for the final one. Both fit the skeleton (one
proposer per slot). -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public SelSpec pubOf)

/-- The Goldilocks output identifiers. -/
inductive GOut where
  | confirmed
  | finalized
  deriving DecidableEq, Repr

/-- The Goldilocks schema: `confirmed` is available and stable (aliased: the
round model's stable ledger is the confirmed one), `finalized` final. -/
def goldilocksSchema : OutputSchema :=
  ⟨GOut, fun
    | .available => some .confirmed
    | .stable => some .confirmed
    | .final => some .finalized⟩

/-- The Goldilocks schema serves a ledger (it has a final output). -/
theorem goldilocksSchema_serves : goldilocksSchema.Serves := Or.inl rfl

/-- Placeholder committee kinds (the FG-SA migration fixes them). -/
inductive GKind where
  | head
  | fin
  deriving DecidableEq, Repr

/-- Slots of `4·Δ`. -/
def goldilocksGrid : TimeGrid := ⟨4, by decide⟩

/-- The Goldilocks skeleton: one proposer per slot, polling disabled, the two
placeholder committee kinds at phases 1 and 2, every key in each. -/
def goldilocksSkeleton (n : Nat) : Skeleton n where
  grid := goldilocksGrid
  proposerSel := .sized 1
  pollSel := .fixed ∅
  Kind := GKind
  decKind := inferInstance
  kinds := [.head, .fin]
  kinds_nodup := by decide
  kinds_complete := fun k => by cases k <;> simp
  phase := fun | .head => 1 | .fin => 2
  kindSel := fun _ => .all

/-- The interim Goldilocks contract (index: the recurrence gap `k : ℕ+`):
numbers `P`, one honest proposer per window of `k` slots for the available and
stable outputs, the finality pattern per window of `k` slots for the final
output. -/
def goldilocksContract (P : Params ℕ+) (finPattern : Pattern) :
    Contract goldilocksSchema ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  params := P
  progress
    | .final, k => .recur ⟨finPattern, k⟩
    | _, k => .recur ⟨Pattern.single, k⟩

/-- The Goldilocks progress fits every family with one proposer per slot. -/
theorem goldilocksContract_progressFits {Info : Type} [DecidableEq Info] [Encodable Info]
    (P : Params ℕ+) (finPattern : Pattern) (F : ShapeFamily goldilocksSchema Info)
    (hsel : ∀ pub, (F pub).skel.proposerSel = .sized 1) :
    (goldilocksContract P finPattern).ProgressFits F := by
  intro cap k pub
  cases cap <;> exact hsel pub

end Consensus.Shape

end
