module
public import ConsensusLean.Instances.Bft.Spec
public import Mathlib.Tactic

@[expose] public section

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public SelSpec pubOf)

/-! ## Streamlet -/

/-- Slots of `2·Δ`. -/
def streamletGrid : TimeGrid := ⟨2⟩

/-- The Streamlet skeleton. -/
def streamletSkeleton (n : Nat) : Skeleton n where
  grid := streamletGrid
  proposerSel := .sized 1
  pollSel := .fixed ∅
  Kind := Unit
  decKind := inferInstance
  kinds := [()]
  phase := fun _ => 1
  kindSel := fun _ => .fixed Finset.univ

/-- Streamlet progress: five consecutive honest proposers within every window
of `k` slots. -/
def streamletProg : Capability → ℕ+ → ProgressReq := fun _ k => .recur ⟨Pattern.range 5, k⟩

/-- The Streamlet contract. -/
abbrev streamletContract : Nat → Affine → Affine → Contract ProgressReq :=
  bftContract streamletProg

/-- The Streamlet progress fits every family with one proposer per slot. -/
theorem streamletContract_progressFits {Info : Type} [DecidableEq Info] [Countable Info]
    (catchUp : Nat) (heal latency : Affine) (F : ShapeFamily bftCore Info)
    (hsel : ∀ pub, (F pub).skel.proposerSel = .sized 1) :
    ProgressFits (streamletContract catchUp heal latency) F :=
  fun _ _ pub => hsel pub

/-- Every provided output tolerates any number of validators not ready and a
bad proposer slot in every window: at gap `6`, five consecutive proposers
(span `4`) leave room for one bad slot. -/
theorem streamletContract_progressTolerant (catchUp : Nat) (heal latency : Affine) :
    ProgressTolerant bftCore (streamletContract catchUp heal latency) :=
  fun _ _ _ => ⟨(6 : ℕ+), show (⟨Pattern.range 5, 6⟩ : Recurrence).BadSlotSlack by decide⟩

end Consensus.Shape

end
