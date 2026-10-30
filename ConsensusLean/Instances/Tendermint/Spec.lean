module
public import ConsensusLean.Instances.Bft.Spec
public import Mathlib.Tactic

@[expose] public section

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public SelSpec pubOf)

/-! ## Tendermint -/

/-- The Tendermint skeleton (the grid is unused). -/
def tendermintSkeleton (n : Nat) : Skeleton n where
  grid := ⟨1⟩
  proposerSel := .fixed ∅
  pollSel := .fixed Finset.univ
  Kind := Empty
  decKind := inferInstance
  kinds := []
  phase := fun k => nomatch k
  kindSel := fun k => nomatch k

/-- Tendermint progress: at most `m` validators not ready. -/
def tendermintProg : Capability → ℕ+ → ProgressReq := fun _ m => .notReadyAtMost m

/-- The Tendermint contract. -/
abbrev tendermintContract : Nat → Affine → Affine → Contract ProgressReq :=
  bftContract tendermintProg

/-- The Tendermint progress fits every family (no slot proposers needed). -/
theorem tendermintContract_progressFits {Info : Type} [DecidableEq Info] [Countable Info]
    (catchUp : Nat) (heal latency : Affine) (F : ShapeFamily bftCore Info) :
    ProgressFits (tendermintContract catchUp heal latency) F :=
  fun _ _ _ => trivial

/-- Every provided output tolerates any number of validators not ready. The
bound is not slot-based: its tolerant indices (`m ≥ n`) hold on every point,
whoever leads, so the bad-proposer tolerance asks nothing more. -/
theorem tendermintContract_progressTolerant (catchUp : Nat) (heal latency : Affine) :
    ProgressTolerant bftCore (tendermintContract catchUp heal latency) := by
  intro cap ho N
  exact ⟨⟨N + 1, by omega⟩, Nat.le_succ N⟩

end Consensus.Shape

end
