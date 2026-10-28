module
public import ConsensusShape.Values.Common

@[expose] public section

/-! # Tendermint as a value (D-16, decision T)

A poll shape: no slot proposals (`proposerSel := .fixed ∅`) and no committee
kinds; every key may sign in the poll role (`pollSel := .all`). Proposals come
from the poll proposal duty (height in `pos`, round in `info`) and votes from
the poll message duty, both at every unit tick; the round-robin leader of a
round is computed locally from the own key and the public `Fin n`. Unit ticks,
no responsiveness claim.

Contract (index: a bound `m : ℕ+` on the validators that are not ready):
standard thresholds (the final output is accountable for a third in every
environment), the readers' catch-up `catchUp`; final liveness in the healthy
regime from a GST, from the heal point `max g 0 + (catchUp + 1 + heal m)·Δ`,
with at most `m` validators not ready from `readyFrom` on
(`ProgressReq.notReadyAtMost m`, which also requires `m` below the validator
count), and latency `latency m` (`Δ`-coefficients, affine in `m`). The bound
is pointwise: the non-ready validators may change over time, so it does not by
itself put a ready honest leader within `m + 1` rounds (an adversarial
schedule can sleep exactly the current leader through each round). A concrete
Tendermint liveness proof needs a temporal leader-opportunity argument or a
revised progress requirement; this contract is a placeholder for that work.
A locked value is re-proposed by carrying its original signed header: the
engine writes the payload of every new header. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public SelSpec pubOf)

/-- The Tendermint skeleton (the grid is unused). -/
def tendermintSkeleton (n : Nat) : Skeleton n where
  grid := ⟨1, by decide⟩
  proposerSel := .fixed ∅
  pollSel := .all
  Kind := Empty
  decKind := inferInstance
  kinds := []
  kinds_nodup := List.nodup_nil
  kinds_complete := fun k => nomatch k
  phase := fun k => nomatch k
  kindSel := fun k => nomatch k

/-- The Tendermint contract, with the readers' catch-up, the heal point after
the catch-up and the latency (affine in the not-ready bound) as parameters. -/
def tendermintContract (catchUp : Nat) (heal latency : Affine) :
    Contract bftCore ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  params := Params.standard catchUp 0 1 (fun _ m => catchUp + 1 + heal.eval m)
    (fun _ m => latency.eval m)
  progress _ m := .notReadyAtMost m

/-- The Tendermint numbers are admissible for a positive catch-up. -/
theorem tendermintContract_admissible {catchUp : Nat} (h : 1 ≤ catchUp)
    (heal latency : Affine) : (tendermintContract catchUp heal latency).params.Admissible :=
  Params.standard_admissible h le_rfl

/-- The Tendermint progress fits every family (no slot proposers needed). -/
theorem tendermintContract_progressFits {Info : Type} [DecidableEq Info] [Encodable Info]
    (catchUp : Nat) (heal latency : Affine) (F : ShapeFamily bftCore Info) :
    (tendermintContract catchUp heal latency).ProgressFits F :=
  fun _ _ _ => trivial

end Consensus.Shape

end
