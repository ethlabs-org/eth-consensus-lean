module
public import ConsensusShape.Values.Common

@[expose] public section

/-! # Streamlet as a value (D-16)

Final-only (`bftCore`) on a grid of `2·Δ` slots, one proposer per slot,
polling disabled, one committee kind (votes) at phase 1 signed by every key.

Contract (index: the recurrence gap `k : ℕ+`): standard thresholds (the final
output is accountable for a third in every environment), the readers'
catch-up `catchUp`; final liveness in the healthy regime from a GST, from the
heal point `max g 0 + (catchUp + 1 + heal k)·Δ`, with five consecutive honest
ready proposers (`streamletPattern`) in every window of `k` slots from
`readyFrom`, and latency `latency k` (`Δ`-coefficients). The outage numbers
(lag, budget) are unused: Streamlet provides no stable output. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public SelSpec pubOf)

/-- Slots of `2·Δ`. -/
def streamletGrid : TimeGrid := ⟨2, by decide⟩

/-- The Streamlet skeleton. -/
def streamletSkeleton (n : Nat) : Skeleton n where
  grid := streamletGrid
  proposerSel := .sized 1
  pollSel := .fixed ∅
  Kind := Unit
  decKind := inferInstance
  kinds := [()]
  kinds_nodup := List.nodup_singleton _
  kinds_complete := fun _ => List.mem_singleton_self _
  phase := fun _ => 1
  kindSel := fun _ => .all

/-- Five consecutive honest proposers. -/
def streamletPattern : Pattern := Pattern.range 5

/-- The Streamlet contract, with the readers' catch-up, the heal point after
the catch-up and the latency (affine in the gap) as parameters. -/
def streamletContract (catchUp : Nat) (heal latency : Affine) :
    Contract bftCore ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  params := Params.standard catchUp 0 1 (fun _ k => catchUp + 1 + heal.eval k)
    (fun _ k => latency.eval k)
  progress _ k := .recur ⟨streamletPattern, k⟩

/-- The Streamlet numbers are admissible for a positive catch-up. -/
theorem streamletContract_admissible {catchUp : Nat} (h : 1 ≤ catchUp) (heal latency : Affine) :
    (streamletContract catchUp heal latency).params.Admissible :=
  Params.standard_admissible h le_rfl

/-- The Streamlet progress fits every family with one proposer per slot. -/
theorem streamletContract_progressFits {Info : Type} [DecidableEq Info] [Encodable Info]
    (catchUp : Nat) (heal latency : Affine) (F : ShapeFamily bftCore Info)
    (hsel : ∀ pub, (F pub).skel.proposerSel = .sized 1) :
    (streamletContract catchUp heal latency).ProgressFits F :=
  fun _ _ pub => hsel pub

end Consensus.Shape

end
