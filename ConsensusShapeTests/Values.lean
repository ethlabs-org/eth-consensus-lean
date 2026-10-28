module
public import ConsensusShape
public import Mathlib.Tactic

@[expose] public section

/-! # Streamlet and Tendermint as values (D-16; moved from the library)

Both are final-only (`bftCore`) and share one contract shape, `bftContract`:
index `k : ℕ+`, standard thresholds (the final output is accountable for a
third in every environment), the readers' catch-up `catchUp`, final liveness
in the healthy regime from a GST from the heal point
`max g 0 + (catchUp + 1 + heal k)·Δ` with latency `latency k`
(`Δ`-coefficients, affine in `k`). The outage numbers (lag, budget) are
unused: neither provides a stable output. They differ in the progress
requirement only, and so each has its own fit and tolerance proof: an
arbitrary progress function is neither (the rejecting tests in `Vacuity`).
Values are skeletons and contracts only; they carry no protocol proofs.

**Streamlet.** A grid of `2·Δ` slots, one proposer per slot, polling
disabled, one committee kind (votes) at phase 1 signed by every key. Progress:
five consecutive honest ready proposers (`Pattern.range 5`) in every window of
`k` slots from `readyFrom`.

**Tendermint (decision T).** A poll shape: no slot proposals
(`proposerSel := .fixed ∅`) and no committee kinds; every key may sign in the
poll role (`pollSel := .fixed univ`). Proposals come from the poll proposal duty
(height in `pos`, round in `info`) and votes from the poll message duty, both
at every unit tick; the round-robin leader of a round is computed locally from
the own key and the public `Fin n`. Unit ticks, no responsiveness claim.
Progress: at most `m` validators not ready from `readyFrom` on
(`ProgressReq.notReadyAtMost m`; for `m ≥ card V` it holds trivially and the
reader-conditional liveness owes nothing where nobody is ready). The bound is
pointwise: the non-ready validators may change over time, so it does not by
itself put a ready honest leader within `m + 1` rounds (an adversarial
schedule can sleep exactly the current leader through each round). A concrete
Tendermint liveness proof needs a temporal leader-opportunity argument or a
revised progress requirement; this contract is a placeholder for that work.
A locked value is re-proposed by carrying its original signed header: the
engine writes the payload of every new header. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public SelSpec pubOf)

/-- An affine bound `a + b·k` (a `Δ`-coefficient) in the index `k` (the
recurrence gap in slots, or a fault count). -/
structure Affine where
  a : Nat
  b : Nat

/-- The value of an affine bound at `k`. -/
def Affine.eval (f : Affine) (k : Nat) : Nat := f.a + f.b * k

/-- The final-only schema: one output, serving the final capability. -/
def bftCore : OutputSchema := ⟨Unit, fun | .final => some () | _ => none⟩

/-- The final-only contract with progress `progress`, the readers' catch-up,
the heal point after the catch-up and the latency (affine in the index) as
parameters. -/
def bftContract (progress : Capability → ℕ+ → ProgressReq) (catchUp : Nat)
    (heal latency : Affine) : Contract ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  params := Params.standard catchUp 0 1 (fun _ k => catchUp + 1 + heal.eval k)
    (fun _ k => latency.eval k)
  progress := progress

/-- The numbers of `bftContract` are admissible for a positive catch-up. -/
theorem bftContract_admissible (progress : Capability → ℕ+ → ProgressReq) {catchUp : Nat}
    (h : 1 ≤ catchUp) (heal latency : Affine) :
    (bftContract progress catchUp heal latency).params.Admissible :=
  Params.standard_admissible h le_rfl

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
  kinds_nodup := List.nodup_singleton _
  kinds_complete := fun _ => List.mem_singleton_self _
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

/-- Every provided output tolerates any number of validators not ready. -/
theorem streamletContract_progressTolerant (catchUp : Nat) (heal latency : Affine) :
    ProgressTolerant bftCore (streamletContract catchUp heal latency) :=
  fun _ _ _ => ⟨(1 : ℕ+), trivial⟩

/-! ## Tendermint -/

/-- The Tendermint skeleton (the grid is unused). -/
def tendermintSkeleton (n : Nat) : Skeleton n where
  grid := ⟨1⟩
  proposerSel := .fixed ∅
  pollSel := .fixed Finset.univ
  Kind := Empty
  decKind := inferInstance
  kinds := []
  kinds_nodup := List.nodup_nil
  kinds_complete := fun k => nomatch k
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

/-- Every provided output tolerates any number of validators not ready. -/
theorem tendermintContract_progressTolerant (catchUp : Nat) (heal latency : Affine) :
    ProgressTolerant bftCore (tendermintContract catchUp heal latency) := by
  intro cap ho N
  exact ⟨⟨N + 1, by omega⟩, Nat.le_succ N⟩

end Consensus.Shape

end
