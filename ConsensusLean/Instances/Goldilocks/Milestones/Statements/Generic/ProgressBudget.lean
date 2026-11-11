module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.EngineTransport

@[expose] public section

/-! # Progress budgets and actual final-production interfaces

These are open supplier contracts, not proofs. Every advertised progress form is retained.
The narrow single-pattern healing transport is unchanged. No constant FrameWindow is produced:
the concrete final-window source instead uses reset and shared healing premises.
-/

set_option autoImplicit false

namespace Consensus.Goldilocks.Generic

open Shape Blocks
open SA (gbar)
open Healing (cutZ)

variable {P : Params} {A : NodeAC P} {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}

/-- A real reset-consuming slot window, including its report deadline and post-reset drain.
The gap is positive and the entire budget is inside the advertised healing time. -/
structure ResetBudgetWindow {sg : A.Msg → Fin P.n} (healing : ACHealing A sg)
    (g ready healed : Time) where
  start : Nat
  gap : Nat
  gap_pos : 1 ≤ gap
  ready_le : ready ≤ P.slotTime start
  gst_le : gbar g ≤ P.slotTime start
  snapshot_le : cutZ P g ≤ P.slotTime start
  deadline_le : P.slotTime (start + resetSlots healing.warmup gap P.δt) + 2 * P.Δ ≤ healed
  drain_le : ∀ a, a ≤ P.slotTime (start + resetSlots healing.warmup gap P.δt) →
    P.slotTime (P.slotOf a + healing.drain) ≤ healed

/-- The explicit four-delay grid and sufficient coefficient budget. This definition supplies
no slot alignment or budget witness. The ready/snapshot reserve remains visible. -/
def ResetCoefficientFit {sg : A.Msg → Fin P.n} (healing : ACHealing A sg)
    (g ready : Time) (healCoeff G : Nat) : Prop :=
  (∀ s, P.slotTime s = (s : Time) * (4 * P.Δ)) ∧ 1 ≤ G ∧
    max ready (max (gbar g) (cutZ P g)) +
      (4 * (resetSlots healing.warmup G P.δt + healing.drain + 2) + 2 : Nat) * P.Δ ≤
      gbar g + (healCoeff : Time) * P.Δ

/-- UNPROVED arithmetic interface from grid/coefficient fit to a real consuming window.
No progress or protocol witness is assumed by the numerical premise. -/
def reset_window_of_coefficients {sg : A.Msg → Fin P.n} (healing : ACHealing A sg) : Prop :=
  ∀ g ready healCoeff G, ResetCoefficientFit healing g ready healCoeff G →
    ∃ W : ResetBudgetWindow healing g ready (gbar g + (healCoeff : Time) * P.Δ), W.gap = G

/-- UNPROVED advertised-coefficient fit, for all nonfinal indices and progress forms.
The chosen gap is data in the conclusion, not an unsupported progress-form exclusion. -/
def ContractResetFit (M : RunMap rho payload) (K : Contract ProgressReq)
    (healing : ACHealing A M.signer) : Prop :=
  ∀ cap idx g, (cap = .available ∨ cap = .stable) →
    ∃ G, ResetCoefficientFit healing g ((Sys F V).ready K g ⟨E, rho⟩)
      (K.params.heal cap idx) G

/-- All-form reset production: no recurrence shape or not-ready form is silently dropped.
This is an open supplier obligation, not evidence that arbitrary contracts meet its budget. -/
def ResetProgressSupply (M : RunMap rho payload) (K : Contract ProgressReq)
    (healing : ACHealing A M.signer) : Prop :=
  rho.ExecutionValid → ∀ cap idx g,
    (cap = .available ∨ cap = .stable) →
    (Sys F V).Healthy K g ⟨E, rho⟩ →
    (Sys F V).prog (shapeProgress F V) K cap idx ((Sys F V).ready K g ⟨E, rho⟩)
      ((Sys F V).heal K cap idx g ⟨E, rho⟩) ⟨E, rho⟩ →
    (Sys F V).heal K cap idx g ⟨E, rho⟩ ≤ rho.horizon →
    ∃ W : ResetBudgetWindow healing g ((Sys F V).ready K g ⟨E, rho⟩)
        ((Sys F V).heal K cap idx g ⟨E, rho⟩),
      ProposalGap M.trace M.honest M.proposer W.gap W.start
        (W.start + resetSlots healing.warmup W.gap P.δt)

/-- An actual nonfinal proposal with publication slack, for every progress form advertised
by the fixed contract, including notReadyAtMost and nonsingle recurrence patterns. -/
def ProposalBudgetSupply (M : RunMap rho payload) (K : Contract ProgressReq)
    (catchUp hold margin : Time) : Prop :=
  rho.ExecutionValid → ∀ cap idx g t,
    (cap = .available ∨ cap = .stable) → (Sys F V).Healthy K g ⟨E, rho⟩ →
    (Sys F V).prog (shapeProgress F V) K cap idx ((Sys F V).ready K g ⟨E, rho⟩)
      rho.horizon ⟨E, rho⟩ →
    (Sys F V).heal K cap idx g ⟨E, rho⟩ ≤ t →
    t + (K.params.latency cap idx : Time) * E.ΔAC ≤ rho.horizon →
    (∃ v, rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v
      (t + (K.params.latency cap idx : Time) * E.ΔAC)) →
    ∃ B k, t < M.trace.time k ∧ ReadyProposal M.trace M.honest catchUp hold B k ∧
      M.trace.time k + margin ≤ t + (K.params.latency cap idx : Time) * E.ΔAC

/-- Sleepy counterpart of the all-form proposal supplier, retaining reader-conditionality. -/
def SleepyProposalBudgetSupply (M : RunMap rho payload) (K : Contract ProgressReq)
    (catchUp hold margin : Time) : Prop :=
  rho.ExecutionValid → ∀ cap idx t,
    (cap = .available ∨ cap = .stable) → (Sys F V).Sleepy K ⟨E, rho⟩ →
    (Sys F V).prog (shapeProgress F V) K cap idx 0 rho.horizon ⟨E, rho⟩ →
    0 ≤ t → t + (K.params.latency cap idx : Time) * E.ΔAC ≤ rho.horizon →
    (∃ v, rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v
      (t + (K.params.latency cap idx : Time) * E.ΔAC)) →
    ∃ B k, t < M.trace.time k ∧ ReadyProposal M.trace M.honest catchUp hold B k ∧
      M.trace.time k + margin ≤ t + (K.params.latency cap idx : Time) * E.ΔAC

/-- Four actual anchors with exact spacing and final publication slack. No constant-frame
premise is hidden in this data. Acceptance/height/processing are separate open suppliers. -/
structure FinalProductionWindow (M : RunMap rho payload) (catchUp hold : Time)
    (query deadline : Time) where
  start : Nat
  gap : Nat
  gap_two : 2 ≤ gap
  gap_span : 3 * gap ≤ P.δt
  block : Fin 4 → A.Blk
  cut : Fin 4 → Nat
  slots : ∀ a, (block a).slot = start + a.val * gap
  proposals : ∀ a, M.trace.ProposesAt (block a).proposer (cut a) (block a)
  ready : ∀ a, ReadyCut M.trace M.honest catchUp (block a).proposer (cut a)
  honest_hold : ∀ a, (block a).proposer ∈ M.honest (M.trace.time (cut a) + hold)
  fresh : query < M.trace.time (cut 0)
  ordered : StrictMono cut
  bounded : ∀ a, M.trace.time (cut a) ≤ deadline
  publication : M.trace.time (cut 3) + P.Δ ≤ deadline

/-- All-form final production from the advertised final progress and latency. A single
proposal or a conditional four-anchor edge is not a supplier of this existential. -/
def FinalWindowSupply (M : RunMap rho payload) (K : Contract ProgressReq)
    (healing : ACHealing A M.signer) (catchUp hold : Time) : Prop :=
  rho.ExecutionValid → ∀ idx g t,
    (Sys F V).Healthy K g ⟨E, rho⟩ →
    (Sys F V).prog (shapeProgress F V) K .final idx ((Sys F V).ready K g ⟨E, rho⟩)
      rho.horizon ⟨E, rho⟩ →
    (Sys F V).heal K .final idx g ⟨E, rho⟩ ≤ t →
    t + (K.params.latency .final idx : Time) * E.ΔAC ≤ rho.horizon →
    (∃ v, rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v
      (t + (K.params.latency .final idx : Time) * E.ΔAC)) →
    ∃ W : FinalProductionWindow M catchUp hold t
        (t + (K.params.latency .final idx : Time) * E.ΔAC),
      HealedFrom M.trace M.honest M.proposer W.start
        (t + (K.params.latency .final idx : Time) * E.ΔAC) ∧
      healing.Run M.proposer M.digest M.honest M.trace

/-- Actual acceptance, chaining and three own-reader height increases for the same anchors.
The supplying protocol must justify these directly; FrameWindow is not manufactured. -/
def FinalHeightSupply (M : RunMap rho payload) (healing : ACHealing A M.signer)
    (catchUp hold : Time) : Prop :=
  ∀ g ΔF query deadline (W : FinalProductionWindow M catchUp hold query deadline),
    healing.Run M.proposer M.digest M.honest M.trace →
    Premises M.trace M.honest M.proposer M.digest M.signer g ΔF deadline →
    HealedFrom M.trace M.honest M.proposer W.start deadline →
    (∀ a, M.trace.AcceptAt (W.block a).proposer (W.cut a) (W.block a)) ∧
    (∀ a b, a ≤ b → Anc (M.trace.HonestBlocksAt M.honest) (W.block a) (W.block b)) ∧
    ∀ a : Fin 3, ∃ z i j, z ∈ M.honest (M.trace.time i) ∧ z ∈ M.honest (M.trace.time j) ∧
      W.block a.castSucc ∈ (M.trace.state z i).fg.tree ∧
      W.block a.succ ∈ (M.trace.state z j).fg.tree ∧
      ((M.trace.state z i).fg.σ (W.block a.castSucc).root).h + 1 ≤
        ((M.trace.state z j).fg.σ (W.block a.succ).root).h

/-- The last actual anchor is processed before each consuming ready cut. The witness uses
the existing CarrierProcessed type, including strict event order and own-event honesty. -/
def FinalCarrierSupply (M : RunMap rho payload) (catchUp hold : Time) : Prop :=
  ∀ query deadline (W : FinalProductionWindow M catchUp hold query deadline) y j,
    deadline ≤ M.trace.time j → M.trace.time j ≤ rho.horizon →
    ReadyCut M.trace M.honest catchUp y j →
    CarrierProcessed M (W.block 3) y j (M.trace.time (W.cut 3)) deadline

/-- Direct cache-production interface without an unsupported constant-frame supplier.
Actual anchor acceptance, ancestry, heights and carrier processing stay explicit inputs. -/
def FinalCacheSupply (M : RunMap rho payload) (healing : ACHealing A M.signer)
    (catchUp hold : Time) : Prop :=
  ∀ g ΔF query deadline (W : FinalProductionWindow M catchUp hold query deadline),
    A.Requirements → (P.genesisBlock A.genesisPayload).RootOk M.digest →
    healing.Run M.proposer M.digest M.honest M.trace →
    Premises M.trace M.honest M.proposer M.digest M.signer g ΔF deadline →
    HealedFrom M.trace M.honest M.proposer W.start deadline →
    (∀ a, M.trace.AcceptAt (W.block a).proposer (W.cut a) (W.block a)) →
    (∀ a b, a ≤ b → Anc (M.trace.HonestBlocksAt M.honest) (W.block a) (W.block b)) →
    (∀ a : Fin 3, ∃ z i j, z ∈ M.honest (M.trace.time i) ∧ z ∈ M.honest (M.trace.time j) ∧
      W.block a.castSucc ∈ (M.trace.state z i).fg.tree ∧
      W.block a.succ ∈ (M.trace.state z j).fg.tree ∧
      ((M.trace.state z i).fg.σ (W.block a.castSucc).root).h + 1 ≤
        ((M.trace.state z j).fg.σ (W.block a.succ).root).h) →
    ∀ y j, deadline ≤ M.trace.time j → M.trace.time j ≤ rho.horizon →
      ReadyCut M.trace M.honest catchUp y j →
      (M.honest (M.trace.time j))ᶜ.ncard < 2 * P.q - P.n →
      CarrierProcessed M (W.block 3) y j (M.trace.time (W.cut 3)) deadline →
      Anc (M.trace.HonestBlocksAt M.honest) (W.block 0) (M.trace.finalizedAt y j)

end Consensus.Goldilocks.Generic

end
