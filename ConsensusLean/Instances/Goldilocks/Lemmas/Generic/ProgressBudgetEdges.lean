module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ProgressBudget
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.CorrectnessEdges
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.StatementsBundle
import Mathlib.Tactic.Linarith

public section

/-! # Progress-budget arithmetic and open consumer edges

The coefficient-fit theorem supplies a reset budget window, not a progress witness.
The remaining implication definitions supply no evidence. The constant-frame final-cache
edge is usable only when an independent FrameWindow witness is explicitly supplied.
-/

set_option autoImplicit false

namespace Consensus.Goldilocks.Generic

open Shape Blocks

variable {P : Params} {A : NodeAC P} {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}

/-- The coefficient reserve covers alignment to the next slot, the reset report,
and the drain from every time at or before the reset endpoint. -/
theorem reset_window_of_coefficients_proof {sg : A.Msg → Fin P.n}
    {runs : ACRun A sg} (healing : ACHealing A sg runs) :
    reset_window_of_coefficients healing := by
  intro g ready healCoeff G hfit
  rcases hfit with ⟨hgrid, hG, hbudget⟩
  let m := max ready (max (SA.gbar g) (Healing.cutZ P g))
  have hm : 0 ≤ m := le_trans (le_max_right g 0)
    ((le_max_left (SA.gbar g) (Healing.cutZ P g)).trans (le_max_right ready _))
  obtain ⟨hmlo, hmhi⟩ := slotOfSpec_iff.mp slotOf_spec P m hm
  let start := P.slotOf m + 1
  have hstart : m ≤ P.slotTime start := hmhi.le
  have halign : P.slotTime start ≤ m + 4 * P.Δ := by
    dsimp [start]
    rw [hgrid] at hmlo ⊢
    push_cast
    nlinarith only [hmlo]
  let r := resetSlots healing.warmup G P.δt
  have hD := P.hΔ
  have hdeadline : P.slotTime (start + r) + 2 * P.Δ ≤
      SA.gbar g + (healCoeff : Time) * P.Δ := by
    rw [hgrid] at halign ⊢
    dsimp [r] at *
    nlinarith only [halign, hbudget, hD, (Nat.cast_nonneg healing.drain : (0 : Time) ≤ _)]
  refine ⟨{ start := start
            gap := G
            gap_pos := hG
            ready_le := (le_max_left ready _).trans hstart
            gst_le := ((le_max_left _ _).trans (le_max_right ready _)).trans hstart
            snapshot_le := ((le_max_right _ _).trans (le_max_right ready _)).trans hstart
            deadline_le := hdeadline
            drain_le := ?_ }, rfl⟩
  intro a ha
  have hslot : P.slotOf a ≤ start + r := by
    by_cases ha0 : 0 ≤ a
    · have hlo := (slotOfSpec_iff.mp slotOf_spec P a ha0).1
      exact P.slotTime_strictMono.le_iff_le.mp (hlo.trans ha)
    · have haZ : a ≤ 0 := (lt_of_not_ge ha0).le
      simp [Params.slotOf, Int.toNat_of_nonpos haZ]
  have hslotTime := P.slotTime_strictMono.monotone (Nat.add_le_add_right hslot healing.drain)
  apply hslotTime.trans
  rw [hgrid] at halign ⊢
  dsimp [r] at *
  nlinarith only [halign, hbudget, hD]

/-- UNPROVED specialization of the healing-gap law at the advertised recurrence.
Only the consuming interval's ready and report-deadline bounds are required. -/
def reset_progress_of_single (M : RunMap rho payload) (K : Contract ProgressReq)
    {runs : ACRun A M.signer} (healing : ACHealing A M.signer runs) : Prop :=
  ∀ cap idx g (r : Recurrence),
    K.progress cap idx = .recur r → r.pattern = Pattern.single →
    (∀ a b, (Sys F V).ready K g ⟨E, rho⟩ ≤ P.slotTime a →
      a + resetSlots healing.warmup (r.gap : Nat) P.δt ≤ b + 1 →
      P.slotTime b + 2 * P.Δ ≤ (Sys F V).heal K cap idx g ⟨E, rho⟩ →
      ProposalGap M.trace M.honest M.proposer (r.gap : Nat) a b) →
    ∀ start, (Sys F V).ready K g ⟨E, rho⟩ ≤ P.slotTime start →
      P.slotTime (start + resetSlots healing.warmup (r.gap : Nat) P.δt) + 2 * P.Δ ≤
        (Sys F V).heal K cap idx g ⟨E, rho⟩ →
      ProposalGap M.trace M.honest M.proposer (r.gap : Nat) start
        (start + resetSlots healing.warmup (r.gap : Nat) P.δt)

/-- UNPROVED composition with the old cache edge, keeping its missing constant frame
as an explicit input. This is not a production law for FrameWindow. -/
def final_cache_of_frame (M : RunMap rho payload) (C : ACCorrectLocal A M.signer) : Prop :=
  final_cache_coverage_at A M.signer C →
  ∀ (βK : ℚ) g ΔF query deadline (W : FinalProductionWindow M C.catchUp C.hold query deadline)
    floor kindJ J,
    βK ≤ 1 / 2 →
    FrameWindow M.trace M.honest (P.slotTime W.start) deadline floor kindJ J →
    C.run.Run M.committee M.proposer M.digest M.honest M.trace →
    Premises M.trace M.honest M.committee βK M.proposer M.digest M.signer g ΔF deadline →
    HealedFrom M.trace M.honest M.proposer W.start deadline →
    FinalHeightSupply M C.catchUp C.hold query deadline W →
    ∀ y j, deadline ≤ M.trace.time j →
      ReadyCut M.trace M.honest C.catchUp y j →
      (M.honest (M.trace.time j))ᶜ.ncard < 2 * P.q - P.n →
      (∃ k < j, M.trace.BlockCallAt y k (W.block 3)) →
      Anc (M.trace.HonestBlocksAt M.honest) (W.block 0) (M.trace.finalizedAt y j)

end Consensus.Goldilocks.Generic

end
