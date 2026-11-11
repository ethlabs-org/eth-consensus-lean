module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ProgressBudget
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.CorrectnessEdges

public section

/-! # Open progress-budget consumer edges

These implication definitions supply no evidence. The existing constant-frame final-cache
edge is usable only when an independent FrameWindow witness is explicitly supplied.
-/

set_option autoImplicit false

namespace Consensus.Goldilocks.Generic

open Shape Blocks

variable {P : Params} {A : NodeAC P} {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}

/-- UNPROVED specialization of the healing-gap law at the advertised recurrence.
Only the consuming interval's ready and report-deadline bounds are required. -/
def reset_progress_of_single (M : RunMap rho payload) (K : Contract ProgressReq)
    (healing : ACHealing A M.signer) : Prop :=
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
  ∀ g ΔF query deadline (W : FinalProductionWindow M C.catchUp C.hold query deadline)
    floor kindJ J,
    FrameWindow M.trace M.honest (P.slotTime W.start) deadline floor kindJ J →
    A.Requirements → (P.genesisBlock A.genesisPayload).RootOk M.digest →
    C.healing.Run M.proposer M.digest M.honest M.trace →
    Premises M.trace M.honest M.proposer M.digest M.signer g ΔF deadline →
    HealedFrom M.trace M.honest M.proposer W.start deadline →
    (∀ a, M.trace.AcceptAt (W.block a).proposer (W.cut a) (W.block a)) →
    (∀ a b, a ≤ b → Anc (M.trace.HonestBlocksAt M.honest) (W.block a) (W.block b)) →
    (∀ a : Fin 3, ∃ z i j, z ∈ M.honest (M.trace.time i) ∧ z ∈ M.honest (M.trace.time j) ∧
      W.block a.castSucc ∈ (M.trace.state z i).fg.tree ∧
      W.block a.succ ∈ (M.trace.state z j).fg.tree ∧
      ((M.trace.state z i).fg.σ (W.block a.castSucc).root).h + 1 ≤
        ((M.trace.state z j).fg.σ (W.block a.succ).root).h) →
    ∀ y j, deadline ≤ M.trace.time j →
      ReadyCut M.trace M.honest C.catchUp y j →
      (M.honest (M.trace.time j))ᶜ.ncard < 2 * P.q - P.n →
      (∃ k < j, M.trace.BlockCallAt y k (W.block 3)) →
      Anc (M.trace.HonestBlocksAt M.honest) (W.block 0) (M.trace.finalizedAt y j)

end Consensus.Goldilocks.Generic

end
