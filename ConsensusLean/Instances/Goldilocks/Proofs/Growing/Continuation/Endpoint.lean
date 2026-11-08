module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Continuation
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
import ConsensusLean.Instances.Goldilocks.Proofs.Growing.Obligations.Main
import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Handover
import ConsensusLean.Lemmas.Problem.Facts.CorrectProtocol
import ConsensusLean.Lemmas.Problem.Facts.Network

public section

/-! # The continuation claims from correctness: past the horizon, and up to the hand-over

Two parts of the continuation claims follow from Goldilocks correctness (`goldilocks_correct`)
alone, without the seeded label induction.

* **Past the horizon.** A hand-over at or after the horizon is the healthy regime
  (`Handover.healthy`: faults only grow, and full participation on `[max g 0, T]` covers
  `[max g 0, horizon]`). Then `healedSafe` gives the `continuedSafe` conclusion, with progress on
  `[ready, heal]`, and `healthyLive` the `continuedLive` conclusion, with progress on
  `[ready, horizon]`: `continued_safe_past_horizon`, `continued_live_past_horizon`.
* **Liveness deadlines up to the hand-over.** For `T ≤ horizon` the run is healthy on the prefix
  through `T`: partial synchrony up to the horizon gives delivery up to `T`, the health and the FG
  delay bound are the hand-over's, and progress on `[ready, horizon]` restricts to
  `[ready, T]`. `healthyLive_prefix` at `b := T` gives the `TxLive` conclusion for every
  deadline `t' ≤ T`: `continued_live_upTo_handover`. -/

namespace Consensus.Goldilocks

open AsChainShape
open Blocks Shape

/-- **`continuedSafe` past the horizon**: on a hand-over run with `horizon ≤ T`, ready-reader
safety from the heal point (`healedSafe` of the healthy regime, `Handover.healthy`). -/
theorem continued_safe_past_horizon (S : Setup) (A : ContractAssumptions S)
    (V : Type) [Fintype V] [DecidableEq V] :
    let Sy := Model.sysOf schema (compiled (goldilocks S)) V
    let K := goldilocksContract A (contract_coefficients S A)
    ∀ cap g, (cap = .available ∨ cap = .stable) → Sy.schema.output cap = some g →
      ∀ i gst T r, Sy.Valid r → Sy.Handover K gst T r → (Sy.pt r).horizon ≤ T →
        Sy.prog (shapeProgress (goldilocks S) V) K cap i (Sy.ready K gst r)
          (Sy.heal K cap i gst r) r →
        (Sy.trace r).ReadySafe (Sy.cDur K r) g (Sy.heal K cap i gst r) ∨ Sy.Excuse r := by
  intro Sy K cap g hcap hg i gst T r hv hh hT hp
  exact (Growing.goldilocks_correct S A V).behaviour.healedSafe cap g hcap hg i gst r hv
    ⟨hh.healthy hT, hp⟩

/-- **`continuedLive` past the horizon**: on a hand-over run with `horizon ≤ T`, transaction
liveness from the heal point (`healthyLive` of the healthy regime, `Handover.healthy`). -/
theorem continued_live_past_horizon (S : Setup) (A : ContractAssumptions S)
    (V : Type) [Fintype V] [DecidableEq V] :
    let Sy := Model.sysOf schema (compiled (goldilocks S)) V
    let K := goldilocksContract A (contract_coefficients S A)
    ∀ cap g, Sy.schema.output cap = some g →
      ∀ i gst T r, Sy.Valid r → Sy.Handover K gst T r → (Sy.pt r).horizon ≤ T →
        Sy.prog (shapeProgress (goldilocks S) V) K cap i (Sy.ready K gst r) (Sy.pt r).horizon r →
        (Sy.trace r).TxLive (Sy.cDur K r) g (Sy.heal K cap i gst r) (Sy.lat K cap i r) ∨
          Sy.Excuse r := by
  intro Sy K cap g hg i gst T r hv hh hT hp
  exact (Growing.goldilocks_correct S A V).behaviour.healthyLive cap g hg i gst r hv
    ⟨hh.healthy hT, hp⟩

/-- **`TxLive` for the deadlines up to the hand-over**: on a hand-over run with `heal ≤ T ≤
horizon` and progress on `[ready, horizon]`, a transaction submitted at `t` is read by every
ready reader at every deadline `t' ∈ [max t heal + ΔAC + lat, T]`. The prefix through `T` is
healthy: partial synchrony delivers up to `T`, with the hand-over's health and FG delay bound,
and progress restricted to `[ready, T]` (`healthyLive_prefix`). -/
theorem continued_live_upTo_handover (S : Setup) (A : ContractAssumptions S)
    (V : Type) [Fintype V] [DecidableEq V] :
    let Sy := Model.sysOf schema (compiled (goldilocks S)) V
    let K := goldilocksContract A (contract_coefficients S A)
    ∀ cap g, Sy.schema.output cap = some g →
      ∀ i gst T r, Sy.Valid r → Sy.Handover K gst T r → T ≤ (Sy.pt r).horizon →
        Sy.heal K cap i gst r ≤ T →
        Sy.prog (shapeProgress (goldilocks S) V) K cap i (Sy.ready K gst r) (Sy.pt r).horizon r →
        (∀ x t t', (Sy.pt r).SubmittedToSome x t →
          max t (Sy.heal K cap i gst r) + (Sy.pt r).env.ΔAC + Sy.lat K cap i r ≤ t' → t' ≤ T →
          ∀ v, (Sy.pt r).Ready (Sy.cDur K r) v t' → x ∈ (Sy.trace r).readAt g v t') ∨
          Sy.Excuse r := by
  intro Sy K cap g hg i gst T r hv hh hTh hhT hp
  have h0 : 0 ≤ Sy.heal K cap i gst r :=
    add_nonneg (le_max_right gst 0) (mul_nonneg (Nat.cast_nonneg _) (Sy.pt r).env.ΔAC_pos.le)
  exact (Growing.goldilocks_correct S A V).healthyLive_prefix hg r hv i gst (h0.trans hhT) hTh
    (CommLog.Delivers.reindex (f := id) hh.1 (fun _ => le_rfl) (fun _ => rfl) (fun _ => rfl) hTh)
    hh.2.1 hh.2.2.1 ((shapeProgress (goldilocks S) V).mono le_rfl hTh hp)

end Consensus.Goldilocks

end
