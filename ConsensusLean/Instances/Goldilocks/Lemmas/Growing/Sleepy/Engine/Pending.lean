module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Interface
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing

public section

/-! # Pending interface of the sleepy engine transport

Statements the engine transport consumes whose home modules are not on this branch yet, under
their final names, so that the engine proofs compose against the final interface:

* the canonical growing trace simulates the engine (`Simulation.simTraceAt_simulates`), hence is
  a growing-fault run (`Simulation.simTraceAt_goldilocksRun`), home `Lemmas/Growing/Simulation/Run`;
* the finite sleepy service from raw synchrony through `b`
  (`Simulation.sleepyServiceBefore_of_syncUntil_at`, home `Lemmas/Growing/Simulation/Service`);
* ready-reader safety under growing faults (`Regimes.Growing.ReadySafeOn`) and the finite node
  safety `Regimes.Growing.sleepy_safe_at` (home `Lemmas/Growing/Sleepy/Node/Regimes`);
* the finite node inclusion `Regimes.Growing.include_sleepy_at` (home
  `Lemmas/Growing/Sleepy/Service/Inclusion`).

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The canonical growing trace of a valid engine run simulates it, with the cut map `cutMap`. -/
theorem simTraceAt_simulates (hv : rho.ExecutionValid) :
    SimulatesAt S rho hn (simTraceAt S rho hn) (cutMap S rho hn) := by
  sorry

/-- The canonical growing trace of a valid engine run is a growing-fault Goldilocks run for the
time-indexed honest keys. -/
theorem simTraceAt_goldilocksRun (hv : rho.ExecutionValid) :
    Consensus.Goldilocks.Growing.GoldilocksRun (runProposer S rho hn) (digestOf S rho)
      (honestKeysAt S rho) (simTraceAt S rho hn) :=
  (simTraceAt_simulates S rho hn hv).run

/-- **The finite sleepy service under growing faults** from raw synchrony through its deadline
bound `b ≤ horizon`: senders honest at their sends, recipients honest at their reading calls
(the growing-fault `sleepyServiceBefore_of_syncUntil`). -/
theorem sleepyServiceBefore_of_syncUntil_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {b : Time} (hbh : b ≤ rho.horizon) (hnet : rho.log.SyncUntil rho.point b) :
    Compose.Growing.SleepyServiceBefore (simTraceAt S rho hn) (honestKeysAt S rho)
      (S.params (pubOf E) hn).Δ b := by
  sorry

end Consensus.Goldilocks.Simulation

namespace Consensus.Goldilocks.Regimes.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- Ready-reader safety of the confirmed output under growing faults, at the read points of
times in `[t₀, t₁]` between the reader's events: each reader is ready at its read time (honest
then, with every earlier cut at a time `≤ t`), and ancestry is read inside the blocks held while
honest. -/
structure ReadySafeOn (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (c t₀ t₁ : Time) : Prop where
  /-- Agreement of the reads of two ready nodes. -/
  agree : ∀ y z i j t t', ReadPoint tr i t → ReadPoint tr j t' → Boundary tr y i →
    Boundary tr z j → t₀ ≤ t → t ≤ t₁ → t₀ ≤ t' → t' ≤ t₁ → ReadyAt tr H c y t →
    ReadyAt tr H c z t' →
    Compatible (tr.HonestBlocksAt H) (readAfter tr y i t) (readAfter tr z j t')
  /-- Monotonicity of a ready node's reads. -/
  mono : ∀ y i j t t', ReadPoint tr i t → ReadPoint tr j t' → Boundary tr y i →
    Boundary tr y j → i ≤ j → t ≤ t' → t₀ ≤ t → t' ≤ t₁ → ReadyAt tr H c y t →
    ReadyAt tr H c y t' →
    Anc (tr.HonestBlocksAt H) (readAfter tr y i t) (readAfter tr y j t')

/-- **Finite ready-reader safety under growing faults** through `b`, from the finite service and
the two count shapes through `b`. -/
theorem sleepy_safe_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {ΔF b : Time} (hb : 0 ≤ b)
    (hsync : Compose.Growing.SleepyServiceBefore tr H ΔF b)
    (hB : Compose.Growing.SleepyBounds tr H b) :
    ReadySafeOn tr H (catchUp sp) 0 b := by
  sorry

/-- **Finite inclusion under growing faults**: a proposal released at `τ` by a proposer ready at
`τ` and honest through its hold is in the read of every node ready at `t ∈ [τ + 6Δ, b]`. -/
theorem include_sleepy_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {ΔF b : Time} (hb0 : 0 ≤ b)
    (hsync : Compose.Growing.SleepyServiceBefore tr H ΔF b)
    (hB : Compose.Growing.SleepyBounds tr H b) {τ : Time} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposalAt tr H (catchUp sp) τ (hold sp) P) {y : Fin sp.n} {t : Time} {j : Nat}
    (hmargin : τ + 6 * sp.Δ ≤ t) (htb : t ≤ b) (hy : ReadyAt tr H (catchUp sp) y t)
    (hj : CutAfter tr j t) :
    Anc (tr.HonestBlocksAt H) P (readAfter tr y j t) := by
  sorry

end Consensus.Goldilocks.Regimes.Growing

end
