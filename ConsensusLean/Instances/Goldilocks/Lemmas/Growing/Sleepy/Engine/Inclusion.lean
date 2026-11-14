module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Reads
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Inclusion

public section

/-! # Finite sleepy inclusion of the engine under growing faults

`sleepy_include_finite_at`: a proposal released at `τ` by a proposer ready at `τ` and honest
through its hold `Δ` is in the read of every node ready at `t ∈ [τ + 6Δ, b]`. It is the static
finite consumer without a constant-fault premise: the proposer and the readers are honest at
their own times. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation
open Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- **Finite inclusion under growing faults.** Through `b ≥ 0`, under the finite service, the
two count shapes and the committee premises of a slot dictionary `K`, a proposal released at `τ`
by a proposer ready at `τ` and honest through its hold is in the confirmed read of every node
ready at `t ∈ [τ + 6Δ, b]`, after all events at `t`. -/
theorem sleepy_include_finite_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn)) {b : Time} (hb0 : 0 ≤ b)
    (hsync : Compose.Growing.SleepyServiceBefore (simTraceAt S rho hn) (honestKeysAt S rho)
      (S.params (pubOf E) hn).Δ b)
    (hB : Compose.Growing.SleepyBoundsFrom (simTraceAt S rho hn) (honestKeysAt S rho) 0 b)
    {τ t : Time} {P : SA.Blk (Fintype.card V) (List (FG.Att (Fintype.card V)))}
    (hP : Regimes.Growing.ReadyProposalAt (simTraceAt S rho hn) (honestKeysAt S rho)
      (Regimes.catchUp (S.params (pubOf E) hn)) τ (Regimes.Growing.hold (S.params (pubOf E) hn))
      P)
    (hmargin : τ + 6 * (S.params (pubOf E) hn).Δ ≤ t) (htb : t ≤ b)
    {y : Fin (Fintype.card V)} {j : Nat}
    (hy : Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho)
      (Regimes.catchUp (S.params (pubOf E) hn)) y t)
    (hj : Regimes.CutAfter (simTraceAt S rho hn) j t) {K : SA.CommitteeDict (Fintype.card V)}
    (hKB : Compose.Growing.CommitteeFacts (simTraceAt S rho hn) (honestKeysAt S rho) K)
    (hBK : Compose.Growing.CommitteeBoundsFrom (simTraceAt S rho hn) (honestKeysAt S rho) K 0 b) :
    Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho)) P
      (Regimes.readAfter (simTraceAt S rho hn) y j t) :=
  Regimes.Growing.include_sleepy_at (simTraceAt_goldilocksRun S rho hn hv) hnc hb0 hsync hB hP
    hmargin htb hy hj hKB hBK

end Consensus.Goldilocks.Obligations.Growing

end
