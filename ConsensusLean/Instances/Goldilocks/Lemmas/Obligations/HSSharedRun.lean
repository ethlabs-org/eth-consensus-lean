module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NetworkTransport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeMature
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunBlocks
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Obligations: the protocol FG delay of a healthy run

`protoFGDelay_pos`, and `protoFGDelay_delivery_of_fgDelay`, `protoFGDelay_timeout_of_fgDelay`: the
FG delay bound of `K S A` (a conjunct of its healthy regime) bounds the engine FG delay by the
contract's bound (`ΔFG ≤ (4·fgSlots − 6)·ΔAC`), so the protocol FG delay
`Δ_F,p = protoFGDelay (pubOf E)` satisfies `6Δ_p + Δ_F,p ≤ 4Δ_p·fgSlots ≤ 4Δ_p·δ_t`
(`fgDelay_bound_iff`, `3·fgSlots ≤ δ_t`). No order between `Δ` and `Δ_F` is used. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Shape Blocks

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The protocol FG delay is positive. -/
theorem protoFGDelay_pos (pub : Model.Public) : 0 < protoFGDelay pub := by
  rw [protoFGDelay_eq]
  exact pub.ΔFG_pos

/-- **The FG transport under the FG delay bound of `K S A`** (a conjunct of its healthy regime):
the engine FG delay is within the contract's bound, `ΔFG ≤ (4·fgSlots − 6)·ΔAC`, so the protocol
delays satisfy `6Δ_p + Δ_F,p ≤ 4Δ_p·fgSlots` (`fgDelay_bound_iff`), with
`Δ_F,p = protoFGDelay (pubOf E)`. -/
theorem protoFGDelay_delivery_of_fgDelay (run : (Sys (goldilocks S) V).Run)
    (hn : 1 ≤ Fintype.card V)
    (hfg : ((Sys (goldilocks S) V).pt run).env.ΔFG ≤
      ((K S A).params.fgDelay : Time) * ((Sys (goldilocks S) V).pt run).env.ΔAC) :
    6 * (S.params (Model.pubOf run.1) hn).Δ + protoFGDelay (Model.pubOf run.1) ≤
      4 * (S.params (Model.pubOf run.1) hn).Δ * (A.fgSlots : Time) := by
  have h := hfg
  change run.1.ΔFG ≤ ((A.fgDelay : ℕ+) : Time) * run.1.ΔAC at h
  rw [protoFGDelay_eq]
  exact (fgDelay_bound_iff A run.1.ΔAC run.1.ΔFG).1 h

/-- **The rise timeout under the FG delay bound of `K S A`** at the protocol FG delay:
`6Δ_p + Δ_F,p ≤ 4Δ_p·fgSlots ≤ 4Δ_p·δ_t`, from `protoFGDelay_delivery_of_fgDelay` and
`3·fgSlots ≤ δ_t` (`ContractAssumptions.timeout`). -/
theorem protoFGDelay_timeout_of_fgDelay (run : (Sys (goldilocks S) V).Run)
    (hn : 1 ≤ Fintype.card V)
    (hfg : ((Sys (goldilocks S) V).pt run).env.ΔFG ≤
      ((K S A).params.fgDelay : Time) * ((Sys (goldilocks S) V).pt run).env.ΔAC) :
    6 * (S.params (Model.pubOf run.1) hn).Δ + protoFGDelay (Model.pubOf run.1) ≤
      4 * (S.params (Model.pubOf run.1) hn).Δ * (S.δt : Time) := by
  have h := protoFGDelay_delivery_of_fgDelay S A V run hn hfg
  have hΔ := (S.params (Model.pubOf run.1) hn).toParams.hΔ
  have hc : (A.fgSlots : Time) ≤ (S.δt : Time) := by
    have := A.timeout
    exact_mod_cast (show A.fgSlots ≤ S.δt by omega)
  linarith [mul_le_mul_of_nonneg_left hc (mul_nonneg zero_le_four hΔ.le)]

end Consensus.Goldilocks.Obligations

end
