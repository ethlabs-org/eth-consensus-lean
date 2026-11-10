module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinalWindowDefs
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Obligations: the seed slot, grid and latency of a final query

The least seed slot `finalSeedMin` of a reset, the grid `finalGrid` of the run's family with its
slot times, the span `3c` of the final pattern `[0, c, 2c, 3c]` and the final latency budget at
the FG gap. They read the query only, not its window, and are the base of the final window
assembly (`FinalWindowAssembly`). -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The least seed slot of a reset at `a`: past the drain, `slot(a) + 2k + 5`. A slot count only:
`ḡ + 4Δ ≤ t_u` is not part of it, the assembly reads it off the first query, which is
strictly after `ready ≥ ḡ + 18Δ + 1`. -/
noncomputable abbrev finalSeedMin (Q : FinalQuery S A V) (a : Time) : Nat :=
  Q.params.slot a + 2 * Q.params.k + 5

/-- The grid of the run's family. -/
noncomputable abbrev finalGrid (Q : FinalQuery S A V) : TimeGrid :=
  (goldilocks S (Model.pubOf Q.run.1)).skel.grid

/-- The grid's slot time is the protocol slot time. -/
theorem finalGrid_slotTime (Q : FinalQuery S A V) (s : Nat) :
    (finalGrid S A V Q).slotTime s = Q.params.ts s := by
  change (s : Time) * (4 * Q.run.1.ΔAC) = 4 * Q.run.1.ΔAC * s
  ring

/-- **Seed glue.** A slot `u ≥ finalSeedMin Q a` is after the drain of `a`. -/
theorem finalSeedMin_spec (Q : FinalQuery S A V) {a : Time} {u : Nat}
    (hu : finalSeedMin S A V Q a ≤ u) :
    Healing.drainTime Q.params a ≤ Q.params.ts u := by
  have hu' : Q.params.slot a + 2 * Q.params.k + 5 ≤ u := hu
  rw [Healing.drainTime_eq]
  exact (SA.ts_le_iff Q.params).2 (by exact_mod_cast hu')

/-- The final pattern with offsets `[0, c, 2c, 3c]` spans `3c` slots. -/
theorem finalWindow_span_of_offsets {c : Nat}
    (hpat : (finalWindow A).offsets = [0, c, 2 * c, 3 * c]) : (finalWindow A).span = 3 * c := by
  unfold Pattern.span
  rw [hpat]
  simp only [List.foldr_cons, List.foldr_nil]
  omega

/-- **The final latency budget at the FG gap `c = fgSlots`**: `contract_latency .final =
8(X + 3c) + 2` engine delays cover the window of span `3c` and one node delay,
`4(X + 3c)Δ + Δ`. -/
theorem final_latency_gap (Q : FinalQuery S A V) :
    Q.query + 4 * ((Q.index : Nat) + 3 * A.fgSlots) * Q.params.Δ + Q.params.Δ ≤ Q.deadline := by
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  have hi : (1 : Time) ≤ ((Q.index : Nat) : Time) := by exact_mod_cast Q.index.pos
  change _ ≤ Q.query + ((K S A).params.latency .final Q.index : Time) * Q.run.1.ΔAC
  rw [show (K S A).params.latency .final Q.index = contract_latency S A .final Q.index from
    congrFun (congrFun (contract_coefficients_latency S A) .final) Q.index,
    contract_latency_final]
  change _ + 4 * _ * Q.run.1.ΔAC + Q.run.1.ΔAC ≤ _
  push_cast
  linarith only [hd, hi]

end Consensus.Goldilocks.Obligations

end
