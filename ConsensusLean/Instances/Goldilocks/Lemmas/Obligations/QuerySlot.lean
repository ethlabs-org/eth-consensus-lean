module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.TraceDefs
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Obligations: the producer slot of a nonfinal query

`nonfinal_query_slot`: the recurrence of a nonfinal progress premise from `ready`, at a query time
`query ≥ max ready 0` whose deadline `query + latency·ΔAC` is within the horizon, selects a
positive slot after the query whose proposal margin `6Δ` ends by the deadline, whose run-selected
proposer is ready at the slot time with the endpoint duration `cDur` and not compromised `ΔAC`
later (clamped at the horizon). It reads the run's environment point and selection only; the
transport of readiness to the trace is its users' (`NonfinalSuppliers` for constant faults,
`Growing/Obligations/Queries/Confirmed` for growing faults). -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation
open Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The producer slot of a nonfinal query**: under nonfinal progress from `ready` up to the
horizon, a query at `query ≥ max ready 0` with its deadline within the horizon has a slot
`s ≥ 1` with `query < t_s`, `t_s + 6Δ` at most the deadline, `0 ≤ t_s ≤ horizon`, and the
selected proposer of `s` ready at `t_s` with duration `cDur` and not faulty at
`min (t_s + ΔAC) horizon`. -/
theorem nonfinal_query_slot (run : (Sys (goldilocks S) V).Run) (hn : 1 ≤ Fintype.card V)
    {cap : Capability} (hnf : cap = .available ∨ cap = .stable) (index : (K S A).Idx)
    {query ready : Time}
    (hbounded : query + ((K S A).params.latency cap index : Time) * run.1.ΔAC ≤ run.2.horizon)
    (hprogress : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A)
      cap index ready run.2.horizon run)
    (hquery : max ready 0 ≤ query) :
    ∃ s : Nat, 1 ≤ s ∧ query < (S.params (Model.pubOf run.1) hn).ts s ∧
      (S.params (Model.pubOf run.1) hn).ts s + 6 * (S.params (Model.pubOf run.1) hn).Δ ≤
        query + ((K S A).params.latency cap index : Time) * run.1.ΔAC ∧
      0 ≤ (S.params (Model.pubOf run.1) hn).ts s ∧
      (S.params (Model.pubOf run.1) hn).ts s ≤ run.2.horizon ∧
      run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) run)
        (run.2.key (runProposer ⟨S, stock⟩ run.2 hn s)) ((S.params (Model.pubOf run.1) hn).ts s) ∧
      run.2.key (runProposer ⟨S, stock⟩ run.2 hn s) ∉ run.2.faultyAt
        (min ((S.params (Model.pubOf run.1) hn).ts s + run.1.ΔAC) run.2.horizon) := by
  classical
  have hquery0 : 0 ≤ query := (le_max_right ready 0).trans hquery
  have hcap : cap ≠ .final := by rcases hnf with h | h <;> simp [h]
  have hrec : PatternRecurrence run.2.point run.2.key
      (fun s => run.2.sel (.proposer s)) (goldilocks S (Model.pubOf run.1)).skel.grid
      ⟨Pattern.single, index, 1⟩ ((Sys (goldilocks S) V).cDur (K S A) run) ready
        run.2.horizon := by
    simpa only [System.prog, shapeProgress, shapeHolds, goldilocksContract, ite_eq_right hcap,
      Model.sysExternal, System.cDur, System.pt, Sys, Model.sysOf, Model.Run.point]
      using hprogress
  have hlat : (4 * (index : Time) + 6) ≤ contract_latency S A cap index := by
    exact_mod_cast contract_latency_ge_sleepy S A cap index hnf
  have hd : (1 : Time) ≤ run.1.ΔAC := run.1.ΔAC_pos
  have hi : (0 : Time) ≤ index := by positivity
  have hbudget : (4 * (index : Time) + 6) * (S.params (Model.pubOf run.1) hn).Δ ≤
      ((K S A).params.latency cap index : Time) * run.1.ΔAC := by
    rw [show (K S A).params.latency cap index = contract_latency S A cap index from
      congrFun (congrFun (contract_coefficients_latency S A) cap) index]
    change (4 * (index : Time) + 6) * run.1.ΔAC ≤ _
    exact mul_le_mul_of_nonneg_right hlat (zero_le_one.trans hd)
  have hwin : query + (index : Time) * (4 * (S.params (Model.pubOf run.1) hn).Δ) ≤
      run.2.horizon := by
    have hb := hbounded
    have hp := (S.params (Model.pubOf run.1) hn).toParams.hΔ
    change query + _ ≤ _ at hb
    linarith
  obtain ⟨s, hlo, hhi, hr⟩ := hrec query (by simpa using hquery)
    (by simpa [Recurrence.len, Pattern.single, Pattern.span, goldilocks,
      goldilocksWith, skeleton] using hwin)
    (by simpa [Recurrence.len, Pattern.single, Pattern.span, goldilocks, goldilocksWith, skeleton,
      Model.Run.point] using hwin)
  have htime : (goldilocks S (Model.pubOf run.1)).skel.grid.slotTime s =
      (S.params (Model.pubOf run.1) hn).ts s := by
    change (s : Time) * (4 * run.1.ΔAC) = 4 * run.1.ΔAC * s
    ring
  rw [htime] at hlo hhi
  have hmargin : (S.params (Model.pubOf run.1) hn).ts s +
      6 * (S.params (Model.pubOf run.1) hn).Δ ≤
      query + ((K S A).params.latency cap index : Time) * run.1.ΔAC := by
    change (S.params (Model.pubOf run.1) hn).ts s ≤
      query + (index : Time) * (4 * (S.params (Model.pubOf run.1) hn).Δ) at hhi
    linarith
  have hready := hr 0 (by simp [Pattern.single])
  simp only [Nat.add_zero] at hready
  have hmem : runProposer ⟨S, stock⟩ run.2 hn s ∈ run.2.sel (.proposer s) := by
    rw [runProposer_eq ⟨S, stock⟩ run.2 hn]
    split
    · exact Finset.min'_mem _ _
    · exact absurd hready.1 ‹_›
  obtain ⟨hR, hH⟩ := hready.2 _ hmem
  rw [htime] at hR hH
  have hs1 : 1 ≤ s := by
    cases s with
    | zero => simp [SA.SAParams.ts] at hlo; linarith
    | succ s => exact Nat.succ_pos s
  have htsh : (S.params (Model.pubOf run.1) hn).ts s ≤ run.2.horizon := by
    have := (S.params (Model.pubOf run.1) hn).toParams.hΔ
    linarith
  refine ⟨s, hs1, hlo, hmargin, hquery0.trans hlo.le, htsh, hR, ?_⟩
  simp only [Nat.cast_one, one_mul, EnvPoint.lookAhead, Model.Run.point] at hH
  exact hH

end Consensus.Goldilocks.Obligations

end
