module
public import ConsensusLeanTest.Goldilocks.Regimes.ProposerHold.Read
public import ConsensusLeanTest.Goldilocks.Refinement.Obligations
@[expose] public section

/-! # Rejection test: proposer hold `0` refutes Goldilocks's sleepy liveness claim

The proposer hold is a parameter of the L2 progress contract: the recurrence `prog` of the
contract asks of the selected proposer of a slot `s` that it be honest through `t_s + hold·ΔAC`.
Goldilocks's contract has hold `1` (`goldilocksContract`, `Statements/Obligations.lean`): a
proposer honest through `t_s + Δ`, when the slot's votes are cast, cannot split them with a
second proposal of its slot. This test is a counterexample just beyond that threshold
(CONTRIBUTING "Statements", kind (c)): at hold `0`, with the contract otherwise unchanged
(`holdContract`), the `sleepyLive` field of `ShapeClaimsAt` fails for the available output at
index `1`. It refutes only that L2 field at hold `0`, and so the shape obligations at hold `0`. It
makes no claim that `GoldilocksCorrect` fails at hold `0`: the L0 row `TxLive` is not refuted by
this run.

**The run** (`ProposerHold/Run.lean`): five validators, everyone awake, `ΔAC = ΔFG = 3` (slots of
`12`), horizon `41`, no submissions. Key `0` is faulty from the start and silent; key `1` proposes
slot `1` at time `12` and is compromised at `13`; key `2` proposes every other slot. Key `1`'s
releases at `12` are held back until `14`, and at `13` the honest keys `2, 3, 4` receive a forged
twin of slot `1` signed by key `1`: parent genesis, empty payload, an input no honest proposal
writes. The run is valid, has no hash collision, is sleepy for the contract, and meets the hold-`0`
recurrence (key `1` is honest at `t_1 = 12`).

**The failure.** Each honest node votes in slot `1` at `13` on the twin, the only slot-`1` block
it holds then (`twin_vote`). On the run with the faults of the horizon kept from the start
(`Model.Run.retain`), the constant-fault Sleepy machinery applies; there every origin within `41`
is genesis or the twin's block (`origin_small`), so key `2`'s confirmed read at `41` holds only the
forged header (`read_hdr`), and the retention does not change it (`read_rho`). No honest proposal
has that header, so `ProposalLiveReady` fails at the query time `11` (deadline `11 + 10·ΔAC = 41`).

**Control.** The same run fails the hold-`1` recurrence (`run_not_prog_hold_one`): key `1` is
compromised at `t_1 + ΔAC = 15`, and the window after `0` holds only slot `1`. At hold `1` the
contract is Goldilocks's (`holdContract_one`). -/

namespace Consensus.Goldilocks.Test.ProposerHold
open AsChainShape Shape Blocks
open Consensus.Model (pubOf)

variable {S : Setup}

/-- Key `2` is ready at `41` in the run, for every catch-up. -/
theorem rho_ready_two (c : Time) : (rho S).point.Ready c 2 41 := by
  rw [rho_point]
  refine ⟨?_, fun _ _ _ => rfl⟩
  change (2 : Fin 5) ∉ faulty 41
  rw [faulty_of_ge (by norm_num)]
  decide

/-- **Key `2`'s confirmed read at `41` holds only the forged header**: the retention keeps key
`2`'s state at the end of `41`. -/
theorem read_rho {h : Header Info}
    (hh : h ∈ (chainTrace (rho S)).readAt .confirmed 2 41) : h = hdr := by
  have h2 : (2 : Fin 5) ∉ (rho S).faultyAt 41 := by
    rw [rho_faultyAt, faulty_of_ge (by norm_num)]; decide
  apply read_hdr (S := S)
  have heq := Model.Run.retain_stateBefore_endCut (d := 41) (rho_sorted (S := S)) h2 41
  change h ∈ (goldilocks S (pubOf env)).out .confirmed
    ((rho S).stateBefore (Nat.findGreatest (fun i => (rho S).cutTime i ≤ 41)
      (rho S).events.length) 2).st.1 at hh
  change h ∈ (goldilocks S (pubOf env)).out .confirmed
    ((rhoc S).stateBefore (Nat.findGreatest (fun i => (rhoc S).cutTime i ≤ 41)
      (rhoc S).events.length) 2).st.1
  rw [heq]
  exact hh

variable (S) in
/-- **Proposer hold `0` refutes Goldilocks's sleepy liveness** (kind (c)): on a valid compiled run
without a hash collision, sleepy for the hold-`0` contract and meeting its recurrence at the
available output and index `1`, `ProposalLiveReady` fails for the confirmed chain. -/
theorem sleepyLive_hold_zero_false (A : ContractAssumptions S) :
    ¬ (Sys (goldilocks S) (Fin 5)).Holds
        (fun r => (Sys (goldilocks S) (Fin 5)).Sleepy (holdContract A (contract_coefficients S A) 0) r ∧
          (Sys (goldilocks S) (Fin 5)).prog (shapeProgress (goldilocks S) (Fin 5))
            (holdContract A (contract_coefficients S A) 0) .available 1 0
            ((Sys (goldilocks S) (Fin 5)).pt r).horizon r)
        (fun r => ProposalLiveReady r.2
          ((Sys (goldilocks S) (Fin 5)).cDur (holdContract A (contract_coefficients S A) 0) r)
          Out.confirmed 0 ((holdContract A (contract_coefficients S A) 0).params.latency .available 1)) := by
  intro h
  rcases h (run S) (rho_valid S) ⟨run_sleepy A _ 0, run_prog_zero A _⟩ with hP | hE
  · have hD : (11 : Time) + (((holdContract A (contract_coefficients S A) 0).params.latency
        .available 1 : Nat) : Time) * env.ΔAC = 41 := rfl
    obtain ⟨τ, k, hh, -, -, hprop, hin⟩ := hP 11 (by norm_num)
      (by rw [hD, rho_horizon]) ⟨2, by rw [hD]; exact rho_ready_two _⟩
    rw [hD] at hin
    exact honestProposal_ne_hdr hprop (read_rho (hin 2 (rho_ready_two _)))
  · exact rho_not_hashCollision S hE

variable (S) in
/-- **The shape claims fail at proposer hold `0`** (kind (c)), through their `sleepyLive` field. -/
theorem claims_hold_zero_false (A : ContractAssumptions S) :
    ¬ ShapeClaimsAt (goldilocks S) (holdContract A (contract_coefficients S A) 0) (Fin 5) :=
  fun hc => sleepyLive_hold_zero_false S A (hc.sleepyLive .available .confirmed (Or.inl rfl) rfl 1)

/-- **The shape obligations fail at proposer hold `0`** (kind (c)), at `setupSmall`. -/
theorem obligations_hold_zero_false :
    ¬ ShapeObligationsAs .ebbAndFlow (goldilocks setupSmall)
        (holdContract assumptionsSmall (contract_coefficients setupSmall assumptionsSmall) 0) :=
  fun ⟨_, ho⟩ => claims_hold_zero_false setupSmall assumptionsSmall (ho.claims (Fin 5))

end Consensus.Goldilocks.Test.ProposerHold

end
