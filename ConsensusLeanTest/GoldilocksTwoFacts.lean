module
public import ConsensusLeanTest.GoldilocksTwoChain
@[expose] public section

/-! # The healthy two-validator run: its observable events

The events of the run of `GoldilocksTwoRun` that the network premises read, stated as one
structure (`RunFacts`), so that the premises (`SyncOn`, `HealthyRun`) can be derived from these
facts alone while the facts are proved from the state invariant:

* no restart; every emission is the own vote of its slot, at the vote time `vt σ` (`1` for slot
  `0`, `t_σ` after), and both votes of every slot are emitted (by their signer) and received (by
  the other node) at that time; every AC send or admission is of a vote at its vote time;
* every processed block is the chain block of its slot, accepted at the slot's start, and both
  nodes accept every chain block of a slot `s ≥ 1` at `t_s`;
* every signed row is the own row of its height, signed at `rt q = t_{10(q−1)+1} + Δ`; every FG
  send or admission is of a row at its signing time, or (by `v0`, of a row of `v1`) thirty-five
  time units later; every row is processed by each node, at its signing time, except `v1`'s rows at
  `v0`, which are processed thirty-five time units later.

This file states the facts; their proof is the run's (`run_facts`, in the invariant file). -/

namespace Consensus.Goldilocks.Witness.TwoRun

/-- The time of the votes of slot `σ`: the tick at `1` for slot `0`, `t_σ` after. -/
def vt (σ : Nat) : Nat := if σ = 0 then 1 else 4 * σ

/-- The signing time of the rows of height `q ≥ 1`: `t_{10(q−1)+1} + Δ`. -/
def rt (q : Nat) : Nat := 40 * (q - 1) + 5

/-- The time at which `z` processes the row of `y` for height `q`: the signing time, except a row
of `v1` at `v0`, delivered thirty-five time units later. -/
def rowRecv (z y : Fin sp.n) (q : Nat) : Nat := if z = w0 ∧ y = w1 then rt q + 35 else rt q

/-- **The observable events of the run.** -/
structure RunFacts : Prop where
  /-- Nobody restarts. -/
  noRestart : ∀ y k, ¬ run.RestartAt y k
  /-- Every emission is the own vote of a slot, at its vote time. -/
  emit : ∀ y i m, run.EmitAt y i m → ∃ σ, m = vote y σ ∧ run.time i = (vt σ : Int)
  /-- Every vote is emitted by its signer at its vote time. -/
  emit_exists : ∀ y σ, ∃ i, run.EmitAt y i (vote y σ) ∧ run.time i = (vt σ : Int)
  /-- Every vote is received by the other node at its vote time. -/
  recv_exists : ∀ y z σ, z ≠ y → ∃ i, run.MsgCallAt z i (vote y σ) ∧ run.time i = (vt σ : Int)
  /-- Every AC send or admission is of a vote, at its vote time. -/
  admitMsg : ∀ x i m, run.SendOrAdmitAt x i m → ∃ y σ, m = vote y σ ∧ run.time i = (vt σ : Int)
  /-- Every processed block is the chain block of its slot `s ≥ 1`, accepted at `t_s`. -/
  block : ∀ y i B, run.BlockCallAt y i B →
    ∃ s, 1 ≤ s ∧ B = blk s ∧ run.time i = 4 * (s : Int) ∧ run.AcceptAt y i B
  /-- Both nodes accept every chain block of a slot `s ≥ 1` at `t_s`. -/
  accept_exists : ∀ y s, 1 ≤ s → ∃ i, run.AcceptAt y i (blk s) ∧ run.time i = 4 * (s : Int)
  /-- Every signed attestation is the own row of a height, at its signing time. -/
  sign : ∀ y i a, run.SignAt y i a → ∃ q, 1 ≤ q ∧ a = row y q ∧ run.time i = (rt q : Int)
  /-- Every FG send or admission is of a row, at its signing time or, by `v0` of a row of `v1`,
  at its delivery thirty-five time units later. -/
  admitAtt : ∀ x i a, run.SendOrAdmitAttAt x i a → ∃ y q, 1 ≤ q ∧ a = row y q ∧
    run.time i = (rowRecv x y q : Int)
  /-- Every row is processed by each node at its receipt time. -/
  processAtt : ∀ z y q, 1 ≤ q →
    ∃ i, run.AttCallAt z i (row y q) ∧ run.time i = (rowRecv z y q : Int)

end Consensus.Goldilocks.Witness.TwoRun

end
