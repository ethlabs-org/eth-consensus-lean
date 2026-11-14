module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Binding
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.CommitteeVotes
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Transport
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The committee facts of a run

The gate `voteK_gate`, and, on a run record of the canonical growing trace, P
(`voteK_committeeP`: the pools and the optimistic-check states) and the frames
(`voteK_frame_member`) hold for the run's dictionary `voteK` (`GS/CommitteeVotes`, with
`voteK_bindsSel`). With the committee size `voteK_ncard` they are the committee facts
`voteK_facts`. `voteK_bounds` gives the committee count shapes from committee sleepy
participation of the run's selection, at the threshold of a contract with `θ ≥ 1/2`.

`sleepy_committee_at` packages both for a sleepy run: the committee premises
(`CommitteeFacts`, `CommitteeBoundsFrom`) of the run's committees through every `b ≤ horizon`,
from the committee clause of `Sleepy`. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V]

section Run

variable (S : BoundSetup) {E : Env V} (rho : Model.Run (compiled (goldilocksWith S)) E)
  (hn : 1 ≤ Fintype.card V)

/-- **The gate**: a node honest at `0` may vote in slot `s` iff it is in the run's committee of
`s`. -/
theorem voteK_gate (hv : rho.ExecutionValid) :
    ∀ x, x ∈ honestKeysAt S rho 0 → ∀ i s,
      ((simTraceAt S rho hn).state x i).ac.mayVote s = true ↔ x ∈ (voteK S rho).committee s :=
  simTraceAt_gate S rho hn hv (voteK_bindsSel S rho)

/-- **P**: the pools of a node honest at `t`, before every cut whose earlier cuts are at times
`≤ t`, and its optimistic-check states at the cuts at which it is honest, hold only votes of
members of their slots. The start's pools are empty (`simIni_voteStart`); a later pool is the
post-state of an honest call (`simTraceAt_pool_member`), and an optimistic-check pool is in the
call's post-state pool (`SA.optimisticPoint_pool_post`). -/
theorem voteK_committeeP (hv : rho.ExecutionValid) (hnc : ¬ rho.HashCollision) {ini}
    (hrun : Growing.GoldilocksRun (runProposer S rho hn) (digestOf S rho) (honestKeysAt S rho)
      (simTraceAt S rho hn) ini) :
    SA.CommitteePAt (voteK S rho) (simTraceAt S rho hn).projAC (honestKeysAt S rho) := by
  have hpool := simTraceAt_pool_member S hrun hv (voteK_bindsSel S rho) hnc
  refine ⟨fun t y hy i hi s v hm => ?_, fun y i ℓ A hy hpt s v hm => ?_⟩
  · cases i with
    | zero =>
      have h0 : ((simTraceAt S rho hn).projAC.state y 0).pool s = [] := by
        change (((simTraceAt S rho hn).init y).ac).pool s = []
        rw [simTraceAt_eq, simTrace_init_eq]
        exact (simIni_voteStart S rho hn y).pool s
      rw [h0] at hm
      exact absurd hm List.not_mem_nil
    | succ i => exact hpool y i s (hrun.antitone (hi i (Nat.lt_succ_self i)) hy) v hm
  · have hm' := hrun.time_mono
    have hacr := Compose.Growing.acRun_upTo hrun
      (noCollRun_simTraceAt S rho hn hv hnc) (hrun.time_nonneg i)
    have hsub := SA.optimisticPoint_pool_post hacr.localRun hy
      ((SA.upTo_optimisticPoint hm').mpr ⟨le_rfl, hpt⟩) s hm
    rw [Trace.upTo_state (simTraceAt S rho hn).projAC y
      fun k hk => hm' (Nat.lt_succ_iff.mp hk)] at hsub
    exact hpool y i s hy v hsub

/-- **The frames of honest nodes carry votes of members.** -/
theorem voteK_frame_member (hv : rho.ExecutionValid) {ini}
    (hrun : Growing.GoldilocksRun (runProposer S rho hn) (digestOf S rho) (honestKeysAt S rho)
      (simTraceAt S rho hn) ini) :
    ∀ w c, w ∈ honestKeysAt S rho ((simTraceAt S rho hn).time c) →
      ∀ C ∈ (Node.frame ((simTraceAt S rho hn).state w c)).tree,
        ∀ v ∈ SA.blockVotes C, v.val ∈ (voteK S rho).committee v.slot :=
  simTraceAt_tree_member S hrun hv (voteK_bindsSel S rho)

/-- **The committee facts of a run**: size, P, frames, and the gate read at every read time
`t ≥ 0` (a node honest at `t` is honest at `0`). -/
theorem voteK_facts (hv : rho.ExecutionValid) (hnc : ¬ rho.HashCollision) {ini}
    (hrun : Growing.GoldilocksRun (runProposer S rho hn) (digestOf S rho) (honestKeysAt S rho)
      (simTraceAt S rho hn) ini) :
    Compose.Growing.CommitteeFacts (simTraceAt S rho hn) (honestKeysAt S rho) (voteK S rho) where
  hsize := voteK_ncard S rho hn hv
  hP := voteK_committeeP S rho hn hv hnc hrun
  hFrame := voteK_frame_member S rho hn hv hrun
  hGate := fun _ ht x hx i _ s => voteK_gate S rho hn hv x (hrun.antitone ht hx) i s

/-- **The committee count shapes of the run's committees** through `b ≤ horizon`, from committee
sleepy participation of the run's selection on `[0, b]` at the threshold of a contract `K` with
`θ ≥ 1/2`, a catch-up `c` that covers joining (`8Δ ≤ c + 1`) and a look-ahead `W ≥ 5Δ`
(`committee_bounds_at` at the slot committees, `mem_voteK_iff_selected`). -/
theorem voteK_bounds (hv : rho.ExecutionValid) {ini}
    (hrun : Growing.GoldilocksRun (runProposer S rho hn) (digestOf S rho) (honestKeysAt S rho)
      (simTraceAt S rho hn) ini)
    {Prog : Type} (K : Contract Prog) (hθ : 1 / 2 ≤ K.params.θ) {η c W b : Time}
    (hc : 8 * (S.params (pubOf E) hn).Δ ≤ c + 1) (hW : 5 * (S.params (pubOf E) hn).Δ ≤ W)
    (hb : b ≤ rho.horizon)
    (hsl : rho.point.CommitteeSleepyOn
      ((shapeProgress (goldilocksWith S) V).toExternal.selected rho.point.env
        ((shapeProgress (goldilocksWith S) V).toExternal.ext ⟨E, rho⟩))
      K.params.θ η c W 0 b) :
    Compose.Growing.CommitteeBoundsFrom (simTraceAt S rho hn) (honestKeysAt S rho) (voteK S rho)
      0 b :=
  committee_bounds_at S rho hn hv hrun (fun _ ht _ => mem_voteK_iff_selected S rho hn hv ht)
    (voteK_nonempty S rho hn hv) hθ hc hW hb hsl
    (add_nonneg (Compose.Growing.ts_natCast_nonneg 0) (S.params (pubOf E) hn).toParams.hΔ.le)
    (le_max_right _ _)

end Run

/-- **The committee premises of a sleepy run** through `b ≤ horizon`: the run's committees
`voteK` carry the committee facts (`voteK_facts`) and the committee count shapes
(`voteK_bounds`, from the committee clause of `Sleepy` with the contract's catch-up and
committee look-ahead) at the contract's threshold, which is `1/2`. -/
theorem sleepy_committee_at (S : BoundSetup) (A : ContractAssumptions S.toSetup) {V : Type}
    [Fintype V] [DecidableEq V] (r : (Sys (goldilocksWith S) V).Run) (hn : 1 ≤ Fintype.card V)
    (hv : (Sys (goldilocksWith S) V).Valid r) (hc : ¬ r.2.HashCollision)
    (hs : (Sys (goldilocksWith S) V).Sleepy (shapeProgress (goldilocksWith S) V).toExternal
      (K S.toSetup A) r)
    {b : Time} (hb : b ≤ r.2.horizon) :
    ∃ K : SA.CommitteeDict (Fintype.card V),
      Compose.Growing.CommitteeFacts (simTraceAt S r.2 hn) (honestKeysAt S r.2) K ∧
      Compose.Growing.CommitteeBoundsFrom (simTraceAt S r.2 hn) (honestKeysAt S r.2) K 0 b := by
  have h19 : (19 : Time) ≤ (contract_catchUp S.toSetup A : Nat) := by
    exact_mod_cast contract_catchUp_ge_sleepy S.toSetup A
  have hd : (1 : Time) ≤ r.1.ΔAC := r.1.ΔAC_pos
  have hcd : 8 * (S.params (pubOf r.1) hn).Δ ≤
      (Sys (goldilocksWith S) V).cDur (K S.toSetup A) r + 1 := by
    simp only [System.cDur, Params.standard, contract_coefficients_catchUp]
    change 8 * r.1.ΔAC ≤ (contract_catchUp S.toSetup A : Nat) * r.1.ΔAC + 1
    nlinarith
  have hrun := simTraceAt_goldilocksRun S r.2 hn hv
  exact ⟨voteK S r.2, voteK_facts S r.2 hn hv hc hrun,
    voteK_bounds S r.2 hn hv hrun (K S.toSetup A) le_rfl (η := 0) hcd
      (by change 5 * r.1.ΔAC ≤ ((5 : Nat) : Int) * r.1.ΔAC; norm_num) hb
      fun t h₁ h₂ => hs.2.2 t h₁ (h₂.trans hb)⟩

end Consensus.Goldilocks.Obligations.Growing

end
