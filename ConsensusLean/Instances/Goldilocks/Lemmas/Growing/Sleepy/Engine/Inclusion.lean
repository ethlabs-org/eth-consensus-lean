module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Reads
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Regimes.Inclusion
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Finite sleepy inclusion and growth of the engine under growing faults

* `sleepy_include_finite_at`: a proposal released at `τ` by a proposer ready at `τ` and honest
  through its hold `Δ` is in the read of every node ready at `t ∈ [τ + 6Δ, b]`;
* `sleepy_grow_finite_at`: with one proposer ready at its slot start and honest through its hold
  in every window of `k ≥ 1` slots up to `b = t + (4k + 6)Δ`, some such proposal after `t` is a
  new common entry of the ready reads at `b`.

Both are the static finite consumers without a constant-fault premise: the proposer and the
readers are honest at their own times. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation
open Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **Finite inclusion under growing faults.** Through `b ≥ 0`, under the finite service and the
two count shapes, a proposal released at `τ` by a proposer ready at `τ` and honest through its
hold is in the confirmed read of every node ready at `t ∈ [τ + 6Δ, b]`, after all events at `t`. -/
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
    (hj : Regimes.CutAfter (simTraceAt S rho hn) j t) :
    Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho)) P
      (Regimes.readAfter (simTraceAt S rho hn) y j t) :=
  Regimes.Growing.include_sleepy_at (simTraceAt_goldilocksRun S rho hn hv) hnc hb0 hsync hB hP
    hmargin htb hy hj rfl

/-- **Finite growth under growing faults.** For `b = t + (4k + 6)Δ` with `t ≥ 0`, `k ≥ 1`, under
the finite service and the two count shapes through `b`, and one proposer ready at its slot
start and honest through its hold in every window of `k` slots up to `b`: some proposal released
at `τ ∈ (t, b − 6Δ]` by a proposer ready at `τ` and honest through its hold is in every ready
read at `b`, in no ready read at `t`, and each ready read at `t` is an ancestor of each ready read
at `b`. -/
theorem sleepy_grow_finite_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn)) {t b : Time} {k : Nat}
    (ht : 0 ≤ t) (hk : 1 ≤ k) (hb : b = t + (4 * k + 6) * (S.params (pubOf E) hn).Δ)
    (hsync : Compose.Growing.SleepyServiceBefore (simTraceAt S rho hn) (honestKeysAt S rho)
      (S.params (pubOf E) hn).Δ b)
    (hB : Compose.Growing.SleepyBoundsFrom (simTraceAt S rho hn) (honestKeysAt S rho) 0 b)
    (hrec : Regimes.Growing.ProposerRecurrence (simTraceAt S rho hn) (honestKeysAt S rho)
      (runProposer S rho hn) (Regimes.catchUp (S.params (pubOf E) hn)) k
      (Regimes.Growing.hold (S.params (pubOf E) hn)) 0 b) :
    ∃ τ P, t < τ ∧ τ + 6 * (S.params (pubOf E) hn).Δ ≤ b ∧
      Regimes.Growing.ReadyProposalAt (simTraceAt S rho hn) (honestKeysAt S rho)
        (Regimes.catchUp (S.params (pubOf E) hn)) τ
        (Regimes.Growing.hold (S.params (pubOf E) hn)) P ∧
      (∀ y j, Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho)
        (Regimes.catchUp (S.params (pubOf E) hn)) y b →
        Regimes.CutAfter (simTraceAt S rho hn) j b →
        Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho)) P
          (Regimes.readAfter (simTraceAt S rho hn) y j b)) ∧
      ∀ x jx, Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho)
        (Regimes.catchUp (S.params (pubOf E) hn)) x t →
        Regimes.CutAfter (simTraceAt S rho hn) jx t →
        ¬ Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho)) P
          (Regimes.readAfter (simTraceAt S rho hn) x jx t) ∧
        ∀ y j, Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho)
          (Regimes.catchUp (S.params (pubOf E) hn)) y b →
          Regimes.CutAfter (simTraceAt S rho hn) j b →
          Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho))
            (Regimes.readAfter (simTraceAt S rho hn) x jx t)
            (Regimes.readAfter (simTraceAt S rho hn) y j b) := by
  let sp := S.params (pubOf E) hn
  let tr := simTraceAt S rho hn
  let H := honestKeysAt S rho
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  have hΔ := sp.toParams.hΔ
  have hcoh := Compose.Growing.honest_blocks_coherent hrun hnc
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  set s₀ := sp.slot t + 1
  have hts₀ : t < sp.ts s₀ := by
    by_contra h
    have := (SA.ts_le_iff_le_slot sp ht (s₀ : Int)).1 (not_lt.1 h)
    omega
  have hts₀' : sp.ts s₀ ≤ t + 4 * sp.Δ := by
    have := (SA.ts_le_iff_le_slot sp ht (sp.slot t : Int)).2 le_rfl
    simp only [SA.SAParams.ts] at this ⊢
    push_cast [s₀]
    linarith
  obtain ⟨s, hs₀s, hss, hready, hhold⟩ := hrec s₀ (lt_of_le_of_lt ht hts₀) (by
    rw [hb]
    simp only [SA.SAParams.ts] at hts₀' ⊢
    have h1k : (1 : Time) ≤ k := by exact_mod_cast hk
    rw [show ((s₀ + k - 1 : Nat) : Time) = (s₀ : Time) + k - 1 by
      rw [Nat.cast_sub (by omega)]; push_cast; ring]
    linarith)
  have hts : t < sp.ts s :=
    lt_of_lt_of_le hts₀ ((SA.ts_le_iff sp).2 (by exact_mod_cast hs₀s))
  have htsD : sp.ts s + 6 * sp.Δ ≤ b := by
    have : sp.ts s ≤ sp.ts (s₀ + (k - 1) : Nat) :=
      (SA.ts_le_iff sp).2 (by push_cast; omega)
    rw [hb]
    simp only [SA.SAParams.ts] at this hts₀' ⊢
    push_cast at this hts₀' ⊢
    rw [show ((k - 1 : Nat) : Time) = k - 1 by rw [Nat.cast_sub hk]; simp] at this
    linarith
  obtain ⟨kP, P, hP, hkP⟩ := Regimes.Growing.ready_proposer_proposes_at hrun hnc (by omega) hready
  have hRP : Regimes.Growing.ReadyProposalAt tr H (Regimes.catchUp sp) (sp.ts s)
      (Regimes.Growing.hold sp) P :=
    ⟨_, kP, hready, hhold, hP, hkP⟩
  have hinc : ∀ y j, Regimes.Growing.ReadyAt tr H (Regimes.catchUp sp) y b →
      Regimes.CutAfter tr j b →
      Anc (tr.HonestBlocksAt H) P (Regimes.readAfter tr y j b) :=
    fun y j hy hj => sleepy_include_finite_at S rho hn hv hnc hb0 hsync hB hRP htsD le_rfl hy hj
  have hnot : ∀ x jx, Regimes.Growing.ReadyAt tr H (Regimes.catchUp sp) x t →
      Regimes.CutAfter tr jx t →
      ¬ Anc (tr.HonestBlocksAt H) P (Regimes.readAfter tr x jx t) := by
    intro x jx hx hjx hPx
    have hΦ := (held_state hrun ht hjx.1 hx.1).2.1
    have hmem := (Regimes.sa_tips (A := (tr.state x jx).ac) hΦ t).1
    have hst := Trace.upTo_state tr x hjx.1
    have hr := (hrun.upTo ht).toLocalRun
    have hXs : (Regimes.readAfter tr x jx t).slot ≤ sp.slot t := by
      change (SA.acConfirmed sp (tr.state x jx).ac (Node.frame (tr.state x jx)) t).slot ≤ _
      have hm1 := hmem.1
      rw [← hst] at hm1 ⊢
      rcases Compose.tree_cases hr hx.1 hm1 with hg | ⟨q, hq, hacc⟩
      · rw [hg]; exact Nat.zero_le _
      · exact ((hr.cutLaw x hx.1 q _ hacc).1).trans
          (SA.slot_mono sp (hrun.time_nonneg q) (hjx.1 q hq))
    have := (Anc.slot_le hcoh hPx).1
    have hPslot : P.slot = s := by
      have h := hP.2.2
      rw [hkP, sp.slotTime_eq] at h
      simp only [SA.SAParams.ts] at h
      have := SA.four_delta_pos sp
      exact_mod_cast (mul_left_cancel₀ this.ne' h).symm
    have hslt : sp.slot t < s := by
      by_contra h
      have := (SA.ts_le_iff_le_slot sp ht (s : Int)).2 (by omega)
      linarith
    omega
  refine ⟨sp.ts s, P, hts, htsD, hRP, hinc,
    fun x jx hx hjx => ⟨hnot x jx hx hjx, fun y j hy hj => ?_⟩⟩
  have hsafe := sleepy_safe_finite_at S rho hn hv hnc hb0 hsync hB
  have hcompat := hsafe.agree x y jx j t b ⟨hjx.1, hjx.2.le⟩ ⟨hj.1, hj.2.le⟩
    (cutAfter_boundary_at S rho hn hv hjx) (cutAfter_boundary_at S rho hn hv hj)
    ht (by linarith) hb0 le_rfl hx hy
  rcases hcompat with h | h
  · exact h
  · exact absurd ((hinc y j hy hj).trans h) (hnot x jx hx hjx)

end Consensus.Goldilocks.Obligations.Growing

end
