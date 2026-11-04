module
public import ConsensusLeanTest.GoldilocksSimulation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Order
import ConsensusLean.Lemmas.Tactic.Linarith
@[expose] public section

/-! # F.4 (`Compose.ReadyImpliesJoined`): the restart branch

Kind (a) and kind (r) (CONTRIBUTING "Statements") for F.4 with an actual restart. Every earlier
fixture is restart-free, so `JoinedAt`'s quantifier over restarts was only met vacuously.

The run: two honest validators, engine and protocol `Δ = ΔF = 2` (slots of `8`), horizon
`64`. Validator `0` is asleep at `0` and awake from `1` on; validator `1` is always awake. So
validator `0` wakes at `1`, and the run has a restart of it at time `1`, which is its first cut:
nothing (no lock, pool or FG state) is carried across the restart.

* `restart_at_one`: the run is a `GoldilocksRun`, with a restart of validator `0` at time `1` and
  no call of it before.
* `readyImpliesJoined_restart` (a): on that run, at `t = 8Δ + 1 = 17` and `c = 8Δ − 1 = 15`
  (`8Δ ≤ c + 1`), the window `[1, 17]` is awake, and F.4 applied to the restart gives
  `0 < slot 17 = 2` and `1 ≤ t_1 = 8` (`readyImpliesJoined_restart_bound`).
* `readyImpliesJoined_needs_catchUp` (r): F.4 without `8Δ ≤ c + 1` is false. On the same run, at
  `t = 8Δ − 1 = 15` and `c = 8Δ − 3 = 13` (`c + 1 = 8Δ − 2`), the window `[1, 15]` is awake, but
  the restart at `1` is after `t_{slot 15 − 1} = t_0 = 0`. -/

namespace Consensus.Goldilocks.Obligations.Test.RestartWitness
open AsChainShape Simulation

open Shape Blocks
open Consensus.Model (pubOf)

/-- Validator `0` is asleep at time `0` only (awake from `1`); validator `1` is always awake.
Engine `Δ = ΔF = 2`, horizon `64`, no submissions. -/
def point : EnvPoint (Fin 2) :=
  ⟨⟨2, by decide, 2, by decide, fun v t => decide (v ≠ 0 ∨ 1 ≤ t)⟩, Finset.univ, 64,
    fun _ _ => []⟩

theorem one_le_card : 1 ≤ Fintype.card (Fin 2) := by decide

variable (S : Setup)

/-- Validator `1` proposes every slot; everyone polls. -/
def sel :
    (Model.protoOf (compiled (goldilocks S)) point.env).Role → Finset (Fin (Fintype.card (Fin 2)))
  | .proposer _ => {⟨1, by decide⟩}
  | .duty _ k => k.elim
  | .poll => Finset.univ

theorem sel_admits : (Model.protoOf (compiled (goldilocks S)) point.env).SelAdmits (sel S) := by
  intro r
  cases r with
  | proposer s =>
    change ((goldilocks S (pubOf point.env)).skel.proposerSel s).Admits _
    rw [Test.skeleton_proposerSel S s]
    change ({(⟨1, by decide⟩ : Fin (Fintype.card (Fin 2)))} : Finset _).card =
      min 1 (Fintype.card (Fin 2))
    simp
  | duty _ k => exact k.elim
  | poll => rfl

/-- The protocol parameters of the run: `Δ = 2`, slots of `8`. -/
abbrev sp := S.params (pubOf point.env) one_le_card

theorem sp_Δ : (sp S).Δ = 2 := rfl

/-- The run has a restart of validator `0` at time `1`, its first cut. -/
theorem restart_at_one :
    ∃ rho : Model.Run (compiled (goldilocks S)) point.env, rho.ExecutionValid ∧
      GoldilocksRun (runProposer S rho one_le_card) (digestOf S rho) (honestKeys S rho)
        (simTrace S rho one_le_card) ∧
      ∃ y ∈ honestKeys S rho,
        (∀ u : Time, (simTrace S rho one_le_card).awake y u ↔ 1 ≤ u ∧ u ≤ 64) ∧
        ∃ k, (simTrace S rho one_le_card).RestartAt y k ∧
          (simTrace S rho one_le_card).time k = 1 ∧
          ∀ j < k, ¬ (simTrace S rho one_le_card).IsCall y j := by
  obtain ⟨rho, hp, hk, -, hv, -, -, -⟩ := Shape.coverage (goldilocks S) point (by decide)
    (by exact Equiv.refl _) (sel S) (sel_admits S) 0
  have hn := one_le_card
  have hhon : rho.honest = Finset.univ := congrArg EnvPoint.honest hp
  have hhor : rho.horizon = 64 := congrArg EnvPoint.horizon hp
  have hrun := simTrace_goldilocksRun S rho hn hv
  let y : Fin (Fintype.card (Fin 2)) := ⟨0, hn⟩
  have hky : rho.key y = 0 := by rw [hk]; rfl
  have hy : y ∈ honestKeys S rho := by
    rw [mem_honestKeys_iff]
    rw [hhon]
    exact Finset.mem_univ _
  have haw : ∀ u : Time, (simTrace S rho hn).awake y u ↔ 1 ≤ u ∧ u ≤ 64 := by
    intro u
    rw [simTrace_awake_iff, awakeAt_iff, hky, hhor]
    change decide ((0 : Fin 2) ≠ 0 ∨ 1 ≤ u) = true ∧ 0 ≤ u ∧ u ≤ 64 ↔ _
    simp only [ne_eq, not_true_eq_false, false_or, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩
  obtain ⟨k, hR, hk0, hk1⟩ := hrun.restart_at_wake y hy 0 1 le_rfl (by decide)
    (fun h => absurd ((haw 0).1 h).1 (by decide)) ((haw 1).2 ⟨le_rfl, by decide⟩)
  have hk : (simTrace S rho hn).time k = 1 :=
    le_antisymm hk1 (by simpa using Int.add_one_le_of_lt hk0)
  refine ⟨rho, hv, hrun, y, hy, haw, k, hR, hk, fun j hj hc => ?_⟩
  obtain ⟨u, hu0, huk, -, hprev⟩ := hrun.sleep_of_restart y hy k hR
  have h₁ := Int.add_one_le_of_lt (hprev j hj hc)
  have h₂ := Int.add_one_le_of_lt (hk ▸ huk)
  linarith [hrun.time_nonneg j]

/-- (a) F.4's premises hold on its restart branch, and F.4 applies: on the run of `restart_at_one`,
at `t = 8Δ + 1 = 17` with `c = 8Δ − 1 = 15`, validator `0` is awake on `[1, 17]`, has a restart at
time `1 ≤ t`, and F.4 gives that this restart is at or before `t_{slot 17 − 1} = t_1 = 8`. -/
theorem readyImpliesJoined_restart :
    ∃ rho : Model.Run (compiled (goldilocks S)) point.env, rho.ExecutionValid ∧
      GoldilocksRun (runProposer S rho one_le_card) (digestOf S rho) (honestKeys S rho)
        (simTrace S rho one_le_card) ∧
      ∃ y ∈ honestKeys S rho, ∃ k, (simTrace S rho one_le_card).RestartAt y k ∧
        (simTrace S rho one_le_card).time k = 1 ∧
        8 * (sp S).Δ ≤ (8 * (sp S).Δ - 1) + 1 ∧
        (∀ u : Time, max 0 ((8 * (sp S).Δ + 1) - (8 * (sp S).Δ - 1) - 1) ≤ u →
          u ≤ 8 * (sp S).Δ + 1 → (simTrace S rho one_le_card).awake y u) ∧
        (simTrace S rho one_le_card).awake y (8 * (sp S).Δ + 1) ∧
        (simTrace S rho one_le_card).JoinedAt y (8 * (sp S).Δ + 1) ∧
        (sp S).toParams.slotOf (8 * (sp S).Δ + 1) = 2 ∧
        (sp S).toParams.slotTime ((sp S).toParams.slotOf (8 * (sp S).Δ + 1) - 1) = 8 := by
  obtain ⟨rho, hv, hrun, y, hy, haw, k, hR, hk, -⟩ := restart_at_one S
  have hwin : ∀ u : Time, max 0 ((8 * (sp S).Δ + 1) - (8 * (sp S).Δ - 1) - 1) ≤ u →
      u ≤ 8 * (sp S).Δ + 1 → (simTrace S rho one_le_card).awake y u := by
    intro u h1 h2
    have h1' := le_of_max_le_right h1
    rw [sp_Δ] at h1' h2
    exact (haw u).2 ⟨by linarith, by linarith⟩
  have hc : 8 * (sp S).Δ ≤ (8 * (sp S).Δ - 1) + 1 := (sub_add_cancel _ _).symm.le
  obtain ⟨hw, hj⟩ := Compose.ready_implies_joined _ _ _ _ _ _ hrun y hy (8 * (sp S).Δ + 1)
    (8 * (sp S).Δ - 1) (by rw [sp_Δ]; decide) hc hwin
  refine ⟨rho, hv, hrun, y, hy, k, hR, hk, hc, hwin, hw, hj, by rw [sp_Δ]; rfl, ?_⟩
  rw [sp_Δ]; rfl

/-- The restart branch of `readyImpliesJoined_restart`, read off: the restart at time `1` is in
`(0, t_1]` and `slot 17 > 0`. -/
theorem readyImpliesJoined_restart_bound :
    ∃ rho : Model.Run (compiled (goldilocks S)) point.env, rho.ExecutionValid ∧
      ∃ y ∈ honestKeys S rho, ∃ k, (simTrace S rho one_le_card).RestartAt y k ∧
        0 < (simTrace S rho one_le_card).time k ∧
        0 < (sp S).toParams.slotOf (8 * (sp S).Δ + 1) ∧
        (simTrace S rho one_le_card).time k ≤
          (sp S).toParams.slotTime ((sp S).toParams.slotOf (8 * (sp S).Δ + 1) - 1) := by
  obtain ⟨rho, hv, -, y, hy, k, hR, hk, -, -, -, hj, -, -⟩ := readyImpliesJoined_restart S
  obtain ⟨h0, hle⟩ := hj k hR (by rw [hk, sp_Δ]; decide)
  exact ⟨rho, hv, y, hy, k, hR, by rw [hk]; decide, h0, hle⟩

include S in
/-- (r) F.4 without its catch-up premise `8Δ ≤ c + 1` is false. On the run of `restart_at_one`,
at `t = 8Δ − 1 = 15` with `c = 8Δ − 3 = 13` (`c + 1 = 8Δ − 2`), validator `0` is awake on its
whole window `[1, 15]`, but its restart at `1` is after `t_{slot 15 − 1} = t_0 = 0`, so it is not
joined at `15`. -/
theorem readyImpliesJoined_needs_catchUp :
    ¬ ∀ (sp : SA.SAParams) (ro : SA.ReplayOrder sp (List (FG.Att sp.n)))
      (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)) (H : Set (Fin sp.n))
      (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
      GoldilocksRun proposer dg H tr → ∀ y ∈ H, ∀ (t c : Time), 0 ≤ t →
        (∀ u : Time, max 0 (t - c - 1) ≤ u → u ≤ t → tr.awake y u) →
        tr.awake y t ∧ tr.JoinedAt y t := by
  intro hall
  obtain ⟨rho, -, hrun, y, hy, haw, k, hR, hk, -⟩ := restart_at_one S
  obtain ⟨-, hj⟩ := hall _ _ _ _ _ _ hrun y hy 15 13 (by decide) (fun u h1 h2 =>
    (haw u).2 ⟨by linarith [le_of_max_le_right h1], by linarith⟩)
  obtain ⟨-, hle⟩ := hj k hR (by rw [hk]; decide)
  rw [hk, show (sp S).toParams.slotTime ((sp S).toParams.slotOf 15 - 1) = 0 from rfl] at hle
  exact absurd hle (by decide)

end Consensus.Goldilocks.Obligations.Test.RestartWitness
