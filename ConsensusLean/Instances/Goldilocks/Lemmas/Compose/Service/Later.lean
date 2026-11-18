module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Adopt
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: the update at `t_s + 6Δ`

`update_of_awake_joined`: an honest validator awake and joined at `t_s + 6Δ` runs the update of
slot `s` there; its tick at that public time starts with `ac_on_tick`, joined. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}

/-- The cuts of a tick: the AC's tick, the proposal step, the FG update. -/
private theorem tick_cuts {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} (y : Fin sp.n)
    (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat) :
    (Node.exec proposer dg y st t (.tick x)).2 = (Node.tickStep proposer dg y st t x .acTick).2 ++
      (Node.tickStep proposer dg y
        (Node.tickStep proposer dg y st t x .acTick).1 t x .proposal).2 ++
      (Node.tickStep proposer dg y (Node.tickStep proposer dg y
        (Node.tickStep proposer dg y st t x .acTick).1 t x
        .proposal).1 t x .fgUpdate).2 := by
  simp [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps]

/-- **An honest validator awake and joined at `t_s + 6Δ` runs the update of slot `s`** there: its
tick at that public time starts with `ac_on_tick`, joined. -/
theorem update_of_awake_joined {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ini}
    (hrun : GoldilocksRun proposer dg H tr ini)
    {x : Fin sp.n} (hx : x ∈ H) {s : Nat} (hw : tr.awake x (sp.ts s + 6 * sp.Δ))
    (hj : tr.JoinedAt x (sp.ts s + 6 * sp.Δ)) :
    ∃ k ℓ, SA.UpdateAt tr.projAC x k s ℓ := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have h0 : (0 : Time) ≤ sp.ts s := by
    simp only [SAParams.ts]
    exact mul_nonneg (by linarith) (Int.natCast_nonneg s)
  obtain ⟨j, c, hj'⟩ := hrun.tick_of_awake x hx _ (by linarith)
    (show sp.toParams.IsPublic _ from Dvd.intro (4 * (s : Int) + 6)
      (by simp only [SAParams.ts]; ring)) hw
  obtain ⟨-, hk, -⟩ := hj'
  have hlen :
      0 < (Node.exec proposer dg x (tr.state x j) (sp.ts s + 6 * sp.Δ) (.tick c)).2.length := by
    rw [tick_cuts]; simp [Node.tickStep]
  obtain ⟨hn0, ht0, -, -, hl0⟩ := hk 0 hlen
  have hget : (Node.exec proposer dg x (tr.state x j) (sp.ts s + 6 * sp.Δ) (.tick c)).2[0]'hlen =
      (Node.acCall x (tr.state x j) (sp.ts s + 6 * sp.Δ) .tick).2 := by
    simp only [tick_cuts]; rfl
  rw [hget] at hl0
  simp only [Nat.add_zero] at hn0 ht0 hl0
  obtain ⟨ℓ, hl, hcall⟩ : ∃ ℓ : ACLabel (goldilocksNode sp ro),
      tr.label j = some (.ac ℓ) ∧ ℓ.call = .tick := ⟨_, hl0, rfl⟩
  have hnr : ¬ tr.RestartAt x j := by
    rintro ⟨ℓ', ⟨-, hl'⟩, hr'⟩
    have h := hl'.symm.trans hl
    injection h with h
    injection h with h
    rw [h, hcall] at hr'
    cases hr'
  have htj : tr.projAC.time j = sp.ts s + 6 * sp.Δ := ht0
  refine ⟨j, ℓ, ⟨hn0, by simp [RunTrace.projAC, hl, RunTrace.acLabel]⟩, hcall, htj, ?_⟩
  rw [projAC_state hrun.toLocalRun hx j, htj]
  exact ((joined_projection_from hrun hx _).2.1 j ⟨_, hn0, hl⟩ hnr ht0).1 hj

end Consensus.Goldilocks.Compose

end
