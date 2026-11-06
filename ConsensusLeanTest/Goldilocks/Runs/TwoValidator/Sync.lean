module
public import ConsensusLeanTest.Goldilocks.Runs.TwoValidator.Facts

public section

/-! # The healthy two-validator run: network service

Derive GST and Healthy from the observable-event interface, independently of its execution
invariant. Votes and blocks reach both validators at their send time. Rows arrive at signing
time or thirty-five time units later, strictly within `ΔF = 36`.

Attestation form (d) permits an earlier processing to satisfy a later admission's deadline.
Each row's receipt therefore suffices, including its signer's processing before a delayed
admission at the other validator. The delay ordering is `Δ = 1 ≤ 36 = ΔF`.
These are conditional witnesses until the run's invariant supplies `RunFacts`.
-/

namespace Consensus.Goldilocks.Witness.TwoRun

private theorem time_lt_index {i j : Nat} (h : run.time i < run.time j) : i < j := by
  change ((i / 1024 : Nat) : Int) < ((j / 1024 : Nat) : Int) at h
  omega

private theorem lastWake_eq (hf : RunFacts) (y : Fin sp.n) :
    ∀ k, run.lastWake y k = ⊥
  | 0 => by simp [RunTrace.lastWake, hf.noRestart]
  | k + 1 => by simp [RunTrace.lastWake, hf.noRestart, lastWake_eq hf y k]

private theorem deadline_eq (hf : RunFacts) (y : Fin sp.n) (k : Nat) (τ Δ' : Time) :
    run.deadline y k τ Δ' = τ + Δ' := by
  simp only [RunTrace.deadline, lastWake_eq hf]
  rfl

/-- The actual two-validator schedule meets GST with `g = 0` and `ΔF = 36`, provided its
observable events satisfy `RunFacts`. No run-law or state invariant is assumed separately. -/
theorem run_gst (hf : RunFacts) : run.GSTRun Set.univ 36 0 where
  deltaF := by decide
  delta_le := by decide
  message x _ i m hm _ z _ j _ hj := by
    obtain ⟨y, σ, rfl, ht⟩ := hf.admitMsg x i m hm
    have hproc : ∃ k, run.ProcessMsgAt z k (vote y σ) ∧ run.time k = (vt σ : Int) := by
      by_cases he : z = y
      · subst z
        obtain ⟨k, hk, hkt⟩ := hf.emit_exists y σ
        exact ⟨k, Or.inr hk, hkt⟩
      · obtain ⟨k, hk, hkt⟩ := hf.recv_exists y z σ he
        exact ⟨k, Or.inl hk, hkt⟩
    obtain ⟨k, hk, hkt⟩ := hproc
    rw [deadline_eq hf, ht, max_eq_left (Int.natCast_nonneg _)] at hj
    change (vt σ : Int) + 1 ≤ run.time j at hj
    have hkj : k < j := time_lt_index (by rw [hkt]; dsimp only [Time] at *; omega)
    refine ⟨k, hkj.le, by rw [ht, hkt], hk, ?_⟩
    rw [deadline_eq hf, ht, max_eq_left (Int.natCast_nonneg _), hkt]
    change (vt σ : Int) < (vt σ : Int) + 1
    omega
  block x _ i B hB _ z _ j _ hj := by
    have hb : run.BlockCallAt x i B := hB.elim (fun h => ⟨true, h⟩) And.left
    obtain ⟨s, hs, rfl, ht, _⟩ := hf.block x i B hb
    obtain ⟨k, hk, hkt⟩ := hf.accept_exists z s hs
    rw [deadline_eq hf, ht, max_eq_left (by positivity)] at hj
    change 4 * (s : Int) + 1 ≤ run.time j at hj
    have hkj : k < j := time_lt_index (by rw [hkt]; dsimp only [Time] at *; omega)
    refine ⟨k, hkj.le, by rw [ht, hkt], ⟨true, hk⟩, ?_⟩
    rw [deadline_eq hf, ht, max_eq_left (by positivity), hkt]
    change 4 * (s : Int) < 4 * (s : Int) + 1
    omega
  relay x _ i B hB _ z _ j _ hj _ := by
    obtain ⟨s, hs, rfl, ht, _⟩ := hf.block x i B ⟨true, hB⟩
    obtain ⟨k, hk, hkt⟩ := hf.accept_exists z s hs
    rw [deadline_eq hf, ht, max_eq_left (by positivity)] at hj
    change 4 * (s : Int) + 1 ≤ run.time j at hj
    have hkj : k < j := time_lt_index (by rw [hkt]; dsimp only [Time] at *; omega)
    refine ⟨k, hkj.le, hk, ?_⟩
    rw [deadline_eq hf, ht, max_eq_left (by positivity), hkt]
    change 4 * (s : Int) < 4 * (s : Int) + 1
    omega
  attestation x _ i a ha _ z _ j _ hj := by
    obtain ⟨y, q, hq, rfl, ht⟩ := hf.admitAtt x i a ha
    obtain ⟨k, hk, hkt⟩ := hf.processAtt z y q hq
    have hhi : run.time k < (rowRecv x y q : Int) + 36 := by
      simp only [hkt, rowRecv]
      split_ifs <;> push_cast <;> dsimp only [Time] at * <;> omega
    rw [deadline_eq hf, ht, max_eq_left (Int.natCast_nonneg _)] at hj
    refine ⟨k, (time_lt_index (hhi.trans_le hj)).le, Or.inl hk, ?_⟩
    rwa [deadline_eq hf, ht, max_eq_left (Int.natCast_nonneg _)]

/-- Both validators are honest and awake forever from time zero. Together with the network
service above this gives the healthy regime, conditional only on the observable run facts. -/
theorem run_healthy (hf : RunFacts) : run.HealthyRun Set.univ 36 0 := by
  refine ⟨run_gst hf, ?_, ?_⟩
  · intro y _ t ht
    exact ht
  · simp

end Consensus.Goldilocks.Witness.TwoRun

end
