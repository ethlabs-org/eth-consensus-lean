module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Trace

@[expose] public section

namespace Consensus.Goldilocks

variable {P : Params} {FGP : Type}

/-- Structural AC run laws, independently of the component's execution equation. -/
structure ACObsRun (A : ACInterface P FGP) (H : Set (Fin P.n)) (U : Set A.Blk)
    (tr : ACTrace A) : Prop where
  coherent : Coherent U
  init : ∀ y ∈ H, tr.init y = A.initial
  frameLaw : ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ →
    (tr.NoCallBetween y 0 i ∧ ∃ Φ₀, A.InitialFrame Φ₀ ∧ A.FrameIn U Φ₀ ∧
      A.CallOK U Φ₀ (tr.time i) ℓ.call ℓ.frame) ∨
    (∃ j ℓ', j < i ∧ tr.CallAt y j ℓ' ∧ tr.NoCallBetween y (j + 1) i ∧
      A.CallOK U ℓ'.frame (tr.time i) ℓ.call ℓ.frame)
  time_nonneg : ∀ i, 0 ≤ tr.time i
  time_mono : Monotone tr.time
  awake_of_call : ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ → tr.awake y (tr.time i)
  restart_of_sleep : ∀ y ∈ H, ∀ i ℓ (u : Time), tr.CallAt y i ℓ →
    0 ≤ u → u < tr.time i → ¬ tr.awake y u →
    (∀ j < i, ∀ ℓ', tr.CallAt y j ℓ' → tr.time j < u) → ℓ.call = .restart
  restart_at_wake : ∀ y ∈ H, ∀ u v : Time, 0 ≤ u → u < v →
    ¬ tr.awake y u → tr.awake y v →
    ∃ k, tr.RestartAt y k ∧ u < tr.time k ∧ tr.time k ≤ v
  sleep_of_restart : ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ → ℓ.call = .restart →
    ∃ u : Time, 0 ≤ u ∧ u < tr.time i ∧ ¬ tr.awake y u ∧
      ∀ j < i, ∀ ℓ', tr.CallAt y j ℓ' → tr.time j < u

end Consensus.Goldilocks

end
