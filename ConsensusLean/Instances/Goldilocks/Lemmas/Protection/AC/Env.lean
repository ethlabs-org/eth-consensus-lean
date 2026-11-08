module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.ProtACEnv
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Tier A protection: facts of the trace vocabulary

* `PSyncAC.of_core`: service from `b₁` follows from `HealthyACCore`'s service at `g := b₁`, the
  relay of older blocks and the re-service of messages after restarts (so `PSyncAC` asks no more
  of the message and relay clauses than H.1's service does);
* `lastCallAt_unique`, `readAC_unique`: a validator has at most one last call at or before `T`,
  hence at most one read at `T`;
* `exists_public_ready`, `readAC_exists`: a validator ready at `T ≥ 0` with a catch-up of at
  least one slot length is awake at a public time of its readiness window, so it ticks by `T`
  (`TickDuty`), and with time progress and monotone time its last call at or before `T` exists,
  hence its read at `T`. -/

namespace Consensus.Goldilocks.Comparison

open SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}

/-- **Service from `b₁` from H.1's service**: `HealthyACCore` at `g := b₁`, the relay of older
blocks and the re-service after restarts give `PSyncAC`. -/
theorem PSyncAC.of_core {b₁ : Time} (h : HealthyACCore tr H U b₁) (ho : OlderRelayAC tr H U b₁)
    (hr : RewakeServiceAC tr H b₁) : PSyncAC tr H U b₁ :=
  ⟨h.message, h.relay, ho, hr⟩

/-- At most one last call at or before `T`. -/
theorem lastCallAt_unique {y : Fin sp.n} {j j' : Nat} {T : Time} (h : LastCallAt tr y j T)
    (h' : LastCallAt tr y j' T) : j = j' := by
  obtain ⟨⟨ℓ, hc⟩, hT, hlast⟩ := h
  obtain ⟨⟨ℓ', hc'⟩, hT', hlast'⟩ := h'
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · exact absurd hT' (not_le.2 (hlast j' ℓ' hlt hc'))
  · exact heq
  · exact absurd hT (not_le.2 (hlast' j ℓ hgt hc))

/-- **At most one read at `T`.** -/
theorem readAC_unique {y : Fin sp.n} {T : Time} {B B' : Blk sp.n FGP} (h : ReadAC tr y T B)
    (h' : ReadAC tr y T B') : B = B' := by
  obtain ⟨j, ℓ, hl, hc, rfl⟩ := h
  obtain ⟨j', ℓ', hl', hc', rfl⟩ := h'
  obtain rfl := lastCallAt_unique hl hl'
  have : ℓ = ℓ' := Option.some.inj (hc.2.symm.trans hc'.2)
  rw [this]

/-- A validator ready at `T ≥ 0` with catch-up `cu·Δ`, `cu ≥ 1`, is awake at a public time
`τ ≤ T` of its readiness window. -/
theorem exists_public_ready {cu : ℕ} (hcu : 1 ≤ cu) {y : Fin sp.n} {T : Time} (hT : 0 ≤ T)
    (hy : ReadyAC tr H ((cu : Time) * sp.Δ) y T) :
    ∃ τ, 0 ≤ τ ∧ τ ≤ T ∧ sp.toParams.IsPublic τ ∧ tr.awake y τ := by
  have hΔ := sp.toParams.hΔ
  have hcu' : (1 : Time) ≤ cu := by exact_mod_cast hcu
  have hm := Int.emod_nonneg T (ne_of_gt hΔ)
  have hm' := Int.emod_lt_of_pos T hΔ
  have hd := Int.emod_def T sp.Δ
  have h0 : 0 ≤ sp.Δ * (T / sp.Δ) := mul_nonneg hΔ.le (Int.ediv_nonneg hT hΔ.le)
  have hc : sp.Δ ≤ (cu : Time) * sp.Δ := by nlinarith
  refine ⟨sp.Δ * (T / sp.Δ), h0, by linarith, dvd_mul_right _ _, hy.2 _ ?_ (by linarith)⟩
  exact max_le h0 (by linarith)

/-- **The read of a ready validator exists**: on a run with the tick duty, time progress and
monotone time, a validator ready at `T ≥ 0` with catch-up `cu·Δ`, `cu ≥ 1`, has a last call at or
before `T`, hence a read at `T`. -/
theorem readAC_exists (hmono : Monotone tr.time) (htick : TickDuty tr H)
    (hprog : TimeProgressAC tr) {cu : ℕ} (hcu : 1 ≤ cu) {y : Fin sp.n} {T : Time} (hT : 0 ≤ T)
    (hy : ReadyAC tr H ((cu : Time) * sp.Δ) y T) : ∃ B, ReadAC tr y T B := by
  classical
  obtain ⟨τ, hτ0, hτT, hpub, haw⟩ := exists_public_ready hcu hT hy
  obtain ⟨i, ℓ, hc, -, hti⟩ := htick y hy.1 τ hτ0 hpub haw
  obtain ⟨i₀, hi₀⟩ := hprog T
  -- every cut at or before `T` is below `i₀`
  have hbelow : ∀ j, tr.time j ≤ T → j < i₀ := fun j hj => by
    by_contra h
    exact absurd hj (not_le.2 (lt_of_lt_of_le hi₀ (hmono (not_lt.1 h))))
  let P : Nat → Prop := fun j => (∃ ℓ, tr.CallAt y j ℓ) ∧ tr.time j ≤ T
  have hPi : P i := ⟨⟨ℓ, hc⟩, hti ▸ hτT⟩
  let j := Nat.findGreatest P i₀
  have hPj : P j := Nat.findGreatest_spec (P := P) (hbelow i hPi.2).le hPi
  obtain ⟨⟨ℓj, hcj⟩, hjT⟩ := hPj
  refine ⟨_, j, ℓj, ⟨⟨ℓj, hcj⟩, hjT, fun j' ℓ' hjj' hc' => ?_⟩, hcj, rfl⟩
  by_contra hle
  have hP' : P j' := ⟨⟨ℓ', hc'⟩, not_lt.1 hle⟩
  exact absurd (Nat.le_findGreatest (hbelow j' hP'.2).le hP') (not_le.2 hjj')

end Consensus.Goldilocks.Comparison

end
