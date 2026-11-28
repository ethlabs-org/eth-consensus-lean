module
public import ConsensusLeanTest.Goldilocks.Runs.OneValidator.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
@[expose] public section

/-! # The one-validator tick run through the run-level healing statements

On the one-validator tick run of `Goldilocks/Runs/OneValidator/Premises` (`n = 1`, `f = 0`, `Δ = 1`,
`k = δ_t = 2`, `t_s = 4s`, a tick at every time `t ≥ 0`, cut `i` at time `⌊i/8⌋`, no restart), with
`g = 0`, `Δ_F = 1`, `κ = 2Δ` and `G_p = 4`, the proved run-level healing statement HR.1
(`CutAndReset`) is applied to the run, its premises met outright (HR.3 is retired).

* **The parameters** (computed from the definitions): `ḡ = 0` (`gbar_zero`), `c_z = 12`
  (`cutZ_zero`), `H_z = 3` (`hz_zero`), `a_z = 16` (`aZ_zero`), `Θ = 12` (`theta_sp1`),
  `C_HS = 86` (`C_HS_sp1`), `A_HS = 173` (`A_HS_sp1`).
* (a) `healing_premises`: `GoldilocksRun`, `HSShared` (with `Healthy(0)` and `NoColl`),
  `Catch(2Δ)` and `Prop⁺(4)`.
* (b) `tickRun_cutAndReset` (HR.1): the conclusion read at these parameters.

With `n = 1` and `f = 0` this shows the premises consistent, not met with faults. -/

namespace Consensus.Goldilocks.Witness.One

open AC Node ChainFrame

/-- Every tick in the constructed run has its signing tag set. -/
theorem tickRun_allTicksSign :
    (tickRun N1 dg1).AllTicksSign (fun _ => v0) dg1 Set.univ := by
  intro y _ j t htick
  obtain ⟨x, fgDue, hg⟩ := htick
  obtain ⟨hj, ht⟩ := tickRun_groupAt_inv hg
  rw [eq_v0 rfl y, ht]
  have hj' : j = 8 * (j / 8) := by omega
  refine ⟨0, ?_⟩
  convert tickRun_groupAt (A := N1) (dg := dg1) rfl (j / 8) using 1

/-! ## The parameters -/

/-- `ḡ = 0` at `g = 0`. -/
theorem gbar_zero : gbar 0 = 0 := max_self 0

/-- `slot(ḡ) + 3 = 3` at `g = 0`. -/
theorem zN_zero : zN 0 = 3 := by
  have h := slotOf_nat 0
  rw [Nat.cast_zero] at h
  unfold zN
  rw [gbar_zero, h]

/-- `c_z = t_{slot(ḡ)+3} = 12` at `g = 0`. -/
theorem cutZ_zero : Healing.cutZ sp1.toParams 0 = 12 := by
  rw [cutZ_eq, zN_zero]; rfl

/-- `H_z = 3` at `g = 0`. -/
theorem hz_zero : Healing.HZ (tickRun N1 dg1) Set.univ 0 = 3 := by
  rw [hz_eq, zN_zero]

/-- The reset `a_z = 16` at `g = 0`. -/
theorem aZ_zero : aZ 0 = 16 := by
  unfold aZ; rw [zN_zero]; rfl

/-- `Θ = 4(k + 1)Δ = 12` (the optimistic confirmation is on by default). -/
theorem theta_sp1 : AC.Θ sp1 = 12 := by decide

/-- `C_HS = (8k + 49 + 4δ_t)Δ + Δ_F + 3G_p = 86` at `Δ_F = 1`, `G_p = 4`. -/
theorem C_HS_sp1 : Healing.C_HS sp1 1 4 = 86 := by decide

/-- `A_HS = 2C_HS + Δ = 173` at `Δ_F = 1`, `G_p = 4`. -/
theorem A_HS_sp1 : Healing.A_HS sp1 1 4 = 173 := by decide

/-! ## The premise bundles -/

/-- (a) **The premises of HR.3** at `g = 0`, `Δ_F = 1`, `κ = 2Δ`, `G_p = 4`: a Goldilocks
run with the HS shared premises (`Healthy(0)`, `NoColl`, genesis root, no restart, the timeout
bound), `Catch(2Δ)` and `Prop⁺(4)`. -/
theorem healing_premises :
    GoldilocksRun (sp := sp1) (fun _ => v0) dg1 Set.univ (tickRun N1 dg1) ∧
      Healing.HSShared (tickRun N1 dg1) Set.univ (AC.CommitteeDict.full sp1.n) dg1 0 1 ∧
      Healing.CatchRun (tickRun N1 dg1) Set.univ 0 (2 * sp1.Δ) ∧
      Healing.PropPlus (tickRun N1 dg1) Set.univ (fun _ => v0) 0 4 :=
  ⟨tickRun_goldilocksRun, tickRun_hsShared 0, tickRun_catch 0 _ (by decide),
    tickRun_propPlus 0 4 le_rfl⟩

/-! ## The statements on the run -/

/-- (b) **HR.1 on the tick run** at `g = 0`, `Δ_F = 1`, with `c_z = 12` and `H_z = 3`. Part (a):
every honest attestation signed at or before `12` has height `≤ 3`, and from `12` on `ac_to_fg`
returns live fast locks (deep sources are off at `sp1`, so HR.1 (a)'s deep arm is empty); part
(b): a chain of state height `≥ 5` carries an honest attestation of height `4`; part (c), at the
reset `a_z = 16`: `12 < 16`, the honest pairs of height `≥ 4` are signed from `16` on, the rows
signed at `16` have height `≤ 4`, and the first clause of (K1) holds with `T₀ = 16 − Δ = 15`. -/
theorem tickRun_cutAndReset :
    (12 : Time) ≤ 0 + 12 * sp1.Δ ∧
    (∀ y ∈ (Set.univ : Set (Fin sp1.n)), ∀ k att, (tickRun N1 dg1).SignAt y k att →
      (tickRun N1 dg1).time k ≤ 12 → att.h ≤ 3) ∧
    (∀ x ∈ (Set.univ : Set (Fin sp1.n)), ∀ i ℓ C, AC.ToFGAt (tickRun N1 dg1).projAC x i ℓ C →
      12 ≤ (tickRun N1 dg1).time i →
      ∃ l ∈ AC.liveLocks sp1 ((tickRun N1 dg1).state x i).ac.locks ℓ.frame
          ((tickRun N1 dg1).time i),
        l.fast = true ∧ l.block = C.root ∧
        ∃ i' < i, ∃ B CV, AC.FastLockAt (tickRun N1 dg1).projAC x i' l.slot B CV ∧
          0 < (tickRun N1 dg1).time i' ∧ Anc ((tickRun N1 dg1).HonestBlocks Set.univ) C B) ∧
    (∀ y ∈ (Set.univ : Set (Fin sp1.n)), ∀ i, ∀ X ∈ ((tickRun N1 dg1).state y i).fg.tree,
      3 + 2 ≤ (((tickRun N1 dg1).state y i).fg.σ X.root).h →
      ∃ Y, ((tickRun N1 dg1).state y i).fg.Anc Y X ∧
        ∃ att ∈ Y.fgPayload, att.val ∈ (Set.univ : Set (Fin sp1.n)) ∧ att.h = 3 + 1) ∧
    ((12 : Time) < 16 ∧
      (∀ y ∈ (Set.univ : Set (Fin sp1.n)), ∀ k att, (tickRun N1 dg1).SignAt y k att →
        3 + 1 ≤ att.h → 16 ≤ (tickRun N1 dg1).time k) ∧
      (∀ y ∈ (Set.univ : Set (Fin sp1.n)), ∀ k src signed,
        (tickRun N1 dg1).CallAt y k (.fg (.attest src signed)) → (tickRun N1 dg1).time k = 16 →
        ((tickRun N1 dg1).state y k).fg.hmax ≤ 3 + 1) ∧
      (∀ y ∈ (Set.univ : Set (Fin sp1.n)), ∀ k att, (tickRun N1 dg1).SignAt y k att →
        (tickRun N1 dg1).time k = 16 → att.h ≤ 3 + 1) ∧
      ∀ E ∈ Healing.HighEntries (tickRun N1 dg1) Set.univ 3,
        (Store.namers sp1.toParams (Payload sp1.n) Set.univ (tickRun N1 dg1).projFG (16 - sp1.Δ)
          E).ncard < sp1.toParams.fg.q) := by
  have h := Healing.cut_and_reset sp1 (fun _ => v0) dg1 Set.univ (tickRun N1 dg1) 0 1
    tickRun_goldilocksRun (tickRun_healthy 0) (dg1_noColl _)
  rw [cutZ_zero, hz_zero, gbar_zero] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, fun x hx i ℓ C hto hi =>
    (h3 x hx i ℓ C hto hi).resolve_right fun ⟨_, _, hD, _⟩ => (nomatch hD), h4,
    h5 16 (by rw [← aZ_zero]; exact tickRun_isReset 0)⟩

end Consensus.Goldilocks.Witness.One

end
