module
public import ConsensusLeanTest.Goldilocks.Runs.OneValidator.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Reset
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
@[expose] public section

/-! # The one-validator tick run through the run-level healing statements

On the one-validator tick run of `Goldilocks/Runs/OneValidator/Premises` (`n = 1`, `f = 0`, `Δ = 1`,
`k = δ_t = 2`, `t_s = 4s`, a tick at every time `t ≥ 0`, cut `i` at time `⌊i/8⌋`, no restart), with
`g = 0`, `Δ_F = 1`, `κ = 2Δ`, `G_p = 4` and `T_b = 0`, the proved run-level healing statements HR.1
(`CutAndReset`), HR.3 (`ResetExistence`) and HR.4 (`HeightScopedRetention`) are applied to the run,
their premises met outright.

* **The parameters** (computed from the definitions): `ḡ = 0` (`gbar_zero`), `c_z = 12`
  (`cutZ_zero`), `H_z = 3` (`hz_zero`), `a_z = 16` (`aZ_zero`), `Θ = 12` (`theta_sp1`),
  `C_HS = 86` (`C_HS_sp1`), `A_HS = 173` (`A_HS_sp1`).
* (a) `healing_premises`: `GoldilocksRun`, `HSShared` (with `Healthy(0)` and `NoColl`),
  `Catch(2Δ)` and `Prop⁺(4)`. `reset_bundle`: `16` is the reset `a_z` (`IsReset`) and H.3 (c)'s
  bridge `BridgeAt` holds at `a_z + T_b = 16`.
* (b) `tickRun_cutAndReset` (HR.1), `tickRun_resetExistence` (HR.3, `a_z ≤ 1056`) and
  `tickRun_retention` (HR.4 at `a_z = 16`): the conclusions read at these parameters.

**Limitation: `Geo` is vacuous here.** The `Geo` part of H.3 (c)'s bridge `BridgeAt`, in
`reset_bundle` (`Geo(P)` for an honest proposal whose proposal and votes lie in one settled
effective phase), holds vacuously on the tick run (`tickRun_bridgeAt`, `not_inSettledPhase`): the
own block, accepted at `t_p` between `ac_proposal` and the vote, raises the frontier `h_max`, so
no proposal of a slot `p ≥ 2` and its votes lie in one settled effective phase. So this witness
does not exercise `Geo`. With `n = 1` and `f = 0` this shows the premises consistent, not met
with faults. -/

namespace Consensus.Goldilocks.Witness.One

open SA Node ChainFrame

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

/-- `Θ = 4(k + 1)Δ = 12`. -/
theorem theta_sp1 : SA.Θ sp1 = 12 := by decide

/-- `C_HS = (8k + 49 + 4δ_t)Δ + Δ_F + 3G_p = 86` at `Δ_F = 1`, `G_p = 4`. -/
theorem C_HS_sp1 : Healing.C_HS sp1 1 4 = 86 := by decide

/-- `A_HS = 2C_HS + Δ = 173` at `Δ_F = 1`, `G_p = 4`. -/
theorem A_HS_sp1 : Healing.A_HS sp1 1 4 = 173 := by decide

/-! ## The premise bundles -/

/-- (a) **The premises of HR.3** at `g = 0`, `Δ_F = 1`, `κ = 2Δ`, `G_p = 4`: a Goldilocks
run with the HS shared premises (`Healthy(0)`, `NoColl`, genesis root, no restart, the timeout
bound), `Catch(2Δ)` and `Prop⁺(4)`. -/
theorem healing_premises :
    GoldilocksRun (sp := sp1) (ro := ro1) (fun _ => v0) dg1 Set.univ (tickRun N1 dg1) ∧
      Healing.HSShared (tickRun N1 dg1) Set.univ (SA.CommitteeDict.full sp1.n) dg1 0 1 ∧
      Healing.CatchRun (tickRun N1 dg1) Set.univ 0 (2 * sp1.Δ) ∧
      Healing.PropPlus (tickRun N1 dg1) Set.univ (fun _ => v0) 0 4 :=
  ⟨tickRun_goldilocksRun, tickRun_hsShared 0, tickRun_catch 0 _ (by decide),
    tickRun_propPlus 0 4 le_rfl⟩

/-- (a) **The reset and the bridge** at `g = 0`: `16` is the reset `a_z` and H.3 (c)'s bridge holds
at `a_z` with `T_b = 0` (its `Geo` part vacuously, `not_inSettledPhase`). -/
theorem reset_bundle :
    Healing.IsReset (tickRun N1 dg1) Set.univ 0 16 ∧
      Healing.BridgeAt (tickRun N1 dg1) Set.univ (fun _ => v0) 0 16 0 := by
  rw [← aZ_zero]
  exact ⟨tickRun_isReset 0, tickRun_bridgeAt 0 _ 0 (by rw [add_zero]; exact aZ_nonneg 0)⟩

/-! ## The statements on the run -/

/-- (b) **HR.1 on the tick run** at `g = 0`, `Δ_F = 1`, with `c_z = 12` and `H_z = 3`. Part (a):
every honest attestation signed at or before `12` has height `≤ 3`, and from `12` on `ac_to_fg`
returns live fast locks; part (b): a chain of state height `≥ 5` carries an honest attestation of
height `4`; part (c), at the reset `a_z = 16`: `12 < 16`, the honest pairs of height `≥ 4` are
signed from `16` on, the rows signed at `16` have height `≤ 4`, and the first clause of (K1)
holds with `T₀ = 16 − Δ = 15`. -/
theorem tickRun_cutAndReset :
    (12 : Time) ≤ 0 + 12 * sp1.Δ ∧
    (∀ y ∈ (Set.univ : Set (Fin sp1.n)), ∀ k att, (tickRun N1 dg1).SignAt y k att →
      (tickRun N1 dg1).time k ≤ 12 → att.h ≤ 3) ∧
    (∀ x ∈ (Set.univ : Set (Fin sp1.n)), ∀ i ℓ C, SA.ToFGAt (tickRun N1 dg1).projAC x i ℓ C →
      12 ≤ (tickRun N1 dg1).time i →
      ∃ l ∈ SA.liveLocks sp1 ((tickRun N1 dg1).state x i).ac.locks ℓ.frame
          ((tickRun N1 dg1).time i),
        l.fast = true ∧ l.block = C.root ∧
        ∃ i' < i, ∃ B CV, SA.FastLockAt (tickRun N1 dg1).projAC x i' l.slot B CV ∧
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
  have h := Healing.cut_and_reset sp1 ro1 (fun _ => v0) dg1 Set.univ (tickRun N1 dg1) 0 1
    tickRun_goldilocksRun (tickRun_healthy 0) (dg1_noColl _)
  rw [cutZ_zero, hz_zero, gbar_zero] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5 16 reset_bundle.1⟩

/-- (b) **HR.3 on the tick run** at `g = 0`, `Δ_F = 1`, `G_p = 4`: `8 < c_z = 12`; HS.0 from
`12` on; `Producer(A_HS)` with `A_HS = 173`; the reset exists, and every reset is at most
`c_z + 6(Δ + A_HS) = 1056 = ḡ + 24Δ + 12C_HS`, with `C_HS = 86`. -/
theorem tickRun_resetExistence :
    ((0 : Time) + 8 * sp1.Δ < 12 ∧
      ∀ u, 12 ≤ u → ∀ j j', Healing.FirstCutAfter (tickRun N1 dg1) j u →
        (tickRun N1 dg1).FirstCutFrom j' (u + sp1.Δ) →
        Healing.PhaseChanged (tickRun N1 dg1).projFG Set.univ j j' ∨
          Healing.SettledAt (tickRun N1 dg1) Set.univ 0 (2 * sp1.Δ) (u + sp1.Δ)) ∧
    (∀ w, Healing.SettledAt (tickRun N1 dg1) Set.univ 0 (2 * sp1.Δ) w → ∀ j j',
      (tickRun N1 dg1).FirstCutFrom j w → Healing.FirstCutAfter (tickRun N1 dg1) j' (w + 173) →
      Healing.PhaseChanged (tickRun N1 dg1).projFG Set.univ j j') ∧
    (∃ a, Healing.IsReset (tickRun N1 dg1) Set.univ 0 a) ∧
    (∀ a, Healing.IsReset (tickRun N1 dg1) Set.univ 0 a → a ≤ 1056) ∧
    (1056 : Time) ≤ 0 + 24 * sp1.Δ + 12 * 86 ∧
    Healing.C_HS sp1 1 4 = 86 := by
  obtain ⟨⟨h1, h2⟩, h3, h4, h5, h6, -, h8⟩ := Healing.reset_existence sp1 ro1 (fun _ => v0) dg1
    Set.univ (tickRun N1 dg1) (SA.CommitteeDict.full sp1.n) 0 1 4
    (by rw [SA.committeeStart_full]; exact tickRun_goldilocksRun) (tickRun_hsShared 0)
    (tickRun_catch 0 _ (by decide)) (tickRun_propPlus 0 4 le_rfl)
  rw [cutZ_zero] at h1 h2 h5 h6
  simp only [gbar_zero, A_HS_sp1, C_HS_sp1] at h1 h3 h5 h6
  refine ⟨⟨h1, h2⟩, h3, h4, fun a ha => (h5 a ha).trans (le_of_eq ?_), h6, C_HS_sp1⟩
  decide

/-- (b) **HR.4 on the tick run** at `g = 0`, `Δ_F = 1`: (R1)–(R4) hold for the reset `a_z = 16`,
at the heights `≥ H_z + 1 = 4`. -/
theorem tickRun_retention : Healing.RetentionAt (tickRun N1 dg1) Set.univ 0 16 :=
  Healing.height_scoped_retention sp1 ro1 (fun _ => v0) dg1 Set.univ (tickRun N1 dg1)
    (SA.CommitteeDict.full sp1.n) 0 1 (by rw [SA.committeeStart_full]; exact tickRun_goldilocksRun)
    (tickRun_healthy 0) (dg1_noColl _) (tickRun_hsShared 0).committee (tickRun_hsShared 0).twoK
    16 reset_bundle.1

end Consensus.Goldilocks.Witness.One

end
