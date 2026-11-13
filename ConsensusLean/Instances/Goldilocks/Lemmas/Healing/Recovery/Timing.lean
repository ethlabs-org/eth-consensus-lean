module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Recovery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Reset
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Recovery: timing and the selected pattern stretch (C0)

The arithmetic and timing shared by the C1.3 proof (acquisition, old-entry crossing, two-window
service) under exactly `PatternPremises`; no stronger timeout or `Δ ≤ Δ_F` is assumed.

* `pattern_reset`: a reset `a` with its whole-run premises, `a ≤ ḡ + Z` (HR.3,
  `reset_existence`) and `drainTime a ≤ R*`.
* `pattern_stretch_after_reset`: for every request `t ≥ R*`, the `UPat` stretch start `v` with
  `t ≤ t_v ≤ t + 4Δ(W + 1)`, after the drain of a bounded reset, with the stretch clause of
  `UPat` unchanged.
* The ceiling sandwiches `slotsCeil_bounds`, `oldSlots_bounds`; the timeout bound
  `timeout_add_three_le_oldSlots`; and the slot budget
  `recovery_slot_budget` (`s ≤ v + b₀`, `u ≤ s + r_old` put the old-entry crossing and two
  windows of `c_F + k_F` slots inside the stretch `[v, v + M)`).
* `pattern_Gp_nonneg`: `0 ≤ G_p` from `Prop⁺(G_p)`. -/

namespace Consensus.Goldilocks.Healing.Recovery

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams}

/-! ## Ceilings -/

/-- **The slot ceiling sandwich**: for `x ≥ 0`, `x ≤ 4Δ⌈x/4Δ⌉ < x + 4Δ`. -/
theorem slotsCeil_bounds {x : Time} (hx : 0 ≤ x) :
    x ≤ 4 * sp.Δ * (slotsCeil sp x : Time) ∧
      4 * sp.Δ * (slotsCeil sp x : Time) < x + 4 * sp.Δ := by
  have hD : (0 : Time) < 4 * sp.Δ := by have := sp.toParams.hΔ; linarith
  set q := (x + 4 * sp.Δ - 1) / (4 * sp.Δ) with hq
  have hq0 : 0 ≤ q := Int.ediv_nonneg (by linarith) hD.le
  have hcast : (slotsCeil sp x : Time) = q := by
    change (((x + 4 * sp.Δ - 1) / (4 * sp.Δ)).toNat : Time) = q
    exact Int.toNat_of_nonneg hq0
  have hlo : 4 * sp.Δ * q ≤ x + 4 * sp.Δ - 1 := by
    have := Int.ediv_mul_le (x + 4 * sp.Δ - 1) hD.ne'
    rw [← hq] at this; linarith
  have hhi : x + 4 * sp.Δ - 1 < 4 * sp.Δ * (q + 1) := by
    have := Int.lt_ediv_add_one_mul_self (x + 4 * sp.Δ - 1) hD
    rw [← hq] at this; linarith
  rw [hcast]
  have h1 : x - 1 < 4 * sp.Δ * q := by linarith
  exact ⟨Int.sub_one_lt_iff.mp h1, by linarith⟩

/-- **The old-entry budget** `r_old = ⌈L_old/4Δ⌉ + 1`: `4Δ(r_old − 1)` is the ceiling. -/
theorem oldSlots_bounds {ΔF Gp : Time} (hΔF : 0 ≤ ΔF) (hGp : 0 ≤ Gp) :
    L_old sp ΔF Gp ≤ 4 * sp.Δ * ((oldSlots sp ΔF Gp : Time) - 1) ∧
      4 * sp.Δ * ((oldSlots sp ΔF Gp : Time) - 1) < L_old sp ΔF Gp + 4 * sp.Δ := by
  have hΔ := sp.toParams.hΔ
  have hδ : (0 : Time) ≤ sp.toParams.δt := Nat.cast_nonneg _
  have h := slotsCeil_bounds (sp := sp) (x := L_old sp ΔF Gp)
    (by simp only [L_old]; linarith [mul_nonneg hδ hΔ.le])
  have he : ((oldSlots sp ΔF Gp : Nat) : Time) - 1 = (slotsCeil sp (L_old sp ΔF Gp) : Time) := by
    simp only [oldSlots]; push_cast; ring
  rw [he]; exact h

/-- **The timeout fits the old-entry budget**: `δ_t + 3 ≤ r_old`, since `L_old > 4Δ(δ_t + 1)`. -/
theorem timeout_add_three_le_oldSlots {ΔF Gp : Time} (hΔF : 0 ≤ ΔF) (hGp : 0 ≤ Gp) :
    sp.toParams.δt + 3 ≤ oldSlots sp ΔF Gp := by
  have hΔ := sp.toParams.hΔ
  have h := (oldSlots_bounds (sp := sp) hΔF hGp).1
  simp only [L_old] at h
  have hlt : 4 * sp.Δ * ((sp.toParams.δt : Time) + 1) <
      4 * sp.Δ * ((oldSlots sp ΔF Gp : Time) - 1) := by linarith
  have := lt_of_mul_lt_mul_left hlt (by linarith : (0 : Time) ≤ 4 * sp.Δ)
  have : ((sp.toParams.δt + 2 : Nat) : Time) < (oldSlots sp ΔF Gp : Time) := by
    push_cast; linarith
  exact_mod_cast this

/-! ## The slot budget -/

/-- **The recovery slot budget**: with the acquired slot `s ≤ v + b₀` and the crossed entry
`u ≤ s + r_old`, the crossing budget ends inside the stretch, and so do two windows of
`c_F + k_F` slots after `u`. -/
theorem recovery_slot_budget {ΔF Gp : Time} {cF kF M v s u : Nat}
    (hM : Mstar sp ΔF Gp cF kF ≤ M)
    (hs : s ≤ v + acqSlots sp Gp) (hu : u ≤ s + oldSlots sp ΔF Gp) :
    s + oldSlots sp ΔF Gp < v + M ∧ u + 2 * (cF + kF) + 1 ≤ v + M := by
  simp only [Mstar] at hM; omega

/-! ## The pattern premises -/

variable {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF Gp : Time} {W M cF kF : Nat}

/-- `Prop⁺(G_p)` forces `G_p ≥ 0`. -/
theorem pattern_Gp_nonneg (hp : PatternPremises tr H proposer dg g ΔF Gp W M cF kF) :
    0 ≤ Gp := by
  obtain ⟨s, k, B, -, h₁, h₂, -⟩ := hp.prop (gbar g) le_rfl
  linarith

private theorem pattern_ΔF_pos (hp : PatternPremises tr H proposer dg g ΔF Gp W M cF kF) :
    0 < ΔF :=
  hp.shared.healthy.1.deltaF

private theorem Zreset_nonneg (hp : PatternPremises tr H proposer dg g ΔF Gp W M cF kF) :
    0 ≤ Zreset sp ΔF Gp := by
  have hΔ := sp.toParams.hΔ
  have hk : (0 : Time) ≤ sp.k := Nat.cast_nonneg _
  have hδ : (0 : Time) ≤ sp.toParams.δt := Nat.cast_nonneg _
  have := pattern_ΔF_pos hp
  have := pattern_Gp_nonneg hp
  simp only [Zreset, C_HS, D_HS]
  linarith [mul_nonneg hk hΔ.le, mul_nonneg hΔ.le hδ]

/-- The drain of a reset `a ≥ 0` ends by `a + (8k + 20)Δ`. -/
private theorem drainTime_le {a : Time} (ha : 0 ≤ a) :
    drainTime sp a ≤ a + (8 * (sp.k : Time) + 20) * sp.Δ := by
  have hs := (SA.ts_le_iff_le_slot sp ha (sp.slot a : Int)).2 le_rfl
  rw [drainTime_eq]
  simp only [SA.SAParams.ts] at hs ⊢
  push_cast
  linarith

/-- A reset is at a cut, so at a time `≥ 0`. -/
private theorem reset_nonneg (hrun : GoldilocksRun proposer dg H tr) {a : Time}
    (ha : IsReset tr H g a) : 0 ≤ a := by
  obtain ⟨y, -, k, -, -, -, hk⟩ := ha.1
  exact hk ▸ hrun.time_nonneg k

/-- **The bounded reset of the pattern premises** (HR.3): a reset `a` with its whole-run
premises, `a ≤ ḡ + Z`, and its drain by `R*`. -/
theorem pattern_reset
    (hrun : GoldilocksRun proposer dg H tr)
    (hp : PatternPremises tr H proposer dg g ΔF Gp W M cF kF) :
    ∃ a, ResetPremises tr H proposer dg g ΔF a ∧
      a ≤ gbar g + Zreset sp ΔF Gp ∧ drainTime sp a ≤ Rstar sp g ΔF Gp := by
  have hr := reset_existence sp ro proposer dg H tr g ΔF Gp hrun hp.shared hp.catchPremise hp.prop
  obtain ⟨a, ha⟩ := hr.2.2.1
  have hab : a ≤ gbar g + Zreset sp ΔF Gp := by
    have h1 := hr.2.2.2.1 a ha
    have h2 := hr.2.2.2.2.1
    simp only [Zreset]; linarith
  refine ⟨a, ⟨hrun, hp.shared.healthy, hp.shared.noColl, ha, hp.shared.stock⟩, hab, ?_⟩
  have := drainTime_le (sp := sp) (reset_nonneg hrun ha)
  simp only [Rstar]; linarith

/-- **The selected pattern stretch after a bounded reset** (C0): for a request `t ≥ R*`, the
`UPat` stretch at `t` starts at `v` with `t ≤ t_v ≤ t + 4Δ(W + 1)`, after the drain of the reset,
and its clause is `UPat`'s, unchanged. -/
theorem pattern_stretch_after_reset
    (hrun : GoldilocksRun proposer dg H tr)
    (hp : PatternPremises tr H proposer dg g ΔF Gp W M cF kF)
    {a t : Time} (ha : IsReset tr H g a)
    (hab : a ≤ gbar g + Zreset sp ΔF Gp)
    (ht : Rstar sp g ΔF Gp ≤ t) :
    ∃ v : Nat, t ≤ sp.ts v ∧ sp.ts v ≤ t + 4 * sp.Δ * ((W : Time) + 1) ∧
      drainTime sp a ≤ sp.ts v ∧
      ∀ s, v ≤ s → s < v + M →
        ∃ (k : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))),
          ReadyProposal tr H proposer (proposer s) k s B ∧
          ∀ y i, Compose.RunEntry tr H y i B →
            ∃ (w : Fin sp.n) (kw : Nat) (Q : SA.Blk sp.n (List (FG.Att sp.n))),
              ReadyProposal tr H proposer w kw Q.slot Q ∧
              s + cF ≤ Q.slot ∧ Q.slot ≤ s + cF + kF ∧
              ∃ Pr, Q.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) B Pr := by
  have hΔ := sp.toParams.hΔ
  have hk : (0 : Time) ≤ sp.k := Nat.cast_nonneg _
  have hZ := Zreset_nonneg hp
  have hgt : gbar g ≤ t := by simp only [Rstar] at ht; linarith [mul_nonneg hk hΔ.le]
  obtain ⟨v, hv₁, hv₂, hv⟩ := hp.pattern t hgt
  refine ⟨v, hv₁, hv₂, ?_, hv⟩
  have := drainTime_le (sp := sp) (reset_nonneg hrun ha)
  simp only [Rstar] at ht
  linarith

end Consensus.Goldilocks.Healing.Recovery

end
