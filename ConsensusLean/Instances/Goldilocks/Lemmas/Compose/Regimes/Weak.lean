module
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Weak
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule

public section

/-! # Goldilocks milestone Regimes: R.6 (weak continuation), assembled over R.3 cut at `T`

`WeakStatements` (`Statements/Regimes/Weak`) from R.3's rows in the form that needs `Healthy` and
the ready-proposer premise only up to the heal point `T`: the four named open steps
`healed_safe_until`, `cross_nest_until`, `include_healed_until` and `grow_healed_until`, stated
over `WeakPremises` (the healing premises of R.3 cut at `T`, with `Sleepy` at `θ = ½` from `T`).
This is the recorded gap of R.6 (Statements/Regimes/Weak, "Open proof items"): H.4 and R.3 are
stated under `Healthy(g)` and `Prop⁺(G_p)` on the whole run, while `Weak` gives them only on
`[ḡ, T]`; after `T` nodes may sleep, so the continuation from `T` is a sleepy-regime argument from
the healed configuration at `T` (an R.1/R.2-style invariant started at `T`, not at genesis). Its
owner is to be assigned (consensus-lean#17).

For `healed_safe_until` the plan (consensus-lean#17, 2026-10-31) is the Sleepy record invariant
over a window starting at `s₀ = r_AC(a + T_b)` (a second pass of the Sleepy box, after
`SleepyInvariantUpTo`), from a base at `s₀`: (1) the live locks of labels `< s₀` are compatible with
the origins of labels `≥ s₀` (they expire by `t_{s₀+k} < a + T_b + (4k + 8)Δ ≤ T_heal ≤ T`, using
`a ≤ ḡ + 24Δ + 12C_HS`); (2) RecRet; (3) `Σ.F`, `Σ.J` and FG sources on the chain of those origins;
(4) their viability (`Inv(a + T_b)`, in `BridgeAt`); (5) every honest row held from `t_{s₀}` names
an entry on that chain or at or below the cut's `fc_root`. Part of the same until-`T` gap: (1) uses
ResetExistence's bound on `a` and H.2's drain, both stated under `Healthy(g)` on the whole run and
used here only up to `T`.

The four open steps keep R.3's conclusions; they differ from R.3 only in the premises (and, for
growth, the proposer recurrence from `T` instead of from `ḡ + 18Δ + 1`, as `WeakGrow`). R.6's rows
follow: `WeakSafe` and `WeakCrossNest` are the first two; `WeakInclude` is the third for proposals
at `τ ≥ T + 8Δ ≥ T`; `WeakGrow` is the fourth. -/

namespace Consensus.Goldilocks.Regimes

open SA (SAParams ReplayOrder Payload gbar)

/-! ## R.3 with `Healthy` and `Prop⁺` up to `T` (open; owner to be assigned) -/

/-- **R.3 `healedSafe` with the premises cut at `T`** (open). -/
theorem healed_safe_until : ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp a Tb T : Time),
    GoldilocksRun dg H tr → WeakPremises tr H dg g ΔF Gp a Tb T →
    ∀ t₁, ReadySafeOn tr H (catchUp sp) T t₁ := by
  sorry

/-- **R.3 `crossNest` with the premises cut at `T`** (open; the corrected form, #104). -/
theorem cross_nest_until : ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp a Tb T : Time),
    GoldilocksRun dg H tr → WeakPremises tr H dg g ΔF Gp a Tb T →
    ∀ t t' x y i j, T ≤ t → t ≤ t' → ReadPoint tr i t → ReadPoint tr j t' → Boundary tr x i →
      Boundary tr y j → ReadyAt tr H (catchUp sp) x t → ReadyAt tr H (catchUp sp) y t' →
      (t' = t → Compatible (tr.HonestBlocks H) (tr.state x i).fg.F (readAfter tr y j t')) ∧
      (t + sp.Δ ≤ t' → Anc (tr.HonestBlocks H) (tr.state x i).fg.F (readAfter tr y j t')) := by
  sorry

/-- **R.3 `includeHealed` with the premises cut at `T`** (open): R.3's conclusion for every
honest ready proposal at `τ ≥ T`, under `(U_all)` from `T`. -/
theorem include_healed_until : ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp a Tb T : Time),
    GoldilocksRun dg H tr → WeakPremises tr H dg g ΔF Gp a Tb T → UnanimousFrom tr H T →
    ∀ τ P, T ≤ τ → ReadyProposalAt tr H (catchUp sp) τ P →
      ∀ y t j, τ + 6 * sp.Δ ≤ t → ReadyAt tr H (catchUp sp) y t → CutAfter tr j t →
        Anc (tr.HonestBlocks H) P (readAfter tr y j t) := by
  sorry

/-- **R.3 `growHealed` with the premises cut at `T`** (open), with the proposer recurrence from
`T`. -/
theorem grow_healed_until : ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp a Tb T : Time) (k : Nat),
    GoldilocksRun dg H tr → WeakPremises tr H dg g ΔF Gp a Tb T → 1 ≤ k →
    UnanimousWithin tr H T (4 * k * sp.Δ) →
    ∀ t, T ≤ t → ProposerRecurrence tr H (catchUp sp) k T (t + (4 * k + 6) * sp.Δ) →
      (∃ v, ReadyAt tr H (catchUp sp) v (t + (4 * k + 6) * sp.Δ)) →
      ∃ τ P, t < τ ∧ ReadyProposalAt tr H (catchUp sp) τ P ∧
        (∀ y j, ReadyAt tr H (catchUp sp) y (t + (4 * k + 6) * sp.Δ) →
          CutAfter tr j (t + (4 * k + 6) * sp.Δ) →
          Anc (tr.HonestBlocks H) P (readAfter tr y j (t + (4 * k + 6) * sp.Δ))) ∧
        ∀ x jx, ReadyAt tr H (catchUp sp) x t → CutAfter tr jx t →
          ¬ Anc (tr.HonestBlocks H) P (readAfter tr x jx t) ∧
          ∀ y j, ReadyAt tr H (catchUp sp) y (t + (4 * k + 6) * sp.Δ) →
            CutAfter tr j (t + (4 * k + 6) * sp.Δ) →
            Anc (tr.HonestBlocks H) (readAfter tr x jx t)
              (readAfter tr y j (t + (4 * k + 6) * sp.Δ)) := by
  sorry

/-! ## R.6 -/

/-- **R.6, `weakSafe`.** -/
theorem weak_safe : WeakSafe := healed_safe_until

/-- **R.6, `weakCrossNest`.** -/
theorem weak_cross_nest : WeakCrossNest := cross_nest_until

/-- **R.6, `weakInclude`**: R.3's inclusion cut at `T`, for proposals at `τ ≥ T + 8Δ`. -/
theorem weak_include : WeakInclude := by
  intro sp ro dg H tr g ΔF Gp a Tb T hrun hw hu τ P hτ hP y t j ht hy hj
  have hΔ := sp.toParams.hΔ
  exact include_healed_until sp ro dg H tr g ΔF Gp a Tb T hrun hw hu τ P (by linarith) hP y t j ht
    hy hj

/-- **R.6, `weakGrow`.** -/
theorem weak_grow : WeakGrow := grow_healed_until

/-- **Milestone Regimes, the weak-continuation rows (R.6)**, over the four open steps above. -/
theorem weak_statements : WeakStatements :=
  ⟨weak_safe, weak_cross_nest, weak_include, weak_grow⟩

end Consensus.Goldilocks.Regimes

end
