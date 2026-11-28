module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Boundaries
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.CallLag
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The finite reset record with the high-source cover

`resetPremisesUpTo_of_reset_cover_at`: the finite reset record through `b` from the same raw
premises as `resetPremisesUpTo_of_reset_at`, with `deepCover` built inside. When `b` is inside the
deep quarantine `c_z + 4DΔ`, the quarantine arm; otherwise the record restricted to
`T = c_z + 4DΔ` is inside it (its snapshot is the first cut after `c_z`, by `T` since the honest
nodes are awake; the reset `a < drainTime a ≤ T`), and the cover supplier `hcover`
(`healthy_high_source_cover_at`, `Healing/Frontier`) turns that record into the high-source cover
through `b`. The supplier is a premise, so this module stays below the frontier. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {hold : Time}

/-- **The finite reset record through `b` with the high-source cover.** The raw premises of
`resetPremisesUpTo_of_reset_at`, the drain of `a` at least `4Δ` before the end `c_z + 4DΔ` of
the deep quarantine, and a cover supplier: from a record up to
`T ≤ b` inside the quarantine with the drain `4Δ` before `T`, the high-source cover through
`b`. -/
theorem resetPremisesUpTo_of_reset_cover_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot (Generic.dictOfTime sp cm)))
    (hnc : Compose.NoCollRun dg tr) {g ΔF a b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hreset : IsReset tr H g a) (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hsnapshot : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g) ∧ tr.time k ≤ b)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartUpTo tr H (gbar g) b)
    (hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time)) (hH : (H b).Nonempty)
    (hfacts : Compose.Growing.CommitteeFacts tr H (Generic.dictOfTime sp cm))
    (hβ : βK ≤ 1 / 2) (hpos : 0 < sp.committeeSize)
    (hcf : Generic.CommitteeFaultsUpTo βK cm H g b)
    (hdrain : ∀ D, sp.deepDepth = some D →
      drainTime sp a + 4 * sp.Δ ≤ cutZ sp.toParams g + 4 * D * sp.Δ)
    (hcover : ∀ T, ResetPremisesUpTo tr H proposer dg g ΔF a T cm βK hold →
      (∀ D, sp.deepDepth = some D → T ≤ cutZ sp.toParams g + 4 * D * sp.Δ) →
      drainTime sp a + 4 * sp.Δ ≤ T → T ≤ b → HighSourceCover tr H g a b) :
    ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold := by
  refine resetPremisesUpTo_of_reset_at hrun hnc hsvc hawake hf hreset hab hsnapshot hcatch hnr hΔF
    hH hfacts hβ hpos hcf fun D hD => ?_
  rcases le_or_gt b (cutZ sp.toParams g + 4 * D * sp.Δ) with hbq | hqb
  · exact Or.inl hbq
  set T := cutZ sp.toParams g + 4 * D * sp.Δ with hT
  have hΔ := sp.toParams.hΔ
  have hdT := hdrain D hD
  have haT : a ≤ T := by linarith [lt_drainTime (sp := sp) ha0]
  have hTq : ∀ D', sp.deepDepth = some D' → T ≤ cutZ sp.toParams g + 4 * D' * sp.Δ := by
    intro D' hD'
    obtain rfl : D = D' := Option.some_injective _ (hD.symm.trans hD')
    exact le_rfl
  have hZT : cutZ sp.toParams g + sp.Δ ≤ T := by
    obtain ⟨k, hk, -⟩ := hsnapshot
    have := lt_drainTime (sp := sp) ha0
    have := cutZ_lt_reset_of_snapshot_at hrun hnc ⟨k, hk⟩ hreset
    linarith
  -- the snapshot at `T`: the first cut after `c_z`, within `Δ` of it (the honest nodes at `T` are
  -- awake on `[ḡ, T]`), not `b`'s snapshot bound
  have hT0 : 0 ≤ T := by linarith [Healing.lt_cutZ sp g, AC.gbar_nonneg g]
  have hHT : (H T).Nonempty := hH.mono (hrun.antitone hqb.le)
  obtain ⟨k, hk, hkT⟩ := Healing.snapshot_of_awake (hrun.upTo hT0).toLocalRun
    (fun y hy t hg ht => ⟨hawake y t (hrun.antitone ht hy) hg (ht.trans hqb.le), ht⟩) hHT hZT
  have hpT : ResetPremisesUpTo tr H proposer dg g ΔF a T cm βK hold :=
    resetPremisesUpTo_of_reset_at hrun hnc (hsvc.restrict hqb.le)
      (fun y t hy hg ht => hawake y t hy hg (ht.trans hqb.le))
      (fun t h0 ht => hf t h0 (ht.trans hqb.le)) hreset haT ⟨k, hk, hkT⟩ hcatch
      (noRestartUpTo_iff.2 fun y k hy hk hkT =>
        noRestartUpTo_iff.1 hnr y k hy hk (hkT.trans hqb.le))
      hΔF (hH.mono (hrun.antitone hqb.le)) hfacts hβ hpos
      (fun t d h1 h2 h3 h4 hne => hcf t d h1 (h2.trans hqb.le) h3 (h4.trans hqb.le) hne)
      fun D' hD' => Or.inl (hTq D' hD')
  exact Or.inr (hcover T hpT hTq hdT hqb.le)

end Consensus.Goldilocks.Healing.Growing

end
