module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: the provenance half of the drain at a formation width

Over a run at a write mode `wm` (`StandaloneRunU wm`), a lock that an honest node stores, live at
a slot `σ` with `t_σ ≥ ḡ + 4(k + w)Δ` (`w = wm.width ≥ 1`, `σ ≤ j + k` for its label `j`), sits
below a good origin of width `w` of its label (`drain_provenanceM`, `GoodOriginW`): its label is
at least `σ − k`, so a fast origin (`fast_lock_provenanceU`) has `t_j ≥ ḡ + 4wΔ ≥ ḡ + 4Δ` and a
slow one (`slow_lock_provenanceM`, of width `w`) has `t_{j−w+1} ≥ ḡ + 4Δ`. At `w = k` this is
the provenance half of `drain_tight` (`goodOriginW_k`). It is provenance only: the transfer of a
good origin of width `w < k` is not proved. -/

namespace Consensus.Goldilocks.SA

variable {wm : SA.WriteMode}

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time} {proposer : Nat → Fin sp.n}

/-- **The drain's provenance at width `wm.width`**: a lock that an honest node stores, live at a
slot `σ` with `t_σ ≥ ḡ + 4(k + w)Δ` for the width `w = wm.width ≥ 1`, sits below a good origin
of width `w` of its label. -/
theorem drain_provenanceM
    {u : Nat → Set Lock} (hS : StandaloneRunU wm u tr H U proposer g) (hw1 : 1 ≤ wm.width)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {l : Lock}
    (hl : l ∈ (tr.state y i).locks) {σ : Nat} (hσ : σ ≤ l.slot + sp.k)
    (hT : gbar g + 4 * ((sp.k : Time) + wm.width) * sp.Δ ≤ sp.ts σ) :
    ∃ B, (∃ L ∈ U, L.root = l.block ∧ Anc U L B) ∧ GoodOriginW wm.width tr H g B l.slot := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  simp only [SAParams.ts] at hT
  have hlk := mul_nonneg hΔ.le (show (0 : Int) ≤ l.slot + sp.k - σ by omega)
  cases hf : l.fast
  · obtain ⟨j, -, B, hsl, hLB⟩ := slow_lock_provenanceM hr
      (fun _ => SA.voteStart_initial _) hy i l hl hf
    refine ⟨B, hLB, goodOriginW_iff.2 (Or.inr ⟨y, hy, j, hsl, ?_⟩)⟩
    simp only [SAParams.ts]
    linarith
  · obtain ⟨j, -, B, CV, hfl, hLB⟩ := fast_lock_provenanceU hr
      (fun _ => voteStart_initial _) hy i l hl hf
    refine ⟨B, hLB, goodOriginW_iff.2 (Or.inl ⟨y, hy, j, CV, hfl, ?_⟩)⟩
    have := mul_nonneg hΔ.le (show (0 : Int) ≤ wm.width - 1 by omega)
    simp only [SAParams.ts]
    linarith

end Consensus.Goldilocks.SA

end
