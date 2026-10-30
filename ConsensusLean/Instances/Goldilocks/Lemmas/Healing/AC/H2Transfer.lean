module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Setting

public section

/-! # Goldilocks Healing: H.2, clean raw origins transfer, the drain, settled locks

workbench `h2-open-items.md`:
* §6.1 (with §§2–3 and §5's root-covered reads): a clean raw origin `(B, j)` is carried by every
  honest vote and honest proposal head of a later slot (`raw_origin_transfer`, open);
* §5, drain: a lock live at a slot `σ` with `t_σ ≥ t₀ + 2Θ` sits below a clean raw origin of its
  label (`h2_drain`, open);
* hence the locks are settled from `t₀ + 2Θ + 4Δ` (`h2_locks_settled`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g t₀ : Time}

/-- **§6.1, raw-origin transfer**: a clean raw origin `(B, j)` is carried by every honest vote
and every honest proposal head of a slot after `j` (by increasing duty label: the first transfer
of a fast target from its counted seats, §§2–3; of a slow target from its saved results; later
labels from the preceding honest batch; root-covered reads per §5). -/
theorem raw_origin_transfer (hI : InclusionRun tr H U g t₀) {B : Blk sp.n FGP} {j : Nat}
    (hB : CleanOrigin tr H t₀ B j) :
    VotesExtendAfter tr H U j B ∧ ProposalsExtendAfter tr H U j B := by
  sorry

/-- **§5, drain**: a lock stored at an honest node and live at a slot `σ` with `t_σ ≥ t₀ + 2Θ`
(`σ ≤ j + k` for its label `j`) sits below a clean raw origin of its label. -/
theorem h2_drain (hI : InclusionRun tr H U g t₀) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {l : Lock} (hl : l ∈ (tr.state y i).locks) {σ : Nat} (hσ : σ ≤ l.slot + sp.k)
    (hT : t₀ + 2 * Θ sp ≤ sp.ts σ) :
    ∃ B, (∃ L ∈ U, L.root = l.block ∧ Anc U L B) ∧ CleanOrigin tr H t₀ B l.slot := by
  sorry

/-- **Settled locks**: from `t₀ + 2Θ + 4Δ` on, every lock live at an honest node is carried by
every later honest duty. -/
theorem h2_locks_settled (hI : InclusionRun tr H U g t₀) :
    LocksSettled tr H U (t₀ + 2 * Θ sp + 4 * sp.Δ) := by
  have hr := hI.run.localRun
  rw [locksSettled_iff]
  intro y hy i hi l hl hlive L hL hLr
  have ht0 := hr.time_nonneg i
  have hσ : t₀ + 2 * Θ sp ≤ sp.ts (sp.slot (tr.time i)) := by
    have h1 : ¬ sp.ts ((sp.slot (tr.time i) : Nat) + 1 : Int) ≤ tr.time i := by
      rw [ts_le_iff_le_slot sp ht0]; omega
    have h2 : sp.ts ((sp.slot (tr.time i) : Nat) + 1 : Int) =
        sp.ts (sp.slot (tr.time i)) + 4 * sp.Δ := by
      simp only [SAParams.ts]; ring
    linarith [not_le.1 h1]
  obtain ⟨B, ⟨L', hL', hL'r, hLB⟩, hclean⟩ := h2_drain hI hy hl hlive hσ
  obtain rfl : L' = L := hr.coherent.1 hL' hL (hL'r.trans hLr.symm)
  obtain ⟨hv, hp⟩ := raw_origin_transfer hI hclean
  refine ⟨votesExtendAfter_iff.2 fun x hx j e he hs => ?_, proposalsExtendAfter_iff.2
    fun x hx j ℓ m d pay hc hcall ht hm hd =>
      hLB.trans (proposalsExtendAfter_iff.1 hp x hx j ℓ m d pay hc hcall ht hm hd)⟩
  obtain ⟨Hd, hHd, hHdr, hBHd⟩ := votesExtendAfter_iff.1 hv x hx j e he hs
  exact ⟨Hd, hHd, hHdr, hLB.trans hBHd⟩

end Consensus.Goldilocks.SA

end
