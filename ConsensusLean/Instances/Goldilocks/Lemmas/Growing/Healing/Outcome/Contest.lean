module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.LeftEntry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.High
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Records

public section

/-! # High contests excluded using own-write origin comparability -/

namespace Consensus.Goldilocks.Healing.Growing.Outcome

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

private theorem entry_root_eq_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {z : Fin sp.n} {m : Nat}
    (hz : z ∈ H (tr.time m))
    {C Z₁ Z₂ : SA.Blk sp.n (List (FG.Att sp.n))} (hC : C ∈ (tr.state z m).fg.tree)
    (h₁ : Anc (tr.HonestBlocksAt H) Z₁ C) (h₂ : Anc (tr.HonestBlocksAt H) Z₂ C)
    (hh : ((tr.state z m).fg.σ Z₁.root).h = ((tr.state z m).fg.σ Z₂.root).h)
    (hT₁ : ((tr.state z m).fg.σ Z₁.root).Th = Z₁.root)
    (hT₂ : ((tr.state z m).fg.σ Z₂.root).Th = Z₂.root) : Z₁.root = Z₂.root := by
  have ht := hrun.time_nonneg m
  have hm : ∀ q < m, tr.time q ≤ tr.time m := fun q hq => hrun.time_mono hq.le
  have hr := fg_reachable_at hrun ht hm hz
  rcases SA.anc_total (Compose.Growing.honest_blocks_coherent hrun hnc) h₁ h₂ with h | h
  · have := Healing.Th_eq_of_anc hr (store_anc_of_honest_anc_at hrun hnc ht hm hz h
      (mem_of_honest_anc_at hrun hnc ht hm hz h₂ hC)) hh.symm
    rw [← hT₁, ← hT₂, this]
  · have := Healing.Th_eq_of_anc hr (store_anc_of_honest_anc_at hrun hnc ht hm hz h
      (mem_of_honest_anc_at hrun hnc ht hm hz h₁ hC)) hh
    rw [← hT₁, ← hT₂, this]

/-- Earlier origins rule out a high contest at a reader's honest cut.
The sole pending dependency is the kernel's frozen origin-comparability boundary. -/
theorem no_high_contest_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} {i : Nat} (hpH : p ∈ H (tr.time i)) (hib : tr.time i ≤ b) :
    ¬ ((tr.state p i).fg.Contest ∧ HZ tr H g + 2 ≤ (tr.state p i).fg.hmax) := by
  have ht := hp.run.time_nonneg i
  have hi : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hp.run.time_mono hq.le
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hreach := fg_reachable_at hp.run ht hi hpH
  have hsub : (tr.state p i).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨p, i, tr.time i, ht, hi, hpH, h⟩
  have hq : (H (tr.time i))ᶜ.ncard < sp.toParams.fg.q := by
    have h3 := hp.faults (tr.time i) ht hib
    have hn := sp.toParams.hn
    change (H (tr.time i))ᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    change 3 * (H (tr.time i))ᶜ.ncard ≤ sp.toParams.n - 1 at h3
    omega
  rintro ⟨⟨hmj, C, hC, _, hCh, hJC⟩, hmax⟩
  obtain ⟨_, hJm, _, ⟨Bj, hBj, hBjJ, hBjhj⟩, _⟩ := Store.cache_invariants _ _ _ _ hreach
  obtain ⟨EJ, hEJ, hEJr, hEJB, hcase⟩ := Store.J_entry_of_reachable hreach hBj
  obtain rfl : EJ = (tr.state p i).fg.J := hU.1 (hsub hEJ) (hsub hJm) (hEJr.trans hBjJ)
  rcases hcase with hg | ⟨hJh, hJT⟩
  · exact hJC (hg ▸ (Store.accepted_tree _ _ _ _ hreach).2.2.2 C hC)
  obtain ⟨_, _, _, _, v₂, _, d₂, hd₂, _, _, r₂, hr₂, l₂, O₂, ho₂, hJO⟩ :=
    left_entry_origin_at (g := g) hp.run hp.noColl ht hi hpH hq hJm hJT
      (by omega) hEJB (by have := Store.hj_lt_h hreach hBj; omega)
  obtain ⟨EC, hEC, hECC, hECh, hECT⟩ := Healing.entry_at_height hreach hC
    (h := (tr.state p i).fg.hj) (by omega) (by omega)
  obtain ⟨_, _, _, _, v₁, _, d₁, hd₁, _, _, r₁, hr₁, l₁, O₁, ho₁, hECO⟩ :=
    left_entry_origin_at (g := g) hp.run hp.noColl ht hi hpH hq hEC hECT
      (by omega) hECC (by omega)
  have upper : ∃ z m W, z ∈ H (tr.time m) ∧ W ∈ (tr.state z m).fg.tree ∧
      Anc (tr.HonestBlocksAt H) O₁ W ∧ Anc (tr.HonestBlocksAt H) O₂ W := by
    have hO₁ := high_origin_mem_at hp.run hp.noColl ho₁
    have hO₂ := high_origin_mem_at hp.run hp.noColl ho₂
    rcases hp.origins_compatible_at ho₁ ((hi r₁ (by omega)).trans hib)
        ho₂ ((hi r₂ (by omega)).trans hib) with h | h
    · exact ⟨v₂, r₂, O₂, ho₂.1, hO₂, h, .refl⟩
    · exact ⟨v₁, r₁, O₁, ho₁.1, hO₁, .refl, h⟩
  obtain ⟨z, m, W, hz, hW, hO₁W, hO₂W⟩ := upper
  have hm : ∀ q < m, tr.time q ≤ tr.time m := fun q hq => hp.run.time_mono hq.le
  have h₁ := hECO.trans hO₁W
  have h₂ := hJO.trans hO₂W
  have hσ₁ := σ_eq_honest_at hp.run hp.noColl ht hi hpH (hp.run.time_nonneg m) hm hz
    hEC (mem_of_honest_anc_at hp.run hp.noColl (hp.run.time_nonneg m) hm hz h₁ hW)
  have hσ₂ := σ_eq_honest_at hp.run hp.noColl ht hi hpH (hp.run.time_nonneg m) hm hz
    hJm (mem_of_honest_anc_at hp.run hp.noColl (hp.run.time_nonneg m) hm hz h₂ hW)
  have he := entry_root_eq_at hp.run hp.noColl hz hW h₁ h₂
    (by rw [← hσ₁, ← hσ₂, hECh, hJh, hBjhj]) (by rw [← hσ₁]; exact hECT)
    (by rw [← hσ₂]; exact hJT)
  have heq : EC = (tr.state p i).fg.J := hU.1 (hsub hEC) (hsub hJm) he
  exact hJC (heq ▸ hECC)

end Consensus.Goldilocks.Healing.Growing.Outcome

end
