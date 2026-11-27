module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.LeftEntry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.High
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Records
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family

public section

/-! # High contests excluded using own-write origin comparability -/

namespace Consensus.Goldilocks.Healing.Growing.Outcome

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
variable {hold : Time}

private theorem entry_root_eq_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {z : Fin sp.n} {m : Nat} {t : Time} (ht : 0 ≤ t)
    (hm : ∀ q < m, tr.time q ≤ t) (hz : z ∈ H t)
    {C Z₁ Z₂ : AC.Blk sp.n (List (FG.Att sp.n))} (hC : C ∈ (tr.state z m).fg.tree)
    (h₁ : Anc (tr.HonestBlocksAt H) Z₁ C) (h₂ : Anc (tr.HonestBlocksAt H) Z₂ C)
    (hh : ((tr.state z m).fg.σ Z₁.root).h = ((tr.state z m).fg.σ Z₂.root).h)
    (hT₁ : ((tr.state z m).fg.σ Z₁.root).Th = Z₁.root)
    (hT₂ : ((tr.state z m).fg.σ Z₂.root).Th = Z₂.root) : Z₁.root = Z₂.root := by
  have hr := fg_reachable_at hrun ht hm hz
  rcases AC.anc_total (Compose.Growing.honest_blocks_coherent hrun hnc) h₁ h₂ with h | h
  · have := Healing.Th_eq_of_anc hr (store_anc_of_honest_anc_at hrun hnc ht hm hz h
      (mem_of_honest_anc_at hrun hnc ht hm hz h₂ hC)) hh.symm
    rw [← hT₁, ← hT₂, this]
  · have := Healing.Th_eq_of_anc hr (store_anc_of_honest_anc_at hrun hnc ht hm hz h
      (mem_of_honest_anc_at hrun hnc ht hm hz h₁ hC)) hh
    rw [← hT₁, ← hT₂, this]

/-- Earlier origins rule out a high contest at a reader's honest cut. Inside the deep quarantine
the origins are compared by the kernel's `ResetPremisesUpTo.origins_compatible_at`; after it, the
two left entries are on the healed chain, compared by the high-source cover's S1. -/
theorem no_high_contest_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {p : Fin sp.n} {i : Nat} (hpH : p ∈ H (tr.time i)) (hib : tr.time i ≤ b) :
    ¬ ((tr.state p i).fg.Contest ∧ HZ tr H g + 2 ≤ (tr.state p i).fg.hmax) := by
  have ht := hp.run.time_nonneg i
  have hi : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hp.run.time_mono hq.le
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hreach := fg_reachable_at hp.run ht hi hpH
  have hsub : (tr.state p i).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨p, i, tr.time i, ht, hi, hpH, h⟩
  have hq : (H (max (cutZ sp.toParams g) (tr.time i)))ᶜ.ncard < sp.toParams.fg.q := by
    obtain ⟨j, hj, hjb⟩ := hp.snapshot
    have h3 := hp.faults _ (ht.trans (le_max_right _ _)) (max_le (hj.2.le.trans hjb) hib)
    have hn := sp.toParams.hn
    change (H (max (cutZ sp.toParams g) (tr.time i)))ᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    change 3 * (H (max (cutZ sp.toParams g) (tr.time i)))ᶜ.ncard ≤ sp.toParams.n - 1 at h3
    omega
  rintro ⟨⟨hmj, C, hC, _, hCh, hJC⟩, hmax⟩
  obtain ⟨_, hJm, _, ⟨Bj, hBj, hBjJ, hBjhj⟩, _⟩ := Store.cache_invariants _ _ _ _ hreach
  obtain ⟨EJ, hEJ, hEJr, hEJB, hcase⟩ := Store.J_entry_of_reachable hreach hBj
  obtain rfl : EJ = (tr.state p i).fg.J := hU.1 (hsub hEJ) (hsub hJm) (hEJr.trans hBjJ)
  rcases hcase with hg | ⟨hJh, hJT⟩
  · exact hJC (hg ▸ (Store.accepted_tree _ _ _ _ hreach).2.2.2 C hC)
  obtain ⟨EC, hEC, hECC, hECh, hECT⟩ := Healing.entry_at_height hreach hC
    (h := (tr.state p i).fg.hj) (by omega) (by omega)
  have hsnap := hp.snapshot.imp fun _ h => h.1
  have hJlt : ((tr.state p i).fg.σ (tr.state p i).fg.J.root).h <
      ((tr.state p i).fg.σ Bj.root).h := by have := Store.hj_lt_h hreach hBj; omega
  -- both entries are below one block held while honest
  have upper : ∃ z m t W, 0 ≤ t ∧ (∀ q < m, tr.time q ≤ t) ∧ z ∈ H t ∧
      W ∈ (tr.state z m).fg.tree ∧ Anc (tr.HonestBlocksAt H) EC W ∧
      Anc (tr.HonestBlocksAt H) (tr.state p i).fg.J W := by
    rcases hp.quarantine_or_cover_at hib with hpre | hc
    · -- inside the deep quarantine: the origins are compared by `origins_compatible_at`
      obtain ⟨_, _, _, _, v₂, _, d₂, hd₂, _, _, r₂, hr₂, l₂, O₂, ho₂, hJO⟩ :=
        left_entry_origin_at (g := g) hp.run hp.noColl ht hi hpH hq hJm hJT
          (by omega) hEJB hJlt hsnap hpre
      obtain ⟨_, _, _, _, v₁, _, d₁, hd₁, _, _, r₁, hr₁, l₁, O₁, ho₁, hECO⟩ :=
        left_entry_origin_at (g := g) hp.run hp.noColl ht hi hpH hq hEC hECT
          (by omega) hECC (by omega) hsnap hpre
      have hO₁ := high_origin_mem_at hp.run hp.noColl ho₁
      have hO₂ := high_origin_mem_at hp.run hp.noColl ho₂
      rcases hp.origins_compatible_at ho₁ ((hi r₁ (by omega)).trans hib)
          ho₂ ((hi r₂ (by omega)).trans hib) with h | h
      · exact ⟨v₂, r₂, _, O₂, hp.run.time_nonneg r₂, fun _ hq => hp.run.time_mono hq.le,
          hp.run.antitone (le_max_right _ _) ho₂.1, hO₂, hECO.trans h, hJO⟩
      · exact ⟨v₁, r₁, _, O₁, hp.run.time_nonneg r₁, fun _ hq => hp.run.time_mono hq.le,
          hp.run.antitone (le_max_right _ _) ho₁.1, hO₁, hECO, hJO.trans h⟩
    · -- after the quarantine: both entries are on the healed chain, whose members are
      -- pairwise compatible (S1)
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hcJ⟩ :=
        left_entry_covered_at (g := g) hp.run hp.noColl ht hi hpH hq hJm hJT (by omega) hEJB hJlt
          hsnap hc hib
      obtain ⟨-, C₂, s₂, h₂, -, hJC₂⟩ := coveredUpTo_iff.1 hcJ
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hcE⟩ :=
        left_entry_covered_at (g := g) hp.run hp.noColl ht hi hpH hq hEC hECT (by omega) hECC
          (by omega) hsnap hc hib
      obtain ⟨-, C₁, s₁, h₁, -, hEC₁⟩ := coveredUpTo_iff.1 hcE
      rcases hc.s1 C₁ s₁ C₂ s₂ h₁ h₂ with h | h
      · obtain ⟨z, m, t, ht', hle', hz, hW⟩ := h₂.mem hp.run hp.noColl
        exact ⟨z, m, t, C₂, ht', hle', hz, hW, hEC₁.trans h, hJC₂⟩
      · obtain ⟨z, m, t, ht', hle', hz, hW⟩ := h₁.mem hp.run hp.noColl
        exact ⟨z, m, t, C₁, ht', hle', hz, hW, hEC₁, hJC₂.trans h⟩
  obtain ⟨z, m, t, W, ht', hm, hz, hW, h₁, h₂⟩ := upper
  have hσ₁ := σ_eq_honest_at hp.run hp.noColl ht hi hpH ht' hm hz
    hEC (mem_of_honest_anc_at hp.run hp.noColl ht' hm hz h₁ hW)
  have hσ₂ := σ_eq_honest_at hp.run hp.noColl ht hi hpH ht' hm hz
    hJm (mem_of_honest_anc_at hp.run hp.noColl ht' hm hz h₂ hW)
  have he := entry_root_eq_at hp.run hp.noColl ht' hm hz hW h₁ h₂
    (by rw [← hσ₁, ← hσ₂, hECh, hJh, hBjhj]) (by rw [← hσ₁]; exact hECT)
    (by rw [← hσ₂]; exact hJT)
  have heq : EC = (tr.state p i).fg.J := hU.1 (hsub hEC) (hsub hJm) he
  exact hJC (heq ▸ hECC)

end Consensus.Goldilocks.Healing.Growing.Outcome

end
