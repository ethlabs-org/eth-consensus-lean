module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LowFinalized
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LeftEntry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HeldRoots
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Old high origins under growing faults

The origin writer is read at its write. These timing and ancestry facts do not
require that writer to remain honest at the later proposal.
-/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g : Time}

/-- A historically held block with the genesis root is below every historically held block. -/
theorem genesis_root_anc_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {G B : SA.Blk sp.n (List (FG.Att sp.n))} (hG : G ∈ tr.HonestBlocksAt H)
    (hg : G.root = sp.toParams.genesisRoot) (hB : B ∈ tr.HonestBlocksAt H) :
    Anc (tr.HonestBlocksAt H) G B := by
  obtain ⟨y, k, t, ht, hle, hy, hBt⟩ := hB
  have hr := fg_reachable_at hrun ht hle hy
  have hh := (Store.accepted_tree _ _ _ _ hr).2.2.2 B hBt
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨y, k, t, ht, hle, hy, h⟩
  have hgen := (Store.accepted_tree _ _ _ _ hr).2.2.1
  have he : G = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload :=
    (Compose.Growing.honest_blocks_coherent hrun hnc).1 hG (hsub hgen) hg
  rw [he]
  exact hh.mono hsub

variable {ΔF a b : Time}

/-- The finalized cache compares with a high origin at independently honest cuts. -/
theorem finalized_compatible_high_origin_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c)) (hcb : tr.time c ≤ b)
    {x : Fin sp.n} {i j : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j O) (hib : tr.time i ≤ b) :
    Compatible (tr.HonestBlocksAt H) (tr.state z c).fg.F O := by
  have ht := hp.run.time_nonneg c
  have hle : ∀ q < c, tr.time q ≤ tr.time c := fun _ hq => hp.run.time_mono hq.le
  have hr := fg_reachable_at hp.run ht hle hz
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hsub : (tr.state z c).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨z, c, tr.time c, ht, hle, hz, h⟩
  by_cases hh : HZ tr H g + 1 ≤ (tr.state z c).fg.hj
  · obtain ⟨_, hJm, hFJ, ⟨C, hC, hCJ, _⟩, _⟩ := Store.cache_invariants _ _ _ _ hr
    obtain ⟨E, hE, hEr, hEC, hcase⟩ := Store.J_entry_of_reachable hr hC
    obtain rfl : E = (tr.state z c).fg.J := hU.1 (hsub hE) (hsub hJm) (hEr.trans hCJ)
    rcases hcase with hg | ⟨hJh, hJT⟩
    · exact Or.inl ((hFJ.mono hsub).trans (genesis_root_anc_at hp.run hp.noColl
        (hsub hJm) (congrArg (·.root) hg)
        ⟨x, i, tr.time i, hp.run.time_nonneg i, fun _ hq => hp.run.time_mono hq.le,
          ho.1, highOrigin_mem_at hp.run hp.noColl ho⟩))
    · obtain ⟨_, _, _, _, v, d, _, hdc, _, _, r, hrd, m, B, hB, hJB⟩ :=
        hp.left_entry_origin_at ht hle hz hcb hJm hJT (by omega) hEC
          (by have := Store.hj_lt_h hr hC; omega)
      have hFB := (hFJ.mono hsub).trans hJB
      rcases hp.origins_compatible_at hB
          ((hp.run.time_mono (show r ≤ c by omega)).trans hcb) ho hib with h | h
      · exact Or.inl (hFB.trans h)
      · exact Anc.total hU hFB h
  · exact Or.inl (hp.low_finalized_below_origin_at ht hle hz hcb (by omega) ho hib)

/-- After the reset, a finalized cache is below an actual high origin written by the horizon. -/
theorem finalized_below_high_origin_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    (ha : a ≤ tr.time k) (hkb : tr.time k ≤ b) :
    ∃ x r l B, HighOrigin tr H g x r l B ∧ tr.time r ≤ tr.time k ∧ tr.time r ≤ b ∧
      Anc (tr.HonestBlocksAt H) (tr.state y k).fg.F B := by
  have ht := hp.run.time_nonneg k
  have hle : ∀ q < k, tr.time q ≤ tr.time k := fun _ hq => hp.run.time_mono hq.le
  have hr := fg_reachable_at hp.run ht hle hy
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨y, k, tr.time k, ht, hle, hy, h⟩
  obtain ⟨hFm, hJm, hFJ, ⟨C, hC, hCJ, _⟩, _⟩ := Store.cache_invariants _ _ _ _ hr
  obtain ⟨E, hE, hEr, hEC, hcase⟩ := Store.J_entry_of_reachable hr hC
  obtain rfl : E = (tr.state y k).fg.J := hU.1 (hsub hE) (hsub hJm) (hEr.trans hCJ)
  rcases hcase with hg | ⟨hJh, hJT⟩
  · obtain ⟨v, r, l, B, ho, hra, _⟩ := hp.reset_seed_at
    have hFG := (Store.accepted_tree _ _ _ _ hr).2.2.2 _ hFm
    rw [← hg] at hFG
    have he := (hFJ.mono hsub).antisymm hU (hFG.mono hsub)
    exact ⟨v, r, l, B, ho, hra.trans ha, hra.trans hp.reset_le,
      genesis_root_anc_at hp.run hp.noColl (hsub hFm)
        (congrArg (·.root) (he.trans hg))
        ⟨v, r, tr.time r, hp.run.time_nonneg r, fun _ hq => hp.run.time_mono hq.le,
          ho.1, highOrigin_mem_at hp.run hp.noColl ho⟩⟩
  by_cases hh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj
  · obtain ⟨_, _, _, _, v, d, _, hdk, _, _, r, hrd, l, B, ho, hJB⟩ :=
      hp.left_entry_origin_at ht hle hy hkb hJm hJT (by omega) hEC
        (by have := Store.hj_lt_h hr hC; omega)
    have hrk := hp.run.time_mono (show r ≤ k by omega)
    exact ⟨v, r, l, B, ho, hrk, hrk.trans hkb, (hFJ.mono hsub).trans hJB⟩
  obtain ⟨v, r, l, B, ho, hra, _⟩ := hp.reset_seed_at
  exact ⟨v, r, l, B, ho, hra.trans ha, hra.trans hp.reset_le,
    hp.low_finalized_below_origin_at ht hle hy hkb (by omega) ho (hra.trans hp.reset_le)⟩

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
