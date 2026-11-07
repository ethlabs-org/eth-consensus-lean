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

/-- Every fast-lock write is at or after its label's slot start. -/
theorem ts_le_of_fastLock_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {x : Fin sp.n} {r l : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (hf : SA.FastLockAt tr.projAC x r l D CV) :
    sp.ts l ≤ tr.time r := by
  rcases hf with ⟨ell, C, ⟨_, _, ht, _⟩, _⟩ | ⟨ell, A, _, hs, _⟩
  · have ht' : tr.time r = sp.ts l + 6 * sp.Δ := ht
    rw [ht']
    have := sp.toParams.hΔ
    linarith
  · change sp.slot (tr.time r) = l at hs
    exact (SA.ts_le_iff_le_slot sp (hrun.time_nonneg r) l).mpr (by omega)

/-- An origin written strictly before a proposal's slot has a strictly older label. -/
theorem label_lt_of_old_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {x : Fin sp.n} {r l u : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (ht : tr.time r < sp.ts u) : l < u := by
  obtain ⟨_, _, ⟨CV, ell, D, _, hf, _⟩, _⟩ := ho
  exact_mod_cast (SA.ts_lt_iff sp).mp ((ts_le_of_fastLock_at hrun hf).trans_lt ht)

/-- A high origin lies below its raw fast-lock head in the historical universe. -/
theorem highOrigin_raw_head_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {x : Fin sp.n} {r l : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) :
    ∃ ell D CV, tr.projAC.CallAt x r ell ∧ SA.FastLockAt tr.projAC x r l D CV ∧
      Anc (tr.HonestBlocksAt H) O D := by
  obtain ⟨hx, _, ⟨CV, ell, D, hc, hf, rfl⟩, _⟩ := ho
  obtain ⟨ell', hc', hD⟩ := Healing.fastLock_mem hf
  obtain rfl : ell = ell' := Option.some.inj (hc.2.symm.trans hc'.2)
  obtain ⟨hok, hsub⟩ := frame_tree_subset_at hrun hnc hx hc
  refine ⟨ell, D, CV, hc, hf, (SA.viableAncestor_anc hok hD).2.mono ?_⟩
  exact fun _ hB => ⟨x, r, tr.time r, hrun.time_nonneg r,
    fun _ hq => hrun.time_mono hq.le, hx, hsub hB⟩

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

/-- A high descendant cannot be held before the snapshot by a holder still honest there.
Honesty only at the earlier read would not suffice: that holder can disappear from HZ. -/
theorem cutZ_lt_of_anc_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x : Fin sp.n} {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) {z : Fin sp.n} {k : Nat}
    (hz : z ∈ H (max (tr.time k) (cutZ sp.toParams g)))
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hW : W ∈ (tr.state z k).fg.tree)
    (hBW : Anc (tr.HonestBlocksAt H) B W) :
    cutZ sp.toParams g < tr.time k := by
  classical
  by_contra h
  have hkZ : tr.time k ≤ cutZ sp.toParams g := not_lt.mp h
  have hzZ : z ∈ H (cutZ sp.toParams g) := by
    rwa [max_eq_right hkZ] at hz
  have hZ0 : 0 ≤ cutZ sp.toParams g := (hp.run.time_nonneg k).trans hkZ
  have hhigh := hp.high_of_anc_at ho hZ0
    (fun _ hq => (hp.run.time_mono hq.le).trans hkZ) hzZ hW hBW
  obtain ⟨c, hc, _⟩ := hp.snapshot
  have hkc : k ≤ c := by
    by_contra hn
    exact (not_lt_of_ge hkZ) (hc.2.trans_le (hp.run.time_mono (by omega)))
  have hr := hp.run.upTo hZ0
  have hWk : W ∈ ((tr.upTo (cutZ sp.toParams g)).state z k).fg.tree := by
    rwa [Trace.upTo_state tr z (fun _ hq => (hp.run.time_mono hq.le).trans hkZ)]
  have hWc := Compose.tree_mono hr.toLocalRun hzZ hkc hWk
  rw [Trace.upTo_state tr z hc.1] at hWc
  have hs := σ_eq_honest_at hp.run hp.noColl hZ0
    (fun _ hq => (hp.run.time_mono hq.le).trans hkZ) hzZ hZ0 hc.1 hzZ hW hWc
  have hbnd := (Store.cache_invariants _ _ _ _ (fg_reachable_at hp.run hZ0 hc.1 hzZ)).2.2.2.2.1
    W hWc
  have hmax : (tr.state z c).fg.hmax ≤ HZ tr H g := by
    refine le_csSup (((Set.finite_range fun v => (tr.state v c).fg.hmax).subset ?_).bddAbove)
      ⟨z, hzZ, c, hc, rfl⟩
    rintro _ ⟨v, _, c', hc', rfl⟩
    obtain rfl := hc'.unique hc
    exact ⟨v, rfl⟩
  rw [← hs] at hbnd
  omega

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
