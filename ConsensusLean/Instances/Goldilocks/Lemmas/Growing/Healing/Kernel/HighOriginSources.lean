module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # High-origin sources independent of retained-vote induction

Raw heads and the snapshot cutoff use only historical local provenance. They
must remain below the retained-vote assembly in the import graph.
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

variable {ΔF a b : Time}

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
