module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources

public section

/-! # Optimistic sources and their supporters, under growing faults

The growing forms of the optimistic comparisons of `Healing/Outcome/FiniteSources`. Each writer
is honest at its own write. Its pool and frame are read on the prefix through the write, and an
optimistic lock's three-quarter quorum is charged at a single observation `≤ b`: the later write
for two locks, the write itself for one. Faults only grow, so a voter honest at that observation
was honest at each earlier vote, and the static one-vote-per-slot applies on the prefix through
it.

* `ResetPremisesUpTo.optimistic_sources_compatible_at`: two optimistic locks of one label are
  compatible;
* `ResetPremisesUpTo.optimistic_supporter_at`: an optimistic lock has an honest supporting vote no
  later than its write. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- Fewer than a third faulty is fewer than a three-quarter quorum. -/
private theorem faulty_lt_quorum {f v n : Nat} (hf : 3 * f ≤ n - 1) (hn : 0 < n)
    (hv : 3 * n ≤ 4 * v) : f < v := by
  omega

/-- Two three-quarter quorums of `n` intersect in more than the faulty count. -/
private theorem faulty_lt_quorum_inter {f i u v w n : Nat} (hf : 3 * f ≤ n - 1) (hn : 0 < n)
    (hv : 3 * n ≤ 4 * v) (hw : 3 * n ≤ 4 * w) (hI : i + u = v + w) (hu : u ≤ n) : f < i := by
  omega

/-- The static AC run of the prefix through `d` of the nodes honest at `d`. -/
private theorem acRun_prefix (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {d : Time}
    (hd : 0 ≤ d) :
    SA.ACRun proposer (tr.projAC.upTo d) (H d) ((tr.upTo d).HonestBlocks (H d)) := by
  have h := Compose.goldilocks_ac_projection sp ro dg (H d) (tr.upTo d) proposer
    (hp.run.upTo hd) (hp.noColl.upTo d)
  rwa [RunTrace.upTo_projAC] at h

/-- **Two optimistic sources of one label are compatible**, for writers honest at their writes
by `b`. The quorum intersection is charged at the later write. -/
theorem optimistic_sources_compatible_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {r q s : Nat} (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time q))
    (hrb : tr.time r ≤ b) (hqb : tr.time q ≤ b)
    {C D : SA.Blk sp.n (List (FG.Att sp.n))} {CV DV : Set (Vote sp.n)}
    (hC : SA.OptimisticLockAt tr.projAC x r s C CV)
    (hD : SA.OptimisticLockAt tr.projAC y q s D DV) :
    Compatible (tr.HonestBlocksAt H) C D := by
  have hm := hp.run.time_mono
  have hr0 := hp.run.time_nonneg r
  have hq0 := hp.run.time_nonneg q
  have hd0 : 0 ≤ max (tr.time r) (tr.time q) := hr0.trans (le_max_left _ _)
  have hdb : max (tr.time r) (tr.time q) ≤ b := max_le hrb hqb
  have hUc := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hrunR := acRun_prefix hp hr0
  have hrunQ := acRun_prefix hp hq0
  have hrunD := acRun_prefix hp hd0
  have hC' := (SA.upTo_optimisticLockAt hm).mpr ⟨le_rfl, hC⟩
  have hD' := (SA.upTo_optimisticLockAt hm).mpr ⟨le_rfl, hD⟩
  obtain ⟨ell, A, hpt, hsl, hsel, _⟩ := hC'
  obtain ⟨ell', A', hpt', hsl', hsel', _⟩ := hD'
  have hU := (SA.frameIn_of_callAt hrunR.localRun hx hpt.1).2
  have hU' := (SA.frameIn_of_callAt hrunQ.localRun hy hpt'.1).2
  have hsubR := RunTrace.honestBlocks_upTo_subset hm (H := H) hr0
  have hsubQ := RunTrace.honestBlocks_upTo_subset hm (H := H) hq0
  unfold SA.optimisticSelect at hsel hsel'
  dsimp only at hsel hsel'
  split_ifs at hsel
  split_ifs at hsel'
  have h34 := (SA.deepest_mem hsel).1.2.1
  have h34' := (SA.deepest_mem hsel').1.2.1
  rw [hsl] at h34
  rw [hsl'] at h34'
  rw [hp.run.stock] at h34 h34'
  have hI := Set.ncard_inter_add_ncard_union (SA.optimisticVoters sp A ell.frame s C)
    (SA.optimisticVoters sp A' ell'.frame s D)
  have hle : (SA.optimisticVoters sp A ell.frame s C ∪
      SA.optimisticVoters sp A' ell'.frame s D).ncard ≤ sp.n :=
    (Set.ncard_le_ncard (Set.subset_univ _)).trans (by
      rw [Set.ncard_univ, Nat.card_fin])
  obtain ⟨z, ⟨⟨v, hv, rfl, R, hR, hRr, hCR⟩,
      ⟨v', hv', hvz, R', hR', hRr', hDR⟩⟩, hz⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := (H (max (tr.time r) (tr.time q)))ᶜ)
      (t := SA.optimisticVoters sp A ell.frame s C ∩
        SA.optimisticVoters sp A' ell'.frame s D)
        (faulty_lt_quorum_inter (hp.faults _ hd0 hdb) (Fin.pos x) h34 h34' hI hle)
  have hz := not_not.mp hz
  have hzr : v.val ∈ H (tr.time r) := hp.run.antitone (le_max_left _ _) hz
  have hzq : v'.val ∈ H (tr.time q) := hp.run.antitone (le_max_right _ _) (hvz ▸ hz)
  obtain ⟨hvs, i, _, e, he, rfl⟩ := SA.optimisticPoint_pool_vote hrunR hx hpt hv hzr
  obtain ⟨hvs', i', _, e', he', rfl⟩ := SA.optimisticPoint_pool_vote hrunQ hy hpt' hv' hzq
  rw [hvz] at he'
  obtain ⟨hit, he₀⟩ := SA.upTo_voteAt.mp he
  obtain ⟨hit', he₀'⟩ := SA.upTo_voteAt.mp he'
  have heD := (SA.upTo_voteAt (d := max (tr.time r) (tr.time q))).mpr
    ⟨hit.trans (le_max_left _ _), he₀⟩
  have heD' := (SA.upTo_voteAt (d := max (tr.time r) (tr.time q))).mpr
    ⟨hit'.trans (le_max_right _ _), he₀'⟩
  obtain ⟨_, rfl⟩ := (SA.one_vote_per_slot sp) _ ro _ _ _ hrunD.localRun _ hz i i' e e' heD
    heD' (hvs.trans hvs'.symm)
  obtain rfl : R = R' := hUc.1 (hsubR (hU hR)) (hsubQ (hU' hR')) (hRr.trans hRr'.symm)
  exact SA.anc_total hUc ((hCR.mono hU).mono hsubR) ((hDR.mono hU').mono hsubQ)

/-- **An optimistic source has an honest supporting vote no later than its write**, for a
writer honest at its write by `b`. The supporter is honest at the write. -/
theorem optimistic_supporter_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x : Fin sp.n} {r s : Nat} (hx : x ∈ H (tr.time r)) (hrb : tr.time r ≤ b)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hop : SA.OptimisticLockAt tr.projAC x r s B CV) :
    B ∈ (tr.state x r).fg.tree ∧ ∃ z q, z ∈ H (tr.time r) ∧ q ≤ r ∧ ∃ e,
      SA.VoteAt tr.projAC z q e ∧ e.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hm := hp.run.time_mono
  have hr0 := hp.run.time_nonneg r
  have hrun := acRun_prefix hp hr0
  have hsub := RunTrace.honestBlocks_upTo_subset hm (H := H) hr0
  have hop' := (SA.upTo_optimisticLockAt hm).mpr ⟨le_rfl, hop⟩
  obtain ⟨ell, A, hpt, hsl, hsel, _⟩ := hop'
  have hU := (SA.frameIn_of_callAt hrun.localRun hx hpt.1).2
  have hpt₀ : tr.projAC.CallAt x r ell := ((Trace.upTo_callAt _).mp hpt.1).2
  unfold SA.optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  refine ⟨(frame_tree_subset_at hp.run hp.noColl hx hpt₀).2 (SA.deepest_mem hsel).1.1, ?_⟩
  have h34 := (SA.deepest_mem hsel).1.2.1
  rw [hp.run.stock] at h34
  obtain ⟨z, ⟨v, hv, rfl, R, hR, hRr, hBR⟩, hz⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := (H (tr.time r))ᶜ)
      (t := SA.optimisticVoters sp A ell.frame (sp.slot ((tr.projAC.upTo (tr.time r)).time r)) B)
      (faulty_lt_quorum (hp.faults _ hr0 hrb) (Fin.pos x) h34)
  obtain ⟨hvs, q, hqr, e, he, rfl⟩ :=
    SA.optimisticPoint_pool_vote hrun hx hpt hv (not_not.mp hz)
  exact ⟨_, q, not_not.mp hz, hqr, e, (SA.upTo_voteAt.mp he).2, hvs.trans hsl, R,
    hsub (hU hR), hRr, (hBR.mono hU).mono hsub⟩

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
