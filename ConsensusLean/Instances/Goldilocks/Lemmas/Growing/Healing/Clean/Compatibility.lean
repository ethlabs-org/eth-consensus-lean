module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee

public section

/-! # Optimistic sources and their supporters, under growing faults

The growing forms of the optimistic comparisons of `Healing/Outcome/FiniteSources`. Each writer
is honest at its own write. Its pool and frame are read on the prefix through the write, and an
optimistic lock's three-quarter quorum is charged at a single observation `≤ b`: the later write
for two locks, the write itself for one, against the slot's committee (its pools hold committee
votes, P, and fewer than half of it is faulty from `ḡ` on). Faults only grow, so a voter honest at
that observation was honest at each earlier vote, and the static one-vote-per-slot applies on the
prefix through it.

* `ResetPremisesUpTo.optimistic_sources_compatible_at`: two optimistic locks of one label are
  compatible;
* `ResetPremisesUpTo.optimistic_supporter_at`: an optimistic lock has an honest supporting vote no
  later than its write. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams ReplayOrder Payload Vote)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {hold : Time}

/-- The static AC run of the prefix through `d` of the nodes honest at `d`. -/
private theorem acRun_prefix {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) {d : Time}
    (hd : 0 ≤ d) :
    AC.ACRun proposer (tr.projAC.upTo d) (H d) ((tr.upTo d).HonestBlocks (H d))
      (AC.committeeStart sp.genesisRoot (Generic.dictOfTime sp cm)) := by
  have h := Compose.goldilocks_ac_projection_from (hp.run.upTo hd) (hp.noColl.upTo d)
  rwa [RunTrace.upTo_projAC] at h

/-- **Two optimistic sources of one label are compatible**, for writers honest at their writes
by `b`. The quorum intersection is charged at the later write. -/
theorem optimistic_sources_compatible_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {r q s : Nat} (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time q))
    (hrb : tr.time r ≤ b) (hqb : tr.time q ≤ b) (hgs : AC.gbar g ≤ sp.ts s)
    {C D : AC.Blk sp.n (List (FG.Att sp.n))} {CV DV : Set (Vote sp.n)}
    (hC : AC.OptimisticLockAt tr.projAC x r s C CV)
    (hD : AC.OptimisticLockAt tr.projAC y q s D DV) :
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
  have hC' := (AC.upTo_optimisticLockAt hm).mpr ⟨le_rfl, hC⟩
  have hD' := (AC.upTo_optimisticLockAt hm).mpr ⟨le_rfl, hD⟩
  obtain ⟨ell, A, hpt, hsl, hsel, _⟩ := hC'
  obtain ⟨ell', A', hpt', hsl', hsel', _⟩ := hD'
  have hU := (AC.frameIn_of_callAt hrunR.localRun hx hpt.1).2
  have hU' := (AC.frameIn_of_callAt hrunQ.localRun hy hpt'.1).2
  have hsubR := RunTrace.honestBlocks_upTo_subset hm (H := H) hr0
  have hsubQ := RunTrace.honestBlocks_upTo_subset hm (H := H) hq0
  unfold AC.optimisticSelect at hsel hsel'
  dsimp only at hsel hsel'
  split_ifs at hsel
  split_ifs at hsel'
  have h34 := (AC.deepest_mem hsel).1.2.1
  have h34' := (AC.deepest_mem hsel').1.2.1
  rw [hsl] at h34
  rw [hsl'] at h34'
  -- both quorums are of slot-`s` committee members, half of whom are honest at the later write
  have hPK := fun t => AC.CommitteePAt.upTo hm hp.run.antitone hp.committeeFacts.hP t
  have hOK : AC.optimisticVoters sp A ell.frame s C ⊆ (Generic.dictOfTime sp cm).committee s :=
    fun _ ⟨v, hv, hvu, _⟩ => hvu ▸ (hPK (tr.time r)).2 x hx r ell A hpt s v hv
  have hOK' : AC.optimisticVoters sp A' ell'.frame s D ⊆
      (Generic.dictOfTime sp cm).committee s :=
    fun _ ⟨v, hv, hvu, _⟩ => hvu ▸ (hPK (tr.time q)).2 y hy q ell' A' hpt' s v hv
  have hsr : sp.ts s ≤ tr.time r :=
    (AC.ts_le_iff_le_slot sp hr0 s).2 (by rw [show sp.slot (tr.time r) = s from hsl])
  have hf := hp.committee_cs2_at hgs (hsr.trans hrb) hd0 hdb
  rw [← hp.committeeFacts.hsize s] at hf
  obtain ⟨z, ⟨⟨v, hv, rfl, R, hR, hRr, hCR⟩,
      ⟨v', hv', hvz, R', hR', hRr', hDR⟩⟩, hz⟩ :=
    AC.quorums_meet _ (hp.committeeFacts.hsize s) hOK hOK' h34 h34' hf
  have hz := not_not.mp hz
  have hzr : v.val ∈ H (tr.time r) := hp.run.antitone (le_max_left _ _) hz
  have hzq : v'.val ∈ H (tr.time q) := hp.run.antitone (le_max_right _ _) (hvz ▸ hz)
  obtain ⟨hvs, i, _, e, he, rfl⟩ := AC.optimisticPoint_pool_vote hrunR hx hpt hv hzr
  obtain ⟨hvs', i', _, e', he', rfl⟩ := AC.optimisticPoint_pool_vote hrunQ hy hpt' hv' hzq
  rw [hvz] at he'
  obtain ⟨hit, he₀⟩ := AC.upTo_voteAt.mp he
  obtain ⟨hit', he₀'⟩ := AC.upTo_voteAt.mp he'
  have heD := (AC.upTo_voteAt (d := max (tr.time r) (tr.time q))).mpr
    ⟨hit.trans (le_max_left _ _), he₀⟩
  have heD' := (AC.upTo_voteAt (d := max (tr.time r) (tr.time q))).mpr
    ⟨hit'.trans (le_max_right _ _), he₀'⟩
  obtain ⟨_, rfl⟩ := AC.one_vote_per_slotU sp _ ro _ _ _ hrunD.localRun.toU _ hz i i' e e' heD
    heD' (hvs.trans hvs'.symm)
  obtain rfl : R = R' := hUc.1 (hsubR (hU hR)) (hsubQ (hU' hR')) (hRr.trans hRr'.symm)
  exact AC.anc_total hUc ((hCR.mono hU).mono hsubR) ((hDR.mono hU').mono hsubQ)

/-- **An optimistic source has an honest supporting vote no later than its write**, for a
writer honest at its write by `b`. The supporter is honest at the write. -/
theorem optimistic_supporter_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {r s : Nat} (hx : x ∈ H (tr.time r)) (hrb : tr.time r ≤ b)
    (hgs : AC.gbar g ≤ sp.ts s)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hop : AC.OptimisticLockAt tr.projAC x r s B CV) :
    B ∈ (tr.state x r).fg.tree ∧ ∃ z q, z ∈ H (tr.time r) ∧ q ≤ r ∧ ∃ e,
      AC.VoteAt tr.projAC z q e ∧ e.msg.slot = s ∧
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hm := hp.run.time_mono
  have hr0 := hp.run.time_nonneg r
  have hrun := acRun_prefix hp hr0
  have hsub := RunTrace.honestBlocks_upTo_subset hm (H := H) hr0
  have hop' := (AC.upTo_optimisticLockAt hm).mpr ⟨le_rfl, hop⟩
  obtain ⟨ell, A, hpt, hsl, hsel, _⟩ := hop'
  have hU := (AC.frameIn_of_callAt hrun.localRun hx hpt.1).2
  have hpt₀ : tr.projAC.CallAt x r ell := ((Trace.upTo_callAt _).mp hpt.1).2
  unfold AC.optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  refine ⟨(frame_tree_subset_at hp.run hp.noColl hx hpt₀).2 (AC.deepest_mem hsel).1.1, ?_⟩
  have h34 := (AC.deepest_mem hsel).1.2.1
  rw [hsl] at h34
  -- the quorum is of slot-`s` committee members, fewer than half of whom are faulty at the write
  have hOK : AC.optimisticVoters sp A ell.frame s B ⊆ (Generic.dictOfTime sp cm).committee s :=
    fun _ ⟨v, hv, hvu, _⟩ => hvu ▸
      (AC.CommitteePAt.upTo hm hp.run.antitone hp.committeeFacts.hP (tr.time r)).2 x hx r ell A
        hpt s v hv
  have hsr : sp.ts s ≤ tr.time r :=
    (AC.ts_le_iff_le_slot sp hr0 s).2 (by rw [show sp.slot (tr.time r) = s from hsl])
  have hf := hp.committee_cs2_at hgs (hsr.trans hrb) hr0 hrb
  have hpos := hp.committee_pos
  obtain ⟨z, hzO, hz⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard
      (s := (Generic.dictOfTime sp cm).committee s ∩ (H (tr.time r))ᶜ)
      (t := AC.optimisticVoters sp A ell.frame s B) (by omega)
  have hzH : z ∈ H (tr.time r) := by_contra fun h => hz ⟨hOK hzO, h⟩
  rw [← hsl] at hzO
  obtain ⟨v, hv, rfl, R, hR, hRr, hBR⟩ := hzO
  obtain ⟨hvs, q, hqr, e, he, rfl⟩ := AC.optimisticPoint_pool_vote hrun hx hpt hv hzH
  exact ⟨_, q, hzH, hqr, e, (AC.upTo_voteAt.mp he).2, hvs.trans hsl, R,
    hsub (hU hR), hRr, (hBR.mono hU).mono hsub⟩

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
