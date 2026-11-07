module
public import ConsensusLeanTest.Goldilocks.Regimes.ProposerHoldRun.Cast
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Read
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import all ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
@[expose] public section

/-! # The proposer-hold counterexample: key `2`'s confirmed read at `41`

On the retained run, every block on the chain of key `2`'s confirmed read at the horizon `41` is
genesis or the twin's block, so every header of the read is the forged header (`read_hdr`).

The read is the block named by the record or `Σ.F` (`ready_read_record_before`), each genesis or
below an origin within `41` (`record_origin_upTo`, `caches_on_chain_upTo`). An origin of a label
`s ≥ 2` within `41` is impossible: an update of slot `s` is at `t_s + 6Δ ≥ 42`, and an optimistic
confirmation needs four of the five validators among the slot-`s` voters of an honest pool, while
the faulty keys `0` and `1` have none (`pool_vote_slot`). An origin of a label `≤ 1` has an honest
supporter of its slot (`honest_supporter_before`), whose head is genesis or the twin's block
(`vote_head`). -/

namespace Consensus.Goldilocks.Test.ProposerHold
open AsChainShape Shape Blocks Simulation Node
open Consensus.Model (pubOf)

variable {S : Setup}

variable (S) in
/-- Genesis or the twin's block. -/
def Small (B : Blk (S.params (pubOf env) one_le_card)) : Prop :=
  B.root = (S.params (pubOf env) one_le_card).genesisRoot ∨
    blockObj (S.params (pubOf env) one_le_card) B = twin S

theorem honest_coherent' : Coherent ((tr S).HonestBlocks (H S)) :=
  Compose.honest_coherent rhoc_run rhoc_noColl

/-- The ancestors of genesis or of the twin's block among the honest blocks are genesis or the
twin's block. -/
theorem small_anc {B C : Blk (S.params (pubOf env) one_le_card)}
    (h : Anc ((tr S).HonestBlocks (H S)) B C) (hs : Small S C) : Small S B := by
  have hgen : ∀ {D}, D ∈ (tr S).HonestBlocks (H S) →
      D.root = (S.params (pubOf env) one_le_card).genesisRoot → D.parent = none := by
    intro D hD hr
    rw [Compose.honest_eq_genesis rhoc_run honest_coherent' hD hr]
    rfl
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨D, hBD, hDC⟩
  · exact hs
  rcases hs with hs | hs
  · exact absurd hDC.2.2 (by rw [hgen hDC.2.1 hs]; simp)
  have hp := congrArg Header.parent (headerOf_of_twin hs)
  simp only [headerOf, hdr, hDC.2.2, parentRef] at hp
  have hDg : D.root = (S.params (pubOf env) one_le_card).genesisRoot := by
    by_contra hne
    simp [hne] at hp
  rcases Relation.ReflTransGen.cases_tail hBD with rfl | ⟨E, -, hED⟩
  · exact Or.inl hDg
  · exact absurd hED.2.2 (by rw [hgen hED.2.1 hDg]; simp)

/-- The honest validators are three. -/
theorem H_ncard_le : (H S).ncard ≤ 3 := by
  have hsub : H S ⊆ ((({key 2, key 3, key 4} : Finset (Fin (Fintype.card (Fin 5)))) :
      Set (Fin (Fintype.card (Fin 5))))) := by
    intro y hy
    rw [mem_H] at hy
    have hlt := y.isLt
    simp only [Fintype.card_fin] at hlt
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases y with ⟨v, hv⟩
    simp only [Fin.mk.injEq]
    simp only at hy hlt
    omega
  exact (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans
    (by rw [Set.ncard_coe_finset]; decide)

/-- **No origin of a label `≥ 2` within `41`.** -/
theorem origin_label {C : Blk (S.params (pubOf env) one_le_card)} {s : Nat}
    (hC : Compose.OriginWithin (tr S) (H S) C s 41) : s ≤ 1 := by
  by_contra hs
  push Not at hs
  have hrun' := Compose.goldilocks_ac_projection _ _ _ _ _ _ (rhoc_run (S := S)) rhoc_noColl
  obtain ⟨x, hx, i, CV, hi, ⟨ℓ, hu, -⟩ | hO⟩ := Compose.originWithin_iff.mp hC
  · have ht : (tr S).time i = (S.params (pubOf env) one_le_card).ts s +
        6 * (S.params (pubOf env) one_le_card).Δ := hu.2.2.1
    rw [ht] at hi
    change 4 * 3 * (s : Int) + 6 * 3 ≤ 41 at hi
    omega
  · obtain ⟨ℓ', A, hpt, -, h34, -⟩ := SA.optimistic_seats hrun' hx hO
    have hsub : SA.optimisticVoters _ A ℓ'.frame s C ⊆ H S := by
      rintro u ⟨v, hv, rfl, -⟩
      by_contra hvH
      have hvs := SA.optimisticPoint_pool_slot hrun'.localRun hx hpt hv
      have hpost := SA.optimisticPoint_pool_post hrun'.localRun hx hpt s hv
      rw [Compose.projAC_state rhoc_run.toLocalRun hx, ← hvs] at hpost
      have := pool_vote_slot hx _ hpost hvH
      omega
    have := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans H_ncard_le
    change 3 * Fintype.card (Fin 5) ≤ _ at h34
    simp only [Fintype.card_fin] at h34
    omega

/-- **Every origin within `41` is genesis or the twin's block.** -/
theorem origin_small {C : Blk (S.params (pubOf env) one_le_card)} {s : Nat}
    (hC : Compose.OriginWithin (tr S) (H S) C s 41) : Small S C := by
  have hs := origin_label hC
  obtain ⟨x, hx, j, e, hv, -, hes, D, hD, hDr, hCD⟩ :=
    Compose.honest_supporter_before rhoc_run rhoc_noColl (by norm_num) rhoc_service
      rhoc_faultBound hC
  obtain ⟨D', hD', hD'r, hsm⟩ := vote_head hx hv (hes ▸ hs)
  have hD'U : D' ∈ (tr S).HonestBlocks (H S) := ⟨x, hx, j, hD'⟩
  have hDD : D = D' := honest_coherent'.1 hD hD'U (hDr.trans hD'r.symm)
  subst hDD
  exact small_anc hCD hsm

/-- **Key `2`'s confirmed read at `41` on the retained run holds only the forged header.** -/
theorem read_hdr {h : Header Info}
    (hh : h ∈ (chainTrace (rhoc S)).read .confirmed 2 ((chainTrace (rhoc S)).endCut 41)) :
    h = hdr := by
  have hready : (rhoc S).point.Ready (Regimes.catchUp (S.params (pubOf env) one_le_card)) 2 41 := by
    have : (2 : Fin 5) ∈ (rhoc S).point.readyAt
        (Regimes.catchUp (S.params (pubOf env) one_le_card)) 41 := by
      rw [rhoc_readyAt]; decide
    classical
    exact (Finset.mem_filter.mp this).2
  have hth : (41 : Time) ≤ (rhoc S).horizon := by rw [rhoc_horizon]
  have hcut := Obligations.sleepy_read_cut S (rhoc S) one_le_card rhoc_const rhoc_valid
    (by norm_num) hth hready
  have hi : (chainTrace (rhoc S)).endCut 41 ≤ (rhoc S).events.length := Nat.findGreatest_le _
  have hhon : (2 : Fin 5) ∉ (rhoc S).faultyAt 0 := by rw [rhoc_faultyAt]; decide
  have hy : (rhoc S).ownKey 2 ∈ H S :=
    (mem_honestKeys_iff S (rhoc S) _).mpr (by rw [ownKey_key']; exact hhon)
  rw [read_eq_out S (rhoc S) one_le_card, outOf,
    simTrace_state S (rhoc S) one_le_card rhoc_const rhoc_valid 2 hhon _ hi, hcut.2.2] at hh
  set y := (rhoc S).ownKey 2
  set j := cutMap S (rhoc S) one_le_card ((chainTrace (rhoc S)).endCut 41)
  set C := Regimes.readAfter (tr S) y j 41 with hCdef
  change h ∈ chainTo ((tr S).state y j).fg.blocks (C.slot + 1) C at hh
  have hprev := hcut.1.1
  have hreach := Compose.fg_reachable rhoc_run.toLocalRun hy j
  have hrd := Obligations.ready_transport S (rhoc S) one_le_card rhoc_valid (by norm_num) hth hready
  have hC : Small S C ∧ C ∈ ((tr S).state y j).fg.tree := by
    rcases Compose.ready_read_record_before rhoc_run rhoc_noColl rhoc_invariant rhoc_service.ac
        (fun s hs => rhoc_faultBound s _ (by simp) hs) ⟨hprev, hcut.1.2.le⟩ hcut.2.1 hrd le_rfl
      with ⟨R, hR, hRr, hread⟩ | ⟨-, hread⟩
    · rw [hCdef, hread]
      obtain ⟨C', hC', hC'r, hor⟩ := Compose.record_origin_upTo rhoc_run rhoc_noColl hy hprev
      have hRC : R = C' := honest_coherent'.1 ⟨y, hy, j, hR.1⟩ ⟨y, hy, j, hC'⟩ (hRr.trans hC'r.symm)
      subst hRC
      refine ⟨?_, hC'⟩
      rcases hor with hg | ⟨s, hs⟩
      · exact Or.inl hg
      · exact origin_small hs
    · rw [hCdef, hread]
      refine ⟨?_, (Store.cache_invariants _ _ _ _ hreach).1⟩
      rcases Compose.onOriginChainWithin_iff.mp (Compose.caches_on_chain_upTo rhoc_run rhoc_noColl
          (rhoc_faultBound 0 0 (by simp) (by change 4 * 3 * ((0 : Nat) : Int) + 0 ≤ 41; norm_num))
          hy hprev).1 with hg | ⟨D, s, hD, hFD⟩
      · exact Or.inl hg
      · exact small_anc hFD (origin_small hD)
  obtain ⟨X, -, hXC, hXg, rfl⟩ := mem_chainTo hreach hC.2 hh
  rcases small_anc (Anc.mono (fun Z hZ => ⟨y, hy, j, hZ⟩) hXC) hC.1 with hg | htw
  · exact absurd hg hXg
  · exact headerOf_of_twin htw

end Consensus.Goldilocks.Test.ProposerHold

end
