module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.VoteReceipt
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.OldSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run

public section

/-! # Bounded historical origins bound an honest cast's root -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- The post-drain cast root is genesis or below a bounded pre-slot high origin. -/
theorem reset_vote_root_source_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b) :
    ell.frame.fcRoot.root = sp.genesisRoot ∨
      ∃ v r l O, HighOrigin tr H g v r l O ∧ tr.time r < sp.ts u ∧ tr.time r ≤ b ∧
        Anc (tr.HonestBlocksAt H) ell.frame.fcRoot O := by
  have ht := hp.run.time_nonneg j
  have hj : ∀ q < j, tr.time q ≤ tr.time j := fun _ hq => hp.run.time_mono hq.le
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := fg_reachable_at hp.run ht hj hy
  have hsub : (tr.state y j).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ hX => ⟨y, j, tr.time j, ht, hj, hy, hX⟩
  have hfr := Outcome.frame_of_call hp.run hy hc.1
  have hc' : SA.CastAt (tr.projAC.upTo (tr.time j)) y j ell e :=
    ⟨(Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩, hc.2⟩
  have htupper : tr.time j ≤ sp.ts u + sp.Δ := by
    have h := (Compose.cast_head_fcRoot (hac.localRun.upTo ht) hy hc').2
    change tr.time j ≤ sp.ts e.msg.slot + sp.Δ at h
    rwa [hes] at h
  obtain ⟨hFm, hJm, hFJ, ⟨C, hCm, hCJ, hChj⟩, hmax, _⟩ :=
    Store.cache_invariants _ _ _ _ hr
  obtain ⟨E, hEm, hEr, hEC, hcase⟩ := Store.J_entry_of_reachable hr hCm
  obtain rfl : E = (tr.state y j).fg.J := hU.1 (hsub hEm) (hsub hJm) (hEr.trans hCJ)
  have hroot : (tr.state y j).fg.fcRoot = (tr.state y j).fg.J ∨
      (tr.state y j).fg.fcRoot = (tr.state y j).fg.F := by
    unfold Store.fcRoot
    split_ifs <;> simp
  rcases hcase with hg | ⟨hJh, hJT⟩
  · left
    rw [hfr]
    rcases hroot with h | h
    · exact congrArg (·.root) (h.trans hg)
    · have hJF := (Store.accepted_tree _ _ _ _ hr).2.2.2 _ hFm
      rw [← hg] at hJF
      have he := Anc.antisymm hU (hFJ.mono hsub) (hJF.mono hsub)
      exact congrArg (·.root) (h.trans (he.trans hg))
  right
  by_cases hh : HZ tr H g + 1 ≤ (tr.state y j).fg.hj
  · have hq : (H (tr.time j))ᶜ.ncard < sp.toParams.fg.q := by
      have h3 := hp.faults (tr.time j) ht hjb
      have hn := sp.toParams.hn
      change 3 * (H (tr.time j))ᶜ.ncard ≤ sp.toParams.n - 1 at h3
      change (H (tr.time j))ᶜ.ncard < (2 * sp.toParams.n + 2) / 3
      omega
    obtain ⟨W, hW, att, ha, v, hv, d, hdj, hs, _, r, hrd, l, O, ho, hJO⟩ :=
      Outcome.left_entry_origin_at (g := g) hp.run hp.noColl ht hj hy hq hJm hJT (by omega) hEC
        (by have := Store.hj_lt_h hr hCm; omega)
    have hlu : l < u := hes ▸ Outcome.row_origin_label_lt_at hp.run hp.noColl
      hy hv hc hW ha hs hdj hrd ho
    obtain ⟨CV, ellw, D, _, hfl, _⟩ := ho.2.2.1
    have hrj : tr.time r ≤ tr.time j := hp.run.time_mono (by omega)
    have hrt := Outcome.fastLock_time_lt_at hp.run hfl hlu (hrj.trans htupper)
    refine ⟨v, r, l, O, ho, hrt, hrj.trans hjb, ?_⟩
    rw [hfr]
    change Anc _ (tr.state y j).fg.fcRoot O
    rcases hroot with h | h
    · rw [h]; exact hJO
    · rw [h]; exact (hFJ.mono hsub).trans hJO
  obtain ⟨v, r, l, O, ho, hrb, hlu, hrt⟩ := hp.reset_seed_before_slot_at hR
  have hFO := hp.low_finalized_below_origin_at ht hj hy hjb (by omega) ho hrb
  refine ⟨v, r, l, O, ho, hrt, hrb, ?_⟩
  have hFO' : Anc (tr.HonestBlocksAt H) ell.frame.F O := by rw [hfr]; exact hFO
  have hOf := (hp.high_origin_held_at_vote_at ho hrb hy hc hjb (by omega) hFO').1
  have hOt := (frame_tree_subset_at hp.run hp.noColl hy hc.1).2 hOf
  have hOh := Outcome.high_of_anc_at hp.run hp.noColl ho ht hj hy hOt .refl
  have hOm := hmax O hOt
  rw [hfr]
  change Anc _ (tr.state y j).fg.fcRoot O
  unfold Store.fcRoot
  split_ifs with hchoose
  · have hJO : (tr.state y j).fg.Anc (tr.state y j).fg.J O := by
      by_contra hn
      exact hchoose.2 ⟨hchoose.1, O, hOt,
        store_anc_of_honest_anc_at hp.run hp.noColl ht hj hy hFO hOt, by omega, hn⟩
    exact hJO.mono hsub
  · exact hFO

/-- Every bounded pre-slot high origin below a target bounds the actual cast root. -/
theorem reset_vote_root_below_bound_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ tr.HonestBlocksAt H)
    (hbound : ∀ x r l B, HighOrigin tr H g x r l B → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocksAt H) B P)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ell e) (hs : e.msg.slot = u) (hjb : tr.time j ≤ b) :
    Anc (tr.HonestBlocksAt H) ell.frame.fcRoot P := by
  rcases hp.reset_vote_root_source_at hR hy hc hs hjb with hg | ⟨x, r, l, B, ho, ht, hrb, hroot⟩
  · have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
    have hc' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hc.1)
    obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt (hac.localRun.upTo (hp.run.time_nonneg j)) hy hc'
    exact ProposalImpl.genesis_root_anc_at hp.run hp.noColl (hPhiU hPhi.fcRoot_mem) hg hP
  · exact hroot.trans (hbound x r l B ho ht hrb)

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
