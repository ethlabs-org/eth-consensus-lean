module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.OptimisticDomain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.ResetSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.LockWriter
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Next
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Lemmas.Tactic.Linarith

import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HealedMembers
public section

/-! # Clean fast sources and their votes, under growing faults

The growing form of the fast-source part of `Healing/Outcome/FiniteSources`: a clean fast source,
written by a node honest at its write, is extended by every later vote of a node honest at it
through the horizon, by strong induction on the cast's cut.

* The first successor vote is the growing first transfer (`AC.Growing.first_transfer_stored`): the
  counted votes reach the voter through the reset service from their releases, each while its
  writer is honest (`fastLock_writer_at`, `KernelProof.carry_of_senders`).
* A later vote is the growing next transfer (`AC.Growing.next_transfer`) over the half committee
  of the previous label.
* The vote domain is the result-prefix domain for a fast update and the optimistic vote domain
  (`optimistic_vote_domain_before_of_quarantine_at`) for an optimistic lock. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams ReplayOrder Payload Vote)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {hold : Time}

/-- **Finite fast-source transfer**, with its vote domain supplied at each later vote of a node
honest at it, given the earlier votes of nodes honest at them. -/
theorem fast_source_votes_of_domain_before_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {r s : Nat} (hx : x ∈ H (tr.time r))
    {B : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfast : AC.FastLockAt tr.projAC x r s B CV) (hts : cutZ sp.toParams g ≤ sp.ts s)
    (hdomain : ∀ y i ell e, y ∈ H (tr.time i) → AC.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → s < e.msg.slot →
      (∀ z q, z ∈ H (tr.time q) → q < i → ∀ e', AC.VoteAt tr.projAC z q e' →
        s < e'.msg.slot → AC.VoteExtends (tr.HonestBlocksAt H) e'.msg B) →
      Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
        B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot)) :
    ∀ i, tr.time i ≤ b → ∀ y, y ∈ H (tr.time i) → ∀ ell e, AC.CastAt tr.projAC y i ell e →
      s < e.msg.slot → AC.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have hPK := hp.committeeFacts.hP
  have hTK := hp.committeeFacts.committeeTAt hrun hnc
  -- the slot committees from the source's label on are bounded through the horizon
  have hgsl : ∀ {u : Nat}, s ≤ u → AC.gbar g ≤ sp.ts u := fun hu =>
    Healing.gbar_le_of_cutZ_le sp (hts.trans ((AC.ts_le_iff sp).mpr (by exact_mod_cast hu)))
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hgs : g ≤ sp.ts s := by
    have := Healing.lt_cutZ sp g
    have := AC.le_gbar g
    linarith
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hib y hy ell e hcast hsi
  have hprior : ∀ z q, z ∈ H (tr.time q) → q < i → ∀ e', AC.VoteAt tr.projAC z q e' →
      s < e'.msg.slot → AC.VoteExtends (tr.HonestBlocksAt H) e'.msg B := by
    rintro z q hz hqi e' ⟨ell', hc'⟩ hse
    exact ih q hqi ((hrun.time_mono hqi.le).trans hib) z hz ell' e' hc' hse
  have hd := hrun.time_nonneg i
  obtain ⟨⟨hΦ, hΦU⟩, hhead, hsl⟩ := KernelProof.castAt_facts_at hrun hnc hy hcast
  rcases hdomain y i ell e hy hcast hib hsi hprior with hBF | hv
  · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := hhead
    exact ⟨Hd, hΦU hHd, hHdr, hBF.trans (hfHd.mono hΦU)⟩
  have hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B := (hΦ.rooted.2 B hv.1.1).mono hΦU
  have htime : sp.ts e.msg.slot ≤ tr.time i :=
    (AC.ts_le_iff_le_slot sp hd _).mpr (by rw [hsl])
  by_cases hfirst : e.msg.slot = s + 1
  · have hts1 : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := AC.ts_succ s
    rw [hfirst] at htime
    have carry := KernelProof.carry_of_senders hp hts hy hcast hfirst (CV := CV)
      fun v hv' => by
        obtain ⟨hvs, ⟨k, hxk, hsend, hk1, hk2⟩, D, -, hDr, hBD, hacc⟩ :=
          fastLock_writer_at hac.localRun hac.vstart hx hfast v hv'
        exact ⟨hvs, ⟨x, k, hxk, hsend, hk1, hk2⟩, D, hDr, hFB.trans hBD,
          hacc.imp_right fun ⟨k, hk⟩ => ⟨x, k, hk⟩⟩
    have hsi : sp.ts s ≤ tr.time i := by linarith only [htime, hts1, hΔ]
    exact AC.Growing.first_transfer_stored hac _
      (fun t => AC.CommitteePAt.upTo hrun.time_mono hrun.antitone hPK t)
      (AC.CommitteeTAt.upTo hrun.antitone hTK) hp.committeeFacts.hsize hx hfast .refl hy hcast
      hfirst (KernelProof.reset_syncACAt hp hgs) carry
      (KernelProof.faultBoundK_late_at hp (hgsl le_rfl) (hsi.trans hib) (hts.trans hsi) le_rfl
        hib)
      (hp.committee_cs2_at (hgsl (by omega)) (htime.trans hib) (hrun.time_nonneg i) hib)
      (by rw [← hfirst]; exact Or.inl hv)
      (fun z q hq hz e' he hslot => hprior z q hz hq e' he (by omega))
  · obtain ⟨m, hm⟩ : ∃ m, e.msg.slot = m + 1 := ⟨e.msg.slot - 1, by omega⟩
    have hsm : s < m := by omega
    rw [hm] at htime
    have hts1 : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := AC.ts_succ m
    have hmts : cutZ sp.toParams g ≤ sp.ts m :=
      hts.trans ((AC.ts_le_iff sp).mpr (by clear * - hsm; omega))
    -- a label-`m` vote of a node honest at it is at an earlier cut
    have hall : ∀ z q e', z ∈ H (tr.time q) → AC.VoteAt tr.projAC z q e' → e'.msg.slot = m →
        AC.VoteExtends (tr.HonestBlocksAt H) e'.msg B := by
      rintro z q e' hz ⟨ell', hc'⟩ hslot
      have hqi : q < i := by
        by_contra hn
        have hq := (KernelProof.castAt_facts_at hrun hnc hz hc').2.2
        have := AC.slot_mono sp hd (hrun.time_mono (Nat.le_of_not_gt hn))
        omega
      exact hprior z q hz hqi e' ⟨ell', hc'⟩ (by omega)
    have hmi : sp.ts m ≤ tr.time i := by linarith only [htime, hts1, hΔ]
    exact AC.Growing.next_transfer_from hac _ hPK hTK
      hp.committeeFacts.hsize hy hcast hm hall
      (hp.half_committee_at hmts (t := tr.time i) (by linarith only [htime, hts1, hΔ]) hib)
      (KernelProof.honest_votes_carry_reset_at hp hy hcast hm hmts hall hFB)
      (KernelProof.faultBoundK_late_at hp (hgsl (by omega)) (hmi.trans hib) (hmts.trans hmi)
        le_rfl hib)
      (hp.committee_cs2_at (hgsl (by omega)) (htime.trans hib) (hrun.time_nonneg i) hib)
      (by rw [← hm]; exact Or.inl hv)
      (fun z q hq hz e' he hslot => hprior z q hz hq e' he (by omega))

/-- **A clean fast source is extended by every later vote** of a node honest at it, through the
horizon. -/
theorem fast_source_votes_before_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {r s : Nat} (hx : x ∈ H (tr.time r))
    {B : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfast : AC.FastLockAt tr.projAC x r s B CV)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b) :
    ∀ i, tr.time i ≤ b → ∀ y, y ∈ H (tr.time i) → ∀ ell e, AC.CastAt tr.projAC y i ell e →
      s < e.msg.slot → AC.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hm := hp.run.time_mono
  have hxU : (tr.state x r).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨x, r, tr.time r, hp.run.time_nonneg r, fun _ hq => hm hq.le, hx, h⟩
  have hcase : (∀ D, sp.deepDepth = some D → b ≤ cutZ sp.toParams g + 4 * D * sp.Δ) ∨
      HighSourceCover tr H g a b := by
    cases hdd : sp.deepDepth with
    | none => exact Or.inl fun D hD => by cases hD
    | some D =>
      rcases hp.deepCover D hdd with hb | hc
      · exact Or.inl fun D' hD' => by cases hD'; exact hb
      · exact Or.inr hc
  rcases hcase with hpre | hc
  swap
  · -- under the high-source cover: S2, the fast lock past the drain being a member
    intro i hib y hy ell e hcast hsi
    exact Compose.Growing.healed_source_votes_at hc.s2
      (Compose.Growing.HealedOrigin.of_lock (rL := healedLockFloor sp a)
        (rO := healedOriginFloor sp a) hs
        (Compose.Growing.lockWithin_iff.2 ⟨x, r, hx, hrb, Or.inl ⟨CV, hfast⟩⟩)) .refl
      (Compose.Growing.hVoteAt_iff.2 ⟨hy, ell, hcast⟩) hib hsi
  apply hp.fast_source_votes_of_domain_before_at hx hfast
    (hp.clean_window_timing_at hs s (by have := sp.two_le_k; clear * - this; omega))
  intro y i ell e hy hcast hib hsi hprior
  rcases hfast with ⟨ellX, C, hupd, hconf, hdeep, _⟩ | hop
  · have hBC := ((AC.deepest_mem hdeep).1.1.2.2).mono
      ((frame_tree_subset_at hp.run hp.noColl hx hupd.1).2.trans hxU)
    exact ProposalImpl.result_prefix_vote_domain_before_of_quarantine_at hp hx hy
      ⟨ellX, hupd, hconf, rfl⟩ hBC hs hrb hcast hsi hib hprior hpre
  · exact hp.optimistic_vote_domain_before_of_quarantine_at hx hy hop hs hrb hcast hsi hib hprior
      hpre

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
