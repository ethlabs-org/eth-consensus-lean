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
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Clean fast sources and their votes, under growing faults

The growing form of the fast-source part of `Healing/Outcome/FiniteSources`: a clean fast source,
written by a node honest at its write, is extended by every later vote of a node honest at it
through the horizon, by strong induction on the cast's cut.

* The first successor vote is the growing first transfer (`SA.Growing.first_transfer_stored`): the
  counted votes reach the voter through the reset service from their releases, each while its
  writer is honest (`fastLock_writer_at`, `KernelProof.carry_of_senders`).
* A later vote is the growing next transfer (`SA.Growing.next_transfer`) over the half committee
  of the previous label.
* The vote domain is the result-prefix domain for a fast update and the optimistic vote domain
  (`optimistic_vote_domain_before_at`) for an optimistic lock. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- **Finite fast-source transfer**, with its vote domain supplied at each later vote of a node
honest at it, given the earlier votes of nodes honest at them. -/
theorem fast_source_votes_of_domain_before_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x : Fin sp.n} {r s : Nat} (hx : x ∈ H (tr.time r))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfast : SA.FastLockAt tr.projAC x r s B CV) (hts : cutZ sp.toParams g ≤ sp.ts s)
    (hdomain : ∀ y i ell e, y ∈ H (tr.time i) → SA.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → s < e.msg.slot →
      (∀ z q, z ∈ H (tr.time q) → q < i → ∀ e', SA.VoteAt tr.projAC z q e' →
        s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B) →
      Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
        B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot)) :
    ∀ i, tr.time i ≤ b → ∀ y, y ∈ H (tr.time i) → ∀ ell e, SA.CastAt tr.projAC y i ell e →
      s < e.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hgs : g ≤ sp.ts s := by
    have := Healing.lt_cutZ sp g
    have := SA.le_gbar g
    linarith
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hib y hy ell e hcast hsi
  have hprior : ∀ z q, z ∈ H (tr.time q) → q < i → ∀ e', SA.VoteAt tr.projAC z q e' →
      s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B := by
    rintro z q hz hqi e' ⟨ell', hc'⟩ hse
    exact ih q hqi ((hrun.time_mono hqi.le).trans hib) z hz ell' e' hc' hse
  have hd := hrun.time_nonneg i
  obtain ⟨⟨hΦ, hΦU⟩, hhead, hsl⟩ := KernelProof.castAt_facts_at hrun hnc hy hcast
  rcases hdomain y i ell e hy hcast hib hsi hprior with hBF | hv
  · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := hhead
    exact ⟨Hd, hΦU hHd, hHdr, hBF.trans (hfHd.mono hΦU)⟩
  have hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B := (hΦ.rooted.2 B hv.1.1).mono hΦU
  have htime : sp.ts e.msg.slot ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp hd _).mpr (by rw [hsl])
  by_cases hfirst : e.msg.slot = s + 1
  · have hts1 : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := SA.ts_succ s
    rw [hfirst] at htime
    have carry := KernelProof.carry_of_senders hp hc hts hy hcast hfirst (CV := CV)
      fun v hv' => by
        obtain ⟨hvs, ⟨k, hxk, hsend, hk1, hk2⟩, D, -, hDr, hBD, hacc⟩ :=
          fastLock_writer_at hac.localRun hx hfast v hv'
        exact ⟨hvs, ⟨x, k, hxk, hsend, hk1, hk2⟩, D, hDr, hFB.trans hBD,
          hacc.imp_right fun ⟨k, hk⟩ => ⟨x, k, hk⟩⟩
    have hfb := KernelProof.fault_bound_late_at hp (t := tr.time i)
      (hts.trans (by linarith only [htime, hts1, hΔ])) hib
    exact SA.Growing.first_transfer_stored hac _ (fun _ => SA.CommitteeP.full)
      (fun _ => SA.CommitteeT.full) (SA.size_binding_full hp.stock) hx hfast .refl hy hcast hfirst
      (KernelProof.reset_syncACAt hp hgs) carry ((SA.ncard_inter_full_lt_iff _ _ _).2 hfb)
      (SA.Growing.cs2_full_of_faultBoundAt hp.stock hfb)
      (by rw [← hfirst]; exact Or.inl hv)
      (fun z q hq hz e' he hslot => hprior z q hz hq e' he (by omega))
  · obtain ⟨m, hm⟩ : ∃ m, e.msg.slot = m + 1 := ⟨e.msg.slot - 1, by omega⟩
    have hsm : s < m := by omega
    rw [hm] at htime
    have hts1 : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := SA.ts_succ m
    have hmts : cutZ sp.toParams g ≤ sp.ts m :=
      hts.trans ((SA.ts_le_iff sp).mpr (by clear * - hsm; omega))
    -- a label-`m` vote of a node honest at it is at an earlier cut
    have hall : ∀ z q e', z ∈ H (tr.time q) → SA.VoteAt tr.projAC z q e' → e'.msg.slot = m →
        SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B := by
      rintro z q e' hz ⟨ell', hc'⟩ hslot
      have hqi : q < i := by
        by_contra hn
        have hq := (KernelProof.castAt_facts_at hrun hnc hz hc').2.2
        have := SA.slot_mono sp hd (hrun.time_mono (Nat.le_of_not_gt hn))
        omega
      exact hprior z q hz hqi e' ⟨ell', hc'⟩ (by omega)
    have hfb := KernelProof.fault_bound_late_at hp (t := tr.time i)
      (hmts.trans (by linarith only [htime, hts1, hΔ])) hib
    exact SA.Growing.next_transfer sp _ ro H _ tr.projAC proposer hac (SA.CommitteeDict.full sp.n)
      ⟨fun _ _ _ _ _ σ _ _ => SA.mem_full σ _, fun _ _ _ _ _ _ σ _ _ => SA.mem_full σ _⟩
      (fun _ _ _ _ _ _ _ v _ => SA.mem_full v.slot _) (SA.size_binding_full hp.stock)
      m y i B ell e hy hcast hm hall
      (by rw [hp.stock]
          exact hp.half_committee_at hmts (t := tr.time i)
            (by linarith only [htime, hts1, hΔ]) hib)
      (KernelProof.honest_votes_carry_reset_at hp hc hy hcast hm hmts hall hFB)
      ((SA.ncard_inter_full_lt_iff _ _ _).2 hfb)
      (SA.Growing.cs2_full_of_faultBoundAt hp.stock hfb)
      (by rw [← hm]; exact Or.inl hv)
      (fun z q hq hz e' he hslot => hprior z q hz hq e' he (by omega))

/-- **A clean fast source is extended by every later vote** of a node honest at it, through the
horizon. -/
theorem fast_source_votes_before_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x : Fin sp.n} {r s : Nat} (hx : x ∈ H (tr.time r))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfast : SA.FastLockAt tr.projAC x r s B CV)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b) :
    ∀ i, tr.time i ≤ b → ∀ y, y ∈ H (tr.time i) → ∀ ell e, SA.CastAt tr.projAC y i ell e →
      s < e.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hm := hp.run.time_mono
  have hxU : (tr.state x r).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨x, r, tr.time r, hp.run.time_nonneg r, fun _ hq => hm hq.le, hx, h⟩
  apply hp.fast_source_votes_of_domain_before_at hc hx hfast
    (hp.clean_window_timing_at hs s (by have := sp.two_le_k; clear * - this; omega))
  intro y i ell e hy hcast hib hsi hprior
  rcases hfast with ⟨ellX, C, hupd, hconf, hdeep, _⟩ | hop
  · have hBC := ((SA.deepest_mem hdeep).1.1.2.2).mono
      ((frame_tree_subset_at hp.run hp.noColl hx hupd.1).2.trans hxU)
    exact ProposalImpl.result_prefix_vote_domain_before_at hp hc hx hy ⟨ellX, hupd, hconf, rfl⟩
      hBC hs hrb hcast hsi hib hprior
  · exact hp.optimistic_vote_domain_before_at hc hx hy hop hs hrb hcast hsi hib hprior

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
