module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResultSupport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Next
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The finite latest-result induction under growing faults

`late_result_prefix_votes_before_at`: every cast at a time `≤ b`, by a node honest at its cut,
of a slot after the label `s` of a result of a writer honest at its update, extends a block `B`
below the result, given the domain and stored-lock inputs. The induction is on the cast's cut;
every writer, cast and vote is read at its own cut, and ancestry is in the blocks held while
honest. The first label `s + 1` transfers the result (its counted votes carried from the writer,
honest at its update, to the voter, honest at its cast); a later label transfers the earlier
votes of nodes honest at them, all extending `B` by induction, counted at the voter's cut.

The node-local facts of the cast are read on the prefix through the cast's time
(`castAt_facts_at`); the first transfer's carry, live locks and writer merge, and the later
transfer's carry, are the reset-form suppliers of `Kernel/ResultSupport`. The transfers are the
growing AC layer's `result_transfer_anc` and `next_transfer`. -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-! ### The induction -/

/-- **The finite latest-result induction**, the kernel skeleton's
`ResetPremisesUpTo.late_result_prefix_votes_before_at` with the same statement: by strong
induction on the cast's cut. -/
theorem late_result_prefix_votes_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x : Fin sp.n} {r s : Nat}
    (hx : x ∈ H (tr.time r))
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocksAt H) B C)
    (_hrb : tr.time r ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts s)
    (hdomain : ∀ y i ell e, y ∈ H (tr.time i) → SA.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → s < e.msg.slot →
      (∀ z q e', q < i → Compose.Growing.HVoteAt tr H z q e' →
        s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B) →
      Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
        B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
    (hstored : ∀ y i ell e, y ∈ H (tr.time i) → SA.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → e.msg.slot = s + 1 → ∀ l ∈ (tr.projAC.state y i).locks,
        sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
        ∀ Y ∈ tr.HonestBlocksAt H, Y.root = l.block → Compatible (tr.HonestBlocksAt H) Y B) :
    ∀ i, tr.time i ≤ b → ∀ y, y ∈ H (tr.time i) → ∀ ell e,
      SA.CastAt tr.projAC y i ell e → s < e.msg.slot →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hrun' := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hib y hy ell e hcast hsi
  have hprior : ∀ z q e', q < i → Compose.Growing.HVoteAt tr H z q e' →
      s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B := by
    intro z q e' hqi hv hse
    obtain ⟨hz, ell', hc'⟩ := Compose.Growing.hVoteAt_iff.1 hv
    exact ih q hqi ((hrun.time_mono hqi.le).trans hib) z hz ell' e' hc' hse
  have hd := hrun.time_nonneg i
  obtain ⟨⟨hΦ, hΦU⟩, hhead, hsl⟩ := castAt_facts_at hrun hnc hy hcast
  rcases hdomain y i ell e hy hcast hib hsi hprior with hBF | hv
  · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := hhead
    exact ⟨Hd, hΦU hHd, hHdr, hBF.trans (hfHd.mono hΦU)⟩
  have hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B := (hΦ.rooted.2 B hv.1.1).mono hΦU
  have hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n := by
    have h3 := hp.faults (tr.time i) hd hib
    have := Fin.pos x
    have hn : sp.n = sp.toParams.n := rfl
    omega
  by_cases hfirst : e.msg.slot = s + 1
  · exact SA.Growing.result_transfer_anc hrun' hx hres hBC hy hcast hfirst
      (result_carry_reset_at hp hc hx hres hts hy hcast hfirst (hFB.trans hBC))
      (by rw [← hfirst]; exact Or.inl hv)
      (live_locks_of_stored_at hrun hnc hf hy hcast hfirst hv.1.1
        (hstored y i ell e hy hcast hib hfirst)
        (fun z q hq hz e' he hslot => hprior z q e' hq
          (Compose.Growing.hVoteAt_iff.2 ⟨hz, he⟩) (by omega)))
      (writer_merged_reset_at hp hx hres hts hy hcast hfirst)
  · obtain ⟨m, hm⟩ : ∃ m, e.msg.slot = m + 1 := ⟨e.msg.slot - 1, by omega⟩
    have hsm : s < m := by omega
    have htime : sp.ts (m + 1 : Nat) ≤ tr.time i :=
      (SA.ts_le_iff_le_slot sp hd _).mpr (by rw [← hsl, hm])
    have hts1 : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    have hmts : cutZ sp.toParams g ≤ sp.ts m :=
      hts.trans ((SA.ts_le_iff sp).mpr (by clear * - hsm; omega))
    -- a label-`m` vote of a node honest at it is at an earlier cut
    have hall : ∀ z q e', z ∈ H (tr.time q) → SA.VoteAt tr.projAC z q e' → e'.msg.slot = m →
        SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B := by
      rintro z q e' hz ⟨ell', hc'⟩ hslot
      have hqi : q < i := by
        by_contra hn
        have hq := (castAt_facts_at hrun hnc hz hc').2.2
        have := SA.slot_mono sp hd (hrun.time_mono (Nat.le_of_not_gt hn))
        omega
      exact hprior z q e' hqi (Compose.Growing.hVoteAt_iff.2 ⟨hz, ell', hc'⟩) (by omega)
    exact SA.Growing.next_transfer sp _ ro H _ tr.projAC proposer hrun' m y i B ell e hy hcast hm
      hall
      (hp.half_committee_at hmts (t := tr.time i) (by linarith only [htime, hts1, hΔ]) hib)
      (honest_votes_carry_reset_at hp hc hy hcast hm hmts hall hFB)
      (fault_bound_late_at hp (t := tr.time i)
        (hmts.trans (by linarith only [htime, hts1, hΔ])) hib)
      (by rw [← hm]; exact Or.inl hv)
      (fun z q hq hz e' he hslot => hprior z q e' hq
        (Compose.Growing.hVoteAt_iff.2 ⟨hz, he⟩) (by omega))

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
