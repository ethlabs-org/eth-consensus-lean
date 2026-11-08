module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.TransferFirst
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.TransferLater
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family

public section

/-! # Goldilocks under `Sleepy` with growing faults: extending the vote frontier

`votes_below_succ_at`: `P_{s+1}` and `V_s` up to `b` give `V_{s+1}` up to `b` over the healed
family, by strong induction on the cut of a slot-`(s+1)` vote of a node honest at it (the first
bad vote), with the first and later transfer steps. The step needs the slot count and the service
for slot `s`, an origin floor at most `s` (an origin of label `s` is then a member), the live locks
of slot at most `s` at the votes from the lock floor on (`hlive`), and the frozen witness at the
votes (`hframe`, S3 for a member of label at most `s` with an honest slot-`s` supporter). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **Extending the vote frontier under growing faults**: the first slot-`(s+1)` vote (of a node
honest at it) at a time `≤ b` that fails to extend a member of the healed family within `b` of
label `j ≤ s` does not exist. For `j < s` the later step applies to the member, with `V_s` for
every slot-`s` vote (cast before the vote's cut); for `j = s` the first step applies to the origin
above the member (a member, as `rO ≤ s`); both with the earlier slot-`(s+1)` votes from the
induction on the cut. -/
theorem votes_below_succ_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b) {σ₀ : Nat}
    (hB : SleepyBoundsFrom tr H σ₀ b) {g : Time} {rL rO s : Nat} (hs₀ : σ₀ ≤ s) (hrO : rO ≤ s)
    (hsa : a + κ ≤ sp.ts s)
    (hlive : ∀ y i ℓ e, y ∈ H (tr.time i) → SA.CastAt tr.projAC y i ℓ e → e.msg.slot = s + 1 →
      tr.time i ≤ b → ∀ l ∈ SA.liveLocks sp e.readPoint.locks ℓ.frame (tr.time i), l.slot ≤ s →
        rL ≤ l.slot)
    (hframe : ∀ y i ℓ e, y ∈ H (tr.time i) → SA.CastAt tr.projAC y i ℓ e → e.msg.slot = s + 1 →
      tr.time i ≤ b → ∀ B j, HealedOrigin tr H g rL rO B j b → j ≤ s →
      (∃ x k e', HVoteAt tr H x k e' ∧ e'.msg.slot = s ∧
        SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B) →
      B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
        Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot)
    (hP : HealedOriginsBelow tr H g rL rO (s + 1) b) (hV : HealedVotesBelow tr H g rL rO s b) :
    HealedVotesBelow tr H g rL rO (s + 1) b := by
  have hcomp : ∀ C j, HealedOrigin tr H g rL rO C j b → j ≤ s →
      ∀ C' j', HealedOrigin tr H g rL rO C' j' b → j' ≤ s →
        Compatible (tr.HonestBlocksAt H) C C' := fun C j hC hj C' j' hC' hj' =>
    healedOriginsBelow_iff.1 hP C j C' j' (by omega) (by omega) hC hC'
  have key : ∀ i, ∀ y e, HVoteAt tr H y i e → tr.time i ≤ b → e.msg.slot = s + 1 →
      ∀ C j, HealedOrigin tr H g rL rO C j b → j ≤ s →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg C := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro y e hv hib hs C j hC hj
      obtain ⟨hy, ℓ, hc⟩ := hVoteAt_iff.1 hv
      have hE : ∀ C' j', HealedOrigin tr H g rL rO C' j' b → j' ≤ s →
          SA.EarlierVotesExtendAt tr.projAC H (tr.HonestBlocksAt H) i (s + 1) C' :=
        fun C' j' hC' hj' x k hk hx e' hv' hs' => ih k hk x e' (hVoteAt_iff.2 ⟨hx, hv'⟩)
          ((hrun.time_mono hk.le).trans hib) hs' C' j' hC' hj'
      have hfr := hframe y i ℓ e hy hc hs hib
      have hlv := hlive y i ℓ e hy hc hs hib
      rcases hj.lt_or_eq with hj | hjs
      · have hti : sp.ts ((s + 1 : Nat) : Int) ≤ tr.time i := by
          have h := (castAt_spec_at hrun hnc hy ⟨hc.1, hc.2⟩).2.1
          rw [hs] at h
          change s + 1 = sp.slot (tr.time i) at h
          exact (SA.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2 (by exact_mod_cast h.le)
        exact later_transfer_step_at hrun hnc hsync hB hs₀ hsa hy hc hs hib hlv
          (fun C' j' hC' hj' => hcomp C j hC hj.le C' j' hC' hj') (hfr C j hC hj.le)
          (fun x k e' hv' hs' => healedVotesBelow_iff.1 hV C j hC x k e' hv'
            ((vote_cut_lt hrun hnc hv' hs' hti).1.le.trans (hti.trans hib)) (by omega) hs'.le)
          (hE C j hC hj.le)
      · subst hjs
        obtain ⟨O, hO, hCO⟩ := hC.below_origin hrun hnc
        have hOm : HealedOrigin tr H g rL rO O j b := HealedOrigin.of_origin hrO hO
        exact voteExtends_of_anc (first_transfer_step_at hrun hnc hsync hB hs₀ hsa hy hc hs hib
          hlv hO (fun C' j' hC' hj' => hcomp O j hOm le_rfl C' j' hC' hj')
          (hfr O j hOm le_rfl) (hE O j hOm le_rfl)) hCO
  refine healedVotesBelow_iff.2 fun C j hC y i e hv hib hj hm => ?_
  rcases Nat.lt_or_ge e.msg.slot (s + 1) with h | h
  · exact healedVotesBelow_iff.1 hV C j hC y i e hv hib hj (by omega)
  · exact key i y e hv hib (by omega) C j hC (by omega)

end Consensus.Goldilocks.Compose.Growing

end
