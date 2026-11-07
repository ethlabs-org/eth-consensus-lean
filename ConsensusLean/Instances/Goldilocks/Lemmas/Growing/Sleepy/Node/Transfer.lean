module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Growing
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule

public section

/-! # Goldilocks under `Sleepy` with growing faults: the transfer of votes

* `vote_extends_of_counted_batch_at` (SA level): a counted batch of validators honest at the
  vote's cut `i`, whose witnessing votes are events of nodes honest at them, makes the successor
  vote extend `B` (the static `vote_extends_of_counted_batch` on the prefix through `tr.time i`).

`acRun_upTo_of_growing` is the stand-in for the SA retention lemma of the growing AC layer
(`SA.Growing.ACRun` on the prefix through `d ≥ 0` is a static `SA.ACRun` for `H d`, inside the
same `U`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

section SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Time → Set (Fin sp.n)}
  {U : Set (SA.Blk sp.n FGP)} {tr' : SA.SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

/-- Stand-in: the prefix of a growing-fault AC run is a static AC run for `H d`, inside `U`. -/
theorem acRun_upTo_of_growing (_hrun : SA.Growing.ACRun proposer tr' H U) {d : Time}
    (_hd : 0 ≤ d) : SA.ACRun proposer (tr'.upTo d) (H d) U := by
  sorry

/-- **The counted batch** under growing faults: at a slot-`(s+1)` vote of a node honest at its cut
`i`, a batch `SX` of validators honest at `i`, each with a slot-`s` vote (an event of a node honest
at it), all such votes extending `B` and carried, outnumbering half of a cover `W` of the merged
voters, with every live lock compatible with `B`, makes the vote extend `B`. -/
theorem vote_extends_of_counted_batch_at (hrun : SA.Growing.ACRun proposer tr' H U)
    {s : Nat} {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr'.time i))
    {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt tr' y i ℓ e) (hs : e.msg.slot = s + 1) {B : SA.Blk sp.n FGP}
    (hviab : SA.ViableAtVote ℓ e (s + 1) B)
    {SX W : Set (Fin sp.n)} (hSXH : SX ⊆ H (tr'.time i))
    (hSXv : ∀ x ∈ SX, ∃ j e', x ∈ H (tr'.time j) ∧ SA.VoteAt tr' x j e' ∧ e'.msg.slot = s)
    (hall : ∀ x ∈ SX, ∀ j e', x ∈ H (tr'.time j) → SA.VoteAt tr' x j e' → e'.msg.slot = s →
      SA.VoteExtends U e'.msg B)
    (hW : SA.voters (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes ⊆ W)
    (hcount : W.ncard < 2 * SX.ncard)
    (hcarry : SA.CarryAt tr' U y i e s
      {v | ∃ x ∈ SX, ∃ j e', x ∈ H (tr'.time j) ∧ SA.VoteAt tr' x j e' ∧ e'.msg = v ∧
        v.slot = s})
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr'.time i), Compatible U L B) :
    SA.VoteExtends U e.msg B := by
  have hm := hrun.localRun.time_mono
  have hanti := hrun.localRun.antitone
  have hd := hrun.localRun.time_nonneg i
  have hr := acRun_upTo_of_growing hrun hd
  have hc' : SA.CastAt (tr'.upTo (tr'.time i)) y i ℓ e := sa_castAt_upTo.mpr ⟨le_rfl, hc⟩
  -- a slot-`s` vote of a node honest at it is at a time before `t_{s+1} ≤ t_i`
  have hti : sp.ts ((s + 1 : Nat) : Int) ≤ tr'.time i := by
    have h := (SA.castAt_spec hr.localRun hy hc').2.1
    rw [hs] at h
    change s + 1 = sp.slot (tr'.time i) at h
    exact (SA.ts_le_iff_le_slot sp hd _).2 (by exact_mod_cast h.le)
  have hji : ∀ x j e', x ∈ H (tr'.time j) → SA.VoteAt tr' x j e' → e'.msg.slot = s →
      tr'.time j ≤ tr'.time i := by
    intro x j e' hx ⟨ℓx, hcx, hex⟩ hes
    have hdj := hrun.localRun.time_nonneg j
    have h := (SA.castAt_spec (acRun_upTo_of_growing hrun hdj).localRun hx
      (sa_castAt_upTo.mpr ⟨le_rfl, hcx, hex⟩)).2.1
    rw [hes] at h
    change s = sp.slot (tr'.time j) at h
    refine (lt_of_not_ge fun hge => ?_).le.trans hti
    have := (SA.ts_le_iff_le_slot sp hdj _).1 hge
    omega
  have hsub : {v | ∃ x ∈ SX, ∃ j e', SA.VoteAt (tr'.upTo (tr'.time i)) x j e' ∧ e'.msg = v ∧
      v.slot = s} ⊆ {v | ∃ x ∈ SX, ∃ j e', x ∈ H (tr'.time j) ∧ SA.VoteAt tr' x j e' ∧
        e'.msg = v ∧ v.slot = s} := by
    rintro v ⟨x, hx, j, e', hv, rfl, hvs⟩
    obtain ⟨hjd, hv⟩ := sa_voteAt_upTo.mp hv
    exact ⟨x, hx, j, e', hanti hjd (hSXH hx), hv, rfl, hvs⟩
  have hT : sp.ts s + 3 * sp.Δ ≤ tr'.time i := by
    have : sp.ts ((s + 1 : Nat) : Int) = sp.ts s + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    linarith [sp.toParams.hΔ]
  refine Compose.vote_extends_of_counted_batch hr hy hc' hs hviab hSXH (fun x hx => ?_)
    (fun x hx j e' hv hes => ?_) hW hcount ⟨⟨hcarry.awake, le_rfl⟩, hcarry.joined,
      fun v hv => ?_, fun v hv => hcarry.holds v (hsub hv)⟩ hlocks
  · obtain ⟨j, e', hxj, hv, hes⟩ := hSXv x hx
    exact ⟨j, e', sa_voteAt_upTo.mpr ⟨hji x j e' hxj hv hes, hv⟩, hes⟩
  · obtain ⟨hjd, hv⟩ := sa_voteAt_upTo.mp hv
    exact hall x hx j e' (hanti hjd (hSXH hx)) hv hes
  · obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads v (hsub hv)
    refine ⟨Hv, hHv, hHvr, fun X hX => ?_⟩
    exact (hacc X hX).imp_right fun ⟨k, hk, hkT⟩ =>
      ⟨k, (ac_acceptAt_upTo _).mpr ⟨(hkT.le.trans hT), hk⟩, hkT⟩

end SA

end Consensus.Goldilocks.Compose.Growing

end
