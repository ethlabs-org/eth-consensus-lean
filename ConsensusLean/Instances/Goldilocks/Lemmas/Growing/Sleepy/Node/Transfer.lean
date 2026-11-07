module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Growing
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest

public section

/-! # Goldilocks under `Sleepy` with growing faults: the transfer of votes

* `vote_extends_of_counted_batch_at` (SA level): a counted batch of validators honest at the
  vote's cut `i`, whose witnessing votes are events of nodes honest at them, makes the successor
  vote extend `B` (the static `vote_extends_of_counted_batch` on the prefix through `tr.time i`).
The prefix of the growing AC run is a static AC run (`SA.Growing.ACRun.upTo`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

section SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Time → Set (Fin sp.n)}
  {U : Set (SA.Blk sp.n FGP)} {tr' : SA.SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

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
  have hr := SA.Growing.ACRun.upTo hrun hd
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
    have h := (SA.castAt_spec (SA.Growing.ACRun.upTo hrun hdj).localRun hx
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

/-! ### Over a run -/

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- A slot-`s` vote of a node honest at it precedes every cut at a time `≥ t_{s+1}`. -/
theorem vote_cut_lt (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {x : Fin sp.n} {j : Nat} {e' : SA.Em sp (List (FG.Att sp.n))} (hv : HVoteAt tr H x j e')
    {s : Nat} (hes : e'.msg.slot = s) {i : Nat} (hi : sp.ts ((s + 1 : Nat) : Int) ≤ tr.time i) :
    tr.time j < sp.ts ((s + 1 : Nat) : Int) ∧ j < i := by
  obtain ⟨hx, ℓx, hcx, hex⟩ := hVoteAt_iff.1 hv
  have h := (castAt_spec_at hrun hnc hx ⟨hcx, hex⟩).2.1
  rw [hes] at h
  change s = sp.slot (tr.time j) at h
  have hlt : tr.time j < sp.ts ((s + 1 : Nat) : Int) := lt_of_not_ge fun hge => by
    have := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).1 hge
    omega
  exact ⟨hlt, lt_of_not_ge fun hij => absurd (hrun.time_mono hij) (not_le.2 (hlt.trans_le hi))⟩

/-- **The later batch** under growing faults: at a slot-`(s+1)` vote of a node honest at its cut
`i ≤ b`, if every earlier slot-`s` vote by a node honest at it extends `B` and is carried, and every
live lock is compatible with `B`, the vote extends `B`. The batch is the slot-`s` voters still
honest at `d = tr.time i`, which outnumber `(H d)ᶜ` (`faults_lt_voters`, `d ≤ t_s + 5Δ`); the static
counted batch applies on the prefix through `d`. -/
theorem vote_extends_of_batch_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hB : SleepyBounds tr H b) {s : Nat} {y : Fin sp.n}
    {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hviab : SA.ViableAtVote ℓ e (s + 1) B)
    (hall : ∀ x j e', j < i → HVoteAt tr H x j e' → e'.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B)
    (hcarry : SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s
      {v | ∃ x j e', HVoteAt tr H x j e' ∧ e'.msg = v ∧ v.slot = s})
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocksAt H) L B) :
    SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hΔ := sp.toParams.hΔ
  have hm := hrun.time_mono
  have hd := hrun.time_nonneg i
  have hsub := upTo_subset hrun hd
  have hU := honestBlocksAt_coherent hrun hnc
  have hr := acRun_upTo hrun hnc hd
  have hc' : SA.CastAt (tr.projAC.upTo (tr.time i)) y i ℓ e := sa_castAt_upTo.mpr ⟨le_rfl, hc⟩
  have hts1 : sp.ts ((s + 1 : Nat) : Int) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hti : sp.ts ((s + 1 : Nat) : Int) ≤ tr.time i := by
    have h := (castAt_spec_at hrun hnc hy hc).2.1
    rw [hs] at h
    change s + 1 = sp.slot (tr.time i) at h
    exact (SA.ts_le_iff_le_slot sp hd _).2 (by exact_mod_cast h.le)
  have hti' : tr.time i ≤ sp.ts ((s + 1 : Nat) : Int) + sp.Δ :=
    hs ▸ (cast_head_fcRoot_at hrun hnc hy hc).2
  -- a vote of the prefix by a validator honest at `d` is one of the run by a node honest at it
  have hvote : ∀ x j e', x ∈ H (tr.time i) → SA.VoteAt (tr.projAC.upTo (tr.time i)) x j e' →
      HVoteAt tr H x j e' := fun x j e' hx hv => by
    obtain ⟨hjd, hv⟩ := sa_voteAt_upTo.mp hv
    exact hVoteAt_iff.2 ⟨hrun.antitone hjd hx, hv⟩
  have hΦ := (frameIn_at hrun hnc hy hc.1).1
  have hBt : B ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact SA.mem_of_anc h hΦ.fcRoot_mem
  have hBU := frame_upTo_at hrun hnc hy hc.1 hBt
  have hT : sp.ts s + 3 * sp.Δ ≤ tr.time i := by linarith
  have h := Compose.vote_extends_of_counted_batch hr hy hc' hs hviab
    (SX := VotersAt tr H s (tr.time i)) (W := VotersAt tr H s (tr.time i) ∪ (H (tr.time i))ᶜ)
    (fun x hx => (votersAt_iff.1 hx).1)
    (fun x hx => by
      obtain ⟨-, j, e', hv, hes⟩ := votersAt_iff.1 hx
      exact ⟨j, e', sa_voteAt_upTo.mpr ⟨(vote_cut_lt hrun hnc hv hes hti).1.le.trans hti,
        (hVoteAt_iff.1 hv).2⟩, hes⟩)
    (fun x hx j e' hv hes => by
      have hv' := hvote x j e' (votersAt_iff.1 hx).1 hv
      refine voteExtends_upTo hrun hnc hd (votersAt_iff.1 hx).1
        (by rw [RunTrace.upTo_projAC]; exact hv)
        (hall x j e' (vote_cut_lt hrun hnc hv' hes hti).2 hv' hes))
    (by
      rintro w ⟨v, hv, rfl⟩
      by_cases hw : v.val ∈ H (tr.time i)
      · obtain ⟨j, -, e', hv', he'⟩ := SA.honest_merged_vote hr hy hc' hv hw
        refine Or.inl (votersAt_iff.2 ⟨hw, j, e', hvote _ j e' hw hv', ?_⟩)
        rw [he']; exact SA.merged_vote_slot hr.localRun hy hc' v hv
      · exact Or.inr hw)
    (by
      have hcount := faults_lt_voters hrun hnc hB (s := s) (d := tr.time i)
        (by linarith) hib (by linarith)
      have := Set.ncard_union_le (VotersAt tr H s (tr.time i)) (H (tr.time i))ᶜ
      omega)
    ⟨⟨hcarry.awake, le_rfl⟩, hcarry.joined, fun v ⟨x, hx, j, e', hv, hev, hvs⟩ => by
      have hv' := hvote x j e' (votersAt_iff.1 hx).1 hv
      obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads v ⟨x, j, e', hv', hev, hvs⟩
      obtain ⟨Hd₂, hHd₂, hHd₂r, -⟩ := SA.honest_head hr (votersAt_iff.1 hx).1 hv
      obtain rfl : Hv = Hd₂ := hU.1 hHv (hsub hHd₂) (hHvr.trans (hev ▸ hHd₂r.symm))
      refine ⟨Hv, hHd₂, hHvr, fun X hX => ?_⟩
      exact (hacc X (hX.mono hsub)).imp_right fun ⟨k, hk, hkT⟩ =>
        ⟨k, (ac_acceptAt_upTo _).mpr ⟨hkT.le.trans hT, hk⟩, hkT⟩,
      fun v ⟨x, hx, j, e', hv, hev, hvs⟩ =>
        hcarry.holds v ⟨x, j, e', hvote x j e' (votersAt_iff.1 hx).1 hv, hev, hvs⟩⟩
    (fun L hL => compatible_upTo hrun hnc hd (frame_upTo_at hrun hnc hy hc.1 hL.1) hBU
      (hlocks L hL))
  obtain ⟨Hd, hHd, hHdr, hBHd⟩ := h
  exact ⟨Hd, hsub hHd, hHdr, hBHd.mono hsub⟩

end Consensus.Goldilocks.Compose.Growing

end
