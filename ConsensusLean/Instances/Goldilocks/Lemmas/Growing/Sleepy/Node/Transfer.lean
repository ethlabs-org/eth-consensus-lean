module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.GrowingPremises
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy` with growing faults: the transfer of votes

* `vote_extends_of_batch_at`: at a slot-`(s+1)` vote of a node honest at its cut `i`, the slot-`s`
  voters still honest at `tr.time i` are a counted batch, so the vote extends `B` (the static
  `vote_extends_of_counted_batch` on the prefix through `tr.time i`).
The prefix of the growing run is a static AC run (`acRun_upTo`). -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams Vote Payload)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n}

/-- A slot-`s` vote of a node honest at it precedes every cut at a time `≥ t_{s+1}`. -/
theorem vote_cut_lt {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {x : Fin sp.n} {j : Nat} {e' : AC.Em sp (List (FG.Att sp.n))} (hv : HVoteAt tr H x j e')
    {s : Nat} (hes : e'.msg.slot = s) {i : Nat} (hi : sp.ts ((s + 1 : Nat) : Int) ≤ tr.time i) :
    tr.time j < sp.ts ((s + 1 : Nat) : Int) ∧ j < i := by
  obtain ⟨hx, ℓx, hcx, hex⟩ := hVoteAt_iff.1 hv
  have h := (castAt_spec_at hrun hnc hx ⟨hcx, hex⟩).2.1
  rw [hes] at h
  change s = sp.slot (tr.time j) at h
  have hlt : tr.time j < sp.ts ((s + 1 : Nat) : Int) := lt_of_not_ge fun hge => by
    have := (AC.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).1 hge
    omega
  exact ⟨hlt, lt_of_not_ge fun hij => absurd (hrun.time_mono hij) (not_le.2 (hlt.trans_le hi))⟩

/-- Lift the static counted batch through the receiving cut. The batch is still honest there;
the cover includes the still-honest slot voters and the compromised committee members. -/
theorem vote_extends_of_counted_batch_at {ini}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr)
    {K : AC.CommitteeDict sp.n} (hTK : AC.CommitteeTAt K tr.projAC H)
    {s : Nat} {y : Fin sp.n} {i : Nat} {ℓ : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hc : AC.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hviab : AC.ViableAtVote ℓ e (s + 1) B)
    {SX W : Set (Fin sp.n)} (hSXH : SX ⊆ H (tr.time i))
    (hSXv : ∀ x ∈ SX, ∃ j e', HVoteAt tr H x j e' ∧ e'.msg.slot = s)
    (hall : ∀ x ∈ SX, ∀ j e', HVoteAt tr H x j e' → e'.msg.slot = s →
      AC.VoteExtends (tr.HonestBlocksAt H) e'.msg B)
    (hW : ∀ x j e', HVoteAt tr H x j e' → x ∈ H (tr.time i) → e'.msg.slot = s → x ∈ W)
    (hWc : K.committee s ∩ (H (tr.time i))ᶜ ⊆ W) (hcount : W.ncard < 2 * SX.ncard)
    (hcarry : AC.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s
      {v | ∃ x ∈ SX, ∃ j e', HVoteAt tr H x j e' ∧ e'.msg = v ∧ v.slot = s})
    (hlocks : ∀ L ∈ AC.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocksAt H) L B) :
    AC.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hΔ := sp.toParams.hΔ
  have hd := hrun.time_nonneg i
  have hsub := upTo_subset hrun hd
  have hU := honestBlocksAt_coherent hrun hnc
  have hr := acRun_upTo hrun hnc hd
  have hc' : AC.CastAt (tr.projAC.upTo (tr.time i)) y i ℓ e := ac_castAt_upTo.mpr ⟨le_rfl, hc⟩
  have hts1 := AC.ts_succ (sp := sp) s
  have hti : sp.ts ((s + 1 : Nat) : Int) ≤ tr.time i := by
    have h := (castAt_spec_at hrun hnc hy hc).2.1
    rw [hs] at h
    change s + 1 = sp.slot (tr.time i) at h
    exact (AC.ts_le_iff_le_slot sp hd _).2 (by exact_mod_cast h.le)
  have hT : sp.ts s + 3 * sp.Δ ≤ tr.time i := by linarith
  have hvote : ∀ x j e', x ∈ H (tr.time i) → AC.VoteAt (tr.projAC.upTo (tr.time i)) x j e' →
      HVoteAt tr H x j e' := fun x j e' hx hv => by
    obtain ⟨hjd, hv⟩ := ac_voteAt_upTo.mp hv
    exact hVoteAt_iff.2 ⟨hrun.antitone hjd hx, hv⟩
  have hΦ := (frameIn_at hrun hnc hy hc.1).1
  have hBt : B ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact AC.mem_of_anc h hΦ.rooted.1
  have hBU := frame_upTo_at hrun hnc hy hc.1 hBt
  obtain ⟨Hd, hHd, hHdr, hBHd⟩ :=
    Compose.vote_extends_of_counted_batch hr hy hc' hs hviab (SX := SX) (W := W) hSXH
      (fun x hx => by
        obtain ⟨j, e', hv, hes⟩ := hSXv x hx
        exact ⟨j, e', ac_voteAt_upTo.mpr ⟨(vote_cut_lt hrun hnc hv hes hti).1.le.trans hti,
          (hVoteAt_iff.1 hv).2⟩, hes⟩)
      (fun x hx j e' hv hes => voteExtends_upTo hrun hnc hd (hSXH hx)
        (by rw [RunTrace.upTo_projAC]; exact hv) (hall x hx j e' (hvote x j e' (hSXH hx) hv) hes))
      (by
        rintro w ⟨v, hv, rfl⟩
        have hvs := AC.merged_vote_slotU hr.localRun.toU hr.vstart hy hc' v hv
        by_cases hw : v.val ∈ H (tr.time i)
        · obtain ⟨j, -, e', hv', he'⟩ := AC.honest_merged_voteU hr.toU hy hc' hv hw
          exact hW _ j e' (hvote _ j e' hw hv') hw (he' ▸ hvs)
        · exact hWc ⟨hvs ▸ hTK y i ℓ e hy hc s v hv, hw⟩)
      hcount
      ⟨⟨hcarry.awake, le_rfl⟩, hcarry.joined, fun v ⟨x, hx, j, e', hv, hev, hvs⟩ => by
        have hv' := hvote x j e' (hSXH hx) hv
        obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads v ⟨x, hx, j, e', hv', hev, hvs⟩
        obtain ⟨Hd₂, hHd₂, hHd₂r, -⟩ := AC.honest_headU hr.toU (hSXH hx) hv
        obtain rfl : Hv = Hd₂ := hU.1 hHv (hsub hHd₂) (hHvr.trans (hev ▸ hHd₂r.symm))
        refine ⟨Hv, hHd₂, hHvr, fun X hX => ?_⟩
        exact (hacc X (hX.mono hsub)).imp_right fun ⟨k, hk, hkT⟩ =>
          ⟨k, (ACTrace.upTo_acceptAt (tr := _)).mpr ⟨hkT.le.trans hT, hk⟩, hkT⟩,
        fun v ⟨x, hx, j, e', hv, hev, hvs⟩ =>
          hcarry.holds v ⟨x, hx, j, e', hvote x j e' (hSXH hx) hv, hev, hvs⟩⟩
      (fun L hL => compatible_upTo hrun hnc hd (frame_upTo_at hrun hnc hy hc.1 hL.1) hBU
        (hlocks L hL))
  exact ⟨Hd, hsub hHd, hHdr, hBHd.mono hsub⟩

/-- **The later batch** under growing faults: at a slot-`(s+1)` vote of a node honest at its cut
`i ≤ b`, for a slot `s ≥ σ₀` (its slot count available), if every earlier slot-`s` vote by a node
honest at it extends `B` and is carried, and every live lock is compatible with `B`, the vote
extends `B`. The batch is the slot-`s` voters still honest at `d = tr.time i`, which outnumber the
compromised members of the slot-`s` committee (`faults_lt_voters`, `d ≤ t_s + 5Δ`); a merged voter
not honest at `d` is such a member (T); the static counted batch applies on the prefix through
`d`. -/
theorem vote_extends_of_batch_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {K : AC.CommitteeDict sp.n} (hKB : CommitteeFacts tr H K)
    {b : Time} {σ₀ : Nat} (hBK : CommitteeBoundsFrom tr H K σ₀ b) {s : Nat}
    (hs₀ : σ₀ ≤ s) {y : Fin sp.n}
    {i : Nat} {ℓ : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : AC.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hviab : AC.ViableAtVote ℓ e (s + 1) B)
    (hall : ∀ x j e', j < i → HVoteAt tr H x j e' → e'.msg.slot = s →
      AC.VoteExtends (tr.HonestBlocksAt H) e'.msg B)
    (hcarry : AC.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s
      {v | ∃ x j e', HVoteAt tr H x j e' ∧ e'.msg = v ∧ v.slot = s})
    (hlocks : ∀ L ∈ AC.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocksAt H) L B) :
    AC.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hΔ := sp.toParams.hΔ
  have hd := hrun.time_nonneg i
  have hts1 := AC.ts_succ (sp := sp) s
  have hti : sp.ts ((s + 1 : Nat) : Int) ≤ tr.time i := by
    have h := (castAt_spec_at hrun hnc hy hc).2.1
    rw [hs] at h
    change s + 1 = sp.slot (tr.time i) at h
    exact (AC.ts_le_iff_le_slot sp hd _).2 (by exact_mod_cast h.le)
  have hti' : tr.time i ≤ sp.ts ((s + 1 : Nat) : Int) + sp.Δ :=
    hs ▸ (cast_head_fcRoot_at hrun hnc hy hc).2
  refine vote_extends_of_counted_batch_at hrun hnc (hKB.committeeTAt hrun hnc) hy hc hs hviab
    (SX := VotersAt tr H s (tr.time i))
    (W := VotersAt tr H s (tr.time i) ∪ (K.committee s ∩ (H (tr.time i))ᶜ))
    (fun x hx => (votersAt_iff.1 hx).1)
    (fun _ hx => (votersAt_iff.1 hx).2)
    (fun x _ j e' hv hes => hall x j e' (vote_cut_lt hrun hnc hv hes hti).2 hv hes)
    (fun _ j e' hv hx hes => Or.inl (votersAt_iff.2 ⟨hx, j, e', hv, hes⟩))
    (fun _ hx => Or.inr hx) ?_ ?_ hlocks
  · have hcount := faults_lt_voters hrun hnc hKB hBK (s := s) (d := tr.time i) hs₀
      (by linarith) hib (by linarith)
    have := Set.ncard_union_le (VotersAt tr H s (tr.time i))
      (K.committee s ∩ (H (tr.time i))ᶜ)
    omega
  · exact ⟨hcarry.awake, hcarry.joined,
      fun v ⟨x, _, j, e', hv, hev, hvs⟩ => hcarry.heads v ⟨x, j, e', hv, hev, hvs⟩,
      fun v ⟨x, _, j, e', hv, hev, hvs⟩ => hcarry.holds v ⟨x, j, e', hv, hev, hvs⟩⟩

end Consensus.Goldilocks.Compose.Growing

end
