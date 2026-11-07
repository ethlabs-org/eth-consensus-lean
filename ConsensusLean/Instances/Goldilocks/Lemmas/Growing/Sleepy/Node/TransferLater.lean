module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.TransferLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.VoteFrame
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy` with growing faults: the later transfer step

`later_transfer_step_at`: at a slot-`(s+1)` vote of a node honest at its cut `i ≤ b`, a block `B`
held while honest, compatible with every origin within `b` of label at most `s`, that every
slot-`s` vote of a node honest at it extends and that the earlier slot-`(s+1)` votes of nodes
honest at them extend, is extended by the vote (`vote_frame_at`, `vote_locks_compatible_at`, and
the batch counted at the voter's cut, `vote_extends_of_batch_at`).

`honest_batch_carry_at` carries every slot-`s` vote of a node honest at it to the vote, each voter
its own writer, honest at its vote and at its acceptance of the head. The per-writer carry
`carryAt_of_writer_at_stub` is the node-transport `carryAt_of_writer_at`, stated here with its
agreed shape until that module is on this branch. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- The per-writer carry of the node transport layer (`carryAt_of_writer_at`), with its agreed
shape; stand-in until that module is on this branch. -/
theorem carryAt_of_writer_at_stub (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b) {s : Nat}
    {w y : Fin sp.n} {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) (hi : tr.time i ≤ b)
    {CV : Set (Vote sp.n)}
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ k, w ∈ H (tr.time k) ∧ tr.projAC.SendOrAdmit w k v ∧ sp.ts s ≤ tr.time k ∧
        tr.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv, Hv.root = v.head ∧ Anc (tr.HonestBlocksAt H) ℓ.frame.F Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, w ∈ H (tr.time k) ∧ tr.projAC.AcceptAt w k Hv ∧
          tr.time k < sp.ts s + 2 * sp.Δ)) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV := by
  sorry

/-- **The batch reaches a next-slot vote** under growing faults: at a slot-`(s+1)` vote of a node
honest at its cut `i ≤ b` whose `Σ.F` is below `B`, every slot-`s` vote of a node honest at it,
all extending `B`, is carried; each voter is its own writer, honest at its vote and at its
acceptance of the head. -/
theorem honest_batch_carry_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b) {s : Nat}
    {y : Fin sp.n} {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hall : ∀ x k e', HVoteAt tr H x k e' → e'.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B)
    (hF : Anc (tr.HonestBlocksAt H) ℓ.frame.F B) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s
      {v | ∃ x j e', HVoteAt tr H x j e' ∧ e'.msg = v ∧ v.slot = s} := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hd := hrun.time_nonneg i
  have hone : ∀ v ∈ {v | ∃ x j e', HVoteAt tr H x j e' ∧ e'.msg = v ∧ v.slot = s},
      SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s {v} := by
    rintro v ⟨x, k, e', hv', rfl, hvs⟩
    obtain ⟨hxk, ℓk, hck, he'⟩ := hVoteAt_iff.1 hv'
    have hk := (castAt_spec_at hrun hnc hxk ⟨hck, he'⟩).2.1
    obtain ⟨⟨Hd, hHd, hHdr, -⟩, hkt⟩ := cast_head_fcRoot_at hrun hnc hxk ⟨hck, he'⟩
    obtain ⟨Hv, hHv, hHvr, hBHv⟩ := hall x k e' hv' hvs
    obtain rfl : Hd = Hv :=
      hU.1 ((frameIn_at hrun hnc hxk hck).2 hHd) hHv (hHdr.trans hHvr.symm)
    have hkt' : tr.time k < sp.ts s + 2 * sp.Δ := by
      rw [hvs] at hkt
      exact hkt.trans_lt (add_lt_add_of_le_of_lt le_rfl (lt_mul_of_one_lt_left hΔ (by norm_num)))
    refine carryAt_of_writer_at_stub (w := x) hrun hnc hsync hy hc hs hib ?_
    rintro v rfl
    refine ⟨hvs, ⟨k, hxk, ⟨ℓk, hck, Or.inl ⟨e', he', rfl⟩⟩,
      (SA.ts_le_iff_le_slot sp (hrun.time_nonneg k) s).2 (by omega), hkt'⟩,
      Hd, hHvr, hF.trans hBHv, ?_⟩
    rcases frame_anc_accepted_at hrun hnc hxk hck hHd .refl with hg | ⟨k', hk', hacc⟩
    · exact Or.inl hg
    · exact Or.inr ⟨k', hrun.antitone (hrun.time_mono hk') hxk, hacc,
        lt_of_le_of_lt (hrun.time_mono hk') hkt'⟩
  have hr := (acRun_upTo hrun hnc hd).localRun
  have hcT : SA.CastAt (tr.projAC.upTo (tr.time i)) y i ℓ e := sa_castAt_upTo.mpr ⟨le_rfl, hc⟩
  exact ⟨(hr.awake_of_call y hy i ℓ hcT.1).1, (castAt_spec_at hrun hnc hy hc).2.2.1,
    fun v hv => (hone v hv).heads v rfl, fun v hv => (hone v hv).holds v rfl⟩

/-- **Later batch under growing faults**: a slot-`s` voter honest at `t_s + Δ` (the slot count
there) gives the frame witness (`vote_frame_at`); below `fc_root` the vote extends `B`, otherwise
the batch of every slot-`s` vote, carried and counted at the voter's cut, with the live locks
compatible with `B` (`vote_locks_compatible_at`). -/
theorem later_transfer_step_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBounds tr H b) {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b) {y : Fin sp.n}
    {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBU : B ∈ tr.HonestBlocksAt H)
    (hBc : ∀ C j, OriginWithin tr H C j b → j ≤ s → Compatible (tr.HonestBlocksAt H) B C)
    (hall : ∀ x k e', HVoteAt tr H x k e' → e'.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B)
    (hE : SA.EarlierVotesExtendAt tr.projAC H (tr.HonestBlocksAt H) i (s + 1) B) :
    SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hd := hrun.time_nonneg i
  have hti : sp.ts ((s + 1 : Nat) : Int) ≤ tr.time i := by
    have h := (castAt_spec_at hrun hnc hy hc).2.1
    rw [hs] at h
    change s + 1 = sp.slot (tr.time i) at h
    exact (SA.ts_le_iff_le_slot sp hd _).2 (by exact_mod_cast h.le)
  have hts1 : sp.ts ((s + 1 : Nat) : Int) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  -- a slot-`s` voter still honest at `t_s + Δ`
  have hcount := faults_lt_voters hrun hnc hB (s := s) (d := sp.ts s + sp.Δ) le_rfl
    (by linarith) (by linarith)
  obtain ⟨x, hx⟩ : (VotersAt tr H s (sp.ts s + sp.Δ)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro h
    rw [h, Set.ncard_empty] at hcount
    omega
  obtain ⟨-, k, e', hv, hvs⟩ := votersAt_iff.1 hx
  have hvf := vote_frame_at hrun hnc hb hsync hB hP hy hc hs hib hBU hBc
    ⟨x, k, e', hv, hvs, hall x k e' hv hvs⟩
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hy hc.1
  rcases hvf with hvB | hBf
  swap
  · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := cast_head_fcRoot_at hrun hnc hy hc
    exact ⟨Hd, hΦU hHd, hHdr, hBf.trans (Anc.mono hΦU hfHd)⟩
  exact vote_extends_of_batch_at hrun hnc hB hy hc hs hib (Or.inl hvB)
    (fun x j e' _ hv hvs => hall x j e' hv hvs)
    (honest_batch_carry_at hrun hnc hsync hy hc hs hib hall
      (Anc.mono hΦU (hΦ.rooted.2 B hvB.1.1)))
    (vote_locks_compatible_at hrun hnc hB hy hc hs hib hBc hE)

end Consensus.Goldilocks.Compose.Growing

end
