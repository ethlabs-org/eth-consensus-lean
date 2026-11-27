module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Frontier.Seed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Frontier.Accountable
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Frontier.Rows

public section

/-! # The frozen witness at a vote after the hand-over (S3 at votes)

The sleepy V-step after the split slot transfers a member `B` of the healed family to an honest
vote of a slot `s + 1 > σ + 1` only if `B` is in the vote's viable voter tree or at or below its
`fc_root`. From genesis this is `vote_frame_at`: `Σ.J`, hence `Σ.F` and `fc_root`, compare with `B`
through the honest sources of the voter's high rows, which sit below origins of labels at most `s`
(`vote_row_source`), all pairwise compatible; and `B` lies between `Σ.F` and a frozen witness.

After a hand-over the voter's tree holds pre-reset rows whose sources sit below origins of labels
under the floors, outside the family, so the genesis classification of the rows does not apply. The
seeded form (`seeded_vote_frame_of`, `Healing/Frontier/Rows`) splits on the voter's justified height
`h_j` against the reset height `H_z`: the rows naming entries of height `≥ H_z + 1` have sources
below members of labels at most `s` (the reset cluster's high rows before `T`, the signer's lock
write after `T`); a high `Σ.J` is such an entry; a low reader's `fc_root` is below the held reset
seed (`GoldilocksRun.finalized_anc_of_lt_conv` for `Σ.F`, no contest at the seed's height for
`Σ.J`). -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams Vote Payload)

variable {sp : ACParams}

variable {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp).State} {g ΔF : Time}

/-- **S3 at a vote after the hand-over (the seeded frozen witness).** At an honest vote of a
slot `s + 1` with `s ≥ σ + 1`, cast at a time `≤ b`, a member `B` of the healed family within `b`
of label at most `s`, extended by an honest slot-`s` vote, is in the vote's viable voter block
tree or at or below its `fc_root`, given `P_{s+1}` up to `b`, the reset service through `b`, the
seed's catch-up, the slot counts from `r` and conviction below a third (`seeded_vote_frame_of`). -/
theorem seeded_vote_frame_at (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {T : Time} {r σ : Nat}
    (hseed : HandoverCore tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK)) {b : Time}
      (hTb : T ≤ b)
    (hsvc : Healing.Growing.ACResetService tr H g ΔF) (hB : SleepyBoundsFrom tr H r b)
    (hcv : ChainConvictedBelowUpTo tr H b) {s : Nat} (hs : σ + 1 ≤ s)
    (hP : HealedOriginsBelow tr H g r (r + sp.k - 1) (s + 1) b) {y : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : AC.CastAt tr.projAC y i ℓ e) (hes : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) {B : AC.Blk sp.n (List (FG.Att sp.n))} {j : Nat}
    (hBm : HealedOrigin tr H g r (r + sp.k - 1) B j b) (hj : j ≤ s)
    (hw : ∃ x k e', HVoteAt tr H x k e' ∧ e'.msg.slot = s ∧
      AC.VoteExtends (tr.HonestBlocksAt H) e'.msg B)
    {K : AC.CommitteeDict sp.n} (hK : CommitteeFacts tr H K)
    (hKB : CommitteeBoundsFrom tr H K r b) :
    B ∈ ℓ.frame.viableTree (AC.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
      Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot :=
  seeded_vote_frame_of hrun hnc hseed hTb hsvc hB hcv hs hP hy hc hes hib
    (fun C l hC hl => healedOriginsBelow_iff.1 hP B j C l (by omega) (by omega) hBm hC) hw hK hKB

end Consensus.Goldilocks.Compose.Growing

end
