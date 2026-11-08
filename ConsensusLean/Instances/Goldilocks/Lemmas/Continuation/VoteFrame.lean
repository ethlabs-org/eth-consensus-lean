module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Seed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Accountable

public section

/-! # The frozen witness at a vote after the hand-over (M8, S3 at votes)

The sleepy V-step after the split slot transfers a member `B` of the healed family to an honest
vote of a slot `s + 1 > σ + 1` only if `B` is in the vote's viable voter tree or at or below its
`fc_root`. From genesis this is `vote_frame_at`: `Σ.J`, hence `Σ.F` and `fc_root`, compare with `B`
through the honest sources of the voter's high rows, which sit below origins of labels at most `s`
(`vote_row_source`), all pairwise compatible; and `B` lies between `Σ.F` and a frozen witness.

After a hand-over the voter's tree holds pre-reset rows whose sources sit below origins of labels
under the floors, outside the family, so the genesis classification of the rows does not apply.
The seeded form splits on the voter's justified height `h_j` against the reset height `H_z`
(design §4.2, §14.3): a high `Σ.J` is on the chain of a family member (the row of its honest
quorum member, `HandoverSeed.rows` before `T`, the lock write of its source after `T`); a low
`Σ.F` is below the reset seed (`GoldilocksRun.finalized_anc_of_lt_conv`), and a low `Σ.J` in the
active case is below the seed by equal-height agreement (`J_eq_of_hj_eq_conv`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF : Time}

/-- **S3 at a vote after the hand-over (the seeded frozen witness).** At an honest vote of a
slot `s + 1` with `s ≥ σ + 1`, cast at a time `≤ b`, a member `B` of the healed family within `b`
of label at most `s`, extended by an honest slot-`s` vote, is in the vote's viable voter block
tree or at or below its `fc_root`, given `P_{s+1}` up to `b`, the reset service through `b`, the
seed's catch-up, the slot counts from `r` and conviction below a third.

Open (`sorry`): the seeded classification of the voter's FG state. The genesis proof
(`vote_frame_at`, through `vote_frame_core`) needs every honest row of the voter's tree at a height
`≥ h_j` to have a source below an origin of label `≤ s` compatible with `B`; after a hand-over this
holds for the rows at heights `≥ H_z + 1` (signed after the reset: `HandoverSeed.rows` up to `T`,
the source's lock write after `T`, `lock_write_at`), and the low rows are excluded by the low-`J`
case analysis of §4.2 with `ChainConvictedBelow` (the reset seed held at the vote,
`HandoverSeed.seedHeld` extended past `T` by tree monotonicity, §14.5). -/
theorem seeded_vote_frame_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {T : Time} {r σ : Nat}
    (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) {b : Time} (hTb : T ≤ b)
    (hsvc : Healing.Growing.ResetService tr H g ΔF b) (hB : SleepyBoundsFrom tr H r b)
    (hcv : ChainConvictedBelow tr H) {s : Nat} (hs : σ + 1 ≤ s)
    (hP : HealedOriginsBelow tr H g r (r + sp.k - 1) (s + 1) b) {y : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : SA.CastAt tr.projAC y i ℓ e) (hes : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat}
    (hBm : HealedOrigin tr H g r (r + sp.k - 1) B j b) (hj : j ≤ s)
    (hw : ∃ x k e', HVoteAt tr H x k e' ∧ e'.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
      Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot := by
  sorry

end Consensus.Goldilocks.Compose.Growing

end
