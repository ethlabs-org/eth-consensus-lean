module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs

public section

/-! # Frozen growing interface of the retained-origin transports

The growing forms of the retention transports of `Healing/Retention/{Boot,Prefix,Finality}`
that the clean cluster and its consumers read, frozen under their final names (static name +
`_at`). Each node is honest at its own cut; a reader of a held state is honest at an observation
time `t` after the state's cuts. Beyond the static statements, they add only the fault-count
bounds `≤ b`, because growing faults are counted only through the horizon:

* `low_finalized_below_origin_at`, `left_entry_origin_at`;
* `high_J_root_of_held_at_call_before_at`, `low_root_of_held_seed_at_call_at`;
* `high_floor_signed_source_of_row_bound_at`;
* `half_committee_at`: the voters of slot `m` honest at a later observation `t ≤ b` are half
  the committee.

Each theorem here is an open `sorry`; this module is deleted when the proofs land. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- A low finalized block of a reader honest at `t ≤ b` is below every bounded high origin. -/
theorem low_finalized_below_origin_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {m : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < m, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) (hlow : (tr.state y m).fg.hj ≤ HZ tr H g) {x : Fin sp.n}
    {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B)
    (hib : tr.time i ≤ b) :
    Anc (tr.HonestBlocksAt H) (tr.state y m).fg.F B := by
  sorry

/-- **Left-entry provenance**: a high entry left by a reader honest at `t ≤ b` is the target of
a held attestation whose signer is honest at `t` and wrote a high origin above the entry before
signing. -/
theorem left_entry_origin_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {E C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hE : E ∈ (tr.state y k).fg.tree) (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h) (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h) :
    ∃ W ∈ (tr.state y k).fg.tree, ∃ att ∈ W.fgPayload, ∃ v d, v ∈ H t ∧ d < k ∧
      tr.SignAt v d att ∧ att.T = E.root ∧ ∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧
        Anc (tr.HonestBlocksAt H) E O := by
  sorry

/-- A call of a node honest at it, with a high justified height, has its finalized-chain root
compatible with every held block compatible with the earlier high origins. -/
theorem high_J_root_of_held_at_call_before_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {i k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time i)) (hBx : B ∈ (tr.state x i).fg.tree) (hy : y ∈ H (tr.time k))
    (hkb : tr.time k ≤ b) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ell)
    (hhigh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj)
    (hcompare : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocksAt H) B O) :
    Compatible (tr.HonestBlocksAt H) ell.frame.fcRoot B := by
  sorry

/-- A call of a node honest at it, with a low justified height and a held high seed, has its
finalized-chain root compatible with every held block compatible with the seed. -/
theorem low_root_of_held_seed_at_call_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y v : Fin sp.n} {r i q m : Nat} {B S : SA.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time r)) (hBx : B ∈ (tr.state x r).fg.tree) (hrb : tr.time r ≤ b)
    (hy : y ∈ H (tr.time i)) (hib : tr.time i ≤ b)
    (hS : HighOrigin tr H g v q m S) (hqb : tr.time q ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ell) (hSy : S ∈ (tr.state y i).fg.tree)
    (hlow : (tr.state y i).fg.hj ≤ HZ tr H g)
    (hBS : Compatible (tr.HonestBlocksAt H) B S)
    (hheld : Anc (tr.HonestBlocksAt H) ell.frame.F B → B ∈ ell.frame.tree) :
    Compatible (tr.HonestBlocksAt H) ell.frame.fcRoot B := by
  sorry

/-- **A high floor has a signed source below a bounded row label**: for a reader honest at
`t ≤ b`, a high origin under the reader's head-height floor yields a high origin, of a label
below `u`, above an entry at or past the floor, signed by the origin's writer after the write. -/
theorem high_floor_signed_source_of_row_bound_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {i j k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {u : Nat}
    (hrow : ∀ W ∈ (tr.state y k).fg.tree, ∀ att ∈ W.fgPayload,
      ∀ v d, v ∈ H (tr.time d) → tr.SignAt v d att → d < k → ∀ r l O,
        r < d → HighOrigin tr H g v r l O → l < u)
    (hpair : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      ∀ v' r' l' O', r' < k → HighOrigin tr H g v' r' l' O' →
      Compatible (tr.HonestBlocksAt H) O O')
    (hcomp : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocksAt H) B O)
    (hfloor : ((tr.state x i).fg.σ B.root).h < (tr.state y k).fg.headHeightFloor) :
    ∃ v r l O E, r < k ∧ HighOrigin tr H g v r l O ∧ l < u ∧
      E ∈ (tr.state y k).fg.tree ∧ Anc (tr.HonestBlocksAt H) E O ∧
      Anc (tr.HonestBlocksAt H) B O ∧
      (tr.state y k).fg.headHeightFloor ≤ ((tr.state y k).fg.σ E.root).h ∧
      ∃ d att, r < d ∧ d < k ∧ v ∈ H (tr.time d) ∧ tr.SignAt v d att ∧ att.T = E.root := by
  sorry

/-- **Half the committee votes**: the nodes honest at an observation `t ∈ [t_m + Δ, b]` that
voted in slot `m` while honest are at least half the committee, for a slot `m` past `c_z`. -/
theorem half_committee_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {m : Nat}
    (hm : cutZ sp.toParams g ≤ sp.ts m) {t : Time} (hmt : sp.ts m + sp.Δ ≤ t) (htb : t ≤ b) :
    sp.n ≤ 2 * {z | z ∈ H t ∧ ∃ q e, z ∈ H (tr.time q) ∧ SA.VoteAt tr.projAC z q e ∧
      e.msg.slot = m}.ncard := by
  sorry

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
