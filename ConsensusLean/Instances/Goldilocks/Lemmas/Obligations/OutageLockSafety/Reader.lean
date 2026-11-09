module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.FamilyInstance
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Locks
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Sources
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Unlocked
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage lock safety: consumers of the invariant

From the invariant at every cut (`outage_lock_inv`):

* `liveLockBlocks_compatible` ((i) at the reader, `outage_reader_locks`): the
  live lock blocks of an honest stored lock set, in the node's frame, are compatible with every
  block `B ⪯ P` (the read tip is below the origin);
* `reader_frame` (`outage_reader_frame`): `fc_root` is compatible with `B`, and `B`,
  when in the frame, is below the anchor or in the full viable tree; the live-lock chain holds
  at every honest cut (`lockInv_state`, `liveBlocks_chain_at`);
* `fastLock_compatible`: every honest fast lock block (update or optimistic
  selection) is compatible with `P`;
* `readPoint_liveLockBlocks_compatible_at` (live-lock compatibility at a cast's read point): the
  live lock blocks of an honest vote's read point are compatible with every block `B ⪯ P` (the
  read-point locks sit below stored locks or below the cut's optimistic selection,
  `SA.readPoint_locks_provenance`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {D : OutageLockPremises tr H proposer dg}

/-- **Transfer to a block below `P`**: a block compatible with `P` is compatible with every block
`B ⪯ P` (the read tip is below the origin). -/
theorem compatible_of_anc_right (hU : Coherent (tr.HonestBlocks H))
    {X B P : SA.Blk sp.n (List (FG.Att sp.n))} (hBP : Anc (tr.HonestBlocks H) B P)
    (hX : Compatible (tr.HonestBlocks H) X P) : Compatible (tr.HonestBlocks H) X B := by
  rcases hX with h | h
  · exact Anc.total hU h hBP
  · exact Or.inr (hBP.trans h)

/-- **(i) at a reader** (`outage_reader_locks`): at every honest cut and time, the live lock
blocks of the stored locks in the node's frame are compatible with every block `B ⪯ P`. -/
theorem liveLockBlocks_compatible (hinv : ∀ i, OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H)
    (m : Nat) (τ : Time) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBP : Anc (tr.HonestBlocks H) B D.P) :
    ∀ X ∈ SA.liveLockBlocks sp (tr.state y m).ac.locks (Node.frame (tr.state y m)) τ,
      Compatible (tr.HonestBlocks H) X B := by
  exact FamilySafety.liveLockBlocks_compatible_instance hinv hy m τ hBP

/-- **The lock invariant at every honest cut**, in the cut's own frame: the stored record names a
block of the node's tree above every stored lock block (`lockInv_of_reachable` at the last AC
call, or none at the initial state), and the record is in the frame once `Σ.F` is below it. -/
theorem lockInv_state (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) (m : Nat) :
    SA.LockInv (tr.HonestBlocks H) (tr.state y m).ac (Node.frame (tr.state y m)) := by
  exact FamilySafety.lockInv_state_instance hrun hnc hy m

/-- **The live lock blocks of an honest node lie on one chain** at every cut and time, in the
cut's frame (`lockInv_state`). -/
theorem liveBlocks_chain_at (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) (m : Nat) (τ : Time) :
    ∀ X ∈ SA.liveLockBlocks sp (tr.state y m).ac.locks (Node.frame (tr.state y m)) τ,
      ∀ Y ∈ SA.liveLockBlocks sp (tr.state y m).ac.locks (Node.frame (tr.state y m)) τ,
        Compatible (Node.frame (tr.state y m)).tree X Y :=
  FamilySafety.liveBlocks_chain_at_instance hrun hnc hy m τ

/-- **The reader frame** (`outage_reader_frame`): at an honest cut, for every block
`B ⪯ P`, `fc_root` is compatible with `B`, and `B`, when in the frame, is below the anchor or in
the full viable tree (the live-lock chain by `liveBlocks_chain_at`). -/
theorem reader_frame (hinv : ∀ i, OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H) (m : Nat)
    (t : Time) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBP : Anc (tr.HonestBlocks H) B D.P) :
    Compatible (tr.HonestBlocks H) (Node.frame (tr.state y m)).fcRoot B ∧
      (B ∈ (Node.frame (tr.state y m)).tree →
        (Node.frame (tr.state y m)).Anc B
            (SA.getAnchor sp (tr.state y m).ac (Node.frame (tr.state y m)) t) ∨
          B ∈ (Node.frame (tr.state y m)).viableTree (Node.frame (tr.state y m)).tree) := by
  exact FamilySafety.reader_frame_instance hinv hy m t hBP

/-- **An honest fast lock block is compatible with `P`, cut-indexed**: a fast update
lock or an optimistic selection of an honest node at cut `c`, whose counted honest votes were
cast at cuts before `n`, from (H)/S5V at the cuts before `n` (`OutageVoteInv D n`) only. -/
theorem fastLock_compatible_at {n : Nat} (hvi : OutageVoteInv D n) {y : Fin sp.n} (hy : y ∈ H)
    {c s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC y c s B CV)
    (hcut : ∀ v ∈ CV, v.val ∈ H → ∃ j < n, ∃ e, SA.VoteAt tr.projAC v.val j e ∧ e.msg = v) :
    Compatible (tr.HonestBlocks H) B D.P := by
  exact FamilySafety.fastLock_compatible_at_instance hvi hy hfl hcut


/-- **Every honest fast lock block is compatible with `P`**: a fast update lock or an
optimistic selection of an honest node. -/
theorem fastLock_compatible (hinv : ∀ i, OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H)
    {c s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC y c s B CV) : Compatible (tr.HonestBlocks H) B D.P :=
  fastLock_compatible_at (hinv (c + 1)).toOutageVoteInv hy hfl fun _ hv hvH =>
    let ⟨j', hj', e, hve, he⟩ := fastLock_honest_vote D.hrun D.hnc hy hfl hv hvH
    ⟨j', Nat.lt_succ_of_le hj', e, hve, he⟩

/-- **(i) at a read point, cut-indexed** (live-lock compatibility inside the cut induction):
at an honest vote of a slot `> 0` cast at cut `i`, the live lock blocks of the read point are
compatible with every block `B ⪯ P`, from the invariant at the cast cut `i` only. The stored locks
are the `locks` field at `i`; the read point's optimistic lock is written by the receipt's check
before the call's own vote, so its counted honest votes were cast at cuts before `i`
(`SA.readPoint_locks_provenance_strict`) and (H)/S5V at the cuts before `i` (`OutageVoteInv`) decide
it. -/
theorem readPoint_liveLockBlocks_compatible_at {i : Nat} (hinv : OutageLockInv D i)
    {y : Fin sp.n} (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hpos : 0 < sp.slot (tr.time i)) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBP : Anc (tr.HonestBlocks H) B D.P) :
    ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocks H) L B := by
  exact FamilySafety.readPoint_liveLockBlocks_compatible_at_instance hinv hy hc hpos hBP

end Consensus.Goldilocks.Compose

end
