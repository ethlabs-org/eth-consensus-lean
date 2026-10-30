module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run

public section

/-! # Goldilocks under `Sleepy`: where records, locks, sources, rows and caches come from

The provenance part of S1 (workbench#11 §1, §4 "The event induction"), which needs no
comparability: it holds of every Goldilocks run, by the handlers alone.

* The record `latest_confirmed` is written only by `update_latest_confirmed`, with the result of a
  non-vetoed update or an optimistic selection; restarts keep it. So it names genesis or an
  origin, a block of the node's tree (`record_origin`).
* Every stored lock sits below an origin of its own slot (`lock_origin`): the update of slot `s`
  locks blocks on its result's path, an optimistic check locks its selection, and the lock
  functions only move locks back (`SA.lock_provenance`).
* Every FG source is a live fast lock block, so on the chain (`source_on_chain`); every honest
  attestation names the entry of its source's state, an ancestor of the source
  (`row_on_chain`); every `Σ.F` and `Σ.J` is genesis or an entry with a target quorum, which has
  an honest row since `q > f` (`caches_on_chain`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro}

/-- **The record names genesis or an origin**, a block of the node's tree. -/
theorem record_origin (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    ∃ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y i).ac.latestConfirmed ∧
      (C.root = sp.genesisRoot ∨ ∃ s, Origin tr H C s) := by
  sorry

/-- **Every stored lock sits below an origin of its slot** whose event precedes the cut, and names
a block of the node's tree. -/
theorem lock_origin (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state y i).ac.locks, ∃ L ∈ (tr.state y i).fg.tree, L.root = l.block ∧
      ∃ C, OriginBefore tr H C l.slot i ∧ Anc (tr.HonestBlocks H) L C := by
  sorry

/-- **Every FG source is on the origin chain**: it is the block of a live fast lock. -/
theorem source_on_chain (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (h : SA.ToFGAt tr.projAC y i ℓ C) :
    OnOriginChain tr H C := by
  sorry

/-- **Every honest row names a block on the origin chain**: an honest attestation's height pair
names the entry of its source's state, an ancestor of the source. -/
theorem row_on_chain (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr) {x : Fin sp.n}
    (hx : x ∈ H) {k : Nat} {a : FG.Att sp.n} (h : tr.SignAt x k a) :
    ∃ E ∈ tr.HonestBlocks H, E.root = a.T ∧ OnOriginChain tr H E := by
  sorry

/-- **Every honest `Σ.F` and `Σ.J` is on the origin chain**, under `Sleepy` (`f < n/2 < q`: a
target quorum has an honest row). -/
theorem caches_on_chain (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr) {ΔF : Time}
    (hsl : tr.SleepyRun H ΔF) {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    OnOriginChain tr H (tr.state y i).fg.F ∧ OnOriginChain tr H (tr.state y i).fg.J := by
  sorry

end Consensus.Goldilocks.Compose

end
