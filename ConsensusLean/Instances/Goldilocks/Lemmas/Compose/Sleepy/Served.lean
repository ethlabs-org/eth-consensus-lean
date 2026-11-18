module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.ServedBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.ServedSteps
import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Steps
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FastExpiry
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.RecordWrites
import ConsensusLean.Lemmas.Tactic.Linarith
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Service

public section

/-! # Goldilocks under `Sleepy`: the anchor at the served head (S4)

`anchor_compatible_of_live_candidates`: after GST, the anchor of the actual record's head (the
deepest of the live lock blocks and `fc_root`) is compatible with the record, from the current
view's votes and participation only; the record's recency and the anchor's compatibility with the
older history are supplied separately, and the live-lock arm needs no majority or service before
GST.

The chain-generic steps are in `Compose/Sleepy/ServedSteps`, imported privately, which the
growing-fault forms share; the facts on the latest view's votes are in `Compose/Sleepy/ServedBase`,
imported publicly. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- Post-GST head support for the actual record. Only the current view's votes and
participation are needed; historical record recency and anchor compatibility are supplied
separately. The live-lock arm requires no majority or service before GST. -/
theorem anchor_compatible_of_live_candidates
    {A : SA.SAState sp.n} {Φ : SA.Frm sp.n (List (FG.Att sp.n))} (hΦ : FrameOK Φ)
    {t : Time} {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hcomp : ∀ X ∈ SA.liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}, Compatible Φ.tree X R) :
    Compatible Φ.tree (SA.getAnchor sp A Φ t) R := by
  have hsub : SA.liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot} ⊆ Φ.tree := by
    rintro X (hX | hX)
    · exact hX.1
    · exact (Set.mem_singleton_iff.mp hX) ▸ hΦ.fcRoot_mem
  obtain ⟨D, hD⟩ := SA.exists_deepest hΦ hsub ⟨Φ.fcRoot, Or.inr rfl⟩
  have ha : SA.getAnchor sp A Φ t = D := by simp only [SA.getAnchor, hD, Option.getD_some]
  rw [ha]
  exact hcomp D (SA.deepest_mem hD).1

end Consensus.Goldilocks.Compose

end
