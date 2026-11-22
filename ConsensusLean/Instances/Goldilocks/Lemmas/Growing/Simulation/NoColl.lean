module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.PublishedBlocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.BlockView
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeBlockView

public section

/-! # Collision freedom of the canonical trace under growing faults

Every block call, including a refused delivery, exposes its canonical object at the
corresponding engine event. The reader is honest at that event's cut; it need not remain
honest at the final cut. Tagged genesis and injectivity of observed headers then suffice.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

open NodeAsChainShape.CanonicalTrace in
/-- Goldilocks releases the canonical object at every own block cut of a public tick. -/
theorem tick_block_release_encoding (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {t : Time} (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t)
    {r} (hr : r ∈ NodeAsChainShape.CanonicalTrace.eventCuts (traceEncoding S hn) rho i)
    {b acc} (hl : r.label = .fg (.block b acc)) (hpos : r.pos ≠ 0) :
    let e := traceEncoding (E := E) S hn
    engineObj e (NodeAsChainShape.blockObj e.codec.encode e.codec.carried b) ∈
      rho.releasesAt i := by
  dsimp only
  obtain ⟨q, hq, hqp, hql⟩ := eventCuts_label_pos S rho hn i r hr
  rw [(blockView_encoding (E := E) S hn).1 b]
  exact (tick_block_vote_releases_at S rho hn hv he hp q hq).1 b acc
    (hql.trans hl) (hqp ▸ hpos)

/-- An occurring block's object is observed while its engine reader is still honest, even if
the reader is compromised later. Refused deliveries count as observations too. -/
theorem occurs_blockObj_observed_at (hv : rho.ExecutionValid)
    {B : Blk (S.params (pubOf E) hn)} (hB : (simTraceAt S rho hn).Occurs B) :
    B.parent ≠ none ∧ blockObj (binding := S.vote) _ B ∈ rho.Observed := by
  obtain ⟨hobj, hcodec⟩ := blockView_encoding (E := E) S hn
  rw [simTraceAt_eq, (simTrace_encoding S rho hn).1,
    ← NodeAsChainShape.CanonicalTrace.simTraceAt_eq] at hB
  obtain ⟨hp, hobs⟩ := NodeAsChainShape.CanonicalTrace.occurs_blockObj_observed_at
    (traceEncoding S hn) rho hv hcodec
    (fun he hp _ hr _ _ hl hpos => tick_block_release_encoding S rho hn hv he hp hr hl hpos) hB
  exact ⟨hp, hobj B ▸ hobs⟩

/-- An occurring block is observed while its engine reader is still honest. -/
theorem occurring_observed_at (hv : rho.ExecutionValid)
    {B : Blk (S.params (pubOf E) hn)} (hB : (simTraceAt S rho hn).Occurs B) :
    B.parent ≠ none ∧ rho.ObservedItem (headerOf (S.params (pubOf E) hn) B) :=
  have h := occurs_blockObj_observed_at S rho hn hv hB
  ⟨h.1, blockObj _ B, h.2, rfl⟩

/-- Absence of observed engine hash collisions gives collision freedom for every canonical
block call, without a constant-fault premise. -/
theorem noCollRun_simTraceAt (hv : rho.ExecutionValid) (hc : ¬ rho.HashCollision) :
    Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn) := by
  rw [simTraceAt_eq]
  exact noCollRun_of_observed S rho hn hc fun B hB =>
    occurring_observed_at S rho hn hv (by rwa [simTraceAt_eq])

end Consensus.Goldilocks.Simulation
