module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outputs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.BlockView
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Held blocks and their evidence belong to the engine reader's view

Track the accepting node cut back to its engine event, retaining the event index. A release
at the same time without that index would not suffice for an event-cut read. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)

variable {binding : VoteBinding}

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- Under constant faults every block a public tick of an honest node calls at a positive
position is released at that event. -/
private theorem tick_block_releases {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {v : V} (hv' : v ∉ rho.faultyAt 0) {j : Nat} {t : Time}
    (he : rho.events[j]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) :
    ∀ r ∈ eventCuts S rho hn j, ∀ B acc, r.label = .fg (.block B acc) → r.pos ≠ 0 →
      blockObj (S.params (pubOf E) hn) B ∈ rho.releasesAt j := by
  have hnf := Regimes.non_framing _ _ _ _ _ _ (simTrace_goldilocksRun S rho hn hf hv)
    _ (honest_ownKey (S := S) hv')
  exact fun r hr => (tick_releases S rho hn hf hv hv' he hp hnf r hr).1

/-- Every called block, accepted or refused, has its canonical object in the final view
of the honest engine node responsible for the call. -/
theorem occurring_in_view {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {B : Blk (S.params (pubOf E) hn)}
    (hB : (simTrace S rho hn).Occurs B) :
    B.parent ≠ none ∧ ∃ v, v ∉ rho.faultyAt 0 ∧ blockObj (S.params (pubOf E) hn) B ∈
      rho.ViewIdx v rho.events.length := by
  have hhon {i : Nat} {ev} (he : rho.events[i]? = some ev) : ev.node ∉ rho.faultyAt 0 :=
    (rho.point.honestAt_iff_zero hf ev.node ev.time).mp
      (hv.honest_only ev (List.mem_of_getElem? he))
  obtain ⟨hp, i, ev, he, hb⟩ := block_call_in_view_of_releases S rho hn
    (fun he => tick_block_releases S rho hn hf hv (hhon he) he) hB
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  exact ⟨hp, ev.node, hhon he, rho.viewIdx_mono (by omega) _ hb⟩

/-- An accepted block is in its reader's engine view at every subsequent mapped cut. -/
theorem accepted_in_view {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {v : V} (hv' : v ∉ rho.faultyAt 0)
    {k i : Nat} {B : Blk (S.params (pubOf E) hn)}
    (hacc : (simTrace S rho hn).AcceptAt (rho.ownKey v) k B)
    (hki : k < cutMap S rho hn i) :
    blockObj (S.params (pubOf E) hn) B ∈ rho.ViewIdx v i :=
  accepted_in_view_of_releases S rho hn hv (tick_block_releases S rho hn hf hv hv') hacc hki

/-- CLAIMS R.8/F.2 and Refinement G1.5: every held non-genesis block was accepted earlier;
`accepted_in_view` retains the engine event index needed to put it in this reader's view.

Paper argument (implementation bridge, not a quotation): apply `tree_cases` at node cut
`cutMap i`. Its genesis alternative contradicts `hg`; otherwise it gives acceptance at some
`k < cutMap i`. Apply `accepted_in_view` with that strict inequality. That theorem locates an
engine event `j` with `cutMap j ≤ k`; monotonicity forces `j < i`, so even simultaneous events
cannot move evidence past the read. No collision or awake-at-read assumption is needed.
Status: proved relative to the existing simulation/acceptance lemmas. -/
theorem held_in_view {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {v : V} (hv' : v ∉ rho.faultyAt 0)
    {i : Nat} {B : Blk (S.params (pubOf E) hn)}
    (hB : B ∈ ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)).fg.tree)
    (hg : B.root ≠ (S.params (pubOf E) hn).genesisRoot) :
    blockObj (S.params (pubOf E) hn) B ∈ rho.ViewIdx v i := by
  rcases Compose.tree_cases (simTrace_goldilocksRun S rho hn hf hv).toLocalRun
      (honest_ownKey (S := S) hv') hB with hgen | ⟨k, hk, hacc⟩
  · exact (hg (congrArg Block.root hgen)).elim
  · exact accepted_in_view S rho hn hf hv hv' hacc hk

/-- CLAIMS G1.5 evidence binding: canonical block objects carry their payload attestations,
and views are closed under carried objects. Genesis has no attestations. This applies to ANY
held block, as required by R.7's two witness chains, not just finalized ancestors.

Paper argument: reachable-store coherence identifies any held block with genesis root as
genesis itself, whose FG payload is empty. Membership of `a` excludes that case. By
`held_in_view`, `blockObj B` is in the view. Its carried list is `payloadObjs B.fgPayload
B.acPayload`, which includes `attObj a` by list-map membership. Compose this direct containment
with the view's witnessing containment (`mem_viewIdx_iff`); views are transitively closed
under carried objects. This uses every held block, not the false restriction that R.7's
witness chains end at the finalized tips. The proof uses the acceptance alternative directly;
the genesis alternative has no attestations. Status: proved. -/
theorem held_att_in_view {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {v : V} (hv' : v ∉ rho.faultyAt 0)
    {i : Nat} {B : Blk (S.params (pubOf E) hn)}
    (hB : B ∈ ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)).fg.tree)
    {a : FG.Att (Fintype.card V)} (ha : a ∈ B.fgPayload) : attObj a ∈ rho.ViewIdx v i := by
  rcases Compose.tree_cases (simTrace_goldilocksRun S rho hn hf hv).toLocalRun
      (honest_ownKey (S := S) hv') hB with hgen | ⟨k, hk, hacc⟩
  · subst B
    simp [Params.genesisBlock] at ha
  · have hb := accepted_in_view S rho hn hf hv hv' hacc hk
    obtain ⟨j, o, hj, ho, hc⟩ := rho.mem_viewIdx_iff.mp hb
    refine rho.mem_viewIdx_iff.mpr ⟨j, o, hj, ho, hc.trans (.step ?_ (.refl _))⟩
    change attObj a ∈ payloadObjs B.fgPayload B.acPayload
    exact List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩)

/-- CLAIMS Refinement G1.5 (b): `mem_chainTo` places each read header in the held tree;
encoding round-trip identifies its attestations, then `held_att_in_view` binds the evidence.

Paper argument: the quantified reader supplies `n ≥ 1`; use `simTrace_simulates` and
`read_finalized`. Its tip is held by the reachable-store cache invariant. `mem_chainTo` makes
the read header `headerOf B` for a held block B. `decodeInfo_encodeInfo` and injectivity of
`some` identify the decoded list `atts` with `B.fgPayload`; apply `held_att_in_view` to `a`.
If V is empty there is no reader, so no simulation with `n ≥ 1` is required. The bound
`i ≤ events.length` is exactly the domain of simulation's state agreement.
Status: proved relative to simulation. -/
theorem evidenceInView (V : Type) [Fintype V] [DecidableEq V] (S : Setup)
    : EvidenceInView V S := by
  rw [evidenceInView_iff]
  intro E rho hf hv v hv' i hi h hh atts p hd a ha
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hs := simTrace_simulates S rho hn hf hv
  have hr := Compose.fg_reachable hs.run.toLocalRun (honest_ownKey (S := S) hv')
    (cutMap S rho hn i)
  rw [read_finalized hs hv' hi] at hh
  obtain ⟨B, hB, _, _, rfl⟩ := mem_chainTo hr (Store.cache_invariants _ _ _ _ hr).1 hh
  have hd' : (B.fgPayload, B.acPayload) = (atts, p) := by
    simpa only [headerOf, decodeInfo_encodeInfo, Option.some.injEq] using hd
  have he : B.fgPayload = atts := congrArg Prod.fst hd'
  exact held_att_in_view S rho hn hf hv hv' hB (by rw [he]; exact ha)

end Consensus.Goldilocks.Simulation

end
