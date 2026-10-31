module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Outputs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Simulation

public section

/-! # Held blocks and their evidence belong to the engine reader's view

Track the accepting node cut back to its engine event, retaining the event index. A release
at the same time without that index would not suffice for an event-cut read. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- An accepted block is in its reader's engine view at every subsequent mapped cut. -/
theorem accepted_in_view (hv : rho.ExecutionValid) {v : V} (hv' : v ∈ rho.honest)
    {k i : Nat} {B : Blk (S.params (pubOf E) hn)}
    (hacc : (simTrace S rho hn).AcceptAt (rho.ownKey v) k B)
    (hki : k < cutMap S rho hn i) :
    blockObj (S.params (pubOf E) hn) B ∈ rho.ViewIdx v i := by
  obtain ⟨hnode, hlab⟩ := hacc
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, j, ev, _, he, hjk, _, hidx, hn', _, _, hlab'⟩ := simTrace_cut S rho hn hl
  have hji : j < i := by
    by_contra h
    have := cutMap_mono S rho hn (not_lt.1 h)
    omega
  have hrl : r.label = .fg (.block B true) := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  have hkey : ev.node = v := rho.key.symm.injective (hn'.symm.trans hnode)
  have hrun := simTrace_goldilocksRun S rho hn hv
  cases ev with
  | tick w t =>
    change w = v at hkey
    subst w
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn j v t he hp] at hmem
      simp at hmem
    have hr0 : r.pos ≠ 0 := by
      intro hr0
      obtain ⟨_, _, _, h⟩ := eq_deliver_of_cut S rho hn he hmem (Or.inl ⟨hr0, _, hrl⟩)
      cases h
    have hnf := Regimes.non_framing _ _ _ _ _ hrun _ (honest_ownKey (S := S) hv')
    have hrel := (tick_releases S rho hn hv hv' he hp hnf r hmem).1 B true hrl hr0
    exact rho.mem_viewIdx_iff.2 ⟨j, _, hji, Or.inl ⟨t, Or.inl he, hrel⟩, .refl _⟩
  | deliver w o t =>
    change w = v at hkey
    subst w
    rw [eventCuts_deliver S rho hn j v o t he] at hmem
    have hnow := (now_eq_lastClock S rho hn hv v j).trans (lastClock_deliver S rho hv he)
    have hq := ((process_relay (digestOf S rho) (Model.digests rho.hash o) t j
      (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v j) 0 hnow).2.2.2 r
      (by rw [stateAt_self]; exact hmem)).1 B hrl
    obtain ⟨cs, hx, hrel⟩ := deliver_relays S rho hn he hq
    exact rho.mem_viewIdx_iff.2 ⟨j, _, hji, Or.inl ⟨t, Or.inr ⟨o, he⟩, hrel⟩,
      .step hx (.refl _)⟩
  | restart w t =>
    exfalso
    rw [eventCuts_restart S rho hn j w t he] at hmem
    obtain ⟨kk, hk, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨_, _, _, _, hlabk⟩ := getElem_groupRecs _ _ _ _ _ _ kk hk
    have hcut := List.getElem_mem (lt_of_lt_of_eq hk (length_groupRecs _ _ _ _ _ _))
    rw [← hlabk, hrl] at hcut
    simp [exec, Node.restart, acCall] at hcut

/-- CLAIMS R.8/F.2 and Refinement G1.5: every held non-genesis block was accepted earlier;
`accepted_in_view` retains the engine event index needed to put it in this reader's view.

Paper argument (implementation bridge, not a quotation): apply `tree_cases` at node cut
`cutMap i`. Its genesis alternative contradicts `hg`; otherwise it gives acceptance at some
`k < cutMap i`. Apply `accepted_in_view` with that strict inequality. That theorem locates an
engine event `j` with `cutMap j ≤ k`; monotonicity forces `j < i`, so even simultaneous events
cannot move evidence past the read. No collision or awake-at-read assumption is needed.
Status: argument complete relative to the existing simulation/acceptance lemmas; Lean open. -/
theorem held_in_view (hv : rho.ExecutionValid) {v : V} (hv' : v ∈ rho.honest)
    {i : Nat} {B : Blk (S.params (pubOf E) hn)}
    (hB : B ∈ ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)).fg.tree)
    (hg : B.root ≠ (S.params (pubOf E) hn).genesisRoot) :
    blockObj (S.params (pubOf E) hn) B ∈ rho.ViewIdx v i := by
  sorry

/-- CLAIMS G1.5 evidence binding: canonical block objects carry their payload attestations,
and views are closed under carried objects. Genesis has no attestations. This applies to ANY
held block, as required by R.7's two witness chains, not just finalized ancestors.

Paper argument: reachable-store coherence identifies any held block with genesis root as
genesis itself, whose FG payload is empty. Membership of `a` excludes that case. By
`held_in_view`, `blockObj B` is in the view. Its carried list is `payloadObjs B.fgPayload
B.acPayload`, which includes `attObj a` by list-map membership. Compose this direct containment
with the view's witnessing containment (`mem_viewIdx_iff`); views are transitively closed
under carried objects. This uses every held block, not the false restriction that R.7's
witness chains end at the finalized tips. Status: argument complete; Lean open. -/
theorem held_att_in_view (hv : rho.ExecutionValid) {v : V} (hv' : v ∈ rho.honest)
    {i : Nat} {B : Blk (S.params (pubOf E) hn)}
    (hB : B ∈ ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)).fg.tree)
    {a : FG.Att (Fintype.card V)} (ha : a ∈ B.fgPayload) : attObj a ∈ rho.ViewIdx v i := by
  sorry

variable (V) in
/-- CLAIMS Refinement G1.5 (b): `mem_chainTo` places each read header in the held tree;
encoding round-trip identifies its attestations, then `held_att_in_view` binds the evidence.

Paper argument: the quantified reader supplies `n ≥ 1`; use `simTrace_simulates` and
`read_finalized`. Its tip is held by the reachable-store cache invariant. `mem_chainTo` makes
the read header `headerOf B` for a held block B. `decodeInfo_encodeInfo` and injectivity of
`some` identify the decoded list `atts` with `B.fgPayload`; apply `held_att_in_view` to `a`.
If V is empty there is no reader, so no simulation with `n ≥ 1` is required. The bound
`i ≤ events.length` is exactly the domain of simulation's state agreement.
Status: argument complete relative to simulation; Lean open. -/
theorem evidenceInView : EvidenceInView V S := by
  sorry

end Consensus.Goldilocks.Refinement

end
