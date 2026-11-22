module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeBlockView

public section

/-! # Block calls of the canonical trace in the engine views, given the tick releases

The engine-event analysis shared by the constant-fault rows of `Simulation/{Evidence,Transport}`
and the growing-fault rows of `Growing/Simulation/{Endpoint/Outputs,NoColl}`. A block call of the
canonical trace comes from a public engine tick, which emits it, or from a delivery, which carries
its canonical object. The premise `hrel` supplies the releases of a public tick; each fault model
supplies it from its own release analysis:

* `block_call_in_view_of_releases`: every called block, accepted or refused, has a parent and its
  canonical object is in the view of the engine node of its event, right after the event;
* `accepted_in_view_of_releases`: an accepted block is in its reader's view at every later mapped
  cut;
* `noCollRun_of_observed`: collision freedom of the canonical trace once every occurring block
  has a parent and an observed header. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **Every called block, accepted or refused, is in the view of its engine node** right after
the engine event of the call, and has a parent. `hrel`: every block a public tick calls at a
positive position is released at that event. -/
theorem block_call_in_view_of_releases (hrel : ∀ {j : Nat} {v : V} {t : Time},
      rho.events[j]? = some (.tick v t) → (S.params (pubOf E) hn).toParams.IsPublic t →
      ∀ r ∈ eventCuts S rho hn j, ∀ B acc, r.label = .fg (.block B acc) → r.pos ≠ 0 →
        blockObj (S.params (pubOf E) hn) B ∈ rho.releasesAt j)
    {B : Blk (S.params (pubOf E) hn)} (hB : (simTrace S rho hn).Occurs B) :
    B.parent ≠ none ∧ ∃ i ev, rho.events[i]? = some ev ∧
      blockObj (S.params (pubOf E) hn) B ∈ rho.ViewIdx ev.node (i + 1) := by
  obtain ⟨hobj, hcodec⟩ := blockView_encoding (E := E) S hn
  rw [(simTrace_encoding S rho hn).1] at hB
  have h := NodeAsChainShape.CanonicalTrace.block_call_in_view_of_releases
    (traceEncoding S hn) rho hcodec (fun he hp r hr b acc hl hpos => by
      obtain ⟨q, hq, hqp, hql⟩ := eventCuts_label_pos S rho hn _ r hr
      rw [hobj]
      exact hrel he hp q hq b acc (hql.trans hl) (hqp ▸ hpos)) hB
  obtain ⟨hp, i, ev, he, hh⟩ := h
  rw [hobj] at hh
  exact ⟨hp, i, ev, he, hh⟩

/-- **An accepted block is in its reader's engine view at every later mapped cut.** `hrel`:
every block a public tick of the reader calls at a positive position is released at that
event. -/
theorem accepted_in_view_of_releases (hv : rho.ExecutionValid) {v : V}
    (hrel : ∀ {j : Nat} {t : Time}, rho.events[j]? = some (.tick v t) →
      (S.params (pubOf E) hn).toParams.IsPublic t →
      ∀ r ∈ eventCuts S rho hn j, ∀ B acc, r.label = .fg (.block B acc) → r.pos ≠ 0 →
        blockObj (S.params (pubOf E) hn) B ∈ rho.releasesAt j)
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
    exact rho.mem_viewIdx_iff.2 ⟨j, _, hji,
      Or.inl ⟨t, Or.inl he, hrel he hp r hmem B true hrl hr0⟩, .refl _⟩
  | deliver w o t =>
    change w = v at hkey
    subst w
    rw [eventCuts_deliver S rho hn j v o t he] at hmem
    have hnow := (now_eq_lastClock S rho hn hv v j).trans (lastClock_deliver S rho hv he)
    have hq := ((process_relay (runProposer S rho hn)
      (digestOf S rho) (Model.digests rho.hash o) t j
      (delivered (Model.digests rho.hash o) (stateAt S rho hn v j) o)
        (stateAt S rho hn v j) 0 hnow).2.2.2 r
      (by rw [self_eq_ownKey]; exact hmem)).1 B hrl
    obtain ⟨cs, hx, hrel⟩ := deliver_relays S rho hn he hq
    exact rho.mem_viewIdx_iff.2 ⟨j, _, hji, Or.inl ⟨t, Or.inr ⟨o, he⟩, hrel⟩,
      .step hx (.refl _)⟩
  | restart w t =>
    exfalso
    rw [eventCuts_restart S rho hn j w t he] at hmem
    obtain ⟨kk, hk, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨_, _, _, _, hlabk⟩ := getElem_groupRecs _ _ _ _ _ _ _ kk hk
    have hcut := List.getElem_mem (lt_of_lt_of_eq hk (length_groupRecs _ _ _ _ _ _ _))
    rw [← hlabk, hrl] at hcut
    simp [exec, Node.restart, acCall] at hcut

/-- **Collision freedom of the canonical trace from observed headers.** If every occurring block
has a parent and an observed header (`hocc`), the absence of observed engine hash collisions
makes equal digests of occurring blocks or genesis have equal fields. -/
theorem noCollRun_of_observed (hnc : ¬ rho.HashCollision)
    (hocc : ∀ B : Blk (S.params (pubOf E) hn), (simTrace S rho hn).Occurs B →
      B.parent ≠ none ∧ rho.ObservedItem (headerOf (S.params (pubOf E) hn) B)) :
    Compose.NoCollRun (digestOf S rho) (simTrace S rho hn) := by
  rw [digestOf_eq]
  refine traceEncoding_induction (E := E) S hn (fun _ _ =>
    Compose.NoCollRun (dgOf rho.hash S.genesisRoot) (simTrace S rho hn)) ?_
  intro e hd
  rw [← hd rho]
  refine NodeAsChainShape.CanonicalTrace.noCollRun_of_observed e rho _ hnc ?_ hocc
  rintro ⟨a, p⟩ ⟨b, q⟩ he
  change encodeInfo a p = encodeInfo b q at he
  have h := congrArg (decodeInfo (Fintype.card V)) he
  simpa only [decodeInfo_encodeInfo, Option.some.injEq] using h

end Consensus.Goldilocks.Simulation

end
