module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outputs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core

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

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- A block an engine tick calls has a parent. -/
private theorem tick_block_parent {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (self : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat)
    {B : Blk sp} {acc : Bool}
    (hc : Cut.fg (.block B acc) ∈ (exec proposer dg self st t (.tick x)).2) :
    B.parent ≠ none := by
  rw [show (exec proposer dg self st t (.tick x)).2 = (onTick proposer dg self st t x).2
    from rfl, onTick_cuts] at hc
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · simp [tickStep, acCall] at hc
    · simp only [tickStep] at hc
      split_ifs at hc
      · split at hc
        · simp [acProposal] at hc
        · simp only [proposeBlock, onBlock] at hc
          split_ifs at hc
          · simp [acProposal] at hc
          · split at hc <;> simp [acCall, acProposal] at hc <;>
              obtain ⟨rfl, _⟩ := hc <;> simp [mkBlock]
      · simp at hc
  · simp only [tickStep] at hc
    split at hc
    · simp [acToFG] at hc
    · simp only [attest, List.mem_cons, acToFG, reduceCtorEq, false_or] at hc
      split at hc <;> simp [onAttestation] at hc

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
  obtain ⟨y, k, acc, hnode, hlab⟩ := hB
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, -, he, -, -, hidx, -, -, -, hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .fg (.block B acc) := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  cases ev with
  | tick v t =>
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn i v t he hp] at hmem
      simp at hmem
    have hr0 : r.pos ≠ 0 := by
      intro hr0
      obtain ⟨w, o, u, h⟩ := eq_deliver_of_cut S rho hn he hmem (Or.inl ⟨hr0, _, hrl⟩)
      cases h
    refine ⟨?_, i, _, he, rho.mem_viewIdx_iff.mpr ⟨i, _, by omega,
      Or.inl ⟨t, Or.inl he, hrel he hp r hmem B acc hrl hr0⟩, .refl _⟩⟩
    rw [eventCuts_tick_public S rho hn i v t he hp] at hmem
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨-, -, -, -, hl⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
    exact tick_block_parent _ _ _ _ _ _ (by rw [← hrl, hl]; exact List.getElem_mem _)
  | deliver v o t =>
    rw [eventCuts_deliver S rho hn i v o t he] at hmem
    obtain ⟨o', e, st', ho, hce, kk, hk, hlk, -⟩ :=
      mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hmem
    have hcut := hlk.symm.trans hrl
    have hzero := pos_of_block_cut _ _ _ _ _ (canonEvent_ne_tick hce) hk hcut
    subst kk
    have heq : e = .block B := by
      cases e with
      | tick x => exact False.elim (canonEvent_ne_tick hce x rfl)
      | block B' =>
        have hm := List.getElem_mem hk
        rw [hcut] at hm
        simp only [exec, onBlock] at hm
        split_ifs at hm
        · simp at hm
        · split at hm <;> simp [acCall] at hm <;> simp_all
      | message m => simp [exec, onMessage, acCall] at hcut
      | attestation a => simp [exec, onAttestation] at hcut
      | restart => simp [exec, Node.restart, acCall] at hcut
    subst e
    have ho' := eq_blockObj_of_decodeBlock (decodeBlock_of_canonEvent hce)
    rw [ho'] at ho
    exact ⟨(decodeBlock_wire (decodeBlock_of_canonEvent hce)).2.1, i, _, he,
      rho.mem_viewIdx_iff.mpr ⟨i, o, by omega, Or.inr ⟨t, he⟩, contains_of_mem_delivered ho⟩⟩
  | restart v t =>
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨kk, hk, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨-, -, -, -, hlk⟩ := getElem_groupRecs _ _ _ _ _ _ _ kk hk
    have hcut := List.getElem_mem (lt_of_lt_of_eq hk (length_groupRecs _ _ _ _ _ _ _))
    rw [← hlk, hrl] at hcut
    simp [exec, Node.restart, acCall] at hcut

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
      (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v j) 0 hnow).2.2.2 r
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
  intro B hB C hC heq
  simp only [digestOf_eq] at heq
  simp only [dgOf_eq (n := Fintype.card V) rho.hash S.genesisRoot] at heq
  rcases hB with rfl | hB <;> rcases hC with rfl | hC
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hp, _⟩ := hocc C hC
    cases hc : C.parent with
    | none => exact False.elim (hp hc)
    | some p =>
      exact False.elim (taggedRoot_ne _ _
        (by simpa [hc, Params.genesisBlock] using heq.symm))
  · obtain ⟨hp, _⟩ := hocc B hB
    cases hb : B.parent with
    | none => exact False.elim (hp hb)
    | some p =>
      exact False.elim (taggedRoot_ne _ _
        (by simpa [hb, Params.genesisBlock] using heq))
  · obtain ⟨hpB, hoB⟩ := hocc B hB
    obtain ⟨hpC, hoC⟩ := hocc C hC
    obtain ⟨pb, hpb⟩ := Option.ne_none_iff_exists'.mp hpB
    obtain ⟨pc, hpc⟩ := Option.ne_none_iff_exists'.mp hpC
    have hh : rho.hash (headerOf (S.params (pubOf E) hn) B) =
        rho.hash (headerOf (S.params (pubOf E) hn) C) := by
      have h := congrArg (rawRoot S.genesisRoot) heq
      simpa [hpb, hpc, headerOf, rawRoot_taggedRoot] using h
    have he : headerOf (S.params (pubOf E) hn) B = headerOf (S.params (pubOf E) hn) C := by
      by_contra h
      exact hnc ⟨_, _, h, hoB, hoC, hh⟩
    have hpar := congrArg (fun h => parentRoot S.genesisRoot h.parent) he
    have hslot := congrArg Header.pos he
    have hin := congrArg Header.input he
    have hinfo := congrArg (fun h => decodeInfo (Fintype.card V) h.info) he
    simp only [headerOf, hpb, hpc, parentRoot_parentRef] at hpar
    simp only [headerOf, decodeInfo_encodeInfo, Option.some.injEq, Prod.mk.injEq] at hinfo
    exact ⟨by simpa [hpb, hpc] using hpar, hslot, hin, hinfo.1, hinfo.2⟩

end Consensus.Goldilocks.Simulation

end
