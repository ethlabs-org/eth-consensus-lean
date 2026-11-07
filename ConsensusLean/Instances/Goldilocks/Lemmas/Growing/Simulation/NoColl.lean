module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.PublishedBlocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Evidence

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

/-- An occurring block is observed while its engine reader is still honest, even if the
reader is compromised later. Refused deliveries count as observations too. -/
theorem occurring_observed_at (hv : rho.ExecutionValid)
    {B : Blk (S.params (pubOf E) hn)} (hB : (simTraceAt S rho hn).Occurs B) :
    B.parent ≠ none ∧ rho.ObservedItem (headerOf (S.params (pubOf E) hn) B) := by
  rw [simTraceAt_eq] at hB
  obtain ⟨y, k, acc, hnode, hlab⟩ := hB
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, -, he, -, -, hidx, -, -, -, hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .fg (.block B acc) := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  have hhon := hv.honest_only ev (List.mem_of_getElem? he)
  have hobs (hp : B.parent ≠ none)
      (hb : blockObj (S.params (pubOf E) hn) B ∈ rho.ViewIdx ev.node (i + 1)) :
      B.parent ≠ none ∧ rho.ObservedItem (headerOf (S.params (pubOf E) hn) B) := by
    refine ⟨hp, blockObj _ B, ⟨ev.node, i + 1, by omega, ?_, hb⟩, rfl⟩
    change ev.node ∉ rho.faultyAt (rho.cutTime (i + 1))
    simpa only [Model.Run.cutTime, he, Option.elim_some] using hhon
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
    have hrel := (tick_block_vote_releases_at S rho hn hv he hp r hmem).1 B acc hrl hr0
    apply hobs
    · rw [eventCuts_tick_public S rho hn i v t he hp] at hmem
      obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hmem
      obtain ⟨-, -, -, -, hl⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
      apply tick_block_parent
      rw [← hrl, hl]
      exact List.getElem_mem _
    · exact rho.mem_viewIdx_iff.mpr ⟨i, _, by omega,
        Or.inl ⟨t, Or.inl he, hrel⟩, .refl _⟩
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
    exact hobs (decodeBlock_wire (decodeBlock_of_canonEvent hce)).2.1
      (rho.mem_viewIdx_iff.mpr ⟨i, o, by omega, Or.inr ⟨t, he⟩, contains_of_mem_delivered ho⟩)
  | restart v t =>
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨kk, hk, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨-, -, -, -, hlk⟩ := getElem_groupRecs _ _ _ _ _ _ _ kk hk
    have hcut := List.getElem_mem (lt_of_lt_of_eq hk (length_groupRecs _ _ _ _ _ _ _))
    rw [← hlk, hrl] at hcut
    simp [exec, Node.restart, acCall] at hcut

/-- Absence of observed engine hash collisions gives collision freedom for every canonical
block call, without a constant-fault premise. -/
theorem noCollRun_simTraceAt (hv : rho.ExecutionValid) (hc : ¬ rho.HashCollision) :
    Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn) := by
  intro B hB C hC heq
  simp only [digestOf_eq] at heq
  simp only [dgOf_eq (n := Fintype.card V) rho.hash S.genesisRoot] at heq
  rcases hB with rfl | hB <;> rcases hC with rfl | hC
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hp, -⟩ := occurring_observed_at S rho hn hv hC
    cases hcp : C.parent with
    | none => exact False.elim (hp hcp)
    | some p =>
      exact False.elim (taggedRoot_ne _ _
        (by simpa [hcp, Params.genesisBlock] using heq.symm))
  · obtain ⟨hp, -⟩ := occurring_observed_at S rho hn hv hB
    cases hb : B.parent with
    | none => exact False.elim (hp hb)
    | some p =>
      exact False.elim (taggedRoot_ne _ _
        (by simpa [hb, Params.genesisBlock] using heq))
  · obtain ⟨hpB, hoB⟩ := occurring_observed_at S rho hn hv hB
    obtain ⟨hpC, hoC⟩ := occurring_observed_at S rho hn hv hC
    obtain ⟨pb, hpb⟩ := Option.ne_none_iff_exists'.mp hpB
    obtain ⟨pc, hpc⟩ := Option.ne_none_iff_exists'.mp hpC
    have hh : rho.hash (headerOf (S.params (pubOf E) hn) B) =
        rho.hash (headerOf (S.params (pubOf E) hn) C) := by
      have h := congrArg (rawRoot S.genesisRoot) heq
      simpa [hpb, hpc, headerOf, rawRoot_taggedRoot] using h
    have he : headerOf (S.params (pubOf E) hn) B = headerOf (S.params (pubOf E) hn) C := by
      by_contra h
      exact hc ⟨_, _, h, hoB, hoC, hh⟩
    have hpar := congrArg (fun h => parentRoot S.genesisRoot h.parent) he
    have hslot := congrArg Header.pos he
    have hin := congrArg Header.input he
    have hinfo := congrArg (fun h => decodeInfo (Fintype.card V) h.info) he
    simp only [headerOf, hpb, hpc, parentRoot_parentRef] at hpar
    simp only [headerOf, decodeInfo_encodeInfo, Option.some.injEq, Prod.mk.injEq] at hinfo
    exact ⟨by simpa [hpb, hpc] using hpar, hslot, hin, hinfo.1, hinfo.2⟩

end Consensus.Goldilocks.Simulation
