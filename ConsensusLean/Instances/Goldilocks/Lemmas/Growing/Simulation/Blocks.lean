module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Events
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Release

public section

/-! # Genuine block releases under growing faults

Release analysis needs only the sender's local proposal inventory. It does not replace the
time-indexed honest set by a terminal one.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Payload)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

private theorem tick_block_fields {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (self : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat)
    {B : Blk sp} {acc : Bool} {k : Nat}
    (hk : k < (exec proposer dg self st t (.tick x)).2.length)
    (hc : (exec proposer dg self st t (.tick x)).2[k] = .fg (.block B acc)) :
    B.proposer = self ∧ B.RootOk dg ∧ B.parent ≠ none ∧ k ≠ 0 := by
  have hzero : k ≠ 0 := by
    intro h
    subst k
    simp [exec, onTick, runSteps, tickSteps, tickStep, acCall] at hc
  have hm := List.getElem_mem hk
  rw [hc] at hm
  rw [show (exec proposer dg self st t (.tick x)).2 = (onTick proposer dg self st t x).2
    from rfl, onTick_cuts] at hm
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · simp [tickStep, acCall] at hm
    · simp only [tickStep] at hm
      split_ifs at hm
      · split at hm
        · simp [acProposal] at hm
        · rename_i d p hdp
          simp only [proposeBlock, onBlock] at hm
          split_ifs at hm
          · simp [acProposal] at hm
          · split at hm <;> simp [acCall, acProposal] at hm <;>
              obtain ⟨rfl, _⟩ := hm <;> exact ⟨rfl, rfl, by simp [mkBlock], hzero⟩
      · simp at hm
  · simp only [tickStep] at hm
    split at hm
    · simp [acToFG] at hm
    · simp only [attest, List.mem_cons, acToFG, reduceCtorEq, false_or] at hm
      split at hm <;> simp [onAttestation] at hm

private theorem ownBlock_of_tick_cut {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t)
    {B : Blk (S.params (pubOf E) hn)} {acc : Bool}
    (hc : Cut.fg (.block B acc) ∈ (exec (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node t
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2) :
    ∃ k < cutMap S rho hn (i + 1), (simTrace S rho hn).OwnBlockAt B.proposer k B := by
  obtain ⟨m, hm, hcm⟩ := List.getElem_of_mem hc
  obtain ⟨hself, _, _, hm0⟩ := tick_block_fields _ _ _ _ _ _ hm hcm
  have hEC := eventCuts_tick_public S rho hn i v t he hp
  have hm' : m < (eventCuts S rho hn i).length := by
    rw [hEC, length_groupRecs]; exact hm
  have hr := allCuts_getElem?_add S rho hn i m (List.getElem?_eq_some_iff.mp he).1 hm'
  rw [List.getElem?_eq_getElem hm'] at hr
  have hgr := getElem_groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
    (stateAt S rho hn v i).node t (Nat.pair i 0)
    (.tick (encodeTxs (Model.mempool rho.inbox v t))) m
    (show m < _ from by rw [length_groupRecs]; exact hm)
  have hr' : (allCuts S rho hn)[cutMap S rho hn i + m]? = some
      ((groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t))))[m]'
          (by rw [length_groupRecs]; exact hm)) :=
    by simpa only [hEC] using hr
  refine ⟨cutMap S rho hn i + m, ?_, ⟨acc, ?_, ?_⟩, ?_⟩
  · rw [cutMap_succ]; omega
  · rw [simTrace_node, hr']; exact hgr.1.trans hself.symm
  · rw [simTrace_label, hr']; exact congrArg some (hgr.2.2.2.2.trans hcm)
  · rw [simTrace_pos, hr']; simpa only [Option.elim_some, hgr.2.2.2.1] using hm0

/-- A genuine block release originated in a proposer tick preceding its release cut. -/
theorem released_block_cut_at (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {t : Time} (hs : rho.SendsAt v i t)
    {B : Blk (S.params (pubOf E) hn)} (hpar : B.parent ≠ none)
    (hroot : B.RootOk (digestOf S rho))
    (hb : blockObj (S.params (pubOf E) hn) B ∈ rho.releasesAt i) :
    ∃ k < cutMap S rho hn (i + 1), (simTraceAt S rho hn).OwnBlockAt B.proposer k B := by
  rw [simTraceAt_eq]
  have hhead : ∀ seen ob,
      blockObj (S.params (pubOf E) hn) B ∉ relHead S rho v seen ob := by
    intro seen ob h
    obtain ⟨q, _, heq⟩ := mem_relHead S rho h
    have hh := congrArg Model.Obj.msg heq
    cases hh
  rcases hs with he | ⟨o, he⟩
  · have hv' := event_honest_zero S rho hv he
    by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
    · obtain ⟨N4, N5, Q, R4, F, G, hr, _, _, hF, hG, _, _, hR4, _⟩ :=
        tick_public_analysis S rho hn hv hv' he hp (preNode_releasable_at S rho hn hv he)
      rw [hr] at hb
      have hb4 : blockObj (S.params (pubOf E) hn) B ∈ R4 := by
        rcases List.mem_append.mp hb with hb | hb
        · rcases List.mem_append.mp hb with hb | hb
          · rcases List.mem_append.mp hb with hb | hb
            · rcases List.mem_append.mp hb with hb | hb
              · exact False.elim (hhead _ _ hb)
              · exact hb
            · rcases List.mem_append.mp hb with hb | hb
              · exact False.elim (hhead _ _ hb)
              · rcases hF _ hb with ⟨τ, cs, heq⟩ | ⟨τ, m, heq⟩
                all_goals have hh := congrArg Model.Obj.msg heq; cases hh
          · exact False.elim (hhead _ _ hb)
        · have hh := hG _ hb
          cases hh
      rw [hR4] at hb4
      obtain ⟨C, acc, hc, hb⟩ := mem_blockObjs.mp hb4
      obtain ⟨m, hm, hcm⟩ := List.getElem_of_mem hc
      obtain ⟨_, hrC, hpC, _⟩ := tick_block_fields _ _ _ _ _ _ hm hcm
      have hBC := blockObj_fields S rho hn hpar hpC hroot hrC hb
      subst C
      exact ownBlock_of_tick_cut S rho hn he hp hc
    · rcases tick_other_releases S rho hn hv hv' he hp _ hb with h | h
      · exact False.elim (hhead _ _ h)
      · cases h
  · have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
    simp only [Model.Run.releasesAt, he, Model.Run.deliver] at hb
    rcases List.mem_append.mp hb with hb | hb
    · rw [deliverDuties_eq S t ht] at hb
      erw [Model.Run.runDuties_cons, Model.Run.runDuties_nil] at hb
      simp only [List.append_nil] at hb
      rcases dutyStep_poll_sub S rho hn v _ _ _ hb with
        ⟨b, _, heq⟩ | ⟨τ, cs, heq⟩ | ⟨τ, m, heq⟩
      all_goals have hh := congrArg Model.Obj.msg heq; cases hh
    · have hh := gossip_unsigned S rho _ _ _ _ hb
      cases hh

/-- A proposer honest at delivery cannot have its block forged before that delivery.
After compromise this conclusion is deliberately unavailable. -/
theorem simTraceAt_block_unforgeable (hv : rho.ExecutionValid) :
    ∀ y i B, y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i) →
      (simTraceAt S rho hn).BlockCallAt y i B →
      B.proposer ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i) →
      ∃ j ≤ i, (simTraceAt S rho hn).OwnBlockAt B.proposer j B := by
  rw [simTraceAt_eq]
  rintro y k B _ ⟨acc, hnode, hlab⟩ hhon
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, _, he, hstart, _, hidx, hn', htime, hpos, hlab'⟩ :=
    simTrace_cut S rho hn hl
  have hrl : r.label = .fg (.block B acc) := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  cases ev with
  | tick v t =>
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn i v t he hp] at hmem
      simp at hmem
    rw [eventCuts_tick_public S rho hn i v t he hp] at hmem
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨_, _, _, hp', hc⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
    obtain ⟨hself, _, _, hm0⟩ := tick_block_fields _ _ _ _ _ _
      (by rwa [length_groupRecs] at hm) (hc.symm.trans hrl)
    exact ⟨k, le_rfl, ⟨acc, hn'.trans hself.symm, hlab⟩, by rwa [hpos, hp']⟩
  | deliver v o t =>
    rw [eventCuts_deliver S rho hn i v o t he] at hmem
    obtain ⟨o', e, st', ho, hce, m, hm, hc, _⟩ := mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hmem
    have hcut := hc.symm.trans hrl
    have heq : e = .block B := by
      have hmem := List.getElem_mem hm
      rw [hcut] at hmem
      cases e with
      | tick x => exact False.elim (canonEvent_ne_tick hce x rfl)
      | block B' =>
        simp only [exec, onBlock] at hmem
        split_ifs at hmem
        · simp at hmem
        · split at hmem <;>
            simp only [acCall, List.mem_cons, Cut.fg.injEq, FGLabel.block.injEq, reduceCtorEq,
              List.not_mem_nil, or_self, or_false] at hmem <;>
            simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, not_lt]
      | message => simp [exec, onMessage, acCall] at hmem
      | attestation => simp [exec, onAttestation] at hmem
      | restart => simp [exec, Node.restart, acCall] at hmem
    subst e
    obtain rfl := eq_blockObj_of_decodeBlock (decodeBlock_of_canonEvent hce)
    obtain ⟨hroot, hpar, _⟩ := decodeBlock_wire (decodeBlock_of_canonEvent hce)
    have hh : rootOf (Model.digests rho.hash o) (headerOf _ B) =
        some (rho.hash (headerOf _ B)) := by
      apply rootOf_digests_of_mem
      exact List.mem_filterMap.mpr ⟨blockObj _ B, mem_delivered ho, rfl⟩
    rw [hh, Option.map_some, Option.some.injEq] at hroot
    have hroot' : B.RootOk (digestOf S rho) := by
      obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp hpar
      rw [digestOf_eq]
      change B.root = dgOf rho.hash S.genesisRoot B.parent B.slot B.input B.fgPayload B.acPayload
      erw [dgOf_eq, ← hroot]
      simp only [headerOf, hp]
    have hsign : rho.signerOf (blockObj (S.params (pubOf E) hn) B) =
        some (rho.key B.proposer) := rfl
    have hhon' : rho.key B.proposer ∉ rho.faultyAt t := by
      rw [mem_honestKeysAt_iff, htime,
        min_eq_left (hv.in_horizon _ (List.mem_of_getElem? he)).2] at hhon
      exact hhon
    obtain ⟨j, t', hj, hs, hb⟩ := hv.unforgeable i v o t he _
      (contains_of_mem_delivered ho) (rho.key B.proposer) hsign hhon'
    obtain ⟨q, hq, hown⟩ := released_block_cut_at S rho hn hv hs hpar hroot' hb
    rw [simTraceAt_eq] at hown
    have hle : cutMap S rho hn (j + 1) ≤ cutMap S rho hn i :=
      cutMap_mono S rho hn (Nat.succ_le_of_lt hj)
    exact ⟨q, by omega, hown⟩
  | restart v t =>
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨_, _, _, _, hc⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
    have hcut := List.getElem_mem (lt_of_lt_of_eq hm (length_groupRecs _ _ _ _ _ _ _))
    rw [← hc, hrl] at hcut
    simp [exec, Node.restart, acCall] at hcut

end Consensus.Goldilocks.Simulation
