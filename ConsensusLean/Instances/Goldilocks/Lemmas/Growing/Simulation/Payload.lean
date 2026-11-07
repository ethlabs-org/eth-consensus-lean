module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Votes

public section

/-! # Provenance of payloads at their processing time

Honesty is checked at the consuming block cut. It transports backward to the proposal view
or the delivery credentials, never forward across a compromise.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)
open SA (Vote blockVotes)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- A payload object signed by a key honest at processing has an earlier genuine release. -/
theorem block_payload_source_at (hv : rho.ExecutionValid) {k : Nat} {y}
    {B : Blk (S.params (pubOf E) hn)} (hc : (simTraceAt S rho hn).BlockCallAt y k B)
    {o : Wire (Fintype.card V)} (ho : o ∈ payloadObjs B.fgPayload B.acPayload)
    {u : V} (hu : u ∉ rho.faultyAt ((simTraceAt S rho hn).time k))
    (hsign : rho.signerOf o = some u) :
    ∃ i t, cutMap S rho hn (i + 1) ≤ k ∧ rho.SendsAt u i t ∧ o ∈ rho.releasesAt i := by
  rw [simTraceAt_eq] at hc hu
  obtain ⟨acc, hnode, hlab⟩ := hc
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, _, he, hstart, _, hidx, _, htime, _, hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .fg (.block B acc) := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  have hbefore : ∀ j < i, cutMap S rho hn (j + 1) ≤ k := by
    intro j hj
    exact (cutMap_mono S rho hn (show j + 1 ≤ i by omega)).trans hstart
  cases ev with
  | tick v t =>
    have hv' : v ∉ rho.faultyAt 0 := event_honest_zero S rho hv he
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn i v t he hp] at hmem
      simp at hmem
    rw [eventCuts_tick_public S rho hn i v t he hp] at hmem
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨_, _, _, _, hc⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
    have hcut := List.getElem_mem (lt_of_lt_of_eq hm (length_groupRecs _ _ _ _ _ _ _))
    rw [← hc, hrl] at hcut
    obtain ⟨N4, N5, Q, R4, F, G, _, _, _, _, _, _, _, hR4, hcar, _⟩ :=
      tick_public_analysis S rho hn hv hv' he hp (preNode_releasable_at S rho hn hv he)
    have hB : blockObj (S.params (pubOf E) hn) B ∈ R4 := by
      rw [hR4]; exact mem_blockObjs.mpr ⟨B, acc, hcut, rfl⟩
    have ho' := hcar _ hB o ho
    have hnil := outbox_empty S rho hn hv v i
    have hrel : relHead S rho v (rho.stateBefore i v).seen
        (stateAt S rho hn v i).outbox.head? = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      obtain ⟨b, hb, _⟩ := mem_relHead S rho hx
      simp [hnil] at hb
    rw [hrel, List.append_nil] at ho'
    have htime' : (simTrace S rho hn).time k = t := htime
    rw [htime'] at hu
    have hui : u ∉ rho.faultyAt (rho.cutTime i) := by
      have hlaws := (Model.sysOf_laws schema (compiled (goldilocks S)) V).trace ⟨E, rho⟩ hv
      have ht := hlaws.cutTime_mono i (i + 1) (by omega)
        (by
          change i + 1 ≤ rho.events.length
          exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp he).1)
      change rho.cutTime i ≤ rho.cutTime (i + 1) at ht
      simp only [Model.Run.cutTime, he, Model.Event.time] at ht
      exact fun hf => hu (rho.faultyAt_mono ht hf)
    obtain ⟨j, hj, t', hs, hr⟩ := rho.signed_seen_released hv
      (Nat.le_of_lt (List.getElem?_eq_some_iff.mp he).1) ho' hui hsign
    exact ⟨j, t', hbefore j hj, hs, hr⟩
  | deliver v x t =>
    rw [eventCuts_deliver S rho hn i v x t he] at hmem
    obtain ⟨x', e, st', hx, hce, m, hm, hc, _⟩ := mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hmem
    have hcut := List.getElem_mem hm
    rw [← hc, hrl] at hcut
    have heq : e = .block B := by
      cases e with
      | tick x => exact False.elim (canonEvent_ne_tick hce x rfl)
      | block B' =>
        simp only [exec, onBlock] at hcut
        split_ifs at hcut
        · simp at hcut
        · split at hcut <;> simp [acCall] at hcut <;> simp_all
      | message => simp [exec, onMessage, acCall] at hcut
      | attestation => simp [exec, onAttestation] at hcut
      | restart => simp [exec, Node.restart, acCall] at hcut
    subst e
    obtain rfl := eq_blockObj_of_decodeBlock (decodeBlock_of_canonEvent hce)
    have hcontains := (contains_of_mem_delivered hx).trans (Model.Obj.Contains.step ho (.refl o))
    have htime' : (simTrace S rho hn).time k = t := htime
    rw [htime'] at hu
    obtain ⟨j, t', hj, hs, hr⟩ := hv.unforgeable i v x t he o hcontains u hsign hu
    exact ⟨j, t', hbefore j hj, hs, hr⟩
  | restart v t =>
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨_, _, _, _, hc⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
    have hcut := List.getElem_mem (lt_of_lt_of_eq hm (length_groupRecs _ _ _ _ _ _ _))
    rw [← hc, hrl] at hcut
    simp [exec, Node.restart, acCall] at hcut

/-- Votes carried by processed blocks were emitted while their signer was still honest. -/
theorem simTraceAt_carried_vote_unforgeable (hv : rho.ExecutionValid) :
    ∀ y i B, y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i) →
      (simTraceAt S rho hn).BlockCallAt y i B →
      ∀ v ∈ blockVotes B, v.val ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i) →
        ∃ j < i, (simTraceAt S rho hn).EmitAt v.val j v := by
  intro y k B _ hc m hm hh
  have hmem : voteObj m ∈ payloadObjs B.fgPayload B.acPayload :=
    List.mem_append_right _ (List.mem_map.mpr ⟨m, List.mem_append_left _ hm, rfl⟩)
  have ht : (simTraceAt S rho hn).time k ≤ rho.horizon := by
    obtain ⟨acc, _, hl⟩ := hc
    exact simTraceAt_labelled_time_le S rho hn hv (by rw [hl]; simp)
  have hh' : rho.key m.val ∉ rho.faultyAt ((simTraceAt S rho hn).time k) := by
    rwa [mem_honestKeysAt_iff, min_eq_left ht] at hh
  obtain ⟨i, t, hik, hs, hr⟩ := block_payload_source_at S rho hn hv hc hmem hh'
    (show rho.signerOf (voteObj m) = some (rho.key m.val) from rfl)
  obtain ⟨q, hq, he⟩ := released_vote_cut_at S rho hn hv hs hr
  exact ⟨q, hq.trans_le hik, by simpa only [ownKey_key] using he⟩

end Consensus.Goldilocks.Simulation
