module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Payload

public section

/-! # Genuine attestation releases under growing faults -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- A released attestation is a signing cut of the releasing tick. -/
theorem att_released_inv_at (hv : rho.ExecutionValid)
    {j : Nat} {v : V} {t : Time} (he : rho.events[j]? = some (.tick v t))
    {b : FG.Att (Fintype.card V)}
    (hb : (attObj b : (Model.protoOf (compiled (goldilocks S)) E).Object) ∈ rho.releasesAt j) :
    (S.params (pubOf E) hn).toParams.IsPublic t ∧ ∃ C,
      Cut.fg (.attest C (some b)) ∈ (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v j).node t (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2 := by
  have hv' : v ∉ rho.faultyAt 0 := event_honest_zero S rho hv he
  obtain ⟨hamo, -⟩ := outbox_inv S rho hn hv v j
  obtain ⟨hvote, -⟩ := (atMostOneVote_iff _).1 hamo
  have hnotpend : ∀ seen, (attObj b : (Model.protoOf (compiled (goldilocks S)) E).Object) ∉
      relHead S rho v seen (stateAt S rho hn v j).outbox.head? := by
    intro seen h
    obtain ⟨q, hq, hqo⟩ := mem_relHead S rho h
    obtain ⟨w, rfl⟩ := hvote q (List.mem_of_mem_head? hq)
    exact absurd (attObj_eq_pollObj S rho hqo).1 (by simp)
  by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
  · refine ⟨hp, ?_⟩
    obtain ⟨N4, N5, Q, R4, F, G, heq, -, -, hF, hG, -, hQ, hR4, -⟩ :=
      tick_public_analysis S rho hn hv hv' he hp (preNode_releasable_at S rho hn hv he)
    rw [heq] at hb
    have hQmem : ∀ seen ob, ob ∈ [Q.head?, Q.tail.head?] →
        (attObj b : (Model.protoOf (compiled (goldilocks S)) E).Object) ∈ relHead S rho v seen ob →
        ∃ C, Cut.fg (.attest C (some b)) ∈ (exec (runProposer S rho hn)
          (digestOf S rho) (rho.ownKey v)
          (stateAt S rho hn v j).node t (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2 := by
      intro seen ob hob h
      obtain ⟨q, rfl, hqo⟩ := mem_relHead S rho h
      obtain ⟨hq, -⟩ := attObj_eq_pollObj S rho hqo
      have hqQ : q ∈ Q := by
        rcases List.mem_pair.mp hob with h' | h'
        · exact List.mem_of_mem_head? h'.symm
        · exact List.mem_of_mem_tail (List.mem_of_mem_head? h'.symm)
      rw [hQ, hq] at hqQ
      obtain ⟨C, a, hc, hw⟩ := att_mem_bodies S hn hqQ
      have hab := encodeAtt_inj hw
      subst hab
      exact ⟨C, hc⟩
    rcases List.mem_append.mp hb with hb | h
    swap
    · exact absurd (hG _ h) (by simp [attObj, Model.Obj.auth])
    rcases List.mem_append.mp hb with hb | h
    swap
    · exact hQmem _ _ (by simp) h
    rcases List.mem_append.mp hb with hb | h
    swap
    · rcases List.mem_append.mp h with h | h
      · exact hQmem _ _ (by simp) h
      · rcases hF _ h with ⟨τ, cs, heq⟩ | ⟨τ, m, heq⟩
        all_goals have hm := congrArg Model.Obj.msg heq; cases hm
    rcases List.mem_append.mp hb with h | h
    · exact absurd h (hnotpend _)
    · rw [hR4] at h; exact absurd h (attObj_not_mem_blockObjs S hn b _)
  · exfalso
    rcases tick_other_releases S rho hn hv hv' he hp _ hb with h | h
    · exact hnotpend _ h
    · exact absurd h (by simp [attObj, Model.Obj.auth])

/-- A genuine attestation release has an earlier signing cut in the same engine prefix. -/
theorem released_att_cut_at (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {t : Time} (hs : rho.SendsAt v i t) {a : FG.Att (Fintype.card V)}
    (hb : attObj a ∈ rho.releasesAt i) :
    ∃ k < cutMap S rho hn (i + 1), (simTraceAt S rho hn).SignAt (rho.ownKey v) k a := by
  rw [simTraceAt_eq]
  rcases hs with hs | ⟨o, hs⟩
  · obtain ⟨hp, C, hc⟩ := att_released_inv_at S rho hn hv hs hb
    exact signAt_before_tick_end S rho hn hs hp hc
  · exact absurd hb (deliver_not_att S rho hn hv hs a)

/-- A signer honest at processing signed the processed attestation at an earlier cut,
also when it is carried by a block or processed by its own signer. -/
theorem simTraceAt_att_unforgeable (hv : rho.ExecutionValid) :
    ∀ y k a, y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time k) →
      ((simTraceAt S rho hn).AttCallAt y k a ∨
        ∃ B, (simTraceAt S rho hn).BlockCallAt y k B ∧ a ∈ B.fgPayload) →
      a.val ∈ honestKeysAt S rho ((simTraceAt S rho hn).time k) →
        ∃ j < k, (simTraceAt S rho hn).SignAt a.val j a := by
  intro y k a _ hc hh
  have hl : (simTraceAt S rho hn).label k ≠ none := by
    rcases hc with ⟨_, hl⟩ | ⟨B, ⟨acc, _, hl⟩, _⟩ <;> rw [hl] <;> simp
  have hh' : rho.key a.val ∉ rho.faultyAt ((simTraceAt S rho hn).time k) := by
    rwa [mem_honestKeysAt_iff, min_eq_left (simTraceAt_labelled_time_le S rho hn hv hl)] at hh
  rcases hc with hc | ⟨B, hc, ha⟩
  swap
  · have hmem : attObj a ∈ payloadObjs B.fgPayload B.acPayload :=
      List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
    obtain ⟨i, t, hik, hs, hr⟩ := block_payload_source_at S rho hn hv hc hmem hh'
      (show rho.signerOf (attObj a) = some (rho.key a.val) from rfl)
    obtain ⟨q, hq, he⟩ := released_att_cut_at S rho hn hv hs hr
    exact ⟨q, hq.trans_le hik, by simpa only [ownKey_key] using he⟩
  rw [simTraceAt_eq] at hc hl hh' ⊢
  obtain ⟨hnode, hlab⟩ := hc
  obtain ⟨r, i, ev, hi, he, hstart, _, hidx, _, htime, _, hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .fg (.attestation a) := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  cases ev with
  | tick v t =>
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn i v t he hp] at hmem
      simp at hmem
    rw [eventCuts_tick_public S rho hn i v t he hp] at hidx
    have hm := (List.getElem?_eq_some_iff.mp hidx).1
    have hr := (List.getElem?_eq_some_iff.mp hidx).2
    have hc := (getElem_groupRecs _ _ _ _ _ _ _ _ hm).2.2.2.2
    rw [hr, hrl] at hc
    have hcs : (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t
        (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2[k - cutMap S rho hn i]? =
          some (.fg (.attestation a)) := by
      rw [List.getElem?_eq_getElem (lt_of_lt_of_eq hm (length_groupRecs _ _ _ _ _ _ _)), ← hc]
    obtain ⟨q, hq, C, hC⟩ := Compose.tick_attestation_prev _ _ _ _ _ _ hcs
    have hval := attest_val_of_mem_exec (sp := S.params (pubOf E) hn) (ro := S.ro _)
      (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) (stateAt S rho hn v i).node t
      (.tick (encodeTxs (Model.mempool rho.inbox v t))) (List.mem_of_getElem? hC)
    have hq' : q < (eventCuts S rho hn i).length := by
      rw [eventCuts_tick_public S rho hn i v t he hp, length_groupRecs]
      exact (List.getElem?_eq_some_iff.mp hC).1
    have hrec := allCuts_getElem?_add S rho hn i q (List.getElem?_eq_some_iff.mp he).1 hq'
    rw [List.getElem?_eq_getElem hq'] at hrec
    refine ⟨cutMap S rho hn i + q, by omega, C, ?_, ?_⟩
    · rw [simTrace_node, hrec]
      simp only [Option.elim_some]
      simp only [eventCuts_tick_public S rho hn i v t he hp]
      exact (getElem_groupRecs _ _ _ _ _ _ _ _ _).1.trans hval.symm
    · rw [simTrace_label, hrec]
      simp only [Option.map_some]
      simp only [eventCuts_tick_public S rho hn i v t he hp]
      exact congrArg some ((getElem_groupRecs _ _ _ _ _ _ _ _ _).2.2.2.2.trans
        (List.getElem?_eq_some_iff.mp hC).2)
  | deliver v o t =>
    rw [eventCuts_deliver S rho hn i v o t he] at hmem
    obtain ⟨o', e, st', ho, hce, q, hq, hc, _⟩ := mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hmem
    have hcut := List.getElem_mem hq
    rw [← hc, hrl] at hcut
    have heq : e = .attestation a := by
      cases e with
      | tick x => exact False.elim (canonEvent_ne_tick hce x rfl)
      | attestation a' =>
        simp only [exec, onAttestation, List.mem_singleton, Cut.fg.injEq,
          FGLabel.attestation.injEq] at hcut
        exact congrArg Event.attestation hcut.symm
      | block B =>
        simp only [exec, onBlock] at hcut
        split_ifs at hcut
        · simp at hcut
        · split at hcut <;> simp [acCall] at hcut
      | message => simp [exec, onMessage, acCall] at hcut
      | restart => simp [exec, Node.restart, acCall] at hcut
    subst e
    have ho' : o' = attObj a := by
      rcases canonEvent_eq_some hce with ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨a', h, ho⟩
      · cases h
      · cases h
      · cases h; exact ho
    subst o'
    have htime' : (simTrace S rho hn).time k = t := htime
    rw [htime'] at hh'
    obtain ⟨j, t', hj, hs, hb⟩ := hv.unforgeable i v o t he _ (contains_of_mem_delivered ho)
      (rho.key a.val) rfl hh'
    obtain ⟨q, hq, hs⟩ := released_att_cut_at S rho hn hv hs hb
    rw [simTraceAt_eq] at hs
    have hle : cutMap S rho hn (j + 1) ≤ cutMap S rho hn i :=
      cutMap_mono S rho hn (Nat.succ_le_of_lt hj)
    exact ⟨q, by omega, by simpa only [ownKey_key] using hs⟩
  | restart v t =>
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨_, _, _, _, hc⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
    have hcut := List.getElem_mem (lt_of_lt_of_eq hm (length_groupRecs _ _ _ _ _ _ _))
    rw [← hc, hrl] at hcut
    simp [exec, Node.restart, acCall] at hcut

end Consensus.Goldilocks.Simulation
