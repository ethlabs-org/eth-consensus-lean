module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Release
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Events

public section

/-! # Genuine vote releases in the canonical growing trace -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)
open SA (Vote)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

private theorem emit_of_record {i : Nat} {ev}
    (he : rho.events[i]? = some ev) {r : CutRec (S.params (pubOf E) hn) (S.ro _)}
    (hr : r ∈ eventCuts S rho hn i) {ℓ} (hl : r.label = .ac ℓ)
    {em} (hem : em ∈ ℓ.emits) :
    ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).EmitAt (rho.ownKey ev.node) k em.msg := by
  have hnode := (mem_eventCuts S rho hn he hr).1
  obtain ⟨m, hm, hrm⟩ := List.getElem_of_mem hr
  have hk := allCuts_getElem?_add S rho hn i m (List.getElem?_eq_some_iff.mp he).1 hm
  rw [List.getElem?_eq_getElem hm, hrm] at hk
  refine ⟨cutMap S rho hn i + m, ?_, ℓ, ⟨?_, ?_⟩, em, hem, rfl⟩
  · rw [cutMap_succ]; omega
  · rw [simTrace_node, hk]; exact hnode
  · rw [simTrace_label, hk]; exact congrArg some hl

private theorem emit_of_tick_body {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) {m : Vote (Fintype.card V)}
    (hm : Body.vote (encodeVote m) ∈ emitted (exec (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node t
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2) :
    ∃ k < cutMap S rho hn (i + 1), (simTrace S rho hn).EmitAt (rho.ownKey v) k m := by
  obtain ⟨ℓ, hc, em, hem, rfl⟩ := mem_emitted.mp hm
  obtain ⟨q, hq, hcq⟩ := List.getElem_of_mem hc
  have hq' : q < (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      (stateAt S rho hn v i).node t (Nat.pair i 0)
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).length := by
    rwa [length_groupRecs]
  apply emit_of_record S rho hn he (r := (groupRecs (runProposer S rho hn) (digestOf S rho)
    (rho.ownKey v) (stateAt S rho hn v i).node t (Nat.pair i 0)
    (.tick (encodeTxs (Model.mempool rho.inbox v t))))[q]) ?_ ?_ hem
  · rw [eventCuts_tick_public S rho hn i v t he hp]; exact List.getElem_mem hq'
  · exact (getElem_groupRecs _ _ _ _ _ _ _ q hq').2.2.2.2.trans hcq

/-- A genuine release of a canonical vote comes from a local emission before the end cut. -/
theorem released_vote_cut_at (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {t : Time} (hs : rho.SendsAt v i t) {m : Vote (Fintype.card V)}
    (hb : voteObj m ∈ rho.releasesAt i) :
    ∃ k < cutMap S rho hn (i + 1), (simTraceAt S rho hn).EmitAt (rho.ownKey v) k m := by
  rw [simTraceAt_eq]
  have hbody : ∀ b, voteObj m = pollObj S rho v b → b = Body.vote (encodeVote m) := by
    intro b heq
    exact (Model.Msg.data.inj (congrArg Model.Obj.msg heq)).symm
  rcases hs with he | ⟨o, he⟩
  · have hv' : v ∉ rho.faultyAt 0 := event_honest_zero S rho hv he
    have hnil := outbox_empty S rho hn hv v i
    by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
    · obtain ⟨N4, N5, Q, R4, F, G, hr, _, _, hF, hG, _, hQ, hR4, _⟩ :=
        tick_public_analysis S rho hn hv hv' he hp (preNode_releasable_at S rho hn hv he)
      have hq : ∀ seen ob, (∀ b, ob = some b → b ∈ Q) →
          voteObj m ∈ relHead S rho v seen ob →
          ∃ k < cutMap S rho hn (i + 1), (simTrace S rho hn).EmitAt (rho.ownKey v) k m := by
        intro seen ob hmem hb
        obtain ⟨b, hob, heq⟩ := mem_relHead S rho hb
        have hbq := hmem b hob
        rw [hbody b heq, hQ] at hbq
        rcases List.mem_append.mp hbq with hbq | hbq
        · exact emit_of_tick_body S rho hn he hp hbq
        · exact False.elim (vote_not_mem_attBodies _ _ hbq)
      rw [hr] at hb
      rcases List.mem_append.mp hb with hb | hb
      · rcases List.mem_append.mp hb with hb | hb
        · rcases List.mem_append.mp hb with hb | hb
          · rcases List.mem_append.mp hb with hb | hb
            · obtain ⟨b, hb, _⟩ := mem_relHead S rho hb
              rw [hnil] at hb
              cases hb
            · rw [hR4] at hb
              obtain ⟨B, acc, _, heq⟩ := mem_blockObjs.mp hb
              have hh := congrArg Model.Obj.msg heq
              cases hh
          · rcases List.mem_append.mp hb with hb | hb
            · exact hq _ _ (fun _ h => List.mem_of_mem_head? h) hb
            · rcases hF _ hb with ⟨τ, cs, heq⟩ | ⟨τ, m, heq⟩
              all_goals have hh := congrArg Model.Obj.msg heq; cases hh
        · exact hq _ _ (fun _ h => List.mem_of_mem_tail (List.mem_of_mem_head? h)) hb
      · have hh := hG _ hb; cases hh
    · rcases tick_other_releases S rho hn hv hv' he hp _ hb with hb | hb
      · obtain ⟨b, hb, _⟩ := mem_relHead S rho hb
        rw [hnil] at hb
        cases hb
      · cases hb
  · have ht0 := (hv.in_horizon _ (List.mem_of_getElem? he)).1
    have hnow : (stateAt S rho hn v i).now = t :=
      (now_eq_lastClock S rho hn hv v i).trans (lastClock_of_deliver S rho hv v he)
    simp only [Model.Run.releasesAt, he, Model.Run.deliver] at hb
    rcases List.mem_append.mp hb with hb | hb
    · rw [deliverDuties_eq S t ht0] at hb
      erw [Model.Run.runDuties_cons, Model.Run.runDuties_nil] at hb
      simp only [List.append_nil] at hb
      rcases dutyStep_poll_sub S rho hn v _ _ _ hb with
        ⟨b, hb, heq⟩ | ⟨τ, cs, heq⟩ | ⟨τ, m, heq⟩
      · have hf : (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).fgDue = false :=
          (process_fgDue _ _ _).trans (fgDue_eq_false S rho hn v i)
        change (pollPre (process ((rho.stateBefore i v).st.1 hn) o
          (Model.digests rho.hash o))).outbox.head? = some b at hb
        rw [← stateAt_eq S rho hn v i] at hb
        rw [pollPre_eq, hf] at hb
        have hb' := List.mem_of_mem_head? hb
        rw [hbody b heq] at hb'
        rcases process_outbox_source (runProposer S rho hn) (digestOf S rho)
          (Model.digests rho.hash o) t i _ (stateAt S rho hn v i) 0 hnow _ hb' with
          hb | ⟨r, hr, ℓ, hl, em, hem, heq⟩
        · rw [outbox_empty S rho hn hv v i] at hb; cases hb
        · have hm := congrArg (decodeVote (Fintype.card V)) (Body.vote.inj heq)
          rw [decodeVote_encodeVote, decodeVote_encodeVote] at hm
          have hm := Option.some.inj hm
          rw [hm]
          apply emit_of_record S rho hn he (r := r) ?_ hl hem
          rw [eventCuts_deliver S rho hn i v o t he, ← self_eq_ownKey S rho hn v i]
          exact hr
      · have hh := congrArg Model.Obj.msg heq; cases hh
      · have hh := congrArg Model.Obj.msg heq; cases hh
    · have hh := gossip_unsigned S rho _ _ _ _ hb; cases hh

/-- A signer still honest when its message is processed genuinely emitted it earlier. -/
theorem simTraceAt_msg_unforgeable (hv : rho.ExecutionValid) :
    ∀ y i (m : Vote (Fintype.card V)), y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i) →
      (simTraceAt S rho hn).MsgCallAt y i m →
      m.val ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i) →
        ∃ j < i, (simTraceAt S rho hn).EmitAt m.val j m := by
  rw [simTraceAt_eq]
  rintro y k m _ ⟨ℓ, ⟨hnode, hlab⟩, hcall⟩ hhon
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, _, he, hstart, _, hidx, _, htime, _, hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .ac ℓ := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  obtain ⟨v, o, t, rfl⟩ := eq_deliver_of_cut S rho hn he hmem (Or.inr ⟨ℓ, m, hrl, hcall⟩)
  rw [eventCuts_deliver S rho hn i v o t he] at hmem
  obtain ⟨o', e, st', ho, hce, q, hq, hc, _⟩ := mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hmem
  have hcut := List.getElem_mem hq
  rw [← hc, hrl] at hcut
  have heq : e = .message m := by
    cases e with
    | tick x => exact False.elim (canonEvent_ne_tick hce x rfl)
    | message m' =>
      simp only [exec, onMessage, acCall, List.mem_singleton, Cut.ac.injEq] at hcut
      subst ℓ
      cases hcall
      rfl
    | block B =>
      simp only [exec, onBlock] at hcut
      split_ifs at hcut
      · simp at hcut
      · split at hcut <;> simp [acCall] at hcut
        subst ℓ
        cases hcall
    | attestation => simp [exec, onAttestation] at hcut
    | restart =>
      simp only [exec, Node.restart, acCall, List.mem_singleton, Cut.ac.injEq] at hcut
      subst ℓ
      cases hcall
  subst e
  have ho' : o' = voteObj m := by
    rcases canonEvent_eq_some hce with ⟨_, h, _⟩ | ⟨m', h, ho⟩ | ⟨_, h, _⟩
    · cases h
    · cases h; exact ho
    · cases h
  subst o'
  have hhon' : rho.key m.val ∉ rho.faultyAt t := by
    rw [mem_honestKeysAt_iff, htime,
      min_eq_left (hv.in_horizon _ (List.mem_of_getElem? he)).2] at hhon
    exact hhon
  obtain ⟨j, t', hj, hs, hb⟩ := hv.unforgeable i v o t he _ (contains_of_mem_delivered ho)
    (rho.key m.val) rfl hhon'
  obtain ⟨q, hq, hem⟩ := released_vote_cut_at S rho hn hv hs hb
  rw [simTraceAt_eq] at hem
  have hle : cutMap S rho hn (j + 1) ≤ cutMap S rho hn i :=
    cutMap_mono S rho hn (Nat.succ_le_of_lt hj)
  exact ⟨q, by omega, by simpa only [ownKey_key] using hem⟩

end Consensus.Goldilocks.Simulation
