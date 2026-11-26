module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Payload
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.AttUnforgeable
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PayloadSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.HeldRefusal
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.SignCut
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.AdmitsAtTick

public section

/-! # Genuine attestation releases under growing faults -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {binding : VoteBinding}

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- A released attestation is a signing cut of the releasing tick, or a held attestation that the
tick's first poll flushes. -/
theorem att_released_inv_at (hv : rho.ExecutionValid)
    {j : Nat} {v : V} {t : Time} (he : rho.events[j]? = some (.tick v t))
    {b : FG.Att (Fintype.card V)}
    (hb : (attObj b : (Model.protoOf (compiled (goldilocks S)) E).Object) ∈ rho.releasesAt j) :
    ((S.params (pubOf E) hn).toParams.IsPublic t ∧ ∃ C,
      Cut.fg (.attest C (some b)) ∈ (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v j).node t
        (.tick (encodeTxs (Model.mempool rho.inbox v t))
          (S.sign (pubOf E) (rho.ownKey v) t))).2) ∨
      b ∈ (stateAt S rho hn v j).held := by
  have hv' : v ∉ rho.faultyAt 0 := event_honest_zero S rho hv he
  obtain ⟨hamo, -⟩ := outbox_inv S rho hn hv v j
  obtain ⟨hvote, -⟩ := (atMostOneVote_iff _).1 hamo
  have hnotpend : (attObj b : (Model.protoOf (compiled (goldilocks S)) E).Object) ∉
      relHead S rho v (stateAt S rho hn v j).outbox.head? := by
    intro h
    obtain ⟨q, hq, hqo⟩ := mem_relHead S rho h
    obtain ⟨w, z, rfl⟩ := hvote q (List.mem_of_mem_head? hq)
    exact absurd (attObj_eq_pollObj S rho hqo).1 (by simp)
  have hflush : (attObj b : (Model.protoOf (compiled (goldilocks S)) E).Object) ∈
      relFlush S rho hn v (stateAt S rho hn v j) t → b ∈ (stateAt S rho hn v j).held := by
    intro h
    rw [relFlush_eq] at h
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp h
    injection heq with _ h₂
    injection h₂ with h₃
    injection h₃ with h₄
    obtain rfl := encodeAtt_inj h₄
    split_ifs at ha
    · exact ha
    · exact absurd ha List.not_mem_nil
  by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
  · obtain ⟨N4, N5, Q, R4, F, G, heq, -, -, hF, hG, -, hQ, hR4, -⟩ :=
      tick_public_analysis S rho hn hv hv' he hp (preNode_releasable_at S rho hn hv he)
    rw [heq] at hb
    have hQmem : ∀ ob, ob ∈ [Q.head?, Q.tail.head?] →
        (attObj b : (Model.protoOf (compiled
            (goldilocks S)) E).Object) ∈ relHead S rho v ob →
        ∃ C, Cut.fg (.attest C (some b)) ∈ (exec (runProposer S rho hn)
          (digestOf S rho) (rho.ownKey v)
          (stateAt S rho hn v j).node t
          (.tick (encodeTxs (Model.mempool rho.inbox v t))
            (S.sign (pubOf E) (rho.ownKey v) t))).2 := by
      intro ob hob h
      obtain ⟨q, rfl, hqo⟩ := mem_relHead S rho h
      obtain ⟨hq, -⟩ := attObj_eq_pollObj S rho hqo
      have hqQ : q ∈ Q := by
        rcases List.mem_pair.mp hob with h' | h'
        · exact List.mem_of_mem_head? h'.symm
        · exact List.mem_of_mem_tail (List.mem_of_mem_head? h'.symm)
      rw [hQ, hq] at hqQ
      have hqQ' : Body.att (encodeAtt b) ∈ emitted (stateAt S rho hn v j).voteIO
          (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
            (stateAt S rho hn v j).node t
            (.tick (encodeTxs (Model.mempool rho.inbox v t))
              (S.sign (pubOf E) (rho.ownKey v) t))).2 ++
          attBodies (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
            (stateAt S rho hn v j).node t
            (.tick (encodeTxs (Model.mempool rho.inbox v t))
              (S.sign (pubOf E) (rho.ownKey v) t))).2 := by
        split_ifs at hqQ
        · exact hqQ
        · exact List.mem_append_left _ (by simpa using hqQ)
      obtain ⟨C, a, hc, hw⟩ := att_mem_bodies S hn hqQ'
      have hab := encodeAtt_inj hw
      subst hab
      exact ⟨C, hc⟩
    rcases List.mem_append.mp hb with hb | h
    swap
    · exact absurd (hG _ h) (by simp [attObj, Model.Obj.auth])
    rcases List.mem_append.mp hb with hb | h
    swap
    · exact Or.inl ⟨hp, hQmem _ (by simp) h⟩
    rcases List.mem_append.mp hb with hb | h
    swap
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl ⟨hp, hQmem _ (by simp) h⟩
        · rcases hF _ h with ⟨τ, cs, heq⟩ | ⟨τ, m, w, heq⟩
          all_goals have hm := congrArg Model.Obj.msg heq; cases hm
      · exact Or.inr (hflush h)
    rcases List.mem_append.mp hb with h | h
    · exact absurd h hnotpend
    · rw [hR4] at h; exact absurd h (attObj_not_mem_blockObjs S hn b _)
  · rcases tick_other_releases S rho hn hv hv' he hp _ hb with h | h | h
    · exact absurd h hnotpend
    · exact Or.inr (hflush h)
    · exact absurd h (by simp [attObj, Model.Obj.auth])

/-- An attestation held by a node at an engine tick is its own, signed in the group of an earlier
public tick of the node. -/
private theorem held_signing_tick (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) {a : FG.Att (Fintype.card V)}
    (ha : a ∈ (stateAt S rho hn v i).held) :
    a.val = rho.ownKey v ∧ ∃ j < i, ∃ t', rho.events[j]? = some (.tick v t') ∧
      (S.params (pubOf E) hn).toParams.IsPublic t' ∧ ∃ C,
        Cut.fg (.attest C (some a)) ∈ (exec (runProposer S rho hn) (digestOf S rho)
          (rho.ownKey v) (stateAt S rho hn v j).node t'
          (.tick (encodeTxs (Model.mempool rho.inbox v t'))
            (S.sign (pubOf E) (rho.ownKey v) t'))).2 := by
  have hw := hv.tick_awake v t (List.mem_of_getElem? he)
  have hc := EngineDutyCut.tick (S := S) (rho := rho) (p := 0) he hw (Nat.zero_le _)
  obtain ⟨hval, j, q, hj, hs⟩ := engine_held_att_signed S rho hn hc (by
    simp only [List.take_zero, Model.Run.runDuties_nil, shapeOf_clock]
    simpa [stateAt_eq] using ha)
  have hji : j < i := by rcases hj with hj | ⟨_, hq⟩; exacts [hj, absurd hq (Nat.not_lt_zero _)]
  obtain ⟨t', he', hp', C, hc'⟩ := engineSignsAt_tick_cut S rho hn hv hs
  exact ⟨hval.trans (cut_self S rho hn hc), j, hji, t', he', hp', C, hc'⟩

/-- An attestation held by a node at an engine tick is its own, signed at an earlier trace cut. -/
private theorem held_signAt_before (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) {a : FG.Att (Fintype.card V)}
    (ha : a ∈ (stateAt S rho hn v i).held) :
    a.val = rho.ownKey v ∧
      ∃ k < cutMap S rho hn i, (simTrace S rho hn).SignAt (rho.ownKey v) k a := by
  obtain ⟨hval, j, hji, t', he', hp', C, hc'⟩ := held_signing_tick S rho hn hv he ha
  obtain ⟨k, hk, hsk⟩ := signAt_before_tick_end S rho hn he' hp' hc'
  exact ⟨hval, k, lt_of_lt_of_le hk (cutMap_mono S rho hn hji), hsk⟩

/-- A genuine attestation release has an earlier signing cut in the same engine prefix. -/
theorem released_att_cut_at (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {t : Time} (hs : rho.SendsAt v i t) {a : FG.Att (Fintype.card V)}
    (hb : attObj a ∈ rho.releasesAt i) :
    ∃ k < cutMap S rho hn (i + 1), (simTraceAt S rho hn).SignAt (rho.ownKey v) k a := by
  rw [simTraceAt_eq]
  rcases hs with hs | ⟨o, hs⟩
  · rcases att_released_inv_at S rho hn hv hs hb with ⟨hp, C, hc⟩ | ha
    · exact signAt_before_tick_end S rho hn hs hp hc
    · obtain ⟨-, k, hk, hsk⟩ := held_signAt_before S rho hn hv hs ha
      exact ⟨k, hk.trans_le (cutMap_mono S rho hn (Nat.le_succ i)), hsk⟩
  · exact absurd hb (deliver_not_att S rho hn hv hs a)

/-- An own admission of a tick is signed: a held attestation the tick flushes was signed at an
earlier trace cut, and an attestation the tick's FG update signs and admits at once is the signing
cut of the tick's own group. -/
private theorem admitsAt_signed (hv : rho.ExecutionValid) {j : Nat} {w : V} {t : Time}
    (he : rho.events[j]? = some (.tick w t)) {a : FG.Att (Fintype.card V)}
    (ha : a ∈ admitsAt S rho hn w j) :
    (∃ q < cutMap S rho hn j, (simTrace S rho hn).SignAt a.val q a) ∨
      ((S.params (pubOf E) hn).toParams.IsPublic t ∧ ∃ C,
        Cut.fg (.attest C (some a)) ∈ (exec (runProposer S rho hn) (digestOf S rho)
          (rho.ownKey w) (stateAt S rho hn w j).node t
          (.tick (encodeTxs (Model.mempool rho.inbox w t))
            (S.sign (pubOf E) (rho.ownKey w) t))).2) := by
  obtain ⟨j', hj', q, hs⟩ := admitsAt_tick_signed S rho hn hv he ha
  obtain ⟨t', he', hp, C, hc⟩ := engineSignsAt_tick_cut S rho hn hv hs
  rcases hj'.lt_or_eq with hlt | rfl
  · obtain ⟨k, hk, hsk⟩ := signAt_before_tick_end S rho hn he' hp hc
    rw [attest_val_of_mem_exec _ _ _ _ _ _ hc]
    exact Or.inl ⟨k, hk.trans_le (cutMap_mono S rho hn hlt), hsk⟩
  · obtain rfl : t' = t := (Model.Event.tick.inj (Option.some.inj (he'.symm.trans he))).2
    exact Or.inr ⟨hp, C, hc⟩

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
  · have hmem : attObj (binding := S.vote) a ∈ payloadObjs B.fgPayload B.acPayload :=
      List.mem_map.mpr ⟨a, ha, rfl⟩
    have hsource := block_payload_source_at S rho hn hv hc hmem hh'
      (show rho.signerOf (attObj a) = some (rho.key a.val) from rfl)
    rcases hsource with hsource | ⟨i, v, t, hik, he, a', ha', heq⟩
    swap
    · obtain ⟨hval, j, hj, hsj⟩ := held_signAt_before S rho hn hv he ha'
      rw [heldObj_eq_attObj S rho hval] at heq
      obtain rfl : a' = a := by
        injection heq with _ h₂
        injection h₂ with h₃
        injection h₃ with h₄
        exact (encodeAtt_inj h₄).symm
      rw [simTraceAt_eq, hval]
      exact ⟨j, lt_of_lt_of_le hj hik, hsj⟩
    rw [(simTrace_encoding S rho hn).2] at hsource
    rw [simTraceAt_eq, (simTrace_encoding S rho hn).1]
    exact NodeAsChainShape.CanonicalTrace.carried_att_sign_of_released (traceEncoding S hn) rho
      hsource fun hs hr => by
        simpa only [ownKey_key, simTraceAt_eq, (simTrace_encoding S rho hn).1,
          (simTrace_encoding S rho hn).2] using released_att_cut_at S rho hn hv hs hr
  rw [simTraceAt_eq] at hc hh' ⊢
  exact attCall_sign_of_released S rho hn hv hc hh' (fun hs hb => by
    simpa only [simTraceAt_eq, ownKey_key] using released_att_cut_at S rho hn hv hs hb)
    fun he ha => admitsAt_signed S rho hn hv he ha

end Consensus.Goldilocks.Simulation
