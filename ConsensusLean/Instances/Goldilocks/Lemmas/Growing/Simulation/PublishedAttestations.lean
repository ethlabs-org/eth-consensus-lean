module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.SigningPrefix
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.PublishedVotes

public section

/-! # Attestation publication through an honest tick -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
private theorem release_closure_source (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (cs) :
    ∀ o ∈ Model.closure (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
      rho.hash (rho.ownKey v) nd cs).1.seen, o ∈ Model.closure nd.seen ∨
        o ∈ (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
          rho.hash (rho.ownKey v) nd cs).2 := by
  induction cs generalizing nd with
  | nil => intro o ho; exact Or.inl ho
  | cons c cs ih =>
    unfold Model.releaseAll
    split
    next hg =>
      intro o ho
      rcases ih _ o ho with ho | ho
      · change o ∈ Model.closure (nd.seen ++ [c]) at ho
        rw [Model.closure_append] at ho
        rcases List.mem_append.mp ho with ho | ho
        · exact Or.inl ho
        · obtain ⟨c', hc', hcon⟩ := (Model.mem_closure_iff _ _).mp ho
          obtain rfl := List.mem_singleton.mp hc'
          rcases hcon.cases with rfl | ⟨x, hx, hxo⟩
          · exact Or.inr List.mem_cons_self
          · have hr := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hg).1).1
            exact Or.inl (mem_closure_of_contains S
              (of_decide_eq_true (List.all_eq_true.mp hr x hx)) hxo)
      · exact Or.inr (List.mem_cons_of_mem _ ho)
    next hg =>
      intro o ho
      rcases ih nd o ho with ho | ho
      · exact Or.inl ho
      · exact Or.inr ho

/-- A tick's signed attestation passes the guard using only signings through that tick. -/
theorem tick_att_releases_at (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) :
    ∀ r ∈ eventCuts S rho hn i, ∀ C a,
      r.label = .fg (.attest C (some a)) → attObj a ∈ rho.releasesAt i := by
  intro r hr C a ha
  have hEC := eventCuts_tick_public S rho hn i v t he hp
  have hlab : r.label ∈ (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      (stateAt S rho hn v i).node t
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2 := by
    rw [hEC] at hr
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hr
    obtain ⟨-, -, -, -, hl⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
    rw [hl]; exact List.getElem_mem _
  have hv' : v ∉ rho.faultyAt 0 := event_honest_zero S rho hv he
  obtain ⟨hamo, -⟩ := outbox_inv S rho hn hv v i
  obtain ⟨hvote, -⟩ := (atMostOneVote_iff _).1 hamo
  obtain ⟨N4, N5, Q, R4, F, G, heq, hseen4, hseen5, hF, -, hQlen, hQ, hR4, hcar, hN5⟩ :=
    tick_public_analysis S rho hn hv hv' he hp (preNode_releasable_at S rho hn hv he)
  set nd := rho.stateBefore i v
  set R1 := relHead S rho v nd.seen (stateAt S rho hn v i).outbox.head?
  let Signed := fun b : FG.Att (Fintype.card V) =>
    ∃ k < cutMap S rho hn (i + 1), (simTraceAt S rho hn).SignAt (rho.ownKey v) k b
  have hsign (C') (b : FG.Att (Fintype.card V))
      (hc : Cut.fg (.attest C' (some b)) ∈ (exec (runProposer S rho hn)
        (digestOf S rho) (rho.ownKey v) (stateAt S rho hn v i).node t
        (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2) : Signed b := by
    rw [show Signed b = (∃ k < cutMap S rho hn (i + 1),
      (simTraceAt S rho hn).SignAt (rho.ownKey v) k b) from rfl, simTraceAt_eq]
    exact signAt_before_tick_end S rho hn he hp hc
  have hbase : ∀ b : FG.Att (Fintype.card V), b.val = rho.ownKey v →
      attObj b ∈ Model.closure (nd.seen ++ R1) → Signed b := by
    intro b hb ho
    rw [Model.closure_append] at ho
    rcases List.mem_append.mp ho with ho | ho
    · have hi := (List.getElem?_eq_some_iff.mp he).1
      have hlaws := (Model.sysOf_laws schema (compiled (goldilocks S)) V).trace ⟨E, rho⟩ hv
      have ht := hlaws.cutTime_mono i (i + 1) (by omega)
        (show i + 1 ≤ rho.events.length by omega)
      change rho.cutTime i ≤ rho.cutTime (i + 1) at ht
      have hhon : v ∉ rho.faultyAt (rho.cutTime i) := by
        intro hf
        have h := rho.faultyAt_mono ht hf
        exact hv.honest_only _ (List.mem_of_getElem? he)
          (by simpa only [Model.Run.cutTime, he, Model.Event.time, Model.Event.node] using h)
      obtain ⟨j, hj, t', hs, hrj⟩ := rho.signed_seen_released hv hi.le ho hhon
        (by simp [Model.Run.signerOf, Model.Obj.signer?, attObj, Model.Obj.auth,
          hb, Model.Run.ownKey])
      obtain ⟨k, hk, hsign⟩ := released_att_cut_at S rho hn hv hs hrj
      exact ⟨k, hk.trans_le (cutMap_mono S rho hn (by omega)), hsign⟩
    · exfalso
      obtain ⟨x, hx, hc⟩ := (Model.mem_closure_iff _ _).mp ho
      obtain ⟨q, hq, rfl⟩ := mem_relHead S rho hx
      obtain ⟨w, rfl⟩ := hvote q (List.mem_of_mem_head? hq)
      exact absurd (attObj_eq_pollObj S rho (contains_atomic S hc)).1 (by simp)
  have hsig4 : ∀ b : FG.Att (Fintype.card V), b.val = rho.ownKey v →
      attObj b ∈ Model.closure N4.seen → Signed b := by
    intro b hb ho
    rw [hseen4, Model.closure_append] at ho
    rcases List.mem_append.mp ho with ho | ho
    · exact hbase b hb ho
    · obtain ⟨c, hc, hcon⟩ := (Model.mem_closure_iff _ _).mp ho
      rcases hcon.cases with h | ⟨x, hx, hcx⟩
      · rw [← h, hR4] at hc
        exact absurd hc (attObj_not_mem_blockObjs S hn b _)
      · exact hbase b hb (mem_closure_of_contains S (hcar c hc x hx) hcx)
  have hsig5 : ∀ b : FG.Att (Fintype.card V), b.val = rho.ownKey v →
      attObj b ∈ Model.closure N5.seen → Signed b := by
    intro b hb ho
    have hsource : attObj b ∈ Model.closure N4.seen ∨
        attObj b ∈ (rho.dutyStep v N4 (.poll t.toNat)).2 := by
      rw [hN5] at ho
      unfold Model.Run.dutyStep at ho ⊢
      split at ho
      · rename_i hsel
        rw [ite_eq_left hsel]
        exact release_closure_source S rho v _ _ _ ho
      · exact Or.inl ho
    rcases hsource with ho | ho
    · exact hsig4 b hb ho
    · have hrel : (rho.dutyStep v N4 (.poll t.toNat)).2 =
          relHead S rho v N4.seen Q.head? ++ F := by
        have hs := dutyStep_seen S rho v N4 (.poll t.toNat)
        rw [← hN5, hseen5] at hs
        exact List.append_cancel_left hs.symm
      rw [hrel] at ho
      rcases List.mem_append.mp ho with hx | hx
      swap
      · rcases hF _ hx with ⟨τ, cs, heq⟩ | ⟨τ, m, heq⟩
        all_goals have hm := congrArg Model.Obj.msg heq; cases hm
      obtain ⟨q, hq, hobj⟩ := mem_relHead S rho hx
      have hq' := (attObj_eq_pollObj S rho hobj).1
      have hqQ : q ∈ Q := List.mem_of_mem_head? hq
      rw [hQ, hq'] at hqQ
      obtain ⟨C', b', hc, hw⟩ := att_mem_bodies S hn hqQ
      obtain rfl := encodeAtt_inj hw
      exact hsign C' b hc
  have hprot (seen : List (Model.protoOf (compiled (goldilocks S)) E).Object)
      (hs : ∀ b : FG.Att (Fintype.card V), b.val = rho.ownKey v →
      attObj b ∈ Model.closure seen → Signed b) :
      Model.protects (Model.protoOf (compiled (goldilocks S)) E) (rho.ownKey v) seen
        (attObj a) = true := by
    obtain ⟨ka, hka, hsa⟩ := hsign C a (ha ▸ hlab)
    refine Model.protects_iff.mpr ?_
    intro _
    refine ⟨Bool.eq_false_iff.mpr fun h => ?_, fun o ho hos =>
      ⟨Bool.eq_false_iff.mpr fun h => ?_, Bool.eq_false_iff.mpr fun h => ?_⟩⟩
    · obtain ⟨a1, b1, h1, h2, hsl⟩ :=
        (conflictsIff_iff.mp conflicts_iff (Fintype.card V) (attObj a) (attObj a)).mp h
      rw [← attObj_inj h1, ← attObj_inj h2] at hsl
      exact simTraceAt_signings_nonFraming_before S rho hn hv he hka hka hsa hsa hsl
    · obtain ⟨a1, b1, h1, rfl, hsl⟩ :=
        (conflictsIff_iff.mp conflicts_iff (Fintype.card V) (attObj a) o).mp h
      rw [← attObj_inj h1] at hsl
      have hb : b1.val = rho.ownKey v := by
        simpa [Model.Obj.signer?, attObj, Model.Obj.auth] using hos
      obtain ⟨kb, hkb, hsb⟩ := hs b1 hb ho
      exact simTraceAt_signings_nonFraming_before S rho hn hv he hka hkb hsa hsb hsl
    · obtain ⟨a1, b1, rfl, h2, hsl⟩ :=
        (conflictsIff_iff.mp conflicts_iff (Fintype.card V) o (attObj a)).mp h
      rw [← attObj_inj h2] at hsl
      have hb : a1.val = rho.ownKey v := by
        simpa [Model.Obj.signer?, attObj, Model.Obj.auth] using hos
      obtain ⟨kb, hkb, hsb⟩ := hs a1 hb ho
      exact simTraceAt_signings_nonFraming_before S rho hn hv he hkb hka hsb hsa hsl
  have hval := attest_val_of_mem_exec _ _ _ _ _ _ (ha ▸ hlab)
  have hq : Body.att (encodeAtt a) ∈ Q := by
    rw [hQ]
    apply List.mem_append_right
    rw [attBodies_eq]
    exact List.mem_flatMap.mpr ⟨_, ha ▸ hlab, List.mem_singleton_self _⟩
  have hobj : (attObj a : (Model.protoOf (compiled (goldilocks S)) E).Object) =
      pollObj S rho v (.att (encodeAtt a)) := by
    unfold attObj; rw [show a.val = rho.ownKey v from hval]; rfl
  have h4 := hprot N4.seen hsig4
  have h5 := hprot N5.seen hsig5
  rw [hobj] at h4 h5
  have hpos : ∀ q ∈ Q, Q.head? = some q ∨ Q.tail.head? = some q := by
    intro q hq
    match Q, hQlen, hq with
    | [a], _, hq => rw [List.mem_singleton] at hq; subst hq; exact Or.inl rfl
    | [a, b], _, hq =>
      rcases List.mem_pair.mp hq with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    | _ :: _ :: _ :: _, h, _ => simp at h
  rw [hobj, heq]
  have hd (seen) : (Model.protoOf (compiled (goldilocks S)) E).dependencies.ready
      (Model.closure seen) (pollObj S rho v (.att (encodeAtt a))) = true := rfl
  rcases hpos _ hq with h | h
  · refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
    apply List.mem_append_left
    rw [h, ← release_head S rho v N4 (some (.att (encodeAtt a)))]
    simp [Model.releaseAll, Model.releasable, Model.Obj.carried, h4, hd]
    exact List.mem_singleton_self _
  · refine List.mem_append_left _ (List.mem_append_right _ ?_)
    rw [h, ← release_head S rho v N5 (some (.att (encodeAtt a)))]
    simp [Model.releaseAll, Model.releasable, Model.Obj.carried, h5, hd]
    exact List.mem_singleton_self _

/-- A trace signing is released at its actual engine tick, under growing faults. -/
theorem simTraceAt_att_released (hv : rho.ExecutionValid) :
    ∀ y k a, y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time k) →
      (simTraceAt S rho hn).SignAt y k a →
      ReleasedFrom S rho (rho.key y) (attObj a) ((simTraceAt S rho hn).time k) := by
  rw [simTraceAt_eq]
  rintro y k a _ ⟨src, hnode, hlab⟩
  erw [releasedFrom_iff]
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, -, he, -, -, hidx, hn', ht, -, hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .fg (.attest src (some a)) := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  have hkey : ev.node = rho.key y := key_of_ownKey S rho (hn'.symm.trans hnode)
  rw [ht, ← hkey]
  cases ev with
  | tick v t =>
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn i v t he hp] at hmem
      simp at hmem
    exact ⟨i, Or.inl he, tick_att_releases_at S rho hn hv he hp r hmem src a hrl⟩
  | deliver v o t =>
    exfalso
    rw [eventCuts_deliver S rho hn i v o t he] at hmem
    obtain ⟨o', e, st', _, hce, kk, hk, hlabk, -⟩ := mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hmem
    have hcut := List.getElem_mem hk
    rw [← hlabk, hrl] at hcut
    obtain ⟨x, rfl⟩ := Compose.signed_only_in_ticks _ _ _ st' t e src a hcut
    exact canonEvent_ne_tick hce x rfl
  | restart v t =>
    exfalso
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨kk, hk, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨-, -, -, -, hlabk⟩ := getElem_groupRecs _ _ _ _ _ _ _ kk hk
    have hk' := lt_of_lt_of_eq hk (length_groupRecs _ _ _ _ _ _ _)
    have hcut := List.getElem_mem hk'
    rw [← hlabk, hrl] at hcut
    obtain ⟨x, hx⟩ := Compose.signed_only_in_ticks _ _ _ _ t .restart src a hcut
    cases hx

end Consensus.Goldilocks.Simulation
