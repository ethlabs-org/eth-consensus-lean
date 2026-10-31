module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Forwarding
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Cuts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Shape
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.EngineSteps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Outbox
public import ConsensusLean.Lemmas.Model.Protection

public section

namespace Consensus.Goldilocks.Refinement

open Blocks Shape Node

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}

/-- Decoding a forwarding envelope identifies its canonical child using the supplied
digests and bounds the child's slot by the acceptance stamp. -/
theorem decodeForward_child {hs : List (Header Info × Nat)} {o : Wire sp.n}
    {x : Fin sp.n} {t : Time} {p : Option (Wire sp.n)} {B : Blk sp}
    (h : decodeForward sp hs o = some (x, t, p, B)) :
    decodeBlock sp hs (blockObj sp B) = some B ∧ sp.toParams.slotTime B.slot ≤ t := by
  unfold decodeForward at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨C, hc, h⟩ := h
    split at h
    · rename_i hp
      cases h
      exact ⟨by simpa only [hp.1] using hc, hp.2.2.2⟩
    · simp at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨C, hc, ⟨⟨y, pt, pp, A⟩, _, h⟩⟩ := h
    split at h
    · rename_i hp
      cases h
      exact ⟨by simpa only [hp.1] using hc, hp.2.2.2.2.2.2.2⟩
    · simp at h
  · simp at h

/-- Parsing a forwarding envelope authenticates its outer signer, independently of
whether its contained block was accepted by any receiver. -/
theorem decodeForward_signer {hs : List (Header Info × Nat)} {o : Wire sp.n}
    {x : Fin sp.n} {t : Time} {p : Option (Wire sp.n)} {B : Blk sp}
    (h : decodeForward sp hs o = some (x, t, p, B)) : o.signer? = some x := by
  rw [forwardObj_of_decodeForward hs o x t p B h]
  rfl

/-- Decoding the same canonical block under two digest tables agrees when they agree
on that block's header; this is the root-sensitive replacement for wire injectivity. -/
theorem decodeBlock_transport {hs hs' : List (Header Info × Nat)} {o : Wire sp.n}
    {B : Blk sp} (hd : decodeBlock sp hs o = some B)
    (hr : rootOf hs' (headerOf sp B) = rootOf hs (headerOf sp B)) :
    decodeBlock sp hs' o = some B := by
  obtain rfl := eq_blockObj_of_decodeBlock hd
  unfold decodeBlock at hd ⊢
  simp only [blockObj] at hd ⊢
  rw [hr]
  exact hd

/-- A durable-map update retains an old wrapper or records this exact acceptance.
This statement deliberately retains the accepted block, including its root; equality of
wire encodings alone does not recover that root. -/
theorem queueAccepted_wrapper_origin (st : State sp ro) (B : Blk sp)
    {root : Nat} {o : Wire sp.n}
    (h : (queueAccepted st B).wrappers root = some o) :
    st.wrappers root = some o ∨
      ∃ p, root = B.root ∧ o = forwardObj sp st.self st.now p B := by
  unfold queueAccepted at h
  split at h
  · exact Or.inl h
  · rename_i r hr
    generalize hp : (if r = sp.genesisRoot then some none else
      (st.wrappers r).map some) = parent at h
    cases parent with
    | none => exact Or.inl h
    | some p =>
      change Function.update st.wrappers B.root
        (some (forwardObj sp st.self st.now p B)) root = some o at h
      simp only [Function.update_apply] at h
      split_ifs at h with hr
      · exact Or.inr ⟨p, hr, (Option.some.inj h).symm⟩
      · exact Or.inl h

/-- Queueing a successful cut preserves the acceptance clock and local identity. -/
private theorem queueAccepted_self_now (st : State sp ro) (B : Blk sp) :
    (queueAccepted st B).self = st.self ∧ (queueAccepted st B).now = st.now := by
  unfold queueAccepted
  split
  · exact ⟨rfl, rfl⟩
  · rename_i r hr
    generalize (if r = sp.genesisRoot then some none else
      (st.wrappers r).map some) = parent
    cases parent <;> exact ⟨rfl, rfl⟩

/-- Every new durable wrapper in a handler result names a successful acceptance cut of
that handler. The old-map alternative preserves history across unrelated handlers. -/
theorem apply_wrapper_origin (st : State sp ro)
    (result : NodeState (goldilocksNode sp ro) × List (Cut (goldilocksNode sp ro)))
    {root : Nat} {o : Wire sp.n} (h : (apply st result).wrappers root = some o) :
    st.wrappers root = some o ∨ ∃ B p,
      .fg (.block B true) ∈ result.2 ∧ root = B.root ∧
      o = forwardObj sp st.self st.now p B := by
  have aux : ∀ (cs : List (Cut (goldilocksNode sp ro))) (st : State sp ro),
      (cs.foldl (fun s c => match c with
        | .fg (.block B true) => queueAccepted s B
        | _ => s) st).wrappers root = some o →
      st.wrappers root = some o ∨ ∃ B p,
        .fg (.block B true) ∈ cs ∧ root = B.root ∧
        o = forwardObj sp st.self st.now p B := by
    intro cs
    induction cs with
    | nil => intro st h; exact Or.inl h
    | cons c cs ih =>
      intro st h
      cases c with
      | ac c =>
        rcases ih st h with h | ⟨B, p, hm, hr, ho⟩
        · exact Or.inl h
        · exact Or.inr ⟨B, p, List.mem_cons_of_mem _ hm, hr, ho⟩
      | fg c =>
        cases c with
        | block B ok =>
          cases ok with
          | false =>
            rcases ih st h with h | ⟨B, p, hm, hr, ho⟩
            · exact Or.inl h
            · exact Or.inr ⟨B, p, List.mem_cons_of_mem _ hm, hr, ho⟩
          | true =>
            rcases ih (queueAccepted st B) h with h | ⟨C, p, hm, hr, ho⟩
            · rcases queueAccepted_wrapper_origin st B h with h | ⟨p, hr, ho⟩
              · exact Or.inl h
              · exact Or.inr ⟨B, p, List.mem_cons_self, hr, ho⟩
            · rw [(queueAccepted_self_now st B).1, (queueAccepted_self_now st B).2] at ho
              exact Or.inr ⟨C, p, List.mem_cons_of_mem _ hm, hr, ho⟩
        | _ =>
          rcases ih st h with h | ⟨B, p, hm, hr, ho⟩
          · exact Or.inl h
          · exact Or.inr ⟨B, p, List.mem_cons_of_mem _ hm, hr, ho⟩
  exact aux result.2 st h

/-- Fresh queue entries retain an indexed successful cut of the very handler that
created them, ready to be embedded into the event's cut prefix. -/
theorem apply_forward_origin_index (st : State sp ro)
    (result : NodeState (goldilocksNode sp ro) × List (Cut (goldilocksNode sp ro)))
    (q : Time × List (Wire sp.n)) (hq : q ∈ (apply st result).forwards) :
    q ∈ st.forwards ∨ ∃ B, ∃ p : Option (Wire sp.n), ∃ j : Nat,
      result.2[j]? = some (.fg (.block B true)) ∧
      q = (st.now, p.toList ++ [blockObj sp B]) := by
  rcases apply_forward_origin st result q hq with h | ⟨B, p, hm, he⟩
  · exact Or.inl h
  · obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hm
    exact Or.inr ⟨B, p, j, by simpa only [List.getElem?_eq_getElem hj] using congrArg some heq, he⟩

/-- A single delivered object can create a wrapper only through its actual canonical
handler. This keeps the handler state needed to locate the cut in recursive processing. -/
theorem processOne_forward_origin (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (hs : List (Header Info × Nat)) (st : State sp ro) (o : Wire sp.n)
    (q : Time × List (Wire sp.n)) (hq : q ∈ (processOne hs st o).forwards) :
    q ∈ st.forwards ∨ ∃ e B, ∃ p : Option (Wire sp.n),
      canonEvent sp ro hs o = some e ∧
      .fg (.block B true) ∈ (exec proposer dg st.self st.node st.now e).2 ∧
      q = (st.now, p.toList ++ [blockObj sp B]) := by
  have hrelay : ∀ (s : State sp ro) (c : Prop) [Decidable c],
      (relayIf s c o).forwards = s.forwards := by
    intro s c _
    unfold relayIf
    split <;> rfl
  rcases canonEvent_cases (ro := ro) hs o with he | ⟨B, he⟩ | ⟨v, he⟩ | ⟨a, he⟩
  · exact Or.inl (by simpa only [processOne, he] using hq)
  all_goals
    simp only [processOne, he, hrelay] at hq
    rcases apply_forward_origin _ _ q hq with h | ⟨C, p, hm, hq⟩
    · exact Or.inl h
    · exact Or.inr ⟨_, C, p, he, hm, hq⟩

/-- A fresh queue entry from recursive receipt has a successful record in that exact
delivery traversal, including its node and clock. -/
theorem foldl_processOne_forward_origin (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (hs : List (Header Info × Nat)) (i : Nat) (q : Time × List (Wire sp.n)) :
    ∀ (os : List (Wire sp.n)) (st : State sp ro) (sub : Nat),
    q ∈ (os.foldl (processOne hs) st).forwards →
    q ∈ st.forwards ∨ ∃ B, ∃ p : Option (Wire sp.n), ∃ r,
      r ∈ deliverRecs proposer dg hs st.self st.now i os st.node sub ∧
      r.label = .fg (.block B true) ∧ r.node = st.self ∧ r.time = st.now ∧
      q = (st.now, p.toList ++ [blockObj sp B]) := by
  intro os
  induction os with
  | nil => intro st sub h; exact Or.inl h
  | cons o os ih =>
    intro st sub h
    rcases ih (processOne hs st o) (sub + 1) h with h | ⟨B, p, r, hm, hl, hn, ht, hq⟩
    · rcases processOne_forward_origin proposer dg hs st o q h with h | ⟨e, B, p, he, hm, hq⟩
      · exact Or.inl h
      · obtain ⟨j, hj, hlabel⟩ := List.getElem_of_mem hm
        have hj' : j <
            (groupRecs proposer dg st.self st.node st.now (Nat.pair i sub) e).length := by
          rwa [length_groupRecs]
        obtain ⟨hn, ht, _, _, hl⟩ :=
          getElem_groupRecs proposer dg st.self st.node st.now (Nat.pair i sub) e j hj'
        refine Or.inr ⟨B, p, _, ?_, hl.trans hlabel, hn, ht, hq⟩
        rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ he]
        exact List.mem_append_left _ (List.getElem_mem hj')
    · simp only [processOne_self, processOne_now] at hm hn ht hq
      rw [processOne_node proposer dg] at hm
      refine Or.inr ⟨B, p, r, ?_, hl, hn, ht, hq⟩
      cases he : canonEvent sp ro hs o with
      | none =>
        rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ he]
        simpa only [he] using hm
      | some e =>
        rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ he]
        exact List.mem_append_right _ (by simpa only [he] using hm)

/-- A canonical, nonfuture block in a recursive receipt produces an actual block-call
record even when the store refuses it. -/
theorem deliverRecs_block_call (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat)
    (B : Blk sp) (hslot : B.slot ≤ sp.toParams.slotOf t) :
    ∀ (os : List (Wire sp.n)) (st : NodeState (goldilocksNode sp ro)) (sub : Nat),
    (∃ o ∈ os, canonEvent sp ro hs o = some (.block B)) →
    ∃ r ∈ deliverRecs proposer dg hs self t i os st sub,
      ∃ accepted, r.label = .fg (.block B accepted) := by
  intro os
  induction os with
  | nil => intro st sub h; simp at h
  | cons o os ih =>
    intro st sub ⟨x, hx, he⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ he]
      have hcuts : ∃ accepted cs,
          (exec proposer dg self st t (.block B)).2 = .fg (.block B accepted) :: cs := by
        simp only [exec, onBlock, show ¬ sp.toParams.slotOf t < B.slot from not_lt.mpr hslot,
          ↓reduceIte]
        split <;> exact ⟨_, _, rfl⟩
      obtain ⟨accepted, cs, hcuts⟩ := hcuts
      have hlen : 0 < (groupRecs proposer dg self st t (Nat.pair i sub) (.block B)).length := by
        rw [length_groupRecs, hcuts]
        exact Nat.zero_lt_succ _
      refine ⟨_, List.mem_append_left _ (List.getElem_mem hlen), accepted, ?_⟩
      rw [(getElem_groupRecs proposer dg self st t (Nat.pair i sub) (.block B) 0 hlen).2.2.2.2]
      simp only [List.getElem_of_eq hcuts, List.getElem_cons_zero]
    · cases ho : canonEvent sp ro hs o with
      | none =>
        rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ ho]
        exact ih st (sub + 1) ⟨x, hx, he⟩
      | some e =>
        rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ ho]
        obtain ⟨r, hr, accepted, ha⟩ := ih (exec proposer dg self st t e).1
          (sub + 1) ⟨x, hx, he⟩
        exact ⟨r, List.mem_append_right _ hr, accepted, ha⟩

section Trace

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- A decoded envelope's child is decoded identically inside any enclosing receipt.
Both roots are obtained from the engine hash of the child's header. -/
theorem decoded_forward_child_in_receipt
    {o receipt : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hc : Model.Obj.Contains receipt o)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) :
    blockObj (S.params (Model.pubOf E) hn) B ∈ receipt.parts ∧
      decodeBlock (S.params (Model.pubOf E) hn) (Model.digests rho.hash receipt)
        (blockObj (S.params (Model.pubOf E) hn) B) = some B := by
  have hchild : Model.Obj.Contains o (blockObj (S.params (Model.pubOf E) hn) B) := by
    rw [forwardObj_of_decodeForward _ _ _ _ _ _ hd]
    apply Model.Obj.Contains.step (c := blockObj _ B)
    · exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact Model.Obj.Contains.refl _
  have hreceipt := hc.trans hchild
  refine ⟨hreceipt, decodeBlock_transport (decodeForward_child hd).1 ?_⟩
  rw [rootOf_digests_of_mem S rho receipt _
    (List.mem_filterMap.mpr ⟨blockObj _ B, hreceipt, rfl⟩)]
  rw [rootOf_digests_of_mem S rho o _
    (List.mem_filterMap.mpr ⟨blockObj _ B, hchild, rfl⟩)]

omit [DecidableEq V] in
/-- A decodable forwarding candidate of a poll comes from its pre-duty forwarding
queue, not the ordinary outbox emission (which carries no child). -/
theorem poll_candidate_forward_queue (v : V)
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (u : Nat)
    {o : Wire (Fintype.card V)} {t : Time} {p : Option (Wire (Fintype.card V))}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (ho : o ∈ rho.signedCandidate v (.poll u)
      ((Model.protoOf (compiled (family S)) E).act nd.st (.poll u)).2)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) :
    (t, p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B]) ∈
      (shapeOf S hn nd).forwards := by
  obtain ⟨m, cs, hm, _, rfl⟩ := rho.mem_signedCandidate.mp ho
  rw [act_poll_snd S hn, (poll_outbox _ _).2] at hm
  rcases List.mem_append.mp hm with hm | hm
  · cases hh : (pollPre (shapeOf S hn nd)).outbox.head? with
    | none =>
      simp only [hh, Option.map_none, Option.toList_none] at hm
      exact False.elim (List.not_mem_nil hm)
    | some b =>
      simp only [hh, Option.map_some, Option.toList_some] at hm
      have he := List.mem_singleton.mp hm
      cases he
      have heq := forwardObj_of_decodeForward _ _ _ _ _ _ hd
      have hc := congrArg Model.Obj.carried heq
      change [] = p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B] at hc
      cases p <;> simp at hc
  · obtain ⟨⟨stamp, children⟩, hq, he⟩ := List.mem_map.mp hm
    cases he
    have heq := forwardObj_of_decodeForward (Model.digests rho.hash
      (.mk (.signed (rho.ownKey v) .poll) (.data (.forward stamp)) children))
      _ _ _ _ _ hd
    simp [forwardObj] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact hq

/-- An honestly signed forwarding envelope in seen closure has an actual prior release
by that signer. This is authentication provenance, not yet an acceptance witness. -/
theorem decoded_forward_seen_released (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {o : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (ho : o ∈ Model.closure (rho.stateBefore i v).seen)
    (hx : rho.key x ∈ rho.honest)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) :
    ∃ j < i, ∃ u, rho.SendsAt (rho.key x) j u ∧ o ∈ rho.releasesAt j := by
  apply rho.signed_seen_released hv ho hx
  change o.signer?.map rho.key = some (rho.key x)
  rw [decodeForward_signer hd]
  rfl

/-- An indexed successful canonical cut supplies acceptance at its actual recorded time.
In particular this bridge never turns a refused block call into acceptance. -/
theorem acceptAt_of_allCuts {k : Nat} {r : CutRec (S.params (Model.pubOf E) hn) (S.ro _)}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hr : (allCuts S rho hn)[k]? = some r) (hb : r.label = .fg (.block B true)) :
    (simTrace S rho hn).AcceptAt r.node k B ∧ (simTrace S rho hn).time k = r.time := by
  constructor
  · exact ⟨by simp [simTrace_node, hr], by simp [simTrace_label, hr, hb]⟩
  · simp [simTrace_time, hr]

/-- An acceptance in an actual event's record list gives the required strict event-prefix
bound; no search for a merely similar successful label is involved. -/
theorem acceptAt_of_eventCuts {i : Nat} (hi : i < rho.events.length)
    {r : CutRec (S.params (Model.pubOf E) hn) (S.ro _)}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hr : r ∈ eventCuts S rho hn i) (hb : r.label = .fg (.block B true)) :
    ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).AcceptAt r.node k B ∧
      (simTrace S rho hn).time k = r.time := by
  obtain ⟨j, hj, he⟩ := List.getElem_of_mem hr
  have hk : (allCuts S rho hn)[cutMap S rho hn i + j]? = some r := by
    rw [allCuts_getElem?_add S rho hn i j hi hj, List.getElem?_eq_getElem hj, he]
  refine ⟨cutMap S rho hn i + j, ?_, acceptAt_of_allCuts S rho hn hk hb⟩
  rw [cutMap_succ]
  omega

/-- The processing phase of an actual delivery queues only wrappers for acceptances in
that delivery, at its actual time. The event-boundary queue is empty, not a premise. -/
theorem delivery_forward_acceptance (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {o : Wire (Fintype.card V)} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (q : Time × List (Wire (Fintype.card V)))
    (hq : q ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).forwards) :
    ∃ B, ∃ p : Option (Wire (Fintype.card V)), ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).AcceptAt (rho.ownKey v) k B ∧
      (simTrace S rho hn).time k = t ∧
      q = (t, p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B]) := by
  have ht : (stateAt S rho hn v i).now = t :=
    (now_eq_lastClock S rho hn hv v i).trans (lastClock_deliver S rho hv he)
  rcases foldl_processOne_forward_origin (runProposer S rho hn) (digestOf S rho)
      (Model.digests rho.hash o) i q _ (stateAt S rho hn v i) 0 hq with
    h | ⟨B, p, r, hr, hb, hn', ht', hq⟩
  · rw [forwards_empty S rho hn hv v i] at h
    exact False.elim (List.not_mem_nil h)
  · simp only [stateAt_self, ht] at hr hn' ht' hq
    have hr' : r ∈ eventCuts S rho hn i := by
      rw [eventCuts_deliver S rho hn i v o t he]
      exact hr
    obtain ⟨k, hk, ha, htime⟩ := acceptAt_of_eventCuts S rho hn
      (List.getElem?_eq_some_iff.mp he).1 hr' hb
    exact ⟨B, p, k, hk, hn' ▸ ha, htime.trans ht', hq⟩

/-- Receipt witnesses require only a block call, including a refused call. -/
theorem blockCallAt_of_allCuts {k : Nat}
    {r : CutRec (S.params (Model.pubOf E) hn) (S.ro _)}
    {B : Blk (S.params (Model.pubOf E) hn)} {accepted : Bool}
    (hr : (allCuts S rho hn)[k]? = some r)
    (hb : r.label = .fg (.block B accepted)) :
    (simTrace S rho hn).BlockCallAt r.node k B ∧
      (simTrace S rho hn).time k = r.time := by
  constructor
  · exact ⟨accepted, by simp [simTrace_node, hr], by simp [simTrace_label, hr, hb]⟩
  · simp [simTrace_time, hr]

/-- Once its authenticated stamp is no later than receipt, a forwarding envelope's
child has a real processing call in that receipt, whether accepted or refused. -/
theorem received_forward_blockCall {i : Nat} {v : V}
    {receipt o : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t u : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    (hc : Model.Obj.Contains receipt o)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) (htu : t ≤ u) :
    ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).BlockCallAt (rho.ownKey v) k B ∧
      (simTrace S rho hn).time k = u := by
  obtain ⟨hmem, hdecode⟩ := decoded_forward_child_in_receipt S rho hn hc hd
  have hs : (S.params (Model.pubOf E) hn).toParams.slotTime B.slot ≤ u :=
    (decodeForward_child hd).2.trans htu
  have hslot : B.slot ≤ (S.params (Model.pubOf E) hn).toParams.slotOf u := by
    apply Nat.le_findGreatest _ hs
    have hcast := (le_slotTime (S.params (Model.pubOf E) hn).toParams B.slot).trans hs
    exact (Int.le_toNat (le_trans (Int.natCast_nonneg _) hcast)).2 hcast
  obtain ⟨r, hr, accepted, hb⟩ := deliverRecs_block_call (runProposer S rho hn)
    (digestOf S rho) (Model.digests rho.hash receipt) (rho.ownKey v) u i B hslot
    (delivered _ receipt) (stateAt S rho hn v i).node 0
    ⟨blockObj _ B, hmem, by simp only [canonEvent, hdecode]⟩
  obtain ⟨hn', ht', _⟩ := mem_deliverRecs (sp := S.params (Model.pubOf E) hn)
    (ro := S.ro _) (runProposer S rho hn) (digestOf S rho)
    (rho.ownKey v) (Model.digests rho.hash receipt) u i hr
  have hr' : r ∈ eventCuts S rho hn i := by
    rw [eventCuts_deliver S rho hn i v receipt u he]
    exact hr
  obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hr'
  have hk : (allCuts S rho hn)[cutMap S rho hn i + j]? = some r := by
    rw [allCuts_getElem?_add S rho hn i j (List.getElem?_eq_some_iff.mp he).1 hj,
      List.getElem?_eq_getElem hj, heq]
  obtain ⟨hcall, htime⟩ := blockCallAt_of_allCuts S rho hn hk hb
  refine ⟨cutMap S rho hn i + j, ?_, hn' ▸ hcall, htime.trans ht'⟩
  rw [cutMap_succ]
  omega

end Trace

end Consensus.Goldilocks.Refinement
