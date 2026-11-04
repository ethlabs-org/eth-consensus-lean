module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSchedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers

public section

/-! # Goldilocks Simulation: payload credentials and blocks of cuts

Carried votes and attestations come from earlier signing cuts. The trace's states and groups
across blocks of cuts support the engine/trace correspondence proved in `RunSimulates`. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload blockVotes)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-! ## `GoldilocksRun` -/

omit [DecidableEq V] in
/-- The genesis block's root is the digest of its content: `dgOf` at `none` is the genesis
root. -/
theorem simTrace_genesis_root_ok :
    ((S.params (pubOf E) hn).toParams.genesisBlock
      (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload).RootOk
        (digestOf S rho) := by
  simp only [Block.RootOk, digestOf_eq, Params.genesisBlock]
  erw [dgOf_eq]

/-- An honest-signed payload object of any called block was released before its engine event. -/
private theorem block_payload_source (hv : rho.ExecutionValid) {k : Nat} {y}
    {B : Blk (S.params (pubOf E) hn)} (hc : (simTrace S rho hn).BlockCallAt y k B)
    {o : Wire (Fintype.card V)} (ho : o ∈ payloadObjs B.fgPayload B.acPayload)
    {u : V} (hu : u ∈ rho.honest) (hsign : rho.signerOf o = some u) :
    ∃ i t, cutMap S rho hn (i + 1) ≤ k ∧ rho.SendsAt u i t ∧ o ∈ rho.releasesAt i := by
  obtain ⟨acc, hnode, hlab⟩ := hc
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, _, he, hstart, _, hidx, _, _, _, hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .fg (.block B acc) := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  have hbefore : ∀ j < i, cutMap S rho hn (j + 1) ≤ k := by
    intro j hj
    exact (cutMap_mono S rho hn (show j + 1 ≤ i by omega)).trans hstart
  cases ev with
  | tick v t =>
    have hv' := hv.honest_only _ (List.mem_of_getElem? he)
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
      tick_public_analysis S rho hn hv hv' he hp (preNode_releasable S rho hn hv hv' he)
    have hB : blockObj (S.params (pubOf E) hn) B ∈ R4 := by
      rw [hR4]; exact mem_blockObjs.mpr ⟨B, acc, hcut, rfl⟩
    have ho' := hcar _ hB o ho
    have hnil := outbox_empty S rho hn hv v hv' i
    have hrel : relHead S rho v (rho.stateBefore i v).seen
        (stateAt S rho hn v i).outbox.head? = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      obtain ⟨b, hb, _⟩ := mem_relHead S rho hx
      simp [hnil] at hb
    simp only [Model.Event.node] at ho'
    rw [hrel, List.append_nil] at ho'
    obtain ⟨j, hj, t', hs, hr⟩ := rho.signed_seen_released hv ho' hu hsign
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
    obtain ⟨j, t', hj, hs, hr⟩ := hv.unforgeable i v x t he o hcontains u hu hsign
    exact ⟨j, t', hbefore j hj, hs, hr⟩
  | restart v t =>
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨_, _, _, _, hc⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
    have hcut := List.getElem_mem (lt_of_lt_of_eq hm (length_groupRecs _ _ _ _ _ _ _))
    rw [← hc, hrl] at hcut
    simp [exec, Node.restart, acCall] at hcut

/-- Honest carried votes originate in earlier canonical emission cuts. -/
theorem simTrace_carried_vote_unforgeable (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i B, (simTrace S rho hn).BlockCallAt y i B →
      ∀ v ∈ blockVotes B, v.val ∈ honestKeys S rho →
        ∃ j < i, (simTrace S rho hn).EmitAt v.val j v := by
  intro y _ k B hc m hm hh
  rw [mem_honestKeys_iff] at hh
  have hmem : voteObj m ∈ payloadObjs B.fgPayload B.acPayload :=
    List.mem_append_right _ (List.mem_map.mpr ⟨m, List.mem_append_left _ hm, rfl⟩)
  obtain ⟨i, t, hik, hs, hr⟩ := block_payload_source S rho hn hv hc hmem hh
    (show rho.signerOf (voteObj m) = some (rho.key m.val) from rfl)
  obtain ⟨q, hq, he⟩ := released_vote_cut S rho hn hv hs hh hr
  exact ⟨q, hq.trans_le hik, by simpa only [ownKey_key] using he⟩

private theorem released_att_cut (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (hs : rho.SendsAt v i t) (hv' : v ∈ rho.honest) {a : FG.Att (Fintype.card V)}
    (hb : attObj a ∈ rho.releasesAt i) :
    ∃ k < cutMap S rho hn (i + 1), (simTrace S rho hn).SignAt (rho.ownKey v) k a := by
  rcases hs with hs | ⟨o, hs⟩
  · obtain ⟨hp, C, hc⟩ := att_released_inv S rho hn hv hv' hs hb
    exact signAt_before_tick_end S rho hn hs hp hc
  · exact absurd hb (deliver_not_att S rho hn hv hs a)

/-- An attestation of an honest signer that an honest node processes was signed by that signer
at an earlier cut, including own processing and refused block payloads. -/
theorem simTrace_att_unforgeable (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i a,
      ((simTrace S rho hn).AttCallAt y i a ∨
        ∃ B, (simTrace S rho hn).BlockCallAt y i B ∧ a ∈ B.fgPayload) →
      a.val ∈ honestKeys S rho → ∃ j < i, (simTrace S rho hn).SignAt a.val j a := by
  intro y _ k a hc hh
  rw [mem_honestKeys_iff] at hh
  rcases hc with ⟨hnode, hlab⟩ | ⟨B, hc, ha⟩
  swap
  · have hmem : attObj a ∈ payloadObjs B.fgPayload B.acPayload :=
      List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
    obtain ⟨i, t, hik, hs, hr⟩ := block_payload_source S rho hn hv hc hmem hh
      (show rho.signerOf (attObj a) = some (rho.key a.val) from rfl)
    obtain ⟨q, hq, he⟩ := released_att_cut S rho hn hv hs hh hr
    exact ⟨q, hq.trans_le hik, by simpa only [ownKey_key] using he⟩
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, hi, he, hstart, _, hidx, _, _, _, hlab'⟩ := simTrace_cut S rho hn hl
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
    obtain ⟨j, t', hj, hs, hb⟩ := hv.unforgeable i v o t he _ (contains_of_mem_delivered ho)
      (rho.key a.val) hh rfl
    obtain ⟨q, hq, hs⟩ := released_att_cut S rho hn hv hs hh hb
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

/-! ## Blocks of cuts

The trace's state across a block of cuts: unchanged across other nodes' cuts, the handler's
state across a group, `deliverState` across a delivery's groups; and a block with the engine's
ids is a `GroupAt` / `DeliverSeq` of the trace. -/

section

variable {P : Params} {A : NodeAC P}

/-- The `k`-th post-state of a cut list is the fold of its first `k + 1` cuts. -/
theorem cutPosts_getElem (self : Fin P.n) (t : Time) (cs : List (Cut A)) (st : NodeState A)
    (k : Nat) (hk : k < (cutPosts self t cs st).length) :
    (cutPosts self t cs st)[k] = (cs.take (k + 1)).foldl (cutPost self t) st := by
  induction cs generalizing st k with
  | nil => simp [cutPosts_nil] at hk
  | cons c cs ih =>
    rw [List.getElem_of_eq (cutPosts_cons self t c cs st) hk]
    cases k with
    | zero => simp
    | succ k =>
      rw [cutPosts_cons, List.length_cons] at hk
      rw [List.getElem_cons_succ, ih _ _ (by omega), List.take_succ_cons, List.foldl_cons]

end

section

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (proposer : Nat → Fin sp.n)
  (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)

/-- The post-state of cut `k` of a group: the handler's `k`-th post-state. -/
theorem getElem_groupRecs_post (st : NodeState (goldilocksNode sp ro)) (t : Time) (id : Nat)
    (e : Event (goldilocksNode sp ro)) (k : Nat)
    (hk : k < (groupRecs proposer dg self st t id e).length) :
    (groupRecs proposer dg self st t id e)[k].post =
      (cutPosts self t (exec proposer dg self st t e).2 st)[k]'(by
        rw [length_cutPosts]; rwa [length_groupRecs] at hk) := by
  rw [List.getElem_of_eq (groupRecs_eq proposer dg self st t id e) hk, List.getElem_mapIdx,
    List.getElem_zip]

/-- A tick makes a cut (the AC's tick). -/
theorem exec_tick_ne_nil (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat) :
    (exec proposer dg self st t (.tick x)).2 ≠ [] := by
  simp [Node.exec, onTick, runSteps, tickSteps, Node.tickStep]

/-- A restart makes a cut (`ac_restart`). -/
theorem exec_restart_ne_nil (st : NodeState (goldilocksNode sp ro)) (t : Time) :
    (exec proposer dg self st t .restart).2 ≠ [] := by
  simp [Node.exec, Node.restart]

end

/-- The trace's state is unchanged over a block of cuts of other nodes. -/
theorem state_of_block_ne {y : Fin (S.params (pubOf E) hn).n} {j0 : Nat} (len : Nat)
    (hne : ∀ k < len, ∀ r, (allCuts S rho hn)[j0 + k]? = some r → r.node ≠ y) :
    (simTrace S rho hn).state y (j0 + len) = (simTrace S rho hn).state y j0 := by
  induction len with
  | zero => rfl
  | succ k ih =>
    change (simTrace S rho hn).state y (j0 + k).succ = _
    rw [Trace.state.eq_2, ite_eq_right, ih (fun k' hk' => hne k' (by omega))]
    rintro ⟨hnode, hlab⟩
    rw [simTrace_node] at hnode
    cases hr : (allCuts S rho hn)[j0 + k]? with
    | none => rw [simTrace_label, hr] at hlab; exact hlab rfl
    | some r =>
      rw [hr] at hnode
      exact hne k (by omega) r hr hnode

/-- The trace's state across a group block at `j0`: the handler's state, by the cut law's
successors. -/
theorem state_of_group
    (proposer : Nat → Fin (S.params (pubOf E) hn).n)
    (dg : Digest (List (FG.Att (S.params (pubOf E) hn).n)) (Payload (S.params (pubOf E) hn).n))
    {y : Fin (S.params (pubOf E) hn).n} {j0 : Nat}
    {st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _))} {t : Time} {id : Nat}
    {e : Event (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    (hcut : ∀ k < (groupRecs proposer dg y st t id e).length,
      (allCuts S rho hn)[j0 + k]? = (groupRecs proposer dg y st t id e)[k]?)
    (h0 : (simTrace S rho hn).state y j0 = st) :
    (simTrace S rho hn).state y (j0 + (groupRecs proposer dg y st t id e).length) =
      (exec proposer dg y st t e).1 := by
  have key : ∀ k ≤ (exec proposer dg y st t e).2.length,
      (simTrace S rho hn).state y (j0 + k) =
        ((exec proposer dg y st t e).2.take k).foldl (cutPost y t) st := by
    intro k
    induction k with
    | zero => intro _; simpa using h0
    | succ k ih =>
      intro hk
      have hk' : k < (groupRecs proposer dg y st t id e).length := by
        rw [length_groupRecs]; omega
      have hr := hcut k hk'
      rw [List.getElem?_eq_getElem hk'] at hr
      obtain ⟨hnode, -, -, -, -⟩ := getElem_groupRecs proposer dg y st t id e k hk'
      change (simTrace S rho hn).state y (j0 + k).succ = _
      rw [Trace.state.eq_2, ite_eq_left, simTrace_post, hr, Option.elim_some,
        getElem_groupRecs_post, cutPosts_getElem]
      rw [simTrace_node, hr, Option.elim_some, hnode, simTrace_label, hr]
      simp
  rw [length_groupRecs, key _ le_rfl, List.take_length, foldl_cutPost_exec]

/-- The trace's state across a delivery block at `j0`: `deliverState`. -/
theorem state_of_deliverRecs
    (proposer : Nat → Fin (S.params (pubOf E) hn).n)
    (dg : Digest (List (FG.Att (S.params (pubOf E) hn).n)) (Payload (S.params (pubOf E) hn).n))
    {y : Fin (S.params (pubOf E) hn).n} {t : Time} {i : Nat}
    (hs : List (Header Info × Nat)) (os : List (Wire (S.params (pubOf E) hn).n)) :
    ∀ (j0 sub : Nat) (st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _))),
    (∀ k < (deliverRecs proposer dg hs y t i os st sub).length,
      (allCuts S rho hn)[j0 + k]? = (deliverRecs proposer dg hs y t i os st sub)[k]?) →
    (simTrace S rho hn).state y j0 = st →
    (simTrace S rho hn).state y (j0 + (deliverRecs proposer dg hs y t i os st sub).length) =
      deliverState proposer dg hs y t os st := by
  induction os with
  | nil => intro j0 sub st _ h0; rw [deliverRecs_nil, List.length_nil, deliverState_nil]; exact h0
  | cons o os ih =>
    intro j0 sub st hcut h0
    cases he : canonEvent (S.params (pubOf E) hn) (S.ro _) hs o with
    | none =>
      rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ he] at hcut ⊢
      rw [deliverState_cons_none _ _ _ _ _ _ _ _ he]
      exact ih j0 (sub + 1) st hcut h0
    | some e =>
      rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ e he] at hcut ⊢
      rw [deliverState_cons_some _ _ _ _ _ _ _ _ _ he, List.length_append]
      have h1 : (simTrace S rho hn).state y
          (j0 + (groupRecs proposer dg y st t (Nat.pair i sub) e).length) =
            (exec proposer dg y st t e).1 :=
        state_of_group S rho hn proposer dg (fun k hk => by
          rw [hcut k (by rw [List.length_append]; omega), List.getElem?_append_left hk]) h0
      rw [← Nat.add_assoc]
      refine ih (j0 + (groupRecs proposer dg y st t (Nat.pair i sub) e).length) (sub + 1) _
        (fun k hk => ?_) h1
      rw [Nat.add_assoc, hcut _ (by rw [List.length_append]; omega),
        List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- The event id of an existing cut is its record's. -/
private theorem event_of_getElem? {k : Nat} {r : CutRec (S.params (pubOf E) hn) (S.ro _)}
    (hr : (allCuts S rho hn)[k]? = some r) : (simTrace S rho hn).event k = r.event := by
  rw [simTrace_event, hr]; rfl

/-- A cut with an event id of engine event `i` lies in the range of event `i`. -/
theorem range_of_event {i : Nat} (hi : i < rho.events.length) {k s : Nat}
    (h : (simTrace S rho hn).event k = Nat.pair i s) :
    cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) := by
  cases hr : (allCuts S rho hn)[k]? with
  | none =>
    rw [simTrace_event, hr, Option.elim_none, Nat.pair_eq_pair] at h
    omega
  | some r =>
    rw [event_of_getElem? S rho hn hr] at h
    obtain ⟨i', ev, he, h1, h2, h3⟩ := exists_event_of_getElem? S rho hn hr
    obtain ⟨-, -, s', hs'⟩ := mem_eventCuts S rho hn he (List.mem_of_getElem? h3)
    rw [hs', Nat.pair_eq_pair] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨h1, h2⟩

/-- A block of group cuts at `j0` whose event id is unique to the block is a group of the
trace; its length is the handler's cut count on the trace's state. -/
theorem groupAt_of_group
    (proposer : Nat → Fin (S.params (pubOf E) hn).n)
    (dg : Digest (List (FG.Att (S.params (pubOf E) hn).n)) (Payload (S.params (pubOf E) hn).n))
    {y : Fin (S.params (pubOf E) hn).n} {j0 : Nat}
    {st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _))} {t : Time} {id : Nat}
    {e : Event (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    (hcut : ∀ k < (groupRecs proposer dg y st t id e).length,
      (allCuts S rho hn)[j0 + k]? = (groupRecs proposer dg y st t id e)[k]?)
    (h0 : (simTrace S rho hn).state y j0 = st) (hne : (exec proposer dg y st t e).2 ≠ [])
    (huniq : ∀ k, (simTrace S rho hn).event k = id →
      j0 ≤ k ∧ k < j0 + (groupRecs proposer dg y st t id e).length) :
    (simTrace S rho hn).GroupAt proposer dg y j0 t e ∧
      (groupRecs proposer dg y st t id e).length =
        (exec proposer dg y ((simTrace S rho hn).state y j0) t e).2.length := by
  subst h0
  set st := (simTrace S rho hn).state y j0 with hst
  have hlen := length_groupRecs proposer dg y st t id e
  have hfact : ∀ k (hk : k < (exec proposer dg y st t e).2.length),
      (simTrace S rho hn).node (j0 + k) = y ∧ (simTrace S rho hn).time (j0 + k) = t ∧
        (simTrace S rho hn).event (j0 + k) = id ∧ (simTrace S rho hn).pos (j0 + k) = k ∧
        (simTrace S rho hn).label (j0 + k) = some (exec proposer dg y st t e).2[k] := by
    intro k hk
    have hk' : k < (groupRecs proposer dg y st t id e).length := by omega
    have hr := hcut k hk'
    rw [List.getElem?_eq_getElem hk'] at hr
    obtain ⟨h1, h2, h3, h4, h5⟩ := getElem_groupRecs proposer dg y st t id e k hk'
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [simTrace_node, hr, Option.elim_some, h1]
    · rw [simTrace_time, hr, Option.elim_some, h2]
    · rw [event_of_getElem? S rho hn hr, h3]
    · rw [simTrace_pos, hr, Option.elim_some, h4]
    · rw [simTrace_label, hr, Option.map_some, h5]
  have h0' : (simTrace S rho hn).event j0 = id := by
    have := (hfact 0 (List.length_pos_of_ne_nil hne)).2.2.1
    rwa [Nat.add_zero] at this
  refine ⟨⟨hne, ?_, ?_⟩, hlen⟩
  · intro k hk
    obtain ⟨h1, h2, h3, h4, h5⟩ := hfact k hk
    exact ⟨h1, h2, h3.trans h0'.symm, h4, h5⟩
  · intro k hk
    rw [← hlen]
    exact huniq k (hk.trans h0')

/-- A delivery block at `j0` whose sub-event ids from `sub` on are unique to the block is a
`DeliverSeq` of the trace. -/
theorem deliverSeq_of_recs
    (proposer : Nat → Fin (S.params (pubOf E) hn).n)
    (dg : Digest (List (FG.Att (S.params (pubOf E) hn).n)) (Payload (S.params (pubOf E) hn).n))
    {y : Fin (S.params (pubOf E) hn).n} {t : Time} {i : Nat}
    (hs : List (Header Info × Nat)) (os : List (Wire (S.params (pubOf E) hn).n)) :
    ∀ (j0 sub : Nat) (st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _))),
    (∀ k < (deliverRecs proposer dg hs y t i os st sub).length,
      (allCuts S rho hn)[j0 + k]? = (deliverRecs proposer dg hs y t i os st sub)[k]?) →
    (simTrace S rho hn).state y j0 = st →
    (∀ k s, (simTrace S rho hn).event k = Nat.pair i s → sub ≤ s →
      j0 ≤ k ∧ k < j0 + (deliverRecs proposer dg hs y t i os st sub).length) →
    DeliverSeq proposer (simTrace S rho hn) dg hs y t os j0
      (j0 + (deliverRecs proposer dg hs y t i os st sub).length) := by
  induction os with
  | nil =>
    intro j0 sub st _ _ _
    rw [deliverRecs_nil, List.length_nil, Nat.add_zero]
    exact .nil j0
  | cons o os ih =>
    intro j0 sub st hcut h0 huniq
    cases he : canonEvent (S.params (pubOf E) hn) (S.ro _) hs o with
    | none =>
      rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ he] at hcut huniq ⊢
      exact .drop he (ih j0 (sub + 1) st hcut h0 fun k s hk hs => huniq k s hk (by omega))
    | some e =>
      rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ e he] at hcut huniq ⊢
      rcases eq_or_ne (exec proposer dg y st t e).2 [] with hnil | hnil
      · have hg : groupRecs proposer dg y st t (Nat.pair i sub) e = [] :=
          List.length_eq_zero_iff.mp (by rw [length_groupRecs, hnil, List.length_nil])
        have hst : (exec proposer dg y st t e).1 = st := by
          have := foldl_cutPost_exec proposer dg y st t e
          rwa [hnil, List.foldl_nil, eq_comm] at this
        rw [hg, List.nil_append, hst] at hcut huniq ⊢
        exact .noCut e he (by rw [h0]; exact hnil)
          (ih j0 (sub + 1) st hcut h0 fun k s hk hs => huniq k s hk (by omega))
      · have hlen := length_groupRecs proposer dg y st t (Nat.pair i sub) e
        have hcutg : ∀ k < (groupRecs proposer dg y st t (Nat.pair i sub) e).length,
            (allCuts S rho hn)[j0 + k]? = (groupRecs proposer dg y st t (Nat.pair i sub) e)[k]? :=
          fun k hk => by
            rw [hcut k (by rw [List.length_append]; omega), List.getElem?_append_left hk]
        -- a cut with an id of the rest is past the group; one with the group's id is in it
        have hrest : ∀ k, (groupRecs proposer dg y st t (Nat.pair i sub) e).length ≤ k →
            k < (groupRecs proposer dg y st t (Nat.pair i sub) e).length +
              (deliverRecs proposer dg hs y t i os (exec proposer dg y st t e).1 (sub + 1)).length →
            ∃ s, sub + 1 ≤ s ∧ (simTrace S rho hn).event (j0 + k) = Nat.pair i s := by
          intro k hk1 hk2
          have hr := hcut k (by rw [List.length_append]; omega)
          have hlt : k - (groupRecs proposer dg y st t (Nat.pair i sub) e).length <
              (deliverRecs proposer dg hs y t i os
                (exec proposer dg y st t e).1 (sub + 1)).length := by omega
          rw [List.getElem?_append_right hk1, List.getElem?_eq_getElem hlt] at hr
          obtain ⟨-, -, s, hs1, hs2⟩ := mem_deliverRecs proposer dg y hs t i (List.getElem_mem hlt)
          exact ⟨s, hs1, by rw [event_of_getElem? S rho hn hr, hs2]⟩
        have hgrp : ∀ k < (groupRecs proposer dg y st t (Nat.pair i sub) e).length,
            (simTrace S rho hn).event (j0 + k) = Nat.pair i sub := by
          intro k hk
          have hr := hcutg k hk
          rw [List.getElem?_eq_getElem hk] at hr
          rw [event_of_getElem? S rho hn hr]
          exact (getElem_groupRecs proposer dg y st t (Nat.pair i sub) e k hk).2.2.1
        obtain ⟨hG, hGlen⟩ := groupAt_of_group S rho hn proposer dg hcutg h0 hnil fun k hk => by
          obtain ⟨h1, h2⟩ := huniq k sub hk le_rfl
          rw [List.length_append] at h2
          refine ⟨h1, ?_⟩
          by_contra h3
          obtain ⟨s, hs1, hs2⟩ := hrest (k - j0) (by omega) (by omega)
          rw [Nat.add_sub_cancel' h1, hk, Nat.pair_eq_pair] at hs2
          omega
        refine .event e he hG ?_
        rw [← hGlen, List.length_append, ← Nat.add_assoc]
        refine ih (j0 + (groupRecs proposer dg y st t (Nat.pair i sub) e).length) (sub + 1) _
          (fun k hk => ?_) (state_of_group S rho hn proposer dg hcutg h0) (fun k s hk hs => ?_)
        · rw [Nat.add_assoc, hcut _ (by rw [List.length_append]; omega),
            List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
        · obtain ⟨h1, h2⟩ := huniq k s hk (by omega)
          rw [List.length_append, ← Nat.add_assoc] at h2
          refine ⟨?_, h2⟩
          by_contra h3
          have := hgrp (k - j0) (by omega)
          rw [Nat.add_sub_cancel' h1, hk, Nat.pair_eq_pair] at this
          omega

end Consensus.Goldilocks.Simulation

end
