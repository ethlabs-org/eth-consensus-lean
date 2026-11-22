module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ReleaseTick
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeDeliveryOrigin

public section

/-! # Own cuts behind released and processed blocks and votes

A block or vote that an engine event releases genuinely comes from a cut of that event, and a
block or AC message processed while its signer is honest comes from an earlier own cut of the
signer. These arguments read only the engine run and its simulating trace. The fault model
enters through premises: the ticking node's honesty at time zero and its proposal's
releasability for a release, and the signer's release analysis for a processed object.
Constant faults (`RunSchedule`) and growing faults (`Growing/Simulation/Blocks`,
`Growing/Simulation/Votes`) supply them. -/

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Blocks Shape Node

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
variable {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
variable {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
variable {hn : 1 ≤ Fintype.card V}
variable {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)}
variable (e : Encoding F E p hN hn A) (rho : Model.Run (compiled F) E)

/-- A block call comes from an own proposal cut or from a decoded delivery part. -/
theorem blockCall_origin {y : Fin (Fintype.card V)} {k : Nat} {b : A.Blk}
    (hc : (simTrace e rho).BlockCallAt y k b) :
    (∃ i v t r, rho.events[i]? = some (.tick v t) ∧ cutMap e rho i ≤ k ∧
      r ∈ eventCuts e rho i ∧ (∃ acc, r.label = .fg (.block b acc)) ∧
      (simTrace e rho).time k = t ∧ (simTrace e rho).OwnBlockAt b.proposer k b) ∨
    ∃ i v o t w, rho.events[i]? = some (.deliver v o t) ∧ cutMap e rho i ≤ k ∧
      (simTrace e rho).time k = t ∧ engineObj e w ∈ o.parts ∧
      decodeBlock e.codec.decode e.codec.carried A.validPayload (Model.digests rho.hash o) w =
        some b := by
  obtain ⟨acc, hn', hl⟩ := hc
  obtain ⟨i, ev, r, he, hstart, hr, hlabel, ht, hnode, hpos, _, _⟩ := labelled_cut_origin e rho hl
  cases ev with
  | tick v t =>
    have hm := List.mem_of_getElem? hr
    rw [eventCuts_tick e rho i v t he] at hr
    split at hr
    · rw [groupRecs_eq, List.getElem?_eq_some_iff] at hr
      obtain ⟨h, rfl⟩ := hr
      have hl' := hlabel
      simp only [List.getElem_mapIdx, List.getElem_zip] at hlabel hpos
      obtain ⟨hp, _, _, hk⟩ := Compose.tick_block_cut_fields _ _ _ _ _ _
        ((List.getElem?_eq_getElem _).trans (congrArg some hlabel))
      exact Or.inl ⟨i, v, t, _, he, hstart, hm, ⟨acc, hl'⟩, ht,
        ⟨acc, hnode.trans hp.symm, hl⟩, hpos ▸ hk⟩
    · simp at hr
  | deliver v o t =>
    obtain ⟨w, hw, hd⟩ := blockCall_delivered e rho he (List.mem_of_getElem? hr) hlabel
    exact Or.inr ⟨i, v, o, t, w, he, hstart, ht, hw, hd⟩
  | restart v t =>
    rw [eventCuts_restart e rho i v t he, groupRecs_eq, List.getElem?_eq_some_iff] at hr
    obtain ⟨_, rfl⟩ := hr
    simp [exec, Node.restart, acCall] at hlabel

omit [DecidableEq V] in
private theorem engine_block_signer (b : A.Blk) :
    rho.signerOf (engineObj e (blockObj e.codec.encode e.codec.carried b)) =
      some (rho.key b.proposer) := by
  have h {s q : ChainShape (Model.pubOf E) O.Id I} (hs : s = q) (o : (compile q).Object) :
      (cast (congrArg (fun z => (compile z).Object) hs.symm) o : (compile s).Object).signer? =
        o.signer? := by cases hs; rfl
  rw (config := { transparency := .default }) [Model.Run.signerOf, engineObj_eq, h e.shape_eq]
  rfl

omit [DecidableEq V] in
private theorem decoded_canonical_block
    {o : (Model.protoOf (compiled F) E).Object}
    {w : ShapeObj (Fintype.card V) e.skel.Kind I e.Body} {b : A.Blk}
    (hw : engineObj e w ∈ o.parts)
    (hd : decodeBlock e.codec.decode e.codec.carried A.validPayload (Model.digests rho.hash o) w =
      some b)
    (hcodec : ∀ {info atts payload}, e.codec.decode info = some (atts, payload) →
      e.codec.encode atts payload = info) :
    w = blockObj e.codec.encode e.codec.carried b ∧ b.parent ≠ none ∧
      b.RootOk (digestOf e rho) := by
  refine ⟨(blockObj_of_decodeBlock hd hcodec).symm, ?_⟩
  unfold decodeBlock at hd
  split at hd
  · rename_i k s hdr cs
    split at hd
    · rename_i atts payload d hdec hroot
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hd
      obtain ⟨⟨hpos, rfl, _, _⟩, rfl⟩ := hd
      subst s
      have hh : hdr ∈ o.parts.filterMap Model.Obj.item? :=
        List.mem_filterMap.mpr ⟨_, hw, (engineObj_item e _).trans rfl⟩
      have hh' : rootOf (Model.digests rho.hash o) hdr = some (rho.hash hdr) :=
        Simulation.find?_map_pair rho.hash hdr _ hh
      rw [hh', Option.some.injEq] at hroot
      subst d
      obtain ⟨par, pos, input, info⟩ := hdr
      have href (g x : Nat) : parentRef g (some (taggedRoot g x)) = .digest x := by
        simp only [parentRef, taggedRoot, rawRoot]
        split_ifs <;> congr <;> omega
      cases par <;>
        simp [blockOf, Block.RootOk, digestOf_eq, hcodec hdec,
          parentRoot, href, show ∀ g, parentRef g (some g) = .root from fun g => by
            simp [parentRef]]
    · cases hd
  · cases hd

/-- An honest proposer's processed block is its own block, at or before processing. -/
theorem blockCall_ownBlock_of_released (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)}
    {k : Nat} {b : A.Blk} (hc : (simTrace e rho).BlockCallAt y k b)
    (hhon : rho.key b.proposer ∉ rho.faultyAt ((simTrace e rho).time k))
    (hcodec : ∀ {info atts payload}, e.codec.decode info = some (atts, payload) →
      e.codec.encode atts payload = info)
    (hrel : ∀ {j t}, rho.SendsAt (rho.key b.proposer) j t → b.parent ≠ none →
      b.RootOk (digestOf e rho) →
      engineObj e (blockObj e.codec.encode e.codec.carried b) ∈ rho.releasesAt j →
      ∃ q < cutMap e rho (j + 1), (simTrace e rho).OwnBlockAt b.proposer q b) :
    ∃ j ≤ k, (simTrace e rho).OwnBlockAt b.proposer j b := by
  rcases blockCall_origin e rho hc with
    ⟨_, _, _, _, _, _, _, _, _, hown⟩ | ⟨i, v, o, t, w, he, hk, ht, hw, hd⟩
  · exact ⟨k, le_rfl, hown⟩
  · obtain ⟨rfl, hp, hdg⟩ := decoded_canonical_block e rho hw hd hcodec
    rw [ht] at hhon
    obtain ⟨j, t', hj, hs, hb⟩ :=
      hv.unforgeable i v o t he _ hw _ (engine_block_signer e rho b) hhon
    obtain ⟨q, hq, hown⟩ := hrel hs hp hdg hb
    exact ⟨q, hq.le.trans ((cutMap_mono e rho (Nat.succ_le_of_lt hj)).trans hk), hown⟩

/-- A decoded message with an honest signer comes from an earlier emission by that signer. -/
theorem msgCall_emit_of_released (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} {k : Nat} {m : A.Msg} {signer : Fin (Fintype.card V)}
    {obj : (Model.protoOf (compiled F) E).Object}
    (hc : (simTraceAt e rho).MsgCallAt y k m)
    (hhon : rho.key signer ∉ rho.faultyAt ((simTraceAt e rho).time k))
    (hcodec : ∀ w, e.codec.message w = some m → engineObj e w = obj)
    (hsign : rho.signerOf obj = some (rho.key signer))
    (hrel : ∀ {j t}, rho.SendsAt (rho.key signer) j t → obj ∈ rho.releasesAt j →
      ∃ q < cutMap e rho (j + 1), (simTraceAt e rho).EmitAt signer q m) :
    ∃ j < k, (simTraceAt e rho).EmitAt signer j m := by
  obtain ⟨i, v, o, t, w, he, hw, hm, hstart, htime⟩ := simTraceAt_msgCall_delivered e rho hc
  rw [htime] at hhon
  rw [hcodec w hm] at hw
  obtain ⟨j, t', hj, hs, hb⟩ := hv.unforgeable i v o t he obj hw _ hsign hhon
  obtain ⟨q, hq, hem⟩ := hrel hs hb
  exact ⟨q, hq.trans_le ((cutMap_mono e rho (Nat.succ_le_of_lt hj)).trans hstart), hem⟩

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

private theorem tick_block_fields {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (self : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat)
    {B : Blk sp} {acc : Bool} {k : Nat}
    (hk : k < (exec proposer dg self st t (.tick x)).2.length)
    (hc : (exec proposer dg self st t (.tick x)).2[k] = .fg (.block B acc)) :
    B.proposer = self ∧ B.RootOk dg ∧ B.parent ≠ none ∧ k ≠ 0 :=
  Compose.tick_block_cut_fields (P := sp.toParams) (A := goldilocksNode sp ro)
    proposer dg self st t x ((List.getElem?_eq_getElem hk).trans (congrArg some hc))

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

/-- A block that an engine event releases genuinely is an own block of a tick cut of that
event. Premises: `hv'`, a ticking node is honest at time zero; `hpre`, its proposal carries
only objects it has seen (`preNode_releasable` for constant faults, `preNode_releasable_at`
for growing faults); `huniq`, `B` is the only rooted block with a parent that has its wire
object (`blockObj_fields`). -/
theorem released_block_cut_of (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {t : Time} (hs : rho.SendsAt v i t)
    (hv' : rho.events[i]? = some (.tick v t) → v ∉ rho.faultyAt 0)
    (hpre : rho.events[i]? = some (.tick v t) →
      ∀ s (hs : 0 < s), (skeleton (pubOf E) S.vote).proposeAt t = [.propose s hs] →
        rho.ownKey v ∈ rho.sel (.proposer s) → ∀ par info cs,
        (propose (shapeOf S hn (preNode S rho v (rho.stateBefore i v) t)) s).2 =
          some (par, info, cs) →
        ∀ o ∈ cs, o ∈ Model.closure (preNode S rho v (rho.stateBefore i v) t).seen)
    {B : Blk (S.params (pubOf E) hn)}
    (huniq : ∀ C : Blk (S.params (pubOf E) hn), C.parent ≠ none →
      C.RootOk (digestOf S rho) →
      blockObj (S.params (pubOf E) hn) (binding := S.vote) B =
        blockObj (S.params (pubOf E) hn) C → B = C)
    (hb : blockObj (S.params (pubOf E) hn) B ∈ rho.releasesAt i) :
    ∃ k < cutMap S rho hn (i + 1), (simTrace S rho hn).OwnBlockAt B.proposer k B := by
  have hhead : ∀ ob,
      blockObj (S.params (pubOf E) hn) B ∉ relHead S rho v ob := by
    intro ob h
    obtain ⟨q, _, heq⟩ := mem_relHead S rho h
    have hh := congrArg Model.Obj.msg heq
    cases hh
  rcases hs with he | ⟨o, he⟩
  · by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
    · obtain ⟨N4, N5, Q, R4, F, G, hr, _, _, hF, hG, _, _, hR4, _⟩ :=
        tick_public_analysis S rho hn hv (hv' he) he hp (hpre he)
      rw [hr] at hb
      have hb4 : blockObj (S.params (pubOf E) hn) B ∈ R4 := by
        rcases List.mem_append.mp hb with hb | hb
        · rcases List.mem_append.mp hb with hb | hb
          · rcases List.mem_append.mp hb with hb | hb
            · rcases List.mem_append.mp hb with hb | hb
              · exact False.elim (hhead _ hb)
              · exact hb
            · rcases List.mem_append.mp hb with hb | hb
              · exact False.elim (hhead _ hb)
              · rcases hF _ hb with ⟨τ, cs, heq⟩ | ⟨τ, m, heq⟩
                all_goals have hh := congrArg Model.Obj.msg heq; cases hh
          · exact False.elim (hhead _ hb)
        · have hh := hG _ hb
          cases hh
      rw [hR4] at hb4
      obtain ⟨C, acc, hc, hb⟩ := mem_blockObjs.mp hb4
      obtain ⟨m, hm, hcm⟩ := List.getElem_of_mem hc
      obtain ⟨_, hrC, hpC, _⟩ := tick_block_fields _ _ _ _ _ _ hm hcm
      have hBC := huniq C hpC hrC hb
      subst C
      exact ownBlock_of_tick_cut S rho hn he hp hc
    · rcases tick_other_releases S rho hn hv (hv' he) he hp _ hb with h | h
      · exact False.elim (hhead _ h)
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

/-- A block that a node processes at cut `k`, while its proposer is honest at the cut's time,
is the proposer's own block at or before `k`. Premise `hrel`: a release of the block's wire
object at an engine event of the proposer comes from an own block cut of that event
(`released_block_cut_of`, with the fault model's premises). -/
theorem blockCall_ownBlock_of_released (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)}
    {k : Nat} {B : Blk (S.params (pubOf E) hn)} (hc : (simTrace S rho hn).BlockCallAt y k B)
    (hhon : rho.key B.proposer ∉ rho.faultyAt ((simTrace S rho hn).time k))
    (hrel : ∀ {j t}, rho.SendsAt (rho.key B.proposer) j t → B.parent ≠ none →
      B.RootOk (digestOf S rho) → blockObj (S.params (pubOf E) hn) B ∈ rho.releasesAt j →
      ∃ q < cutMap S rho hn (j + 1), (simTrace S rho hn).OwnBlockAt B.proposer q B) :
    ∃ j ≤ k, (simTrace S rho hn).OwnBlockAt B.proposer j B := by
  let enc := traceEncoding (E := E) S hn
  rw [(simTrace_encoding S rho hn).1] at hc hhon hrel ⊢
  rw [(simTrace_encoding S rho hn).2, (runProposer_digestOf S rho hn).2] at hrel
  obtain ⟨hobj, hcodec⟩ := blockView_encoding (E := E) S hn
  exact NodeAsChainShape.CanonicalTrace.blockCall_ownBlock_of_released enc rho hv hc hhon hcodec
    (fun hs hp hd hb => hrel hs hp hd (hobj B ▸ hb))

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

/-- A vote that an engine event releases genuinely comes from an emission of that event
before its end cut. Premises `hv'` and `hpre` as for `released_block_cut_of`. -/
theorem released_vote_cut_of (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {t : Time} (hs : rho.SendsAt v i t)
    (hv' : rho.events[i]? = some (.tick v t) → v ∉ rho.faultyAt 0)
    (hpre : rho.events[i]? = some (.tick v t) →
      ∀ s (hs : 0 < s), (skeleton (pubOf E) S.vote).proposeAt t = [.propose s hs] →
        rho.ownKey v ∈ rho.sel (.proposer s) → ∀ par info cs,
        (propose (shapeOf S hn (preNode S rho v (rho.stateBefore i v) t)) s).2 =
          some (par, info, cs) →
        ∀ o ∈ cs, o ∈ Model.closure (preNode S rho v (rho.stateBefore i v) t).seen)
    {m : Vote (Fintype.card V)} (hb : voteObj m ∈ rho.releasesAt i) :
    ∃ k < cutMap S rho hn (i + 1), (simTrace S rho hn).EmitAt (rho.ownKey v) k m := by
  have hbody : ∀ b, voteObj m = pollObj S rho v b → b = Body.vote (encodeVote m) := by
    intro b heq
    exact (Model.Msg.data.inj (congrArg Model.Obj.msg heq)).symm
  rcases hs with he | ⟨o, he⟩
  · have hnil := outbox_empty S rho hn hv v i
    by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
    · obtain ⟨N4, N5, Q, R4, F, G, hr, _, _, hF, hG, _, hQ, hR4, _⟩ :=
        tick_public_analysis S rho hn hv (hv' he) he hp (hpre he)
      have hq : ∀ ob, (∀ b, ob = some b → b ∈ Q) →
          voteObj m ∈ relHead S rho v ob →
          ∃ k < cutMap S rho hn (i + 1), (simTrace S rho hn).EmitAt (rho.ownKey v) k m := by
        intro ob hmem hb
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
              simp [hnil] at hb
            · rw [hR4] at hb
              obtain ⟨B, acc, _, heq⟩ := mem_blockObjs.mp hb
              have hh := congrArg Model.Obj.msg heq
              cases hh
          · rcases List.mem_append.mp hb with hb | hb
            · exact hq _ (fun _ h => List.mem_of_mem_head? h) hb
            · rcases hF _ hb with ⟨τ, cs, heq⟩ | ⟨τ, m, heq⟩
              all_goals have hh := congrArg Model.Obj.msg heq; cases hh
        · exact hq _ (fun _ h => List.mem_of_mem_tail (List.mem_of_mem_head? h)) hb
      · have hh := hG _ hb; cases hh
    · rcases tick_other_releases S rho hn hv (hv' he) he hp _ hb with hb | hb
      · obtain ⟨b, hb, _⟩ := mem_relHead S rho hb
        simp [hnil] at hb
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

/-- **A received AC message was delivered**: the cut `k` of a message call is a cut of a
delivery event `i` at the cut's time, whose delivered object contains the vote. -/
theorem msgCall_delivered {y : Fin (Fintype.card V)} {k : Nat} {m : Vote (Fintype.card V)}
    (hc : (simTrace S rho hn).MsgCallAt y k m) :
    ∃ i v o t, rho.events[i]? = some (.deliver v o t) ∧ Model.Obj.Contains o (voteObj m) ∧
      cutMap S rho hn i ≤ k ∧ (simTrace S rho hn).time k = t := by
  let enc := traceEncoding (E := E) S hn
  rw [(simTrace_encoding S rho hn).1] at hc ⊢
  rw [(simTrace_encoding S rho hn).2]
  obtain ⟨i, v, o, t, w, he, hw, hm, hstart, htime⟩ :=
    NodeAsChainShape.CanonicalTrace.simTraceAt_msgCall_delivered enc rho
      (by rwa [NodeAsChainShape.CanonicalTrace.simTraceAt_eq])
  have hobj : ∀ w, enc.codec.message w = some m →
      NodeAsChainShape.CanonicalTrace.engineObj enc w = voteObj (binding := S.vote) m :=
    traceEncoding_induction S hn (fun e _ => ∀ w, e.codec.message w = some m →
      NodeAsChainShape.CanonicalTrace.engineObj e w = voteObj (binding := S.vote) m) fun _ w h => by
        have hwire := eq_voteObj_of_decodeVoteObj h
        subst w
        rw (config := { transparency := .default })
          [NodeAsChainShape.CanonicalTrace.engineObj_eq, cast_eq]
  rw [hobj w hm] at hw
  rw [NodeAsChainShape.CanonicalTrace.simTraceAt_eq] at htime
  exact ⟨i, v, o, t, he, hw, hstart, htime⟩

/-- An AC message that a node receives at cut `k`, while its signer is honest at the cut's
time, was emitted by the signer at an earlier cut. Premise `hrel`: a release of the vote at an
engine event of the signer comes from an own emission cut of that event
(`released_vote_cut_of`, with the fault model's premises). -/
theorem msgCall_emit_of_released (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)}
    {k : Nat} {m : Vote (Fintype.card V)} (hc : (simTrace S rho hn).MsgCallAt y k m)
    (hhon : rho.key m.val ∉ rho.faultyAt ((simTrace S rho hn).time k))
    (hrel : ∀ {j t}, rho.SendsAt (rho.key m.val) j t → voteObj m ∈ rho.releasesAt j →
      ∃ q < cutMap S rho hn (j + 1), (simTrace S rho hn).EmitAt m.val q m) :
    ∃ j < k, (simTrace S rho hn).EmitAt m.val j m := by
  let enc := traceEncoding (E := E) S hn
  rw [(simTrace_encoding S rho hn).1] at hc hhon hrel ⊢
  rw [(simTrace_encoding S rho hn).2] at hrel
  simp only [← NodeAsChainShape.CanonicalTrace.simTraceAt_eq] at hc hhon hrel ⊢
  refine NodeAsChainShape.CanonicalTrace.msgCall_emit_of_released enc rho hv hc hhon ?_ rfl hrel
  exact traceEncoding_induction S hn
    (fun e _ => ∀ w, e.codec.message w = some m →
      NodeAsChainShape.CanonicalTrace.engineObj e w = voteObj (binding := S.vote) m)
    fun _ w hw => by
      obtain rfl := eq_voteObj_of_decodeVoteObj hw
      rw (config := { transparency := .default })
        [NodeAsChainShape.CanonicalTrace.engineObj_eq, cast_eq]

end Consensus.Goldilocks.Simulation
