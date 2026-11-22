module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeDeliveryOrigin
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GenericRun
import ConsensusLean.Lemmas.Model.View
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts

public section

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Blocks Shape Node

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
variable {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
variable {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
variable {hn : 1 ≤ Fintype.card V}
variable {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)}
variable (e : Encoding F E p hN hn A) (rho : Model.Run (compiled F) E)

private theorem taggedRoot_ne_genesis (g x : Nat) : taggedRoot g x ≠ g := by
  simp only [taggedRoot]
  split <;> omega

private theorem rawRoot_of_tagged (g x : Nat) : rawRoot g (taggedRoot g x) = x := by
  simp only [rawRoot, taggedRoot]
  split <;> (try split) <;> omega

private theorem parentRoot_of_ref (g x : Nat) : parentRoot g (parentRef g (some x)) = some x := by
  by_cases h : x = g
  · simp [parentRoot, parentRef, h]
  · simp only [parentRoot, parentRef, ite_eq_right h, Option.some.injEq, rawRoot, taggedRoot]
    split <;> (try split) <;> omega

/-- In a trace whose occurring blocks have observed headers, no observed engine hash collision
and an injective header encoder give collision freedom on the occurring blocks and genesis. -/
theorem noCollRun_of_observed (tr : RunTrace A) (hnc : ¬ rho.HashCollision)
    (hinj : Function.Injective
      (fun x : List (FG.Att (Fintype.card V)) × A.Payload => e.codec.encode x.1 x.2))
    (hocc : ∀ b : A.Blk, tr.Occurs b →
      b.parent ≠ none ∧ rho.ObservedItem (headerOf e.codec.encode b)) :
    Compose.NoCollRun (digestOf e rho) tr := by
  intro b hb c hc hd
  simp only [digestOf_eq] at hd
  rcases hb with rfl | hb <;> rcases hc with rfl | hc
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp (hocc c hc).1
    exact False.elim (taggedRoot_ne_genesis _ _
      (by simpa [hx, Params.genesisBlock] using hd.symm))
  · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp (hocc b hb).1
    exact False.elim (taggedRoot_ne_genesis _ _
      (by simpa [hx, Params.genesisBlock] using hd))
  · obtain ⟨hpb, hob⟩ := hocc b hb
    obtain ⟨hpc, hoc⟩ := hocc c hc
    obtain ⟨pb, hpb⟩ := Option.ne_none_iff_exists'.mp hpb
    obtain ⟨pc, hpc⟩ := Option.ne_none_iff_exists'.mp hpc
    have hh : rho.hash (headerOf e.codec.encode b) = rho.hash (headerOf e.codec.encode c) := by
      have h := congrArg (rawRoot p.genesisRoot) hd
      simpa [headerOf, hpb, hpc, rawRoot_of_tagged] using h
    have he : headerOf e.codec.encode b = headerOf e.codec.encode c := by
      by_contra h
      exact hnc ⟨_, _, h, hob, hoc, hh⟩
    have hpar := congrArg (fun h => parentRoot p.genesisRoot h.parent) he
    simp only [headerOf, hpb, hpc, parentRoot_of_ref] at hpar
    have hpay : (b.fgPayload, b.acPayload) = (c.fgPayload, c.acPayload) :=
      hinj (congrArg Header.info he)
    exact ⟨by simpa [hpb, hpc] using hpar, congrArg Header.pos he, congrArg Header.input he,
      congrArg Prod.fst hpay, congrArg Prod.snd hpay⟩

/-- Every occurring block is in the engine view at its call; tick releases are a premise. -/
theorem block_call_in_view_of_releases
    (hcodec : ∀ {info atts payload}, e.codec.decode info = some (atts, payload) →
      e.codec.encode atts payload = info)
    (hrel : ∀ {j : Nat} {v : V} {t : Time}, rho.events[j]? = some (.tick v t) →
      (paramsAtCount p (Fintype.card V) hN hn).IsPublic t →
      ∀ r ∈ eventCuts e rho j, ∀ b acc, r.label = .fg (.block b acc) → r.pos ≠ 0 →
        engineObj e (blockObj e.codec.encode e.codec.carried b) ∈ rho.releasesAt j)
    {b : A.Blk} (hb : (simTrace e rho).Occurs b) :
    b.parent ≠ none ∧ ∃ i ev, rho.events[i]? = some ev ∧
      engineObj e (blockObj e.codec.encode e.codec.carried b) ∈ rho.ViewIdx ev.node (i + 1) := by
  obtain ⟨_, k, acc, _, hl⟩ := hb
  rw [simTrace_label] at hl
  cases hr : (allCuts e rho)[k]? with
  | none => simp [hr] at hl
  | some r =>
    rw [hr] at hl
    have hrl : r.label = .fg (.block b acc) := Option.some.inj hl
    rw [allCuts_eq] at hr
    obtain ⟨i, hi, _, hm⟩ := cut_event e rho _ _ _ hr
    cases he : rho.events[i] with
    | tick v t =>
      have het := (List.getElem?_eq_getElem hi).trans (congrArg some he)
      have hg := hm
      rw [eventCuts_tick e rho i v t het] at hg
      split at hg
      · rename_i hp
        rw [groupRecs_eq] at hg
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
        simp only [List.getElem_mapIdx, List.getElem_zip] at hrl hm ⊢
        obtain ⟨_, _, hparent, hnz⟩ := Compose.tick_block_cut_fields _ _ _ _ _ _
          ((List.getElem?_eq_getElem _).trans (congrArg some hrl))
        refine ⟨hparent, i, _, het, ?_⟩
        exact rho.mem_viewIdx_iff.2 ⟨i, _, by omega,
          Or.inl ⟨t, Or.inl het, hrel het hp _ hm _ _ hrl hnz⟩, .refl _⟩
      · cases hg
    | deliver v o t =>
      have het := (List.getElem?_eq_getElem hi).trans (congrArg some he)
      obtain ⟨w, _, hd⟩ := blockCall_delivered e rho het hm hrl
      have hpar : b.parent ≠ none := by
        unfold decodeBlock at hd
        split at hd
        · rename_i _ _ header _ _
          split at hd
          · simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hd
            obtain ⟨_, rfl⟩ := hd
            cases hp : header.parent <;> simp [blockOf, parentRoot, hp]
          · cases hd
        · cases hd
      exact ⟨hpar, i, _, het, rho.mem_viewIdx_iff.2
        ⟨i, o, by omega, Or.inr ⟨t, het⟩, blockObj_delivered e rho het hm hrl hcodec⟩⟩
    | restart v t =>
      have het := (List.getElem?_eq_getElem hi).trans (congrArg some he)
      rw [eventCuts_restart e rho i v t het, groupRecs_eq] at hm
      obtain ⟨j, _, rfl⟩ := List.getElem_of_mem hm
      simp [exec, Node.restart, acCall] at hrl

omit [DecidableEq V] in
private theorem item_cast {s q : ChainShape (Model.pubOf E) O.Id I} (h : s = q)
    (w : (compile s).Object) :
    (cast (congrArg (fun z => (compile z).Object) h) w).item? = w.item? := by
  cases h
  rfl

/-- An object in the reader's view at an actual event was observed while the reader was honest. -/
theorem observed_of_event_view (hv : rho.ExecutionValid)
    {i : Nat} {ev : Model.Event V (Model.protoOf (compiled F) E).Object}
    {o : (Model.protoOf (compiled F) E).Object} (he : rho.events[i]? = some ev)
    (hview : o ∈ rho.ViewIdx ev.node (i + 1)) : o ∈ rho.Observed := by
  have hi := (List.getElem?_eq_some_iff.mp he).1
  refine ⟨ev.node, i + 1, by omega, ?_, hview⟩
  change ev.node ∉ rho.faultyAt (rho.cutTime (i + 1))
  simpa only [Model.Run.cutTime, he, Option.elim_some] using
    hv.honest_only ev (List.mem_of_getElem? he)

/-- A block call's object is observed before any later compromise of its reader. -/
theorem occurs_blockObj_observed_at (hv : rho.ExecutionValid)
    (hcodec : ∀ {info atts payload}, e.codec.decode info = some (atts, payload) →
      e.codec.encode atts payload = info)
    (hrel : ∀ {j : Nat} {v : V} {t : Time}, rho.events[j]? = some (.tick v t) →
      (paramsAtCount p (Fintype.card V) hN hn).IsPublic t →
      ∀ r ∈ eventCuts e rho j, ∀ b acc, r.label = .fg (.block b acc) → r.pos ≠ 0 →
        engineObj e (blockObj e.codec.encode e.codec.carried b) ∈ rho.releasesAt j)
    {b : A.Blk} (hb : (simTraceAt e rho).Occurs b) :
    b.parent ≠ none ∧ engineObj e (blockObj e.codec.encode e.codec.carried b) ∈ rho.Observed := by
  rw [simTraceAt_eq] at hb
  obtain ⟨hp, i, ev, he, hview⟩ := block_call_in_view_of_releases e rho hcodec hrel hb
  exact ⟨hp, observed_of_event_view rho hv he hview⟩

/-- An occurring block has an engine header observed while its reader is honest. -/
theorem occurring_observed_at (hv : rho.ExecutionValid)
    (hcodec : ∀ {info atts payload}, e.codec.decode info = some (atts, payload) →
      e.codec.encode atts payload = info)
    (hrel : ∀ {j : Nat} {v : V} {t : Time}, rho.events[j]? = some (.tick v t) →
      (paramsAtCount p (Fintype.card V) hN hn).IsPublic t →
      ∀ r ∈ eventCuts e rho j, ∀ b acc, r.label = .fg (.block b acc) → r.pos ≠ 0 →
        engineObj e (blockObj e.codec.encode e.codec.carried b) ∈ rho.releasesAt j)
    {b : A.Blk} (hb : (simTraceAt e rho).Occurs b) :
    b.parent ≠ none ∧ rho.ObservedItem (headerOf e.codec.encode b) := by
  obtain ⟨hp, hobs⟩ := occurs_blockObj_observed_at e rho hv hcodec hrel hb
  refine ⟨hp, _, hobs, ?_⟩
  rw [engineObj_eq]
  exact (item_cast e.shape_eq.symm (blockObj e.codec.encode e.codec.carried b)).trans rfl

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace
