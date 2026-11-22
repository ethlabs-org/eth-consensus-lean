module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSchedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Unforgeable
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeDeliveryOrigin
import ConsensusLean.Lemmas.Model.Protection

public section

/-! # Sources of the payload objects of a called block

The payload provenance behind `block_payload_source_at` (`Growing/Simulation/Payload`). A payload
object of a block called at a public tick was in the
proposer's view before the tick; one of a delivered block was carried by the delivery. Only the
proposal closure at a tick (`hpre`) depends on the fault model; each supplies it. -/

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Blocks Shape Node

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
variable {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
variable {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
variable {hn : 1 ≤ Fintype.card V}
variable {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)}
variable (e : Encoding F E p hN hn A) (rho : Model.Run (compiled F) E)

/-- A carried object with an honest signer has a release before the containing call's event.
For own proposals, availability is required before the event, not just before its proposal duty. -/
theorem block_payload_source_of (hv : rho.ExecutionValid)
    {k : Nat} {y} {b : A.Blk} (hc : (simTrace e rho).BlockCallAt y k b)
    {w : ShapeObj (Fintype.card V) e.skel.Kind I e.Body}
    (hw : w ∈ e.codec.carried b.fgPayload b.acPayload)
    {u : V} (hu : u ∉ rho.faultyAt ((simTrace e rho).time k))
    (hsign : rho.signerOf (engineObj e w) = some u)
    (hpre : ∀ {i v t r acc}, rho.events[i]? = some (.tick v t) →
      r ∈ eventCuts e rho i → r.label = .fg (.block b acc) →
      engineObj e w ∈ Model.closure (rho.stateBefore i v).seen) :
    ∃ i t, cutMap e rho (i + 1) ≤ k ∧ rho.SendsAt u i t ∧ engineObj e w ∈ rho.releasesAt i := by
  rcases blockCall_origin e rho hc with
    ⟨i, v, t, r, he, hk, hr, ⟨acc, hl⟩, ht, _⟩ | ⟨i, v, o, t, w', he, hk, ht, hpart, hd⟩
  · have hi := (List.getElem?_eq_some_iff.mp he).1
    have hle := ((Model.sysOf_laws O (compiled F) V).trace ⟨E, rho⟩ hv).cutTime_mono i (i + 1)
      (Nat.le_succ i) (Nat.succ_le_of_lt hi)
    change rho.cutTime i ≤ rho.cutTime (i + 1) at hle
    simp only [Model.Run.cutTime, he] at hle
    rw [ht] at hu
    obtain ⟨j, hj, t', hs, hr'⟩ := rho.signed_seen_released hv hi.le (hpre he hr hl)
      (fun hf => hu (rho.faultyAt_mono hle hf)) hsign
    exact ⟨j, t', (cutMap_mono e rho (Nat.succ_le_of_lt hj)).trans hk, hs, hr'⟩
  · have hcar : engineObj e w ∈ (engineObj e w').carried := by
      have h {s q : ChainShape (Model.pubOf E) O.Id I} (hs : s = q) (x : (compile q).Object) :
          (cast (congrArg (fun z => (compile z).Object) hs.symm) x : (compile s).Object).carried =
            x.carried.map (cast (congrArg (fun z => (compile z).Object) hs.symm)) := by
        cases hs
        exact (List.map_id _).symm
      rw (config := { transparency := .default })
        [engineObj_eq, h e.shape_eq, carried_of_decodeBlock hd]
      rw [engineObj_eq]
      exact List.mem_map_of_mem (f := cast _) hw
    rw [ht] at hu
    obtain ⟨j, t', hj, hs, hr⟩ := hv.unforgeable i v o t he _
      (Model.Obj.Contains.trans hpart (.step hcar (.refl _))) u hsign hu
    exact ⟨j, t', (cutMap_mono e rho (Nat.succ_le_of_lt hj)).trans hk, hs, hr⟩

/-- Combine a carried object's release source with its attestation signing law. -/
theorem carried_att_sign_of_released {k : Nat} {a : FG.Att (Fintype.card V)}
    {o : (Model.protoOf (compiled F) E).Object}
    (hsource : ∃ i t, cutMap e rho (i + 1) ≤ k ∧ rho.SendsAt (rho.key a.val) i t ∧
      o ∈ rho.releasesAt i)
    (hrel : ∀ {j t}, rho.SendsAt (rho.key a.val) j t → o ∈ rho.releasesAt j →
      ∃ q < cutMap e rho (j + 1), (simTrace e rho).SignAt a.val q a) :
    ∃ q < k, (simTrace e rho).SignAt a.val q a := by
  obtain ⟨_, _, hik, hs, hr⟩ := hsource
  obtain ⟨q, hq, ha⟩ := hrel hs hr
  exact ⟨q, hq.trans_le hik, ha⟩

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **A payload object signed by a key honest at processing has an earlier genuine release.**
`hpre`: the objects a tick's proposal carries are in the proposer's view before the tick. -/
theorem block_payload_source_of (hv : rho.ExecutionValid)
    (hpre : ∀ {i : Nat} {v : V} {t : Time}, rho.events[i]? = some (.tick v t) →
      ∀ s (hs : 0 < s), (skeleton (pubOf E) S.vote).proposeAt t = [.propose s hs] →
      rho.ownKey v ∈ rho.sel (.proposer s) → ∀ par info cs,
      (propose (shapeOf S hn (preNode S rho v (rho.stateBefore i v) t)) s).2 =
        some (par, info, cs) →
      ∀ o ∈ cs, o ∈ Model.closure (preNode S rho v (rho.stateBefore i v) t).seen)
    {k : Nat} {y} {B : Blk (S.params (pubOf E) hn)} (hc : (simTrace S rho hn).BlockCallAt y k B)
    {o : Wire (Fintype.card V) S.vote} (ho : o ∈ payloadObjs B.fgPayload B.acPayload)
    {u : V} (hu : u ∉ rho.faultyAt ((simTrace S rho hn).time k))
    (hsign : rho.signerOf o = some u) :
    ∃ i t, cutMap S rho hn (i + 1) ≤ k ∧ rho.SendsAt u i t ∧ o ∈ rho.releasesAt i := by
  let enc := traceEncoding (E := E) S hn
  let w := NodeAsChainShape.CanonicalTrace.wireOf enc o
  have hobj := NodeAsChainShape.CanonicalTrace.engineObj_wireOf enc o
  have hmem : w ∈ enc.codec.carried B.fgPayload B.acPayload :=
    traceEncoding_induction S hn (fun e _ =>
      NodeAsChainShape.CanonicalTrace.wireOf e o ∈ e.codec.carried B.fgPayload B.acPayload)
      fun _ => by
        rw (config := { transparency := .default })
          [NodeAsChainShape.CanonicalTrace.wireOf_eq, cast_eq]
        exact ho
  rw [(simTrace_encoding S rho hn).1] at hc hu
  rw [(simTrace_encoding S rho hn).2]
  obtain ⟨i, t, hik, hs, hr⟩ := NodeAsChainShape.CanonicalTrace.block_payload_source_of enc rho hv
    hc hmem hu (by rwa [hobj]) (fun {i v t r acc} he hr hl => by
    rw [hobj]
    obtain ⟨q, hq, _, hql⟩ := eventCuts_label_pos S rho hn i r hr
    have hv' : v ∉ rho.faultyAt 0 := by
      have hm := List.mem_of_getElem? he
      exact fun hf => hv.honest_only _ hm (rho.faultyAt_mono (hv.in_horizon _ hm).1 hf)
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn i v t he hp] at hq
      simp at hq
    rw [eventCuts_tick_public S rho hn i v t he hp] at hq
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨_, _, _, _, hc⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
    have hcut := List.getElem_mem (lt_of_lt_of_eq hm (length_groupRecs _ _ _ _ _ _ _))
    rw [← hc, hql, hl] at hcut
    obtain ⟨N4, N5, Q, R4, F, G, _, _, _, _, _, _, _, hR4, hcar, _⟩ :=
      tick_public_analysis S rho hn hv hv' he hp (hpre he)
    have hB : blockObj (S.params (pubOf E) hn) B ∈ R4 := by
      rw [hR4]; exact mem_blockObjs.mpr ⟨B, acc, hcut, rfl⟩
    have ho' := hcar _ hB o ho
    have hnil := outbox_empty S rho hn hv v i
    have hrel : relHead S rho v
        (stateAt S rho hn v i).outbox.head? = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      obtain ⟨b, hb, _⟩ := mem_relHead S rho hx
      simp [hnil] at hb
    simpa only [hrel, List.append_nil] using ho')
  exact ⟨i, t, hik, hs, hobj ▸ hr⟩

end Consensus.Goldilocks.Simulation

end
