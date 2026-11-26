module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ReleaseTick
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeDeliveryOrigin

public section

/-! # Own signing cuts behind processed attestations

An attestation processed while its signer is honest was signed by the signer at an earlier
cut. The argument reads only the engine run and its simulating trace; the fault model enters
through the signer's release analysis. Constant faults (`RunBlocks`) and growing faults
(`Growing/Simulation/Attestations`) supply it. -/

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Blocks Shape Node

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
variable {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
variable {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
variable {hn : 1 ≤ Fintype.card V}
variable {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)}
variable (e : Encoding F E p hN hn A) (rho : Model.Run (compiled F) E)

omit [DecidableEq I] [Countable I] in
private theorem length_cutPosts' {Q : Params} {N : NodeAC Q} (self : Fin Q.n) (t : Time) :
    ∀ (cs : List (Cut N)) (st : NodeState N), (cutPosts self t cs st).length = cs.length
  | [], st => by rw [cutPosts_nil]; rfl
  | c :: cs, st => by
    rw [cutPosts_cons, List.length_cons, List.length_cons, length_cutPosts' self t cs]

omit [DecidableEq I] [Countable I] in
private theorem length_groupRecs' {Q : Params} {N : NodeAC Q} {pr : Nat → Fin Q.n}
    {dg : Digest (List (FG.Att Q.n)) N.Payload} {y : Fin Q.n} {st : NodeState N} {t : Time}
    {i : Nat} {ev : Node.Event N} :
    (groupRecs pr dg y st t i ev).length = (exec pr dg y st t ev).2.length := by
  rw [groupRecs_eq]
  simp only [List.length_mapIdx, List.length_zip, length_cutPosts', Nat.min_self]

/-- A processed attestation was signed earlier: locally in the tick, or by the releaser of
the decoded attestation received by the node. -/
theorem attCall_sign_of_released (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)}
    {k : Nat} {a : FG.Att (Fintype.card V)} (hc : (simTrace e rho).AttCallAt y k a)
    (hhon : rho.key a.val ∉ rho.faultyAt ((simTrace e rho).time k))
    {obj : (Model.protoOf (compiled F) E).Object}
    (hcodec : ∀ w, e.codec.attestation w = some a → engineObj e w = obj)
    (hsign : rho.signerOf obj = some (rho.key a.val))
    (hrel : ∀ {j t}, rho.SendsAt (rho.key a.val) j t → obj ∈ rho.releasesAt j →
      ∃ q < cutMap e rho (j + 1), (simTrace e rho).SignAt a.val q a)
    (hadm : ∀ {j w t}, rho.events[j]? = some (.tick w t) → a ∈ admitsAt e rho w j →
      (∃ q < cutMap e rho j, (simTrace e rho).SignAt a.val q a) ∨
        ((paramsAtCount p (Fintype.card V) hN hn).IsPublic t ∧ ∃ C,
          Cut.fg (.attest C (some a)) ∈ (exec (runProposer rho hn) (digestOf e rho)
            (rho.ownKey w) (e.adapter.node (stateAt e rho w j)) t
            (.tick (encodeTxs (Model.mempool rho.inbox w t))
              (e.adapter.sign (rho.ownKey w) t))).2)) :
    ∃ j < k, (simTrace e rho).SignAt a.val j a := by
  obtain ⟨_, hl⟩ := hc
  obtain ⟨i, ev, r, he, hstart, hr, hlabel, ht, _, _, _, _⟩ := labelled_cut_origin e rho hl
  cases ev with
  | tick v t =>
    rcases mem_eventCuts_tick e rho he (List.mem_of_getElem? hr) with
      ⟨-, hg⟩ | ⟨a', ha', st, s, -, hg⟩
    · exact (Compose.tick_no_attestation _ _ _ _ _ _ _ _
        (hlabel ▸ (mem_groupRecs_fields _ _ _ _ _ _ _ hg).1)).elim
    have hl' := (mem_groupRecs_fields _ _ _ _ _ _ _ hg).1
    rw [hlabel] at hl'
    obtain rfl : a = a' := by simpa [exec, onAttestation] using hl'
    rcases hadm he ha' with ⟨q, hq, hsig⟩ | ⟨hp, C, hC⟩
    · exact ⟨q, hq.trans_le hstart, hsig⟩
    obtain ⟨G, hG⟩ : ∃ G, G = groupRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
        (e.adapter.node (stateAt e rho v i)) t (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t)) (e.adapter.sign (rho.ownKey v) t)) :=
      ⟨_, rfl⟩
    have hEj : eventCuts e rho i = G ++
        admitRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v) t i (admitsAt e rho v i)
          (postTick e rho e.adapter.sign v i t) 1 := by
      rw [eventCuts_tick e rho i v t he, ite_eq_left hp, hG]
    obtain ⟨m, hm, hCm⟩ := List.getElem_of_mem hC
    have hmG : m < G.length := by rw [hG, length_groupRecs']; exact hm
    have hend : cutMap e rho i + G.length ≤ k := by
      refine Nat.le_of_not_lt fun hlt => ?_
      rw [hEj, List.getElem?_append_left (by omega)] at hr
      exact Compose.tick_no_attestation _ _ _ _ _ _ _ _
        (hlabel ▸ (mem_groupRecs_fields _ _ _ _ _ _ _ (hG ▸ List.mem_of_getElem? hr)).1)
    have hval : a.val = rho.ownKey v := Simulation.attest_val_of_mem_node_exec
      (A := A) (C := C) (a := a) (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
      (e.adapter.node (stateAt e rho v i)) t
      (.tick (encodeTxs (Model.mempool rho.inbox v t)) (e.adapter.sign (rho.ownKey v) t)) hC
    have hrec := allCuts_getElem?_add e rho i m (List.getElem?_eq_some_iff.mp he).1
      (by rw [hEj, List.length_append]; omega)
    rw [hEj, List.getElem?_append_left hmG, List.getElem?_eq_getElem hmG] at hrec
    subst hG
    refine ⟨cutMap e rho i + m, by omega, C, ?_, ?_⟩
    · rw [simTrace_node, hrec, hval]
      simp only [Option.elim_some, groupRecs_eq, List.getElem_mapIdx]
    · rw [simTrace_label, hrec]
      simp only [Option.map_some, groupRecs_eq, List.getElem_mapIdx, List.getElem_zip,
        Option.some.injEq]
      exact hCm
  | deliver v o t =>
    obtain ⟨w, ev, st, hw, hcanon, hcut⟩ := delivery_origin e rho he (List.mem_of_getElem? hr)
    rw [hlabel] at hcut
    have heq : ev = .attestation a := by
      cases ev with
      | tick => unfold canonEvent at hcanon; split at hcanon <;> cases hcanon
      | restart => simp [exec, Node.restart, acCall] at hcut
      | message => simp [exec, onMessage, acCall] at hcut
      | block =>
        simp only [exec, onBlock] at hcut
        split at hcut
        · cases hcut
        · split at hcut <;> simp [acCall] at hcut
      | attestation a' => simpa [exec, onAttestation, eq_comm] using hcut
    subst ev
    have ha : e.codec.attestation w = some a := by
      unfold canonEvent at hcanon
      split at hcanon <;> cases hcanon
      rename_i h
      rwa [receiverCodec_eq] at h
    rw [hcodec w ha] at hw
    rw [ht] at hhon
    obtain ⟨j, t', hj, hs, hb⟩ := hv.unforgeable i v o t he obj hw _ hsign hhon
    obtain ⟨q, hq, hsig⟩ := hrel hs hb
    exact ⟨q, hq.trans_le ((cutMap_mono e rho (Nat.succ_le_of_lt hj)).trans hstart), hsig⟩
  | restart v t =>
    rw [eventCuts_restart e rho i v t he, groupRecs_eq, List.getElem?_eq_some_iff] at hr
    obtain ⟨_, rfl⟩ := hr
    simp [exec, Node.restart, acCall] at hlabel

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- An attestation that a node processes at cut `k`, while its signer is honest at the cut's
time, was signed by the signer at an earlier cut. Premise `hrel`: a release of the attestation
at an engine event of the signer comes from an own signing cut of that event
(`released_att_cut_at`). -/
theorem attCall_sign_of_released (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)}
    {k : Nat} {a : FG.Att (Fintype.card V)} (hc : (simTrace S rho hn).AttCallAt y k a)
    (hhon : rho.key a.val ∉ rho.faultyAt ((simTrace S rho hn).time k))
    (hrel : ∀ {j t}, rho.SendsAt (rho.key a.val) j t → attObj a ∈ rho.releasesAt j →
      ∃ q < cutMap S rho hn (j + 1), (simTrace S rho hn).SignAt a.val q a)
    (hadm : ∀ {j w t}, rho.events[j]? = some (.tick w t) → a ∈ admitsAt S rho hn w j →
      (∃ q < cutMap S rho hn j, (simTrace S rho hn).SignAt a.val q a) ∨
        ((S.params (pubOf E) hn).toParams.IsPublic t ∧ ∃ C,
          Cut.fg (.attest C (some a)) ∈ (exec (runProposer S rho hn) (digestOf S rho)
            (rho.ownKey w) (stateAt S rho hn w j).node t
            (.tick (encodeTxs (Model.mempool rho.inbox w t))
              (S.sign (pubOf E) (rho.ownKey w) t))).2)) :
    ∃ j < k, (simTrace S rho hn).SignAt a.val j a := by
  let enc := traceEncoding (E := E) S hn
  obtain ⟨hpr, hdg⟩ := runProposer_digestOf S rho hn
  have hstate : ∀ v i, (stateAt S rho hn v i).node =
      (traceEncoding S hn).adapter.node
        (NodeAsChainShape.CanonicalTrace.stateAt (traceEncoding S hn) rho v i) := fun v i => by
    rw [stateAt_eq]
    exact traceEncoding_induction S hn (fun e _ _ =>
      ((rho.stateBefore i v).st.1 hn).node =
        e.adapter.node (NodeAsChainShape.CanonicalTrace.stateAt e rho v i)) fun _ => by
      rw (config := { transparency := .default })
        [NodeAsChainShape.CanonicalTrace.stateAt_eq, cast_eq]
      rfl
  rw [(simTrace_encoding S rho hn).1] at hc hhon hrel hadm ⊢
  rw [(simTrace_encoding S rho hn).2] at hrel hadm
  refine NodeAsChainShape.CanonicalTrace.attCall_sign_of_released enc rho hv hc hhon ?_ rfl hrel
    fun {j w t} hw ha => ?_
  · exact traceEncoding_induction S hn (fun e _ _ => ∀ w, e.codec.attestation w = some a →
      NodeAsChainShape.CanonicalTrace.engineObj e w = attObj (binding := S.vote) a) fun _ w hw => by
      obtain rfl := eq_attObj_of_decodeAttObj hw
      rw (config := { transparency := .default })
        [NodeAsChainShape.CanonicalTrace.engineObj_eq, cast_eq]
  rw [NodeAsChainShape.CanonicalTrace.admitsAt_eq, ← hstate, ← hstate, ← admitsAt_eq] at ha
  rcases hadm hw ha with h | ⟨hp, C, hC⟩
  · exact Or.inl h
  · rw [hpr, hdg, hstate, ← traceEncoding_adapter_sign S hn] at hC
    exact Or.inr ⟨hp, C, hC⟩

end Consensus.Goldilocks.Simulation
