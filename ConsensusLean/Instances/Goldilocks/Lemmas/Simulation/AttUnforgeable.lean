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

/-- A processed attestation was signed earlier: locally in the tick, or by the releaser of
the decoded attestation received by the node. -/
theorem attCall_sign_of_released (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)}
    {k : Nat} {a : FG.Att (Fintype.card V)} (hc : (simTrace e rho).AttCallAt y k a)
    (hhon : rho.key a.val ∉ rho.faultyAt ((simTrace e rho).time k))
    {obj : (Model.protoOf (compiled F) E).Object}
    (hcodec : ∀ w, e.codec.attestation w = some a → engineObj e w = obj)
    (hsign : rho.signerOf obj = some (rho.key a.val))
    (hrel : ∀ {j t}, rho.SendsAt (rho.key a.val) j t → obj ∈ rho.releasesAt j →
      ∃ q < cutMap e rho (j + 1), (simTrace e rho).SignAt a.val q a) :
    ∃ j < k, (simTrace e rho).SignAt a.val j a := by
  obtain ⟨_, hl⟩ := hc
  obtain ⟨i, ev, r, he, hstart, hr, hlabel, ht, _, _, _, _⟩ := labelled_cut_origin e rho hl
  cases ev with
  | tick v t =>
    have hi := (List.getElem?_eq_some_iff.mp he).1
    rw [eventCuts_tick e rho i v t he] at hr
    split at hr
    · rename_i hp
      rw [groupRecs_eq, List.getElem?_eq_some_iff] at hr
      obtain ⟨hm, rfl⟩ := hr
      simp only [List.getElem_mapIdx, List.getElem_zip] at hlabel
      obtain ⟨q, hq, C, hC⟩ := Compose.tick_attestation_prev _ _ _ _ _ _
        ((List.getElem?_eq_getElem _).trans (congrArg some hlabel))
      have hval : a.val = rho.ownKey v := Simulation.attest_val_of_mem_node_exec
        (A := A) (C := C) (a := a)
        (runProposer rho hn) (digestOf e rho) (rho.ownKey v) (e.adapter.node (stateAt e rho v i)) t
        (.tick (encodeTxs (Model.mempool rho.inbox v t))) (List.mem_of_getElem? hC)
      have hq' : q < (eventCuts e rho i).length := by
        rw [eventCuts_tick e rho i v t he, ite_eq_left hp, groupRecs_eq]
        simp only [List.length_mapIdx, List.length_zip, Nat.lt_min] at hm ⊢
        exact ⟨hq.trans hm.1, hq.trans hm.2⟩
      have hgroup := eventCuts_tick e rho i v t he
      rw [ite_eq_left hp, groupRecs_eq] at hgroup
      have hrec := allCuts_getElem?_add e rho i q hi hq'
      have hq'' := hq'
      rw [hgroup] at hq''
      rw [hgroup] at hrec
      rw [List.getElem?_eq_getElem hq''] at hrec
      refine ⟨cutMap e rho i + q, by omega, C, ?_, ?_⟩
      · rw [simTrace_node, hrec, hval]
        simp only [Option.elim_some, List.getElem_mapIdx]
      · rw [simTrace_label, hrec]
        simp only [Option.map_some, List.getElem_mapIdx, List.getElem_zip, Option.some.injEq]
        exact (List.getElem?_eq_some_iff.mp hC).2
    · simp at hr
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
      assumption
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
      ∃ q < cutMap S rho hn (j + 1), (simTrace S rho hn).SignAt a.val q a) :
    ∃ j < k, (simTrace S rho hn).SignAt a.val j a := by
  let enc := traceEncoding (E := E) S hn
  rw [(simTrace_encoding S rho hn).1] at hc hhon hrel ⊢
  rw [(simTrace_encoding S rho hn).2] at hrel
  refine NodeAsChainShape.CanonicalTrace.attCall_sign_of_released enc rho hv hc hhon ?_ rfl hrel
  exact traceEncoding_induction S hn (fun e _ => ∀ w, e.codec.attestation w = some a →
    NodeAsChainShape.CanonicalTrace.engineObj e w = attObj (binding := S.vote) a) fun _ w hw => by
    obtain rfl := eq_attObj_of_decodeAttObj hw
    rw (config := { transparency := .default })
      [NodeAsChainShape.CanonicalTrace.engineObj_eq, cast_eq]

end Consensus.Goldilocks.Simulation
