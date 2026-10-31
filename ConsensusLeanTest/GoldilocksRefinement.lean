module
public import ConsensusLean.Instances.Goldilocks.Statements.Refinement
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Trace
import all ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Shape
@[expose] public section

/-! # Witnesses for the Goldilocks refinement statements

Labelled by kind (CONTRIBUTING "Statements"):

* (a) `selValid_proposer`: in a run admitted by the engine (`SelValid`, part of
  `ExecutionValid`), the proposer role of every slot selects exactly the setup's proposer of
  that slot, the spec node's own `proposer`: the skeleton's per-slot `proposerSel` is the fixed
  singleton `{proposer s}` (for `n ≥ 1`). This is the schedule hypothesis `SelIs` of the earlier
  statements, now a consequence of validity rather than a premise.
* (b) `selValid_exists`: a valid selection exists (the schedule with everyone polling), so
  `SelValid` is satisfiable. -/

namespace Consensus.Goldilocks.Refinement.Test

open Shape
open Consensus.Model (pubOf SelSpec)

variable {V : Type} [Fintype V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- The skeleton's proposer selection at slot `s` is the singleton of the setup's proposer. -/
theorem skeleton_proposerSel (s : Nat) :
    (family S (pubOf E)).skel.proposerSel s =
      .fixed {(S.params (pubOf E) hn).toParams.proposer s} := by
  change SelSpec.fixed _ = _
  congr 1
  ext k
  constructor
  · intro hk
    exact Finset.mem_singleton.mpr (Fin.ext (Finset.mem_filter.mp hk).2)
  · intro hk
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, congrArg Fin.val (Finset.mem_singleton.mp hk)⟩

/-- In an admitted run, the proposer role of slot `s` selects exactly the setup's proposer. -/
theorem selValid_proposer (hsel : rho.SelValid) (s : Nat) :
    rho.sel (.proposer s) = {(S.params (pubOf E) hn).toParams.proposer s} := by
  have h := hsel (.proposer s)
  change ((family S (pubOf E)).skel.proposerSel s).Admits _ at h
  rw [skeleton_proposerSel S hn s] at h
  exact h

include hn in
/-- The schedule with everyone polling is an admissible selection. -/
theorem selValid_exists :
    ∃ sel : (Model.protoOf (compiled (family S)) E).Role → Finset (Fin (Fintype.card V)),
      (Model.protoOf (compiled (family S)) E).SelAdmits sel := by
  refine ⟨fun r => match r with
    | .proposer s => {(S.params (pubOf E) hn).toParams.proposer s}
    | .duty _ k => k.elim
    | .poll => Finset.univ, ?_⟩
  intro r
  cases r with
  | proposer s =>
    change ((family S (pubOf E)).skel.proposerSel s).Admits _
    rw [skeleton_proposerSel S hn s]
    rfl
  | duty _ k => exact k.elim
  | poll => rfl

variable [DecidableEq V]

/-- Exact-time release cannot be satisfied solely by a later send, even at the horizon. -/
theorem released_requires_same_time (v : V)
    (o : (Model.protoOf (compiled (family S)) E).Object) (τ : Time)
    (h : ReleasedFrom S rho v o τ) : rho.releases v o τ := h

/-- An admission at the horizon still requires a relay at that same time. -/
theorem relayed_at_horizon (v : V) (o : (Model.protoOf (compiled (family S)) E).Object)
    (h : RelayedFrom S rho v o rho.horizon) :
    ∃ cs, o ∈ cs ∧ rho.releases v (.mk .none (.data .relay) cs) rho.horizon := h

omit [DecidableEq V] in
/-- A canonical block carrying one vote runs the block handler first and then the actual
message handler on its resulting state. This holds whether the block handler accepts, refuses,
or silently drops the block: none of those outcomes skips the payload message. -/
theorem payload_message_after_block {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (hs : List (Blocks.Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat)
    (st : NodeState (goldilocksNode sp ro)) (B : Blk sp) (v : SA.Vote sp.n)
    (ha : B.fgPayload = []) (hp : B.acPayload = ([v], []))
    (hc : canonEvent sp ro hs (blockObj sp B) = some (.block B)) :
    deliverRecs dg hs self t i (delivered sp (blockObj sp B)) st 0 =
      groupRecs dg self st t (Nat.pair i 0) (.block B) ++
      groupRecs dg self (Node.onBlock self st t B).1 t (Nat.pair i 1) (.message v) := by
  have hd : delivered sp (blockObj sp B) = [blockObj sp B, voteObj v] := by
    simp [delivered, blockObj, payloadObjs, ha, hp, voteObj, Model.Obj.parts,
      Model.Obj.parts.partsList]
  rw [hd]
  simp [deliverRecs, hc, canonEvent_voteObj, Node.exec]

omit [DecidableEq V] in
/-- Two nested relay wrappers still execute the carried vote's message handler, with its
actual cuts and post-states, rather than dropping the inner wrapper's contents. -/
theorem nested_payload_message {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (hs : List (Blocks.Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat)
    (st : NodeState (goldilocksNode sp ro)) (v : SA.Vote sp.n) :
    deliverRecs dg hs self t i
      (delivered sp (.mk .none (.data .relay) [.mk .none (.data .relay) [voteObj v]])) st 0 =
      groupRecs dg self st t (Nat.pair i 2) (.message v) := by
  simp [delivered, Model.Obj.parts, Model.Obj.parts.partsList, deliverRecs,
    canonEvent, decodeBlock, decodeVoteObj, decodeAttObj, voteObj,
    decodeVote_encodeVote, Option.filter]

/-- Unsigned timestamps cannot certify forwarding freshness. -/
theorem unsigned_forward_rejected (sp : SA.SAParams) (hs : List (Blocks.Header Info × Nat))
    (t : Time) (cs : List (Wire sp.n)) :
    decodeForward sp hs (.mk .none (.data (.forward t)) cs) = none := by
  simp [decodeForward]

/-- A parent signed by a different origin cannot satisfy the forwarding chain. -/
theorem foreign_parent_rejected (sp : SA.SAParams) (hs : List (Blocks.Header Info × Nat))
    (x y : Fin sp.n) (hne : y ≠ x) (t pt : Time) (B A : Blk sp)
    (p : Wire sp.n) (pp : Option (Wire sp.n))
    (hb : decodeBlock sp hs (blockObj sp B) = some B)
    (hp : decodeForward sp hs p = some (y, pt, pp, A)) :
    decodeForward sp hs (forwardObj sp x t (some p) B) = none := by
  simp [forwardObj, decodeForward, hb, hp, hne]

/-- A negative claimed acceptance time is rejected even for a canonical genesis child. -/
theorem negative_forward_rejected (sp : SA.SAParams) (hs : List (Blocks.Header Info × Nat))
    (x : Fin sp.n) (t : Time) (ht : t < 0) (B : Blk sp)
    (hb : decodeBlock sp hs (blockObj sp B) = some B) :
    decodeForward sp hs (forwardObj sp x t none B) = none := by
  simp [forwardObj, decodeForward, hb, not_le.mpr ht]

/-- Carrying a parent in the current envelope is insufficient: the exact parent
must already be held. A different timestamped object does not substitute for it. -/
theorem forward_dependency_preheld :
    let parent : Wire 1 := .mk (.signed 0 .poll) (.data (.forward 1)) []
    let other : Wire 1 := .mk (.signed 0 .poll) (.data (.forward 2)) []
    let child : Wire 1 := .mk (.signed 0 .poll) (.data (.forward 3))
      [parent, .mk .none (.data .relay) []]
    (dependencies 1).ready [] child = false ∧
      (dependencies 1).ready [other] child = false ∧
      (dependencies 1).ready [parent] child = true := by
  decide

end Consensus.Goldilocks.Refinement.Test
