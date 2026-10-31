module
public import ConsensusLean.Instances.Goldilocks.Statements.Refinement
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Trace
import all ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Shape
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Run
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Sleepy
public import ConsensusLean.Proofs.RegimesRealizable.Main
@[expose] public section

/-! # Witnesses for the Goldilocks refinement statements

Labelled by kind (CONTRIBUTING "Statements"):

* (a) `selValid_proposer`: in a run admitted by the engine (`SelValid`, part of
  `ExecutionValid`), each slot selects exactly its run-specific proposer. The skeleton requires
  one proposer but does not fix its identity.
* (b) `selValid_exists`: a valid selection exists (the schedule with everyone polling), so
  `SelValid` is satisfiable. -/

namespace Consensus.Goldilocks.Refinement.Test

open Shape
open Consensus.Model (pubOf SelSpec)

variable {V : Type} [Fintype V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- The skeleton requires one proposer without fixing its identity. -/
theorem skeleton_proposerSel (s : Nat) :
    (family S (pubOf E)).skel.proposerSel s = .sized 1 := rfl

/-- In an admitted run, the node schedule is the selected proposer. -/
theorem selValid_proposer (hsel : rho.SelValid) (s : Nat) :
    rho.sel (.proposer s) = {runProposer S rho hn s} :=
  Refinement.selValid_proposer S rho hn hsel s

include hn in
/-- The schedule with everyone polling is an admissible selection. -/
theorem selValid_exists :
    ∃ sel : (Model.protoOf (compiled (family S)) E).Role → Finset (Fin (Fintype.card V)),
      (Model.protoOf (compiled (family S)) E).SelAdmits sel := by
  refine ⟨fun r => match r with
    | .proposer _ => {⟨0, hn⟩}
    | .duty _ k => k.elim
    | .poll => Finset.univ, ?_⟩
  intro r
  cases r with
  | proposer s =>
    change ((family S (pubOf E)).skel.proposerSel s).Admits _
    rw [skeleton_proposerSel S s]
    change ({(⟨0, hn⟩ : Fin (Fintype.card V))} : Finset _).card = min 1 (Fintype.card V)
    simp [min_eq_left hn]
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
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (hs : List (Blocks.Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat)
    (st : NodeState (goldilocksNode sp ro)) (B : Blk sp) (v : SA.Vote sp.n)
    (ha : B.fgPayload = []) (hp : B.acPayload = ([v], []))
    (hc : canonEvent sp ro hs (blockObj sp B) = some (.block B)) :
    deliverRecs proposer dg hs self t i (delivered sp (blockObj sp B)) st 0 =
      groupRecs proposer dg self st t (Nat.pair i 0) (.block B) ++
      groupRecs proposer dg self (Node.onBlock self st t B).1 t (Nat.pair i 1) (.message v) := by
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
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (hs : List (Blocks.Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat)
    (st : NodeState (goldilocksNode sp ro)) (v : SA.Vote sp.n) :
    deliverRecs proposer dg hs self t i
      (delivered sp (.mk .none (.data .relay) [.mk .none (.data .relay) [voteObj v]])) st 0 =
      groupRecs proposer dg self st t (Nat.pair i 2) (.message v) := by
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

/-- Without observation metadata the legacy action-covered horizon is unchanged. -/
theorem action_only_horizon {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (tr : GoldilocksTrace sp ro) (h : tr.observationHorizon = none) (t : Time) :
    tr.InHorizon t ↔ ∃ i, tr.label i ≠ none ∧ t ≤ tr.time i := by
  simp [RunTrace.InHorizon, h]

/-- Projection preserves finite observation metadata, including the absence of it. -/
theorem projection_observation {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (tr : GoldilocksTrace sp ro) :
    tr.projAC.observationHorizon = tr.observationHorizon ∧
      tr.projFG.observationHorizon = tr.observationHorizon := ⟨rfl, rfl⟩

/-- Regression #118: a non-public terminal observation belongs to a valid run. -/
def terminalPoint : EnvPoint (Fin 1) :=
  ⟨⟨2, by decide, fun _ _ => true⟩, Finset.univ, 1, fun _ _ => []⟩

/-- A ready reader remains awake at the finite horizon, and a strictly later unlabelled
cut exists. The old constant-horizon filler makes this conclusion impossible. -/
theorem terminal_observation (S : Setup) :
    ∃ rho : Model.Run (compiled (family S)) terminalPoint.env,
      rho.ExecutionValid ∧ rho.horizon = 1 ∧
      rho.point.Ready (Regimes.catchUp (S.params (pubOf terminalPoint.env) (by decide)))
        0 rho.horizon ∧
      (simTrace S rho (by decide)).awake (rho.ownKey 0) rho.horizon ∧
      ∃ j, (simTrace S rho (by decide)).label j = none ∧
        Regimes.CutAfter (simTrace S rho (by decide)) j rho.horizon := by
  let sel : (Model.protoOf (compiled (family S)) terminalPoint.env).Role →
      Finset (Fin (Fintype.card (Fin 1))) := fun _ => Finset.univ
  have hsel : (Model.protoOf (compiled (family S)) terminalPoint.env).SelAdmits sel := by
    intro r
    cases r with
    | proposer s => change (Finset.univ : Finset (Fin 1)).card = min 1 1; decide
    | poll => rfl
    | duty s k => exact k.elim
  obtain ⟨rho, hp, _, _, hv, _, _, _⟩ := Shape.coverage (family S) terminalPoint
    (by decide) (by exact Equiv.refl _) sel hsel 0
  have hh : rho.horizon = 1 := congrArg EnvPoint.horizon hp
  have hr : rho.point.Ready (Regimes.catchUp (S.params (pubOf terminalPoint.env) (by decide)))
      0 rho.horizon := by
    rw [hp]
    exact ⟨Finset.mem_univ _, fun _ _ _ => rfl⟩
  refine ⟨rho, hv, hh, hr, ?_, (allCuts S rho (by decide)).length, ?_, ?_⟩
  · exact ⟨rfl, hv.horizon_nonneg, le_rfl⟩
  · rw [simTrace_label, List.getElem?_length]; rfl
  · constructor
    · intro k hk
      apply simTrace_labelled_time_le S rho (by decide) hv
      rw [simTrace_label, List.getElem?_eq_getElem hk]
      simp
    · rw [simTrace_time, List.getElem?_length]
      simp

/-- Raw hashes at and on both sides of genesis round-trip without naming genesis.
In particular, a raw parent digest equal to genesis is a valid non-genesis reference. -/
theorem tagged_genesis_boundary :
    taggedRoot 7 6 = 6 ∧ taggedRoot 7 7 = 8 ∧ taggedRoot 7 8 = 9 ∧
      parentRoot 7 (.digest 7) = some 8 ∧ parentRef 7 (some 8) = .digest 7 ∧
      parentRef 7 (some 7) = .root := by decide

end Consensus.Goldilocks.Refinement.Test
