module
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Trace
import all ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape
import all ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Concrete
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Proofs.RegimesRealizable.Main
import ConsensusLean.Lemmas.Tactic.Linarith
@[expose] public section

/-! # Witnesses for the Goldilocks refinement statements

Labelled by kind (CONTRIBUTING "Statements"):

* (a) `selValid_proposer`: in a run admitted by the engine (`SelValid`, part of
  `ExecutionValid`), each slot selects exactly its run-specific proposer. The skeleton requires
  one proposer but does not fix its identity.
* (b) `selValid_exists`: a valid selection exists (the schedule with everyone polling), so
  `SelValid` is satisfiable. -/

namespace Consensus.Goldilocks.Simulation.Test
open AsChainShape

open Shape
open Consensus.Model (pubOf SelSpec)

variable {V : Type} [Fintype V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The skeleton requires one proposer without fixing its identity. -/
theorem skeleton_proposerSel (s : Nat) :
    (goldilocks S (pubOf E)).skel.proposerSel s = .sized 1 := rfl

/-- In an admitted run, the node schedule is the selected proposer. -/
theorem selValid_proposer (hsel : rho.SelValid) (s : Nat) :
    rho.sel (.proposer s) = {runProposer ⟨S, stock⟩ rho hn s} :=
  Simulation.selValid_proposer ⟨S, stock⟩ rho hn hsel s

include hn in
/-- The schedule with everyone polling is an admissible selection. -/
theorem selValid_exists :
    ∃ sel : (Model.protoOf (compiled (goldilocks S)) E).Role → Finset (Fin (Fintype.card V)),
      (Model.protoOf (compiled (goldilocks S)) E).SelAdmits sel := by
  refine ⟨fun r => match r with
    | .proposer _ => {⟨0, hn⟩}
    | .duty _ k => k.elim
    | .poll => Finset.univ, ?_⟩
  intro r
  cases r with
  | proposer s =>
    change ((goldilocks S (pubOf E)).skel.proposerSel s).Admits _
    rw [skeleton_proposerSel S s]
    change ({(⟨0, hn⟩ : Fin (Fintype.card V))} : Finset _).card = min 1 (Fintype.card V)
    simp [min_eq_left hn]
  | duty _ k => exact k.elim
  | poll => rfl

variable [DecidableEq V]

/-- Exact-time release cannot be satisfied solely by a later send, even at the horizon. -/
theorem released_requires_same_time (v : V)
    (o : (Model.protoOf (compiled (goldilocks S)) E).Object) (τ : Time)
    (h : ReleasedFrom ⟨S, stock⟩ rho v o τ) : rho.releases v o τ :=
  (releasedFrom_iff ⟨S, stock⟩ rho v o τ).mp h

/-- An admission at the horizon still requires a relay at that same time. -/
theorem relayed_at_horizon (v : V) (o : (Model.protoOf (compiled (goldilocks S)) E).Object)
    (h : RelayedFrom ⟨S, stock⟩ rho v o rho.horizon) :
    ∃ cs, o ∈ cs ∧ rho.releases v (.mk .none (.data .relay) cs) rho.horizon :=
  (relayedFrom_iff ⟨S, stock⟩ rho v o rho.horizon).mp h

/-- At the stock binding `releasedFrom_of_pending` concludes its population-wide form, by `rfl`:
the pending body was released as the object signed in the poll role. -/
theorem releasedFrom_of_pending_stock (hv : rho.ExecutionValid) {i : Nat}
    {ev : Model.Event V (Model.protoOf (compiled (goldilocksWith ⟨S, stock⟩)) E).Object}
    (he : rho.events[i]? = some ev) {b : Body}
    (hb : b ∈ (stateAt ⟨S, stock⟩ rho hn ev.node (i + 1)).outbox) :
    ReleasedFrom ⟨S, stock⟩ rho ev.node
      (Model.Obj.mk (.signed (rho.ownKey ev.node) .poll) (.data b) []) ev.time :=
  releasedFrom_of_pending ⟨S, stock⟩ rho hn hv he hb

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
    (hc : canonEvent sp ro hs (blockObj sp (binding := stock) B) = some (.block B)) :
    deliverRecs (binding := stock) proposer dg hs self t i (delivered sp (blockObj sp B)) st 0 =
      groupRecs proposer dg self st t (Nat.pair i 0) (.block B) ++
      groupRecs proposer dg self (Node.onBlock self st t B).1 t (Nat.pair i 1) (.message v) := by
  have hd : delivered sp (blockObj sp (binding := stock) B) =
      [blockObj sp B, voteObj v] := by
    simp [delivered, blockObj, payloadObjs, ha, hp, voteObj, Model.Obj.parts,
      Model.Obj.parts.partsList]
  rw [hd]
  simp [deliverRecs_cons, deliverRecs_nil, hc, canonEvent_voteObj, Node.exec]

omit [DecidableEq V] in
/-- Two nested relay wrappers still execute the carried vote's message handler, with its
actual cuts and post-states, rather than dropping the inner wrapper's contents. -/
theorem nested_payload_message {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (hs : List (Blocks.Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat)
    (st : NodeState (goldilocksNode sp ro)) (v : SA.Vote sp.n) :
    deliverRecs (binding := stock) proposer dg hs self t i
      (delivered sp (.mk .none (.data .relay) [.mk .none (.data .relay) [voteObj v]])) st 0 =
      groupRecs proposer dg self st t (Nat.pair i 2) (.message v) := by
  simp only [delivered, voteObj, Model.Obj.parts, Model.Obj.parts.partsList,
    List.append_nil]
  simp only [deliverRecs_cons, deliverRecs_nil]
  simp [canonEvent, decodeBlock, decodeVoteObj, decodeAttObj,
    stock, VoteBinding.voteRole, decodeVote_encodeVote, Option.filter]

/-- Unsigned timestamps cannot certify forwarding freshness. -/
theorem unsigned_forward_rejected (sp : SA.SAParams) (hs : List (Blocks.Header Info × Nat))
    (t : Time) (cs : List (Wire sp.n)) :
    decodeForward sp hs (.mk .none (.data (.forward t)) cs) = none := by
  simp [decodeForward]

/-- A parent signed by a different origin cannot satisfy the forwarding chain. -/
theorem foreign_parent_rejected (sp : SA.SAParams) (hs : List (Blocks.Header Info × Nat))
    (x y : Fin sp.n) (hne : y ≠ x) (t pt : Time) (B A : Blk sp)
    (p : Wire sp.n) (pp : Option (Wire sp.n))
    (hb : decodeBlock sp hs (blockObj sp (binding := stock) B) = some B)
    (hp : decodeForward sp hs p = some (y, pt, pp, A)) :
    decodeForward sp hs (forwardObj sp x t (some p) B) = none := by
  simp [forwardObj, decodeForward, hb, hp, hne]

/-- A negative claimed acceptance time is rejected even for a canonical genesis child. -/
theorem negative_forward_rejected (sp : SA.SAParams) (hs : List (Blocks.Header Info × Nat))
    (x : Fin sp.n) (t : Time) (ht : t < 0) (B : Blk sp)
    (hb : decodeBlock sp hs (blockObj sp (binding := stock) B) = some B) :
    decodeForward sp (binding := stock) hs (forwardObj sp x t none B) = none := by
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

/-- Regression: a non-public terminal observation belongs to a valid run. -/
def terminalPoint : EnvPoint (Fin 1) :=
  ⟨⟨2, by decide, 2, by decide, fun _ _ => true⟩, fun _ => ∅,
    monotone_const, 1, fun _ _ => []⟩

/-- A ready reader remains awake at the finite horizon, and a strictly later unlabelled
cut exists. The old constant-horizon filler makes this conclusion impossible. -/
theorem terminal_observation (S : Setup) :
    ∃ rho : Model.Run (compiled (goldilocks S)) terminalPoint.env,
      rho.ExecutionValid ∧ rho.horizon = 1 ∧
      rho.point.Ready (Regimes.catchUp (S.params (pubOf terminalPoint.env) (by decide)))
        0 rho.horizon ∧
      (simTrace ⟨S, stock⟩ rho (by decide)).awake (rho.ownKey 0) rho.horizon ∧
      ∃ j, (simTrace ⟨S, stock⟩ rho (by decide)).label j = none ∧
        Regimes.CutAfter (simTrace ⟨S, stock⟩ rho (by decide)) j rho.horizon := by
  let sel : (Model.protoOf (compiled (goldilocks S)) terminalPoint.env).Role →
      Finset (Fin (Fintype.card (Fin 1))) := fun _ => Finset.univ
  have hsel : (Model.protoOf (compiled (goldilocks S)) terminalPoint.env).SelAdmits sel := by
    intro r
    cases r with
    | proposer s => change (Finset.univ : Finset (Fin 1)).card = min 1 1; decide
    | poll => rfl
    | duty s k => exact k.elim
  obtain ⟨rho, hp, _, _, hv, _, _, _⟩ := Shape.coverage (goldilocks S) terminalPoint
    (by decide) (by exact Equiv.refl _) sel hsel 0
  have hh : rho.horizon = 1 := congrArg EnvPoint.horizon hp
  have hr : rho.point.Ready (Regimes.catchUp (S.params (pubOf terminalPoint.env) (by decide)))
      0 rho.horizon := by
    rw [hp]
    exact ⟨by simp [EnvPoint.HonestAt, terminalPoint], fun _ _ _ => rfl⟩
  refine ⟨rho, hv, hh, hr, ?_, (allCuts ⟨S, stock⟩ rho (by decide)).length, ?_, ?_⟩
  · rw [simTrace_awake_iff ⟨S, stock⟩ rho (by decide), awakeAt_iff ⟨S, stock⟩ rho (by decide)]
    exact ⟨rfl, hv.horizon_nonneg, le_rfl⟩
  · rw [simTrace_label ⟨S, stock⟩ rho (by decide), List.getElem?_length]; rfl
  · constructor
    · intro k hk
      apply simTrace_labelled_time_le ⟨S, stock⟩ rho (by decide) hv
      rw [simTrace_label ⟨S, stock⟩ rho (by decide), List.getElem?_eq_getElem hk]
      simp
    · rw [simTrace_time ⟨S, stock⟩ rho (by decide), List.getElem?_length]
      simp

/-- Raw hashes at and on both sides of genesis round-trip without naming genesis.
In particular, a raw parent digest equal to genesis is a valid non-genesis reference. -/
theorem tagged_genesis_boundary :
    taggedRoot 7 6 = 6 ∧ taggedRoot 7 7 = 8 ∧ taggedRoot 7 8 = 9 ∧
      parentRoot 7 (.digest 7) = some 8 ∧ parentRef 7 (some 8) = .digest 7 ∧
      parentRef 7 (some 7) = .root := by decide

/-- Engine Δ=2 induces protocol Δ=2 (`Δ_p = Δ_e`), with no increment in either grid:
slots of `4Δ = 8`. -/
theorem protocol_delay_grid (S : Setup) :
    let pub : Model.Public := ⟨1, 2, by decide, 2, by decide⟩
    (S.params pub (by decide)).Δ = 2 ∧
      (goldilocks S pub).skel.grid.slotTime 1 = 8 ∧
      (goldilocksShape (S.params pub (by decide)) (S.ro 1)).skel.grid.slotTime 1 = 8 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Half-open engine delivery (held by `base + Δ − 1`) is strict protocol delivery
(`< base + Δ_p`) at `Δ_p = Δ_e`. -/
theorem protocol_delivery_endpoint (S : Setup) (pub : Model.Public) (hn : 1 ≤ pub.n)
    (base delivered : Time) (h : delivered ≤ base + pub.ΔAC - 1) :
    delivered < base + (S.params pub hn).Δ := by
  change delivered < base + pub.ΔAC
  linarith

/-- **Control**: the protocol delay adds no slack, so a receipt at the engine bound
`base + Δ` itself is not strictly before `base + Δ_p`. -/
theorem protocol_delivery_bound_not_strict (S : Setup) (pub : Model.Public) (hn : 1 ≤ pub.n)
    (base : Time) : ¬ base + pub.ΔAC < base + (S.params pub hn).Δ := by
  change ¬ base + pub.ΔAC < base + pub.ΔAC
  exact lt_irrefl _

/-- Old k=2 coefficients fail independently (recorded under the former `Δp = Δe + 1`): Δe=1 gives
insufficient lag; Δe=8, Δp=9, b₀=89 has phase 35, so the old duration 24 violates lifetime 54. -/
theorem old_outage_coefficients_fail :
    (4 : Int) * 1 < 4 * (1 + 1) ∧
      (89 : Int) ≥ 4 * 9 ∧
      24 + (89 - 6 * 9) % (4 * 9) > (4 * 2 - 2) * 9 ∧
      16 + (89 - 6 * 9) % (4 * 9) ≤ (4 * 2 - 2) * 9 := by decide

/-- Actual successful cuts queue a parent and child at one timestamp, with the child's
exact parent wrapper supplied by the persistent root map. Refusal queues neither. -/
theorem acceptance_publication_order {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (A B : Blk sp)
    (ha : A.parent = some sp.genesisRoot) (hb : B.parent = some A.root)
    (hroot : A.root ≠ sp.genesisRoot) (hq : st.forwards = []) :
    (apply st (st.node, [.fg (.block A true), .fg (.block B true)])).forwards =
      [(st.now, [blockObj sp A]),
       (st.now, [forwardObj sp st.self st.now none A, blockObj sp B])] ∧
    (apply st (st.node, [.fg (.block A false)])).forwards = [] := by
  simp [apply, queueAccepted, ha, hb, hroot, hq, Function.update]

/-- The installed poll drains all timestamped wrappers in order and retains their durable map. -/
theorem publisher_poll_drain {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (t : Time)
    (hf : st.fgDue = false) (ho : st.outbox = []) :
    (goldilocksShape sp ro).pollBatch st t =
      ({ st with forwards := [], voteForwards := [] },
        st.forwards.map (fun p => (.forward p.1, p.2)) ++
        st.voteForwards.map (fun p => (.voteForward p.1 (encodeVote p.2), [voteObj p.2]))) := by
  simp [goldilocksShape, pollBatch, poll, hf, ho]
  rfl

/-- A duplicate block is refused by the actual node handler and creates no fresh candidate. -/
theorem duplicate_no_publication {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (B : Blk sp)
    (hs : st.node.fg.blocks B.root = some B) :
    (apply st (Node.onBlock st.self st.node st.now B)).forwards = st.forwards := by
  unfold Node.onBlock
  split
  · rfl
  · have hr : st.node.fg.onBlock B = none := by
      unfold Store.onBlock
      cases hp : B.parent <;> simp [hs]
    rw [hr]
    rfl

/-- Wire equality alone cannot identify an accepted block's root: headers omit that field.
Publication provenance must use decoding with the engine digest, not only `forwardObj` equality. -/
theorem forwarding_root_alias (sp : SA.SAParams) (x : Fin sp.n) (t : Time)
    (p : Option (Wire sp.n)) (B : Blk sp) :
    forwardObj sp x t p { B with root := B.root + 1 } = forwardObj sp x t p B ∧
      ({ B with root := B.root + 1 } : Blk sp) ≠ B := by
  refine ⟨rfl, ?_⟩
  intro h
  have hr := congrArg (fun C : Blk sp => C.root) h
  simp at hr

/-- **Row classification** (`isFGAtt`): a standalone attestation and a
relay wrapper of attestations only are rows (bound `ΔF`); a mixed relay wrapper (an attestation
with a vote) and the empty relay wrapper are not (bound `Δ`). -/
theorem isFGAtt_classification {n : Nat} (a : FG.Att n) (v : SA.Vote n) :
    isFGAtt (attObj (binding := stock) a) ∧
      isFGAtt (.mk .none (.data .relay) [attObj a] : Wire n) ∧
      ¬ isFGAtt (.mk .none (.data .relay) [attObj a, voteObj v] : Wire n) ∧
      ¬ isFGAtt (.mk .none (.data .relay) [] : Wire n) := by
  simp [isFGAtt, IsAttObj, attObj, voteObj]

end Consensus.Goldilocks.Simulation.Test
