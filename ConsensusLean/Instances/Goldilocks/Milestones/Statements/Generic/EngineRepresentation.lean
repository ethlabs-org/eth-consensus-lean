module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.CorrectLocal
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.BlockFinality
public import ConsensusLean.Spec.Shape.Run

@[expose] public section

set_option autoImplicit false
namespace Consensus.Goldilocks.Generic
open Shape Blocks Generic
variable {P : Params} {A : NodeAC P} {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V}

structure RunMap (rho : Model.Run (compiled F) E) (payload : A.Blk → Set Nat) where
  validator : Fin P.n ≃ V
  keyIndex : Fin P.n ≃ Fin (Fintype.card V)
  key_eq : ∀ y, rho.key (keyIndex y) = validator y
  trace : RunTrace A
  proposer : Nat → Fin P.n
  digest : Digest (List (FG.Att P.n)) A.Payload
  signer : A.Msg → Fin P.n
  honest : Time → Set (Fin P.n)
  cut : Nat → Nat
  cut_mono : Monotone cut
  event : Nat → Nat
  event_bound : ∀ k, trace.label k ≠ none → event k < rho.events.length
  event_group : ∀ k, trace.label k ≠ none →
    cut (event k) ≤ k ∧ k < cut (event k + 1)
  before_time : ∀ i, i ≤ rho.events.length → ∀ k < cut i,
    trace.time k ≤ rho.cutTime i
  after_time : ∀ i, i ≤ rho.events.length → rho.cutTime i ≤ trace.time (cut i)
  event_time : ∀ k e, trace.label k ≠ none → rho.events[event k]? = some e →
    trace.time k = e.time
  state : (F (Model.pubOf E)).State → NodeState A
  state_eq : ∀ v i, i ≤ rho.events.length → rho.point.HonestAt v (rho.cutTime i) →
    state (rho.stateBefore i v).st.1 = trace.state (validator.symm v) (cut i)
  honest_eq : ∀ y t, y ∈ honest t ↔ rho.point.HonestAt (validator y) t
  awake_eq : ∀ y t, trace.awake y t ↔ E.awake (validator y) t = true ∧
    0 ≤ t ∧ t ≤ rho.horizon
  horizon_eq : ∀ t, trace.InHorizon t ↔ t ≤ rho.horizon
  delta_eq : P.Δ = E.ΔAC
  header : A.Blk → Header Info
  header_input : ∀ B, (header B).input = B.input
  payload_eq : ∀ B, payload B = {tx | tx ∈ decodeTxs (header B).input}
  proposalObject : A.Blk → (Model.protoOf (compiled F) E).Object
  proposal_role : ∀ B, ∃ r cs, ProposalRole (header B) r ∧
    proposalObject B = .mk (.signed (keyIndex B.proposer) r) (.item (header B)) cs
  attObject : FG.Att P.n → (Model.protoOf (compiled F) E).Object
  att_signer : ∀ a, rho.signerOf (attObject a) = some (validator a.val)
  att_conflict : ∀ a b, FG.slashable a b →
    (Model.protoOf (compiled F) E).conflicts (attObject a) (attObject b) = true
  tip : O.Id → NodeState A → Time → A.Blk
  chain : NodeState A → A.Blk → List A.Blk
  output_eq : ∀ g v i, i ≤ rho.events.length →
    (F (Model.pubOf E)).out g (rho.stateBefore i v).st.1 =
      (chain (state (rho.stateBefore i v).st.1)
        (tip g (state (rho.stateBefore i v).st.1) (rho.cutTime i))).map header
  available_tip : ∀ g, O.output .available = some g → ∀ st t,
    tip g st t = A.confirmed st.ac (Node.frame st) t

variable {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}
structure ReadRepresentation (M : RunMap rho payload) : Prop where
  chain_held : ∀ st tip B, B ∈ M.chain st tip → B ∈ st.fg.tree
  linked : ∀ st tip, st.fg.Reachable A.genesisPayload →
    (∀ B ∈ st.fg.tree, B.RootOk M.digest) →
    Chain.Linked rho.hash ((M.chain st tip).map M.header)
  increasing : ∀ st tip, st.fg.Reachable A.genesisPayload →
    Chain.PosIncreasing ((M.chain st tip).map M.header)
  ancestor_prefix : ∀ u v i j, i ≤ rho.events.length → j ≤ rho.events.length →
    rho.point.HonestAt u (rho.cutTime i) → rho.point.HonestAt v (rho.cutTime j) →
    let st := M.trace.state (M.validator.symm u) (M.cut i)
    let st' := M.trace.state (M.validator.symm v) (M.cut j)
    st.fg.Reachable A.genesisPayload → st'.fg.Reachable A.genesisPayload →
    (∀ X ∈ st.fg.tree, X.RootOk M.digest) →
    (∀ X ∈ st'.fg.tree, X.RootOk M.digest) →
    Coherent (M.trace.HonestBlocksAt M.honest) →
    st.fg.tree ⊆ M.trace.HonestBlocksAt M.honest →
    st'.fg.tree ⊆ M.trace.HonestBlocksAt M.honest →
    ∀ B B', B ∈ st.fg.tree → B' ∈ st'.fg.tree →
      Anc (M.trace.HonestBlocksAt M.honest) B B' →
      List.IsPrefix ((M.chain st B).map M.header) ((M.chain st' B').map M.header)
  tip_in_chain : ∀ st B, B ∈ st.fg.tree → B.root ≠ P.genesisRoot →
    M.header B ∈ (M.chain st B).map M.header
  confirmed_tip : ∀ g, O.output .stable = some g → ∀ st t,
    M.tip g st t = A.confirmed st.ac (Node.frame st) t
  finalized_tip : ∀ g, O.output .final = some g → ∀ st t, M.tip g st t = st.fg.F

structure HonestReadTransport (M : RunMap rho payload) : Prop where
  reachable : rho.ExecutionValid → ∀ v i, i ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime i) →
    (M.trace.state (M.validator.symm v) (M.cut i)).fg.Reachable A.genesisPayload
  roots : rho.ExecutionValid → ∀ v i, i ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime i) →
    ∀ B ∈ (M.trace.state (M.validator.symm v) (M.cut i)).fg.tree, B.RootOk M.digest
  held_view : rho.ExecutionValid → ∀ v i, i ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime i) →
    ∀ B ∈ (M.trace.state (M.validator.symm v) (M.cut i)).fg.tree,
      B.root ≠ P.genesisRoot → M.proposalObject B ∈ rho.ViewIdx v i
  chain_nonroot : ∀ st tip B, B ∈ M.chain st tip → B.root ≠ P.genesisRoot
  held_att_view : rho.ExecutionValid → ∀ v i, i ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime i) →
    ∀ B ∈ (M.trace.state (M.validator.symm v) (M.cut i)).fg.tree,
    ∀ a ∈ B.fgPayload, M.attObject a ∈ rho.ViewIdx v i
  chain_att_view : rho.ExecutionValid → ∀ v i, i ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime i) → ∀ X a,
    a ∈ BlockFinality.ChainAtts M.trace (M.validator.symm v) (M.cut i) X →
    M.attObject a ∈ rho.ViewIdx v i

def ReadyRead (M : RunMap rho payload) (c : Time) (y : Fin P.n) (i : Nat)
    (t : Time) : Prop :=
  y ∈ M.honest t ∧ (∀ k < i, M.trace.time k ≤ t) ∧ t ≤ M.trace.time i ∧
    0 ≤ t ∧ t ≤ rho.horizon ∧
    ∀ u, max 0 (t - c - 1) ≤ u → u ≤ t → M.trace.awake y u

structure EngineBinding (payload : A.Blk → Set Nat) where
  map : ∀ (E : Env V) (rho : Model.Run (compiled F) E),
    rho.ExecutionValid → RunMap rho payload

structure CoveringWitnessBinding (p : EnvPoint V)
    (ext : (Model.sysExternal O (compiled F) V).Ext p.env) (gst : Time)
    (rho : Model.Run (compiled F) p.env) (M : RunMap (A := A) rho payload) : Prop where
  valid : rho.ExecutionValid
  clean : ¬ rho.HashCollision
  point : rho.point = p
  external : (rho.key, rho.sel) = ext
  eager : rho.log.EagerFrom rho.point gst
  progress : ∀ π c s t, (shapeProgress F V).holds π c s t p ext →
    (shapeProgress F V).holds π c s t rho.point (rho.key, rho.sel)
  local_run : Growing.LocalRun M.proposer M.digest M.honest M.signer M.trace

end Consensus.Goldilocks.Generic
