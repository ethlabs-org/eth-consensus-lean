module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Reachable
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Interface
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Client

@[expose] public section

/-! # Goldilocks milestone Compose/AnyAC: the node (statements)

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` (goldilocks#21 and
later), the composition nodes stated at **one node composed with any AC** that meets
requirements 1–5 (`ACInterface.Requirements`), over the configurations the node reaches
(`Node.Reachable`, `Spec/Node`): C0.2 (finalized monotone, also across restarts), C0.3
(honest blocks are accepted), C0.4 (tick order) and C0.5 (projection onto the components: the
AC's states are reachable AC states under the call law, the FG's states are reachable FG states,
the record is a client run, every handler's cuts obey the cut law). C0.1 (three tips on one
chain) at the node is `TipsNested` (`Compose/Interface`) at the AC states of
`ACStatesReachable`, so it has no statement here. The run-level composition statements (C1.1,
Service, Healing, Regimes) are over `Spec/Run`, in their own modules; nothing here mentions a
run, the SA or the engine.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P} (proposer : Nat → Fin P.n)
  (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)

/-- The digest is collision free on the contents of the blocks of `S` (the hypothesis
`NoColl` of claims F.3, C0.3): equal digests of two blocks of `S` mean equal contents. -/
def NoCollOn (S : Set A.Blk) : Prop :=
  ∀ B ∈ S, ∀ C ∈ S,
    dg B.parent B.slot B.input B.fgPayload B.acPayload =
        dg C.parent C.slot C.input C.fgPayload C.acPayload →
      B.parent = C.parent ∧ B.slot = C.slot ∧ B.input = C.input ∧ B.fgPayload = C.fgPayload ∧
        B.acPayload = C.acPayload

/-- **C0.2, finalized monotone.** Along the configurations an honest node reaches, also
across restarts, `Σ.F` moves only to a descendant: the later `Σ.F` extends the earlier one
inside the later tree. -/
def FinalizedMonotone : Prop :=
  ∀ cfg cfg' : Config A, Reachable proposer dg self cfg → Reaches proposer dg self cfg cfg' →
    cfg'.st.fg.Anc cfg.st.fg.F cfg'.st.fg.F

/-- **C0.2, the restart half.** A restart keeps `Σ` and `Λ` (composition.tex §"State"); only
`𝒜` changes, to `ac_restart(𝒜, fg_to_ac(Σ), t)`. -/
def RestartKeepsFG : Prop :=
  ∀ (st : NodeState A) (t : Time),
    (restart self st t).1.fg = st.fg ∧ (restart self st t).1.record = st.record ∧
      (restart self st t).1.ac = (A.restart self st.ac (frame st) t).1

/-- **C0.3, honest blocks are accepted.** Premises: the AC meets the requirements, and genesis
has its digest as root (the spec makes every block's root its digest; the Lean genesis root
is a parameter). In the tick of an honest node at `t = t_s` with `s > 0` whose proposer it
is, after the AC's tick step, when `ac_proposal` returns a parent `H` and a payload `p`, the
block `B` that `propose_block` makes passes the checks of its maker: `H` is held and extends
`Σ.F`, with a smaller slot (the proposal runs before the objects of `t_s`, C0.4, and the node
drops blocks of a future slot); every attestation of `B` is valid against `Σ.σ[H]` and well
formed (the form of fg.tex §"Attestations", checked on the wire by composition.tex §"Blocks";
the Lean `state_transition` folds that check into the FG, consensus-lean#65); `B`'s payload
passes `ac_valid_payload` (requirement 5); `B`'s root is the digest of its content; and, when
the digest is collision free on the tree with `B`, no held block has its root and
`fg_on_block(Σ, B)` accepts `B`. -/
def HonestBlockAccepted : Prop :=
  A.Requirements → (P.genesisBlock A.genesisPayload).RootOk dg →
    ∀ (cfg cfg' : Config A) (t : Time) (x : Nat), Reachable proposer dg self cfg →
      Step proposer dg self cfg (.tick x) t cfg' → Proposes proposer self t →
      let st₁ := (tickStep proposer dg self cfg.st t x .acTick).1
      let r := acProposal st₁ t
      ∀ d p, r.2.2 = some (d, p) →
        let B := mkBlock dg self r.1.fg t x d.head p
        d.head ∈ r.1.fg.tree ∧ r.1.fg.Anc r.1.fg.F d.head ∧ d.head.slot < B.slot ∧
        (∀ a ∈ B.fgPayload, a.WellFormed ∧ (r.1.fg.σ d.head.root).validAtt a) ∧
        A.validPayload B ∧ B.RootOk dg ∧
        (NoCollOn dg (insert B r.1.fg.tree) → r.1.fg.blocks B.root = none ∧
          ∃ fg', r.1.fg.onBlock B = some fg')

/-- The cuts of the proposal step at validator `self` and time `t`: none when `self` does not
propose at `t`; else `ac_proposal`, then nothing (`⊥`), or the own block `B` of slot `slot(t)`
and proposer `self`, refused by the FG, or accepted and then given to `ac_on_block`. -/
def ProposalCuts (t : Time) (pc : List (Cut A)) : Prop :=
  (¬ Proposes proposer self t ∧ pc = []) ∨
  (Proposes proposer self t ∧ ∃ ℓ : ACLabel A, ℓ.call = .proposal ∧
    (pc = [.ac ℓ] ∨
      ∃ B : A.Blk, B.slot = P.slotOf t ∧ B.proposer = self ∧
        (pc = [.ac ℓ, .fg (.block B false)] ∨
          ∃ ℓ' : ACLabel A, ℓ'.call = .block B ∧ pc = [.ac ℓ, .fg (.block B true), .ac ℓ'])))

/-- The cuts of the FG update: `ac_to_fg`, then nothing (`⊥`), or `fg_attest` on the source
`C`, which signs nothing, or signs `a` and the own `fg_on_attestation(a)` follows. -/
def UpdateCuts (uc : List (Cut A)) : Prop :=
  ∃ ℓ : ACLabel A, ℓ.call = .toFG ∧
    (uc = [.ac ℓ] ∨ (∃ C : A.Blk, uc = [.ac ℓ, .fg (.attest C none)]) ∨
      ∃ (C : A.Blk) (a : FG.Att P.n), uc = [.ac ℓ, .fg (.attest C (some a)), .fg (.attestation a)])

/-- The shape of a tick's cuts (claims C0.4): `ac_on_tick`, the proposal cuts, the FG update
cuts, in this order. -/
def TickShape (t : Time) (cs : List (Cut A)) : Prop :=
  ∃ (ℓ : ACLabel A) (pc uc : List (Cut A)),
    ℓ.call = .tick ∧ cs = .ac ℓ :: (pc ++ uc) ∧ ProposalCuts proposer self t pc ∧ UpdateCuts uc

/-- **C0.4, tick order.** The cuts of `on_tick(t)` at every state have the shape `TickShape`:
the AC's tick; at `t = t_s` with `s > 0`, for the slot's proposer, `ac_proposal` and then,
when it returns a proposal, the own block, processed at once (`fg_on_block`, then
`ac_on_block`); the FG update (`ac_to_fg`, then `fg_attest` with the own attestation
processed at once). That a restart precedes the tick and the tick precedes the objects
received at its time is `Node.Step` (`EventOK`). -/
def TickOrder : Prop :=
  ∀ (st : NodeState A) (t : Time) (x : Nat),
    TickShape proposer self t (onTick proposer dg self st t x).2

/-- **C0.5 (c), honest attestations are signed only in ticks.** An `fg_attest` cut that signs
appears only in the cuts of a tick (so, by `Node.Step`, at a public time). -/
def SignedOnlyInTicks : Prop :=
  ∀ (st : NodeState A) (t : Time) (e : Event A) (C : A.Blk) (a : FG.Att P.n),
    Cut.fg (.attest C (some a)) ∈ (exec proposer dg self st t e).2 → ∃ x, e = .tick x

/-- **C0.5 (b), the AC sees only blocks the FG accepted** (claims C0.5 (b), goldilocks#36). In
the cuts of every event at every state, an AC cut with the call `ac_on_block(B)` comes right
after the FG cut that accepts `B`, and at the FG state `Σ` before that cut `fg_on_block(Σ, B)`
accepts: `B` is not of a future slot, its root is new, its full parent is held, it extends
`Σ.F`, and `state_transition` passes from the parent's state (so its parent is of a smaller
slot, the assertion of `state_transition`). That its proposer is its slot's is not a node fact
and is not part of this statement: no node check reads the proposer, and in a run it is the run
law `LocalRun.proposerCredential` for a delivered block and `Proposes` for the own block
(`accept_facts`; `docs/decisions.md` 2026-10-31). A restart passes no block: its replay runs
inside `ac_restart`, over the frame's tree. -/
def ACSeesAcceptedBlocks : Prop :=
  ∀ (st : NodeState A) (t : Time) (e : Event A) (ℓ : ACLabel A) (B : A.Blk),
    Cut.ac ℓ ∈ (exec proposer dg self st t e).2 → ℓ.call = .block B →
      ∃ (cs₁ cs₂ : List (Cut A)) (st₁ : NodeState A),
        (exec proposer dg self st t e).2 = cs₁ ++ Cut.fg (.block B true) :: Cut.ac ℓ :: cs₂ ∧
        CutChain self t st cs₁ st₁ ∧
        B.slot ≤ P.slotOf t ∧ (st₁.fg.onBlock B).isSome ∧
        st₁.fg.blocks B.root = none ∧
        ∃ pr, B.parent = some pr ∧ (st₁.fg.blocks pr).isSome ∧
          Anc (insert B st₁.fg.tree) st₁.fg.F B ∧
          (P.fg.stateTransition (st₁.fg.σ pr) B.fgView).isSome

/-- **C0.5, every handler's cuts obey the cut law.** The cuts of every event at every state
form a `CutChain` from the state before to the state after: each AC cut executes the AC with
the frame `fg_to_ac(Σ)` at that cut and changes only `𝒜`; each FG cut executes its FG call. -/
def ExecIsCutChain : Prop :=
  ∀ (st : NodeState A) (t : Time) (e : Event A),
    CutChain self t st (exec proposer dg self st t e).2 (exec proposer dg self st t e).1

/-- **C0.5 (a), (b), the AC's states are reachable.** At a reachable configuration of an
honest node, the accepted tree is coherent and the AC state is reachable inside it
(`ACInterface.ReachableAt`): from the initial AC state by calls at nondecreasing times, under
the call law (`CallOK`: well-formed frames in `Σ.T`, equal frames between calls except
`Φ ⊑_B Φ'` at `ac_on_block(Φ', B)`, wire-checked inputs), with the frame of the last call the
current `fg_to_ac(Σ)` and its time at most the clock. Requirement 5 supplies the own block's
payload check. -/
def ACStatesReachable : Prop :=
  A.Requirements → ∀ cfg : Config A, Reachable proposer dg self cfg →
    Coherent cfg.st.fg.tree ∧
      ∃ t₀, t₀ ≤ cfg.time ∧ A.ReachableAt self cfg.st.fg.tree cfg.st.ac (frame cfg.st) t₀

/-- **C0.5 (c), the FG's states are reachable.** At a reachable configuration of an honest
node, the FG state is reachable by the FG handlers (`Store.Reachable`) from the initial state
with the AC's genesis payload. -/
def FGStatesReachable : Prop :=
  ∀ cfg : Config A, Reachable proposer dg self cfg → cfg.st.fg.Reachable A.genesisPayload

/-- **C0.5 (c), the record is a client run.** At a reachable configuration of an honest node,
the record is the record of the client run (`FG.Record.run`) over the entry states of the
sources given to `fg_attest`, in order, and every attestation that run signed is in the
pool. -/
def RecordIsClientRun : Prop :=
  ∀ cfg : Config A, Reachable proposer dg self cfg →
    ∃ σes : List (FG.ChainState P.n),
      cfg.st.record = (FG.Record.run self FG.Record.empty σes).1 ∧
        ∀ a ∈ (FG.Record.run self FG.Record.empty σes).2, a ∈ cfg.st.fg.atts

/-- **C0.5 (c), the sources are held.** In the tick of an honest node at a reachable
configuration, the source `C` given to `fg_attest` is a block of the tree of the frame after
the tick that extends `Σ.F` (the FG input contract: `Σ.σ[C]` is the state of a held block). -/
def SourcesHeld : Prop :=
  A.Requirements → ∀ (cfg cfg' : Config A) (t : Time) (x : Nat),
    Reachable proposer dg self cfg →
    Step proposer dg self cfg (.tick x) t cfg' → ∀ (C : A.Blk) (s : Option (FG.Att P.n)),
      Cut.fg (.attest C s) ∈ (exec proposer dg self cfg.st t (.tick x)).2 →
        C ∈ cfg'.st.fg.tree ∧ cfg'.st.fg.Anc cfg'.st.fg.F C

/-- The Compose/AnyAC node statements, for one node (one AC, digest and validator). -/
structure NodeStatements : Prop where
  finalizedMonotone : FinalizedMonotone proposer dg self
  restartKeepsFG : RestartKeepsFG (A := A) self
  honestBlockAccepted : HonestBlockAccepted proposer dg self
  tickOrder : TickOrder proposer dg self
  signedOnlyInTicks : SignedOnlyInTicks proposer dg self
  acSeesAcceptedBlocks : ACSeesAcceptedBlocks proposer dg self
  execIsCutChain : ExecIsCutChain proposer dg self
  acStatesReachable : ACStatesReachable proposer dg self
  fgStatesReachable : FGStatesReachable proposer dg self
  recordIsClientRun : RecordIsClientRun proposer dg self
  sourcesHeld : SourcesHeld proposer dg self

/-- The Compose/AnyAC node statements, for every parameter set, AC, digest and validator. -/
def ComposeNodeStatements : Prop :=
  ∀ (P : Params) (A : NodeAC P) (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n), NodeStatements proposer dg self

end Consensus.Goldilocks.Compose

end
