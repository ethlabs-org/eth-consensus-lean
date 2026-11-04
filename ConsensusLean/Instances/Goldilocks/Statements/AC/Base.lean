module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Trace

@[expose] public section

/-! # Goldilocks milestone ACBase: the AC interface and the SA's foundations (statements)

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` (goldilocks#21, merged as
goldilocks main `c4928a76`), the L0 nodes of the AC module (decomposition §3.1, §4.1): F.1 (a)–(c)
(the SA's schedule arithmetic, lock expiry, joining), A0.1–A0.5, A0.7, A0.8 (pool, resolution,
counting, lock store, lock to tip, restart, one vote per slot), A0.6 (requirements 1–4 of
composition.tex §"The available chain" over reachable AC states) and A0.9 (requirement 5: the
proposal payload is valid), against the SA of `Spec/SA` and the AC interface and traces of
`Spec/AC`. One more statement is not a claims node: `LocalRunReachable`, that the AC trace contract
gives reachable states (decomposition §2 D), so that the step statements of ACSteps can use the A0
nodes.

"At an honest node at every time" reads: at every reachable state (`ACInterface.ReachableAt`,
with the frame and the time of its last call) inside a coherent set of blocks, and every later
time. The nodes about one node's life across restarts (F.1 (c), A0.7's joined clause, A0.8)
are stated over an AC trace with its contract (`ACLocalRun`). The A1 step lemmas are the later
milestone ACSteps. `docs/goldilocks-mapping.md` §"ACBase" maps each statement to its node.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- **F.1 (a), slot arithmetic.** `slot(t_s + iΔ) = s` for `0 ≤ i < 4`;
`t_s + 5Δ = t_{s+1} + Δ` and `t_s + 6Δ = t_{s+1} + 2Δ`. -/
def SlotArithmetic : Prop :=
  ∀ s : Nat, (∀ i : Nat, i < 4 → sp.slot (sp.ts s + i * sp.Δ) = s) ∧
    sp.ts s + 5 * sp.Δ = sp.ts (s + 1 : Nat) + sp.Δ ∧
    sp.ts s + 6 * sp.Δ = sp.ts (s + 1 : Nat) + 2 * sp.Δ

/-- **F.1 (b), lock expiry.** For fixed stored locks and a fixed frame, the live locks are the
same at all times of one slot `[t_m, t_{m+1})`. -/
def LockExpiry : Prop :=
  ∀ (FGP : Type) (L : Set Lock) (Φ : Frm sp.n FGP) (m : Nat) (t t' : Time),
    sp.ts m ≤ t → t < sp.ts (m + 1 : Nat) → sp.ts m ≤ t' → t' < sp.ts (m + 1 : Nat) →
      liveLocks sp L Φ t = liveLocks sp L Φ t'

/-- **F.1 (c), joining.** A node whose latest restart is at `t_j` is joined from `t_{j+1}`, and
one whose latest restart is in `(t_j, t_{j+1})` from `t_{j+2}`. -/
def JoinedFrom : Prop :=
  ∀ (A : SAState sp.n) (j : Nat) (w t : Time), A.restartTime = (w : WithBot Time) → w ≤ t →
    (w = sp.ts j → (joined sp A t ↔ sp.ts (j + 1 : Nat) ≤ t)) ∧
    (sp.ts j < w → w < sp.ts (j + 1 : Nat) → (joined sp A t ↔ sp.ts (j + 2 : Nat) ≤ t))

/-- **F.1 (c), a joined node.** In an AC trace with its contract: an honest node that is joined
after a call at `t` has been awake on `[max(0, t_{slot(t)−1}), t]`, with no restart in
`(t_{slot(t)−1}, t]` up to that call. -/
def JoinedAwake : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro),
    ACLocalRun (goldilocksSA sp FGP ro) H U tr → ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ →
      joined sp (tr.post i) (tr.time i) →
      (∀ u : Time, max 0 (sp.ts ((sp.slot (tr.time i) : Int) - 1)) ≤ u → u ≤ tr.time i →
        tr.awake y u) ∧
      ∀ j ≤ i, tr.RestartAt y j → tr.time j ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1)

/-- **A0.1, pool capacity.** At a reachable state, the slot-`σ` pool holds only slot-`σ` votes,
and at most two distinct votes per validator. -/
def PoolCap : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP),
    (goldilocksSA sp FGP ro).AtReachable fun _ _ (A : SAState sp.n) _ _ =>
    ∀ σ, (∀ x ∈ A.pool σ, x.slot = σ) ∧
      ∀ i : Fin sp.n, ((A.pool σ).filter (fun x => x.val = i)).dedup.length ≤ 2

/-- **A0.1, admission slots.** In every call at `t`, from every state and with every frame, every
vote of the pools after the call that was not in them before (or every vote, for a restart) has
slot `slot(t) − 1` or `slot(t)`. (The claims state it for lawful calls from reachable states.) -/
def AdmissionSlots : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : SAState sp.n)
    (Φ' : Frm sp.n FGP) (t : Time) (c : (goldilocksSA sp FGP ro).Call),
    let A' : SAState sp.n := ((goldilocksSA sp FGP ro).step self A Φ' t c).1
    ∀ σ, ∀ x ∈ A'.pool σ, (x ∈ A.pool σ ∧ c ≠ .restart) ∨
      x.slot + 1 = sp.slot t ∨ x.slot = sp.slot t

/-- **A0.1, stamps.** A lawful call other than a restart, from a reachable state, changes no
stamp that is set (finite or `−∞`): a stamp never changes between two restarts. -/
def StampStable : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP),
    (goldilocksSA sp FGP ro).AtReachable fun self U (A : SAState sp.n) Φ t₀ =>
    ∀ (c : (goldilocksSA sp FGP ro).Call) Φ' t, t₀ ≤ t →
      (goldilocksSA sp FGP ro).CallOK U Φ t c Φ' →
      c ≠ .restart →
      let A' : SAState sp.n := ((goldilocksSA sp FGP ro).step self A Φ' t c).1
      (∀ x, A.voteStamp x ≠ ⊤ → A'.voteStamp x = A.voteStamp x) ∧
        ∀ r, A.blockStamp r ≠ ⊤ → A'.blockStamp r = A.blockStamp r

/-- **A0.1, carried votes.** When a block `B` with a valid payload is processed at `t` with
`slot(t) = B.slot`, from every state and with every frame, a vote of `B.votes` that is not in the
pool after `ac_on_block` makes its validator an equivocator in that pool. (The claims state it for
a lawful block call from a reachable state; its lawfulness gives the valid payload.) -/
def CarriedVotes : Prop :=
  ∀ (FGP : Type) (self : Fin sp.n) (A : SAState sp.n) (Φ' : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP), validPayload B → sp.slot t = B.slot →
    let A' : SAState sp.n := (acOnBlock sp self A Φ' t B).1
    ∀ v ∈ blockVotes B, v ∉ A'.pool v.slot → v.val ∈ equivocators {x | x ∈ A'.pool v.slot}

/-- **A0.1, stamps along parent edges.** At a reachable state, the stamp of a block of the
frame tree is at least the stamp of its parent in the tree (so a voter block tree is closed
under ancestors). -/
def StampParent : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP),
    (goldilocksSA sp FGP ro).AtReachable fun _ _ (A : SAState sp.n) Φ _ =>
    ∀ B ∈ Φ.tree, ∀ Pa ∈ Φ.tree, B.parent = some Pa.root →
      A.blockStamp Pa.root ≤ A.blockStamp B.root

/-- **A0.2, resolution is stable.** From a reachable state, along lawful calls with no restart
in between: a resolved vote (finite resolution time) whose head is in the later frame's tree
has the same resolution time at the later state and frame. -/
def ResolutionStable : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP),
    (goldilocksSA sp FGP ro).AtReachable fun self U (A : SAState sp.n) Φ t₀ =>
    ∀ (A' : SAState sp.n) Φ' t',
      Relation.ReflTransGen
        (fun p q => ∃ c, c ≠ ACInterface.Call.restart ∧
          (goldilocksSA sp FGP ro).CallStep self U p c q) (A, Φ, t₀) (A', Φ', t') →
      ∀ v : Vote sp.n, resolutionTime A Φ v ≠ ⊤ → InTree Φ' v.head →
        resolutionTime A' Φ' v = resolutionTime A Φ v

/-- **A0.2, support heads and the opponents of `Φ.F`.** In a well-formed frame, the support
votes of every vote view and of every merged view have their heads in the tree, so in such a
view the opponents of `Φ.F` (against any slot) are exactly the equivocators. -/
def SupportInTree : Prop :=
  ∀ (FGP : Type) (A : SAState sp.n) (Φ : Frm sp.n FGP), FrameOK Φ →
    (∀ (σ : Int) (cutoff : ETime) (s' : Int),
      (∀ x ∈ (voteView A Φ σ cutoff).support, InTree Φ x.head) ∧
      opponents sp Φ (voteView A Φ σ cutoff) s' Φ.F = equivocators (voteView A Φ σ cutoff).votes) ∧
    ∀ (s : Nat) (s' : Int),
      (∀ x ∈ (mergedVoteView sp A Φ s).support, InTree Φ x.head) ∧
      opponents sp Φ (mergedVoteView sp A Φ s) s' Φ.F =
        equivocators (mergedVoteView sp A Φ s).votes

/-- **A0.3, supporters.** In any view, the supporters of an ancestor include those of a
descendant. -/
def SupportersAntitone : Prop :=
  ∀ (FGP : Type) (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (B C : Blk sp.n FGP),
    Φ.Anc B C → supporters Φ V s C ⊆ supporters Φ V s B

/-- **A0.3, opponents.** In any view and well-formed frame, the opponents of an ancestor are
opponents of a descendant. -/
def OpponentsMonotone : Prop :=
  ∀ (FGP : Type) (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (B C : Blk sp.n FGP),
    FrameOK Φ → Φ.Anc B C → opponents sp Φ V s B ⊆ opponents sp Φ V s C

/-- **A0.3, majority blocks.** In a well-formed frame and a view whose support is among its
votes, the blocks of the tree whose supporters are a strict majority of the voters lie on one
chain. -/
def MajorityChain : Prop :=
  ∀ (FGP : Type) (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (B C : Blk sp.n FGP),
    FrameOK Φ → V.support ⊆ V.votes → B ∈ Φ.tree → C ∈ Φ.tree →
    (voters V.votes).ncard < 2 * (supporters Φ V s B).ncard →
    (voters V.votes).ncard < 2 * (supporters Φ V s C).ncard → Compatible Φ.tree B C

/-- **A0.3, optimistic blocks.** In a well-formed frame, if fewer than `n/2` validators
equivocate in the slot-`s` pool, the blocks of the tree with three quarters of the committee as
optimistic voters lie on one chain. -/
def OptimisticChain : Prop :=
  ∀ (FGP : Type) (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat) (B C : Blk sp.n FGP),
    FrameOK Φ → 2 * (equivocators {x | x ∈ A.pool s}).ncard < sp.n → B ∈ Φ.tree → C ∈ Φ.tree →
    3 * sp.n ≤ 4 * (optimisticVoters sp A Φ s B).ncard →
    3 * sp.n ≤ 4 * (optimisticVoters sp A Φ s C).ncard → Compatible Φ.tree B C

/-- **A0.3, the merged view's opponents.** At a reachable state whose last call is in slot
`σ + 1`, at the same frame, every opponent in the merged view of a slot-`(σ+1)` voter is an
opponent in `vote_view(𝒜, Φ, σ, +∞)` (against the slot-`σ` votes). -/
def MergedOpponents : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP),
    (goldilocksSA sp FGP ro).AtReachable fun _ _ (A : SAState sp.n) Φ t₀ =>
    ∀ (σ : Nat) (B : Blk sp.n FGP), sp.slot t₀ = σ + 1 →
      opponents sp Φ (mergedVoteView sp A Φ (σ + 1)) σ B ⊆ opponents sp Φ (voteView A Φ σ ⊤) σ B

/-- **A0.4 (a), (b), the live locks.** At a reachable state and every time, the blocks of the
live locks lie on one chain, and each is in the viable tree or at or below `fc_root`. -/
def LiveLocksChain : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP),
    (goldilocksSA sp FGP ro).AtReachable fun _ _ (A : SAState sp.n) Φ _ =>
    ∀ t,
      (∀ B ∈ liveLockBlocks sp A.locks Φ t, ∀ C ∈ liveLockBlocks sp A.locks Φ t,
        Compatible Φ.tree B C) ∧
      ∀ B ∈ liveLockBlocks sp A.locks Φ t, B ∈ Φ.viableTree Φ.tree ∨ Φ.Anc B Φ.fcRoot

/-- `L'` moves the locks of `L` only back: each lock of `L'` has the slot, the fast bit and the
expiry of a lock of `L` and its block is an ancestor of that lock's block (both in the tree). -/
def MovesBack {FGP : Type} (Φ : Frm sp.n FGP) (L L' : Set Lock) : Prop :=
  ∀ l' ∈ L', ∃ l ∈ L, l'.slot = l.slot ∧ l'.fast = l.fast ∧ l'.expiry = l.expiry ∧
    ∃ B ∈ Φ.tree, B.root = l.block ∧ ∃ B' ∈ Φ.tree, B'.root = l'.block ∧ Φ.Anc B' B

/-- **A0.4 (c), locks only move back.** In a well-formed frame, `live_locks`, `add_locks` (from
the stored locks with the new ones) and `unlock` move a lock only to an ancestor and keep its
slot, fast bit and expiry. -/
def LocksMoveBack : Prop :=
  ∀ (FGP : Type) (Φ : Frm sp.n FGP) (L : Set Lock) (t : Time), FrameOK Φ →
    MovesBack sp Φ L (liveLocks sp L Φ t) ∧
    (∀ (s : Nat) (N : Set (Nat × Bool × Nat)),
      MovesBack sp Φ (L ∪ {l | ∃ p ∈ N, l = ⟨p.1, s, p.2.1, p.2.2⟩}) (addLocks sp L Φ t s N)) ∧
    ∀ (s : Int) (V : View sp.n), MovesBack sp Φ L (unlock sp L Φ t s V)

/-- **A0.4 (d), unlocking is idempotent** for a fixed frame, slot, view and time. -/
def UnlockIdempotent : Prop :=
  ∀ (FGP : Type) (Φ : Frm sp.n FGP) (L : Set Lock) (t : Time) (s : Int) (V : View sp.n),
    FrameOK Φ → unlock sp (unlock sp L Φ t s V) Φ t s V = unlock sp L Φ t s V

/-- **A0.4 (e), no fallback.** In a well-formed frame and any view, if fewer than `n/2`
validators equivocate then `Φ.F` has fewer than half of the committee as opponents (so `unlock`
never falls back to `Φ.F` for want of a block). -/
def UnlockNoFallback : Prop :=
  ∀ (FGP : Type) (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int), FrameOK Φ →
    2 * (equivocators V.votes).ncard < sp.n →
      2 * (opponents sp Φ V s Φ.F).ncard < sp.n

/-- **A0.4 (f), the FG candidates.** At a reachable state and every time, the candidates of
`ac_to_fg` lie on one chain and the anchor extends each of them. -/
def CandidatesChain : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP),
    (goldilocksSA sp FGP ro).AtReachable fun _ _ (A : SAState sp.n) Φ _ =>
    ∀ t,
      (∀ B ∈ toFGCandidates sp A Φ t, ∀ C ∈ toFGCandidates sp A Φ t, Compatible Φ.tree B C) ∧
      ∀ B ∈ toFGCandidates sp A Φ t, Φ.Anc B (getAnchor sp A Φ t)

/-- **A0.5, lock to tip.** At a reachable state and every time, every block of a live lock is
an ancestor of the effective record: `latest_confirmed` when it is in the tree, else `Φ.F`. -/
def LockToTip : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP),
    (goldilocksSA sp FGP ro).AtReachable fun _ _ (A : SAState sp.n) Φ _ =>
    ∀ t, ∀ B ∈ liveLockBlocks sp A.locks Φ t,
      Φ.Anc B ((lookup Φ A.latestConfirmed).getD Φ.F)

/-- **A0.6, the interface requirements 1–4** of composition.tex §"The available chain", for the
Goldilocks SA, at every reachable state. -/
def InterfaceRequirements : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP), (goldilocksSA sp FGP ro).ReqHeads ∧
    (goldilocksSA sp FGP ro).ReqSource ∧ (goldilocksSA sp FGP ro).ReqOutputs ∧
    (goldilocksSA sp FGP ro).ReqParent

/-- **A0.7, restart.** After `ac_restart` at `t ≥ 0` with a well-formed frame: the locks and
`latest_confirmed` are kept; the saved results, `fg_reported` and `voted_slot` are initial;
`restart_time = t`; the pools hold only votes of blocks of the tree, stamped `t`; every vote
stamp is `t` or unset; every block stamp is initial or `t` for a non-genesis block of the tree;
the node is not joined at `t`, so the replay sends nothing. -/
def RestartState : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time), FrameOK Φ → 0 ≤ t →
    let r := acRestart sp ro self A Φ t
    let I : SAState sp.n := SAState.initial sp.genesisRoot
    r.2 = [] ∧ r.1.locks = A.locks ∧ r.1.latestConfirmed = A.latestConfirmed ∧
    r.1.saved = I.saved ∧ r.1.fgReported = I.fgReported ∧ r.1.votedSlot = I.votedSlot ∧
    r.1.restartTime = (t : WithBot Time) ∧ ¬ joined sp r.1 t ∧
    (∀ σ, ∀ x ∈ r.1.pool σ, r.1.voteStamp x = ETime.of t ∧ ∃ B ∈ Φ.tree, x ∈ blockVotes B) ∧
    (∀ x, r.1.voteStamp x = ⊤ ∨ r.1.voteStamp x = ETime.of t) ∧
    ∀ q, r.1.blockStamp q = I.blockStamp q ∨
      (r.1.blockStamp q = ETime.of t ∧ q ≠ sp.genesisRoot ∧ InTree Φ q)

/-- **A0.7, joining.** In an AC trace with its contract: an honest node that is joined after a
call at `t` erased, at each of its restarts, no vote of slot `slot(t) − 1` or later. -/
def JoinedKeepsVotes : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro),
    ACLocalRun (goldilocksSA sp FGP ro) H U tr → ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ →
      joined sp (tr.post i) (tr.time i) → ∀ j ≤ i, tr.RestartAt y j →
        ∀ σ, ∀ x ∈ (tr.state y j : SAState sp.n).pool σ,
          (x.slot : Int) < (sp.slot (tr.time i) : Int) - 1

/-- **A0.8, one vote per slot.** In an AC trace with its contract, an honest node casts at most
one vote per slot, also across restarts. -/
def OneVotePerSlot : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro),
    ACLocalRun (goldilocksSA sp FGP ro) H U tr → ∀ y ∈ H, ∀ i j e e',
      VoteAt tr y i e → VoteAt tr y j e' → e.msg.slot = e'.msg.slot → i = j ∧ e = e'

/-- **A0.9, the proposal payload is valid** (requirement 5) for the Goldilocks SA, at every
reachable state. -/
def ProposalPayloadValid : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP), (goldilocksSA sp FGP ro).ReqPayload

/-- The ACBase statements, for the SA parameters `sp`. -/
structure ACBaseAt : Prop where
  slotArithmetic : SlotArithmetic sp
  lockExpiry : LockExpiry sp
  joinedFrom : JoinedFrom sp
  joinedAwake : JoinedAwake sp
  poolCap : PoolCap sp
  admissionSlots : AdmissionSlots sp
  stampStable : StampStable sp
  carriedVotes : CarriedVotes sp
  stampParent : StampParent sp
  resolutionStable : ResolutionStable sp
  supportInTree : SupportInTree sp
  supportersAntitone : SupportersAntitone sp
  opponentsMonotone : OpponentsMonotone sp
  majorityChain : MajorityChain sp
  optimisticChain : OptimisticChain sp
  mergedOpponents : MergedOpponents sp
  liveLocksChain : LiveLocksChain sp
  locksMoveBack : LocksMoveBack sp
  unlockIdempotent : UnlockIdempotent sp
  unlockNoFallback : UnlockNoFallback sp
  candidatesChain : CandidatesChain sp
  lockToTip : LockToTip sp
  interfaceRequirements : InterfaceRequirements sp
  restartState : RestartState sp
  joinedKeepsVotes : JoinedKeepsVotes sp
  oneVotePerSlot : OneVotePerSlot sp
  proposalPayloadValid : ProposalPayloadValid sp

/-- **Milestone ACBase**: the ACBase statements for all SA parameters. -/
def ACBase : Prop := ∀ sp : SAParams, ACBaseAt sp

end Consensus.Goldilocks.SA

namespace Consensus.Goldilocks

/-- **The AC trace contract gives reachable states** (decomposition §2 D; not a claims node): in
an AC trace with its contract, the state an honest node's call leaves is reachable inside `U`,
with the call's frame and time. -/
def LocalRunReachable : Prop :=
  ∀ (P : Params) (FGP : Type) (A : ACInterface P FGP) (H : Set (Fin P.n)) (U : Set A.Blk)
    (tr : ACTrace A), ACLocalRun A H U tr →
      ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ → A.ReachableAt y U (tr.post i) ℓ.frame (tr.time i)

end Consensus.Goldilocks

end
