module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Base
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Steps
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Growing

@[expose] public section

/-! # Goldilocks milestones ACBase and ACSteps under growing faults (statements)

The statements of `Statements/AC/{Base,Steps}` that bind the honest set, for a time-indexed
honest set `H` (antitone), over `Growing.ACLocalRun` / `SA.Growing.ACRun`:

* a node named at a cut is honest at that cut's time; a vote or a lock write is by a node honest
  at its own cut (an event fact, kept after a later compromise); A1.1 reads the proposer at the
  later of its proposal and the vote it is compared with;
* every count is charged at the cut that performs it: `SA.FaultBoundAt tr H t t` at a vote
  (`f_t < h_t`), `2 f_t < n` at the voter's cut for the optimistic transfer, at the update's cut
  for the next update, and at the `ac_to_fg` call for source compatibility; the honest voters of
  the next transfer are those honest at the voter's cut that voted in the slot while honest (a
  vote emitted after its voter's compromise is not an honest vote, whatever the voter's honesty
  at another time);
* the network premise is `SyncACAt`.

The statements without an honest set (the pure SA facts of ACBase) are unchanged and are not
restated. At `H := fun _ => H₀` each statement here implies its static counterpart.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.SA.Growing

variable (sp : SAParams)

/-- **F.1 (c), a joined node**, for a node honest at its call. -/
def JoinedAwake : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro),
    Consensus.Goldilocks.Growing.ACLocalRun (goldilocksSA sp FGP ro) H U tr →
    ∀ y i ℓ, y ∈ H (tr.time i) → tr.CallAt y i ℓ → joined sp (tr.post i) (tr.time i) →
      (∀ u : Time, max 0 (sp.ts ((sp.slot (tr.time i) : Int) - 1)) ≤ u → u ≤ tr.time i →
        tr.awake y u) ∧
      ∀ j ≤ i, tr.RestartAt y j → tr.time j ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1)

/-- **A0.7, joining**, for a node honest at its call. -/
def JoinedKeepsVotes : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro),
    Consensus.Goldilocks.Growing.ACLocalRun (goldilocksSA sp FGP ro) H U tr →
    ∀ y i ℓ, y ∈ H (tr.time i) → tr.CallAt y i ℓ → joined sp (tr.post i) (tr.time i) →
      ∀ j ≤ i, tr.RestartAt y j → ∀ σ, ∀ x ∈ (tr.state y j : SAState sp.n).pool σ,
        (x.slot : Int) < (sp.slot (tr.time i) : Int) - 1

/-- **A0.8, one vote per slot**, for a node honest at the later of its two votes. -/
def OneVotePerSlot : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro),
    Consensus.Goldilocks.Growing.ACLocalRun (goldilocksSA sp FGP ro) H U tr →
    ∀ y i j e e', y ∈ H (max (tr.time i) (tr.time j)) →
      VoteAt tr y i e → VoteAt tr y j e' → e.msg.slot = e'.msg.slot → i = j ∧ e = e'

/-- **A1.1 under growing faults**: the voter honest at its vote cut, the proposer honest at the
later of the proposal and vote cuts (a proposer compromised after its proposal and before the vote
can equivocate with a second proposal of the slot, whose votes the voter's merged view admits). -/
def ProposerVotersAgree : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro) (proposer : Nat → Fin sp.n),
    ACRun proposer tr H U → ∀ (s : Nat) (p y : Fin sp.n) (i j : Nat)
      (ℓp ℓy : ACLabel (goldilocksSA sp FGP ro))
      (pay : Payload sp.n) (e : Em sp FGP),
    p ∈ H (max (tr.time i) (tr.time j)) → y ∈ H (tr.time j) → p = proposer (s + 1) →
    ProposalAt tr p i ℓp pay → tr.time i = sp.ts (s + 1 : Nat) →
    CastAt tr y j ℓy e → e.msg.slot = s + 1 →
    (∃ P ∈ ℓy.frame.tree, P.slot = s + 1 ∧ P.acPayload = pay) →
    SyncACAt (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat)) tr →
    {X | X ∈ ℓp.frame.tree ∧ X.slot ≤ s} = {X | X ∈ ℓy.frame.tree ∧ X.slot ≤ s} →
    ∀ B ∈ ℓp.frame.tree, B.slot ≤ s →
      opponents sp ℓp.frame (View.ofLists pay) s B =
        opponents sp ℓy.frame (mergedVoteView sp e.readPoint ℓy.frame (s + 1)) s B

/-- **A1.2 under growing faults, first transfer (per vote).** The writer is honest at its
write, the voter at its vote; the count `f < h` among the slot-`s` committee and
`2f < committeeSize` among the slot-`(s+1)` committee are charged at the vote. The slot committee
`K` has `committeeSize` members per slot, and its members sign the votes held by the nodes honest
at each time `t` at the cuts through `t` (`CommitteePAt`, `CommitteeTAt`). -/
def FirstTransfer : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro) (proposer : Nat → Fin sp.n),
    ACRun proposer tr H U →
    ∀ (K : CommitteeDict sp.n), CommitteePAt K tr H → CommitteeTAt K tr H →
      (∀ σ, (K.committee σ).ncard = sp.committeeSize) →
    ∀ (s : Nat) (x y : Fin sp.n) (i₀ i : Nat) (B : Blk sp.n FGP)
      (CV : Set (Vote sp.n)) (ℓ : ACLabel (goldilocksSA sp FGP ro)) (e : Em sp FGP),
    x ∈ H (tr.time i₀) → FastLockAt tr x i₀ s B CV →
    y ∈ H (tr.time i) → CastAt tr y i ℓ e → e.msg.slot = s + 1 →
    SyncACAt (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr →
    CarryAt tr U y i e s CV → FaultBoundK K s tr (H (tr.time i)) (tr.time i) →
    2 * (K.committee (s + 1) ∩ (H (tr.time i))ᶜ).ncard < sp.committeeSize →
    ViableAtVote ℓ e (s + 1) B → EarlierVotesExtendAt tr H U i (s + 1) B →
    VoteExtends U e.msg B

/-- **A1.3 under growing faults, next transfer (per vote).** The votes of slot `m` are those of
nodes honest at their votes; the honest voters of slot `m` are the validators honest at the
voter's cut that voted in slot `m` while honest, and `f < h` among the slot-`m` committee and
`2f < committeeSize` among the slot-`(m+1)` committee are charged there; the slot committee `K` is
as in A1.2. -/
def NextTransfer : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro) (proposer : Nat → Fin sp.n),
    ACRun proposer tr H U →
    ∀ (K : CommitteeDict sp.n), CommitteePAt K tr H → CommitteeTAt K tr H →
      (∀ σ, (K.committee σ).ncard = sp.committeeSize) →
    ∀ (m : Nat) (y : Fin sp.n) (i : Nat) (B : Blk sp.n FGP)
      (ℓ : ACLabel (goldilocksSA sp FGP ro)) (e : Em sp FGP),
    y ∈ H (tr.time i) → CastAt tr y i ℓ e → e.msg.slot = m + 1 →
    (∀ x j e', x ∈ H (tr.time j) → VoteAt tr x j e' → e'.msg.slot = m →
      VoteExtends U e'.msg B) →
    sp.committeeSize ≤ 2 * {x | x ∈ H (tr.time i) ∧
      ∃ j e', x ∈ H (tr.time j) ∧ VoteAt tr x j e' ∧ e'.msg.slot = m}.ncard →
    CarryAt tr U y i e m
      {v | ∃ x j e', x ∈ H (tr.time j) ∧ VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = m} →
    FaultBoundK K m tr (H (tr.time i)) (tr.time i) →
    2 * (K.committee (m + 1) ∩ (H (tr.time i))ᶜ).ncard < sp.committeeSize →
    ViableAtVote ℓ e (m + 1) B → EarlierVotesExtendAt tr H U i (m + 1) B →
    VoteExtends U e.msg B

/-- **A1.4 (a) under growing faults, optimistic is fast: the transfer (per vote).**
`2f < committeeSize` among the slot-`s` and the slot-`(s+1)` committees is charged at the voter's
cut; the slot committee `K` is as in A1.2. -/
def OptimisticTransfer : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro) (proposer : Nat → Fin sp.n),
    ACRun proposer tr H U →
    ∀ (K : CommitteeDict sp.n), CommitteePAt K tr H → CommitteeTAt K tr H →
      (∀ σ, (K.committee σ).ncard = sp.committeeSize) →
    ∀ (s : Nat) (x y : Fin sp.n) (i₀ i : Nat) (B : Blk sp.n FGP)
      (CV : Set (Vote sp.n)) (ℓ : ACLabel (goldilocksSA sp FGP ro)) (e : Em sp FGP),
    x ∈ H (tr.time i₀) → OptimisticLockAt tr x i₀ s B CV →
    2 * (K.committee s ∩ (H (tr.time i))ᶜ).ncard < sp.committeeSize →
    2 * (K.committee (s + 1) ∩ (H (tr.time i))ᶜ).ncard < sp.committeeSize →
    y ∈ H (tr.time i) → CastAt tr y i ℓ e → e.msg.slot = s + 1 →
    CarryAt tr U y i e s CV →
    ViableAtVote ℓ e (s + 1) B → EarlierVotesExtendAt tr H U i (s + 1) B →
    VoteExtends U e.msg B

/-- **A1.4 (b) under growing faults, the next update.** `2f < committeeSize` among the
slot-`(s+1)` committee and the honest voters of the
updater's pool are read at the update's cut; the votes of slot `s + 1` are those of nodes honest
at their votes; the slot committee `K` is as in A1.2. -/
def OptimisticNextUpdate : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro) (proposer : Nat → Fin sp.n),
    ACRun proposer tr H U →
    ∀ (K : CommitteeDict sp.n), CommitteePAt K tr H → CommitteeTAt K tr H →
      (∀ σ, (K.committee σ).ncard = sp.committeeSize) →
    ∀ (s : Nat) (z : Fin sp.n) (k : Nat) (B : Blk sp.n FGP)
      (ℓ : ACLabel (goldilocksSA sp FGP ro)),
    2 * (K.committee (s + 1) ∩ (H (tr.time k))ᶜ).ncard < sp.committeeSize →
    (∀ x' j e, x' ∈ H (tr.time j) → VoteAt tr x' j e → e.msg.slot = s + 1 →
      VoteExtends U e.msg B) →
    z ∈ H (tr.time k) → UpdateAt tr z k (s + 1) ℓ →
    sp.committeeSize ≤ 2 *
      {v | v ∈ H (tr.time k) ∧ ∃ x' ∈ (tr.state z k).pool (s + 1), x'.val = v}.ncard →
    (∀ x' ∈ (tr.state z k).pool (s + 1), x'.val ∈ H (tr.time k) →
      resolutionTime (tr.state z k) ℓ.frame x' < ETime.of (sp.ts (s + 1 : Nat) + 2 * sp.Δ)) →
    ∃ C, getConfirmation sp (tr.state z k) ℓ.frame (s + 1) = some C ∧ Anc U B C ∧
      (B.root ≠ sp.genesisRoot →
        ∃ D, fastSelect sp (tr.state z k) ℓ.frame (s + 1) C = some D ∧ Anc U B D)

/-- **A1.5 under growing faults, source age**, for a node honest at its `ac_to_fg` call. -/
def SourceAge : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro),
    Consensus.Goldilocks.Growing.ACLocalRun (goldilocksSA sp FGP ro) H U tr →
    ∀ (τ : Time) (x : Fin sp.n) (i : Nat) (ℓ : ACLabel (goldilocksSA sp FGP ro))
      (C : Blk sp.n FGP),
    x ∈ H (tr.time i) → ToFGAt tr x i ℓ C → sp.slot τ + 3 ≤ sp.slot (tr.time i) →
    ∃ j ≤ i, ∃ s' B' CV', FastLockAt tr x j s' B' CV' ∧ τ < tr.time j ∧
      sp.slot (tr.time i) ≤ s' + 2 ∧ Anc U C B'

/-- **A1.8 under growing faults, result transfer (per vote).** The writer is honest at its
update, the voter at its vote; no participation bound. -/
def ResultTransfer : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro) (proposer : Nat → Fin sp.n),
    ACRun proposer tr H U → ∀ (s : Nat) (X y : Fin sp.n) (i₀ i : Nat) (C : Blk sp.n FGP)
      (CV : Set (Vote sp.n)) (ℓ : ACLabel (goldilocksSA sp FGP ro)) (e : Em sp FGP),
    X ∈ H (tr.time i₀) → ResultAt tr X i₀ s C CV →
    y ∈ H (tr.time i) → CastAt tr y i ℓ e → e.msg.slot = s + 1 →
    CarryAt tr U y i e s CV → ViableAtVote ℓ e (s + 1) C →
    (∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L C) →
    (∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s}) →
    VoteExtends U e.msg C

/-- **A1.9 under growing faults, source compatibility after the cut (per call).** The writer is
honest at its write; `2f < n` is charged at the `ac_to_fg` call; the votes of slots in `(s, m]`
are those of nodes honest at their votes. -/
def SourceCompatible : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro) (proposer : Nat → Fin sp.n),
    sp.committeeSize = sp.n →
    ACRun proposer tr H U → ∀ (s m : Nat) (w x : Fin sp.n) (i₀ i : Nat) (B : Blk sp.n FGP)
      (CV : Set (Vote sp.n)) (ℓ : ACLabel (goldilocksSA sp FGP ro)) (C : Blk sp.n FGP),
    w ∈ H (tr.time i₀) → FastLockAt tr w i₀ s B CV →
    SyncACAt (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) tr →
    Carry tr H U s CV → 2 * (H (tr.time i))ᶜ.ncard < sp.n →
    x ∈ H (tr.time i) → ToFGAt tr x i ℓ C →
    sp.ts (s + 1 : Nat) + sp.Δ < tr.time i → tr.time i ≤ sp.ts m + sp.Δ →
    (∀ z j, j < i → z ∈ H (tr.time j) → ∀ e, VoteAt tr z j e → s < e.msg.slot →
      e.msg.slot ≤ m → VoteExtends U e.msg B) →
    ((∃ j < i, ∃ ℓ' e, CastAt tr x j ℓ' e ∧ e.msg.slot = s + 1 ∧ Compatible U ℓ'.frame.F B) ∨
      (∃ k < i, tr.RestartAt x k ∧ sp.ts s < tr.time k)) →
    Compatible U C B

/-- The ACSteps statements under growing faults, for the SA parameters `sp`. -/
structure ACStepsAt : Prop where
  proposerVotersAgree : ProposerVotersAgree sp
  firstTransfer : FirstTransfer sp
  nextTransfer : NextTransfer sp
  optimisticTransfer : OptimisticTransfer sp
  optimisticNextUpdate : OptimisticNextUpdate sp
  sourceAge : SourceAge sp
  resultTransfer : ResultTransfer sp
  sourceCompatible : SourceCompatible sp

/-- **Milestone ACSteps under growing faults**, for population-sized committees. -/
def ACSteps : Prop := ∀ sp : SAParams, ACStepsAt sp

end Consensus.Goldilocks.SA.Growing

namespace Consensus.Goldilocks.Growing

/-- **The AC trace contract gives reachable states**, for a node honest at its call. -/
def LocalRunReachable : Prop :=
  ∀ (P : Params) (FGP : Type) (A : ACInterface P FGP) (H : Time → Set (Fin P.n)) (U : Set A.Blk)
    (tr : ACTrace A), Growing.ACLocalRun A H U tr →
      ∀ y i ℓ, y ∈ H (tr.time i) → tr.CallAt y i ℓ →
        A.ReachableAt y U (tr.post i) ℓ.frame (tr.time i)

end Consensus.Goldilocks.Growing

end
