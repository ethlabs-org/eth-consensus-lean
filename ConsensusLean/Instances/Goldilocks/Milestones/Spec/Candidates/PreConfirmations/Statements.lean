module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Candidates.PreConfirmations.Projection
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.WeightedEm

@[expose] public section

/-! # ½ pre-confirmations: the statements of the layer's facts

The facts the layer is checked against, as `Prop`s; each is proved in
`Lemmas/Candidates/PreConfirmations` by a theorem of the same name, lower camel case. None needs a
settling argument: they are about one store, one call, or the run's acks.

**The one release.**
* `OneReleaseScan`: the code's scan (the deepest ancestor `Y` of the lock's block with
  `|evidence(Y)| < min(W(Y), μ_r)`, else `Φ.F`) is the stage's target from the parent's unlock
  target. That the stage is lawful (`UnlockStage.Lawful`, with the keep premise "the evidence lies
  in a set of fewer validators than `min(W(Y), μ_r)`") and fixes its own choice
  (`UnlockStage.Fixes`, every lock) is stated over the lock-rule laws of `Lemmas/AC/LockRule`, so
  it is not a `Prop` here.

**The core runs its own update functions at the PC's start (E2).** The PC adds no write mechanism:
the core's writes are the same update functions, on the PC-selected vote. They are not in general
equal to the core's writes at the parent's start (the own vote's head can differ, and it enters the
pool before the same call's optimistic confirmation).
* `AckCallCoreId`: an ack receipt leaves the core state as it is and emits nothing;
* `ParentStartIsCore`: the core skeleton with the parent's start is the core's handlers at mode
  `m` and stage `E` (`Candidates/EvidenceRelease`);
* `CoreStepAtCallStart`: every other call's core result and forgotten emissions are the core
  skeleton's at the call's named start `callStartPC` (the PC start of the store evaluated after
  the call's record and before the walk);
* `ProposalAtCallStart`: the proposal's core result, duty head and payload are the skeleton's at
  that start (`stepEMAt` keeps only the state of a proposal);
* `CoreStepOfNoKeys`: with no key in `pcs` the start is the parent's anchor, so the call is the
  core's (a conditional equality);
* `RestartResets`: a restart is the core's restart, and the store after it has no ack, key, mark
  or decision, and its vote record is that of the replayed payloads' votes;
* `ProjStateCore`: on an honest node, the forgotten trace's state is the core of the state.

**The store (E4).**
* `RefreshIdem`: evaluating the store twice is evaluating it once (so a cached evaluation and an
  evaluation at every call agree on the same inputs);
* `AuthorityCompatible`: the targets of two authoritative keys are compatible (annihilation);
* `AuthorityWindow`: an authoritative key is in the window;
* `PCProjFacts`: the D21 projection is an ancestor of the target in the tree, the deepest one with
  fewer than `μ` opponents (the code's upward walk), or `Φ.F`;
* `PCBaseFacts`: the base exists exactly when a key is authoritative, and is the deepest
  projection of an authoritative key;
* `PCAnchorFacts`: the PC anchor extends the base and is the base or the deepest live lock block
  extending it;
* `PCPathSameState`: a walk from a block on the walk from `a₀` that extends `a₀` ends where the
  walk from `a₀` ends (so a PC start on the parent's walk changes no head);
* `AckSendsWindow`, `OnAckWindow`, `RecordWindow`: the window arithmetic of the sends, the
  admission and the record;
* `KeyProvenance`: with fewer than `μ` faulty validators, a key in an honest node's `pcs` has an
  honest acker that decided it at its update of the key's slot, with `μ` clean early supporters
  of the target there. -/

namespace Consensus.Goldilocks.PreConfirmations

open SA EvidenceRelease

variable (sp : SAParams) (FGP : Type)

/-! ## The one release -/

/-- **The one release reads the code's scan**: the deepest ancestor `Y` in the tree of the lock's
block `B`, at or above `Φ.F`, with `|evidence(Y)| < min(W(Y), μ_r)`, else `Φ.F`, is the stage's
target from the parent's unlock target of `B`. -/
def OneReleaseScan : Prop :=
  ∀ {Φ : Frm sp.n FGP}, FrameOK Φ → ∀ (V : View sp.n) (s : Int) (w : WLock) (B : Blk sp.n FGP),
    B ∈ Φ.tree →
    (deepest Φ {Y | Y ∈ Φ.tree ∧ Φ.Anc Φ.F Y ∧ Φ.Anc Y B ∧
        (evidence sp Φ V s Y).ncard < min (w.weight Y.root) (releaseMu sp)}).getD Φ.F =
      oneReleaseTarget sp Φ V s w (unlockTarget sp Φ V s B)

section Calls

variable {σ : Type} (E : UnlockStage sp wlockStore σ) (c : σ) (m : WriteMode)
  (ro : ReplayOrder sp FGP)

/-! ## The core (E2) -/

/-- **An ack receipt is a core identity**: the core is unchanged, the store takes `onAck`, and
nothing is emitted. -/
def AckCallCoreId : Prop :=
  ∀ (self : Fin sp.n) (X : PCState sp.n) (Φ : Frm sp.n FGP) (t : Time) (a : Ack sp.n),
    (preConfSAM sp E c m FGP ro).step self X Φ t (.message (.inr a)) =
      (⟨X.core, onAck sp X.store t a⟩, [])

/-- **The skeleton at the parent's start is the core**: each handler with the walk from the
parent's anchor is the weighted handler at mode `m` and stage `E`. -/
def ParentStartIsCore : Prop :=
  ∀ (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time),
    (∀ v, acOnMessageEMAt sp E c m (parentStart sp Φ t) self X Φ t v =
      acOnMessageEM sp E c m self X Φ t v) ∧
    (∀ B, acOnBlockEMAt sp E c m (parentStart sp Φ t) self X Φ t B =
      acOnBlockEM sp E c m self X Φ t B) ∧
    acOnTickEMAt sp E c m (parentStart sp Φ t) self X Φ t = acOnTickEM sp E c m self X Φ t ∧
    acProposalEAt sp E c (parentStart sp Φ t) X Φ t = acProposalE sp E c X Φ t ∧
    acRestartEMAt sp E c m (parentStart sp Φ t) ro self X Φ t = acRestartEM sp E c m ro self X Φ t

/-- **The core at the call's start**: every call other than an ack receipt has, on the core, the
result and the forgotten emissions of the core skeleton at the call's start `callStartPC`. -/
def CoreStepAtCallStart : Prop :=
  ∀ (self : Fin sp.n) (X : PCState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (k : (preConfSAM sp E c m FGP ro).Call) (k' : (goldilocksSA sp FGP ro).Call),
    projCallPC E c m ro k = some k' →
      ((preConfSAM sp E c m FGP ro).step self X Φ t k).1.core =
        (stepEMAt sp E c m ro (callStartPC sp X Φ t k') self X.core Φ t k').1 ∧
      ((preConfSAM sp E c m FGP ro).step self X Φ t k).2.filterMap projEmPC =
        (stepEMAt sp E c m ro (callStartPC sp X Φ t k') self X.core Φ t k').2.map projEm

/-- **The proposal at its start**: the proposal's core result, and its duty head (head, start and
domain) and payload, are the skeleton's at the PC start of the store evaluated at the call. -/
def ProposalAtCallStart : Prop :=
  ∀ (X : PCState sp.n) (Φ : Frm sp.n FGP) (t : Time),
    (acProposalPC sp E c X Φ t).1.core =
        (acProposalEAt sp E c (callStartPC (ro := ro) sp X Φ t .proposal) X.core Φ t).1 ∧
      (acProposalPC sp E c X Φ t).2 =
        (acProposalEAt sp E c (callStartPC (ro := ro) sp X Φ t .proposal) X.core Φ t).2

/-- **No key, no change**: with no key in `pcs`, every call other than an ack receipt has, on the
core, the core's result and forgotten emissions (the skeleton at the parent's start). -/
def CoreStepOfNoKeys : Prop :=
  ∀ (self : Fin sp.n) (X : PCState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (k : (preConfSAM sp E c m FGP ro).Call) (k' : (goldilocksSA sp FGP ro).Call),
    projCallPC E c m ro k = some k' → X.store.pcs = ∅ →
      ((preConfSAM sp E c m FGP ro).step self X Φ t k).1.core =
        (stepEMAt sp E c m ro (parentStart sp Φ t) self X.core Φ t k').1 ∧
      ((preConfSAM sp E c m FGP ro).step self X Φ t k).2.filterMap projEmPC =
        (stepEMAt sp E c m ro (parentStart sp Φ t) self X.core Φ t k').2.map projEm

/-- **A restart empties the store**: its core result and forgotten emissions are the core's
restart, and the store after it has no ack, key, mark or decision, and its vote record is that of
the replayed blocks' payload votes, recorded in the replay order from the empty store. -/
def RestartResets : Prop :=
  ∀ (self : Fin sp.n) (X : PCState sp.n) (Φ : Frm sp.n FGP) (t : Time),
    ((preConfSAM sp E c m FGP ro).step self X Φ t .restart).1.core =
        (acRestartEM sp E c m ro self X.core Φ t).1 ∧
      ((preConfSAM sp E c m FGP ro).step self X Φ t .restart).2.filterMap projEmPC =
        (acRestartEM sp E c m ro self X.core Φ t).2.map projEm ∧
      ((preConfSAM sp E c m FGP ro).step self X Φ t .restart).1.store.pcs = ∅ ∧
      ((preConfSAM sp E c m FGP ro).step self X Φ t .restart).1.store.valid = ∅ ∧
      ((preConfSAM sp E c m FGP ro).step self X Φ t .restart).1.store.dead = ∅ ∧
      (∀ s X' j, ((preConfSAM sp E c m FGP ro).step self X Φ t .restart).1.store.acks s X' j = ∅) ∧
      (∀ s, ((preConfSAM sp E c m FGP ro).step self X Φ t .restart).1.store.myAcks s = none) ∧
      ((preConfSAM sp E c m FGP ro).step self X Φ t .restart).1.store.votes =
        ((ro.order t Φ).foldl (fun P B => recordVotes sp P t (blockVotes B)) PCStore.empty).votes

/-- **The forgotten state is the core**: on a run of the PC SA, the forgotten trace's state of an
honest node is the core's parent state of its state (an ack receipt is a stutter of the forgotten
trace). -/
def ProjStateCore : Prop :=
  ∀ (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (tr : ACTrace (preConfSAM sp E c m FGP ro)),
    ACLocalRun (preConfSAM sp E c m FGP ro) H U tr →
      ∀ y ∈ H, ∀ i, (projTracePC tr).state y i = (tr.state y i).core.ac

/-! ## Key provenance -/

/-- Honest `v` decides the ack `(s, X)` at its tick cut `i`: it had no decision of slot `s`
before, has `X` after, and `X` has `μ` clean early supporters at the update of slot `s` (the
state after the call). -/
def AckDecidedAt (tr : ACTrace (preConfSAM sp E c m FGP ro)) (v : Fin sp.n) (i s X : Nat) :
    Prop :=
  ∃ ℓ, tr.CallAt v i ℓ ∧ ℓ.call = .tick ∧ (tr.state v i).store.myAcks s = none ∧
    (tr.post i).store.myAcks s = some X ∧
    ∃ B ∈ ℓ.frame.tree, B.root = X ∧ pcMu sp ≤ confirmationScore sp (tr.post i).core.ac ℓ.frame s B

/-- **Key provenance**: with fewer than `μ` faulty validators, a key `(s, X)` in an honest node's
`pcs` before cut `i` was decided by an honest acker at an earlier tick cut. -/
def KeyProvenance : Prop :=
  ∀ (selectedProposer : Nat → Fin sp.n) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : ACTrace (preConfSAM sp E c m FGP ro)),
    ACLocalRun (preConfSAM sp E c m FGP ro) H U tr → HonestObjectsPC selectedProposer tr H →
    (Hᶜ).ncard < pcMu sp →
    ∀ y ∈ H, ∀ i (s X : Nat), (s, X) ∈ (tr.state y i).store.pcs →
      ∃ v ∈ H, ∃ i' < i, AckDecidedAt sp FGP E c m ro tr v i' s X

end Calls

/-! ## The store (E4) -/

/-- **Evaluation is idempotent.** -/
def RefreshIdem : Prop :=
  ∀ (P : PCStore sp.n) (Φ : Frm sp.n FGP) (t : Time),
    refresh sp (refresh sp P Φ t) Φ t = refresh sp P Φ t

/-- **Authoritative targets are compatible.** -/
def AuthorityCompatible : Prop :=
  ∀ (P : PCStore sp.n) (Φ : Frm sp.n FGP) (t : Time), ∀ k ∈ authority sp P Φ t,
    ∀ k' ∈ authority sp P Φ t, ∀ X ∈ Φ.tree, ∀ X' ∈ Φ.tree, X.root = k.2 → X'.root = k'.2 →
      Compatible Φ.tree X X'

/-- **Authoritative keys are in the window.** -/
def AuthorityWindow : Prop :=
  ∀ (P : PCStore sp.n) (Φ : Frm sp.n FGP) (t : Time), ∀ k ∈ authority sp P Φ t, InWindow sp t k

/-- **The D21 projection**: an ancestor of the target in the tree; for a key of slot below the
view's, with fewer than `μ` opponents or `Φ.F`, and every block strictly between it and the
target has `μ` opponents or more (the code's upward walk); every ancestor of the target with fewer
than `μ` opponents is an ancestor of it. -/
def PCProjFacts : Prop :=
  ∀ {Φ : Frm sp.n FGP}, FrameOK Φ → ∀ (V : View sp.n) (b : Int) (s : Nat) (X : Blk sp.n FGP),
    X ∈ Φ.tree →
    pcProj sp Φ V b s X ∈ Φ.tree ∧ Φ.Anc (pcProj sp Φ V b s X) X ∧
    ((s : Int) < b → ((d21Opponents sp Φ V (pcProj sp Φ V b s X)).ncard < pcMu sp ∨
        pcProj sp Φ V b s X = Φ.F) ∧
      ∀ Z ∈ Φ.tree, Φ.Anc (pcProj sp Φ V b s X) Z → Z ≠ pcProj sp Φ V b s X → Φ.Anc Z X →
        pcMu sp ≤ (d21Opponents sp Φ V Z).ncard) ∧
    ∀ Z ∈ Φ.tree, Φ.Anc Z X → (d21Opponents sp Φ V Z).ncard < pcMu sp →
      Φ.Anc Z (pcProj sp Φ V b s X)

/-- **The base**: it exists exactly when a key is authoritative, and it is the projection of an
authoritative key's target, at least as deep as every other. -/
def PCBaseFacts : Prop :=
  ∀ {Φ : Frm sp.n FGP}, FrameOK Φ → ∀ (P : PCStore sp.n) (t : Time) (V : View sp.n) (b : Int),
    (pcBase sp P Φ t V b = none ↔ authority sp P Φ t = ∅) ∧
    ∀ Y, pcBase sp P Φ t V b = some Y →
      ∃ k ∈ authority sp P Φ t, ∃ X ∈ Φ.tree, X.root = k.2 ∧ Y = pcProj sp Φ V b k.1 X ∧
        ∀ k' ∈ authority sp P Φ t, ∀ X' ∈ Φ.tree, X'.root = k'.2 →
          depth Φ (pcProj sp Φ V b k'.1 X') ≤ depth Φ Y

/-- **The PC anchor** of a base `Y` in the tree extends `Y`, is `Y` or a live lock block, and is
at least as deep as every live lock block extending `Y`. -/
def PCAnchorFacts : Prop :=
  ∀ {Φ : Frm sp.n FGP}, FrameOK Φ → ∀ (A : SAState sp.n) (t : Time) (Y : Blk sp.n FGP),
    Y ∈ Φ.tree →
    Φ.Anc Y (pcAnchor sp A Φ t Y) ∧
    (pcAnchor sp A Φ t Y = Y ∨ pcAnchor sp A Φ t Y ∈ liveLockBlocks sp A.locks Φ t) ∧
    ∀ B ∈ liveLockBlocks sp A.locks Φ t, Φ.Anc Y B → depth Φ B ≤ depth Φ (pcAnchor sp A Φ t Y)

/-- **Same-state PC path**: a walk from a block `a₁` that extends `a₀` and lies on the walk from
`a₀` ends where the walk from `a₀` ends. -/
def PCPathSameState : Prop :=
  ∀ {Φ : Frm sp.n FGP}, FrameOK Φ → ∀ (a₀ a₁ : Blk sp.n FGP) (t : Time)
    (tree : Set (Blk sp.n FGP)) (V : View sp.n) (s : Int), tree ⊆ Φ.tree →
    Φ.Anc a₀ a₁ → Φ.Anc a₁ (headFrom sp a₀ Φ t tree V s) →
      headFrom sp a₁ Φ t tree V s = headFrom sp a₀ Φ t tree V s

/-- **The sends' window**: an ack sent with the slot-`s` vote is the sender's decision of slot
`s − j` for an ack committee `j`, and it is in the window at slot `s` (`j ≤ 3 ≤ e`). -/
def AckSendsWindow : Prop :=
  ∀ (P : PCStore sp.n) (self : Fin sp.n) (s : Nat), ∀ a ∈ ackSends sp P self s,
    a.val = self ∧ AckSlot a.j ∧ a.slot + a.j = s ∧ s ≤ a.slot + pcWindow sp ∧
      P.myAcks a.slot = some a.target

/-- **The admission's window**: an ack of no ack committee, or out of the window, changes
nothing. -/
def OnAckWindow : Prop :=
  ∀ (P : PCStore sp.n) (t : Time) (a : Ack sp.n),
    (¬ AckSlot a.j ∨ a.slot + pcWindow sp < sp.slot t) → onAck sp P t a = P

/-- **The record's window**: a vote of a slot below `slot(t) − e − 2` is not recorded. -/
def RecordWindow : Prop :=
  ∀ (P : PCStore sp.n) (t : Time) (v : Vote sp.n),
    v.slot + pcWindow sp + 2 < sp.slot t → recordVote sp P t v = P

end Consensus.Goldilocks.PreConfirmations

end
