module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Premises
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.CommitteeRun

public section

/-! # Goldilocks under `Sleepy` with growing faults: origins and the record invariant

The vocabulary of `Compose/Sleepy/Defs` for a time-indexed honest set `H : Time → Set (Fin n)`.
Every node quantifier reads honesty at the cut of the event it constrains:

* `HVoteAt tr H y i e`: a vote cast at a cut at which its node is honest. A vote of a node
  compromised at the time of the cut is not constrained by the run, so every vote quantifier of the
  invariant ranges over `HVoteAt`;
* an **origin** (`Origin`, `OriginWithin`, `OriginBefore`): a result or an optimistic selection
  of a node honest at its event cut. Events are immutable, so a later compromise removes no
  origin;
* the frontier `OriginsBelowUpTo`, `VotesBelowUpTo`, the slot voters still honest at `d`
  (`VotersAt`), the count shapes `SleepyBoundsFrom` (`f_d < n / 2` at every `d ≤ b`, and, for the
  slots from a first slot on, the slot count `FaultBoundAt (t_s + Δ) d` for `d ≤ t_s + 6Δ`), the
  finite service `SleepyServiceBefore` and its form from a start time `SleepyServiceFrom` (sends and
  acceptances from `a`, older acceptances caught up by `a + κ`), and the invariant
  `SleepyInvariantUpTo` (S1–S3, every node at its own cut). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **The finite Sleepy service under growing faults**: SA message service and acceptance relay
(senders honest at the send, recipients honest at the reading call), and node acceptance relay
inside the blocks held while honest. -/
structure SleepyServiceBefore (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (ΔF b : Time) : Prop where
  deltaF : 0 < ΔF
  message : ∀ x i v, x ∈ H (tr.time i) → tr.projAC.SendOrAdmit x i v → 0 ≤ tr.time i →
    ∀ y j ℓ, y ∈ H (tr.time j) → tr.projAC.CallAt y j ℓ → tr.projAC.deadline y j (tr.time i) ≤ b →
      tr.projAC.deadline y j (tr.time i) ≤ tr.time j →
      SA.MessageServedBefore tr.projAC y j (tr.time i) v
  acRelay : ∀ x i B, x ∈ H (tr.time i) → tr.projAC.AcceptAt x i B → 0 ≤ tr.time i →
    ∀ y j ℓ, y ∈ H (tr.time j) → tr.projAC.CallAt y j ℓ → tr.projAC.deadline y j (tr.time i) ≤ b →
      tr.projAC.deadline y j (tr.time i) ≤ tr.time j → Anc (tr.HonestBlocksAt H) ℓ.frame.F B →
      ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧ tr.time k < tr.projAC.deadline y k (tr.time i)
  relay : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → 0 ≤ tr.time i →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.deadline y j (tr.time i) sp.Δ ≤ b →
      tr.deadline y j (tr.time i) sp.Δ ≤ tr.time j →
      Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B → tr.BlockAcceptedBy y j (tr.time i) B

/-- **The finite Sleepy service from `a`** under growing faults: the service of
`SleepyServiceBefore` for the sends and acceptances at times `≥ a`, and the catch-up of older
acceptances: a block that a node honest then accepted before `a` is accepted, before `a + κ`, by
every node honest at a call from `a + κ` on whose `Σ.F` it extends (`old` at the node, `acOld` at
its AC projection). From genesis `a = κ = 0`, and the catch-up is vacuous
(`SleepyServiceBefore.toFrom`); after GST, `a = ḡ` with the catch-up window `κ`. -/
structure SleepyServiceFrom (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (ΔF a κ b : Time) : Prop where
  deltaF : 0 < ΔF
  kappa : 0 ≤ κ
  message : ∀ x i v, x ∈ H (tr.time i) → tr.projAC.SendOrAdmit x i v → a ≤ tr.time i →
    ∀ y j ℓ, y ∈ H (tr.time j) → tr.projAC.CallAt y j ℓ → tr.projAC.deadline y j (tr.time i) ≤ b →
      tr.projAC.deadline y j (tr.time i) ≤ tr.time j →
      SA.MessageServedBefore tr.projAC y j (tr.time i) v
  acRelay : ∀ x i B, x ∈ H (tr.time i) → tr.projAC.AcceptAt x i B → a ≤ tr.time i →
    ∀ y j ℓ, y ∈ H (tr.time j) → tr.projAC.CallAt y j ℓ → tr.projAC.deadline y j (tr.time i) ≤ b →
      tr.projAC.deadline y j (tr.time i) ≤ tr.time j → Anc (tr.HonestBlocksAt H) ℓ.frame.F B →
      ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧ tr.time k < tr.projAC.deadline y k (tr.time i)
  relay : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → a ≤ tr.time i →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.deadline y j (tr.time i) sp.Δ ≤ b →
      tr.deadline y j (tr.time i) sp.Δ ≤ tr.time j →
      Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B → tr.BlockAcceptedBy y j (tr.time i) B
  old : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → tr.time i < a →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → a + κ ≤ tr.time j →
      Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B →
      ∃ k < j, tr.AcceptAt y k B ∧ tr.time k < a + κ
  acOld : ∀ x i B, x ∈ H (tr.time i) → tr.projAC.AcceptAt x i B → tr.time i < a →
    ∀ y j ℓ, y ∈ H (tr.time j) → tr.projAC.CallAt y j ℓ → a + κ ≤ tr.time j →
      Anc (tr.HonestBlocksAt H) ℓ.frame.F B →
      ∃ k < j, tr.projAC.AcceptAt y k B ∧ tr.time k < a + κ

variable (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- A vote cast at a cut at which its node is honest. -/
def HVoteAt (y : Fin sp.n) (i : Nat) (e : SA.Em sp (List (FG.Att sp.n))) : Prop :=
  y ∈ H (tr.time i) ∧ SA.VoteAt tr.projAC y i e

/-- **An origin of label `s`**: the result of an update, or the selection of an optimistic check,
of slot `s` by a node honest at its event cut. -/
def Origin (C : SA.Blk sp.n (List (FG.Att sp.n))) (s : Nat) : Prop :=
  ∃ x i CV, x ∈ H (tr.time i) ∧
    (SA.ResultAt tr.projAC x i s C CV ∨ SA.OptimisticLockAt tr.projAC x i s C CV)

/-- An origin of label `s` whose event cut is at a time `≤ b`. -/
def OriginWithin (C : SA.Blk sp.n (List (FG.Att sp.n))) (s : Nat) (b : Time) : Prop :=
  ∃ x i CV, x ∈ H (tr.time i) ∧ tr.time i ≤ b ∧
    (SA.ResultAt tr.projAC x i s C CV ∨ SA.OptimisticLockAt tr.projAC x i s C CV)

/-- An origin of label `s` whose event is at a cut before `i`. -/
def OriginBefore (C : SA.Blk sp.n (List (FG.Att sp.n))) (s i : Nat) : Prop :=
  ∃ x k CV, k < i ∧ x ∈ H (tr.time k) ∧
    (SA.ResultAt tr.projAC x k s C CV ∨ SA.OptimisticLockAt tr.projAC x k s C CV)

/-- `B` is genesis or an ancestor (inside the blocks held while honest) of an origin within `b`. -/
def OnOriginChainWithin (B : SA.Blk sp.n (List (FG.Att sp.n))) (b : Time) : Prop :=
  B.root = sp.genesisRoot ∨ ∃ C s, OriginWithin tr H C s b ∧ Anc (tr.HonestBlocksAt H) B C

/-- **`P_s` up to `b`**: origins within `b` of labels below `s` are pairwise compatible. -/
def OriginsBelowUpTo (s : Nat) (b : Time) : Prop :=
  ∀ C j C' j', j < s → j' < s → OriginWithin tr H C j b → OriginWithin tr H C' j' b →
    Compatible (tr.HonestBlocksAt H) C C'

/-- **`V_s` up to `b`**: every honest vote at a time `≤ b` of a slot `m` with `j < m ≤ s`
extends every origin within `b` of label `j`. -/
def VotesBelowUpTo (s : Nat) (b : Time) : Prop :=
  ∀ C j, OriginWithin tr H C j b → ∀ y i e, HVoteAt tr H y i e → tr.time i ≤ b →
    j < e.msg.slot → e.msg.slot ≤ s → SA.VoteExtends (tr.HonestBlocksAt H) e.msg C

/-- The voters of slot `s` (honest at their vote) that are still honest at `d`. -/
def VotersAt (s : Nat) (d : Time) : Set (Fin sp.n) :=
  {x | x ∈ H d ∧ ∃ j e, HVoteAt tr H x j e ∧ e.msg.slot = s}

/-- **The count shapes through `b` for the slots from `σ₀` on**: `2 f_d < n` at every
`d ∈ [0, b]`, and for every slot `s ≥ σ₀` the slot count `f_d < h_{t_s + Δ}` at every
`d ∈ [t_s + Δ, min b (t_s + 6Δ)]` and the late count `f_d < h_{t_s + 2Δ}` at every
`d ∈ [t_s + 2Δ, min b (t_s + 7Δ)]`. From genesis, `σ₀ = 0`. -/
structure SleepyBoundsFrom (σ₀ : Nat) (b : Time) : Prop where
  two : ∀ d, 0 ≤ d → d ≤ b → 2 * (H d)ᶜ.ncard < sp.n
  slot : ∀ (s : Nat) (d : Time), σ₀ ≤ s → sp.ts s + sp.Δ ≤ d → d ≤ b →
    d ≤ sp.ts s + 6 * sp.Δ → tr.FaultBoundAt H (sp.ts s + sp.Δ) d
  late : ∀ (s : Nat) (d : Time), σ₀ ≤ s → sp.ts s + 2 * sp.Δ ≤ d → d ≤ b →
    d ≤ sp.ts s + 7 * sp.Δ → tr.FaultBoundAt H (sp.ts s + 2 * sp.Δ) d

/-- **The run half of the committee premises** for the slot dictionary `K`: committees of
`committeeSize` members, P (`CommitteePAt`), the frames of nodes honest at the cut carry votes of
members, and the gate: a node honest at `t ≥ 0` may vote in slot `s`, before every cut whose
earlier cuts are at times `≤ t`, iff it is in the slot-`s` committee. T (`CommitteeTAt`) follows
from P and the frames on a run (`CommitteeFacts.hT`). -/
structure CommitteeFacts (K : SA.CommitteeDict sp.n) : Prop where
  hsize : ∀ s, (K.committee s).ncard = sp.committeeSize
  hP : SA.CommitteePAt K tr.projAC H
  hFrame : ∀ w c, w ∈ H (tr.time c) → ∀ C ∈ (Node.frame (tr.state w c)).tree,
    ∀ v ∈ SA.blockVotes C, v.val ∈ K.committee v.slot
  hGate : ∀ t, 0 ≤ t → ∀ x, x ∈ H t → ∀ i, (∀ k < i, tr.time k ≤ t) → ∀ s,
    ((tr.state x i).ac.mayVote s = true ↔ x ∈ K.committee s)

/-- **The committee count shapes through `b` for the slots from `σ₀` on**: for every slot `s ≥ σ₀`,
CS at the slot-`s` committee (`FaultBoundK`, faults charged at `d`, readiness at `t_s + Δ`) at
every `d ∈ [t_s + Δ, min b (t_s + 6Δ)]`, and CS2 `2 f_d < |K s|` among the slot-`s` committee at
every `d ∈ [t_s, min b (t_s + 2Δ)]`. -/
structure CommitteeBoundsFrom (K : SA.CommitteeDict sp.n) (σ₀ : Nat) (b : Time) : Prop where
  slotK : ∀ (s : Nat) (d : Time), σ₀ ≤ s → sp.ts s + sp.Δ ≤ d → d ≤ b →
    d ≤ sp.ts s + 6 * sp.Δ → SA.FaultBoundK K s tr.projAC (H d) (sp.ts s + sp.Δ)
  twoK : ∀ (s : Nat) (d : Time), σ₀ ≤ s → sp.ts s ≤ d → d ≤ b → d ≤ sp.ts s + 2 * sp.Δ →
    2 * (K.committee s ∩ (H d)ᶜ).ncard < (K.committee s).ncard

/-- **The Sleepy record invariant up to `b`** (S1–S3). A node's state before cut `i` is read at a
time `t ∈ [0, b]` at or after every earlier cut, with the node honest at `t` (the convention of
`HonestBlocksAt`): the state depends only on the earlier cuts. FG sources are the node's own event
at cut `i`, so `sources` reads honesty at the cut. -/
structure SleepyInvariantUpTo (b : Time) : Prop where
  /-- S1: any two origins within `b` are compatible. -/
  origins_compatible : ∀ C s C' s', OriginWithin tr H C s b → OriginWithin tr H C' s' b →
    Compatible (tr.HonestBlocksAt H) C C'
  /-- S2: every honest vote at a time `≤ b` of a slot after the label of an origin within `b`
  extends it. -/
  vote_extends : ∀ C s, OriginWithin tr H C s b → ∀ y i e, HVoteAt tr H y i e →
    tr.time i ≤ b → s < e.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e.msg C
  /-- S1: the state of a node before a cut whose earlier cuts are at times `≤ t ≤ b`, with the node
  honest at `t`: the record names a block of its tree that is genesis or an origin within `b`. -/
  record : ∀ y i t, 0 ≤ t → (∀ k < i, tr.time k ≤ t) → t ≤ b → y ∈ H t →
    ∃ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y i).ac.latestConfirmed ∧
      (C.root = sp.genesisRoot ∨ ∃ s, OriginWithin tr H C s b)
  /-- S1: `Σ.F` and `Σ.J` are on the chain of the origins within `b` (state read at `t`). -/
  caches : ∀ y i t, 0 ≤ t → (∀ k < i, tr.time k ≤ t) → t ≤ b → y ∈ H t →
    OnOriginChainWithin tr H (tr.state y i).fg.F b ∧
      OnOriginChainWithin tr H (tr.state y i).fg.J b
  /-- S1: every stored lock names a block of the node's tree on the chain of the origins within
  `b` (state read at `t`). -/
  locks : ∀ y i t, 0 ≤ t → (∀ k < i, tr.time k ≤ t) → t ≤ b → y ∈ H t →
    ∀ l ∈ (tr.state y i).ac.locks,
    ∃ L ∈ (tr.state y i).fg.tree, L.root = l.block ∧ OnOriginChainWithin tr H L b
  /-- S1: every FG source is on the chain of the origins within `b`. -/
  sources : ∀ y i, y ∈ H (tr.time i) → (∀ k < i, tr.time k ≤ b) → ∀ ℓ C,
    SA.ToFGAt tr.projAC y i ℓ C → OnOriginChainWithin tr H C b
  /-- S3 (full reads): an origin within `b` that the node holds (state read at `t`) is at or below
  its `fc_root`, or in its full viable tree. -/
  viable : ∀ y i t, 0 ≤ t → (∀ k < i, tr.time k ≤ t) → t ≤ b → y ∈ H t → ∀ C s,
    OriginWithin tr H C s b → C ∈ (Node.frame (tr.state y i)).tree →
    (Node.frame (tr.state y i)).Anc C (Node.frame (tr.state y i)).fcRoot ∨
      C ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree

variable {tr H}

theorem sleepyServiceBefore_iff {ΔF b : Time} :
    SleepyServiceBefore tr H ΔF b ↔ 0 < ΔF ∧
      (∀ x i v, x ∈ H (tr.time i) → tr.projAC.SendOrAdmit x i v → 0 ≤ tr.time i →
        ∀ y j ℓ, y ∈ H (tr.time j) → tr.projAC.CallAt y j ℓ →
          tr.projAC.deadline y j (tr.time i) ≤ b →
          tr.projAC.deadline y j (tr.time i) ≤ tr.time j →
          SA.MessageServedBefore tr.projAC y j (tr.time i) v) ∧
      (∀ x i B, x ∈ H (tr.time i) → tr.projAC.AcceptAt x i B → 0 ≤ tr.time i →
        ∀ y j ℓ, y ∈ H (tr.time j) → tr.projAC.CallAt y j ℓ →
          tr.projAC.deadline y j (tr.time i) ≤ b →
          tr.projAC.deadline y j (tr.time i) ≤ tr.time j →
          Anc (tr.HonestBlocksAt H) ℓ.frame.F B →
          ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧ tr.time k < tr.projAC.deadline y k (tr.time i)) ∧
      (∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → 0 ≤ tr.time i →
        ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.deadline y j (tr.time i) sp.Δ ≤ b →
          tr.deadline y j (tr.time i) sp.Δ ≤ tr.time j →
          Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B →
          tr.BlockAcceptedBy y j (tr.time i) B) :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

theorem hVoteAt_iff {y : Fin sp.n} {i : Nat} {e : SA.Em sp (List (FG.Att sp.n))} :
    HVoteAt tr H y i e ↔ y ∈ H (tr.time i) ∧ SA.VoteAt tr.projAC y i e :=
  Iff.rfl

theorem origin_iff {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} :
    Origin tr H C s ↔ ∃ x i CV, x ∈ H (tr.time i) ∧
      (SA.ResultAt tr.projAC x i s C CV ∨ SA.OptimisticLockAt tr.projAC x i s C CV) :=
  Iff.rfl

theorem originWithin_iff {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {b : Time} :
    OriginWithin tr H C s b ↔ ∃ x i CV, x ∈ H (tr.time i) ∧ tr.time i ≤ b ∧
      (SA.ResultAt tr.projAC x i s C CV ∨ SA.OptimisticLockAt tr.projAC x i s C CV) :=
  Iff.rfl

theorem originBefore_iff {C : SA.Blk sp.n (List (FG.Att sp.n))} {s i : Nat} :
    OriginBefore tr H C s i ↔ ∃ x k CV, k < i ∧ x ∈ H (tr.time k) ∧
      (SA.ResultAt tr.projAC x k s C CV ∨ SA.OptimisticLockAt tr.projAC x k s C CV) :=
  Iff.rfl

theorem onOriginChainWithin_iff {B : SA.Blk sp.n (List (FG.Att sp.n))} {b : Time} :
    OnOriginChainWithin tr H B b ↔
      B.root = sp.genesisRoot ∨ ∃ C s, OriginWithin tr H C s b ∧ Anc (tr.HonestBlocksAt H) B C :=
  Iff.rfl

theorem originsBelowUpTo_iff {s : Nat} {b : Time} :
    OriginsBelowUpTo tr H s b ↔ ∀ C j C' j', j < s → j' < s → OriginWithin tr H C j b →
      OriginWithin tr H C' j' b → Compatible (tr.HonestBlocksAt H) C C' :=
  Iff.rfl

theorem votesBelowUpTo_iff {s : Nat} {b : Time} :
    VotesBelowUpTo tr H s b ↔ ∀ C j, OriginWithin tr H C j b → ∀ y i e, HVoteAt tr H y i e →
      tr.time i ≤ b → j < e.msg.slot → e.msg.slot ≤ s →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg C :=
  Iff.rfl

theorem votersAt_iff {s : Nat} {d : Time} {x : Fin sp.n} :
    x ∈ VotersAt tr H s d ↔ x ∈ H d ∧ ∃ j e, HVoteAt tr H x j e ∧ e.msg.slot = s :=
  Iff.rfl

theorem OriginWithin.origin {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {b : Time}
    (h : OriginWithin tr H C s b) : Origin tr H C s :=
  let ⟨x, i, CV, hx, _, h⟩ := h
  ⟨x, i, CV, hx, h⟩

theorem OriginWithin.mono {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {b b' : Time}
    (h : OriginWithin tr H C s b) (hb : b ≤ b') : OriginWithin tr H C s b' :=
  let ⟨x, i, CV, hx, hi, h⟩ := h
  ⟨x, i, CV, hx, hi.trans hb, h⟩

/-- An origin whose event precedes a cut within `b` is within `b`. -/
theorem OriginBefore.within {C : SA.Blk sp.n (List (FG.Att sp.n))} {s i : Nat} {b : Time}
    (h : OriginBefore tr H C s i) (hi : ∀ k < i, tr.time k ≤ b) : OriginWithin tr H C s b :=
  let ⟨x, k, CV, hk, hx, h⟩ := h
  ⟨x, k, CV, hx, hi k hk, h⟩

/-- The result of a node honest at its update is an origin within every horizon after it. -/
theorem OriginWithin.of_result {x : Fin sp.n} {i s : Nat} (hx : x ∈ H (tr.time i)) {b : Time}
    (hib : tr.time i ≤ b) {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (h : SA.ResultAt tr.projAC x i s C CV) : OriginWithin tr H C s b :=
  ⟨x, i, CV, hx, hib, Or.inl h⟩

/-- The selection of a node honest at its optimistic check is an origin within every horizon
after it. -/
theorem OriginWithin.of_optimistic {x : Fin sp.n} {i s : Nat} (hx : x ∈ H (tr.time i)) {b : Time}
    (hib : tr.time i ≤ b) {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (h : SA.OptimisticLockAt tr.projAC x i s C CV) : OriginWithin tr H C s b :=
  ⟨x, i, CV, hx, hib, Or.inr h⟩

/-- The bounds through `b` give the bounds through every `b' ≤ b`. -/
theorem SleepyBoundsFrom.mono {σ₀ : Nat} {b b' : Time} (h : SleepyBoundsFrom tr H σ₀ b)
    (hb : b' ≤ b) : SleepyBoundsFrom tr H σ₀ b' :=
  ⟨fun d h0 hd => h.two d h0 (hd.trans hb),
    fun s d hs h1 hd h6 => h.slot s d hs h1 (hd.trans hb) h6,
    fun s d hs h1 hd h7 => h.late s d hs h1 (hd.trans hb) h7⟩

/-- The committee bounds through `b` give the committee bounds through every `b' ≤ b`. -/
theorem CommitteeBoundsFrom.mono {K : SA.CommitteeDict sp.n} {σ₀ : Nat} {b b' : Time}
    (h : CommitteeBoundsFrom tr H K σ₀ b) (hb : b' ≤ b) : CommitteeBoundsFrom tr H K σ₀ b' :=
  ⟨fun s d hs h1 hd h6 => h.slotK s d hs h1 (hd.trans hb) h6,
    fun s d hs h0 hd h2 => h.twoK s d hs h0 (hd.trans hb) h2⟩

/-- **CS2 from CS**: at `d ∈ [t_s + Δ, min b (t_s + 6Δ)]` for a slot `s ≥ σ₀`, fewer than half of
the slot-`s` committee is compromised by `d`. -/
theorem CommitteeBoundsFrom.two_of_slotK {K : SA.CommitteeDict sp.n} {σ₀ : Nat} {b : Time}
    (h : CommitteeBoundsFrom tr H K σ₀ b) {s : Nat} {d : Time} (hs : σ₀ ≤ s)
    (h1 : sp.ts s + sp.Δ ≤ d) (hdb : d ≤ b) (h6 : d ≤ sp.ts s + 6 * sp.Δ) :
    2 * (K.committee s ∩ (H d)ᶜ).ncard < (K.committee s).ncard := by
  have hk : (K.committee s ∩ (H d)ᶜ).ncard < (K.committee s ∩ {y | y ∈ H d ∧
      tr.projAC.awake y (sp.ts s + sp.Δ) ∧ SA.JoinedAt tr.projAC y (sp.ts s + sp.Δ)}).ncard :=
    h.slotK s d hs h1 hdb h6
  have hle := Set.ncard_le_ncard (s := K.committee s ∩ {y | y ∈ H d ∧
      tr.projAC.awake y (sp.ts s + sp.Δ) ∧ SA.JoinedAt tr.projAC y (sp.ts s + sp.Δ)})
    (t := K.committee s ∩ H d) fun _ hy => ⟨hy.1, hy.2.1⟩
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard (K.committee s) (H d)
  rw [Set.sdiff_eq] at hsplit
  omega

/-- **Awake and joined at the AC projection** is awake and joined at the run. -/
theorem mem_awakeJoined_projAC {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {proposer : Nat → Fin sp.n} {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {t : Time} {y : Fin sp.n} :
    (tr.projAC.awake y t ∧ SA.JoinedAt tr.projAC y t) ↔ (tr.awake y t ∧ tr.JoinedAt y t) :=
  and_congr Iff.rfl (projAC_joinedAt_iff hrun.time_nonneg y t).symm

/-- The service through `b` gives the service through every `b' ≤ b`. -/
theorem SleepyServiceBefore.mono {ΔF b b' : Time} (h : SleepyServiceBefore tr H ΔF b)
    (hb : b' ≤ b) : SleepyServiceBefore tr H ΔF b' :=
  ⟨h.deltaF, fun x i v hx hv h0 y j ℓ hy hc hd hdj => h.message x i v hx hv h0 y j ℓ hy hc
      (hd.trans hb) hdj,
    fun x i B hx hB h0 y j ℓ hy hc hd hdj ha => h.acRelay x i B hx hB h0 y j ℓ hy hc
      (hd.trans hb) hdj ha,
    fun x i B hx hB h0 y j hy hc hd hdj ha => h.relay x i B hx hB h0 y j hy hc (hd.trans hb) hdj ha⟩

/-- **The service from genesis is the service from `0`**, with a vacuous catch-up: every cut is
at a time `≥ 0`. -/
theorem SleepyServiceBefore.toFrom {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {proposer : Nat → Fin sp.n} {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {ΔF b : Time}
    (h : SleepyServiceBefore tr H ΔF b) : SleepyServiceFrom tr H ΔF 0 0 b :=
  ⟨h.deltaF, le_rfl, fun x i v hx hv _ => h.message x i v hx hv (hrun.time_nonneg i),
    fun x i B hx hB _ => h.acRelay x i B hx hB (hrun.time_nonneg i),
    fun x i B hx hB _ => h.relay x i B hx hB (hrun.time_nonneg i),
    fun _ i _ _ _ hi => absurd hi (not_lt.2 (hrun.time_nonneg i)),
    fun _ i _ _ _ hi => absurd hi (not_lt.2 (hrun.time_nonneg i))⟩

/-! ### The per-node fields at a cut -/

/-- A cut `i` of a node honest then, with every earlier cut within `b ≥ 0`, is read at
`t = tr.time (i − 1)` (or `0` at `i = 0`). -/
theorem exists_read_time {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {proposer : Nat → Fin sp.n} {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini) {b : Time}
    (hb : 0 ≤ b) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) (hi : ∀ k < i, tr.time k ≤ b) :
    ∃ t, 0 ≤ t ∧ (∀ k < i, tr.time k ≤ t) ∧ t ≤ b ∧ y ∈ H t := by
  rcases i with _ | k
  · exact ⟨0, le_rfl, fun _ h => absurd h (Nat.not_lt_zero _), hb,
      hrun.antitone (hrun.time_nonneg 0) hy⟩
  · exact ⟨tr.time k, hrun.time_nonneg k, fun _ h => hrun.time_mono (Nat.lt_succ_iff.mp h),
      hi k (Nat.lt_succ_self k), hrun.antitone (hrun.time_mono (Nat.le_succ k)) hy⟩

section AtCut

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {proposer : Nat → Fin sp.n}
  {b : Time} (hinv : SleepyInvariantUpTo tr H b) {ini}
  (hrun : Growing.GoldilocksRun proposer dg H tr ini)
  (hb : 0 ≤ b) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) (hi : ∀ k < i, tr.time k ≤ b)
include hinv hrun hb hy hi

theorem SleepyInvariantUpTo.record_at_cut :
    ∃ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y i).ac.latestConfirmed ∧
      (C.root = sp.genesisRoot ∨ ∃ s, OriginWithin tr H C s b) :=
  have ⟨t, h0, hit, htb, hyt⟩ := exists_read_time hrun hb hy hi
  hinv.record y i t h0 hit htb hyt

theorem SleepyInvariantUpTo.caches_at_cut :
    OnOriginChainWithin tr H (tr.state y i).fg.F b ∧
      OnOriginChainWithin tr H (tr.state y i).fg.J b :=
  have ⟨t, h0, hit, htb, hyt⟩ := exists_read_time hrun hb hy hi
  hinv.caches y i t h0 hit htb hyt

theorem SleepyInvariantUpTo.locks_at_cut : ∀ l ∈ (tr.state y i).ac.locks,
    ∃ L ∈ (tr.state y i).fg.tree, L.root = l.block ∧ OnOriginChainWithin tr H L b :=
  have ⟨t, h0, hit, htb, hyt⟩ := exists_read_time hrun hb hy hi
  hinv.locks y i t h0 hit htb hyt

theorem SleepyInvariantUpTo.viable_at_cut : ∀ C s, OriginWithin tr H C s b →
    C ∈ (Node.frame (tr.state y i)).tree →
    (Node.frame (tr.state y i)).Anc C (Node.frame (tr.state y i)).fcRoot ∨
      C ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree :=
  have ⟨t, h0, hit, htb, hyt⟩ := exists_read_time hrun hb hy hi
  hinv.viable y i t h0 hit htb hyt

end AtCut

end Consensus.Goldilocks.Compose.Growing

end
