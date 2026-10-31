module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Run

public section

/-! # Goldilocks under `Sleepy`: origins and the record invariant (definitions)

The vocabulary of the Sleepy safety invariant from genesis (fradamt-agent/workbench#11,
`repos/goldilocks/notes/healing-simple/sleepy-record-invariant.md`, §1), over a Goldilocks run,
read on its AC projection, with ancestry inside the honest blocks of the run:

* an **origin** of label `s` (`Origin`): the result `C ≠ ⊥` of an honest joined update of slot `s`
  (fast, slow, vetoed or not: `SA.ResultAt`), or the raw block an honest optimistic check of
  slot `s` selects (`SA.OptimisticLockAt`). Origins are actual events of the run, whatever their
  time relative to the votes that read them;
* `OnOriginChain B`: `B` is genesis or an ancestor of an origin (the ancestor closure of the
  origin chain);
* `SleepyInvariant` (S1–S3 of the note, at every cut): origins are pairwise compatible; every
  honest vote of a later slot extends an origin (label-strict transfer); every honest record is
  genesis or an origin; every honest `Σ.F`, `Σ.J`, stored lock and FG source is on the origin
  chain; and an origin that an honest node holds is at or below its `fc_root` or in its full
  viable tree;
* the bounded frontier of the induction (§4, repaired): `OriginsBelow s` (`P_s`: origins of labels
  below `s` compare pairwise) and `VotesBelow s` (`V_s`: every honest vote of a slot `m` with
  `j < m ≤ s` extends every origin of label `j < s`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- **An origin of label `s`**: the result `C ≠ ⊥` of the update of slot `s` of an honest node
(joined at `t_s + 6Δ`), or the block that an honest optimistic check of slot `s` selects. -/
def Origin (C : SA.Blk sp.n (List (FG.Att sp.n))) (s : Nat) : Prop :=
  ∃ x ∈ H, ∃ i CV, SA.ResultAt tr.projAC x i s C CV ∨ SA.OptimisticLockAt tr.projAC x i s C CV

/-- An origin of label `s` whose event is at a cut before `i` (the origins a read at cut `i` can
depend on). -/
def OriginBefore (C : SA.Blk sp.n (List (FG.Att sp.n))) (s i : Nat) : Prop :=
  ∃ x ∈ H, ∃ k < i, ∃ CV,
    SA.ResultAt tr.projAC x k s C CV ∨ SA.OptimisticLockAt tr.projAC x k s C CV

/-- `B` is on the ancestor closure of the origin chain: genesis, or an ancestor (inside the
honest blocks) of an origin. -/
def OnOriginChain (B : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  B.root = sp.genesisRoot ∨ ∃ C s, Origin tr H C s ∧ Anc (tr.HonestBlocks H) B C

/-- **`P_s`**: origins of labels below `s` are pairwise compatible. -/
def OriginsBelow (s : Nat) : Prop :=
  ∀ C j C' j', j < s → j' < s → Origin tr H C j → Origin tr H C' j' →
    Compatible (tr.HonestBlocks H) C C'

/-- **`V_s`**: every honest vote of a slot `m` with `j < m ≤ s` extends every origin of label
`j`. -/
def VotesBelow (s : Nat) : Prop :=
  ∀ C j, Origin tr H C j → ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → j < e.msg.slot →
    e.msg.slot ≤ s → SA.VoteExtends (tr.HonestBlocks H) e.msg C

variable {tr H}

theorem origin_iff {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} :
    Origin tr H C s ↔ ∃ x ∈ H, ∃ i CV,
      SA.ResultAt tr.projAC x i s C CV ∨ SA.OptimisticLockAt tr.projAC x i s C CV :=
  Iff.rfl

theorem originBefore_iff {C : SA.Blk sp.n (List (FG.Att sp.n))} {s i : Nat} :
    OriginBefore tr H C s i ↔ ∃ x ∈ H, ∃ k < i, ∃ CV,
      SA.ResultAt tr.projAC x k s C CV ∨ SA.OptimisticLockAt tr.projAC x k s C CV :=
  Iff.rfl

theorem OriginBefore.origin {C : SA.Blk sp.n (List (FG.Att sp.n))} {s i : Nat}
    (h : OriginBefore tr H C s i) : Origin tr H C s :=
  let ⟨x, hx, k, _, CV, h⟩ := h
  ⟨x, hx, k, CV, h⟩

/-- The result of an honest joined update is an origin of its slot. -/
theorem Origin.of_result {x : Fin sp.n} (hx : x ∈ H) {i s : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (h : SA.ResultAt tr.projAC x i s C CV) : Origin tr H C s :=
  ⟨x, hx, i, CV, Or.inl h⟩

/-- The selection of an honest optimistic check is an origin of its slot. -/
theorem Origin.of_optimistic {x : Fin sp.n} (hx : x ∈ H) {i s : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (h : SA.OptimisticLockAt tr.projAC x i s C CV) : Origin tr H C s :=
  ⟨x, hx, i, CV, Or.inr h⟩

theorem onOriginChain_iff {B : SA.Blk sp.n (List (FG.Att sp.n))} :
    OnOriginChain tr H B ↔
      B.root = sp.genesisRoot ∨ ∃ C s, Origin tr H C s ∧ Anc (tr.HonestBlocks H) B C :=
  Iff.rfl

theorem originsBelow_iff {s : Nat} :
    OriginsBelow tr H s ↔ ∀ C j C' j', j < s → j' < s → Origin tr H C j → Origin tr H C' j' →
      Compatible (tr.HonestBlocks H) C C' :=
  Iff.rfl

theorem votesBelow_iff {s : Nat} :
    VotesBelow tr H s ↔ ∀ C j, Origin tr H C j → ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e →
      j < e.msg.slot → e.msg.slot ≤ s → SA.VoteExtends (tr.HonestBlocks H) e.msg C :=
  Iff.rfl

variable (tr H)

/-- **The Sleepy record invariant** (workbench#11 S1–S3). -/
structure SleepyInvariant : Prop where
  /-- S1: any two origins are compatible. -/
  origins_compatible : ∀ C s C' s', Origin tr H C s → Origin tr H C' s' →
    Compatible (tr.HonestBlocks H) C C'
  /-- S2: every honest vote of a slot after an origin's label extends it. -/
  vote_extends : ∀ C s, Origin tr H C s → ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e →
    s < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg C
  /-- S1: every honest record names a block of the node's tree that is genesis or an origin. -/
  record : ∀ y ∈ H, ∀ i, ∃ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y i).ac.latestConfirmed ∧
    (C.root = sp.genesisRoot ∨ ∃ s, Origin tr H C s)
  /-- S1: every honest `Σ.F` and `Σ.J` is on the origin chain. -/
  caches : ∀ y ∈ H, ∀ i, OnOriginChain tr H (tr.state y i).fg.F ∧
    OnOriginChain tr H (tr.state y i).fg.J
  /-- S1: every honest stored lock names a block of the node's tree on the origin chain. -/
  locks : ∀ y ∈ H, ∀ i, ∀ l ∈ (tr.state y i).ac.locks,
    ∃ L ∈ (tr.state y i).fg.tree, L.root = l.block ∧ OnOriginChain tr H L
  /-- S1: every honest FG source (a block `ac_to_fg` returns) is on the origin chain. -/
  sources : ∀ y ∈ H, ∀ i ℓ C, SA.ToFGAt tr.projAC y i ℓ C → OnOriginChain tr H C
  /-- S3 (full reads): an origin that an honest node holds is at or below its `fc_root`, or in
  its full viable tree. -/
  viable : ∀ y ∈ H, ∀ i C s, Origin tr H C s → C ∈ (Node.frame (tr.state y i)).tree →
    (Node.frame (tr.state y i)).Anc C (Node.frame (tr.state y i)).fcRoot ∨
      C ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree

/-! ### The invariant up to a horizon `b`

The prefix premises of `Regimes.SleepySafePrefix` up to `b` (`SleepyPrefix`: `Sync[0, b − Δ]`
and `f < h_t` at the slot points `≤ b`), the origins whose event is at a time `≤ b`
(`OriginWithin`), and the invariant restricted to them and to the cuts **within `b`** (every
earlier cut at a time `≤ b`, so that the state before the cut is the state at a time `≤ b`):
`SleepyInvariantUpTo`. -/

/-- **The prefix premises of `SleepySafePrefix` up to `b`**: `Sync[0, b − Δ]` and `f < h_t` at
every `t ∈ {t_s, t_s + Δ, t_s + 2Δ}` with `t ≤ b`. -/
def SleepyPrefix (ΔF b : Time) : Prop :=
  0 ≤ b ∧ tr.SyncRun H ΔF 0 (b - sp.Δ) ∧
    ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d)

/-- An origin of label `s` whose event cut is at a time `≤ b`. -/
def OriginWithin (C : SA.Blk sp.n (List (FG.Att sp.n))) (s : Nat) (b : Time) : Prop :=
  ∃ x ∈ H, ∃ i CV, tr.time i ≤ b ∧
    (SA.ResultAt tr.projAC x i s C CV ∨ SA.OptimisticLockAt tr.projAC x i s C CV)

/-- `B` is on the ancestor closure of the origins within `b`: genesis, or an ancestor (inside the
honest blocks) of an origin whose event is at a time `≤ b`. -/
def OnOriginChainWithin (B : SA.Blk sp.n (List (FG.Att sp.n))) (b : Time) : Prop :=
  B.root = sp.genesisRoot ∨ ∃ C s, OriginWithin tr H C s b ∧ Anc (tr.HonestBlocks H) B C

/-- **`P_s` up to `b`**: origins within `b` of labels below `s` are pairwise compatible. -/
def OriginsBelowUpTo (s : Nat) (b : Time) : Prop :=
  ∀ C j C' j', j < s → j' < s → OriginWithin tr H C j b → OriginWithin tr H C' j' b →
    Compatible (tr.HonestBlocks H) C C'

/-- **`V_s` up to `b`**: every honest vote at a time `≤ b` of a slot `m` with `j < m ≤ s`
extends every origin within `b` of label `j`. -/
def VotesBelowUpTo (s : Nat) (b : Time) : Prop :=
  ∀ C j, OriginWithin tr H C j b → ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → tr.time i ≤ b →
    j < e.msg.slot → e.msg.slot ≤ s → SA.VoteExtends (tr.HonestBlocks H) e.msg C

variable {tr H}

theorem sleepyPrefix_iff {ΔF b : Time} :
    SleepyPrefix tr H ΔF b ↔ 0 ≤ b ∧ tr.SyncRun H ΔF 0 (b - sp.Δ) ∧
      ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
        tr.FaultBound H (sp.ts s + d) :=
  Iff.rfl

theorem originWithin_iff {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {b : Time} :
    OriginWithin tr H C s b ↔ ∃ x ∈ H, ∃ i CV, tr.time i ≤ b ∧
      (SA.ResultAt tr.projAC x i s C CV ∨ SA.OptimisticLockAt tr.projAC x i s C CV) :=
  Iff.rfl

theorem onOriginChainWithin_iff {B : SA.Blk sp.n (List (FG.Att sp.n))} {b : Time} :
    OnOriginChainWithin tr H B b ↔
      B.root = sp.genesisRoot ∨ ∃ C s, OriginWithin tr H C s b ∧ Anc (tr.HonestBlocks H) B C :=
  Iff.rfl

theorem originsBelowUpTo_iff {s : Nat} {b : Time} :
    OriginsBelowUpTo tr H s b ↔ ∀ C j C' j', j < s → j' < s → OriginWithin tr H C j b →
      OriginWithin tr H C' j' b → Compatible (tr.HonestBlocks H) C C' :=
  Iff.rfl

theorem votesBelowUpTo_iff {s : Nat} {b : Time} :
    VotesBelowUpTo tr H s b ↔ ∀ C j, OriginWithin tr H C j b → ∀ y ∈ H, ∀ i e,
      SA.VoteAt tr.projAC y i e → tr.time i ≤ b → j < e.msg.slot → e.msg.slot ≤ s →
        SA.VoteExtends (tr.HonestBlocks H) e.msg C :=
  Iff.rfl

theorem OriginWithin.origin {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {b : Time}
    (h : OriginWithin tr H C s b) : Origin tr H C s :=
  let ⟨x, hx, i, CV, _, h⟩ := h
  ⟨x, hx, i, CV, h⟩

theorem OriginWithin.mono {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {b b' : Time}
    (h : OriginWithin tr H C s b) (hb : b ≤ b') : OriginWithin tr H C s b' :=
  let ⟨x, hx, i, CV, hi, h⟩ := h
  ⟨x, hx, i, CV, hi.trans hb, h⟩

/-- Every origin is within some horizon (the time of its event). -/
theorem Origin.exists_within {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (h : Origin tr H C s) : ∃ b, OriginWithin tr H C s b :=
  let ⟨x, hx, i, CV, h⟩ := h
  ⟨tr.time i, x, hx, i, CV, le_rfl, h⟩

/-- An origin whose event precedes a cut within `b` is within `b`. -/
theorem OriginBefore.within {C : SA.Blk sp.n (List (FG.Att sp.n))} {s i : Nat} {b : Time}
    (h : OriginBefore tr H C s i) (hi : ∀ k < i, tr.time k ≤ b) : OriginWithin tr H C s b :=
  let ⟨x, hx, k, hk, CV, h⟩ := h
  ⟨x, hx, k, CV, hi k hk, h⟩

theorem OnOriginChainWithin.onOriginChain {B : SA.Blk sp.n (List (FG.Att sp.n))} {b : Time}
    (h : OnOriginChainWithin tr H B b) : OnOriginChain tr H B :=
  h.imp_right fun ⟨C, s, hC, hBC⟩ => ⟨C, s, hC.origin, hBC⟩

/-- `P_s` gives `P_s` up to every `b`. -/
theorem OriginsBelow.upTo {s : Nat} (h : OriginsBelow tr H s) (b : Time) :
    OriginsBelowUpTo tr H s b :=
  fun C j C' j' hj hj' hC hC' => originsBelow_iff.1 h C j C' j' hj hj' hC.origin hC'.origin

/-- `V_s` gives `V_s` up to every `b`. -/
theorem VotesBelow.upTo {s : Nat} (h : VotesBelow tr H s) (b : Time) :
    VotesBelowUpTo tr H s b :=
  fun C j hC y hy i e hv _ hj hs => votesBelow_iff.1 h C j hC.origin y hy i e hv hj hs

/-- Every cut is within a horizon `b ≥ 0`. -/
theorem exists_horizon {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    (hrun : GoldilocksRun dg H tr) (i : Nat) : ∃ b, 0 ≤ b ∧ ∀ k < i, tr.time k ≤ b :=
  ⟨max 0 (tr.time (i - 1)), le_max_left _ _,
    fun _ hk => (hrun.time_mono (by omega)).trans (le_max_right _ _)⟩

/-- **`Sleepy` gives the prefix premises up to every `b ≥ 0`.** -/
theorem _root_.Consensus.Goldilocks.RunTrace.SleepyRun.prefix {ΔF : Time}
    (hsl : tr.SleepyRun H ΔF) {b : Time} (hb : 0 ≤ b) : SleepyPrefix tr H ΔF b := by
  refine ⟨hb, show tr.SyncOn H ΔF _ _ id from
    ⟨hsl.1.deltaF, fun x hx i m hm hw => hsl.1.message x hx i m hm hw.1,
      fun x hx i B hB hw => hsl.1.block x hx i B hB hw.1,
      fun x hx i B hB hw => hsl.1.relay x hx i B hB hw.1,
      fun x hx i a h hw => hsl.1.attestation x hx i a h hw.1⟩, fun s d hd _ => ?_⟩
  obtain ⟨h0, h1, h2⟩ := hsl.2 s
  have hT : sp.toParams.slotTime s = sp.ts s := by
    rw [sp.slotTime_eq]; simp only [SAParams.ts]
  rw [hT] at h0 h1 h2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases hd with rfl | rfl | rfl
  · simpa using h0
  · exact h1
  · exact h2

variable (tr H)

/-- **The Sleepy record invariant up to `b`** (S1–S3 restricted to the origins within `b`, the
honest votes at times `≤ b`, and the cuts within `b`: every earlier cut at a time `≤ b`). -/
structure SleepyInvariantUpTo (b : Time) : Prop where
  /-- S1: any two origins within `b` are compatible. -/
  origins_compatible : ∀ C s C' s', OriginWithin tr H C s b → OriginWithin tr H C' s' b →
    Compatible (tr.HonestBlocks H) C C'
  /-- S2: every honest vote at a time `≤ b` of a slot after the label of an origin within `b`
  extends it. -/
  vote_extends : ∀ C s, OriginWithin tr H C s b → ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e →
    tr.time i ≤ b → s < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg C
  /-- S1: at a cut within `b`, every honest record names a block of the node's tree that is
  genesis or an origin within `b`. -/
  record : ∀ y ∈ H, ∀ i, (∀ k < i, tr.time k ≤ b) →
    ∃ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y i).ac.latestConfirmed ∧
      (C.root = sp.genesisRoot ∨ ∃ s, OriginWithin tr H C s b)
  /-- S1: at a cut within `b`, every honest `Σ.F` and `Σ.J` is on the chain of the origins
  within `b`. -/
  caches : ∀ y ∈ H, ∀ i, (∀ k < i, tr.time k ≤ b) →
    OnOriginChainWithin tr H (tr.state y i).fg.F b ∧
      OnOriginChainWithin tr H (tr.state y i).fg.J b
  /-- S1: at a cut within `b`, every honest stored lock names a block of the node's tree on the
  chain of the origins within `b`. -/
  locks : ∀ y ∈ H, ∀ i, (∀ k < i, tr.time k ≤ b) → ∀ l ∈ (tr.state y i).ac.locks,
    ∃ L ∈ (tr.state y i).fg.tree, L.root = l.block ∧ OnOriginChainWithin tr H L b
  /-- S1: at a cut within `b`, every honest FG source is on the chain of the origins within
  `b`. -/
  sources : ∀ y ∈ H, ∀ i, (∀ k < i, tr.time k ≤ b) → ∀ ℓ C, SA.ToFGAt tr.projAC y i ℓ C →
    OnOriginChainWithin tr H C b
  /-- S3 (full reads): at a cut within `b`, an origin within `b` that an honest node holds is at
  or below its `fc_root`, or in its full viable tree. -/
  viable : ∀ y ∈ H, ∀ i, (∀ k < i, tr.time k ≤ b) → ∀ C s, OriginWithin tr H C s b →
    C ∈ (Node.frame (tr.state y i)).tree →
    (Node.frame (tr.state y i)).Anc C (Node.frame (tr.state y i)).fcRoot ∨
      C ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree

end Consensus.Goldilocks.Compose

end
