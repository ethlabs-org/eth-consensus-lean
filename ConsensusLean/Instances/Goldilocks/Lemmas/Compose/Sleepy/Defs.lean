module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection

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

/-- The finite Sleepy consumers need SA evidence and actual block acceptance relay,
not fresh processing of every repeated vote or attestation admission. -/
structure SleepyServiceBefore {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (ΔF b : Time) : Prop where
  deltaF : 0 < ΔF
  ac : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC
  relay : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → 0 ≤ tr.time i →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (tr.time i) sp.Δ ≤ b →
      tr.deadline y j (tr.time i) sp.Δ ≤ tr.time j →
      Anc (tr.HonestBlocks H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j (tr.time i) B

/-- Assemble finite Sleepy service from SA message evidence and node acceptance relay.
The latter also supplies AC acceptance relay via the following AC block cut. -/
theorem sleepyServiceBefore_of_message_relay
    {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)} {b : Time}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    (hr : Node.LocalRun proposer dg H SA.Vote.val tr)
    (message : ∀ x ∈ H, ∀ i v, tr.projAC.SendOrAdmit x i v → 0 ≤ tr.time i →
      ∀ y ∈ H, ∀ j ℓ, tr.projAC.CallAt y j ℓ → tr.projAC.deadline y j (tr.time i) ≤ b →
        tr.projAC.deadline y j (tr.time i) ≤ tr.time j →
          SA.MessageServedBefore tr.projAC y j (tr.time i) v)
    (relay : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → 0 ≤ tr.time i →
      ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (tr.time i) sp.Δ ≤ b →
        tr.deadline y j (tr.time i) sp.Δ ≤ tr.time j →
        Anc (tr.HonestBlocks H) (tr.state y j).fg.F B →
        tr.BlockAcceptedBy y j (tr.time i) B) :
    SleepyServiceBefore tr H sp.Δ b := by
  refine ⟨sp.toParams.hΔ, ⟨message, ?_⟩, relay⟩
  intro x hx i B hacc hai y hy j ℓ hc hdb hdl hanc
  obtain ⟨ℓ₀, hc₀, hb⟩ := hacc
  have hc := projAC_callAt.mp hc
  obtain ⟨i', rfl, hi', hti⟩ := acBlock_prev hr hx (projAC_callAt.mp hc₀) hb
  have hfr : ℓ.frame.F = (tr.state y j).fg.F := by
    rw [(hr.cutLaw y hy j _ hc).1]
    rfl
  obtain ⟨k, hkj, hk, hlt⟩ := relay x hx i' B hi' (hti ▸ hai) y hy j ⟨_, hc⟩
    (by rw [hti, ← projAC_deadline]; exact hdb)
    (by rw [hti, ← projAC_deadline]; exact hdl) (hfr ▸ hanc)
  obtain ⟨ℓ', hc', hb', htk⟩ := accept_next hr hy hk
  have hkj' : k + 1 ≤ j := by
    rcases Nat.lt_or_eq_of_le hkj with hlt' | rfl
    · omega
    · cases Option.some.inj (hk.2.symm.trans hc.2)
  have hnr : ¬ tr.RestartAt y (k + 1) := fun ⟨ℓr, hcr, hrestart⟩ => by
    cases Option.some.inj (hc'.2.symm.trans hcr.2)
    rw [hb'] at hrestart
    cases hrestart
  refine ⟨k + 1, hkj', ⟨ℓ', projAC_callAt.mpr hc', hb'⟩, ?_⟩
  change tr.time (k + 1) < tr.projAC.deadline y (k + 1) (tr.time (i' + 1))
  rw [projAC_deadline, htk, ← hti]
  simp only [RunTrace.deadline, RunTrace.lastWake, hnr, ite_false] at hlt ⊢
  exact hlt

/-- Existing node synchrony is sufficient for the specialized Sleepy service. -/
theorem sleepyServiceBefore_of_sync {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)} {ΔF b : Time}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    (hr : Node.LocalRun proposer dg H SA.Vote.val tr) (hs : tr.SyncBefore H ΔF b) :
    SleepyServiceBefore tr H ΔF b :=
  ⟨hs.deltaF, SA.serviceBefore_of_sync (syncBefore_projection hr hs), hs.relay⟩

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

The send-window prefix premises up to `b` (`SleepyPrefix`: `Sync[0, b − Δ]`
and `f < h_t` at the slot points `≤ b`), the origins whose event is at a time `≤ b`
(`OriginWithin`), and the invariant restricted to them and to the cuts **within `b`** (every
earlier cut at a time `≤ b`, so that the state before the cut is the state at a time `≤ b`):
`SleepyInvariantUpTo`. -/

/-- **The send-window prefix premises up to `b`**: `Sync[0, b − Δ]` and `f < h_t` at
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
    {proposer : Nat → Fin sp.n} (hrun : GoldilocksRun proposer dg H tr) (i : Nat) :
    ∃ b, 0 ≤ b ∧ ∀ k < i, tr.time k ≤ b :=
  ⟨max 0 (tr.time (i - 1)), le_max_left _ _,
    fun _ hk => (hrun.time_mono (by omega)).trans (le_max_right _ _)⟩

/-- **`Sleepy` gives the prefix premises up to every `b ≥ 0`.** -/
theorem _root_.Consensus.Goldilocks.RunTrace.SleepyRun.prefix {ΔF : Time}
    (hsl : tr.SleepyRun H ΔF) {b : Time} (hb : 0 ≤ b) : SleepyPrefix tr H ΔF b := by
  refine ⟨hb, show tr.SyncOn H ΔF _ _ id from
    ⟨hsl.1.deltaF, hsl.1.delta_le, fun x hx i m hm hw => hsl.1.message x hx i m hm hw.1,
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

/-! ### The invariant from a start label `s₀`

The induction started at a label `s₀` (after a heal, R.6): the premises from `t_{s₀}` on
(`SleepyFrom`: `Sync[t_{s₀}, ∞)` and `f < h_t` at the slot points of the slots `≥ s₀`), the
origins of labels `≥ s₀` (`OriginFrom`, whole-run), the pre-`s₀` history replaced by the base
facts `SleepyBase`, and the invariant over those origins at the cuts from `t_{s₀}` on
(`SleepyInvariantFrom`). The step lemmas run on a window `[t_{s₀}, b]` (`SleepyWindow`), which
both the prefix premises (`s₀ = 0`) and `SleepyFrom` give. -/

/-- **The Sleepy premises on the window from slot `s₀` to `b`**: `Sync[t_{s₀}, b − Δ]` and
`f < h_t` at every `t ∈ {t_s, t_s + Δ, t_s + 2Δ}` with `s ≥ s₀` and `t ≤ b`. -/
def SleepyWindow (ΔF : Time) (s₀ : Nat) (b : Time) : Prop :=
  sp.ts s₀ ≤ b ∧ tr.SyncRun H ΔF (sp.ts s₀) (b - sp.Δ) ∧
    ∀ s : Nat, s₀ ≤ s → ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d)

/-- **The Sleepy premises from slot `s₀`**: `Sync[t_{s₀}, ∞)` and `f < h_t` at every
`t ∈ {t_s, t_s + Δ, t_s + 2Δ}` with `s ≥ s₀`. -/
def SleepyFrom (ΔF : Time) (s₀ : Nat) : Prop :=
  tr.SyncOn H ΔF (fun τ => sp.ts s₀ ≤ τ) (fun τ => sp.ts s₀ ≤ τ) id ∧
    ∀ s : Nat, s₀ ≤ s → ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), tr.FaultBound H (sp.ts s + d)

/-- An origin of label `s ≥ s₀` (whole-run, as `Origin`). -/
def OriginFrom (C : SA.Blk sp.n (List (FG.Att sp.n))) (s s₀ : Nat) : Prop :=
  Origin tr H C s ∧ s₀ ≤ s

/-- `B` is on the ancestor closure of the origins of labels `≥ s₀`: genesis (an ancestor of every
honest block, so compatible with all of them), or an ancestor (inside the honest blocks) of an
origin of label `≥ s₀`. -/
def OnOriginChainFrom (B : SA.Blk sp.n (List (FG.Att sp.n))) (s₀ : Nat) : Prop :=
  B.root = sp.genesisRoot ∨ ∃ C s, OriginFrom tr H C s s₀ ∧ Anc (tr.HonestBlocks H) B C

variable {tr H}

theorem sleepyWindow_iff {ΔF b : Time} {s₀ : Nat} :
    SleepyWindow tr H ΔF s₀ b ↔ sp.ts s₀ ≤ b ∧ tr.SyncRun H ΔF (sp.ts s₀) (b - sp.Δ) ∧
      ∀ s : Nat, s₀ ≤ s → ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
        tr.FaultBound H (sp.ts s + d) :=
  Iff.rfl

theorem sleepyFrom_iff {ΔF : Time} {s₀ : Nat} :
    SleepyFrom tr H ΔF s₀ ↔ tr.SyncOn H ΔF (fun τ => sp.ts s₀ ≤ τ) (fun τ => sp.ts s₀ ≤ τ) id ∧
      ∀ s : Nat, s₀ ≤ s → ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time),
        tr.FaultBound H (sp.ts s + d) :=
  Iff.rfl

theorem originFrom_iff {C : SA.Blk sp.n (List (FG.Att sp.n))} {s s₀ : Nat} :
    OriginFrom tr H C s s₀ ↔ Origin tr H C s ∧ s₀ ≤ s :=
  Iff.rfl

theorem onOriginChainFrom_iff {B : SA.Blk sp.n (List (FG.Att sp.n))} {s₀ : Nat} :
    OnOriginChainFrom tr H B s₀ ↔
      B.root = sp.genesisRoot ∨ ∃ C s, OriginFrom tr H C s s₀ ∧ Anc (tr.HonestBlocks H) B C :=
  Iff.rfl

/-- `t_0 = 0`. -/
theorem ts_natCast_zero : sp.ts ((0 : Nat) : Int) = 0 := by
  simp [SAParams.ts]

/-- **The prefix premises up to `b` are the window premises from slot `0` to `b`.** -/
theorem SleepyPrefix.window {ΔF b : Time} (hpre : SleepyPrefix tr H ΔF b) :
    SleepyWindow tr H ΔF 0 b := by
  obtain ⟨hb, hs, hfb⟩ := sleepyPrefix_iff.1 hpre
  rw [sleepyWindow_iff, ts_natCast_zero]
  exact ⟨hb, hs, fun s _ d hd h => hfb s d hd h⟩

/-- **`SleepyFrom` gives the window premises from slot `s₀` to every `b ≥ t_{s₀}`.** -/
theorem SleepyFrom.window {ΔF b : Time} {s₀ : Nat} (hfrom : SleepyFrom tr H ΔF s₀)
    (hb : sp.ts s₀ ≤ b) : SleepyWindow tr H ΔF s₀ b := by
  obtain ⟨hs, hfb⟩ := sleepyFrom_iff.1 hfrom
  exact ⟨hb, show tr.SyncOn H ΔF _ _ id from
    ⟨hs.deltaF, hs.delta_le, fun x hx i m hm hw => hs.message x hx i m hm hw.1,
      fun x hx i B hB hw => hs.block x hx i B hB hw.1,
      fun x hx i B hB hw => hs.relay x hx i B hB hw.1,
      fun x hx i a h hw => hs.attestation x hx i a h hw.1⟩,
    fun s hs d hd _ => hfb s hs d hd⟩

theorem OriginFrom.origin {C : SA.Blk sp.n (List (FG.Att sp.n))} {s s₀ : Nat}
    (h : OriginFrom tr H C s s₀) : Origin tr H C s :=
  h.1

theorem OriginFrom.le {C : SA.Blk sp.n (List (FG.Att sp.n))} {s s₀ : Nat}
    (h : OriginFrom tr H C s s₀) : s₀ ≤ s :=
  h.2

variable (tr H)

/-- **The base facts at a start label `s₀`** (the pre-`s₀` history that the induction from `s₀`
reads; the paper side, ACBase, discharges them). Each field is stated as weakly as its consumer
allows: the pre-`s₀` cases only, at the cuts the consumer reads. For `s₀ = 0` every field holds
of every Goldilocks run under `SleepyFrom` slot `0` (`sleepyBase_zero`). -/
structure SleepyBase (s₀ : Nat) : Prop where
  /-- (1) **Locks**, read by the lock step of the vote induction (`vote_locks_compatible_from`,
  through `first_transfer_step_from` and `later_transfer_step_from`): at an honest vote of a slot
  `> s₀`, every live lock block of a read-point lock of slot `< s₀` is compatible with every
  origin of a label in `[s₀, slot)`. (A read-point lock of slot `≥ s₀` sits below an origin of
  its slot, `lock_origin`; an expired stored lock is not read.) -/
  locks : ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → s₀ < e.msg.slot →
    ∀ L ∈ SA.liveLockBlocks sp {l ∈ e.readPoint.locks | l.slot < s₀} ℓ.frame (tr.time i),
      ∀ C j, OriginFrom tr H C j s₀ → j < e.msg.slot → Compatible (tr.HonestBlocks H) L C
  /-- (2) **Records**, read by `SleepyInvariantFrom.record`: at a cut from `t_{s₀} + 6Δ`, a
  record whose block is an origin of a label `< s₀` is on the chain from `s₀` or at or below
  `Σ.F`. -/
  records : ∀ y ∈ H, ∀ i, sp.ts s₀ + 6 * sp.Δ ≤ tr.time i → ∀ C ∈ (tr.state y i).fg.tree,
    C.root = (tr.state y i).ac.latestConfirmed → (∃ s < s₀, Origin tr H C s) →
      OnOriginChainFrom tr H C s₀ ∨ Anc (tr.HonestBlocks H) C (tr.state y i).fg.F
  /-- (3) **Caches**, read by `SleepyInvariantFrom.caches` only (no step lemma reads them): at a
  cut from `t_{s₀+2}`, `Σ.F` and `Σ.J` are on the chain from `s₀`. -/
  caches : ∀ y ∈ H, ∀ i, sp.ts (s₀ + 2 : Nat) ≤ tr.time i →
    OnOriginChainFrom tr H (tr.state y i).fg.F s₀ ∧ OnOriginChainFrom tr H (tr.state y i).fg.J s₀
  /-- (3) **Sources**, read by `SleepyInvariantFrom.sources` only (no step lemma reads them): at
  a cut from `t_{s₀+2}`, an FG source below an origin of a label `< s₀` (the block of a live fast
  lock of a slot `< s₀`) is on the chain from `s₀`. -/
  sources : ∀ y ∈ H, ∀ i ℓ C, SA.ToFGAt tr.projAC y i ℓ C → sp.ts (s₀ + 2 : Nat) ≤ tr.time i →
    (∃ C' l, Origin tr H C' l ∧ l < s₀ ∧ Anc (tr.HonestBlocks H) C C') →
      OnOriginChainFrom tr H C s₀
  /-- (5) **Rows at votes**, read by `vote_frame_from` (the source geometry of `Σ.J` and of the
  floor crossing, at heights `≥ h_j`): at an honest vote of slot `s + 1 > s₀`, an honest row on a
  block the voter holds, whose named entry has height `≥ h_j`, and whose signing source is below
  an origin of a label `< s₀`, has an honest source below an origin of a label in `[s₀, s]`. -/
  vote_rows : ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → ∀ s, e.msg.slot = s + 1 →
    s₀ ≤ s → ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H →
      (tr.state y i).fg.hj ≤ ((tr.state y i).fg.σ a.T).h →
      (∃ D C l, (∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧
        ((tr.state x k).fg.σ D.root).Th = a.T) ∧ Origin tr H C l ∧ l < s₀ ∧
          Anc (tr.HonestBlocks H) D C) →
      ∃ D C l, (∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧
        ((tr.state x k).fg.σ D.root).Th = a.T) ∧ OriginFrom tr H C l s₀ ∧ l ≤ s ∧
          Anc (tr.HonestBlocks H) D C
  /-- (5) **Rows at cuts**, read by `held_origin_viable_from` (S3 at full reads): at a cut from
  `t_{s₀}`, an honest row as in `vote_rows` has an honest source below an origin of a label
  `≥ s₀`. -/
  event_rows : ∀ y ∈ H, ∀ i, sp.ts s₀ ≤ tr.time i → ∀ X ∈ (tr.state y i).fg.tree,
    ∀ a ∈ X.fgPayload, a.val ∈ H → (tr.state y i).fg.hj ≤ ((tr.state y i).fg.σ a.T).h →
      (∃ D C l, (∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧
        ((tr.state x k).fg.σ D.root).Th = a.T) ∧ Origin tr H C l ∧ l < s₀ ∧
          Anc (tr.HonestBlocks H) D C) →
      ∃ D C l, (∃ x ∈ H, ∃ k, D ∈ (tr.state x k).fg.tree ∧
        ((tr.state x k).fg.σ D.root).Th = a.T) ∧ OriginFrom tr H C l s₀ ∧
          Anc (tr.HonestBlocks H) D C
  /-- (6) **Old blocks caught up**, read by the frozen witness (`vote_frame_from`) and by the
  carry of the counted votes (`result_carry_win`, `optimistic_carry_win`, the honest batch;
  through `first_transfer_step_from` and `later_transfer_step_from`): `Sync[t_{s₀}, ∞)` relays
  only acceptances from `t_{s₀}` on, so a vote head that its writer accepted before `t_{s₀}` must
  reach an honest slot-`(s+1)` voter (`s ≥ s₀`) whose `Σ.F` it extends before the freeze
  `t_s + 3Δ` by other means (`Catch(κ)` after a heal). -/
  old_blocks : ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → ∀ s, e.msg.slot = s + 1 →
    s₀ ≤ s → ∀ x ∈ H, ∀ m B, tr.AcceptAt x m B → tr.time m < sp.ts s₀ →
      Anc (tr.HonestBlocks H) ℓ.frame.F B → SA.AcceptedBefore tr.projAC y B (sp.ts s + 3 * sp.Δ)

/-- **The Sleepy record invariant from `s₀`** (S1–S3 over the origins of labels `≥ s₀`, at the
cuts from `t_{s₀}`; records from `t_{s₀} + 6Δ`, caches and sources from `t_{s₀+2}`). -/
structure SleepyInvariantFrom (s₀ : Nat) : Prop where
  /-- S1: any two origins of labels `≥ s₀` are compatible. -/
  origins_compatible : ∀ C s C' s', OriginFrom tr H C s s₀ → OriginFrom tr H C' s' s₀ →
    Compatible (tr.HonestBlocks H) C C'
  /-- S2: every honest vote of a slot after the label `≥ s₀` of an origin extends it. -/
  vote_extends : ∀ C s, OriginFrom tr H C s s₀ → ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e →
    s < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg C
  /-- S1: at a cut from `t_{s₀} + 6Δ`, every honest record names a block of the node's tree that
  is genesis or an origin of a label `≥ s₀`, or (a pre-`s₀` record, `SleepyBase.records`) on the
  chain from `s₀` or at or below `Σ.F`. -/
  record : ∀ y ∈ H, ∀ i, sp.ts s₀ + 6 * sp.Δ ≤ tr.time i →
    ∃ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y i).ac.latestConfirmed ∧
      ((C.root = sp.genesisRoot ∨ ∃ s, OriginFrom tr H C s s₀) ∨ OnOriginChainFrom tr H C s₀ ∨
        Anc (tr.HonestBlocks H) C (tr.state y i).fg.F)
  /-- S1: at a cut from `t_{s₀+2}`, every honest `Σ.F` and `Σ.J` is on the chain from `s₀`. -/
  caches : ∀ y ∈ H, ∀ i, sp.ts (s₀ + 2 : Nat) ≤ tr.time i →
    OnOriginChainFrom tr H (tr.state y i).fg.F s₀ ∧ OnOriginChainFrom tr H (tr.state y i).fg.J s₀
  /-- S1: every honest stored lock of a slot `≥ s₀` names a block of the node's tree on the
  chain from `s₀`. -/
  locks : ∀ y ∈ H, ∀ i, ∀ l ∈ (tr.state y i).ac.locks, s₀ ≤ l.slot →
    ∃ L ∈ (tr.state y i).fg.tree, L.root = l.block ∧ OnOriginChainFrom tr H L s₀
  /-- S1: at a cut from `t_{s₀+2}`, every honest FG source is on the chain from `s₀`. -/
  sources : ∀ y ∈ H, ∀ i ℓ C, SA.ToFGAt tr.projAC y i ℓ C → sp.ts (s₀ + 2 : Nat) ≤ tr.time i →
    OnOriginChainFrom tr H C s₀
  /-- S3 (full reads): at a cut from `t_{s₀}`, an origin of a label `≥ s₀` that an honest node
  holds is at or below its `fc_root`, or in its full viable tree. -/
  viable : ∀ y ∈ H, ∀ i, sp.ts s₀ ≤ tr.time i → ∀ C s, OriginFrom tr H C s s₀ →
    C ∈ (Node.frame (tr.state y i)).tree →
    (Node.frame (tr.state y i)).Anc C (Node.frame (tr.state y i)).fcRoot ∨
      C ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree

end Consensus.Goldilocks.Compose

end
