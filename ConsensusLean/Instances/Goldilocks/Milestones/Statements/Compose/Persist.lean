module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGStore.Trace

@[expose] public section

/-! # Goldilocks milestone Persist, part 2: honest fast confirmations persist (statements)

Transcribed from `specs/goldilocks/tex/goldilocks-claims.tex`,
C1.1 over the Goldilocks run (`Spec/Run`, `GoldilocksRun`): the induction over the
events of the run (F.5 (run)) that joins the per-vote transfer steps A1.2–A1.4 (`Statements/AC`),
the source step A1.9 and the FG cut G1.10 (`Statements/FGStore`). Its premises are the run
premises of the claims (`Sync[t_s, t_m + Δ]`, `Carry`, half-committee honest votes, `f < h_t` at
the vote times, `NoColl`, unforgeability from `GoldilocksRun`) and **`Clean(s, m, B)`**: (K0) the
honest caches at `t_s` are compatible with `B`, (K1) the attestation cut of G1.10 at the scope of
C1.1 (`Store.namers` of the FG projection, at `T₀ = t_{s+1} + Δ`, below `q` for every entry that
conflicts with `B` and strictly extends an honest `Σ.F` at `t_s`), (K2) the height lead at each
honest vote of a slot in `(s, m]`.

The AC-side notions (votes, `Carry`, fast locks, `ac_to_fg`, viability at a vote) are read on
the AC projection of the run (`SA.*` over `tr.projAC`), the FG-side ones (signings, the attestation
cut) on its FG projection; the run premises (`Sync`, `f < h_t`) are the run's (`JoinedProjection`
bridges them to the AC projection's). "The state of `y` at `t`" is `y`'s state before the first
cut of the run at a time `≥ t` (`FirstCutFrom`).

C1.1 itself is retired as a milestone statement; its premises (`PersistPremises`) stay, as
vocabulary that downstream code reads.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder goldilocksSA Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- The votes of the honest validators of slot `σ` in the run (the counted set of A1.3's
`Carry` for the later slots). -/
def honestVotes (σ : Nat) : Set (Vote sp.n) :=
  {v | ∃ x ∈ H, ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg = v ∧ v.slot = σ}

/-- **The excluded entries of C1.1's scope of G1.10**: the blocks that conflict with `B` and
strictly extend the `Σ.F` of some honest node at `t_s` (inside the honest blocks of the run). -/
def excludedEntries (s : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) :
    Set (SA.Blk sp.n (List (FG.Att sp.n))) :=
  {E' | ¬ Compatible (tr.HonestBlocks H) E' B ∧
    ∃ y ∈ H, ∃ j, tr.FirstCutFrom j (sp.ts s) ∧
      Anc (tr.HonestBlocks H) (tr.state y j).fg.F E' ∧ E' ≠ (tr.state y j).fg.F}

/-- **`Clean(s, m, B)`** (claims C1.1): the premises on the honest caches, the attestations and the
heights that the regime nodes discharge. -/
structure Clean (s m : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) : Prop where
  /-- (K0) Honest caches: at `t_s`, the `Σ.F` and the `Σ.J` of every honest node are compatible
  with `B`. -/
  caches : ∀ y ∈ H, ∀ j, tr.FirstCutFrom j (sp.ts s) →
    Compatible (tr.HonestBlocks H) (tr.state y j).fg.F B ∧
      Compatible (tr.HonestBlocks H) (tr.state y j).fg.J B
  /-- (K1) FG attestation cut (the claims' attestation cut): for every excluded entry `E'`, the
  validators that are faulty, or honest and
  sign at or before `t_{s+1} + Δ` an attestation whose height pair names `E'`, number fewer
  than `q`. -/
  fgAttCut : ∀ E' ∈ excludedEntries tr H s B,
    (Store.namers sp.toParams (Payload sp.n) H tr.projFG (sp.ts (s + 1 : Nat) + sp.Δ) E').ncard <
      sp.toParams.fg.q
  /-- (K2) Height lead: at each honest vote of a slot in `(s, m]`, the voter block tree holds a
  descendant of `B` (or `B`) whose state height is at least the voter's head height floor, or
  `B ⪯ fc_root` at the voter (block order inside the honest blocks, as in (i)). -/
  heightLead : ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → s < e.msg.slot → e.msg.slot ≤ m →
    (∃ D ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
      Anc (tr.HonestBlocks H) B D ∧ (tr.state y i).fg.IsViable D) ∨
    Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot

/-- **A stored fast lock** (claims C1.1, HR.4: "the stored block after the move back"): `x`
writes a fast lock of slot `s` at cut `i` (fast test or optimistic confirmation) that selects `D`
with counted votes `CV`, and `B` is the block it stores, `D` moved back to its viable ancestor in
the frame of that write (`add_locks` keeps the live locks, each moved back: `liveLocks`). -/
def StoredFastLockAt (x : Fin sp.n) (i s : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n)))
    (CV : Set (Vote sp.n)) : Prop :=
  ∃ ℓ D, tr.projAC.CallAt x i ℓ ∧ SA.FastLockAt tr.projAC x i s D CV ∧
    B = ℓ.frame.viableAncestor D

/-- **The premises of C1.1** for a fast lock of slot `s` on `B` with counted votes `CV`, written
at cut `i₀` by the honest joined node `x`, and a later slot `m`: `Sync[t_s, t_m + Δ]`,
`Carry(s, S, B)`, for every slot `s' ∈ (s, m]` honest votes of at least half of the committee
and `Carry(s', S_{s'}, B)` with `S_{s'}` the honest voters of slot `s'`, `f < h_t` at every
honest vote time in `(t_s, t_m + Δ]`, `NoColl`, and `Clean(s, m, B)` (unforgeability is
`GoldilocksRun`'s). -/
structure PersistPremises (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (ΔF : Time)
    (x : Fin sp.n) (i₀ s m : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) (CV : Set (Vote sp.n)) :
    Prop where
  /-- The writer is honest. -/
  writer_honest : x ∈ H
  /-- The writer writes a fast lock of slot `s` at cut `i₀`, counting `CV`, whose stored block
  (after the move back) is `B` (claims C1.1). -/
  fastLock : StoredFastLockAt tr x i₀ s B CV
  /-- The writer is joined at the write. -/
  writer_joined : SA.joined sp (tr.state x i₀).ac (tr.time i₀)
  /-- `s < m`. -/
  lt : s < m
  /-- `Sync[t_s, t_m + Δ]`. -/
  sync : tr.SyncRun H ΔF (sp.ts s) (sp.ts m + sp.Δ)
  /-- `Carry(s, S, B)`. -/
  carry : SA.Carry tr.projAC H (tr.HonestBlocks H) s CV
  /-- For every slot `s' ∈ (s, m]`, at least half of the committee votes honestly. -/
  halfCommittee : ∀ s', s < s' → s' ≤ m →
    sp.n ≤ 2 * {x' | x' ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x' j e' ∧ e'.msg.slot = s'}.ncard
  /-- For every slot `s' ∈ (s, m]`, `Carry(s', S_{s'}, B)` for the honest votes of slot `s'`. -/
  carryLater : ∀ s', s < s' → s' ≤ m →
    SA.Carry tr.projAC H (tr.HonestBlocks H) s' (honestVotes tr H s')
  /-- `f < h_t` at every honest vote time `t ∈ (t_s, t_m + Δ]`. -/
  faultBound : ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → sp.ts s < tr.time i →
    tr.time i ≤ sp.ts m + sp.Δ → tr.FaultBound H (tr.time i)
  /-- `NoColl` on the blocks of the run. -/
  noColl : NoCollRun dg tr
  /-- `Clean(s, m, B)`. -/
  clean : Clean tr H s m B
  /-- The committee is population-sized (`committeeSize = n`). -/
  stock : sp.committeeSize = sp.n

end Consensus.Goldilocks.Compose

end
