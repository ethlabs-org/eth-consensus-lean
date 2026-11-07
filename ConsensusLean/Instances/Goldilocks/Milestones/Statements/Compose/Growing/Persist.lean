module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Persist
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGStore.Growing

@[expose] public section

/-! # Goldilocks milestone Persist under growing faults (statements)

C1.1 (`Statements/Compose/Persist`) for a time-indexed honest set `H` (antitone), over
`Growing.GoldilocksRun`:

* the writer is honest at its write; votes are those of nodes honest at their votes; every node
  named at a cut is honest at that cut; caches at `t_s` are those of nodes honest at `t_s`;
* the counts are charged where they are consumed: `f < h_t` at each vote time; the
  half-committee of slot `s'` among the validators honest at `t_{s'+1} + Δ`, by when the votes of
  slot `s' + 1` that read it are cast, that voted in slot `s'` while honest; and `2 f < n` at
  `t_m + Δ`, the last `ac_to_fg` call the attestations read;
* **(K1)**, the attestation cut of G1.10 at the scope of C1.1, is charged at the consumption
  horizon of the whole induction, `d = t_m + 2Δ` (every block the cuts cover is accepted before
  `t_{s'} + 2Δ ≤ t_m + 2Δ`): the namers of an excluded entry are the validators compromised by
  `d` or naming it by `T₀ = t_{s+1} + Δ`. A consumer discharges it from a fault bound at `d`, not
  from a fixed honest set.

At `H := fun _ => H₀` each statement implies its static counterpart.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder goldilocksSA Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- The votes of slot `σ` of the validators honest at their votes. -/
def honestVotes (σ : Nat) : Set (Vote sp.n) :=
  {v | ∃ x j e', x ∈ H (tr.time j) ∧ SA.VoteAt tr.projAC x j e' ∧ e'.msg = v ∧ v.slot = σ}

/-- **The excluded entries of C1.1's scope of G1.10** under growing faults: the blocks that
conflict with `B` and strictly extend the `Σ.F` at `t_s` of some node honest at `t_s`. -/
def excludedEntries (s : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) :
    Set (SA.Blk sp.n (List (FG.Att sp.n))) :=
  {E' | ¬ Compatible (tr.HonestBlocksAt H) E' B ∧
    ∃ y j, y ∈ H (sp.ts s) ∧ tr.FirstCutFrom j (sp.ts s) ∧
      Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F E' ∧ E' ≠ (tr.state y j).fg.F}

/-- **`Clean(s, m, B)`** under growing faults. -/
structure Clean (s m : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) : Prop where
  /-- (K0) The caches at `t_s` of the nodes honest at `t_s` are compatible with `B`. -/
  caches : ∀ y j, y ∈ H (sp.ts s) → tr.FirstCutFrom j (sp.ts s) →
    Compatible (tr.HonestBlocksAt H) (tr.state y j).fg.F B ∧
      Compatible (tr.HonestBlocksAt H) (tr.state y j).fg.J B
  /-- (K1) The attestation cut, charged at `d = t_m + 2Δ`. -/
  fgAttCut : ∀ E' ∈ excludedEntries tr H s B,
    (Store.Growing.namers sp.toParams (Payload sp.n) H tr.projFG (sp.ts (s + 1 : Nat) + sp.Δ)
      (sp.ts m + 2 * sp.Δ) E').ncard < sp.toParams.fg.q
  /-- (K2) Height lead at each vote of a slot in `(s, m]` by a node honest at its vote. -/
  heightLead : ∀ y i ℓ e, y ∈ H (tr.time i) → SA.CastAt tr.projAC y i ℓ e → s < e.msg.slot →
    e.msg.slot ≤ m →
    (∃ D ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
      Anc (tr.HonestBlocksAt H) B D ∧ (tr.state y i).fg.IsViable D) ∨
    Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot

/-- **The premises of C1.1** under growing faults. -/
structure PersistPremises (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (ΔF : Time)
    (x : Fin sp.n) (i₀ s m : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) (CV : Set (Vote sp.n)) :
    Prop where
  /-- The writer is honest at its write. -/
  writer_honest : x ∈ H (tr.time i₀)
  /-- The writer writes a fast lock of slot `s` at cut `i₀` whose stored block is `B`. -/
  fastLock : StoredFastLockAt tr x i₀ s B CV
  /-- The writer is joined at the write. -/
  writer_joined : SA.joined sp (tr.state x i₀).ac (tr.time i₀)
  /-- `s < m`. -/
  lt : s < m
  /-- `Sync[t_s, t_m + Δ]`. -/
  sync : tr.SyncRunAt H ΔF (sp.ts s) (sp.ts m + sp.Δ)
  /-- `Carry(s, S, B)`. -/
  carry : SA.Growing.Carry tr.projAC H (tr.HonestBlocksAt H) s CV
  /-- For every slot `s' ∈ (s, m]`, at least half of the committee are validators honest at
  `t_{s'+1} + Δ` that vote in slot `s'` while honest. -/
  halfCommittee : ∀ s', s < s' → s' ≤ m →
    sp.n ≤ 2 * {x' | x' ∈ H (sp.ts (s' + 1 : Nat) + sp.Δ) ∧
      ∃ j e', x' ∈ H (tr.time j) ∧ SA.VoteAt tr.projAC x' j e' ∧ e'.msg.slot = s'}.ncard
  /-- For every slot `s' ∈ (s, m]`, `Carry(s', S_{s'}, B)` for the votes of slot `s'`. -/
  carryLater : ∀ s', s < s' → s' ≤ m →
    SA.Growing.Carry tr.projAC H (tr.HonestBlocksAt H) s' (honestVotes tr H s')
  /-- `f < h_t` at every vote time `t ∈ (t_s, t_m + Δ]`, charged at that time. -/
  faultBound : ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e → sp.ts s < tr.time i →
    tr.time i ≤ sp.ts m + sp.Δ → tr.FaultBoundAt H (tr.time i) (tr.time i)
  /-- `2 f < n` at `t_m + Δ`, so at every call up to it (the last `ac_to_fg` call that C1.1's
  attestations read is at `t_m + Δ`, possibly after every vote of slot `m`). -/
  twoFaults : 2 * (H (sp.ts m + sp.Δ))ᶜ.ncard < sp.n
  /-- `NoColl` on the blocks of the run. -/
  noColl : NoCollRun dg tr
  /-- `Clean(s, m, B)`. -/
  clean : Clean tr H s m B

/-- **The conclusion of G1.10 at the scope of C1.1** under growing faults, for `y`: at every
block `y` accepts while honest, and at every cut or state read while `y` is honest. -/
structure CutScopeAt (y : Fin sp.n) (B : SA.Blk sp.n (List (FG.Att sp.n))) (s : Nat) (T : Time) :
    Prop where
  /-- (a), (b) at every block `y` accepts in `[t_s, T + Δ)` while honest, or its own proposal at
  `T + Δ`. -/
  chains : ∀ i X, y ∈ H (tr.time i) → tr.AcceptAt y i X → sp.ts s ≤ tr.time i →
    (tr.time i < T + sp.Δ ∨ (tr.time i = T + sp.Δ ∧ tr.ProposesAt y i X)) →
    let S := (tr.post i).fg
    (∀ A' ∈ S.tree, S.Anc A' X → ∀ Jb, S.blocks (S.σ A'.root).J = some Jb →
      Compatible (tr.HonestBlocksAt H) Jb B) ∧
    (¬ Compatible (tr.HonestBlocksAt H) X B →
      ∀ Pc, Anc (tr.HonestBlocksAt H) Pc X → Anc (tr.HonestBlocksAt H) Pc B →
        (∀ Q, Anc (tr.HonestBlocksAt H) Q X → Anc (tr.HonestBlocksAt H) Q B →
          Anc (tr.HonestBlocksAt H) Q Pc) →
        (S.σ X.root).h ≤ (S.σ Pc.root).h + 1)
  /-- (c) on `[t_s, T + Δ)` at every cut of `y` while honest, and at the end of the interval
  when `y` is honest at `T + Δ`. -/
  caches : ∀ k, (y ∈ H (tr.time k) ∧ tr.IsCall y k ∧ sp.ts s ≤ tr.time k ∧
      tr.time k < T + sp.Δ) ∨ (y ∈ H (T + sp.Δ) ∧ tr.FirstCutFrom k (T + sp.Δ)) →
    Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.F B ∧
      Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.J B
  /-- (c) after the cut at `T + Δ` that accepts `y`'s own proposal, `y` honest at `T + Δ`. -/
  caches_own : ∀ k X, y ∈ H (T + sp.Δ) → tr.ProposesAt y k X → tr.time k = T + sp.Δ →
    tr.AcceptAt y k X →
    Compatible (tr.HonestBlocksAt H) (tr.post k).fg.F B ∧
      Compatible (tr.HonestBlocksAt H) (tr.post k).fg.J B

/-- **The conclusion of C1.1** for the slot `s' ∈ (s, m]` under growing faults. -/
structure PersistAt (B : SA.Blk sp.n (List (FG.Att sp.n))) (s s' : Nat) : Prop where
  /-- (iii) G1.10 at the scope of C1.1 with `T = t_{s'} + Δ`, at every node. -/
  cut : ∀ y, CutScopeAt tr H y B s (sp.ts s' + sp.Δ)
  /-- (i) viability at every vote of slot `s'` by a node honest at its vote. -/
  viable : ∀ y i ℓ e, y ∈ H (tr.time i) → SA.CastAt tr.projAC y i ℓ e → e.msg.slot = s' →
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s') ∨
      Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot
  /-- (ii) every vote of slot `s'` by a node honest at its vote extends `B`. -/
  extends_ : ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e → e.msg.slot = s' →
    SA.VoteExtends (tr.HonestBlocksAt H) e.msg B

/-- **C1.1 under growing faults, honest fast confirmations persist.** -/
def HonestFastConfirmationsPersist : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (ΔF : Time) (x : Fin sp.n) (i₀ s m : Nat)
    (B : SA.Blk sp.n (List (FG.Att sp.n))) (CV : Set (Vote sp.n)) (proposer : Nat → Fin sp.n),
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr →
    PersistPremises tr H dg ΔF x i₀ s m B CV →
    ∀ s', s < s' → s' ≤ m → PersistAt tr H B s s'

/-- **C1.1's corollary under growing faults, recent source, next vote.** The writer is honest at
its `ac_to_fg` call. -/
def RecentSourceNextVote : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (ΔF : Time) (x : Fin sp.n) (i₀ i j m : Nat)
    (ℓ : ACLabel (goldilocksNode sp ro)) (B : SA.Blk sp.n (List (FG.Att sp.n)))
    (CV : Set (Vote sp.n)) (proposer : Nat → Fin sp.n),
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr →
    PersistPremises tr H dg ΔF x i₀ j (m + 1) B CV →
    x ∈ H (tr.time i) → SA.ToFGAt tr.projAC x i ℓ B → sp.slot (tr.time i) = m → j ≤ m →
    m ≤ j + 2 →
    ∀ y k e, y ∈ H (tr.time k) → SA.VoteAt tr.projAC y k e → e.msg.slot = m + 1 →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg B

end Consensus.Goldilocks.Compose.Growing

end
