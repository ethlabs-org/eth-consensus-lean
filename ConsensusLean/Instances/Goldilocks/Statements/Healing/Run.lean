module
public import Mathlib.Order.Lattice.Nat
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Persist
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.AC

@[expose] public section

/-! # Goldilocks milestone Healing: the run-level healing statements (statements)

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` §"Healing: top-level
statements" (HR.1–HR.4, H.2 (run), H.3, H.4) and §"Healing: phase service" (the HS shared
premises, the settled predicate and the constants `D`, `C`, `A`), over the Goldilocks run
(`Spec/Run`, `GoldilocksRun`) and, for HR.2, over FG traces (`FGLocalRun`).

**Vocabulary.**

* `cutZ` is `c_z = t_{slot(ḡ)+3}`; `HZ` is `H_z`, the greatest `Σ.h_max` of the honest nodes
  after all events at `c_z` (`FirstCutAfter`: the state before the first cut after `c_z`);
  `IsReset` says that `a` is the reset `a_z`, the first time at which an honest validator signs an
  attestation whose height pair has height `H_z + 1` (honest signing is at public times, in ticks,
  so this is the first public time of one); `HighEntries` are the entries of heights `≥ H_z + 1`
  of the honest accepted chains.
* `CatchRun` is `Catch(κ)`, `PropPlus` is `Prop⁺(G_p)` (an honest joined proposal at a slot start
  in every window `[τ, τ + G_p]` from `ḡ`, whose slot-`(s−1)` support references are held by every
  honest node before the vote deadline `t_s + Δ`: the ready-proposer premise), `NoRestartAfter`
  is "no honest restart after `t`"; `HSShared` bundles the HS shared premises (with the
  parameter bound `δ_t ≥ ⌈(6Δ + Δ_F)/(4Δ)⌉`); `D_HS`, `C_HS`, `A_HS` are the HS constants.
* **The effective phase** (HS shared premises, HR.2) is read over an FG trace at a cut: the
  frontier `m` is the greatest honest `Σ.h_max` (`FrontierAt`); the case (`PhaseCase`) is a gap
  (no justification at `m − 1` on an honest accepted chain), a top `J` (a justification of `J` at
  `m − 1` and no contest) or a contest (`J` justified at `m − 1` and an honest accepted block of
  state height `m` that does not extend `J`). It reads the honest accepted blocks of all nodes, not
  one node's `Σ.F`, so an advance of an honest `Σ.F` changes no phase by definition (HR.2's last
  sentence). Over a run it is read on the FG projection (`projFG`), cut by cut.
  `SettledAt` is the HS settled predicate, `PhaseChanged` a change of the frontier or the case.

**HR.2 is stated over FG traces** (`FGLocalRun`), not over runs: the claims make it an FG store
node over the FG component trace, the phase reads only the honest `Σ` (which an FG trace carries,
with the honest records, unforgeability and serialized clients in `FGLocalRun`), and so it sits
with G1.4 (`Store.FinalizedSafety`), whose premise `f < 2q − n` it shares. A run reaches it through
C0.5 (c) (`Compose.FGProjection`), and HR.3 reads the same phase on `tr.projFG`.

"The state at `t`" is the state before the first cut at a time `≥ t` (`FirstCutFrom`); "after
all events at `t`" is the state before the first cut at a time `> t` (`FirstCutAfter`).

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar blockSupport)

section Vocabulary

/-- Cut `j` is the first cut after the time `t`: every earlier cut is at a time `≤ t` and cut `j`
is later, so the state before `j` is the state after all events at `t`. -/
def FirstCutAfter {N S L : Type} (tr : Trace N S L) (j : Nat) (t : Time) : Prop :=
  (∀ k < j, tr.time k ≤ t) ∧ t < tr.time j

/-- `c_z = t_{slot(ḡ)+3}`, the cut of the reset (claims HR.1). -/
def cutZ (P : Params) (g : Time) : Time := P.slotTime (P.slotOf (gbar g) + 3)

variable {P : Params} {A : NodeAC P} (tr : RunTrace A) (H : Set (Fin P.n))

/-- `H_z` (claims HR.1): the greatest `Σ.h_max` of the honest nodes after all events at `c_z`.
(When no cut follows `c_z`, which `Healthy(g)` excludes, the set is empty and this is `0`.) -/
noncomputable def HZ (g : Time) : Nat :=
  sSup {h | ∃ y ∈ H, ∃ j, FirstCutAfter tr j (cutZ P g) ∧ (tr.state y j).fg.hmax = h}

/-- **The reset `a_z`** (claims HR.1 (c)): `a` is the first time at which an honest validator
signs an attestation whose height pair has height `H_z + 1`. -/
def IsReset (g a : Time) : Prop :=
  (∃ y ∈ H, ∃ k att, tr.SignAt y k att ∧ att.h = HZ tr H g + 1 ∧ tr.time k = a) ∧
    ∀ y ∈ H, ∀ k att, tr.SignAt y k att → att.h = HZ tr H g + 1 → a ≤ tr.time k

/-- The entries of heights `≥ H_z + 1` of the honest accepted chains: the blocks `E` of an honest
tree that are the entry `T_h` of an accepted state of height `h ≥ H_z + 1`. -/
def HighEntries (Hz : Nat) : Set (NodeBlock P A.Payload) :=
  {E | ∃ y ∈ H, ∃ i, E ∈ (tr.state y i).fg.tree ∧ ∃ B ∈ (tr.state y i).fg.tree,
    Hz + 1 ≤ ((tr.state y i).fg.σ B.root).h ∧ ((tr.state y i).fg.σ B.root).Th = E.root}

/-- **`Catch(κ)` over a run** (accepted-old-block catch-up): every block an honest node accepts
at a time `< ḡ` is accepted before `ḡ + κ` by every honest `y` whose `Σ.F` at `ḡ + κ` it extends
(its needed ancestry with it: the FG accepts a block only on a held parent). -/
def CatchRun (g κ : Time) : Prop :=
  ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → tr.time i < gbar g →
    ∀ y ∈ H, ∀ j, tr.FirstCutFrom j (gbar g + κ) →
      Anc (tr.HonestBlocks H) (tr.state y j).fg.F B → ∃ k < j, tr.AcceptAt y k B

/-- No honest restart after `t`. -/
def NoRestartAfter (t : Time) : Prop := ∀ y ∈ H, ∀ k, tr.RestartAt y k → tr.time k ≤ t

end Vocabulary

section Constants

variable (sp : SAParams)

/-- The HS constant `D = (8k + 48)Δ + 2G`. -/
def D_HS (G : Time) : Time := (8 * (sp.k : Time) + 48) * sp.Δ + 2 * G

/-- The HS constant `C = D + 4Δδ_t + Δ_F + G + Δ`. -/
def C_HS (ΔF G : Time) : Time := D_HS sp G + 4 * sp.Δ * (sp.toParams.δt : Time) + ΔF + G + sp.Δ

/-- The HS constant `A = 2C + Δ` (`Producer(A)`). -/
def A_HS (ΔF G : Time) : Time := 2 * C_HS sp ΔF G + sp.Δ

end Constants

section Phase

variable {P : Params} {ACP : Type} (tr : FGTrace P ACP) (H : Set (Fin P.n))

/-- The frontier at cut `i` is `m`: the greatest `Σ.h_max` of the honest nodes. -/
def FrontierAt (i m : Nat) : Prop :=
  (∃ y ∈ H, (tr.store y i).hmax = m) ∧ ∀ y ∈ H, (tr.store y i).hmax ≤ m

/-- At cut `i`, `J` is justified at height `h` on an honest accepted chain: an honest node holds
`J` and a block whose state has the justification `(h, J)`. -/
def JustifiedAt (i h : Nat) (J : NodeBlock P ACP) : Prop :=
  ∃ y ∈ H, J ∈ (tr.store y i).tree ∧ ∃ B ∈ (tr.store y i).tree,
    ((tr.store y i).σ B.root).hj = h ∧ ((tr.store y i).σ B.root).J = J.root

/-- At cut `i`, a contest against `J` at `m`: an honest node holds a block of state height `m`
that does not extend `J`. -/
def ContestAt (i m : Nat) (J : NodeBlock P ACP) : Prop :=
  ∃ y ∈ H, ∃ B ∈ (tr.store y i).tree, ((tr.store y i).σ B.root).h = m ∧ ¬ (tr.store y i).Anc J B

/-- The case of an effective phase (claims HR.2 (b), HS shared premises). -/
inductive PhaseCase (β : Type) where
  /-- No justification at `m − 1`. -/
  | gap
  /-- A unique top justification `J` at `m − 1` and no contest. -/
  | top (J : β)
  /-- A contest: a block of height `m` that does not extend the top justification `J`. -/
  | contest (J : β)

/-- The order of the cases: gap, then top `J`, then contest. -/
def PhaseCase.rank {β : Type} : PhaseCase β → Nat
  | .gap => 0
  | .top _ => 1
  | .contest _ => 2

/-- The top justification of a case, if any. -/
def PhaseCase.topJ {β : Type} : PhaseCase β → Option β
  | .gap => none
  | .top J => some J
  | .contest J => some J

/-- **The effective phase at cut `i`** is `(m, c)`: the frontier is `m` and the case is `c`, read
on the honest accepted blocks (not on one node's `Σ.F` or local allowedness). -/
def PhaseAt (i m : Nat) : PhaseCase (NodeBlock P ACP) → Prop
  | .gap => FrontierAt tr H i m ∧ ∀ J, ¬ JustifiedAt tr H i (m - 1) J
  | .top J => FrontierAt tr H i m ∧ JustifiedAt tr H i (m - 1) J ∧ ¬ ContestAt tr H i m J
  | .contest J => FrontierAt tr H i m ∧ JustifiedAt tr H i (m - 1) J ∧ ContestAt tr H i m J

/-- The effective phase changes from cut `i` to cut `j`: the frontier has risen or the case has
changed (no phase at `i` is the phase at `j`). -/
def PhaseChanged (i j : Nat) : Prop :=
  ∀ m c, PhaseAt tr H i m c → ¬ PhaseAt tr H j m c

/-- The FG state `st` holds the defining evidence of the effective phase `(m, c)`: a block of
state height `m`; for a top `J` or a contest, `J` and a block whose state justifies `J` at
`m − 1`; for a contest, also a block of state height `m` that does not extend `J`. -/
def HoldsEvidence (st : Store P ACP) (m : Nat) : PhaseCase (NodeBlock P ACP) → Prop
  | .gap => ∃ B ∈ st.tree, (st.σ B.root).h = m
  | .top J => (∃ B ∈ st.tree, (st.σ B.root).h = m) ∧ J ∈ st.tree ∧
      ∃ B ∈ st.tree, (st.σ B.root).hj = m - 1 ∧ (st.σ B.root).J = J.root
  | .contest J => (∃ B ∈ st.tree, (st.σ B.root).h = m) ∧ J ∈ st.tree ∧
      (∃ B ∈ st.tree, (st.σ B.root).hj = m - 1 ∧ (st.σ B.root).J = J.root) ∧
      ∃ B ∈ st.tree, (st.σ B.root).h = m ∧ ¬ st.Anc J B

end Phase

section Run

variable {P : Params} {A : NodeAC P} (tr : RunTrace A) (H : Set (Fin P.n))

/-- **Settled at `w`** (HS shared premises): `w ≥ max(ḡ + κ, ḡ + 8Δ)`; at `w` every honest
validator is joined and holds the defining frontier, top-`J` and contest evidence of the current
effective phase; and the pre-GST acceptance catch-up is complete (every block an honest node
accepted before `ḡ` is held by every honest node whose `Σ.F` at `w` it extends). -/
structure SettledAt (g κ w : Time) : Prop where
  /-- `w ≥ max(ḡ + κ, ḡ + 8Δ)`. -/
  late : max (gbar g + κ) (gbar g + 8 * P.Δ) ≤ w
  /-- Every honest validator is joined at `w`. -/
  joined : ∀ y ∈ H, tr.JoinedAt y w
  /-- At `w`, every honest node holds the evidence of the effective phase. -/
  evidence : ∀ j, tr.FirstCutFrom j w → ∀ m c, PhaseAt tr.projFG H j m c →
    ∀ y ∈ H, HoldsEvidence (tr.projFG.store y j) m c
  /-- The pre-GST acceptance catch-up is complete at `w`. -/
  catchUp : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → tr.time i < gbar g →
    ∀ y ∈ H, ∀ j, tr.FirstCutFrom j w → Anc (tr.HonestBlocks H) (tr.state y j).fg.F B →
      ∃ k < j, tr.AcceptAt y k B

end Run

section Goldilocks

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- **A ready proposal**: the honest proposer `p` of slot `s`, joined at `t_s`, makes its
proposal `B` of slot `s` at cut `k`, and every slot-`(s−1)` support reference of `B` is a block of
slot `≤ s − 1` that every honest node holds before the vote deadline `t_s + Δ` (so `B` is ready
at every honest voter: `vote_ready`'s condition). -/
def ReadyProposal (proposer : Nat → Fin sp.n)
    (p : Fin sp.n) (k s : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  p ∈ H ∧ p = proposer s ∧ tr.JoinedAt p (sp.ts s) ∧ tr.ProposesAt p k B ∧
    B.slot = s ∧
    ∀ x ∈ blockSupport B, x.slot + 1 = s → ∀ y ∈ H, ∀ j, tr.FirstCutFrom j (sp.ts s + sp.Δ) →
      ∃ R ∈ (tr.state y j).fg.tree, R.root = x.head ∧ R.slot + 1 ≤ s

/-- **`Prop⁺(G_p)`** (the HS ready-proposer premise with `G = G_p`): for every trigger `τ ≥ ḡ`
there is a slot `s ≥ 1` with `τ ≤ t_s ≤ τ + G_p` with a ready proposal (`ReadyProposal`). -/
def PropPlus (proposer : Nat → Fin sp.n) (g Gp : Time) : Prop :=
  ∀ τ, gbar g ≤ τ → ∃ (s : Nat) (k : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))),
    1 ≤ s ∧ τ ≤ sp.ts s ∧ sp.ts s ≤ τ + Gp ∧
    ReadyProposal tr H proposer (proposer s) k s B

/-- **The HS shared premises** (claims §"Healing: phase service") other than the two regime
premises (`CatchRun`, `PropPlus`, taken separately): `NoColl` with a genesis whose root is its
digest (the model's reading of `NoColl` for genesis, as C0.3), `Healthy(g)` (with `GST(g)`'s
strict delivery, acceptance relay and row convention), no honest restart after `ḡ`, and the
protocol's parameter bound `δ_t ≥ 𝓕 = ⌈(6Δ + Δ_F)/(4Δ)⌉` (from `δ_t ≥ x + 𝓕 + k_F`,
`x, k_F ≥ 0`; `k ≥ 2` and `Δ_F ≥ Δ` are carried by `SAParams` and `SyncOn`). Unforgeable
signatures, persistent honest client records and finite event prefixes are laws of the run
(`GoldilocksRun`). -/
structure HSShared (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g ΔF : Time) : Prop where
  /-- `NoColl` on the blocks of the run. -/
  noColl : Compose.NoCollRun dg tr
  /-- Genesis's root is its digest (as C0.3 and A1.7 take it): otherwise an honest proposal
  whose digest is the genesis root is refused by every FG, and the healing statements that need
  honest proposals to be accepted (HR.3's reset, C1.2, H.3, H.4) fail (consensus-lean#73). -/
  genesisRoot : (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg
  /-- `Healthy(g)`. -/
  healthy : tr.HealthyRun H ΔF g
  /-- No honest restart after `ḡ`. -/
  noRestart : NoRestartAfter tr H (gbar g)
  /-- `δ_t ≥ ⌈(6Δ + Δ_F)/(4Δ)⌉`. -/
  timeoutDelay : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.δt : Time)

/-- **A high origin** `(B, j)` (claims HR.4), written at cut `i` of `x`: a write of a fast lock
(fast test or optimistic confirmation) of label `j` at the honest node `x`, joined at the write,
whose stored block `B` has state height `≥ H_z + 1`. The stored block is the selected block `D`
after the move back of `add_locks` (`viable_ancestor` in the frame of the writing call; claims
C1.1, "stored block after the move back"), not the raw selected block. -/
def HighOrigin (g : Time) (x : Fin sp.n) (i j : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) :
    Prop :=
  x ∈ H ∧ tr.JoinedAt x (tr.time i) ∧
    (∃ CV, Compose.StoredFastLockAt tr x i j B CV) ∧
    HZ tr H g + 1 ≤ ((tr.state x i).fg.σ B.root).h

/-- **(R1)–(R4) of HR.4** for the reset `a`. -/
structure RetentionAt (g a : Time) : Prop where
  /-- (R1) The blocks of any two high origins are comparable. -/
  comparable : ∀ x i j B x' i' j' B', HighOrigin tr H g x i j B → HighOrigin tr H g x' i' j' B' →
    Compatible (tr.HonestBlocks H) B B'
  /-- (R1) Every honest attestation signed at or after `a` whose height pair has height
  `h ≥ H_z + 1` names the entry at `h` of a high origin's chain. -/
  rows : ∀ y ∈ H, ∀ k att, tr.SignAt y k att → a ≤ tr.time k → HZ tr H g + 1 ≤ att.h →
    ∃ x i j B, HighOrigin tr H g x i j B ∧ ∃ E ∈ (tr.state x i).fg.tree,
      (tr.state x i).fg.Anc E B ∧ E.root = att.T ∧ ((tr.state x i).fg.σ E.root).h = att.h ∧
      ((tr.state x i).fg.σ E.root).Th = E.root
  /-- (R2) After every cut of an honest node at a time `≥ a` (from its tick at `a` on), its
  `Σ.F`, and its `Σ.J` when `Σ.h_j ≥ H_z + 1`, are compatible with every high origin written at
  that cut or earlier. -/
  caches : ∀ y ∈ H, ∀ k, tr.IsCall y k → a ≤ tr.time k →
    ∀ x i j B, HighOrigin tr H g x i j B → i ≤ k →
      Compatible (tr.HonestBlocks H) (tr.post k).fg.F B ∧
      (HZ tr H g + 1 ≤ (tr.post k).fg.hj → Compatible (tr.HonestBlocks H) (tr.post k).fg.J B)
  /-- (R3) For a high origin `(B, j)`, every honest vote of a slot `> j` extends `B`, and at that
  vote `B` is in the voter's viable voter block tree or `B ⪯ fc_root` (block order inside the
  honest blocks, not ancestry inside the frame tree, which `B` leaves once `Σ.F` passes it). -/
  votes : ∀ x i j B, HighOrigin tr H g x i j B → ∀ y ∈ H, ∀ k ℓ e,
    SA.CastAt tr.projAC y k ℓ e → j < e.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B ∧
      (B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
        Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot)
  /-- (R4) For every `h ≥ H_z + 1`, the nonempty target, timeout and lock entries at `h` of the
  honest client records name at most one block. -/
  records : ∀ h, HZ tr H g + 1 ≤ h →
    {r | ∃ y ∈ H, ∃ i, (tr.state y i).record.target h = some r ∨
      r ∈ (tr.state y i).record.timeout h ∨ (tr.state y i).record.lock h = some r}.Subsingleton

end Goldilocks

/-- **HR.1, cut and reset.** In a Goldilocks run (unforgeable signatures, durable records) under
`Healthy(g)` and `NoColl`, with `c_z = t_{slot(ḡ)+3}` (`≤ ḡ + 12Δ`) and `H_z`:
(a) every honest attestation signed at or before `c_z` has a height pair of height `≤ H_z`; from
`c_z` on, every block `C` that `ac_to_fg` returns at an honest `x` is the block of a live fast
lock of `x` whose label `j` has a fast-lock write at `x` after `ḡ` on a descendant of `C` (A1.5
with `τ = ḡ`; the lock's block is the written block moved back to an ancestor);
(b) the chain of an honest accepted block of state height `≥ H_z + 2` carries an honest
attestation whose height pair has height `H_z + 1`;
(c) if `a` is the reset `a_z`: `a > c_z` and no honest height pair of height `≥ H_z + 1` is
signed before `a`; at the FG update (`fg_attest`) of each honest tick at `a` the accepted
frontier is `≤ H_z + 1`, so every honest row signed at `a` has height `≤ H_z + 1`; for every set
`𝓔` of entries of heights `≥ H_z + 1` the first clause of (K1_𝓔) of G1.10 holds with
`T₀ = a − Δ`; and for every `T ≥ a` every honest row signed at `a` lies in `(T₀, T]`. -/
def CutAndReset : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF : Time),
    GoldilocksRun proposer dg H tr → tr.HealthyRun H ΔF g → Compose.NoCollRun dg tr →
    cutZ sp.toParams g ≤ gbar g + 12 * sp.Δ ∧
    (∀ y ∈ H, ∀ k att, tr.SignAt y k att → tr.time k ≤ cutZ sp.toParams g →
      att.h ≤ HZ tr H g) ∧
    (∀ x ∈ H, ∀ i ℓ C, SA.ToFGAt tr.projAC x i ℓ C → cutZ sp.toParams g ≤ tr.time i →
      ∃ l ∈ SA.liveLocks sp (tr.state x i).ac.locks ℓ.frame (tr.time i),
        l.fast = true ∧ l.block = C.root ∧
        ∃ i' < i, ∃ B CV, SA.FastLockAt tr.projAC x i' l.slot B CV ∧ gbar g < tr.time i' ∧
          Anc (tr.HonestBlocks H) C B) ∧
    (∀ y ∈ H, ∀ i, ∀ X ∈ (tr.state y i).fg.tree, HZ tr H g + 2 ≤ ((tr.state y i).fg.σ X.root).h →
      ∃ Y, (tr.state y i).fg.Anc Y X ∧ ∃ att ∈ Y.fgPayload, att.val ∈ H ∧ att.h = HZ tr H g + 1) ∧
    ∀ a, IsReset tr H g a →
      cutZ sp.toParams g < a ∧
      (∀ y ∈ H, ∀ k att, tr.SignAt y k att → HZ tr H g + 1 ≤ att.h → a ≤ tr.time k) ∧
      (∀ y ∈ H, ∀ k src signed, tr.CallAt y k (.fg (.attest src signed)) → tr.time k = a →
        (tr.state y k).fg.hmax ≤ HZ tr H g + 1) ∧
      (∀ y ∈ H, ∀ k att, tr.SignAt y k att → tr.time k = a → att.h ≤ HZ tr H g + 1) ∧
      (∀ 𝓔 ⊆ HighEntries tr H (HZ tr H g), ∀ E ∈ 𝓔,
        (Store.namers sp.toParams (Payload sp.n) H tr.projFG (a - sp.Δ) E).ncard <
          sp.toParams.fg.q) ∧
      ∀ T, a ≤ T → ∀ y ∈ H, ∀ k att, tr.SignAt y k att → tr.time k = a →
        a - sp.Δ < tr.time k ∧ tr.time k ≤ T

/-- **HR.2, phase count** (an FG store node over FG traces). In an FG trace (unforgeable honest
signatures, durable and serialized honest clients, `NoColl` as the coherence of `U`:
`FGLocalRun`) with `f < 2q − n`:
(a) on the honest accepted chains at most one entry is justified at each height: two honest
accepted states with the same `h_j` have the same `J`;
(b) while the frontier `m` stays fixed, the effective phase moves only forward through gap, top
`J`, contest (a contest ends only when `m` rises), with one `J`; so there are at most two effective
phase changes (between consecutive cuts) per value of `m`. (An advance of an honest `Σ.F` below
`m` changes no phase: the phase does not read `Σ.F`.) -/
def PhaseCount (P : Params) (ACP : Type) : Prop :=
  ∀ (acp₀ : ACP) (H : Set (Fin P.n)) (U : Set (NodeBlock P ACP)) (tr : FGTrace P ACP),
    FGLocalRun acp₀ H U tr → Hᶜ.ncard < 2 * P.fg.q - P.n →
    (∀ y ∈ H, ∀ z ∈ H, ∀ i j, ∀ B ∈ (tr.store y i).tree, ∀ B' ∈ (tr.store z j).tree,
      ((tr.store y i).σ B.root).hj = ((tr.store z j).σ B'.root).hj →
        ((tr.store y i).σ B.root).J = ((tr.store z j).σ B'.root).J) ∧
    (∀ m i j c c', i ≤ j → PhaseAt tr H i m c → PhaseAt tr H j m c' →
      c.rank ≤ c'.rank ∧ ∀ J, c.topJ = some J → c'.topJ = some J) ∧
    ∀ m, {i | ∃ c c', PhaseAt tr H i m c ∧ PhaseAt tr H (i + 1) m c' ∧ c ≠ c'}.encard ≤ 2

/-- **HR.3, reset existence.** In a Goldilocks run under the HS shared premises (`HSShared`,
with `Healthy(g)`), `Catch(2Δ)` and `Prop⁺(G_p)` (so `κ = 2Δ`, `G = G_p`):
(a) `c_z > ḡ + 8Δ`, and for every `u ≥ c_z` HS.0 applies at `u` (`Settle(Δ)`): the effective phase
after all events at `u` has changed by `u + Δ` (at the state at `u + Δ`), or the run is settled
at `u + Δ`;
(b) from every settled `w`, by `w + A_HS` (after all events at `w + A_HS`) the effective phase has
changed or the frontier has risen (`Producer(A)`; advances of `Σ.F` below the frontier do not
count);
(c) the reset `a_z` exists, and
`a_z ≤ c_z + 6(Δ + A_HS) ≤ ḡ + 24Δ + 12C_HS = ḡ + (96k + 612 + 48δ_t)Δ + 12Δ_F + 36G_p`, with
`C_HS = (8k + 49 + 4δ_t)Δ + Δ_F + 3G_p`. -/
def ResetExistence : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time),
    GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF → CatchRun tr H g (2 * sp.Δ) →
    PropPlus tr H proposer g Gp →
    (gbar g + 8 * sp.Δ < cutZ sp.toParams g ∧
      ∀ u, cutZ sp.toParams g ≤ u → ∀ j j', FirstCutAfter tr j u →
        tr.FirstCutFrom j' (u + sp.Δ) →
        PhaseChanged tr.projFG H j j' ∨ SettledAt tr H g (2 * sp.Δ) (u + sp.Δ)) ∧
    (∀ w, SettledAt tr H g (2 * sp.Δ) w → ∀ j j', tr.FirstCutFrom j w →
      FirstCutAfter tr j' (w + A_HS sp ΔF Gp) → PhaseChanged tr.projFG H j j') ∧
    (∃ a, IsReset tr H g a) ∧
    (∀ a, IsReset tr H g a → a ≤ cutZ sp.toParams g + 6 * (sp.Δ + A_HS sp ΔF Gp)) ∧
    cutZ sp.toParams g + 6 * (sp.Δ + A_HS sp ΔF Gp) ≤
      gbar g + 24 * sp.Δ + 12 * C_HS sp ΔF Gp ∧
    gbar g + 24 * sp.Δ + 12 * C_HS sp ΔF Gp =
      gbar g + (96 * (sp.k : Time) + 612 + 48 * (sp.toParams.δt : Time)) * sp.Δ + 12 * ΔF +
        36 * Gp ∧
    C_HS sp ΔF Gp = (8 * (sp.k : Time) + 49 + 4 * (sp.toParams.δt : Time)) * sp.Δ + ΔF + 3 * Gp

/-- **HR.4, height-scoped retention.** In a Goldilocks run (unforgeable signatures, durable and
serialized honest clients) under `Healthy(g)` and `NoColl`, if the reset `a_z` exists, (R1)–(R4)
hold for it (`RetentionAt`). -/
def HeightScopedRetention : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF : Time),
    GoldilocksRun proposer dg H tr → tr.HealthyRun H ΔF g → Compose.NoCollRun dg tr →
    ∀ a, IsReset tr H g a → RetentionAt tr H g a

section Top

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- The honest votes of slot `p` (over the AC projection) are all `P`. -/
def Unanimous (p : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = p → e.msg.head = P.root

/-- `P` is the honest proposal of slot `p` (its proposer is honest) over the AC projection. -/
def HonestProposalRun (proposer : Nat → Fin sp.n)
    (p : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  proposer p ∈ H ∧ SA.HonestProposal tr.projAC (proposer p) p P

/-- `P` is in the AC confirmed tip of every honest node at every time `t ≥ t₁` (at every call at
a time `≥ t₁`, after it; at `t₁` itself from the node's tick there on). -/
def IncludedFrom (t₁ : Time) (P : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∀ y ∈ H, ∀ j ℓ, tr.projAC.CallAt y j ℓ → t₁ ≤ tr.time j →
    (tr.time j = t₁ → ∃ k ≤ j, ∃ ℓ', tr.projAC.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧
      tr.time k = tr.time j) →
    Anc (tr.HonestBlocks H) P (SA.acConfirmed sp (tr.post j).ac ℓ.frame (tr.time j))

/-- The proposal of slot `p` and the honest slot-`p` votes lie in one effective phase in which
every honest node is settled (HS definitions, with `κ = 2Δ`): the run is settled at some
`w ≤ t_p`, and the effective phase is the same at every cut from `w` through `t_p` and through
the last honest vote of slot `p`. -/
def InSettledPhase (g : Time) (p : Nat) : Prop :=
  ∃ w m c, SettledAt tr H g (2 * sp.Δ) w ∧ w ≤ sp.ts p ∧
    ∀ i, w ≤ tr.time i →
      (tr.time i ≤ sp.ts p ∨ ∃ y ∈ H, ∃ i' e, i ≤ i' ∧ SA.VoteAt tr.projAC y i' e ∧
        e.msg.slot = p) →
      PhaseAt tr.projFG H i m c

/-- **The bridge of H.3 (c)** with offset `T_b` from the reset `a`: the AC projection satisfies
`Inv(a + T_b)`, and `Geo(P)` holds for every honest proposal `P` of a slot
`p ≥ s_AC(a + T_b)` (`t_p ≥ a + T_b + 2Θ + 8Δ`) whose proposal and votes lie in one settled
effective phase. -/
def BridgeAt (proposer : Nat → Fin sp.n) (g a Tb : Time) : Prop :=
  SA.Inv proposer tr.projAC H (tr.HonestBlocks H) (a + Tb) ∧
    ∀ (p : Nat) P, HonestProposalRun tr H proposer p P →
      a + Tb + 2 * SA.Θ sp + 8 * sp.Δ ≤ sp.ts p →
      InSettledPhase tr H g p → SA.Geo proposer tr.projAC H p P

end Top

/-- **H.2 (run), AC inclusion in runs.** In a Goldilocks run (unforgeable signatures) under
`NoColl`, a genesis whose root is its digest (so that the honest proposal of driven-trace clause (b)
is accepted, as C0.3; consensus-lean#73), `Healthy(g)` and `Catch(2Δ)`, the AC projection is a
driven AC trace (clause (a) from the FG's acceptance tests, C0.5 (b) `Compose.ACSeesAcceptedBlocks`;
clause (b) from C0.4) with `Healthy(g)` and `Catch(2Δ)` read on it, inside the honest blocks of the
run; and H.2 holds for the run: for `t₀ ≥ ḡ` with `Inv(t₀)` on the projection and an honest proposal
`P` of slot `p` with `t_p ≥ t₀ + 2Θ + 8Δ`, (i) `Geo(P)` gives a unanimous slot `p`, and (ii) a
unanimous slot `p` puts `P` in every honest node's AC confirmed tip from `t_p + 6Δ` on. -/
def RunInclusion : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF : Time),
    GoldilocksRun proposer dg H tr → Compose.NoCollRun dg tr →
    (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg →
    tr.HealthyRun H ΔF g → CatchRun tr H g (2 * sp.Δ) →
    (SA.Driven proposer tr.projAC H ∧ SA.HealthyAC tr.projAC H (tr.HonestBlocks H) g ∧
      SA.CatchAC tr.projAC H (tr.HonestBlocks H) g (2 * sp.Δ)) ∧
    ∀ t₀, gbar g ≤ t₀ → SA.Inv proposer tr.projAC H (tr.HonestBlocks H) t₀ →
      ∀ (p : Nat) P, HonestProposalRun tr H proposer p P →
        t₀ + 2 * SA.Θ sp + 8 * sp.Δ ≤ sp.ts p →
        (SA.Geo proposer tr.projAC H p P → Unanimous tr H p P) ∧
        (Unanimous tr H p P → IncludedFrom tr H (sp.ts p + 6 * sp.Δ) P)

/-- **H.3, FG non-interference after the reset.** Under the premises of HR.3 and HR.4
(`HSShared`, `Catch(2Δ)`, `Prop⁺(G_p)`): (a) the reset `a_z` exists, and
`a_z ≤ ḡ + 24Δ + 12C_HS`; (b) from `a_z` on, (R1)–(R4) hold; (c) the bridge: there is
`T_b ≥ 0`, a function of the parameters only (`n`, `Δ`, `Δ_F`, `k`, `δ_t`; `K_W = 2` is fixed,
`k_F` and `x` are not model parameters; not of `G_p` or the proposer schedule), such that the AC
projection satisfies `Inv(a_z + T_b)` and `Geo(P)` holds for every honest proposal `P` of a slot
`p ≥ s_AC(a_z + T_b)` whose proposal and slot-`p` votes lie in one settled effective phase
(`BridgeAt`). (Candidate, not claimed: `T_b = 8Δ`.) -/
def NonInterference : Prop :=
  ∃ Tb : Nat → Time → Time → Nat → Nat → Time, (∀ n Δ ΔF k δt, 0 ≤ Tb n Δ ΔF k δt) ∧
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time),
    GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF → CatchRun tr H g (2 * sp.Δ) →
    PropPlus tr H proposer g Gp →
    ∃ a, IsReset tr H g a ∧ a ≤ gbar g + 24 * sp.Δ + 12 * C_HS sp ΔF Gp ∧
      RetentionAt tr H g a ∧ BridgeAt tr H proposer g a (Tb sp.n sp.Δ ΔF sp.k sp.toParams.δt)

/-- `T_heal = ḡ + 24Δ + 12C_HS + T_b + 2Θ + 8Δ` (claims H.4). -/
def T_heal (sp : SAParams) (g ΔF Gp Tb : Time) : Time :=
  gbar g + 24 * sp.Δ + 12 * C_HS sp ΔF Gp + Tb + 2 * SA.Θ sp + 8 * sp.Δ

/-- **H.4, healing of the available chain, assembled** (a conditional assembly). Under the
premises of H.3, for the reset `a_z` and a `T_b ≥ 0` for which H.3 (c)'s bridge holds
(`BridgeAt`), with `T_heal = ḡ + (104k + 628 + 48δ_t)Δ + 12Δ_F + 36G_p + T_b`:
(i) an honest proposal `P` with `t_p ≥ T_heal` whose honest slot-`p` votes are all `P` is in every
honest confirmed tip at every `t ≥ t_p + 6Δ`;
(ii) under `(U_B)` (from `T_heal` on, every window `[t, t + B]` has a unanimous honest proposal),
for every `t ≥ T_heal` some honest proposal released in `[t, t + B]` is in every honest confirmed
tip from `t + B + 6Δ` on;
(iii) under `(U_all)` (every honest proposal with `t_p ≥ T_heal` is unanimous), every honest
proposal with `t_p ≥ T_heal` is in every honest confirmed tip from `t_p + 6Δ` on. -/
def AvailableHealing : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time),
    GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF → CatchRun tr H g (2 * sp.Δ) →
    PropPlus tr H proposer g Gp →
    ∀ a Tb, IsReset tr H g a → 0 ≤ Tb → BridgeAt tr H proposer g a Tb →
      T_heal sp g ΔF Gp Tb =
        gbar g + (104 * (sp.k : Time) + 628 + 48 * (sp.toParams.δt : Time)) * sp.Δ + 12 * ΔF +
          36 * Gp + Tb ∧
      (∀ (p : Nat) P, HonestProposalRun tr H proposer p P → T_heal sp g ΔF Gp Tb ≤ sp.ts p →
        Unanimous tr H p P → IncludedFrom tr H (sp.ts p + 6 * sp.Δ) P) ∧
      (∀ B : Time,
        (∀ t, T_heal sp g ΔF Gp Tb ≤ t →
          ∃ (p : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))), t ≤ sp.ts p ∧ sp.ts p ≤ t + B ∧
            HonestProposalRun tr H proposer p P ∧ Unanimous tr H p P) →
        ∀ t, T_heal sp g ΔF Gp Tb ≤ t →
          ∃ (p : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))), t ≤ sp.ts p ∧ sp.ts p ≤ t + B ∧
            HonestProposalRun tr H proposer p P ∧ IncludedFrom tr H (t + B + 6 * sp.Δ) P) ∧
      ((∀ (p : Nat) P, HonestProposalRun tr H proposer p P → T_heal sp g ΔF Gp Tb ≤ sp.ts p →
          Unanimous tr H p P) →
        ∀ (p : Nat) P, HonestProposalRun tr H proposer p P → T_heal sp g ΔF Gp Tb ≤ sp.ts p →
          IncludedFrom tr H (sp.ts p + 6 * sp.Δ) P)

/-- The run-level statements of milestone Healing (HR.1–HR.4, H.2 (run), H.3, H.4). -/
structure HealingRunStatements : Prop where
  cutAndReset : CutAndReset
  phaseCount : ∀ (P : Params) (ACP : Type), PhaseCount P ACP
  resetExistence : ResetExistence
  heightScopedRetention : HeightScopedRetention
  runInclusion : RunInclusion
  nonInterference : NonInterference
  availableHealing : AvailableHealing

end Consensus.Goldilocks.Healing

end
