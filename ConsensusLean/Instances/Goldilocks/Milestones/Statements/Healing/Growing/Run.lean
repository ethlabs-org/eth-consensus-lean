module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.AC
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Persist

@[expose] public section

/-! # Goldilocks milestone Healing under growing faults: the run-level statements (statements)

HR.1–HR.4, H.2 (run), H.3 and H.4 (`Statements/Healing/Run`) for a time-indexed honest set `H`
(antitone), over `Growing.GoldilocksRun` (and, for HR.2, `Growing.FGLocalRun`):

* **who is honest where**: a node at a cut is honest at the time of the cut; a signer at its
  signing cut; "the state at `t`" and "after all events at `t`" are read over the validators
  honest at `t`, and "every honest node by `t`" is every node honest at `t`; so `H_z` is read
  over the validators honest at `c_z`, the reset `a_z` over signers honest at their signing, and a
  signer compromised by `c_z` is charged as faulty, not bounded by `H_z`;
* **counts are charged where they are consumed**: `Healthy(g)` is `HealthyRunAt` (`3 f_t ≤ n − 1`
  at every `t`), and the (K1) clause of HR.1 (c) holds for the namers at every consumption
  horizon `d ≥ a_z − Δ` (`Store.Growing.namers`);
* **the effective phase** is read over a cohort: HR.2's monotonicity and count over the
  validators honest at a horizon `d`, at cuts up to `d`; HR.3's steps, settledness and the
  settled phase of H.3's bridge for every cohort horizon `d`: a phase change is read at both cuts
  over the cohort `H d` of one fixed `d` at or after the later state's time, and each other
  honesty read at time `t` is at `max d t` (the fixed cohort `H d` up to `d`); so the steps of the
  reset count do not cross a change of cohort (a compromise, which removes a node's blocks from
  the honest reads, is not a phase change), and nothing moves `d` with an endpoint;
* **the reset bound** of HR.3 (c), and with it H.3's and H.4's, is indexed by the lag `L` of the
  counting cohort `H D` behind `H_z` at `c_z` (`LagWithin`): the window is
  `c_z + 6(Δ + A_HS) + LΔ`; at a constant honest set `L = 0`;
* **the proposer** of a healed or ready slot `s` is honest through `t_s + hold`
  (`Regimes.Growing.hold`).

The vocabulary that binds no honest set (`FirstCutAfter`, `cutZ`, the constants, the phase case,
`HoldsEvidence`, `T_heal`) is the static one; the phase predicates `FrontierAt`, `JustifiedAt`,
`ContestAt`, `PhaseAt` and `PhaseChanged` are the static ones applied to `H t`. At
`H := fun _ => H₀` each statement implies its static counterpart.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar blockSupport)
open Regimes.Growing (hold)

section Vocabulary

variable {P : Params} {A : NodeAC P} (tr : RunTrace A) (H : Time → Set (Fin P.n))

/-- `H_z` under growing faults: the greatest `Σ.h_max` of the validators honest at `c_z`, after
all events at `c_z`. -/
noncomputable def HZ (g : Time) : Nat :=
  sSup {h | ∃ y, y ∈ H (cutZ P g) ∧ ∃ j, FirstCutAfter tr j (cutZ P g) ∧
    (tr.state y j).fg.hmax = h}

/-- **The reset `a_z`** under growing faults: the first time at which a validator honest at its
signing signs an attestation whose height pair has height `H_z + 1`. -/
def IsReset (g a : Time) : Prop :=
  (∃ y k att, y ∈ H (tr.time k) ∧ tr.SignAt y k att ∧ att.h = HZ tr H g + 1 ∧ tr.time k = a) ∧
    ∀ y k att, y ∈ H (tr.time k) → tr.SignAt y k att → att.h = HZ tr H g + 1 → a ≤ tr.time k

/-- The entries of heights `≥ H_z + 1` of the chains accepted by nodes honest at their cuts. -/
def HighEntries (Hz : Nat) : Set (NodeBlock P A.Payload) :=
  {E | ∃ y i, y ∈ H (tr.time i) ∧ E ∈ (tr.state y i).fg.tree ∧ ∃ B ∈ (tr.state y i).fg.tree,
    Hz + 1 ≤ ((tr.state y i).fg.σ B.root).h ∧ ((tr.state y i).fg.σ B.root).Th = E.root}

/-- **`Catch(κ)` over a run** under growing faults: a block accepted at a time `< ḡ` by a node
honest at its acceptance is accepted before `ḡ + κ` by every validator `y` honest at `ḡ + κ` whose
`Σ.F` at `ḡ + κ` it extends. -/
def CatchRun (g κ : Time) : Prop :=
  ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → tr.time i < gbar g →
    ∀ y j, y ∈ H (gbar g + κ) → tr.FirstCutFrom j (gbar g + κ) →
      Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B → ∃ k < j, tr.AcceptAt y k B

/-- No restart after `t` of a node honest at its restart. -/
def NoRestartAfter (t : Time) : Prop :=
  ∀ y k, y ∈ H (tr.time k) → tr.RestartAt y k → tr.time k ≤ t

/-- **Settled at `w`** under growing faults, for the cohort of horizon `d`: over the validators
honest at `max d w` (the cohort `H d` when `w ≤ d`). -/
structure SettledAt (d g κ w : Time) : Prop where
  /-- `w ≥ max(ḡ + κ, ḡ + 8Δ)`. -/
  late : max (gbar g + κ) (gbar g + 8 * P.Δ) ≤ w
  /-- Every validator honest at `max d w` is joined at `w`. -/
  joined : ∀ y, y ∈ H (max d w) → tr.JoinedAt y w
  /-- At `w`, every validator honest at `max d w` holds the evidence of the effective phase read
  over the validators honest at `max d w`. -/
  evidence : ∀ j, tr.FirstCutFrom j w → ∀ m c, PhaseAt tr.projFG (H (max d w)) j m c →
    ∀ y, y ∈ H (max d w) → HoldsEvidence (tr.projFG.store y j) m c
  /-- The pre-GST acceptance catch-up is complete at `w`. -/
  catchUp : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → tr.time i < gbar g →
    ∀ y j, y ∈ H (max d w) → tr.FirstCutFrom j w →
      Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B → ∃ k < j, tr.AcceptAt y k B

end Vocabulary

section Goldilocks

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- **A ready proposal** under growing faults: the proposer `p` of slot `s`, honest through
`t_s + hold` and joined at `t_s`, makes its proposal `B` of slot `s` at cut `k`, and every
slot-`(s−1)` support reference of `B` is held before the vote deadline `t_s + Δ` by every validator
honest at `t_s + Δ`. -/
def ReadyProposal (proposer : Nat → Fin sp.n)
    (p : Fin sp.n) (k s : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  p ∈ H (sp.ts s + hold sp) ∧ p = proposer s ∧ tr.JoinedAt p (sp.ts s) ∧ tr.ProposesAt p k B ∧
    B.slot = s ∧
    ∀ x ∈ blockSupport B, x.slot + 1 = s → ∀ y j, y ∈ H (sp.ts s + sp.Δ) →
      tr.FirstCutFrom j (sp.ts s + sp.Δ) →
      ∃ R ∈ (tr.state y j).fg.tree, R.root = x.head ∧ R.slot + 1 ≤ s

/-- **`Prop⁺(G_p)`** under growing faults. -/
def PropPlus (proposer : Nat → Fin sp.n) (g Gp : Time) : Prop :=
  ∀ τ, gbar g ≤ τ → ∃ (s : Nat) (k : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))),
    1 ≤ s ∧ τ ≤ sp.ts s ∧ sp.ts s ≤ τ + Gp ∧
    ReadyProposal tr H proposer (proposer s) k s B

/-- **The HS shared premises** under growing faults, with `Healthy(g)` as `HealthyRunAt`. -/
structure HSShared (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g ΔF : Time) : Prop where
  /-- `NoColl` on the blocks of the run. -/
  noColl : Compose.NoCollRun dg tr
  /-- Genesis's root is its digest. -/
  genesisRoot : (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg
  /-- `Healthy(g)` under growing faults. -/
  healthy : tr.HealthyRunAt H ΔF g
  /-- No restart after `ḡ` of a node honest at its restart. -/
  noRestart : NoRestartAfter tr H (gbar g)
  /-- `δ_t ≥ ⌈(6Δ + Δ_F)/(4Δ)⌉`. -/
  timeoutDelay : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.δt : Time)

/-- **A high origin** `(B, j)` under growing faults: written by `x` honest at its write. -/
def HighOrigin (g : Time) (x : Fin sp.n) (i j : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) :
    Prop :=
  x ∈ H (tr.time i) ∧ tr.JoinedAt x (tr.time i) ∧
    (∃ CV, Compose.StoredFastLockAt tr x i j B CV) ∧
    HZ tr H g + 1 ≤ ((tr.state x i).fg.σ B.root).h

/-- **(R1)–(R4) of HR.4** under growing faults, for the reset `a`. -/
structure RetentionAt (g a : Time) : Prop where
  /-- (R1) The blocks of any two high origins are comparable. -/
  comparable : ∀ x i j B x' i' j' B', HighOrigin tr H g x i j B → HighOrigin tr H g x' i' j' B' →
    Compatible (tr.HonestBlocksAt H) B B'
  /-- (R1) Every attestation signed at or after `a`, by a signer honest at its signing, whose
  height pair has height `h ≥ H_z + 1` names the entry at `h` of a high origin's chain. -/
  fgAtts : ∀ y k att, y ∈ H (tr.time k) → tr.SignAt y k att → a ≤ tr.time k →
    HZ tr H g + 1 ≤ att.h →
    ∃ x i j B, HighOrigin tr H g x i j B ∧ ∃ E ∈ (tr.state x i).fg.tree,
      (tr.state x i).fg.Anc E B ∧ E.root = att.T ∧ ((tr.state x i).fg.σ E.root).h = att.h ∧
      ((tr.state x i).fg.σ E.root).Th = E.root
  /-- (R2) After every cut at a time `≥ a` of a node honest at the cut, its `Σ.F`, and its `Σ.J`
  when `Σ.h_j ≥ H_z + 1`, are compatible with every high origin written at that cut or earlier. -/
  caches : ∀ y k, y ∈ H (tr.time k) → tr.IsCall y k → a ≤ tr.time k →
    ∀ x i j B, HighOrigin tr H g x i j B → i ≤ k →
      Compatible (tr.HonestBlocksAt H) (tr.post k).fg.F B ∧
      (HZ tr H g + 1 ≤ (tr.post k).fg.hj → Compatible (tr.HonestBlocksAt H) (tr.post k).fg.J B)
  /-- (R3) For a high origin `(B, j)`, every vote of a slot `> j` by a node honest at its vote
  extends `B`, with `B` in the viable voter block tree or at or below `fc_root`. -/
  votes : ∀ x i j B, HighOrigin tr H g x i j B → ∀ y k ℓ e, y ∈ H (tr.time k) →
    SA.CastAt tr.projAC y k ℓ e → j < e.msg.slot →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg B ∧
      (B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
        Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot)
  /-- (R4) For every `h ≥ H_z + 1`, the nonempty target, timeout and lock entries at `h` of the
  client records of nodes at cuts at which they are honest name at most one block. -/
  records : ∀ h, HZ tr H g + 1 ≤ h →
    {r | ∃ y i, y ∈ H (tr.time i) ∧ ((tr.state y i).record.target h = some r ∨
      r ∈ (tr.state y i).record.timeout h ∨ (tr.state y i).record.lock h = some r)}.Subsingleton

end Goldilocks

/-- **HR.1 under growing faults, cut and reset.** The attestations signed by `c_z` that `H_z`
bounds are those of validators honest at `c_z`; the attestation on a high chain is by a validator
honest at the holding cut; the (K1) clause holds for the namers charged at every horizon
`d ≥ a_z − Δ`. -/
def CutAndReset : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF : Time),
    sp.committeeSize = sp.n →
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → tr.HealthyRunAt H ΔF g →
    Compose.NoCollRun dg tr →
    cutZ sp.toParams g ≤ gbar g + 12 * sp.Δ ∧
    (∀ y k att, y ∈ H (cutZ sp.toParams g) → tr.SignAt y k att →
      tr.time k ≤ cutZ sp.toParams g → att.h ≤ HZ tr H g) ∧
    (∀ x i ℓ C, x ∈ H (tr.time i) → SA.ToFGAt tr.projAC x i ℓ C →
      cutZ sp.toParams g ≤ tr.time i →
      ∃ l ∈ SA.liveLocks sp (tr.state x i).ac.locks ℓ.frame (tr.time i),
        l.fast = true ∧ l.block = C.root ∧
        ∃ i' < i, ∃ B CV, SA.FastLockAt tr.projAC x i' l.slot B CV ∧ gbar g < tr.time i' ∧
          Anc (tr.HonestBlocksAt H) C B) ∧
    (∀ y i, y ∈ H (tr.time i) → ∀ X ∈ (tr.state y i).fg.tree,
      HZ tr H g + 2 ≤ ((tr.state y i).fg.σ X.root).h →
      ∃ Y, (tr.state y i).fg.Anc Y X ∧ ∃ att ∈ Y.fgPayload, att.val ∈ H (tr.time i) ∧
        att.h = HZ tr H g + 1) ∧
    ∀ a, IsReset tr H g a →
      cutZ sp.toParams g < a ∧
      (∀ y k att, y ∈ H (tr.time k) → tr.SignAt y k att → HZ tr H g + 1 ≤ att.h →
        a ≤ tr.time k) ∧
      (∀ y k src signed, y ∈ H (tr.time k) → tr.CallAt y k (.fg (.attest src signed)) →
        tr.time k = a → (tr.state y k).fg.hmax ≤ HZ tr H g + 1) ∧
      (∀ y k att, y ∈ H (tr.time k) → tr.SignAt y k att → tr.time k = a →
        att.h ≤ HZ tr H g + 1) ∧
      (∀ d, a - sp.Δ ≤ d → ∀ 𝓔 ⊆ HighEntries tr H (HZ tr H g), ∀ E ∈ 𝓔,
        (Store.Growing.namers sp.toParams (Payload sp.n) H tr.projFG (a - sp.Δ) d E).ncard <
          sp.toParams.fg.q) ∧
      ∀ T, a ≤ T → ∀ y k att, y ∈ H (tr.time k) → tr.SignAt y k att → tr.time k = a →
        a - sp.Δ < tr.time k ∧ tr.time k ≤ T

/-- **HR.2 under growing faults, phase count** (an FG store node over FG traces). (a) is read at
the two nodes' cuts, with `f < 2q − n` at the later one. (b) and (c) read the phase over the
validators honest at a horizon `d`, at cuts up to `d`, with `f_d < 2q − n`. -/
def PhaseCount (P : Params) (ACP : Type) : Prop :=
  ∀ (acp₀ : ACP) (H : Time → Set (Fin P.n)) (U : Set (NodeBlock P ACP)) (tr : FGTrace P ACP),
    Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr →
    (∀ y z i j, y ∈ H (tr.time i) → z ∈ H (tr.time j) →
      (H (max (tr.time i) (tr.time j)))ᶜ.ncard < 2 * P.fg.q - P.n →
      ∀ B ∈ (tr.store y i).tree, ∀ B' ∈ (tr.store z j).tree,
        ((tr.store y i).σ B.root).hj = ((tr.store z j).σ B'.root).hj →
          ((tr.store y i).σ B.root).J = ((tr.store z j).σ B'.root).J) ∧
    ∀ d, (H d)ᶜ.ncard < 2 * P.fg.q - P.n →
      (∀ m i j c c', i ≤ j → tr.time j ≤ d → PhaseAt tr (H d) i m c →
        PhaseAt tr (H d) j m c' → c.rank ≤ c'.rank ∧ ∀ J, c.topJ = some J → c'.topJ = some J) ∧
      ∀ m, {i | tr.time (i + 1) ≤ d ∧ ∃ c c', PhaseAt tr (H d) i m c ∧
        PhaseAt tr (H d) (i + 1) m c' ∧ c ≠ c'}.encard ≤ 2

/-- **HR.2 under growing faults** at every parameter and AC payload type. -/
def PhaseCountAll : Prop := ∀ (P : Params) (ACP : Type), PhaseCount P ACP

/-- The reset window of HR.3 at lag `L`: `c_z + 6(Δ + A_HS) + LΔ`. -/
def resetWindow (sp : SAParams) (g ΔF Gp : Time) (L : Nat) : Time :=
  cutZ sp.toParams g + 6 * (sp.Δ + A_HS sp ΔF Gp) + (L : Time) * sp.Δ

/-- The lag of the cohort of horizon `D` at `c_z` is at most `L`: `H_z` is at most `L` above the
greatest `Σ.h_max` at `c_z` of the validators honest at `D`. -/
def LagWithin {P : Params} {A : NodeAC P} (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (g D : Time) (L : Nat) : Prop :=
  HZ tr H g ≤ HZ tr (fun _ => H D) g + L

/-- **HR.3 under growing faults, reset existence.** (a) and (b) hold for every fixed cohort
horizon `d` at or after the step's later time (`u + Δ`, resp. `w + A_HS`): the phase change from
the state after all events at `u` (or at a settled `w`) to the state at `u + Δ` (after all events
at `w + A_HS`), and the settledness, are read over the cohort `H d`, both cuts at the same `d`
(every event either state covers is at a time `≤ d`). So the steps of the reset count are read
over one cohort, with no change of `d` between them.

(c) is **indexed by the lag** `L` of the counting cohort: the reset exists and is at most
`c_z + 6(Δ + A_HS) + LΔ` for every horizon `D` at or after that window whose cohort lags `H_z` by
at most `L` at `c_z` (`LagWithin`). The count runs over the cohort `H D`, whose frontier at `c_z`
can be below `H_z` when the holders of the top are compromised by `D`; the relay of the top block
stays owed after their compromise, so the cohort catches up within `Δ` in total, not per unit of
lag; the lag is at most one. `L` is fixed by the run through `LagWithin`; the strongest instance is
the actual lag, and at a constant honest set it is `0`. -/
def ResetExistence : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time),
    sp.committeeSize = sp.n →
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF →
    CatchRun tr H g (2 * sp.Δ) → PropPlus tr H proposer g Gp →
    (gbar g + 8 * sp.Δ < cutZ sp.toParams g ∧
      ∀ d u, cutZ sp.toParams g ≤ u → u + sp.Δ ≤ d → ∀ j j', FirstCutAfter tr j u →
        tr.FirstCutFrom j' (u + sp.Δ) →
        PhaseChanged tr.projFG (H d) j j' ∨ SettledAt tr H d g (2 * sp.Δ) (u + sp.Δ)) ∧
    (∀ d w, w + A_HS sp ΔF Gp ≤ d → SettledAt tr H d g (2 * sp.Δ) w → ∀ j j',
      tr.FirstCutFrom j w → FirstCutAfter tr j' (w + A_HS sp ΔF Gp) →
      PhaseChanged tr.projFG (H d) j j') ∧
    (∀ L D, resetWindow sp g ΔF Gp L ≤ D → LagWithin tr H g D L →
      ∃ a, IsReset tr H g a ∧ a ≤ resetWindow sp g ΔF Gp L) ∧
    cutZ sp.toParams g + 6 * (sp.Δ + A_HS sp ΔF Gp) ≤
      gbar g + 24 * sp.Δ + 12 * C_HS sp ΔF Gp ∧
    gbar g + 24 * sp.Δ + 12 * C_HS sp ΔF Gp =
      gbar g + (96 * (sp.k : Time) + 612 + 48 * (sp.toParams.δt : Time)) * sp.Δ + 12 * ΔF +
        36 * Gp ∧
    C_HS sp ΔF Gp = (8 * (sp.k : Time) + 49 + 4 * (sp.toParams.δt : Time)) * sp.Δ + ΔF + 3 * Gp

/-- **HR.4 under growing faults, height-scoped retention**, for population-sized committees. -/
def HeightScopedRetention : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF : Time),
    sp.committeeSize = sp.n →
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → tr.HealthyRunAt H ΔF g →
    Compose.NoCollRun dg tr → ∀ a, IsReset tr H g a → RetentionAt tr H g a

section Top

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- The votes of slot `p` of the nodes honest at their votes are all `P`. -/
def Unanimous (p : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∀ x j e, x ∈ H (tr.time j) → SA.VoteAt tr.projAC x j e → e.msg.slot = p → e.msg.head = P.root

/-- `P` is the honest proposal of slot `p`, by a proposer honest through `t_p + hold`. -/
def HonestProposalRun (proposer : Nat → Fin sp.n)
    (p : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  proposer p ∈ H (sp.ts p + hold sp) ∧ SA.HonestProposal tr.projAC (proposer p) p P

/-- `P` is in the AC confirmed tip at every call at a time `≥ t₁` of a node honest at the call. -/
def IncludedFrom (t₁ : Time) (P : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∀ y j ℓ, y ∈ H (tr.time j) → tr.projAC.CallAt y j ℓ → t₁ ≤ tr.time j →
    (tr.time j = t₁ → ∃ k ≤ j, ∃ ℓ', tr.projAC.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧
      tr.time k = tr.time j) →
    Anc (tr.HonestBlocksAt H) P (SA.acConfirmed sp (tr.post j).ac ℓ.frame (tr.time j))

/-- The proposal of slot `p` and the slot-`p` votes of the cohort of horizon `d` lie in one
settled effective phase, read at each cut `i` over the validators honest at `max d (time i)`. -/
def InSettledPhase (d g : Time) (p : Nat) : Prop :=
  ∃ w m c, SettledAt tr H d g (2 * sp.Δ) w ∧ w ≤ sp.ts p ∧
    ∀ i, w ≤ tr.time i →
      (tr.time i ≤ sp.ts p ∨ ∃ y i' e, i ≤ i' ∧ y ∈ H (max d (tr.time i')) ∧
        SA.VoteAt tr.projAC y i' e ∧ e.msg.slot = p) →
      PhaseAt tr.projFG (H (max d (tr.time i))) i m c

/-- **The bridge of H.3 (c)** under growing faults: `Geo(P)` for the cohort of every horizon
`d` (its voters honest at `max d` of their vote times) whose settled phase holds the slot. -/
def BridgeAt (proposer : Nat → Fin sp.n) (g a Tb : Time) : Prop :=
  SA.Growing.Inv proposer tr.projAC H (tr.HonestBlocksAt H) (a + Tb) ∧
    ∀ d (p : Nat) P, HonestProposalRun tr H proposer p P →
      a + Tb + 2 * SA.Θ sp + 8 * sp.Δ ≤ sp.ts p →
      InSettledPhase tr H d g p → SA.Growing.Geo proposer tr.projAC (fun t => H (max d t)) p P

end Top

/-- **H.2 (run) under growing faults, AC inclusion in runs**, for population-sized committees. -/
def RunInclusion : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF : Time),
    sp.committeeSize = sp.n →
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → Compose.NoCollRun dg tr →
    (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg →
    tr.HealthyRunAt H ΔF g → CatchRun tr H g (2 * sp.Δ) →
    (SA.Growing.Driven proposer tr.projAC H ∧
      SA.Growing.HealthyAC tr.projAC H (tr.HonestBlocksAt H) g ∧
      SA.Growing.CatchAC tr.projAC H (tr.HonestBlocksAt H) g (2 * sp.Δ)) ∧
    ∀ t₀, gbar g ≤ t₀ → SA.Growing.Inv proposer tr.projAC H (tr.HonestBlocksAt H) t₀ →
      ∀ (p : Nat) P, HonestProposalRun tr H proposer p P →
        t₀ + 2 * SA.Θ sp + 8 * sp.Δ ≤ sp.ts p →
        (SA.Growing.Geo proposer tr.projAC H p P → Unanimous tr H p P) ∧
        (Unanimous tr H p P → IncludedFrom tr H (sp.ts p + 6 * sp.Δ) P)

/-- **H.3 under growing faults, FG non-interference after the reset**, at the lag `L` of a
counting cohort (as HR.3 (c)): the reset is at most `ḡ + 24Δ + 12C_HS + LΔ`. -/
def NonInterference : Prop :=
  ∃ Tb : Nat → Time → Time → Nat → Nat → Time, (∀ n Δ ΔF k δt, 0 ≤ Tb n Δ ΔF k δt) ∧
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time),
    sp.committeeSize = sp.n →
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF →
    CatchRun tr H g (2 * sp.Δ) → PropPlus tr H proposer g Gp →
    ∀ L D, resetWindow sp g ΔF Gp L ≤ D → LagWithin tr H g D L →
    ∃ a, IsReset tr H g a ∧
      a ≤ gbar g + 24 * sp.Δ + 12 * C_HS sp ΔF Gp + (L : Time) * sp.Δ ∧
      RetentionAt tr H g a ∧ BridgeAt tr H proposer g a (Tb sp.n sp.Δ ΔF sp.k sp.toParams.δt)

/-- **H.4 under growing faults, healing of the available chain, assembled**, at the lag `L` of a
counting cohort (as HR.3 (c)): the healed slot is from `T_heal + LΔ` on. -/
def AvailableHealing : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time),
    sp.committeeSize = sp.n →
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF →
    CatchRun tr H g (2 * sp.Δ) → PropPlus tr H proposer g Gp →
    ∀ L D, resetWindow sp g ΔF Gp L ≤ D → LagWithin tr H g D L →
    ∀ a Tb, IsReset tr H g a → 0 ≤ Tb → BridgeAt tr H proposer g a Tb →
      ∀ (p : Nat) P, HonestProposalRun tr H proposer p P →
        T_heal sp g ΔF Gp Tb + (L : Time) * sp.Δ ≤ sp.ts p →
        Unanimous tr H p P → IncludedFrom tr H (sp.ts p + 6 * sp.Δ) P

end Consensus.Goldilocks.Healing.Growing

end
