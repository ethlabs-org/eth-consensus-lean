module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Persist

@[expose] public section

/-! # Goldilocks milestone Healing under growing faults: the run-level statements (statements)

The run-level healing vocabulary and HR.2 (`Statements/Healing/Run`) for a time-indexed honest
set `H` (antitone), over `Growing.GoldilocksRun` (and, for HR.2, `Growing.FGLocalRun`): the
definitions the growing healing proofs read. HR.1, HR.3, HR.4, H.2 (run), H.3 and H.4 are not
stated under growing faults. The definitions read the honest set as follows:

* **who is honest where**: a node at a cut is honest at the time of the cut; a signer at its
  signing cut; "the state at `t`" and "after all events at `t`" are read over the validators
  honest at `t`, and "every honest node by `t`" is every node honest at `t`; so `H_z` is read
  over the validators honest at `c_z`, the reset `a_z` over signers honest at their signing, and a
  signer compromised by `c_z` is charged as faulty, not bounded by `H_z`;
* **counts are charged where they are consumed**: `Healthy(g)` is `HealthyRunAt` (`3 f_t ≤ n − 1`
  at every `t`), and the (K1) clause of HR.1 (c) holds for the namers at every consumption
  horizon `d ≥ a_z − Δ` (`Store.Growing.namers`);
* **the effective phase** is read over a cohort: HR.2's monotonicity and count over the
  validators honest at a horizon `d`, at cuts up to `d`; a phase change is read at both cuts over
  the cohort `H d` of one fixed `d`, so the steps of the count do not cross a change of cohort (a
  compromise, which removes a node's blocks from the honest reads, is not a phase change);
* **the proposer** of a healed or ready slot `s` is honest through `t_s + hold`
  (`Regimes.Growing.hold`).

The vocabulary that binds no honest set (`FirstCutAfter`, `cutZ`, the constants, the phase case,
`T_heal`) is the static one; the phase predicates `FrontierAt`, `JustifiedAt`,
`ContestAt`, `PhaseAt` and `PhaseChanged` are the static ones applied to `H t`.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar declaredSupportVotes)
open Regimes.Growing (hold)

section Vocabulary

variable {P : Params} {A : NodeAC P} (tr : RunTrace A) (H : Time → Set (Fin P.n))

/-- `H_z` under growing faults: the greatest `Σ.h_max` of the validators honest at `c_z`, after
all events at `c_z`. -/
noncomputable def HZ (g : Time) : Nat :=
  sSup {h | ∃ y, y ∈ H (cutZ P g) ∧ ∃ j, FirstCutAfter tr j (cutZ P g) ∧
    (tr.state y j).fg.hmax = h}

/-- **The reset `a_z`** under growing faults: the first time at which a validator honest at its
signing and at `c_z` signs an attestation whose height pair has height `H_z + 1`. A signer
compromised by `c_z` is charged as faulty: `H_z` does not bound it. -/
def IsReset (g a : Time) : Prop :=
  (∃ y k att, y ∈ H (max (cutZ P g) (tr.time k)) ∧ tr.SignAt y k att ∧
      att.h = HZ tr H g + 1 ∧ tr.time k = a) ∧
    ∀ y k att, y ∈ H (max (cutZ P g) (tr.time k)) → tr.SignAt y k att →
      att.h = HZ tr H g + 1 → a ≤ tr.time k

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

end Vocabulary

section Goldilocks

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- **A ready proposal** under growing faults: the proposer `p` of slot `s`, honest through
`t_s + hold` and joined at `t_s`, makes its proposal `B` of slot `s` at cut `k`, and every
slot-`(s−1)` support reference of `B` is held before the vote deadline `t_s + Δ` by every validator
honest at `t_s + Δ`. -/
def ReadyProposal (proposer : Nat → Fin sp.n)
    (p : Fin sp.n) (k s : Nat) (B : AC.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  p ∈ H (sp.ts s + hold sp) ∧ p = proposer s ∧ tr.JoinedAt p (sp.ts s) ∧ tr.ProposesAt p k B ∧
    B.slot = s ∧
    ∀ x ∈ declaredSupportVotes B, x.slot + 1 = s → ∀ y j, y ∈ H (sp.ts s + sp.Δ) →
      tr.FirstCutFrom j (sp.ts s + sp.Δ) →
      ∃ R ∈ (tr.state y j).fg.tree, R.root = x.head ∧ R.slot + 1 ≤ s

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

/-- **A high origin** `(B, j)` under growing faults: written by `x` honest at its write and at
`c_z`. -/
def HighOrigin (g : Time) (x : Fin sp.n) (i j : Nat) (B : AC.Blk sp.n (List (FG.Att sp.n))) :
    Prop :=
  x ∈ H (max (cutZ sp.toParams g) (tr.time i)) ∧ tr.JoinedAt x (tr.time i) ∧
    (∃ CV, Compose.StoredFastLockAt tr x i j B CV) ∧
    HZ tr H g + 1 ≤ ((tr.state x i).fg.σ B.root).h

end Goldilocks

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

section Top

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- `P` is the honest proposal of slot `p`, by a proposer honest through `t_p + hold`. -/
def HonestProposalRun (proposer : Nat → Fin sp.n)
    (p : Nat) (P : AC.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  proposer p ∈ H (sp.ts p + hold sp) ∧ AC.HonestProposal tr.projAC (proposer p) p P

end Top

end Consensus.Goldilocks.Healing.Growing

end
