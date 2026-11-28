module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Persist

@[expose] public section

/-! # Goldilocks milestone Healing under growing faults: the run-level statements (statements)

The run-level healing vocabulary and G1.9 (b) (`CacheAcceptance`, the growing form of HR.5) for a
time-indexed honest set `H` (antitone), over `Growing.GoldilocksRun`: the definitions the growing
healing proofs read. HR.1–HR.4, H.2 (run), H.3 and H.4 are not
stated under growing faults. The definitions read the honest set as follows:

* **who is honest where**: a node at a cut is honest at the time of the cut; a signer at its
  signing cut; "the state at `t`" and "after all events at `t`" are read over the validators
  honest at `t`, and "every honest node by `t`" is every node honest at `t`; so `H_z` is read
  over the validators honest at `c_z`, the reset `a_z` over signers honest at their signing, and a
  signer compromised by `c_z` is charged as faulty, not bounded by `H_z`;
* **counts are charged where they are consumed**: `Healthy(g)` is `HealthyRunAt` (`3 f_t ≤ n − 1`
  at every `t`), and the (K1) clause of HR.1 (c) holds for the namers at every consumption
  horizon `d ≥ a_z − Δ` (`Store.Growing.namers`);
* **the proposer** of a healed slot `s` is honest through `t_s + hold`
  (`Regimes.Growing.hold`).

The vocabulary that binds no honest set (`FirstCutAfter`, `cutZ`, the constants, `T_heal`) is the
static one.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload gbar declaredSupportVotes)
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

variable {sp : ACParams}
  (tr : GoldilocksTrace sp) (H : Time → Set (Fin sp.n))

/-- **A high origin** `(B, j)` under growing faults: written by `x` honest at its write and at
`c_z`. -/
def HighOrigin (g : Time) (x : Fin sp.n) (i j : Nat) (B : AC.Blk sp.n (List (FG.Att sp.n))) :
    Prop :=
  x ∈ H (max (cutZ sp.toParams g) (tr.time i)) ∧ tr.JoinedAt x (tr.time i) ∧
    (∃ CV, Compose.StoredFastLockAt tr x i j B CV) ∧
    HZ tr H g + 1 ≤ ((tr.state x i).fg.σ B.root).h

end Goldilocks

/-- **G1.9 (b) under growing faults, cache acceptance.** In a Goldilocks run under growing
faults, from any starts, under `NoColl`: at every acceptance of a block `B` by a node honest at
that cut, with fewer than a third of the validators compromised by the cut (`3 f ≤ n − 1`, charged
where it is consumed), `F* = σ[B].F` satisfies `F* ⪯ Σ.F` after that `fg_on_block` call. (The
claims' reset and height bound are not needed, as in the static HR.5.) -/
def CacheAcceptance : Prop :=
  ∀ (sp : ACParams)
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp) (ini : Fin sp.n → (goldilocksNode sp).State),
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini →
    Compose.NoCollRun dg tr →
      ∀ y k B, y ∈ H (tr.time k) → 3 * (H (tr.time k))ᶜ.ncard ≤ sp.n - 1 →
        tr.AcceptAt y k B →
        ∀ Fs ∈ (tr.post k).fg.tree, Fs.root = ((tr.post k).fg.σ B.root).F →
          (tr.post k).fg.Anc Fs (tr.post k).fg.F

section Top

variable {sp : ACParams}
  (tr : GoldilocksTrace sp) (H : Time → Set (Fin sp.n))

/-- `P` is the honest proposal of slot `p`, by a proposer honest through `t_p + hold`. -/
def HonestProposalRun (proposer : Nat → Fin sp.n)
    (p : Nat) (P : AC.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  proposer p ∈ H (sp.ts p + hold sp) ∧ AC.HonestProposal tr.projAC (proposer p) p P

end Top

end Consensus.Goldilocks.Healing.Growing

end
