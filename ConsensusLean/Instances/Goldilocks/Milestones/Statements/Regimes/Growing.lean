module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Always
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Premises

@[expose] public section

/-! # Goldilocks milestone Regimes under growing faults (statements)

The rows of `Statements/Regimes/{Sleepy,Always}` for a time-indexed honest set `H` (antitone), over
`Growing.GoldilocksRun`:

* **Readers** are honest at the later of the read time and the time of the cut whose state they
  read (`y ∈ H (max t (tr.time i))`), or at their own cut; a node's reads after its compromise
  are not claimed. Ancestry and compatibility are read inside the blocks held while honest
  (`HonestBlocksAt`).
* **Sleepy** is `SleepyRunAt` with the look-ahead `ahead sp = 5Δ`: the count at each slot point is
  charged with the faults of `5Δ` later, the time of the slot's last count (the confirmation
  update at `t_s + 6Δ`, from the participation point `t_s + Δ`).
* **Proposers** of the liveness rows are ready at their slot time and still honest `hold sp = Δ`
  later, when the slot's votes have been cast (`ReadyProposalAt`, `ProposerRecurrence`). A
  proposer compromised before that can split its slot with a second proposal.
* **Finalized safety** charges `f < 2q − n` at the later of the two reads; **non-framing** covers
  a validator honest at the later of its two signings; **final accountability** has no fault
  bound, with each reader honest at its own cut.

The margins (`τ + 6Δ`, `D = (4k + 6)Δ`) are those of the static rows. At `H := fun _ => H₀` each
statement implies its static counterpart (`Lemmas/Growing/Statements/Regimes`).

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Regimes.Growing

open SA (SAParams ReplayOrder Payload)

/-- The sleepy look-ahead of the Goldilocks contract (`ahead = 5`) at `Δp = Δe`. -/
def ahead (sp : SAParams) : Time := 5 * sp.Δ

/-- The proposer hold of the Goldilocks contract (`hold = 1`) at `Δp = Δe`. -/
def hold (sp : SAParams) : Time := sp.Δ

section Defs

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- `y` is ready at `t` with catch-up `c`: honest at `t` and awake throughout
`[max(0, t − c − 1), t]`. -/
def ReadyAt (c : Time) (y : Fin sp.n) (t : Time) : Prop :=
  y ∈ H t ∧ ∀ τ, max 0 (t - c - 1) ≤ τ → τ ≤ t → tr.awake y τ

/-- `P` is an honest proposal released at `τ` by a proposer ready at `τ` (catch-up `c`) and still
honest at `τ + h`. -/
def ReadyProposalAt (c τ h : Time) (P : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∃ p kP, ReadyAt tr H c p τ ∧ p ∈ H (τ + h) ∧ tr.ProposesAt p kP P ∧ tr.time kP = τ

/-- One proposer ready at its slot start and still honest `h` later in every window of `k`
consecutive slots whose first slot starts after `a` and whose last slot starts by `b`. -/
def ProposerRecurrence (proposer : Nat → Fin sp.n) (c : Time) (k : Nat) (h a b : Time) : Prop :=
  ∀ s₀ : Nat, a < sp.ts s₀ → sp.ts (s₀ + k - 1 : Nat) ≤ b →
    ∃ s, s₀ ≤ s ∧ s < s₀ + k ∧ ReadyAt tr H c (proposer s) (sp.ts s) ∧
      proposer s ∈ H (sp.ts s + h)

end Defs

/-- **R.1 under growing faults.** Under `Sleepy` with look-ahead `ahead`: any two confirmed reads
of nodes honest at their reads are compatible; and a node's reads at two read points between its
events, in cut order, where it is ready, only extend. -/
def SleepySafe : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n) (ΔF : Time),
    sp.committeeSize = sp.n →
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → Compose.NoCollRun dg tr →
    tr.SleepyRunAt H ΔF (ahead sp) →
    (∀ y z i j t t', y ∈ H (max t (tr.time i)) → z ∈ H (max t' (tr.time j)) →
      Compatible (tr.HonestBlocksAt H) (readAfter tr y i t) (readAfter tr z j t')) ∧
    ∀ y i j t t', ReadPoint tr i t → ReadPoint tr j t' → Boundary tr y i → Boundary tr y j →
      i ≤ j → ReadyAt tr H (catchUp sp) y t → ReadyAt tr H (catchUp sp) y t' →
      Anc (tr.HonestBlocksAt H) (readAfter tr y i t) (readAfter tr y j t')

/-- **R.2, inclusion, under growing faults.** Under `Sleepy` with look-ahead `ahead`, every honest
proposal released at `τ` by a proposer ready at `τ` and still honest at `τ + hold` is in the
confirmed read of every node ready at `t`, for every `t ≥ τ + 6Δ`. -/
def IncludeSleepy : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n) (ΔF : Time),
    sp.committeeSize = sp.n →
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → Compose.NoCollRun dg tr →
    tr.SleepyRunAt H ΔF (ahead sp) →
    ∀ τ P, ReadyProposalAt tr H (catchUp sp) τ (hold sp) P →
      ∀ y t j, τ + 6 * sp.Δ ≤ t → ReadyAt tr H (catchUp sp) y t → CutAfter tr j t →
        Anc (tr.HonestBlocksAt H) P (readAfter tr y j t)

/-- **R.2, growth, under growing faults.** Under `Sleepy` with look-ahead `ahead`, for every
`t ≥ 0` with one proposer ready and honest through its hold in every window of `k ≥ 1` slots up
to `t + D`, `D = (4k + 6)Δ`, some honest proposal `P` released at `τ > t` by a proposer ready at
`τ` and honest through its hold is a new common entry at `t + D`: in the read at `t + D` of every
node ready then, in none of the reads at `t` of the nodes ready then, and each of those reads is
an ancestor of each ready read at `t + D`. -/
def GrowSleepy : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n) (ΔF : Time) (k : Nat),
    sp.committeeSize = sp.n →
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → Compose.NoCollRun dg tr →
    tr.SleepyRunAt H ΔF (ahead sp) → 1 ≤ k →
    let D := (4 * k + 6) * sp.Δ
    ∀ t, 0 ≤ t → ProposerRecurrence tr H proposer (catchUp sp) k (hold sp) 0 (t + D) →
      ∃ τ P, t < τ ∧ ReadyProposalAt tr H (catchUp sp) τ (hold sp) P ∧
        (∀ y j, ReadyAt tr H (catchUp sp) y (t + D) → CutAfter tr j (t + D) →
          Anc (tr.HonestBlocksAt H) P (readAfter tr y j (t + D))) ∧
        (∀ x jx, ReadyAt tr H (catchUp sp) x t → CutAfter tr jx t →
          ¬ Anc (tr.HonestBlocksAt H) P (readAfter tr x jx t)) ∧
        ∀ x jx y j, ReadyAt tr H (catchUp sp) x t → CutAfter tr jx t →
          ReadyAt tr H (catchUp sp) y (t + D) → CutAfter tr j (t + D) →
          Anc (tr.HonestBlocksAt H) (readAfter tr x jx t) (readAfter tr y j (t + D))

/-- **R.8, `nested`, under growing faults**, at every cut of a node honest at its time. -/
def OutputsNested : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr →
    ∀ y i, y ∈ H (tr.time i) →
      (tr.state y i).fg.Anc (tr.finalizedAt y i) (tr.confirmedAt y i) ∧
      (tr.state y i).fg.Anc (tr.confirmedAt y i) (tr.headAt y i)

/-- **R.8, `finalMonotone`, under growing faults**, for a node honest at the later cut. -/
def FinalizedMonotone : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr →
    ∀ y i j, i ≤ j → y ∈ H (tr.time j) →
      (tr.state y j).fg.Anc (tr.finalizedAt y i) (tr.finalizedAt y j)

/-- **R.8, `outputValid`, under growing faults**, at every cut of a node honest at its time. -/
def OutputsValid : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr →
    ∀ y i, y ∈ H (tr.time i) →
      ValidOutput tr proposer dg y i (tr.finalizedAt y i) ∧
      ValidOutput tr proposer dg y i (tr.confirmedAt y i)

/-- **R.7, `finalAccountable`, under growing faults.** If the finalized tips of two nodes, each
honest at its own cut, conflict inside the blocks held while honest, at least `2q − n`
validators each have a slashable pair among the attestations included on two chains the two
readers hold. No fault bound. -/
def FinalAccountable : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → Compose.NoCollRun dg tr →
    ∀ y z i j, y ∈ H (tr.time i) → z ∈ H (tr.time j) →
      ¬ Compatible (tr.HonestBlocksAt H) (tr.finalizedAt y i) (tr.finalizedAt z j) →
      ∃ X₁ ∈ (tr.state y i).fg.tree, ∃ X₂ ∈ (tr.state z j).fg.tree,
        ∃ S : Finset (Fin sp.n), 2 * sp.toParams.q - sp.n ≤ S.card ∧
          ∀ v ∈ S, ∃ a ∈ ChainAtts tr y i X₁ ∪ ChainAtts tr z j X₂,
            ∃ b ∈ ChainAtts tr y i X₁ ∪ ChainAtts tr z j X₂, a.val = v ∧ FG.slashable a b

/-- **R.7, `nonFraming`, under growing faults.** A validator honest at the later of two of its
signings signs no slashable pair with them. -/
def NonFraming : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr →
    ∀ v k k' a b, tr.SignAt v k a → tr.SignAt v k' b → v ∈ H (max (tr.time k) (tr.time k')) →
      ¬ FG.slashable a b

/-- **R.7, `finalized_safe_below_third`, under growing faults.** With fewer than `2q − n`
validators compromised by the later of the two reads, the finalized tips of two nodes, each honest
at its own cut, never conflict. -/
def FinalizedSafe : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → Compose.NoCollRun dg tr →
    ∀ y z i j, y ∈ H (tr.time i) → z ∈ H (tr.time j) →
      (H (max (tr.time i) (tr.time j)))ᶜ.ncard < 2 * sp.toParams.q - sp.n →
      Compatible (tr.HonestBlocksAt H) (tr.finalizedAt y i) (tr.finalizedAt z j)

end Consensus.Goldilocks.Regimes.Growing

end
