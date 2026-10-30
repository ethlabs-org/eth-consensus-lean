module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Persist

@[expose] public section

/-! # Goldilocks milestone Service: the available chain after C1.1 (statements)

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` (goldilocks main
`4ea71d05`) §"Available chain, after C1.1", over the Goldilocks run (`Spec/Run`,
`GoldilocksRun`) under `Sleepy` (`SleepyRun`) and `NoColl` (`NoCollRun`; the claims' standing
assumption on the digest, taken explicitly here as every run-level statement does, since the
SA's chain reasoning identifies blocks by root):

* **A1.6, head extends the record under synchrony**: at an honest node awake and joined at `t`
  that has run the update of slot `slot(t) − 2` with no restart since, the head extends
  `𝒜.latest_confirmed` when that block is in the frame's tree, so `ac_confirmed` is that block;
  and while both conditions hold, the record only moves to a descendant.
* **A1.7, inclusion**: an honest proposal `P` of slot `s` by a joined proposer is in the
  confirmed tip of every honest node awake and joined at `t ≥ t_s + 6Δ` that was awake and
  joined at `t_s + 6Δ` with no restart since.

C1.2 (AC outcome service for honest entries) and C1.3 (finalizing coverage recurs) are "to be
fixed" in the claims and are not transcribed. "At `t`" is read at a cut of the node at time `t`
(`tr.IsCall y i`, `tr.time i = t`), with the state before the cut.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- `y` has run the update of slot `s` before cut `i` with no restart since: the update ran at a
cut `k < i` and no cut in `(k, i)` is a restart of `y`. -/
def UpdatedNoRestart (y : Fin sp.n) (i s : Nat) : Prop :=
  ∃ k < i, ∃ ℓ, SA.UpdateAt tr.projAC y k s ℓ ∧ ∀ k', k < k' → k' < i → ¬ tr.RestartAt y k'

/-- The condition of A1.6 at cut `i` of `y`: awake and joined at its time, and the update of
slot `slot(t) − 2` has run with no restart since (`slot(t) ≥ 2`). -/
def ServedAt (y : Fin sp.n) (i : Nat) : Prop :=
  tr.IsCall y i ∧ tr.awake y (tr.time i) ∧ tr.JoinedAt y (tr.time i) ∧
    ∃ s : Nat, s + 2 = sp.slot (tr.time i) ∧ UpdatedNoRestart tr y i s

/-- The block of `y`'s record `𝒜.latest_confirmed` before cut `i`, if it is in the frame's
tree. -/
def RecordAt (y : Fin sp.n) (i : Nat) (R : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  R ∈ (Node.frame (tr.state y i)).tree ∧ R.root = (tr.state y i).ac.latestConfirmed

/-- **A1.6, head extends the record under synchrony.** Under `Sleepy`, at every cut of an honest
node awake and joined at its time that has run the update of slot `slot(t) − 2` with no restart
since: when the record `𝒜.latest_confirmed` is a block of the frame's tree, the head extends it
(inside the frame) and `ac_confirmed` is that block; and while the condition keeps holding (at
every cut of the node from now to a later cut), the record then extends the record now (inside
the honest blocks). -/
def HeadExtendsRecord : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (ΔF : Time),
    GoldilocksRun dg H tr → NoCollRun dg tr → tr.SleepyRun H ΔF →
    ∀ y ∈ H, ∀ i, ServedAt tr y i → ∀ R, RecordAt tr y i R →
      ((Node.frame (tr.state y i)).Anc R (tr.headAt y i) ∧ tr.confirmedAt y i = R) ∧
      ∀ i', i ≤ i' → (∀ k, i ≤ k → k ≤ i' → tr.IsCall y k → ServedAt tr y k) →
        ∀ R', RecordAt tr y i' R' → Anc (tr.HonestBlocks H) R R'

/-- **A1.7, inclusion.** Under `Sleepy`, with a genesis whose root is its digest, an honest
proposal `P` of slot `s` by a proposer joined at its proposal is in the confirmed tip (inside
the honest blocks) of every honest node at every cut at a time `t ≥ t_s + 6Δ` where it is awake
and joined, if it was awake and joined at `t_s + 6Δ`, has not restarted at a cut in
`(t_s + 6Δ, t]`, and has run the update of slot `s` at a cut before this one with no restart
since (`UpdatedNoRestart`, as A1.6). The update clause is needed at the boundary `t = t_s + 6Δ`:
"at `t`" is the state before a cut at `t`, and the node's first cut there is the AC tick that
runs the update of slot `s` (at `t_{s+1} + 2Δ`), so before it the record can still be older
than `P` (consensus-lean#77). With the node awake and joined at `t_s + 6Δ` the update is that
tick, so the clause excludes only the cuts of that tick up to the update. The genesis root is
needed as in C0.3: an honest proposal whose root is `P.genesisRoot` is refused by every FG, so
it is in no honest tree (consensus-lean#73). -/
def Inclusion : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (ΔF : Time),
    GoldilocksRun dg H tr → NoCollRun dg tr → tr.SleepyRun H ΔF →
    (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg →
    ∀ p ∈ H, ∀ k (P : SA.Blk sp.n (List (FG.Att sp.n))) (s : Nat),
      tr.ProposesAt p k P → P.slot = s → SA.joined sp (tr.state p k).ac (tr.time k) →
      ∀ y ∈ H, ∀ i, tr.IsCall y i → sp.ts s + 6 * sp.Δ ≤ tr.time i →
        tr.awake y (tr.time i) → tr.JoinedAt y (tr.time i) →
        tr.awake y (sp.ts s + 6 * sp.Δ) → tr.JoinedAt y (sp.ts s + 6 * sp.Δ) →
        (∀ k', tr.RestartAt y k' → sp.ts s + 6 * sp.Δ < tr.time k' → tr.time k' ≤ tr.time i →
          False) →
        UpdatedNoRestart tr y i s →
        Anc (tr.HonestBlocks H) P (tr.confirmedAt y i)

/-- The statements of milestone Service (so far). -/
structure ServiceStatements : Prop where
  headExtendsRecord : HeadExtendsRecord
  inclusion : Inclusion

end Consensus.Goldilocks.Compose

end
