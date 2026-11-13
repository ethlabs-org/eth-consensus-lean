module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.TransferLater
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Read
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record

public section

/-! # Goldilocks under `Sleepy` with growing faults: ready-reader safety (R.1, finite)

The growing-fault form of `Compose/Regimes/Sleepy`. A reader is read at a read point `(i, t)`
between its events, ready at `t` (honest at `t`, every cut before `i` at a time `≤ t`):

* `ReadySafeOn tr H c t₀ t₁`: agreement of the reads of two ready nodes and monotonicity of a
  ready node's reads, at read times in `[t₀, t₁]`, inside the blocks held while honest;
* `sleepy_safe_at`: `ReadySafeOn tr H catchUp 0 b` from the finite service and the count shapes
  through `b`. Agreement is `read_compatible_at`; a ready read is the effective record
  (`ready_read_record_at`), which only extends (`effective_record_mono_at`). -/

namespace Consensus.Goldilocks.Regimes.Growing

open SA (SAParams ReplayOrder Payload)
open Compose.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- Ready-reader safety of the confirmed output under growing faults, at the read points of
times in `[t₀, t₁]` between the reader's events: each reader is ready at its read time (honest
then, with every earlier cut at a time `≤ t`), and ancestry is read inside the blocks held while
honest. -/
structure ReadySafeOn (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (c t₀ t₁ : Time) : Prop where
  /-- Agreement of the reads of two ready nodes. -/
  agree : ∀ y z i j t t', ReadPoint tr i t → ReadPoint tr j t' → Boundary tr y i →
    Boundary tr z j → t₀ ≤ t → t ≤ t₁ → t₀ ≤ t' → t' ≤ t₁ → ReadyAt tr H c y t →
    ReadyAt tr H c z t' →
    Compatible (tr.HonestBlocksAt H) (readAfter tr y i t) (readAfter tr z j t')
  /-- Monotonicity of a ready node's reads. -/
  mono : ∀ y i j t t', ReadPoint tr i t → ReadPoint tr j t' → Boundary tr y i →
    Boundary tr y j → i ≤ j → t ≤ t' → t₀ ≤ t → t' ≤ t₁ → ReadyAt tr H c y t →
    ReadyAt tr H c y t' →
    Anc (tr.HonestBlocksAt H) (readAfter tr y i t) (readAfter tr y j t')

/-- The confirmed read is the effective record (the record's block when it is in the frame, else
`Σ.F`) when it is one of the two, for a node honest at a time `t ≥ 0` at or after every cut before
`j`. -/
private theorem read_effective_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {j : Nat} {t u : Time} (ht0 : 0 ≤ t) (hj : ∀ k < j, tr.time k ≤ t)
    (hy : y ∈ H t)
    (h : (∃ R ∈ (Node.frame (tr.state y j)).tree,
        R.root = (tr.state y j).ac.latestConfirmed ∧ readAfter tr y j u = R) ∨
      ((¬ ∃ R ∈ (Node.frame (tr.state y j)).tree,
          R.root = (tr.state y j).ac.latestConfirmed) ∧
        readAfter tr y j u = (tr.state y j).fg.F)) :
    readAfter tr y j u = (SA.lookup (Node.frame (tr.state y j))
      (tr.state y j).ac.latestConfirmed).getD (Node.frame (tr.state y j)).F := by
  have hΦ : FrameOK (Node.frame (tr.state y j)) := by
    rw [← Trace.upTo_state tr y hj]
    exact Compose.frameOK_state (hrun.upTo ht0).toLocalRun hy j
  rcases h with ⟨R, hR, hRr, h⟩ | ⟨hn, h⟩
  · rw [h]
    cases hl : SA.lookup (Node.frame (tr.state y j)) (tr.state y j).ac.latestConfirmed with
    | none => exact absurd ⟨R, hR, hRr⟩ (SA.lookup_eq_none hl)
    | some R' =>
      obtain ⟨hR', hr'⟩ := SA.lookup_eq_some hl
      exact (hΦ.coherent.1 hR' hR (hr'.trans hRr.symm)).symm
  · rw [h]
    cases hl : SA.lookup (Node.frame (tr.state y j)) (tr.state y j).ac.latestConfirmed with
    | none => rfl
    | some R' =>
      obtain ⟨hR', hr'⟩ := SA.lookup_eq_some hl
      exact absurd ⟨R', hR', hr'⟩ hn

/-- **Finite ready-reader safety under growing faults** through `b`, from the finite service and
the count shapes through `b`. -/
theorem sleepy_safe_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {ΔF b : Time} (hb : 0 ≤ b)
    (hsync : Compose.Growing.SleepyServiceBefore tr H ΔF b)
    (hB : Compose.Growing.SleepyBoundsFrom tr H 0 b) (hstock : sp.committeeSize = sp.n) :
    ReadySafeOn tr H (catchUp sp) 0 b := by
  have hinv := sleepy_invariant_at hrun hnc (CommitteeFacts.of_full hrun hnc hstock) hb hsync hB
    (CommitteeBoundsFrom.of_full hrun hB)
  refine ⟨fun y z i j t t' hi hj _ _ ht0 htb ht0' htb' hy hz => ?_,
    fun y i j t t' hi hj _ _ hij htt ht0 htb hy hy' => ?_⟩
  · exact hinv.read_compatible_at hrun hnc ht0 hi.1 htb hy.1 ht0' hj.1 htb' hz.1 t t'
  · have ht0' := ht0.trans htt
    rw [read_effective_at hrun ht0 hi.1 hy.1
        (ready_read_record_at hrun hnc hinv hsync hB hi ht0 hy (htt.trans htb)),
      read_effective_at hrun ht0' hj.1 hy'.1
        (ready_read_record_at hrun hnc hinv hsync hB hj ht0' hy' htb)]
    exact hinv.effective_record_mono_at hrun hnc hij ht0' hj.1 htb hy'.1

end Consensus.Goldilocks.Regimes.Growing

end
