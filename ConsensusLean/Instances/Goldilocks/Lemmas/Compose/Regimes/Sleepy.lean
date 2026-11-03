module
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Read

public section

/-! # Goldilocks milestone Regimes: R.1 under `Sleepy`

Under `Sleepy` (and `NoColl`), every confirmed read of an honest node, at the state before any cut
and at any time, is an honest block on the origin chain (`confirmed_read_on_chain` with the
Sleepy invariant), and blocks on the origin chain are compatible. So any two honest confirmed
reads are compatible (`sleepy_reads_compatible`), the agreement half of `ReadySafeOn`
(`sleepy_ready_agree`). At a ready read point the read is the effective record (the record's
block, or `Σ.F` when the record is not in the frame; `ready_read_record`), which only moves to
descendants (`effective_record_mono`): the monotone half (`sleepy_ready_mono`). Together,
`sleepy_safe : SleepySafe`.

Up to a horizon `b`, `sleepy_safe_before` gives the same two halves under `SleepyServiceBefore b`
(the route of the finite Refinement form `sleepy_safe_finite`). There is no node-level prefix
row: the prefix claim is the generic `Good.sleepySafe_prefix`. -/

namespace Consensus.Goldilocks.Regimes

open SA (SAParams ReplayOrder Payload)
open Compose

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **Agreement of the honest confirmed reads under `Sleepy`**: any two confirmed reads of honest
nodes, at any cuts and at any times, are compatible (inside the honest blocks). -/
theorem sleepy_reads_compatible (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) :
    ∀ y ∈ H, ∀ z ∈ H, ∀ i j t t',
      Compatible (tr.HonestBlocks H) (readAfter tr y i t) (readAfter tr z j t') := by
  intro y hy z hz i j t t'
  have hinv := sleepy_invariant hrun hnc hsl
  obtain ⟨hB, hc⟩ := confirmed_read_on_chain hinv hrun hnc hy i t
  obtain ⟨hB', hc'⟩ := confirmed_read_on_chain hinv hrun hnc hz j t'
  exact OnOriginChain.compatible hrun hnc hinv.origins_compatible hB hB' hc hc'

/-- **R.1, the agreement half of `ReadySafeOn`** under `Sleepy`, for every window and catch-up. -/
theorem sleepy_ready_agree (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) (c t₀ t₁ : Time) :
    ∀ y z i j t t', ReadPoint tr i t → ReadPoint tr j t' → Boundary tr y i → Boundary tr z j →
      t₀ ≤ t → t ≤ t₁ → t₀ ≤ t' → t' ≤ t₁ → ReadyAt tr H c y t → ReadyAt tr H c z t' →
      Compatible (tr.HonestBlocks H) (readAfter tr y i t) (readAfter tr z j t') :=
  fun y z i j t t' _ _ _ _ _ _ _ _ hy hz =>
    sleepy_reads_compatible hrun hnc hsl y hy.1 z hz.1 i j t t'


private theorem lookup_getD_of_mem {Φ : SA.Frm sp.n (List (FG.Att sp.n))} (hΦ : FrameOK Φ)
    {R : SA.Blk sp.n (List (FG.Att sp.n))} (hR : R ∈ Φ.tree) {r : Nat} (hr : R.root = r) :
    (SA.lookup Φ r).getD Φ.F = R := by
  cases h : SA.lookup Φ r with
  | none => exact absurd ⟨R, hR, hr⟩ (SA.lookup_eq_none h)
  | some R' =>
    obtain ⟨hR', hr'⟩ := SA.lookup_eq_some h
    exact hΦ.coherent.1 hR' hR (hr'.trans hr.symm)

private theorem lookup_getD_of_not {Φ : SA.Frm sp.n (List (FG.Att sp.n))} {r : Nat}
    (hn : ¬ ∃ R ∈ Φ.tree, R.root = r) : (SA.lookup Φ r).getD Φ.F = Φ.F := by
  cases h : SA.lookup Φ r with
  | none => rfl
  | some R' =>
    obtain ⟨hR', hr'⟩ := SA.lookup_eq_some h
    exact absurd ⟨R', hR', hr'⟩ hn

/-- The confirmed read is the effective record (the record's block when it is in the frame, else
`Σ.F`) when it is one of the two (`ready_read_record`'s conclusion). -/
private theorem read_effective_of (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {t : Time}
    (h : (∃ R ∈ (Node.frame (tr.state y j)).tree,
        R.root = (tr.state y j).ac.latestConfirmed ∧ readAfter tr y j t = R) ∨
      ((¬ ∃ R ∈ (Node.frame (tr.state y j)).tree,
          R.root = (tr.state y j).ac.latestConfirmed) ∧
        readAfter tr y j t = (tr.state y j).fg.F)) :
    readAfter tr y j t = (SA.lookup (Node.frame (tr.state y j))
      (tr.state y j).ac.latestConfirmed).getD (Node.frame (tr.state y j)).F := by
  have hΦ : FrameOK (Node.frame (tr.state y j)) :=
    (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy j)).1
  rcases h with ⟨R, hR, hRr, h⟩ | ⟨hn, h⟩
  · rw [h, lookup_getD_of_mem hΦ hR hRr]
  · rw [h, lookup_getD_of_not hn]
    rfl

/-- At a ready read point (between the reader's events), the confirmed read is the effective
record: the record's block when it is in the frame, else `Σ.F`. -/
theorem ready_read_effective (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {y : Fin sp.n} {j : Nat} {t : Time} (hrp : ReadPoint tr j t)
    (hb : Boundary tr y j) (hready : ReadyAt tr H (catchUp sp) y t) :
    readAfter tr y j t = (SA.lookup (Node.frame (tr.state y j))
      (tr.state y j).ac.latestConfirmed).getD (Node.frame (tr.state y j)).F :=
  read_effective_of hrun hready.1 (ready_read_record hrun hnc hsl hrp hb hready)

/-- **R.1, the monotone half of `ReadySafeOn`** under `Sleepy`, for every window and catch-up
`18Δ`. -/
theorem sleepy_ready_mono (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) (t₀ t₁ : Time) :
    ∀ y i j t t', ReadPoint tr i t → ReadPoint tr j t' → Boundary tr y i → Boundary tr y j →
      i ≤ j → t ≤ t' → t₀ ≤ t → t' ≤ t₁ → ReadyAt tr H (catchUp sp) y t →
      ReadyAt tr H (catchUp sp) y t' →
      Anc (tr.HonestBlocks H) (readAfter tr y i t) (readAfter tr y j t') := by
  intro y i j t t' hi hj hbi hbj hij _ _ _ hy hy'
  rw [ready_read_effective hrun hnc hsl hi hbi hy, ready_read_effective hrun hnc hsl hj hbj hy']
  exact effective_record_mono hrun hnc hsl hy.1 hij

/-- **R.1, `sleepySafe` / `confirmed_safe_sleepy`.** -/
theorem sleepy_safe : SleepySafe := fun _ _ _ _ _ _ _ hrun hnc hsl t₁ =>
  ⟨sleepy_ready_agree hrun hnc hsl _ 0 t₁, sleepy_ready_mono hrun hnc hsl 0 t₁⟩

/-- R.1 localized to recipient deadlines within the observation horizon. -/
theorem sleepy_safe_before {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d)) : ReadySafeOn tr H (catchUp sp) 0 b := by
  have hinv := sleepy_invariant_before hrun hnc hb hsync hfb
  have hac := hsync.ac
  have hpop := fun s hs => hfb s sp.Δ (by simp) hs
  refine ⟨fun y z i j t t' hi hj _ _ _ htb _ htb' hy hz => ?_,
    fun y i j t t' hi hj hbi hbj hij htt _ htb hy hy' => ?_⟩
  · exact hinv.read_compatible hrun hnc hy.1 hz.1 (fun k hk => (hi.1 k hk).trans htb)
      (fun k hk => (hj.1 k hk).trans htb') t t'
  · rw [read_effective_of hrun hy.1 (ready_read_record_before hrun hnc hinv hac hpop hi hbi hy
        (htt.trans htb)),
      read_effective_of hrun hy'.1 (ready_read_record_before hrun hnc hinv hac hpop hj hbj hy' htb)]
    exact effective_record_mono_of_invariant hrun hnc hinv hy.1 hij
      fun k hk => (hj.1 k hk).trans htb

end Consensus.Goldilocks.Regimes

end
