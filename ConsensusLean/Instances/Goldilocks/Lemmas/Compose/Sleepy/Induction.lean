module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer

public section

/-! # Goldilocks under `Sleepy`: the record invariant from genesis

workbench#11 §4 (the bounded frontier, at workbench `40d6006`): `P_0` and `V_0` hold vacuously;
`P_s, V_s ⊢ P_{s+1}` (`origins_below_succ`) and `P_{s+1}, V_s ⊢ V_{s+1}` (`votes_below_succ`), so
every finite frontier holds (`frontier`), and unbounded S1 and S2 follow. With the provenance of
records, locks, sources and caches (`Sleepy/Provenance`) and full viability (`held_origin_viable`)
this is `SleepyInvariant` (`sleepy_invariant`), and R.1's safety part, pairwise compatibility of
the honest confirmed outputs (`sleepy_confirmed_compatible`).

The same induction runs up to a horizon `b` under the prefix premises of `SleepySafePrefix`
(`SleepyPrefix`: `Sync[0, b − Δ]`, `f < h_t` at the slot points `≤ b`), for the origins within
`b`, the honest votes at times `≤ b` and the cuts within `b` (`frontier_upTo`,
`sleepy_invariant_upTo`): each step reads deliveries of sends at times `≤ b − Δ` and `f < h_t`
at slot points `≤ b` only. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time}

/-- **Every finite frontier**: `P_s` and `V_s` for every `s`. -/
theorem frontier (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) : ∀ s, OriginsBelow tr H s ∧ VotesBelow tr H s := by
  intro s
  induction s with
  | zero =>
    refine ⟨originsBelow_iff.2 fun _ _ _ _ h => absurd h (Nat.not_lt_zero _),
      votesBelow_iff.2 fun _ _ _ _ _ _ _ _ h₁ h₂ => ?_⟩
    omega
  | succ s ih =>
    have hP := origins_below_succ hrun hnc hsl ih.1 ih.2
    exact ⟨hP, votes_below_succ hrun hnc hsl hP ih.2⟩

/-- **The Sleepy record invariant** (S1–S3) holds of every Goldilocks run under `Sleepy` and
`NoColl`. -/
theorem sleepy_invariant (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) : SleepyInvariant tr H := by
  have hF := frontier hrun hnc hsl
  have hcomp : ∀ C s C' s', Origin tr H C s → Origin tr H C' s' →
      Compatible (tr.HonestBlocks H) C C' := fun C s C' s' h h' =>
    originsBelow_iff.1 (hF (max s s' + 1)).1 C s C' s' (by omega) (by omega) h h'
  refine ⟨hcomp, fun C s hC y hy i e he hs => ?_, fun y hy i => record_origin hrun hnc hy i,
    fun y hy i => caches_on_chain hrun hnc hsl hy i, fun y hy i l hl => ?_,
    fun y hy i ℓ C h => source_on_chain hrun hnc hy h,
    fun y hy i C s hC hCt => held_origin_viable hrun hnc hsl (fun s => (hF s).1) hy i
      (fun C' s' hC' => hcomp C s C' s' hC hC'.origin) hCt⟩
  · exact votesBelow_iff.1 (hF e.msg.slot).2 C s hC y hy i e he hs le_rfl
  · obtain ⟨L, hL, hLr, C, hC, hLC⟩ := lock_origin hrun hnc hy i l hl
    exact ⟨L, hL, hLr, onOriginChain_iff.2 (Or.inr ⟨C, l.slot, hC.origin, hLC⟩)⟩

/-- **Every finite frontier up to `b`**: `P_s` and `V_s` up to `b` for every `s`, under the
prefix premises up to `b`. -/
theorem frontier_upTo {b : Time} (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) : ∀ s, OriginsBelowUpTo tr H s b ∧ VotesBelowUpTo tr H s b := by
  intro s
  induction s with
  | zero =>
    refine ⟨originsBelowUpTo_iff.2 fun _ _ _ _ h => absurd h (Nat.not_lt_zero _),
      votesBelowUpTo_iff.2 fun _ _ _ _ _ _ _ _ _ h₁ h₂ => ?_⟩
    omega
  | succ s ih =>
    have hP := origins_below_succ_upTo hrun hnc hpre ih.1 ih.2
    exact ⟨hP, votes_below_succ_upTo hrun hnc hpre hP ih.2⟩

/-- **The Sleepy record invariant up to `b`** (S1–S3 for the origins within `b`, the honest votes
at times `≤ b` and the cuts within `b`) holds of every Goldilocks run under `NoColl` and the
prefix premises of `SleepySafePrefix` up to `b`, whatever happens after `b`. -/
theorem sleepy_invariant_upTo {b : Time} (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) : SleepyInvariantUpTo tr H b := by
  have hF := frontier_upTo hrun hnc hpre
  have hcomp : ∀ C s C' s', OriginWithin tr H C s b → OriginWithin tr H C' s' b →
      Compatible (tr.HonestBlocks H) C C' := fun C s C' s' h h' =>
    originsBelowUpTo_iff.1 (hF (max s s' + 1)).1 C s C' s' (by omega) (by omega) h h'
  have hfb : tr.FaultBound H (sp.ts (0 : Nat) + 0) := (sleepyPrefix_iff.1 hpre).2.2 0 0
    (by simp) (by simpa [SAParams.ts] using (sleepyPrefix_iff.1 hpre).1)
  refine ⟨hcomp, fun C s hC y hy i e he hib hs => ?_,
    fun y hy i hi => record_origin_upTo hrun hnc hy hi,
    fun y hy i hi => caches_on_chain_upTo hrun hnc hfb hy hi, fun y hy i hi l hl => ?_,
    fun y hy i hi ℓ C h => source_on_chain_upTo hrun hnc hy hi h,
    fun y hy i hi C s hC hCt => held_origin_viable_upTo hrun hnc hpre (fun s => (hF s).1) hy i hi
      (fun C' s' hC' => hcomp C s C' s' hC (hC'.within hi)) hCt⟩
  · exact votesBelowUpTo_iff.1 (hF e.msg.slot).2 C s hC y hy i e he hib hs le_rfl
  · obtain ⟨L, hL, hLr, C, hC, hLC⟩ := lock_origin hrun hnc hy i l hl
    exact ⟨L, hL, hLr, onOriginChainWithin_iff.2 (Or.inr ⟨C, l.slot, hC.within hi, hLC⟩)⟩

/-- **R.1's safety part under `Sleepy`**: the confirmed outputs of honest nodes at any two cuts
are compatible (inside the honest blocks), whether or not the nodes are served. -/
theorem sleepy_confirmed_compatible (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) :
    ∀ y ∈ H, ∀ y' ∈ H, ∀ i i',
      Compatible (tr.HonestBlocks H) (tr.confirmedAt y i) (tr.confirmedAt y' i') :=
  (sleepy_invariant hrun hnc hsl).confirmed_compatible hrun hnc

end Consensus.Goldilocks.Compose

end
