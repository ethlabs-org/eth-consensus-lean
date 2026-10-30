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
the honest confirmed outputs (`sleepy_confirmed_compatible`). -/

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
    fun y hy i C s hC hCt => held_origin_viable hrun hnc hsl (fun s => (hF s).1) hy i hC hCt⟩
  · exact votesBelow_iff.1 (hF e.msg.slot).2 C s hC y hy i e he hs le_rfl
  · obtain ⟨L, hL, hLr, C, hC, hLC⟩ := lock_origin hrun hnc hy i l hl
    exact ⟨L, hL, hLr, onOriginChain_iff.2 (Or.inr ⟨C, l.slot, hC, hLC⟩)⟩

/-- **R.1's safety part under `Sleepy`**: the confirmed outputs of honest nodes at any two cuts
are compatible (inside the honest blocks), whether or not the nodes are served. -/
theorem sleepy_confirmed_compatible (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) :
    ∀ y ∈ H, ∀ y' ∈ H, ∀ i i',
      Compatible (tr.HonestBlocks H) (tr.confirmedAt y i) (tr.confirmedAt y' i') :=
  (sleepy_invariant hrun hnc hsl).confirmed_compatible hrun hnc

end Consensus.Goldilocks.Compose

end
