module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.FG.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Phase
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Reset
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PhaseMono
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service

public section

/-! # Healing phases over a fixed later honest cohort

The cohort is `H d` throughout each comparison or count. These lemmas do not identify a
phase over that cohort with a phase over the validators honest at an earlier cut. No
service or global origin invariant is reconstructed on the retained trace.
-/

namespace Consensus.Goldilocks.Healing.Growing

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Time → Set (Fin P.n)}
  {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}

/-- Retention preserves the phase vocabulary at every bounded observation. -/
theorem justifiedAt_upTo_iff {d : Time} {i h : Nat} {J : NodeBlock P ACP}
    (hi : ∀ k < i, tr.time k ≤ d) :
    JustifiedAt (tr.upTo d) (H d) i h J ↔ JustifiedAt tr (H d) i h J := by
  simp only [JustifiedAt, FGTrace.store, Trace.upTo_state tr _ hi]

/-- Contest witnesses are unchanged by retention through their observation. -/
theorem contestAt_upTo_iff {d : Time} {i m : Nat} {J : NodeBlock P ACP}
    (hi : ∀ k < i, tr.time k ≤ d) :
    ContestAt (tr.upTo d) (H d) i m J ↔ ContestAt tr (H d) i m J := by
  simp only [ContestAt, FGTrace.store, Trace.upTo_state tr _ hi]

/-- The frontier of a fixed cohort is unchanged at a bounded cut. -/
theorem frontierAt_upTo_iff {d : Time} {i m : Nat}
    (hi : ∀ k < i, tr.time k ≤ d) :
    FrontierAt (tr.upTo d) (H d) i m ↔ FrontierAt tr (H d) i m := by
  simp only [FrontierAt, FGTrace.store, Trace.upTo_state tr _ hi]

/-- Retention transports the complete phase, keeping its cohort fixed. -/
theorem phaseAt_upTo_iff {d : Time} {i m : Nat} {c : PhaseCase (NodeBlock P ACP)}
    (hi : ∀ k < i, tr.time k ≤ d) :
    PhaseAt (tr.upTo d) (H d) i m c ↔ PhaseAt tr (H d) i m c := by
  cases c <;> simp only [PhaseAt, frontierAt_upTo_iff hi, justifiedAt_upTo_iff hi,
    contestAt_upTo_iff hi]

/-- Equal justified heights agree across observations of the same later-horizon cohort.
Only the states before the observations need to be within the retained prefix. -/
theorem J_eq_of_hj_eq (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    {d : Time} (hd : 0 ≤ d) (hf : (H d)ᶜ.ncard < 2 * P.fg.q - P.n)
    {y z : Fin P.n} (hy : y ∈ H d) (hz : z ∈ H d) {i j : Nat}
    (hi : ∀ k < i, tr.time k ≤ d) (hj : ∀ k < j, tr.time k ≤ d)
    {B B' : NodeBlock P ACP}
    (hB : B ∈ (tr.store y i).tree) (hB' : B' ∈ (tr.store z j).tree)
    (he : ((tr.store y i).σ B.root).hj = ((tr.store z j).σ B'.root).hj) :
    ((tr.store y i).σ B.root).J = ((tr.store z j).σ B'.root).J := by
  simpa only [FGTrace.store, Trace.upTo_state tr _ hi, Trace.upTo_state tr _ hj]
    using Healing.J_eq_of_hj_eq (hr.upTo hd) hf hy hz (i := i) (j := j) (B := B) (B' := B')
      (by simpa only [FGTrace.store, Trace.upTo_state tr _ hi] using hB)
      (by simpa only [FGTrace.store, Trace.upTo_state tr _ hj] using hB')
      (by simpa only [FGTrace.store, Trace.upTo_state tr _ hi,
        Trace.upTo_state tr _ hj] using he)

/-- A justified entry is unique across bounded cuts, without changing the cohort. -/
theorem justifiedAt_unique (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    {d : Time} (hd : 0 ≤ d) (hf : (H d)ᶜ.ncard < 2 * P.fg.q - P.n)
    {i j h : Nat} (hi : ∀ k < i, tr.time k ≤ d) (hj : ∀ k < j, tr.time k ≤ d)
    {J J' : NodeBlock P ACP} (hJ : JustifiedAt tr (H d) i h J)
    (hJ' : JustifiedAt tr (H d) j h J') : J = J' := by
  exact Healing.justifiedAt_unique (hr.upTo hd) hf
    ((justifiedAt_upTo_iff hi).mpr hJ) ((justifiedAt_upTo_iff hj).mpr hJ')

/-- A justification held by a validator honest at the later horizon stays held up to it. -/
theorem justifiedAt_mono (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    {d : Time} (hd : 0 ≤ d) {i j h : Nat} (hij : i ≤ j)
    (hj : ∀ k < j, tr.time k ≤ d) {J : NodeBlock P ACP}
    (hJ : JustifiedAt tr (H d) i h J) : JustifiedAt tr (H d) j h J := by
  have hi : ∀ k < i, tr.time k ≤ d := fun k hk => hj k (hk.trans_le hij)
  exact (justifiedAt_upTo_iff hj).mp
    (Healing.justifiedAt_mono (hr.upTo hd) hij ((justifiedAt_upTo_iff hi).mpr hJ))

/-- A contest's holder survives throughout the fixed horizon comparison. -/
theorem contestAt_mono (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    {d : Time} (hd : 0 ≤ d) {i j m : Nat} (hij : i ≤ j)
    (hj : ∀ k < j, tr.time k ≤ d) {J : NodeBlock P ACP}
    (hc : ContestAt tr (H d) i m J) : ContestAt tr (H d) j m J := by
  have hi : ∀ k < i, tr.time k ≤ d := fun k hk => hj k (hk.trans_le hij)
  exact (contestAt_upTo_iff hj).mp
    (Healing.contestAt_mono (hr.upTo hd) hij ((contestAt_upTo_iff hi).mpr hc))

/-- At a fixed frontier, phases of one later-horizon cohort move only forward. -/
theorem phaseAt_mono (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    {d : Time} (hd : 0 ≤ d) (hf : (H d)ᶜ.ncard < 2 * P.fg.q - P.n)
    {i j m : Nat} {c c' : PhaseCase (NodeBlock P ACP)} (hij : i ≤ j)
    (hj : tr.time j ≤ d)
    (hc : PhaseAt tr (H (max d (tr.time i))) i m c)
    (hc' : PhaseAt tr (H (max d (tr.time j))) j m c') :
    c.rank ≤ c'.rank ∧ ∀ J, c.topJ = some J → c'.topJ = some J := by
  have hi := (hr.time_mono hij).trans hj
  rw [max_eq_left hi] at hc
  rw [max_eq_left hj] at hc'
  exact Healing.phaseAt_mono (hr.upTo hd) hf hij
    ((phaseAt_upTo_iff (fun k hk => (hr.time_mono hk.le).trans hi)).mpr hc)
    ((phaseAt_upTo_iff (fun k hk => (hr.time_mono hk.le).trans hj)).mpr hc')

/-- A bounded cut has at most one phase for the fixed cohort. -/
theorem phaseAt_unique (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    {d : Time} (hd : 0 ≤ d) (hf : (H d)ᶜ.ncard < 2 * P.fg.q - P.n)
    {i m : Nat} (hi : ∀ k < i, tr.time k ≤ d)
    {c c' : PhaseCase (NodeBlock P ACP)}
    (hc : PhaseAt tr (H d) i m c) (hc' : PhaseAt tr (H d) i m c') : c = c' := by
  exact Healing.phaseAt_unique (hr.upTo hd) hf
    ((phaseAt_upTo_iff hi).mpr hc) ((phaseAt_upTo_iff hi).mpr hc')

/-- There are at most two bounded phase changes at a frontier, all charged to the same `d`.
The bound on `i + 1` includes every transition visible in the second observation. -/
theorem phase_changes_le_two (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    {d : Time} (hd : 0 ≤ d) (hf : (H d)ᶜ.ncard < 2 * P.fg.q - P.n) (m : Nat) :
    {i | tr.time (i + 1) ≤ d ∧ ∃ c c',
      PhaseAt tr (H (max d (tr.time i))) i m c ∧
      PhaseAt tr (H (max d (tr.time (i + 1)))) (i + 1) m c' ∧ c ≠ c'}.encard ≤ 2 := by
  apply le_trans (Set.encard_le_encard ?_) (Healing.phase_changes_le_two (hr.upTo hd) hf m)
  intro i hi
  obtain ⟨hib, c, c', hc, hc', hne⟩ := hi
  have hi := (hr.time_mono i.le_succ).trans hib
  rw [max_eq_left hi] at hc
  rw [max_eq_left hib] at hc'
  exact ⟨c, c', (phaseAt_upTo_iff (fun k hk => (hr.time_mono hk.le).trans hi)).mpr hc,
    (phaseAt_upTo_iff (fun k hk => (hr.time_mono hk.le).trans hib)).mpr hc', hne⟩

/-- HR.2 (b)/(c), with precisely the fixed-cohort reading of the growing statement.
A negative horizon has no observations, rather than requiring an extra premise. -/
theorem phase_count_at (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    (d : Time) (hf : (H d)ᶜ.ncard < 2 * P.fg.q - P.n) :
    (∀ m i j c c', i ≤ j → tr.time j ≤ d → PhaseAt tr (H d) i m c →
      PhaseAt tr (H d) j m c' → c.rank ≤ c'.rank ∧ ∀ J, c.topJ = some J → c'.topJ = some J) ∧
    ∀ m, {i | tr.time (i + 1) ≤ d ∧ ∃ c c', PhaseAt tr (H d) i m c ∧
      PhaseAt tr (H d) (i + 1) m c' ∧ c ≠ c'}.encard ≤ 2 := by
  constructor
  · intro m i j c c' hij hj hc hc'
    have hi := (hr.time_mono hij).trans hj
    apply phaseAt_mono hr ((hr.time_nonneg j).trans hj) hf hij hj
    · simpa only [max_eq_left hi] using hc
    · simpa only [max_eq_left hj] using hc'
  · intro m
    by_cases hd : 0 ≤ d
    · apply le_trans (Set.encard_le_encard ?_) (phase_changes_le_two hr hd hf m)
      rintro i ⟨hib, c, c', hc, hc', hne⟩
      have hi := (hr.time_mono i.le_succ).trans hib
      exact ⟨hib, c, c', by simpa only [max_eq_left hi] using hc,
        by simpa only [max_eq_left hib] using hc', hne⟩
    · have he : {i | tr.time (i + 1) ≤ d ∧ ∃ c c', PhaseAt tr (H d) i m c ∧
          PhaseAt tr (H d) (i + 1) m c' ∧ c ≠ c'} = ∅ := by
        ext i
        exact ⟨fun hi => (hd ((hr.time_nonneg (i + 1)).trans hi.1)).elim, False.elim⟩
      rw [he, Set.encard_empty]
      exact zero_le

/-- A phase change persists within one fixed later-horizon cohort. This is the static
potential argument on the retained run, not transport to a different cohort. -/
theorem phaseChanged_mono (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    {d : Time} (hd : 0 ≤ d) (hf : (H d)ᶜ.ncard < 2 * P.fg.q - P.n)
    {i j₁ j₂ : Nat} (hij : i ≤ j₁) (hj : j₁ ≤ j₂) (hjd : tr.time j₂ ≤ d)
    (hc : PhaseChanged tr (H d) i j₁) : PhaseChanged tr (H d) i j₂ := by
  have hb : ∀ {k}, k ≤ j₂ → ∀ l < k, tr.time l ≤ d :=
    fun hk l hl => (hr.time_mono (hl.le.trans hk)).trans hjd
  have hc' : PhaseChanged (tr.upTo d) (H d) i j₁ := by
    intro m c hi hj₁
    exact hc m c ((phaseAt_upTo_iff (hb (hij.trans hj))).mp hi)
      ((phaseAt_upTo_iff (hb hj)).mp hj₁)
  have h := Healing.PhaseChanged.mono (hr.upTo hd) hf hij hj hc'
  intro m c hi hj₂
  exact h m c ((phaseAt_upTo_iff (hb (hij.trans hj))).mpr hi)
    ((phaseAt_upTo_iff (hb le_rfl)).mpr hj₂)

end Consensus.Goldilocks.Healing.Growing

end
