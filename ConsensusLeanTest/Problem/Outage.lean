module
public import ConsensusLean.Lemmas.Problem.Facts.Outage

@[expose] public section

/-! # Outage premises at other numbers: statements and axioms

The facts of `Lemmas/Problem/Facts/Outage` that a client uses restated as named theorems, with their
axioms pinned: the η-sleepy participation weakens at smaller numbers (`EtaSleepyOn.weaken`), the
cohort margin passes to subwindows on a retained view (`NoSleepOn.retain_sub`,
`NoSleepOn.awakeAt_sub`, `CohortOn.retain_sub`), and readiness and protected recovery move with the
catch-up (`Ready.catchUp_mono`, `ProtectedReadyUpTo.catchUp_mono`). -/

namespace Consensus.OutageFactsTest

variable {V : Type}

/-- Readiness at a longer catch-up implies readiness at a shorter one. -/
theorem ready_catchUp_mono (p : EnvPoint V) {c c' : Time} {v : V} {t : Time}
    (h : p.Ready c' v t) (hc : c ≤ c') : p.Ready c v t :=
  EnvPoint.Ready.catchUp_mono p h hc

/-- η-sleepy participation weakens at smaller numbers. -/
theorem etaSleepyOn_weaken [Fintype V] [DecidableEq V] (p : EnvPoint V) {θ θ' : ℚ}
    {η η' c c' W W' a b : Time} (h : p.EtaSleepyOn θ η c W a b) (ha : 0 ≤ a) (hθ : θ' ≤ θ)
    (hθ0 : 0 ≤ θ') (hη : η' ≤ η) (hc : c' ≤ c) (hc0 : 0 ≤ c') (hW : W' ≤ W) :
    p.EtaSleepyOn θ' η' c' W' a b :=
  EnvPoint.EtaSleepyOn.weaken p h ha hθ hθ0 hη hc hc0 hW

/-- `NoSleepOn` on a retained view passes to every subwindow. -/
theorem noSleepOn_retain_sub (p : EnvPoint V) {d a z a' z' : Time}
    (h : (p.retain d).NoSleepOn a z) (ha : a ≤ a') (hz : z' ≤ z) :
    (p.retain d).NoSleepOn a' z' :=
  EnvPoint.NoSleepOn.retain_sub p h ha hz

/-- The awake set at the start grows to a later start within the window. -/
theorem noSleepOn_awakeAt_sub [Fintype V] [DecidableEq V] (p : EnvPoint V) {d a z a' : Time}
    (h : (p.retain d).NoSleepOn a z) (ha : a ≤ a') (haz : a = a' ∨ a' ≤ z) :
    (p.retain d).awakeAt a ⊆ (p.retain d).awakeAt a' :=
  EnvPoint.NoSleepOn.awakeAt_sub p h ha haz

/-- `CohortOn` with `NoSleepOn` passes to subwindows. -/
theorem cohortOn_retain_sub [Fintype V] [DecidableEq V] (p : EnvPoint V) {d a z a' z' : Time}
    (hns : (p.retain d).NoSleepOn a z) (h : (p.retain d).CohortOn a z) (ha : a ≤ a')
    (hz : z' ≤ z) (haz : a = a' ∨ a' ≤ z) : (p.retain d).CohortOn a' z' :=
  EnvPoint.CohortOn.retain_sub p hns h ha hz haz

/-- Protected recovery for a shorter catch-up gives it for a longer one. -/
theorem protectedReadyUpTo_catchUp_mono {α Id : Type} (tr : Trace V α Id) {c c' : Time}
    {src dst : Id} {T t₀ b : Time} (h : tr.ProtectedReadyUpTo c src dst T t₀ b) (hc : c ≤ c') :
    tr.ProtectedReadyUpTo c' src dst T t₀ b :=
  Trace.ProtectedReadyUpTo.catchUp_mono tr h hc

end Consensus.OutageFactsTest

-- `#guard_msgs in #print axioms` puts the command off column 0; the pinned messages are longer
-- than 100 columns.
set_option linter.style.whitespace false
set_option linter.style.longLine false

/-- info: 'Consensus.OutageFactsTest.ready_catchUp_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.OutageFactsTest.ready_catchUp_mono

/-- info: 'Consensus.OutageFactsTest.etaSleepyOn_weaken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.OutageFactsTest.etaSleepyOn_weaken

/-- info: 'Consensus.OutageFactsTest.noSleepOn_retain_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.OutageFactsTest.noSleepOn_retain_sub

/-- info: 'Consensus.OutageFactsTest.noSleepOn_awakeAt_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.OutageFactsTest.noSleepOn_awakeAt_sub

/-- info: 'Consensus.OutageFactsTest.cohortOn_retain_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.OutageFactsTest.cohortOn_retain_sub

/-- info: 'Consensus.OutageFactsTest.protectedReadyUpTo_catchUp_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.OutageFactsTest.protectedReadyUpTo_catchUp_mono

end
