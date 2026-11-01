module
public import AvailableChainFGSAProofs.Proofs.Healing.AttemptSettle -- shake: keep (four cut starts)
public import AvailableChainFGSAProofs.Proofs.Healing.Attempt -- shake: keep (conditional assembly)
public import AvailableChainFGSAProofs.Proofs.Healing.AttemptBudget -- shake: keep (four budgets)
public import AvailableChainFGSAProofs.Proofs.Healing.AttemptStop -- shake: keep (event/cut tests)
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseBoot -- shake: keep (B21 boundary)
public import AvailableChainFGSAProofs.Proofs.Assembly.ProgressAttempt -- shake: keep (example)

set_option linter.privateModule false

public section

namespace AvailableChain.FGSA.Run.Tests.HealingAttempt
open AvailableChain.SimplexFG

private def attemptParams : Params where
  Δ := 1
  n := 4
  k := 2
  η := 0
  deltaPos := by decide
  nPos := by decide
  kLarge := by decide
  etaNonneg := by decide
  R := 3
  δt := 6
  RLarge := by decide
  digest := fun d => ⟨d.slot + 1⟩

-- The W bound permits a row delay greater than the block delay.
example : attemptParams.Δ < (6 : Time) ∧ LivenessBoundW attemptParams 6 :=
  ⟨by decide, ⟨by decide⟩⟩

example (k : AttemptKey) (htask : k.task = .raise) (hphase : k.phase = .contest) :
    attemptBudget attemptParams 10 k = 72 := by
  rw [healing_attempt_raise_contest_budget attemptParams 10 k htask hphase]
  decide

example (k : AttemptKey) (htask : k.task = .raise) (hphase : k.phase = .gap) :
    attemptBudget attemptParams 10 k = 112 := by
  rw [healing_attempt_raise_other_budget attemptParams 10 k htask
    (by rw [hphase]; intro h; cases h)]
  decide

example (k : AttemptKey) (htask : k.task = .raise) (hphase : k.phase = .topJ) :
    attemptBudget attemptParams 10 k = 112 := by
  rw [healing_attempt_raise_other_budget attemptParams 10 k htask
    (by rw [hphase]; intro h; cases h)]
  decide

example (k : AttemptKey) (htask : k.task = .firstRow) (hphase : k.phase = .contest) :
    attemptBudget attemptParams 10 k = 45 := by
  rw [healing_attempt_firstRow_contest_budget attemptParams 10 k htask hphase]
  decide

example (k : AttemptKey) (htask : k.task = .firstRow) (hphase : k.phase = .gap) :
    attemptBudget attemptParams 10 k = 85 := by
  rw [healing_attempt_firstRow_other_budget attemptParams 10 k htask
    (by rw [hphase]; intro h; cases h)]
  decide

example (k : AttemptKey) (htask : k.task = .firstRow) (hphase : k.phase = .topJ) :
    attemptBudget attemptParams 10 k = 85 := by
  rw [healing_attempt_firstRow_other_budget attemptParams 10 k htask
    (by rw [hphase]; intro h; cases h)]
  decide

-- The exact sums include settlement, the frozen repair, and each opening.
example (p : Params) (G : Time) :
    (3 * p.Δ + ρΓ p G) + (P p - 4 * p.Δ) + (2 * P p + Γ p G - 9 * p.Δ) =
      ρΓ p G + 3 * P p + Γ p G - 10 * p.Δ :=
  healing_attempt_raise_contest_cost p G

example (p : Params) (G : Time) :
    (3 * p.Δ + ρΓ p G) + (P p - 4 * p.Δ) + (2 * P p + Γ p G - 4 * p.Δ) +
      (P p - 4 * p.Δ) + (2 * P p + Γ p G - 9 * p.Δ) =
      ρΓ p G + 6 * P p + 2 * Γ p G - 18 * p.Δ :=
  healing_attempt_raise_other_cost p G

example (p : Params) (G : Time) :
    (3 * p.Δ + ρΓ p G) + (P p - 4 * p.Δ) = ρΓ p G + P p - p.Δ :=
  healing_attempt_firstRow_contest_cost p G

example (p : Params) (G : Time) :
    (3 * p.Δ + ρΓ p G) + (P p - 4 * p.Δ) + (2 * P p + Γ p G - 4 * p.Δ) +
      (P p - 4 * p.Δ) = ρΓ p G + 4 * P p + Γ p G - 9 * p.Δ :=
  healing_attempt_firstRow_other_cost p G

example (p : Params) (G : Time) (hG : 4 * p.Δ ≤ G) :
    4 * P p + Γ p G - 13 * p.Δ ≤ 6 * P p + 2 * Γ p G - 21 * p.Δ :=
  healing_attempt_high_source_cost p G hG

-- The terminal carrier needs five fewer delta units than the gate-service carrier.
example : (18 : Time) + 2 * P attemptParams + Γ attemptParams 10 - 9 * attemptParams.Δ = 45 ∧
    ¬ ((18 : Time) + 2 * P attemptParams + Γ attemptParams 10 - 4 * attemptParams.Δ ≤ 45) := by
  decide


-- Both raise rows can use all of the frozen budget at the terminal deadline.
-- The gate-service carrier needs five more delta units; terminal promotion uses this budget.
example (k : AttemptKey) (htask : k.task = .raise) (hphase : k.phase = .contest) :
    (45 : Time) + 2 * P attemptParams + Γ attemptParams 10 - 9 * attemptParams.Δ =
        attemptBudget attemptParams 10 k ∧
      (45 : Time) + 2 * P attemptParams + Γ attemptParams 10 - 4 * attemptParams.Δ =
        attemptBudget attemptParams 10 k + 5 := by
  rw [healing_attempt_raise_contest_budget attemptParams 10 k htask hphase]
  decide

example (k : AttemptKey) (htask : k.task = .raise) (hphase : k.phase ≠ .contest) :
    (85 : Time) + 2 * P attemptParams + Γ attemptParams 10 - 9 * attemptParams.Δ =
        attemptBudget attemptParams 10 k ∧
      (85 : Time) + 2 * P attemptParams + Γ attemptParams 10 - 4 * attemptParams.Δ =
        attemptBudget attemptParams 10 k + 5 := by
  rw [healing_attempt_raise_other_budget attemptParams 10 k htask hphase]
  decide

-- GUP r2: G = 10, delta = 1 is allowed without alignment.
-- Its raw recurrence endpoint now precedes the rounded terminal deadline.
example :
    (3 : Time) * P attemptParams + 2 * P attemptParams - 4 * attemptParams.Δ + 10 = 66 ∧
      attemptParams.actionTime 3 + 2 * P attemptParams + Γ attemptParams 10 -
        9 * attemptParams.Δ = 69 := by
  decide

-- P1 arithmetic: the shifted endpoint is within the terminal deadline in all four classes.
-- Round-up excludes the old proposal at a for positive remainders as well.
example : Γ attemptParams 5 = 8 := by decide

example : (8 : Time) % 4 = 0 ∧ Γ attemptParams 8 = 8 ∧
    (56 : Time) + Γ attemptParams 8 - 8 = 56 ∧
    (56 : Time) + Γ attemptParams 8 ≤
      attemptParams.actionTime 3 + 2 * P attemptParams + Γ attemptParams 8 -
        9 * attemptParams.Δ := by decide

example : (9 : Time) % 4 = 1 ∧ Γ attemptParams 9 = 12 ∧
    (56 : Time) + Γ attemptParams 9 - 9 = 59 ∧
    (56 : Time) + Γ attemptParams 9 ≤
      attemptParams.actionTime 3 + 2 * P attemptParams + Γ attemptParams 9 -
        9 * attemptParams.Δ := by decide

example : (10 : Time) % 4 = 2 ∧ Γ attemptParams 10 = 12 ∧
    (56 : Time) + Γ attemptParams 10 - 10 = 58 ∧
    (56 : Time) + Γ attemptParams 10 ≤
      attemptParams.actionTime 3 + 2 * P attemptParams + Γ attemptParams 10 -
        9 * attemptParams.Δ := by decide

example : (11 : Time) % 4 = 3 ∧ Γ attemptParams 11 = 12 ∧
    (56 : Time) + Γ attemptParams 11 - 11 = 57 ∧
    (56 : Time) + Γ attemptParams 11 ≤
      attemptParams.actionTime 3 + 2 * P attemptParams + Γ attemptParams 11 -
        9 * attemptParams.Δ := by decide

example : SA.proposalTime attemptParams.toParams 14 =
    (3 : Time) * P attemptParams + 2 * P attemptParams - 4 * attemptParams.Δ ∧
    SA.proposalTime attemptParams.toParams 14 < attemptParams.actionTime 5 ∧
    ¬ ((9 : Nat) + attemptParams.δt ≤ 14) := by decide

example : ∀ G ∈ ([9, 10, 11] : List Time),
    ¬ ((56 : Time) + Γ attemptParams G - G < SA.proposalTime attemptParams.toParams 14) ∧
    (56 : Time) + Γ attemptParams G - G < SA.proposalTime attemptParams.toParams 15 ∧
    SA.proposalTime attemptParams.toParams 15 ≤ (56 : Time) + Γ attemptParams G := by decide

-- Class 0 excludes t_s = a and allows the next grid slot, which is mature.
example : ¬ ((56 : Time) + Γ attemptParams 8 - 8 < SA.proposalTime attemptParams.toParams 14) ∧
    (9 : Nat) + attemptParams.δt ≤ 15 := by decide

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

-- A strictly earlier effective event ends the attempt without later service.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G : Time)
    {k : AttemptKey} {ev ev' : V2.Event V (Obj p)} {j : Nat}
    (hstart : rho.events[k.start]? = some ev) (hj : k.start < j)
    (hnext : rho.events[j]? = some ev')
    (htime : ev'.time < ev.time + attemptBudget p G k)
    (heff : EffectiveEvent p c E rho j) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) :=
  healing_attempt_ends_of_event E rho hstart hj hnext htime.le heff

-- An event at the budget endpoint is included.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G : Time)
    {k : AttemptKey} {ev ev' : V2.Event V (Obj p)} {j : Nat}
    (hstart : rho.events[k.start]? = some ev) (hj : k.start < j)
    (hnext : rho.events[j]? = some ev')
    (htime : ev'.time = ev.time + attemptBudget p G k)
    (heff : EffectiveEvent p c E rho j) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) :=
  healing_attempt_ends_of_event E rho hstart hj hnext htime.le heff

-- One matching row is enough; all-reader common entry is not a premise.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G : Time)
    {k : AttemptKey} {ev ev' : V2.Event V (Obj p)} {j : Nat} {y : V} {r : Nat}
    {a : RowWire p.n} {e : BlockId}
    (hstart : rho.events[k.start]? = some ev) (hj : k.start < j)
    (hnext : rho.events[j]? = some ev') (htime : ev'.time ≤ ev.time + attemptBudget p G k)
    (htask : k.task = .firstRow) (hrow : HonestRowAt p c E rho j y r a)
    (hnamed : namedEntry a.payload.height_pair = some (k.frontier, e)) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) :=
  healing_attempt_ends_of_row E rho hstart hj hnext htime htask hrow hnamed

-- B21: a valid attempt at frontier one must use the inclusive-cut start.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hnr : V2.D.NoRestart rho) {k : AttemptKey}
    (hvalid : AttemptValid p c E rho k) (hk : k.frontier = 1) :
    ∃ ev rG, rho.events[k.start]? = some ev ∧ recoveryStart p E ≤ ev.time ∧
      recoveryStart p E ≤ p.actionTime rG ∧
      (∀ r, recoveryStart p E ≤ p.actionTime r → rG ≤ r) ∧
      ev.time = p.actionTime (rG + 2) ∧
      timeIdx rho (p.actionTime (rG + 2)) = k.start + 1 := by
  have hf : frontierAtIdx p c E rho (k.start + 1) = 1 := by
    obtain ⟨_, _, _, _, hf, _⟩ := hvalid
    exact hf.symm.trans hk
  exact healing_attempt_inclusive_start E rho hvalid (boot_not_effective_one p c E rho hnr hf)

-- B21 also fixes the live phase at genesis top J.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {i : Nat} {x : V}
    (hx : x ∈ rho.honest) (hf : frontierAtIdx p c E rho i = 1) :
    (R_at p c E rho i x).J = .genesis ∧ (R_at p c E rho i x).contest = false := by
  have h := boot_height_one p c E rho hx hf
  exact ⟨h.2.2.1, h.2.2.2.1⟩

-- The conditional wrapper still accepts four row facts; the complete lane proves each row.
example (p : Params) (G ΔF : Time)
    (raise_contest : p.δt = 2 * p.R →
      ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
        (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
        HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
        ∀ k ev, AttemptValid p c E rho k → rho.events[k.start]? = some ev →
          ev.time + attemptBudget p G k ≤ rho.horizon →
          k.task = .raise → k.phase = .contest →
          AttemptEndsBy p c E rho k (attemptBudget p G k))
    (raise_other : p.δt = 2 * p.R →
      ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
        (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
        HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
        ∀ k ev, AttemptValid p c E rho k → rho.events[k.start]? = some ev →
          ev.time + attemptBudget p G k ≤ rho.horizon →
          k.task = .raise → k.phase ≠ .contest →
          AttemptEndsBy p c E rho k (attemptBudget p G k))
    (firstRow_contest : p.δt = 2 * p.R →
      ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
        (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
        HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
        ∀ k ev, AttemptValid p c E rho k → rho.events[k.start]? = some ev →
          ev.time + attemptBudget p G k ≤ rho.horizon →
          k.task = .firstRow → k.phase = .contest →
          AttemptEndsBy p c E rho k (attemptBudget p G k))
    (firstRow_other : p.δt = 2 * p.R →
      ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
        (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
        HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
        ∀ k ev, AttemptValid p c E rho k → rho.events[k.start]? = some ev →
          ev.time + attemptBudget p G k ≤ rho.horizon →
          k.task = .firstRow → k.phase ≠ .contest →
          AttemptEndsBy p c E rho k (attemptBudget p G k))
    : ProgressAttemptStatement p G ΔF :=
  healing_progressAttempt_of p G ΔF raise_contest raise_other firstRow_contest firstRow_other

-- The non-effective cut start in the raise / contest row.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (mono : RMonoAll p c E rho)
    (heldServices : ∀ i (ev : V2.Event V (Obj p)) m,
      rho.events[i]? = some ev → recoveryStart p E ≤ ev.time → 1 ≤ m →
      frontierAtIdx p c E rho (i + 1) = m → ev.time + p.Δ ≤ rho.horizon →
      PhaseWitnessReceiptScope E rho (i + 1) m (ev.time + p.Δ))
    (crossing : RXing p c E rho) [Fintype V] {G ΔF : Time}
    (hrec : HealingSet p c E rho G ΔF) {k : AttemptKey}
    {ev : V2.Event V (Obj p)} {v : Time}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hne : ¬ EffectiveEvent p c E rho k.start)
    (hu : ev.time + 3 * p.Δ ≤ v) (hv : v ≤ rho.horizon)
    (hquiet : ∀ j, k.start < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j)
    (htask : k.task = .raise) (hphase : k.phase = .contest) :
    ∃ rG J,
      ev.time = p.actionTime (rG + 2) ∧
      timeIdx rho (p.actionTime (rG + 2)) = k.start + 1 ∧
      let root := match k.phase with | .gap => none | .topJ => some J | .contest => none
      let contested := match k.phase with | .gap => false | .topJ => false | .contest => true
      PhaseInterval p c E rho (ev.time + 3 * p.Δ) v k.frontier root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
        SA.voteTime p.toParams s ≤ v →
        postClock E rho y (SA.voteTime p.toParams s) = some nd →
        SettledPhaseFrame p nd.st k.frontier root contested) := by
  obtain ⟨ev0, rG, hi0, _, _, _, ht, hcut⟩ :=
    healing_attempt_inclusive_start E rho hvalid hne
  have he : ev0 = ev := Option.some.inj (hi0.symm.trans hstart)
  subst ev0
  obtain ⟨J, hsettled⟩ := healing_attempt_raise_contest_settle p c E rho mono
    (fun t ht => healing_ready_read_cutoff (p := p) (t := t) E ht) heldServices
    crossing hrec
    hvalid hstart hu hv hquiet htask hphase
  exact ⟨rG, J, ht, hcut, hsettled⟩

-- The non-effective cut start in the raise / other row.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (mono : RMonoAll p c E rho)
    (heldServices : ∀ i (ev : V2.Event V (Obj p)) m,
      rho.events[i]? = some ev → recoveryStart p E ≤ ev.time → 1 ≤ m →
      frontierAtIdx p c E rho (i + 1) = m → ev.time + p.Δ ≤ rho.horizon →
      PhaseWitnessReceiptScope E rho (i + 1) m (ev.time + p.Δ))
    (crossing : RXing p c E rho) [Fintype V] {G ΔF : Time}
    (hrec : HealingSet p c E rho G ΔF) {k : AttemptKey}
    {ev : V2.Event V (Obj p)} {v : Time}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hne : ¬ EffectiveEvent p c E rho k.start)
    (hu : ev.time + 3 * p.Δ ≤ v) (hv : v ≤ rho.horizon)
    (hquiet : ∀ j, k.start < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j)
    (htask : k.task = .raise) (hphase : k.phase ≠ .contest) :
    ∃ rG J,
      ev.time = p.actionTime (rG + 2) ∧
      timeIdx rho (p.actionTime (rG + 2)) = k.start + 1 ∧
      let root := match k.phase with | .gap => none | .topJ => some J | .contest => none
      let contested := match k.phase with | .gap => false | .topJ => false | .contest => true
      PhaseInterval p c E rho (ev.time + 3 * p.Δ) v k.frontier root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
        SA.voteTime p.toParams s ≤ v →
        postClock E rho y (SA.voteTime p.toParams s) = some nd →
        SettledPhaseFrame p nd.st k.frontier root contested) := by
  obtain ⟨ev0, rG, hi0, _, _, _, ht, hcut⟩ :=
    healing_attempt_inclusive_start E rho hvalid hne
  have he : ev0 = ev := Option.some.inj (hi0.symm.trans hstart)
  subst ev0
  obtain ⟨J, hsettled⟩ := healing_attempt_raise_other_settle p c E rho mono
    (fun t ht => healing_ready_read_cutoff (p := p) (t := t) E ht) heldServices
    crossing hrec
    hvalid hstart hu hv hquiet htask hphase
  exact ⟨rG, J, ht, hcut, hsettled⟩

-- The non-effective cut start in the firstRow / contest row.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (mono : RMonoAll p c E rho)
    (heldServices : ∀ i (ev : V2.Event V (Obj p)) m,
      rho.events[i]? = some ev → recoveryStart p E ≤ ev.time → 1 ≤ m →
      frontierAtIdx p c E rho (i + 1) = m → ev.time + p.Δ ≤ rho.horizon →
      PhaseWitnessReceiptScope E rho (i + 1) m (ev.time + p.Δ))
    (crossing : RXing p c E rho) [Fintype V] {G ΔF : Time}
    (hrec : HealingSet p c E rho G ΔF) {k : AttemptKey}
    {ev : V2.Event V (Obj p)} {v : Time}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hne : ¬ EffectiveEvent p c E rho k.start)
    (hu : ev.time + 3 * p.Δ ≤ v) (hv : v ≤ rho.horizon)
    (hquiet : ∀ j, k.start < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j)
    (htask : k.task = .firstRow) (hphase : k.phase = .contest) :
    ∃ rG J,
      ev.time = p.actionTime (rG + 2) ∧
      timeIdx rho (p.actionTime (rG + 2)) = k.start + 1 ∧
      let root := match k.phase with | .gap => none | .topJ => some J | .contest => none
      let contested := match k.phase with | .gap => false | .topJ => false | .contest => true
      PhaseInterval p c E rho (ev.time + 3 * p.Δ) v k.frontier root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
        SA.voteTime p.toParams s ≤ v →
        postClock E rho y (SA.voteTime p.toParams s) = some nd →
        SettledPhaseFrame p nd.st k.frontier root contested) := by
  obtain ⟨ev0, rG, hi0, _, _, _, ht, hcut⟩ :=
    healing_attempt_inclusive_start E rho hvalid hne
  have he : ev0 = ev := Option.some.inj (hi0.symm.trans hstart)
  subst ev0
  obtain ⟨J, hsettled⟩ := healing_attempt_firstRow_contest_settle p c E rho mono
    (fun t ht => healing_ready_read_cutoff (p := p) (t := t) E ht) heldServices
    crossing hrec
    hvalid hstart hu hv hquiet htask hphase
  exact ⟨rG, J, ht, hcut, hsettled⟩

-- The non-effective cut start in the firstRow / other row.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (mono : RMonoAll p c E rho)
    (heldServices : ∀ i (ev : V2.Event V (Obj p)) m,
      rho.events[i]? = some ev → recoveryStart p E ≤ ev.time → 1 ≤ m →
      frontierAtIdx p c E rho (i + 1) = m → ev.time + p.Δ ≤ rho.horizon →
      PhaseWitnessReceiptScope E rho (i + 1) m (ev.time + p.Δ))
    (crossing : RXing p c E rho) [Fintype V] {G ΔF : Time}
    (hrec : HealingSet p c E rho G ΔF) {k : AttemptKey}
    {ev : V2.Event V (Obj p)} {v : Time}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hne : ¬ EffectiveEvent p c E rho k.start)
    (hu : ev.time + 3 * p.Δ ≤ v) (hv : v ≤ rho.horizon)
    (hquiet : ∀ j, k.start < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j)
    (htask : k.task = .firstRow) (hphase : k.phase ≠ .contest) :
    ∃ rG J,
      ev.time = p.actionTime (rG + 2) ∧
      timeIdx rho (p.actionTime (rG + 2)) = k.start + 1 ∧
      let root := match k.phase with | .gap => none | .topJ => some J | .contest => none
      let contested := match k.phase with | .gap => false | .topJ => false | .contest => true
      PhaseInterval p c E rho (ev.time + 3 * p.Δ) v k.frontier root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
        SA.voteTime p.toParams s ≤ v →
        postClock E rho y (SA.voteTime p.toParams s) = some nd →
        SettledPhaseFrame p nd.st k.frontier root contested) := by
  obtain ⟨ev0, rG, hi0, _, _, _, ht, hcut⟩ :=
    healing_attempt_inclusive_start E rho hvalid hne
  have he : ev0 = ev := Option.some.inj (hi0.symm.trans hstart)
  subst ev0
  obtain ⟨J, hsettled⟩ := healing_attempt_firstRow_other_settle p c E rho mono
    (fun t ht => healing_ready_read_cutoff (p := p) (t := t) E ht) heldServices
    crossing hrec
    hvalid hstart hu hv hquiet htask hphase
  exact ⟨rG, J, ht, hcut, hsettled⟩

section CompleteRows
variable [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (qc : RQCOrigin p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉
          @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
            (actView pre) w C)
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))



-- Complete contest row at either start arm, with no row-result premise.
example {k : AttemptKey} {ev : V2.Event V (Obj p)}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hhor : ev.time + attemptBudget p G k ≤ rho.horizon)
    (htask : k.task = .firstRow) (hphase : k.phase = .contest) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) :=
  healing_attempt_firstRow_contest E rho hrec mono crossing qc
    (healing_repair_service_scopes_recovery E rho hrec mono)
    (healing_opening_service_scopes_recovery E rho hrec mono) writes rowCoverage
    hvalid hstart hhor htask hphase

variable
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))


-- Complete gap and topJ row at either start arm, with the promotion INLINE facts.
example {k : AttemptKey} {ev : V2.Event V (Obj p)}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hhor : ev.time + attemptBudget p G k ≤ rho.horizon)
    (htask : k.task = .firstRow) (hphase : k.phase ≠ .contest) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) :=
  healing_attempt_firstRow_other E rho hrec mono crossing qc
    (healing_repair_service_scopes_recovery E rho hrec mono)
    (healing_opening_service_scopes_recovery E rho hrec mono) writes rowCoverage hδ hbound
    rowsReceipt progressCoverage hfold faultQ honestQuorum hvalid hstart hhor htask hphase

-- Apply the complete raise / contest row at either AttemptValid start arm.
example {k : AttemptKey} {ev : V2.Event V (Obj p)}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hhor : ev.time + attemptBudget p G k ≤ rho.horizon)
    (htask : k.task = .raise) (hphase : k.phase = .contest) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) :=
  healing_attempt_raise_contest E rho hrec mono crossing qc
    (healing_repair_service_scopes_recovery E rho hrec mono)
    (healing_opening_service_scopes_recovery E rho hrec mono) writes rowCoverage hδ hbound
    rowsReceipt progressCoverage hfold faultQ honestQuorum hvalid hstart hhor htask hphase

-- Apply the complete raise / gap or topJ row at either start arm.
example {k : AttemptKey} {ev : V2.Event V (Obj p)}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hhor : ev.time + attemptBudget p G k ≤ rho.horizon)
    (htask : k.task = .raise) (hphase : k.phase ≠ .contest) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) :=
  healing_attempt_raise_other E rho hrec mono crossing qc
    (healing_repair_service_scopes_recovery E rho hrec mono)
    (healing_opening_service_scopes_recovery E rho hrec mono) writes rowCoverage hδ hbound
    rowsReceipt progressCoverage hfold faultQ honestQuorum hvalid hstart hhor htask hphase

-- Apply the lane assembly without a row-result premise.
example {k : AttemptKey} {ev : V2.Event V (Obj p)}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hhor : ev.time + attemptBudget p G k ≤ rho.horizon) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) :=
  healing_progressAttempt E rho hrec mono crossing qc
    (healing_repair_service_scopes_recovery E rho hrec mono)
    (healing_opening_service_scopes_recovery E rho hrec mono) writes rowCoverage hδ hbound
    rowsReceipt progressCoverage hfold faultQ honestQuorum hvalid hstart hhor

end CompleteRows

-- Both required gaps are aligned for every parameter record.
example (p : Params) : 4 * p.Δ ∣ 8 * p.Δ ∧ Γ p (8 * p.Δ) = 8 * p.Δ := by
  have hd : 4 * p.Δ ∣ 8 * p.Δ := ⟨2, by ring⟩
  exact ⟨hd, fgsa_gamma_eq_of_dvd p hd⟩

example (p : Params) : 4 * p.Δ ∣ 12 * p.Δ ∧ Γ p (12 * p.Δ) = 12 * p.Δ := by
  have hd : 4 * p.Δ ∣ 12 * p.Δ := ⟨3, by ring⟩
  exact ⟨hd, fgsa_gamma_eq_of_dvd p hd⟩

-- Check all four frozen budgets at G = 8Δ and G = 12Δ.
example (k : AttemptKey) (htask : k.task = .raise) (hphase : k.phase = .contest) :
    attemptBudget attemptParams 8 k = 64 ∧ attemptBudget attemptParams 12 k = 72 := by
  rw [healing_attempt_raise_contest_budget attemptParams 8 k htask hphase,
    healing_attempt_raise_contest_budget attemptParams 12 k htask hphase]
  decide

example (k : AttemptKey) (htask : k.task = .raise) (hphase : k.phase ≠ .contest) :
    attemptBudget attemptParams 8 k = 100 ∧ attemptBudget attemptParams 12 k = 112 := by
  rw [healing_attempt_raise_other_budget attemptParams 8 k htask hphase,
    healing_attempt_raise_other_budget attemptParams 12 k htask hphase]
  decide

example (k : AttemptKey) (htask : k.task = .firstRow) (hphase : k.phase = .contest) :
    attemptBudget attemptParams 8 k = 41 ∧ attemptBudget attemptParams 12 k = 45 := by
  rw [healing_attempt_firstRow_contest_budget attemptParams 8 k htask hphase,
    healing_attempt_firstRow_contest_budget attemptParams 12 k htask hphase]
  decide

example (k : AttemptKey) (htask : k.task = .firstRow) (hphase : k.phase ≠ .contest) :
    attemptBudget attemptParams 8 k = 77 ∧ attemptBudget attemptParams 12 k = 85 := by
  rw [healing_attempt_firstRow_other_budget attemptParams 8 k htask hphase,
    healing_attempt_firstRow_other_budget attemptParams 12 k htask hphase]
  decide

-- Blueprint 21 H.10; plan item S5 PA-ASSEMBLY T; DC: SAME frozen inputs only.
example [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (rows : ProgressAttemptRows p G ΔF)
    (hδ : p.δt = 2 * p.R) (hset : HealingSet p c E rho G ΔF)
    (hbound : LivenessBoundW p ΔF) (k : AttemptKey) (ev : V2.Event V (Obj p))
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hhor : ev.time + attemptBudget p G k ≤ rho.horizon) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) :=
  healing_progressAttemptStatement p G ΔF rows hδ c E rho hset hbound k ev hvalid hstart hhor

end AvailableChain.FGSA.Run.Tests.HealingAttempt
end
