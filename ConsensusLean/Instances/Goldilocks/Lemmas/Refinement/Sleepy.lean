module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Run
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Sleepy
public import ConsensusLean.Spec.Shape.Run

public section

/-! # Finite sleepy transport obligations

OPEN skeleton, owned by the Refinement/Accepted integration. CLAIMS R.1/R.2 prove node
safety/inclusion/growth; they do not prove these finite engine bridges. No whole-run
`SleepyRun` or `HealthyRun` is inferred from a finite engine horizon.

`SleepySafePrefix` requires `SyncRun 0 (b - Δ)`: this still quantifies receiver calls after
`b`, including later wakes. `SyncUntil b` alone cannot supply it. The finite consumers below
instead use `SyncBefore`, which bounds the recipient's deadline, and bound all observations
by `b`. Their proofs need a dependency-local version of R.1/R.2, not direct application of
`IncludeSleepy`/`GrowSleepy` (both currently require whole-run `SleepyRun`).

The missing network supplier is named as a proposition, NOT asserted as a theorem. Current
`Setup.params` has Δp = Δe; inclusive engine receipt does not imply strict node processing
before the same deadline. The pending Δp = Δe + 1 repair must also reconcile catch-up,
slot grid, recurrence and latency coefficients. No impossible strict-delay premise is used.
The raw-genesis/canonical collision bridge is separately owned by the encoding integration.
-/

namespace Consensus.Goldilocks.Refinement

open Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- Engine readiness bridge. Map honesty by the key equivalence
and awake intervals by canonical simulation. Both ends are inside the finite horizon; the
catch-up is the NODE duration, not silently `18 * E.Δ`. R.1 defines the same closed interval,
but supplies no engine proof. -/
theorem sleepy_ready (_hv : rho.ExecutionValid) {v : V} {t : Time}
    (_ht : 0 ≤ t) (hth : t ≤ rho.horizon)
    (hr : rho.point.Ready (Regimes.catchUp (S.params (pubOf E) hn)) v t) :
    Regimes.ReadyAt (simTrace S rho hn) (honestKeys S rho)
      (Regimes.catchUp (S.params (pubOf E) hn)) (rho.ownKey v) t := by
  have hkey : rho.key (rho.ownKey v) = v := rho.key.apply_symm_apply v
  constructor
  · change rho.key (rho.ownKey v) ∈ rho.honest
    rw [hkey]
    exact hr.1
  · intro τ hτ hτt
    rw [simTrace_awake_iff, awakeAt_iff, hkey]
    exact ⟨hr.2 τ hτ hτt, (le_max_left _ _).trans hτ, hτt.trans hth⟩

/-- OPEN quorum bridge (owner: Refinement). Half-ready means faulty < ready; transport
counts through the key equivalence and use ready-implies-joined at each slot point.
Only points through `b` are claimed, including slot zero. Depends on `sleepy_ready` and
the node readiness/join lemma, not on synchrony or whole-run participation. -/
theorem sleepy_faultBound (hv : rho.ExecutionValid) {b : Time}
    (hb : b ≤ rho.horizon)
    (hhalf : rho.point.SleepyOn (1 / 2) (Regimes.catchUp (S.params (pubOf E) hn)) 0 b) :
    ∀ s : Nat, ∀ d ∈ ({0, (S.params (pubOf E) hn).Δ,
      2 * (S.params (pubOf E) hn).Δ} : Set Time), (S.params (pubOf E) hn).ts s + d ≤ b →
      (simTrace S rho hn).FaultBound (honestKeys S rho) ((S.params (pubOf E) hn).ts s + d) := by
  sorry

/-- OPEN missing service supplier (owner: timing/encoding integration), not a proved or
assumed fact of Accepted. A proposed interface after the timing repair: finite engine
deadline service yields node deadline-bounded service, including acceptance relay.
Receipt alone does not prove acceptance relay, and Δp = Δe currently lacks strict slack.
This definition records the missing obligation without adding a vacuous `hdelay` premise.
The repaired supplier may require a larger engine service window, which must be propagated
to the consumer and contract rather than assumed away. -/
def SleepyServiceSupplier : Prop :=
  ∀ b, 0 ≤ b → b ≤ rho.horizon → rho.ExecutionValid →
    rho.log.SyncUntil rho.point b →
    (simTrace S rho hn).SyncBefore (honestKeys S rho) (S.params (pubOf E) hn).Δ b

private theorem event_before_endCut (hv : rho.ExecutionValid) {t : Time} (ht : 0 ≤ t)
    {i : Nat} {e : Model.Event V (Model.protoOf (compiled (family S)) E).Object}
    (he : rho.events[i]? = some e) :
    i < (chainTrace rho).endCut t ↔ e.time ≤ t := by
  classical
  let n := (chainTrace rho).endCut t
  have hnle : n ≤ rho.events.length := Nat.findGreatest_le _
  have hnTime : rho.cutTime n ≤ t :=
    Nat.findGreatest_spec (P := fun i => rho.cutTime i ≤ t)
      (Nat.zero_le _) (by simpa [Model.Run.cutTime] using ht)
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  constructor
  · intro hin
    cases hn : n with
    | zero => omega
    | succ k =>
      have hk : k < rho.events.length := by omega
      let f := rho.events[k]
      have hf : rho.events[k]? = some f := List.getElem?_eq_getElem hk
      have hft : f.time ≤ t := by simpa [hn, Model.Run.cutTime, hf] using hnTime
      have hik : i ≤ k := by omega
      rcases hik.lt_or_eq with hik | rfl
      · have horder := keyLe_of_lt S rho hv he hf hik
        have hef : e.time ≤ f.time := by
          rcases horder with h | ⟨h, _⟩
          · exact h.le
          · exact h.le
        exact hef.trans hft
      · rw [he] at hf
        exact (Option.some.inj hf) ▸ hft
  · intro het
    have hle : i + 1 ≤ Nat.findGreatest (fun k => rho.cutTime k ≤ t) rho.events.length :=
      Nat.le_findGreatest (by omega)
      (by simpa [Model.Run.cutTime, he] using het)
    exact hle

/-- End-of-time cut bridge. The canonical cut map covers every
engine event at `t` before advancing to a later node time, including the terminal filler
cut. A ready node has a tick at `t`, so its last clock is `t`, not the next node cut's time.
This supplies the exact state/clock read needed by finite R.2. No paper proof of encoding. -/
theorem sleepy_read_cut (hv : rho.ExecutionValid) {v : V} {t : Time}
    (ht : 0 ≤ t) (hth : t ≤ rho.horizon)
    (hr : rho.point.Ready (Regimes.catchUp (S.params (pubOf E) hn)) v t) :
    Regimes.CutAfter (simTrace S rho hn) (cutMap S rho hn ((chainTrace rho).endCut t)) t ∧
      Regimes.Boundary (simTrace S rho hn) (rho.ownKey v)
        (cutMap S rho hn ((chainTrace rho).endCut t)) ∧
      (stateAt S rho hn v ((chainTrace rho).endCut t)).now = t := by
  classical
  let n := (chainTrace rho).endCut t
  let j := cutMap S rho hn n
  have hnle : n ≤ rho.events.length := Nat.findGreatest_le _
  have hprev : ∀ k < j, (simTrace S rho hn).time k ≤ t := by
    intro k hk
    have hlen : k < (allCuts S rho hn).length := by
      rw [length_allCuts]
      exact hk.trans_le (cutMap_mono S rho hn hnle)
    have hl : (simTrace S rho hn).label k ≠ none := by
      rw [simTrace_label, List.getElem?_eq_getElem hlen]
      simp
    obtain ⟨_, i, e, _, he, hi, _, _, _, htime, _⟩ := simTrace_cut S rho hn hl
    have hin : i < n := by
      by_contra h
      have := cutMap_mono S rho hn (Nat.le_of_not_gt h)
      omega
    rw [htime]
    exact (event_before_endCut S rho hv ht he).mp hin
  have hnext : t < (simTrace S rho hn).time j := by
    cases hrj : (allCuts S rho hn)[j]? with
    | none =>
      rw [(simTrace_of_getElem?_none S rho hn hrj).2]
      linarith
    | some r =>
      have hl : (simTrace S rho hn).label j ≠ none := by
        rw [simTrace_label, hrj]; simp
      obtain ⟨_, i, e, _, he, _, hi, _, _, htime, _⟩ := simTrace_cut S rho hn hl
      have hni : n ≤ i := by
        by_contra h
        have := cutMap_mono S rho hn (show i + 1 ≤ n by omega)
        omega
      rw [htime]
      exact lt_of_not_ge fun het => by
        have := (event_before_endCut S rho hv ht he).mpr het
        omega
  refine ⟨⟨hprev, hnext⟩, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    have hy : rho.ownKey v ∈ honestKeys S rho := by
      change rho.key (rho.ownKey v) ∈ rho.honest
      rw [show rho.key (rho.ownKey v) = v from rho.key.apply_symm_apply v]
      exact hr.1
    obtain ⟨j0, e, hg, hle, hlt⟩ := simTrace_grouped S rho hn hv _ hy j c hc
    have heq : j0 = j := by
      by_contra h
      have h0 := (hg.2.1 0 (by omega)).2.1
      simp only [Nat.add_zero] at h0
      have := hprev j0 (lt_of_le_of_ne hle h)
      rw [h0] at this
      exact (not_lt_of_ge this) hnext
    subst j0
    simpa using (hg.2.1 0 (by omega)).2.2.2.1
  · have hw : E.awake v t = true := hr.2 t (by
      apply max_le ht
      unfold Regimes.catchUp
      have := (S.params (pubOf E) hn).toParams.hΔ
      linarith) le_rfl
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hv.tick_total v hr.1 t ht hth hw)
    have hin : i < n := (event_before_endCut S rho hv ht hi).mpr le_rfl
    rw [now_eq_lastClock S rho hn hv]
    apply lastClock_of_between S rho v t i (Or.inl hi) n hin
    intro k hik hkn e he
    have hlo := keyLe_of_lt S rho hv hi he hik
    have hhi := (event_before_endCut S rho hv ht he).mp hkn
    rcases hlo with hlo | ⟨hlo, _⟩
    · exact le_antisymm hhi hlo.le
    · exact hlo.symm

/-- OPEN finite R.1 consumer (owner: Regimes/Refinement). Localize the R.1 induction to
cuts observed through `b`; all network invocations must have recipient deadlines ≤ b.
Depends on the finite quorum supplier and `SyncBefore`, NOT a claimed conversion to
`SyncRun 0 (b-Δ)` or infinite `SleepyRun`. Prove this locality before using the consumer
in Accepted. Canonical execution uses `runProposer S rho hn`, selected by `rho.sel`. -/
theorem sleepy_safe_finite (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn)) {b : Time}
    (hb0 : 0 ≤ b) (hbh : b ≤ rho.horizon)
    (hsync : (simTrace S rho hn).SyncBefore (honestKeys S rho) (S.params (pubOf E) hn).Δ b)
    (hf : ∀ s : Nat, ∀ d ∈ ({0, (S.params (pubOf E) hn).Δ,
      2 * (S.params (pubOf E) hn).Δ} : Set Time), (S.params (pubOf E) hn).ts s + d ≤ b →
      (simTrace S rho hn).FaultBound (honestKeys S rho) ((S.params (pubOf E) hn).ts s + d)) :
    Regimes.ReadySafeOn (simTrace S rho hn) (honestKeys S rho)
      (Regimes.catchUp (S.params (pubOf E) hn)) 0 b := by
  sorry

/-- OPEN finite R.2 inclusion consumer (owner: Regimes/Refinement). Re-run A1.7/F.4 only
through the observation `t ≤ b`: the producer at `τ` is in the horizon, and its full `6Δ`
margin ends before the observation. Every service dependency must fit `SyncBefore b`.
`IncludeSleepy` is the paper source, not an applicable finite theorem. No future participation
or whole-run extension is assumed. Uses the canonical run with `runProposer S rho hn`. -/
theorem sleepy_include_finite (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn)) {b : Time}
    (hb0 : 0 ≤ b) (hbh : b ≤ rho.horizon)
    (hsync : (simTrace S rho hn).SyncBefore (honestKeys S rho) (S.params (pubOf E) hn).Δ b)
    (hf : ∀ s : Nat, ∀ d ∈ ({0, (S.params (pubOf E) hn).Δ,
      2 * (S.params (pubOf E) hn).Δ} : Set Time), (S.params (pubOf E) hn).ts s + d ≤ b →
      (simTrace S rho hn).FaultBound (honestKeys S rho) ((S.params (pubOf E) hn).ts s + d))
    {τ t : Time} {P : SA.Blk (Fintype.card V) (List (FG.Att (Fintype.card V)))}
    (hτ : 0 ≤ τ) (hτb : τ ≤ b)
    (hP : Regimes.ReadyProposalAt (simTrace S rho hn) (honestKeys S rho)
      (Regimes.catchUp (S.params (pubOf E) hn)) τ P)
    (hmargin : τ + 6 * (S.params (pubOf E) hn).Δ ≤ t) (htb : t ≤ b)
    {y : Fin (Fintype.card V)} {j : Nat}
    (hy : Regimes.ReadyAt (simTrace S rho hn) (honestKeys S rho)
      (Regimes.catchUp (S.params (pubOf E) hn)) y t)
    (hj : Regimes.CutAfter (simTrace S rho hn) j t) :
    Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho)) P
      (Regimes.readAfter (simTrace S rho hn) y j t) := by
  sorry

/-- OPEN finite R.2 growth consumer (owner: Regimes/Refinement). Select a ready scheduled
producer in `(t, t+4kΔ]`, leaving `6Δ` before `b = t+(4k+6)Δ`. Apply finite inclusion and
finite safety; slot bounds exclude the new block from every earlier ready read. The explicit
upper producer bound is needed to transport release/proposal evidence inside the horizon.
The recurrence is for `runProposer S rho hn` (from `rho.sel`), never a setup-fixed schedule.
The engine pattern-to-recurrence and duration adapters remain separate OPEN suppliers. -/
theorem sleepy_grow_finite (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn)) {t b : Time} {k : Nat}
    (ht : 0 ≤ t) (hk : 1 ≤ k) (hb : b = t + (4 * k + 6) * (S.params (pubOf E) hn).Δ)
    (hbh : b ≤ rho.horizon)
    (hsync : (simTrace S rho hn).SyncBefore (honestKeys S rho) (S.params (pubOf E) hn).Δ b)
    (hf : ∀ s : Nat, ∀ d ∈ ({0, (S.params (pubOf E) hn).Δ,
      2 * (S.params (pubOf E) hn).Δ} : Set Time), (S.params (pubOf E) hn).ts s + d ≤ b →
      (simTrace S rho hn).FaultBound (honestKeys S rho) ((S.params (pubOf E) hn).ts s + d))
    (hrec : Regimes.ProposerRecurrence (simTrace S rho hn) (honestKeys S rho)
      (runProposer S rho hn) (Regimes.catchUp (S.params (pubOf E) hn)) k 0 b)
    (hreader : ∃ v, Regimes.ReadyAt (simTrace S rho hn) (honestKeys S rho)
      (Regimes.catchUp (S.params (pubOf E) hn)) v b) :
    ∃ τ P, t < τ ∧ τ + 6 * (S.params (pubOf E) hn).Δ ≤ b ∧
      Regimes.ReadyProposalAt (simTrace S rho hn) (honestKeys S rho)
        (Regimes.catchUp (S.params (pubOf E) hn)) τ P ∧
      (∀ y j, Regimes.ReadyAt (simTrace S rho hn) (honestKeys S rho)
        (Regimes.catchUp (S.params (pubOf E) hn)) y b →
        Regimes.CutAfter (simTrace S rho hn) j b →
        Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho)) P
          (Regimes.readAfter (simTrace S rho hn) y j b)) ∧
      ∀ x jx, Regimes.ReadyAt (simTrace S rho hn) (honestKeys S rho)
        (Regimes.catchUp (S.params (pubOf E) hn)) x t →
        Regimes.CutAfter (simTrace S rho hn) jx t →
        ¬ Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho)) P
          (Regimes.readAfter (simTrace S rho hn) x jx t) ∧
        ∀ y j, Regimes.ReadyAt (simTrace S rho hn) (honestKeys S rho)
          (Regimes.catchUp (S.params (pubOf E) hn)) y b →
          Regimes.CutAfter (simTrace S rho hn) j b →
          Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho))
            (Regimes.readAfter (simTrace S rho hn) x jx t)
            (Regimes.readAfter (simTrace S rho hn) y j b) := by
  sorry

/-- OPEN missing grid supplier (owner: family/timing integration). Single-pattern engine
recurrence must become node recurrence at exactly the same selected schedule. This is only
a named obligation: the pending slot-grid repair must justify every window endpoint, rather
than assuming the node recurrence in an unconditional Accepted theorem. -/
def SleepyRecurrenceSupplier : Prop :=
  ∀ (k : ℕ+) b, 0 ≤ b → b ≤ rho.horizon → rho.ExecutionValid →
    Blocks.PatternRecurrence rho.point rho.key (fun s => rho.sel (.proposer s))
      (family S (pubOf E)).skel.grid ⟨Blocks.Pattern.single, k⟩
      (Regimes.catchUp (S.params (pubOf E) hn)) 0 b →
    Regimes.ProposerRecurrence (simTrace S rho hn) (honestKeys S rho) (runProposer S rho hn)
      (Regimes.catchUp (S.params (pubOf E) hn)) k 0 b

/-- OPEN proposal evidence bridge (owner: Refinement). Unpack the canonical producer's
tick and `block_released`: its signed header is the engine proposal, and readiness transfers
back through the key equivalence. The producer's time is explicitly bounded by the horizon.
R.2 supplies the node producer, not this encoding/release proof. -/
theorem sleepy_proposal (hv : rho.ExecutionValid) {τ : Time}
    (hτ : 0 ≤ τ) (hτh : τ ≤ rho.horizon)
    {P : SA.Blk (Fintype.card V) (List (FG.Att (Fintype.card V)))}
    (hP : Regimes.ReadyProposalAt (simTrace S rho hn) (honestKeys S rho)
      (Regimes.catchUp (S.params (pubOf E) hn)) τ P) :
    ∃ k, rho.point.Ready (Regimes.catchUp (S.params (pubOf E) hn)) (rho.key k) τ ∧
      Shape.HonestProposal rho τ k (headerOf (S.params (pubOf E) hn) P) := by
  sorry

/-- OPEN inclusion-to-chain consumer (owner: Refinement). Parent-closed coherent stores
turn node ancestry into membership of the encoded non-genesis header. `sleepy_read_cut`
supplies the end-of-time cut and exact output clock. Keep readiness, producer provenance,
collision freedom and the finite observation bound; ancestry alone is not engine inclusion.
Depends on the chain lemmas, canonical simulation and the encoding repair. -/
theorem sleepy_inBy (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn)) {τ t : Time}
    (hτ : 0 ≤ τ) (hτt : τ ≤ t) (hth : t ≤ rho.horizon)
    {P : SA.Blk (Fintype.card V) (List (FG.Att (Fintype.card V)))}
    (hP : Regimes.ReadyProposalAt (simTrace S rho hn) (honestKeys S rho)
      (Regimes.catchUp (S.params (pubOf E) hn)) τ P)
    (hinc : ∀ y j, Regimes.ReadyAt (simTrace S rho hn) (honestKeys S rho)
      (Regimes.catchUp (S.params (pubOf E) hn)) y t →
      Regimes.CutAfter (simTrace S rho hn) j t →
      Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho)) P
        (Regimes.readAfter (simTrace S rho hn) y j t)) :
    InBy rho (Regimes.catchUp (S.params (pubOf E) hn)) .confirmed
      (headerOf (S.params (pubOf E) hn) P) t := by
  sorry

/-- OPEN arbitrary-cut safety consumer (owner: Refinement). R.1 bounds node reads; the
engine exposes every event cut, not only end-of-time reads. Relate each ready reader's
stored clock/output to a node boundary at the engine cut time before applying finite R.1.
`sleepy_read_cut` alone is insufficient because it only handles end-of-time cuts. This
leaf records that separate clock obligation; no future node time is used as observation.
Depends on finite R.1 and structural chain compatibility/monotonicity transport. -/
theorem sleepy_safe_engine (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    (hsync : (simTrace S rho hn).SyncBefore (honestKeys S rho)
      (S.params (pubOf E) hn).Δ rho.horizon)
    (hf : ∀ s : Nat, ∀ d ∈ ({0, (S.params (pubOf E) hn).Δ,
      2 * (S.params (pubOf E) hn).Δ} : Set Time),
      (S.params (pubOf E) hn).ts s + d ≤ rho.horizon →
      (simTrace S rho hn).FaultBound (honestKeys S rho) ((S.params (pubOf E) hn).ts s + d)) :
    (chainTrace rho).ReadySafe (Regimes.catchUp (S.params (pubOf E) hn)) .confirmed 0 := by
  sorry

end Consensus.Goldilocks.Refinement

end
