module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Order
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Regimes.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outputs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Sleepy
public import ConsensusLean.Spec.Shape.Run
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Finite sleepy transport obligations

OPEN skeleton, owned by the simulation/obligations integration. CLAIMS R.1/R.2 prove node
safety/inclusion/growth; they do not prove these finite engine bridges. No whole-run
`SleepyRun` or `HealthyRun` is inferred from a finite engine horizon.

There is no node-level prefix attestation (retired; the prefix claim is the generic
`CorrectProtocol.sleepySafe_prefix`). The finite consumers below
use `SleepyServiceBefore`, which permits retained stamped SA evidence and bounds
the recipient's deadline, and bound all observations
by `b`. Their proofs need a dependency-local version of R.1/R.2, not direct application of
`IncludeSleepy`/`GrowSleepy` (both currently require whole-run `SleepyRun`).

The missing network supplier is named as a proposition, NOT asserted as a theorem.
`Setup.params` has Δp = Δe with matching protocol slots: L0 delivers strictly before the bound,
which is the node's strict deadline. This covers no relay delay and no missing processing proof.
Catch-up, recurrence and latency transport remain separate obligations. No impossible
strict-delay premise is used. The raw-genesis/canonical collision bridge is separately owned by
the encoding integration.
-/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- Engine readiness bridge. Map honesty by the key equivalence
and awake intervals by canonical simulation. Both ends are inside the finite horizon; the
catch-up is the NODE duration, not silently `18 * E.ΔAC`. R.1 defines the same closed interval,
but supplies no engine proof. -/
theorem ready_transport (_hv : rho.ExecutionValid) {c : Time} {v : V} {t : Time}
    (_ht : 0 ≤ t) (hth : t ≤ rho.horizon)
    (hr : rho.point.Ready c v t) :
    Regimes.ReadyAt (simTrace S rho hn) (honestKeys S rho)
      c (rho.ownKey v) t := by
  have hkey : rho.key (rho.ownKey v) = v := rho.key.apply_symm_apply v
  constructor
  · rw [mem_honestKeys_iff]
    rw [hkey]
    exact hr.1
  · intro τ hτ hτt
    rw [simTrace_awake_iff, awakeAt_iff, hkey]
    exact ⟨hr.2 τ hτ hτt, (le_max_left _ _).trans hτ, hτt.trans hth⟩

theorem sleepy_ready (hv : rho.ExecutionValid) {v : V} {t : Time}
    (ht : 0 ≤ t) (hth : t ≤ rho.horizon)
    (hr : rho.point.Ready (Regimes.catchUp (S.params (pubOf E) hn)) v t) :
    Regimes.ReadyAt (simTrace S rho hn) (honestKeys S rho)
      (Regimes.catchUp (S.params (pubOf E) hn)) (rho.ownKey v) t :=
  ready_transport S rho hn hv ht hth hr

/-- Quorum bridge. Half-ready means faulty < ready; transport
counts through the key equivalence and use ready-implies-joined at each slot point.
Only points through `b` are claimed, including slot zero. Depends on `sleepy_ready` and
the node readiness/join lemma, not on synchrony or whole-run participation. -/
theorem sleepy_faultBound (hv : rho.ExecutionValid) {b : Time}
    (hb : b ≤ rho.horizon)
    (hhalf : rho.point.SleepyOn (1 / 2) (Regimes.catchUp (S.params (pubOf E) hn)) 0 b) :
    ∀ s : Nat, ∀ d ∈ ({0, (S.params (pubOf E) hn).Δ,
      2 * (S.params (pubOf E) hn).Δ} : Set Time), (S.params (pubOf E) hn).ts s + d ≤ b →
      (simTrace S rho hn).FaultBound (honestKeys S rho) ((S.params (pubOf E) hn).ts s + d) := by
  classical
  intro s d hd htb
  let t := (S.params (pubOf E) hn).ts s + d
  have hΔ := (S.params (pubOf E) hn).toParams.hΔ
  have ht : 0 ≤ t := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl | rfl <;>
      dsimp [t, SA.SAParams.ts] <;> positivity
  have hh := hhalf t ht htb
  have hlt : rho.point.faulty.card <
      (rho.point.readyAt (Regimes.catchUp (S.params (pubOf E) hn)) t).card := by
    unfold EnvPoint.ReadyAbove at hh
    have hq : (rho.point.faulty.card : ℚ) <
        (rho.point.readyAt (Regimes.catchUp (S.params (pubOf E) hn)) t).card := by
      linarith
    exact_mod_cast hq
  have hf : (honestKeys S rho)ᶜ.ncard = rho.point.faulty.card := by
    have heq : (honestKeys S rho)ᶜ = rho.key ⁻¹' (↑rho.point.faulty : Set V) := by
      ext k
      simp [mem_honestKeys_iff, EnvPoint.faulty, Model.Run.point]
    rw [heq, Set.ncard_preimage_of_injective_subset_range rho.key.injective
      (by simp [rho.key.surjective.range_eq]), Set.ncard_coe_finset]
  have hcount : (rho.point.readyAt (Regimes.catchUp (S.params (pubOf E) hn)) t).card ≤
      (simTrace S rho hn).honestAwakeJoined (honestKeys S rho) t := by
    rw [← Set.ncard_coe_finset]
    apply Set.ncard_le_ncard_of_injOn rho.ownKey
    · intro v hv'
      have hr : rho.point.Ready (Regimes.catchUp (S.params (pubOf E) hn)) v t :=
        (Finset.mem_filter.mp hv').2
      have hready := sleepy_ready S rho hn hv ht (htb.trans hb) hr
      refine ⟨hready.1, ?_⟩
      exact Compose.ready_implies_joined _ _ _ _ _ _ (simTrace_goldilocksRun S rho hn hv)
        _ hready.1 t _ ht (by unfold Regimes.catchUp; linarith) hready.2
    · exact rho.key.symm.injective.injOn
  change (honestKeys S rho)ᶜ.ncard < _
  rw [hf]
  exact hlt.trans_le hcount

/-- OPEN missing service supplier, not a proved or
assumed fact of the obligations endpoint. With the timing adapter installed: finite engine
deadline service yields node deadline-bounded service, including acceptance relay.
Receipt alone does not prove acceptance relay; Δp = Δe matches only the strict endpoint.
This definition records the missing obligation without adding a vacuous `hdelay` premise.
The repaired supplier may require a larger engine service window, which must be propagated
to the consumer and contract rather than assumed away. -/
def SleepyServiceSupplier : Prop :=
  ∀ b, 0 ≤ b → b ≤ rho.horizon → rho.ExecutionValid →
    rho.log.SyncUntil rho.point b →
    Compose.SleepyServiceBefore (simTrace S rho hn) (honestKeys S rho) (S.params (pubOf E) hn).Δ b

theorem event_before_endCut (hv : rho.ExecutionValid) {t : Time} (ht : 0 ≤ t)
    {i : Nat} {e : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object}
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
theorem ready_read_cut (hv : rho.ExecutionValid) {c : Time} (hc : 0 ≤ c) {v : V} {t : Time}
    (ht : 0 ≤ t) (hth : t ≤ rho.horizon)
    (hr : rho.point.Ready c v t) :
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
      rw [mem_honestKeys_iff]
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

theorem sleepy_read_cut (hv : rho.ExecutionValid) {v : V} {t : Time}
    (ht : 0 ≤ t) (hth : t ≤ rho.horizon)
    (hr : rho.point.Ready (Regimes.catchUp (S.params (pubOf E) hn)) v t) :
    Regimes.CutAfter (simTrace S rho hn) (cutMap S rho hn ((chainTrace rho).endCut t)) t ∧
      Regimes.Boundary (simTrace S rho hn) (rho.ownKey v)
        (cutMap S rho hn ((chainTrace rho).endCut t)) ∧
      (stateAt S rho hn v ((chainTrace rho).endCut t)).now = t :=
  ready_read_cut S rho hn hv (by
    unfold Regimes.catchUp
    have := (S.params (pubOf E) hn).toParams.hΔ
    linarith) ht hth hr

set_option linter.unusedVariables false in
/-- Finite R.1 from recipient-deadline service and the in-horizon quorum bounds.
Canonical execution uses `runProposer S rho hn`, selected by `rho.sel`.
The unused horizon premise is retained to preserve the existing named-argument interface. -/
theorem sleepy_safe_finite (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn)) {b : Time}
    (hb0 : 0 ≤ b) (hbh : b ≤ rho.horizon)
    (hsync : Compose.SleepyServiceBefore (simTrace S rho hn) (honestKeys S rho)
      (S.params (pubOf E) hn).Δ b)
    (hf : ∀ s : Nat, ∀ d ∈ ({0, (S.params (pubOf E) hn).Δ,
      2 * (S.params (pubOf E) hn).Δ} : Set Time), (S.params (pubOf E) hn).ts s + d ≤ b →
      (simTrace S rho hn).FaultBound (honestKeys S rho) ((S.params (pubOf E) hn).ts s + d)) :
    Regimes.ReadySafeOn (simTrace S rho hn) (honestKeys S rho)
      (Regimes.catchUp (S.params (pubOf E) hn)) 0 b := by
  exact Regimes.sleepy_safe_before (simTrace_goldilocksRun S rho hn hv) hnc hb0 hsync hf

set_option linter.unusedVariables false in
/-- Finite R.2 inclusion consumer. Re-run A1.7/F.4 only
through the observation `t ≤ b`: the producer at `τ` is in the horizon, and its full `6Δ`
margin ends before the observation. Every service dependency must fit `SleepyServiceBefore b`.
`IncludeSleepy` is the paper source, not an applicable finite theorem. No future participation
or whole-run extension is assumed. Uses the canonical run with `runProposer S rho hn`. -/
theorem sleepy_include_finite (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn)) {b : Time}
    (hb0 : 0 ≤ b) (hbh : b ≤ rho.horizon)
    (hsync : Compose.SleepyServiceBefore (simTrace S rho hn) (honestKeys S rho)
      (S.params (pubOf E) hn).Δ b)
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
  have hrun := simTrace_goldilocksRun S rho hn hv
  have hinv := Compose.sleepy_invariant_before hrun hnc hb0 hsync hf
  exact Regimes.read_extends_of_record_before hrun hnc hinv
    hsync.ac
    (fun s hs => hf s _ (by simp) hs) hy.1 hj hy htb
    (Regimes.ready_record_extends_before hrun hnc hb0 hsync hf hinv hP hmargin hy hj htb)

/-- Finite R.2 growth consumer. Select a ready scheduled
producer in `(t, t+4kΔ]`, leaving `6Δ` before `b = t+(4k+6)Δ`. Apply finite inclusion and
finite safety; slot bounds exclude the new block from every earlier ready read. The explicit
upper producer bound is needed to transport release/proposal evidence inside the horizon.
The recurrence is for `runProposer S rho hn` (from `rho.sel`), never a setup-fixed schedule.
The engine pattern-to-recurrence and duration adapters remain separate OPEN suppliers. -/
theorem sleepy_grow_finite (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn)) {t b : Time} {k : Nat}
    (ht : 0 ≤ t) (hk : 1 ≤ k) (hb : b = t + (4 * k + 6) * (S.params (pubOf E) hn).Δ)
    (hbh : b ≤ rho.horizon)
    (hsync : Compose.SleepyServiceBefore (simTrace S rho hn) (honestKeys S rho)
      (S.params (pubOf E) hn).Δ b)
    (hf : ∀ s : Nat, ∀ d ∈ ({0, (S.params (pubOf E) hn).Δ,
      2 * (S.params (pubOf E) hn).Δ} : Set Time), (S.params (pubOf E) hn).ts s + d ≤ b →
      (simTrace S rho hn).FaultBound (honestKeys S rho) ((S.params (pubOf E) hn).ts s + d))
    (hrec : Regimes.ProposerRecurrence (simTrace S rho hn) (honestKeys S rho)
      (runProposer S rho hn) (Regimes.catchUp (S.params (pubOf E) hn)) k 0 b)
    (_hreader : ∃ v, Regimes.ReadyAt (simTrace S rho hn) (honestKeys S rho)
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
  let sp := S.params (pubOf E) hn
  let tr := simTrace S rho hn
  let H := honestKeys S rho
  have hrun := simTrace_goldilocksRun S rho hn hv
  have hΔ := sp.toParams.hΔ
  have hcoh := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  set s₀ := sp.slot t + 1
  have hts₀ : t < sp.ts s₀ := by
    by_contra h
    have := (SA.ts_le_iff_le_slot sp ht (s₀ : Int)).1 (not_lt.1 h)
    omega
  have hts₀' : sp.ts s₀ ≤ t + 4 * sp.Δ := by
    have := (SA.ts_le_iff_le_slot sp ht (sp.slot t : Int)).2 le_rfl
    simp only [SA.SAParams.ts] at this ⊢
    push_cast [s₀]
    linarith
  obtain ⟨s, hs₀s, hss, hready⟩ := hrec s₀ (lt_of_le_of_lt ht hts₀) (by
    rw [hb]
    simp only [SA.SAParams.ts] at hts₀' ⊢
    have h1k : (1 : Time) ≤ k := by exact_mod_cast hk
    rw [show ((s₀ + k - 1 : Nat) : Time) = (s₀ : Time) + k - 1 by
      rw [Nat.cast_sub (by omega)]; push_cast; ring]
    linarith)
  have hts : t < sp.ts s :=
    lt_of_lt_of_le hts₀ ((SA.ts_le_iff sp).2 (by exact_mod_cast hs₀s))
  have htsD : sp.ts s + 6 * sp.Δ ≤ b := by
    have : sp.ts s ≤ sp.ts (s₀ + (k - 1) : Nat) :=
      (SA.ts_le_iff sp).2 (by push_cast; omega)
    rw [hb]
    simp only [SA.SAParams.ts] at this hts₀' ⊢
    push_cast at this hts₀' ⊢
    rw [show ((k - 1 : Nat) : Time) = k - 1 by rw [Nat.cast_sub hk]; simp] at this
    linarith
  obtain ⟨kP, P, hP, hkP⟩ := Regimes.ready_proposer_proposes hrun hnc (by omega) hready
  have hPslot : P.slot = s := by
    have h := hP.2.2
    rw [hkP, sp.slotTime_eq] at h
    simp only [SA.SAParams.ts] at h
    have := SA.four_delta_pos sp
    exact_mod_cast (mul_left_cancel₀ this.ne' h).symm
  have hRP : Regimes.ReadyProposalAt tr H (Regimes.catchUp sp) (sp.ts s) P :=
    ⟨_, kP, hready, hP, hkP⟩
  have hinc : ∀ y j, Regimes.ReadyAt tr H (Regimes.catchUp sp) y b →
      Regimes.CutAfter tr j b → Anc (tr.HonestBlocks H) P (Regimes.readAfter tr y j b) :=
    fun y j hy hj => sleepy_include_finite S rho hn hv hnc hb0 hbh hsync hf
      (ht.trans hts.le) (by linarith) hRP htsD le_rfl hy hj
  have hnot : ∀ x jx, Regimes.ReadyAt tr H (Regimes.catchUp sp) x t →
      Regimes.CutAfter tr jx t → ¬ Anc (tr.HonestBlocks H) P (Regimes.readAfter tr x jx t) := by
    intro x jx hx hjx hPx
    have hΦ := Compose.frameOK_state hrun.toLocalRun hx.1 jx
    have hmem := (Regimes.sa_tips (A := (tr.state x jx).ac) hΦ t).1
    have hXs : (Regimes.readAfter tr x jx t).slot ≤ sp.slot t := by
      change (SA.acConfirmed sp (tr.state x jx).ac (Node.frame (tr.state x jx)) t).slot ≤ _
      rcases Compose.tree_cases hrun.toLocalRun hx.1 hmem.1 with hg | ⟨q, hq, hacc⟩
      · rw [hg]; exact Nat.zero_le _
      · exact ((hrun.cutLaw x hx.1 q _ hacc).1).trans
          (SA.slot_mono sp (hrun.time_nonneg q) (hjx.1 q hq))
    have := (Anc.slot_le hcoh hPx).1
    have hslt : sp.slot t < s := by
      by_contra h
      have := (SA.ts_le_iff_le_slot sp ht (s : Int)).2 (by omega)
      linarith
    omega
  refine ⟨sp.ts s, P, hts, htsD, hRP, hinc,
    fun x jx hx hjx => ⟨hnot x jx hx hjx, fun y j hy hj => ?_⟩⟩
  have hsafe := sleepy_safe_finite S rho hn hv hnc hb0 hbh hsync hf
  have hcompat := hsafe.1 x y jx j t b ⟨hjx.1, hjx.2.le⟩ ⟨hj.1, hj.2.le⟩
    (Regimes.cutAfter_boundary hrun hx.1 hjx) (Regimes.cutAfter_boundary hrun hy.1 hj)
    ht (by linarith) hb0 le_rfl hx hy
  rcases hcompat with h | h
  · exact h
  · exact absurd ((hinc y j hy hj).trans h) (hnot x jx hx hjx)

/-- OPEN missing grid supplier. Single-pattern engine
recurrence must become node recurrence at exactly the same selected schedule. This is only
a named obligation: the pending slot-grid repair must justify every window endpoint, rather
than assuming the node recurrence in an unconditional obligations theorem. -/
def SleepyRecurrenceSupplier : Prop :=
  ∀ (k : ℕ+) b, 0 ≤ b → b ≤ rho.horizon → rho.ExecutionValid →
    Blocks.PatternRecurrence rho.point rho.key (fun s => rho.sel (.proposer s))
      (goldilocks S (pubOf E)).skel.grid ⟨Blocks.Pattern.single, k⟩
      (Regimes.catchUp (S.params (pubOf E) hn)) 0 b →
    Regimes.ProposerRecurrence (simTrace S rho hn) (honestKeys S rho) (runProposer S rho hn)
      (Regimes.catchUp (S.params (pubOf E) hn)) k 0 b

/-- Proposal evidence bridge. Unpack the canonical producer's
tick and `block_released`: its signed header is the engine proposal, and readiness transfers
back through the key equivalence. The producer's time is explicitly bounded by the horizon.
R.2 supplies the node producer, not this encoding/release proof. -/
theorem ready_proposal (hv : rho.ExecutionValid) {c : Time} {τ : Time}
    (_hτ : 0 ≤ τ) (_hτh : τ ≤ rho.horizon)
    {P : SA.Blk (Fintype.card V) (List (FG.Att (Fintype.card V)))}
    (hP : Regimes.ReadyProposalAt (simTrace S rho hn) (honestKeys S rho)
      c τ P) :
    ∃ k, rho.point.Ready c (rho.key k) τ ∧
      Shape.HonestProposal rho τ k (headerOf (S.params (pubOf E) hn) P) := by
  obtain ⟨p, k, hr, hP, htime⟩ := hP
  have hp := hP.2.1
  subst p
  have hhon := (mem_honestKeys_iff S rho P.proposer).mp hr.1
  refine ⟨P.proposer, ⟨hhon, ?_⟩, hhon, .proposer P.slot, payloadObjs P.fgPayload P.acPayload,
    rfl, ?_⟩
  · intro u hu hut
    exact (simTrace_awake_of S rho hn hv P.proposer hr.1 u (hr.2 u hu hut)).1
  · have hrel := simTrace_block_released S rho hn hv (simTrace_goldilocksRun S rho hn hv)
      P.proposer hr.1 k P hP.1
    rw [htime] at hrel
    exact hrel

theorem sleepy_proposal (hv : rho.ExecutionValid) {τ : Time}
    (hτ : 0 ≤ τ) (hτh : τ ≤ rho.horizon)
    {P : SA.Blk (Fintype.card V) (List (FG.Att (Fintype.card V)))}
    (hP : Regimes.ReadyProposalAt (simTrace S rho hn) (honestKeys S rho)
      (Regimes.catchUp (S.params (pubOf E) hn)) τ P) :
    ∃ k, rho.point.Ready (Regimes.catchUp (S.params (pubOf E) hn)) (rho.key k) τ ∧
      Shape.HonestProposal rho τ k (headerOf (S.params (pubOf E) hn) P) :=
  ready_proposal S rho hn hv hτ hτh hP

/-- Final-cache ancestry at the finite endpoint becomes engine final-output membership.
The readiness duration is supplied unchanged by the caller. -/
theorem finalized_inBy (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {c t : Time} (hc : 0 ≤ c) (ht : 0 ≤ t) (hth : t ≤ rho.horizon)
    {P : SA.Blk (Fintype.card V) (List (FG.Att (Fintype.card V)))}
    (hroot : P.root ≠ (S.params (pubOf E) hn).genesisRoot)
    (hinc : ∀ y j, Regimes.ReadyAt (simTrace S rho hn) (honestKeys S rho) c y t →
      Regimes.CutAfter (simTrace S rho hn) j t →
      Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho)) P
        ((simTrace S rho hn).state y j).fg.F) :
    InBy rho c .finalized (headerOf (S.params (pubOf E) hn) P) t := by
  intro v hr
  let i := (chainTrace rho).endCut t
  let j := cutMap S rho hn i
  have hs := simTrace_simulates S rho hn hv
  have hi : i ≤ rho.events.length := Nat.findGreatest_le _
  have hy := honest_ownKey (S := S) hr.1
  have hreach := Compose.fg_reachable hs.run.toLocalRun hy j
  have htip := (Store.cache_invariants _ _ _ _ hreach).1
  have hcut := ready_read_cut S rho hn hv hc ht hth hr
  have ha := hinc _ j (ready_transport S rho hn hv ht hth hr) hcut.1
  have hanc := anc_in_store hreach (Compose.honest_blocks_coherent hs.run.toLocalRun hnc)
    (fun _ h => ⟨_, hy, j, h⟩) ha htip
  have hprefix := chainTo_prefix hreach hanc
  have hmem : headerOf (S.params (pubOf E) hn) P ∈
      chainTo ((simTrace S rho hn).state (rho.ownKey v) j).fg.blocks (P.slot + 1) P := by
    simp only [chainTo, ite_eq_right hroot]
    split <;> simp
  have hout := hprefix.subset hmem
  change headerOf (S.params (pubOf E) hn) P ∈ (chainTrace rho).read .finalized v i
  rw [read_eq_out S rho hn, outOf, hs.state v hr.1 i hi]
  exact hout

/-- Inclusion-to-chain consumer. Parent-closed coherent stores
turn node ancestry into membership of the encoded non-genesis header. `sleepy_read_cut`
supplies the end-of-time cut and exact output clock. Keep readiness, producer provenance,
collision freedom and the finite observation bound; ancestry alone is not engine inclusion.
Depends on the chain lemmas, canonical simulation and the encoding repair. -/
theorem confirmed_inBy (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {c : Time} (hc : 0 ≤ c) {τ t : Time}
    (hτ : 0 ≤ τ) (hτt : τ ≤ t) (hth : t ≤ rho.horizon)
    {P : SA.Blk (Fintype.card V) (List (FG.Att (Fintype.card V)))}
    (hP : Regimes.ReadyProposalAt (simTrace S rho hn) (honestKeys S rho)
      c τ P)
    (hinc : ∀ y j, Regimes.ReadyAt (simTrace S rho hn) (honestKeys S rho)
      c y t →
      Regimes.CutAfter (simTrace S rho hn) j t →
      Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho)) P
        (Regimes.readAfter (simTrace S rho hn) y j t)) :
    InBy rho c .confirmed
      (headerOf (S.params (pubOf E) hn) P) t := by
  have hs := simTrace_simulates S rho hn hv
  have hroot : P.root ≠ (S.params (pubOf E) hn).genesisRoot := by
    obtain ⟨p, k, hp, hprop, _⟩ := hP
    obtain ⟨⟨acc, hc⟩, hpos⟩ := hprop.1
    rcases Compose.blockCall_cases hs.run.toLocalRun hp.1 hc with hg | hg
    · have := (hg.2.1 0 (List.length_pos_iff.mpr hg.1)).2.2.2.1
      exact False.elim (hpos (by simpa using this))
    · obtain ⟨j, x, _, _, _, d, p', _, hB, _⟩ := hg
      rw [hB, digestOf_eq]
      simp only [Node.mkBlock]
      erw [dgOf_eq]
      exact taggedRoot_ne _ _
  intro v hr
  let i := (chainTrace rho).endCut t
  let j := cutMap S rho hn i
  have hi : i ≤ rho.events.length := Nat.findGreatest_le _
  have hy := honest_ownKey (S := S) hr.1
  have hreach := Compose.fg_reachable hs.run.toLocalRun hy j
  have hframe := (Store.frame_realization _ _ _ _ hreach).1
  have htip := (Regimes.sa_tips
    (A := ((simTrace S rho hn).state (rho.ownKey v) j).ac) hframe t).1.1
  have hcut := ready_read_cut S rho hn hv hc (hτ.trans hτt) hth hr
  have ha := hinc _ j (ready_transport S rho hn hv (hτ.trans hτt) hth hr) hcut.1
  have hanc := anc_in_store hreach (Compose.honest_blocks_coherent hs.run.toLocalRun hnc)
    (fun _ h => ⟨_, hy, j, h⟩) ha htip
  have hprefix := chainTo_prefix hreach hanc
  have hmem : headerOf (S.params (pubOf E) hn) P ∈
      chainTo ((simTrace S rho hn).state (rho.ownKey v) j).fg.blocks (P.slot + 1) P := by
    simp only [chainTo, ite_eq_right hroot]
    split <;> simp
  have hout := hprefix.subset hmem
  change headerOf (S.params (pubOf E) hn) P ∈ (chainTrace rho).read .confirmed v i
  rw [read_eq_out S rho hn, outOf, hs.state v hr.1 i hi, hcut.2.2]
  exact hout

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
      (headerOf (S.params (pubOf E) hn) P) t :=
  confirmed_inBy S rho hn hv hnc (by
    unfold Regimes.catchUp
    have := (S.params (pubOf E) hn).toParams.hΔ
    linarith) hτ hτt hth hP hinc

/-- The mapped post-event cut is a nonstrict read point at the event time.
Other nodes may still have events at the same time. -/
theorem readPoint_after_event (hv : rho.ExecutionValid) {i : Nat}
    {e : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object}
    (he : rho.events[i]? = some e) :
    Regimes.ReadPoint (simTrace S rho hn) (cutMap S rho hn (i + 1)) e.time := by
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  constructor
  · intro k hk
    have hlen : k < (allCuts S rho hn).length := by
      rw [length_allCuts]
      exact hk.trans_le (cutMap_mono S rho hn (by omega))
    have hl : (simTrace S rho hn).label k ≠ none := by
      rw [simTrace_label, List.getElem?_eq_getElem hlen]
      simp
    obtain ⟨_, j, f, _, hf, hj, _, _, _, ht, _⟩ := simTrace_cut S rho hn hl
    have hji : j ≤ i := by
      by_contra h
      have := cutMap_mono S rho hn (show i + 1 ≤ j by omega)
      omega
    rw [ht]
    rcases hji.lt_or_eq with h | rfl
    · rcases keyLe_of_lt S rho hv hf he h with h | ⟨h, _⟩
      · exact h.le
      · exact h.le
    · rw [he] at hf
      exact (Option.some.inj hf) ▸ le_rfl
  · cases hr : (allCuts S rho hn)[cutMap S rho hn (i + 1)]? with
    | none =>
      rw [(simTrace_of_getElem?_none S rho hn hr).2]
      have := (hv.in_horizon e (List.mem_of_getElem? he)).2
      linarith
    | some r =>
      have hl : (simTrace S rho hn).label (cutMap S rho hn (i + 1)) ≠ none := by
        rw [simTrace_label, hr]; simp
      obtain ⟨_, j, f, _, hf, _, hj, _, _, ht, _⟩ := simTrace_cut S rho hn hl
      have hij : i < j := by
        by_contra h
        have := cutMap_mono S rho hn (show j + 1 ≤ i + 1 by omega)
        omega
      rw [ht]
      rcases keyLe_of_lt S rho hv he hf hij with h | ⟨h, _⟩
      · exact h.le
      · exact h.le

/-- A completed local event leaves the stored clock at that event's time, including
deliveries (whose preceding tick is forced by execution validity). -/
theorem now_after_local_event (hv : rho.ExecutionValid) {v : V} {i : Nat}
    {e : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object}
    (he : rho.events[i]? = some e) (hev : e.node = v) :
    (stateAt S rho hn v (i + 1)).now = e.time := by
  rw [now_eq_lastClock S rho hn hv]
  cases e with
  | tick w t =>
    simp only [Model.Event.node] at hev
    subst v
    exact lastClock_succ_tick S rho w he
  | restart w t =>
    simp only [Model.Event.node] at hev
    subst v
    exact lastClock_succ_restart S rho w he
  | deliver w o t =>
    simp only [Model.Event.node] at hev
    subst v
    rw [lastClock_succ_deliver S rho w he]
    exact lastClock_of_deliver S rho hv w he

/-- At any cut the reader is still initial, or its state is the post-state of a
complete local event. Other nodes' later events do not move this reader's clock. -/
theorem stateAt_last_local_event (hv : rho.ExecutionValid) (v : V) : ∀ i,
    stateAt S rho hn v i = stateAt S rho hn v 0 ∨
      ∃ j < i, ∃ e, rho.events[j]? = some e ∧ e.node = v ∧
        stateAt S rho hn v i = stateAt S rho hn v (j + 1) ∧
        (stateAt S rho hn v i).now = e.time
  | 0 => Or.inl rfl
  | i + 1 => by
    cases he : rho.events[i]? with
    | none =>
      rw [stateAt_succ_none S rho hn v he]
      rcases stateAt_last_local_event hv v i with h | ⟨j, hj, e, he, hev, hs, ht⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, e, he, hev, hs, ht⟩
    | some e =>
      by_cases hev : e.node = v
      · exact Or.inr ⟨i, Nat.lt_succ_self i, e, he, hev, rfl,
          now_after_local_event S rho hn hv he hev⟩
      · rw [state_of_other S rho hn v i e he hev]
        rcases stateAt_last_local_event hv v i with h | ⟨j, hj, e, he, hev, hs, ht⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, by omega, e, he, hev, hs, ht⟩

/-- A positive own tick no later than the stored clock has completed, provided
the reader did not restart at that tick's time. Equality uses event phase order. -/
theorem tick_before_stored_clock (hv : rho.ExecutionValid) {v : V} {p i : Nat} {t : Time}
    (he : rho.events[p]? = some (.tick v t)) (ht : 0 < t)
    (hti : t ≤ (stateAt S rho hn v i).now)
    (hnr : ∀ q < i, rho.events[q]? ≠ some (.restart v t)) : p < i := by
  by_contra hpi
  have hip : i ≤ p := by omega
  rcases stateAt_last_local_event S rho hn hv v i with h | ⟨q, hqi, e, hq, hnode, _, htime⟩
  · rw [h, stateAt_eq] at hti
    change t ≤ 0 at hti
    linarith
  · have hqp : q < p := by omega
    have horder := keyLe_of_index_lt S rho hv hq he hqp
    have hte : t ≤ e.time := hti.trans_eq htime
    rcases horder with horder | ⟨heq, hphase⟩
    · exact (not_lt_of_ge hte) horder
    · cases e with
      | tick w u =>
        simp only [Model.Event.node] at hnode
        simp only [Model.Event.time] at heq
        subst w; subst u
        have := index_eq_of_events S rho hv hq he
        omega
      | restart w u =>
        simp only [Model.Event.node] at hnode
        simp only [Model.Event.time] at heq
        subst w; subst u
        exact hnr q hqi hq
      | deliver w o u => simp only [Model.Event.phase] at hphase; omega

/-- A stored clock cannot be ahead of the next engine event. -/
theorem now_le_event (hv : rho.ExecutionValid) (v : V) {i : Nat}
    {e : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object}
    (he : rho.events[i]? = some e) : (stateAt S rho hn v i).now ≤ e.time := by
  rcases stateAt_last_local_event S rho hn hv v i with h | ⟨j, hj, f, hf, _, _, ht⟩
  · rw [h, stateAt_eq]
    exact (hv.in_horizon e (List.mem_of_getElem? he)).1
  · rw [ht]
    rcases keyLe_of_lt S rho hv hf he hj with h | ⟨h, _⟩
    · exact h.le
    · exact h.le

/-- Restarts, ticks and deliveries never decrease the stored clock. -/
theorem now_mono (hv : rho.ExecutionValid) (v : V) :
    Monotone (fun i => (stateAt S rho hn v i).now) := by
  apply monotone_nat_of_le_succ
  intro i
  cases he : rho.events[i]? with
  | none => rw [stateAt_succ_none S rho hn v he]
  | some e =>
    by_cases hev : e.node = v
    · rw [now_after_local_event S rho hn hv he hev]
      exact now_le_event S rho hn hv v he
    · rw [state_of_other S rho hn v i e he hev]

/-- At a valid event cut the stored clock is between zero and the cut time. -/
theorem now_bounds_cut (hv : rho.ExecutionValid) (v : V) {i : Nat}
    (hi : i ≤ rho.events.length) :
    0 ≤ (stateAt S rho hn v i).now ∧ (stateAt S rho hn v i).now ≤ rho.cutTime i := by
  have hmono := now_mono S rho hn hv v (Nat.zero_le i)
  dsimp only at hmono
  rw [stateAt_eq S rho hn v 0] at hmono
  refine ⟨hmono, ?_⟩
  cases i with
  | zero => rw [stateAt_eq]; exact le_rfl
  | succ i =>
    have hi' : i < rho.events.length := by omega
    let e := rho.events[i]
    have he : rho.events[i]? = some e := List.getElem?_eq_getElem hi'
    simp only [Model.Run.cutTime, he]
    by_cases hev : e.node = v
    · exact (now_after_local_event S rho hn hv he hev).le
    · rw [state_of_other S rho hn v i e he hev]
      exact now_le_event S rho hn hv v he

/-- Unit-time ticks bound a ready reader's clock lag, even before its tick at
the current cut time. The extra unit of catch-up pays for this lag. -/
theorem stored_now_ge_cutTime_sub_one (hv : rho.ExecutionValid) {v : V} {i : Nat}
    (hi : i ≤ rho.events.length) {c : Time} (hc : 0 ≤ c)
    (hr : rho.point.Ready (c + 1) v (rho.cutTime i)) :
    rho.cutTime i - 1 ≤ (stateAt S rho hn v i).now := by
  obtain ⟨hn0, hnT⟩ := now_bounds_cut S rho hn hv v hi
  have hlag : rho.cutTime i - 1 ≤ (stateAt S rho hn v i).now := by
    by_cases ht : 0 ≤ rho.cutTime i - 1
    · have hth : rho.cutTime i - 1 ≤ rho.horizon := by
        cases i with
        | zero => simp [Model.Run.cutTime] at ht
        | succ i =>
          have hi' : i < rho.events.length := by omega
          have he := List.getElem?_eq_getElem hi'
          have := (hv.in_horizon _ (List.mem_of_getElem? he)).2
          simp only [Model.Run.cutTime, he]
          linarith
      have hw : E.awake v (rho.cutTime i - 1) = true := hr.2 _
        (max_le ht (by linarith)) (by linarith)
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp
        (hv.tick_total v hr.1 _ ht hth hw)
      have hji : j < i := by
        cases i with
        | zero => simp [Model.Run.cutTime] at ht
        | succ k =>
          have hk : k < rho.events.length := by omega
          have he := List.getElem?_eq_getElem hk
          have htime : rho.cutTime (k + 1) = (rho.events[k]).time := by
            simp [Model.Run.cutTime, he]
          by_contra h
          have hkj : k < j := by omega
          have horder := keyLe_of_lt S rho hv he hj hkj
          change (rho.events[k]).time < rho.cutTime (k + 1) - 1 ∨
            (rho.events[k]).time = rho.cutTime (k + 1) - 1 ∧ _ at horder
          rw [htime] at horder
          rcases horder with horder | ⟨horder, _⟩ <;> linarith
      have hclock := now_after_local_event S rho hn hv (v := v) hj rfl
      have hm := now_mono S rho hn hv v (show j + 1 ≤ i by omega)
      dsimp only at hm
      rw [hclock] at hm
      exact hm
    · linarith
  exact hlag

/-- The extra unit of ready history pays for the stored clock's one-unit lag. -/
theorem ready_at_stored_now (hv : rho.ExecutionValid) {v : V} {i : Nat}
    (hi : i ≤ rho.events.length) {c : Time} (hc : 0 ≤ c)
    (hr : rho.point.Ready (c + 1) v (rho.cutTime i)) :
    rho.point.Ready c v (stateAt S rho hn v i).now := by
  obtain ⟨hn0, hnT⟩ := now_bounds_cut S rho hn hv v hi
  have hlag := stored_now_ge_cutTime_sub_one S rho hn hv hi hc hr
  refine ⟨hr.1, fun τ hlo hhi => hr.2 τ ?_ (hhi.trans hnT)⟩
  apply max_le
  · exact (le_max_left _ _).trans hlo
  · have := (le_max_right _ _).trans hlo
    linarith

/-- At a ready read point, confirmed output is the stored effective record.
This uses the head-support theorem directly: no call-boundary premise is needed. -/
private theorem read_eq_effective_record (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    (hinv : Compose.SleepyInvariantUpTo (simTrace S rho hn) (honestKeys S rho) rho.horizon)
    (hsync : Compose.SleepyServiceBefore (simTrace S rho hn) (honestKeys S rho)
      (S.params (pubOf E) hn).Δ rho.horizon)
    (hf : ∀ s : Nat, (S.params (pubOf E) hn).ts s + (S.params (pubOf E) hn).Δ ≤ rho.horizon →
      (simTrace S rho hn).FaultBound (honestKeys S rho)
        ((S.params (pubOf E) hn).ts s + (S.params (pubOf E) hn).Δ))
    {y : Fin (Fintype.card V)} {j : Nat} {t : Time}
    (hrp : Regimes.ReadPoint (simTrace S rho hn) j t)
    (hr : Regimes.ReadyAt (simTrace S rho hn) (honestKeys S rho)
      (Regimes.catchUp (S.params (pubOf E) hn)) y t) (ht : t ≤ rho.horizon) :
    Regimes.readAfter (simTrace S rho hn) y j t =
      (SA.lookup (Node.frame ((simTrace S rho hn).state y j))
        ((simTrace S rho hn).state y j).ac.latestConfirmed).getD
          ((simTrace S rho hn).state y j).fg.F := by
  let hrun := simTrace_goldilocksRun S rho hn hv
  have hΦ := Compose.frameOK_state hrun.toLocalRun hr.1 j
  cases hl : SA.lookup (Node.frame ((simTrace S rho hn).state y j))
      ((simTrace S rho hn).state y j).ac.latestConfirmed with
  | none =>
    exact SA.acConfirmed_eq_F hΦ (SA.lookup_eq_none hl)
  | some R =>
    obtain ⟨hR, hRr⟩ := SA.lookup_eq_some hl
    have hwj : 0 ≤ t → (simTrace S rho hn).awake y t ∧
        (simTrace S rho hn).JoinedAt y t := fun ht0 =>
      Compose.ready_implies_joined _ _ _ _ _ _ hrun y hr.1 t _ ht0
        (by unfold Regimes.catchUp; linarith [(S.params (pubOf E) hn).toParams.hΔ]) hr.2
    obtain ⟨hc, hs⟩ := Compose.read_head_support_before hinv hrun hnc
      hsync.ac hr.1 ht
      (fun s hs => hf s (hs.trans ht)) hrp.1 hrp.2 hwj ⟨hR, hRr⟩
    exact SA.acConfirmed_eq hΦ hR hRr (SA.anc_acHead hΦ hR hc hs)

/-- Move a ready engine read to a complete local-event cut, evaluate the record
there, then transport back through the unchanged local state. -/
private theorem stored_read_eq_record (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    (hinv : Compose.SleepyInvariantUpTo (simTrace S rho hn) (honestKeys S rho) rho.horizon)
    (hsync : Compose.SleepyServiceBefore (simTrace S rho hn) (honestKeys S rho)
      (S.params (pubOf E) hn).Δ rho.horizon)
    (hf : ∀ s : Nat, (S.params (pubOf E) hn).ts s + (S.params (pubOf E) hn).Δ ≤ rho.horizon →
      (simTrace S rho hn).FaultBound (honestKeys S rho)
        ((S.params (pubOf E) hn).ts s + (S.params (pubOf E) hn).Δ))
    {v : V} {i : Nat} (hi : i ≤ rho.events.length)
    (hr : rho.point.Ready (Regimes.catchUp (S.params (pubOf E) hn) + 1) v (rho.cutTime i)) :
    Regimes.readAfter (simTrace S rho hn) (rho.ownKey v) (cutMap S rho hn i)
        (stateAt S rho hn v i).now =
      (SA.lookup (Node.frame ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)))
        ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)).ac.latestConfirmed).getD
          ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)).fg.F := by
  have hready := ready_at_stored_now S rho hn hv hi (by
    unfold Regimes.catchUp
    linarith [(S.params (pubOf E) hn).toParams.hΔ]) hr
  obtain ⟨q, hq, hs, hrp, hth⟩ : ∃ q ≤ rho.events.length,
      stateAt S rho hn v i = stateAt S rho hn v q ∧
      Regimes.ReadPoint (simTrace S rho hn) (cutMap S rho hn q) (stateAt S rho hn v i).now ∧
      (stateAt S rho hn v i).now ≤ rho.horizon := by
    rcases stateAt_last_local_event S rho hn hv v i with hs | ⟨j, hj, e, he, hev, hs, ht⟩
    · refine ⟨0, Nat.zero_le _, hs, ?_, ?_⟩
      · rw [hs, cutMap_zero, stateAt_eq]
        exact ⟨fun k hk => by omega, (simTrace_goldilocksRun S rho hn hv).time_nonneg 0⟩
      · rw [hs, stateAt_eq]
        exact hv.horizon_nonneg
    · refine ⟨j + 1, by omega, hs, ?_, ?_⟩
      · rw [ht]
        exact readPoint_after_event S rho hn hv he
      · rw [ht]
        exact (hv.in_horizon e (List.mem_of_getElem? he)).2
  have hn0 := (now_bounds_cut S rho hn hv v hi).1
  have hnready := ready_transport S rho hn hv hn0 hth hready
  have heq := read_eq_effective_record S rho hn hv hnc hinv hsync hf hrp hnready hth
  have hstate : (simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i) =
      (simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn q) := by
    rw [← simTrace_state S rho hn hv v hr.1 i hi, ← simTrace_state S rho hn hv v hr.1 q hq, hs]
  simpa only [Regimes.readAfter, hstate] using heq

/-- Finite safety at arbitrary engine cuts. Compatibility holds at arbitrary stored
clocks. For monotonicity, one extra unit of readiness absorbs the clock lag; the last
complete local event identifies the output with the effective record. Records extend
at the original ordered cuts, and coherent stores preserve their emitted chains. -/
theorem sleepy_safe_engine (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    (hsync : Compose.SleepyServiceBefore (simTrace S rho hn) (honestKeys S rho)
      (S.params (pubOf E) hn).Δ rho.horizon)
    (hf : ∀ s : Nat, ∀ d ∈ ({0, (S.params (pubOf E) hn).Δ,
      2 * (S.params (pubOf E) hn).Δ} : Set Time),
      (S.params (pubOf E) hn).ts s + d ≤ rho.horizon →
      (simTrace S rho hn).FaultBound (honestKeys S rho) ((S.params (pubOf E) hn).ts s + d)) :
    (chainTrace rho).ReadySafe (Regimes.catchUp (S.params (pubOf E) hn) + 1) .confirmed 0 := by
  let tr := simTrace S rho hn
  let H := honestKeys S rho
  have hrun := simTrace_goldilocksRun S rho hn hv
  have hinv := Compose.sleepy_invariant_before hrun hnc hv.horizon_nonneg hsync hf
  have hU := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  have hcut : ∀ i ≤ rho.events.length, ∀ k < cutMap S rho hn i, tr.time k ≤ rho.horizon := by
    intro i hi k hk
    apply simTrace_labelled_time_le S rho hn hv
    have hlen : k < (allCuts S rho hn).length := by
      rw [length_allCuts]
      exact hk.trans_le (cutMap_mono S rho hn hi)
    rw [simTrace_label, List.getElem?_eq_getElem hlen]
    simp
  let C := fun v i => Regimes.readAfter tr (rho.ownKey v) (cutMap S rho hn i)
    (stateAt S rho hn v i).now
  have hC : ∀ v ∈ rho.honest, ∀ i,
      C v i ∈ (tr.state (rho.ownKey v) (cutMap S rho hn i)).fg.tree := by
    intro v hv' i
    exact (Regimes.sa_tips (A := (tr.state (rho.ownKey v) (cutMap S rho hn i)).ac)
      (Compose.frameOK_state hrun.toLocalRun (honest_ownKey (S := S) hv') _) _).1.1
  have hread : ∀ v ∈ rho.honest, ∀ i ≤ rho.events.length,
      (chainTrace rho).read .confirmed v i =
        chainTo (tr.state (rho.ownKey v) (cutMap S rho hn i)).fg.blocks
          ((C v i).slot + 1) (C v i) := by
    intro v hv' i hi
    rw [read_eq_out S rho hn, outOf, simTrace_state S rho hn hv v hv' i hi]
    rfl
  have hprefix : ∀ u v i j, u ∈ rho.honest → v ∈ rho.honest →
      i ≤ rho.events.length → j ≤ rho.events.length →
      Anc (tr.HonestBlocks H) (C u i) (C v j) →
      (chainTrace rho).read .confirmed u i <+: (chainTrace rho).read .confirmed v j := by
    intro u v i j hu hv' hi hj ha
    have hu' := honest_ownKey (S := S) hu
    have hv'' := honest_ownKey (S := S) hv'
    have hri := Compose.fg_reachable hrun.toLocalRun hu' (cutMap S rho hn i)
    have hrj := Compose.fg_reachable hrun.toLocalRun hv'' (cutMap S rho hn j)
    have hsi : (tr.state (rho.ownKey u) (cutMap S rho hn i)).fg.tree ⊆ tr.HonestBlocks H :=
      fun _ h => ⟨_, hu', _, h⟩
    have hsj : (tr.state (rho.ownKey v) (cutMap S rho hn j)).fg.tree ⊆ tr.HonestBlocks H :=
      fun _ h => ⟨_, hv'', _, h⟩
    have ha' := anc_in_store hrj hU hsj ha (hC v hv' j)
    have hm : C u i ∈ (tr.state (rho.ownKey v) (cutMap S rho hn j)).fg.tree := by
      by_cases he : C u i = C v j
      · exact he ▸ hC v hv' j
      · exact (Anc.mem ha' he).1
    rw [hread u hu i hi, hread v hv' j hj,
      chainTo_agree hri hrj hU hsi hsj (hC u hu i) hm]
    exact chainTo_prefix hrj ha'
  constructor
  · intro u v i j hi hj hu hv'
    have hc := hinv.read_compatible hrun hnc (honest_ownKey (S := S) hu.1)
      (honest_ownKey (S := S) hv'.1) (hcut i hi.1) (hcut j hj.1)
      (stateAt S rho hn u i).now (stateAt S rho hn v j).now
    rcases hc with hc | hc
    · exact Or.inl (hprefix u v i j hu.1 hv'.1 hi.1 hj.1 hc)
    · exact Or.inr (hprefix v u j i hv'.1 hu.1 hj.1 hi.1 hc)
  · intro v i j hi hij hj hvi hvj
    apply hprefix v v i j hvi.1 hvj.1 hi.1 hj.1
    have hfi := stored_read_eq_record S rho hn hv hnc hinv hsync
      (fun s hs => hf s _ (by simp) hs) hi.1 hvi
    have hfj := stored_read_eq_record S rho hn hv hnc hinv hsync
      (fun s hs => hf s _ (by simp) hs) hj.1 hvj
    dsimp only [C]
    rw [hfi, hfj]
    exact Compose.effective_record_mono_of_invariant hrun hnc hinv
      (honest_ownKey (S := S) hvi.1) (cutMap_mono S rho hn hij) (hcut j hj.1)

end Consensus.Goldilocks.Obligations

end
