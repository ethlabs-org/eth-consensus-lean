module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Simulates
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Regimes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Order
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Transport of the sleepy premises to the canonical growing trace

The engine-side premises of the finite sleepy rows under growing faults, read on the canonical
trace `simTraceAt` with the time-indexed honest keys `honestKeysAt`:

* `ready_transport_at`: an engine node ready at `t ≤ horizon` is ready at `t` in the trace, with
  honesty read at `t` (no constant-fault premise);
* `sleepy_bounds_at`: the L0 sleepy budget with look-ahead `5Δ` on `[a, b]`
  (`EnvPoint.SleepyOn` on the view retained through `lookAhead (5Δ) t`) gives the count
  `FaultBoundAt t d` charged at `d = min (t + 5Δ) b`, at every `t ∈ [max a 0, b]`, `b ≤ horizon`,
  hence the count shapes `SleepyBoundsFrom σ₀` through `b`, for the slots whose slot point
  `t_s + Δ` is at or after `a`.

The finite service comes from `sleepyServiceBefore_of_syncUntil_at`. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation
open Shape
open Consensus.Model (pubOf)

section Lift

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- A node honest at `t ≥ 0` and awake through the catch-up window before `t` is awake and joined
at `t` (the static `ready_implies_joined` on the prefix through `t`). -/
private theorem ready_implies_joined_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    {t c : Time} (hy : y ∈ H t) (ht : 0 ≤ t) (hc : 8 * sp.Δ ≤ c + 1)
    (hawake : ∀ u : Time, max 0 (t - c - 1) ≤ u → u ≤ t → tr.awake y u) :
    tr.awake y t ∧ tr.JoinedAt y t := by
  obtain ⟨hw, hj⟩ := Compose.ready_implies_joined _ _ _ _ _ _ (hrun.upTo ht) y hy t c ht hc
    fun u h1 h2 => ⟨hawake u h1 h2, h2⟩
  exact ⟨hw.1, fun k hk hkt => hj k ((RunTrace.upTo_restartAt tr).2 ⟨hkt, hk⟩) hkt⟩

/-- `2 f_d < n` from the count at `d`, with `h_t ≤ |H d|`. -/
private theorem two_faults_lt_of_faultBoundAt {t d : Time} (h : tr.FaultBoundAt H t d) :
    2 * (H d)ᶜ.ncard < sp.n := by
  have hle : {y | y ∈ H d ∧ tr.awake y t ∧ tr.JoinedAt y t}.ncard ≤ (H d).ncard :=
    Set.ncard_le_ncard fun x hx => hx.1
  have hn : (H d).ncard + (H d)ᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have : (H d)ᶜ.ncard < {y | y ∈ H d ∧ tr.awake y t ∧ tr.JoinedAt y t}.ncard := h
  omega

/-- **The count shapes from the counts after a start `a`** (the look-ahead budget clamped at
`b`), for the slots `s ≥ σ₀` whose slot point `t_s + Δ` is at or after `a`: `2 f_d < n` at
`d ∈ [a, b]` from the count at `d` charged at `min (d + 5Δ) b ≥ d`, and at `d ∈ [0, a)` from the
count at `a` (faults only grow; `a ≤ b` unless `a ≤ 0`); the slot count at
`d ∈ [t_s + Δ, t_s + 6Δ]` from the count at `t_s + Δ` charged at `min (t_s + 6Δ) b ≥ d`, and the
late count likewise from `t_s + 2Δ`. -/
private theorem sleepyBoundsFrom_of_faultBoundAt (hanti : Antitone H) {a b : Time} {σ₀ : Nat}
    (hσ : a ≤ sp.ts σ₀ + sp.Δ) (hab : a ≤ max b 0)
    (hfb : ∀ t, 0 ≤ t → a ≤ t → t ≤ b → tr.FaultBoundAt H t (min (t + 5 * sp.Δ) b)) :
    Compose.Growing.SleepyBoundsFrom tr H σ₀ b := by
  have hΔ := sp.toParams.hΔ
  refine ⟨fun d h0 hdb => ?_, fun s d hs h1 hdb h6 => ?_, fun s d hs h1 hdb h7 => ?_⟩
  · rcases le_or_gt a d with had | hda
    · exact two_faults_lt_of_faultBoundAt
        (RunTrace.FaultBoundAt.mono_right hanti (le_min (by linarith) hdb) (hfb d h0 had hdb))
    · have hab' : a ≤ b := (le_max_iff.mp hab).resolve_right (by linarith)
      exact two_faults_lt_of_faultBoundAt (RunTrace.FaultBoundAt.mono_right hanti
        (le_min (by linarith) hdb) (hfb a (by linarith) le_rfl hab'))
  · have hts := Compose.ts_le_ts (sp := sp) hs
    have h0 := Compose.Growing.ts_natCast_nonneg (sp := sp) s
    have h := hfb (sp.ts s + sp.Δ) (by linarith) (by linarith) (h1.trans hdb)
    exact RunTrace.FaultBoundAt.mono_right hanti (le_min (by linarith) hdb) h
  · have hts := Compose.ts_le_ts (sp := sp) hs
    have h0 := Compose.Growing.ts_natCast_nonneg (sp := sp) s
    have h := hfb (sp.ts s + 2 * sp.Δ) (by linarith) (by linarith) (h1.trans hdb)
    exact RunTrace.FaultBoundAt.mono_right hanti (le_min (by linarith) hdb) h

end Lift

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

set_option linter.unusedVariables false in
/-- **Engine readiness under growing faults.** An engine node ready at `t ∈ [0, horizon]` is ready
at `t` in the canonical trace: its key is honest at `t` and awake throughout the catch-up window.
Validity is not used; the premise keeps the interface of the other transports. -/
theorem ready_transport_at (hv : rho.ExecutionValid) {c : Time} {v : V} {t : Time}
    (ht : 0 ≤ t) (hth : t ≤ rho.horizon) (hr : rho.point.Ready c v t) :
    Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho) c (rho.ownKey v) t := by
  have hkey : rho.key (rho.ownKey v) = v := rho.key.apply_symm_apply v
  refine ⟨honest_ownKey_at S rho hr.1 hth, fun τ hτ hτt => ?_⟩
  rw [simTraceAt_awake_iff, awakeAt_iff, hkey]
  exact ⟨hr.2 τ hτ hτt, (le_max_left _ _).trans hτ, hτt.trans hth⟩

/-- **The sleepy counts under growing faults.** Under the L0 sleepy budget with look-ahead `5Δ`
on `[a, b]` (`b ≤ horizon`), at every `t ∈ [max a 0, b]` the keys compromised by
`min (t + 5Δ) b` are fewer than the keys honest then, awake and joined at `t`. The engine count is
charged at `lookAhead (5Δ) t ≥ min (t + 5Δ) b`; compromise only grows, and a ready node is
honest, awake and (by its catch-up) joined at `t`. -/
private theorem sleepy_faultBoundAt (hv : rho.ExecutionValid) {a b : Time} (hb : b ≤ rho.horizon)
    (hhalf : rho.point.SleepyOn (1 / 2) (Regimes.catchUp (S.params (pubOf E) hn))
      (5 * (S.params (pubOf E) hn).Δ) a b)
    {t : Time} (ht : 0 ≤ t) (hat : a ≤ t) (htb : t ≤ b) :
    (simTraceAt S rho hn).FaultBoundAt (honestKeysAt S rho) t
      (min (t + 5 * (S.params (pubOf E) hn).Δ) b) := by
  classical
  have hΔ := (S.params (pubOf E) hn).toParams.hΔ
  set sp := S.params (pubOf E) hn
  set c := Regimes.catchUp sp
  set d' := min (t + 5 * sp.Δ) b
  set D := rho.point.lookAhead (5 * sp.Δ) t
  have hd'D : d' ≤ D := min_le_min_left _ hb
  have htd' : t ≤ d' := le_min (by linarith) htb
  have hd'h : d' ≤ rho.horizon := (min_le_right _ _).trans hb
  -- the engine count on the view retained through `D`
  have hh := hhalf t hat htb
  set R := (rho.point.retain D).readyAt c t
  have hlt : (rho.faultyAt D).card < R.card := by
    have hq : ((rho.faultyAt D).card : ℚ) < R.card := by
      change (1 / 2 : ℚ) * (R.card + (rho.faultyAt D).card) < R.card at hh
      linarith
    exact_mod_cast hq
  -- the trace's compromised keys at `d'` are the engine's faults at `d' ≤ D`
  have hf : (honestKeysAt S rho d')ᶜ.ncard ≤ (rho.faultyAt D).card := by
    have heq : (honestKeysAt S rho d')ᶜ = rho.key ⁻¹' (↑(rho.faultyAt d') : Set V) := by
      ext k
      simp [mem_honestKeysAt_iff, min_eq_left hd'h]
    rw [heq, Set.ncard_preimage_of_injective_subset_range rho.key.injective
      (by simp [rho.key.surjective.range_eq]), Set.ncard_coe_finset]
    exact Finset.card_le_card (rho.faultyAt_mono hd'D)
  -- each retained-ready validator is honest at `d'`, awake and joined at `t`
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  have hcount : R.card ≤ {y | y ∈ honestKeysAt S rho d' ∧ (simTraceAt S rho hn).awake y t ∧
      (simTraceAt S rho hn).JoinedAt y t}.ncard := by
    rw [← Set.ncard_coe_finset]
    apply Set.ncard_le_ncard_of_injOn rho.ownKey
    · intro v hv'
      have hr : (rho.point.retain D).Ready c v t := (Finset.mem_filter.mp hv').2
      have hvD : v ∉ rho.faultyAt D := hr.1
      have hrt : rho.point.Ready c v t :=
        ⟨fun h => hvD (rho.faultyAt_mono (htd'.trans hd'D) h), hr.2⟩
      have hready := ready_transport_at S rho hn hv ht (htb.trans hb) hrt
      refine ⟨honest_ownKey_at S rho (fun h => hvD (rho.faultyAt_mono hd'D h)) hd'h, ?_⟩
      exact ready_implies_joined_at hrun hready.1 ht (by dsimp [c, Regimes.catchUp]; linarith)
        hready.2
    · exact rho.key.symm.injective.injOn
  exact hf.trans_lt (hlt.trans_le hcount)

/-- **The sleepy count shapes under growing faults** through `b ≤ horizon`, from the L0 sleepy
budget with look-ahead `5Δ` on `[a, b]`, for the slots `s ≥ σ₀` with `a ≤ t_{σ₀} + Δ` (and
`a ≤ b` unless `a ≤ 0`). -/
theorem sleepy_bounds_at (hv : rho.ExecutionValid) {a b : Time} (hb : b ≤ rho.horizon)
    (hhalf : rho.point.SleepyOn (1 / 2) (Regimes.catchUp (S.params (pubOf E) hn))
      (5 * (S.params (pubOf E) hn).Δ) a b)
    {σ₀ : Nat} (hσ : a ≤ (S.params (pubOf E) hn).ts σ₀ + (S.params (pubOf E) hn).Δ)
    (hab : a ≤ max b 0) :
    Compose.Growing.SleepyBoundsFrom (simTraceAt S rho hn) (honestKeysAt S rho) σ₀ b :=
  sleepyBoundsFrom_of_faultBoundAt (honestKeysAt_antitone S rho) hσ hab
    fun _ ht hat htb => sleepy_faultBoundAt S rho hn hv hb hhalf ht hat htb

end Consensus.Goldilocks.Obligations.Growing

end
