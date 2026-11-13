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
import ConsensusLean.Lemmas.Problem.Facts.Regimes
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Transport of the sleepy premises to the canonical growing trace

The engine-side premises of the finite sleepy rows under growing faults, read on the canonical
trace `simTraceAt` with the time-indexed honest keys `honestKeysAt`:

* `ready_transport_at`: an engine node ready at `t ≤ horizon` is ready at `t` in the trace, with
  honesty read at `t` (no constant-fault premise);
* `committee_faultBoundAt` (the one transport): committee η-sleepy participation for a selection
  `Sel` (`EnvPoint.CommitteeSleepyOn`, look-ahead `W ≥ 5Δ`) gives, at every `t ∈ [max a 0, b]`,
  `b ≤ horizon`, the count among the keys selected at `t` charged at `d = min (t + 5Δ) b`;
* `committee_bounds_at`: with the slot committees the selections (`hK`), the committee count
  shapes `CommitteeBoundsFrom σ₀` through `b`;
* `sleepy_bounds_at`: the L0 sleepy budget with look-ahead `5Δ` on `[a, b]`
  (`EnvPoint.SleepyOn` on the view retained through `lookAhead (5Δ) t`) gives the population count
  `FaultBoundAt t d` (the `Sel = univ`, `η = 0` instance of `committee_faultBoundAt`), hence the
  count shapes `SleepyBoundsFrom σ₀` through `b`, for the slots whose slot point `t_s + Δ` is at
  or after `a`.

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
private theorem ready_implies_joined_at {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    {t c : Time} (hy : y ∈ H t) (ht : 0 ≤ t) (hc : 8 * sp.Δ ≤ c + 1)
    (hawake : ∀ u : Time, max 0 (t - c - 1) ≤ u → u ≤ t → tr.awake y u) :
    tr.awake y t ∧ tr.JoinedAt y t := by
  obtain ⟨hw, hj⟩ := Compose.ready_implies_joined_of (hrun.upTo ht) hy ht hc
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

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

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

/-- **The committee sleepy counts under growing faults (the one transport).** Under committee
η-sleepy participation for the selection `Sel` on `[a, b]` (`b ≤ horizon`) with `θ ≥ 1/2`, a
catch-up `c` that covers joining (`8Δ ≤ c + 1`) and a look-ahead `W ≥ 5Δ`, at every
`t ∈ [max a 0, b]` with `Sel t` nonempty, the keys selected at `t` compromised by `min (t + 5Δ) b`
are fewer than those honest then, awake and joined at `t`. The engine count is charged at
`lookAhead W t ≥ min (t + 5Δ) b` (its η-look-back form only enlarges the denominator); compromise
only grows, and a ready node is honest, awake and (by its catch-up) joined at `t`. The population
count `sleepy_faultBoundAt` is its `Sel = univ`, `η = 0` instance. -/
theorem committee_faultBoundAt (hv : rho.ExecutionValid) {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun (runProposer S rho hn) (digestOf S rho)
      (honestKeysAt S rho) (simTraceAt S rho hn) ini)
    {Sel : Time → Finset V} {θ : ℚ} {η c W a b : Time} (hθ : 1 / 2 ≤ θ)
    (hc : 8 * (S.params (pubOf E) hn).Δ ≤ c + 1) (hW : 5 * (S.params (pubOf E) hn).Δ ≤ W)
    (hb : b ≤ rho.horizon) (hsl : rho.point.CommitteeSleepyOn Sel θ η c W a b)
    {t : Time} (ht : 0 ≤ t) (hat : a ≤ t) (htb : t ≤ b) (hne : (Sel t).Nonempty) :
    (rho.key ⁻¹' ↑(Sel t) ∩
        (honestKeysAt S rho (min (t + 5 * (S.params (pubOf E) hn).Δ) b))ᶜ).ncard <
      (rho.key ⁻¹' ↑(Sel t) ∩
        {y | y ∈ honestKeysAt S rho (min (t + 5 * (S.params (pubOf E) hn).Δ) b) ∧
          (simTraceAt S rho hn).awake y t ∧ (simTraceAt S rho hn).JoinedAt y t}).ncard := by
  classical
  have hΔ := (S.params (pubOf E) hn).toParams.hΔ
  set sp := S.params (pubOf E) hn
  set d' := min (t + 5 * sp.Δ) b
  set D := rho.point.lookAhead W t
  have hd'D : d' ≤ D := min_le_min (by linarith) hb
  have htd' : t ≤ d' := le_min (by linarith) htb
  have hd'h : d' ≤ rho.horizon := (min_le_right _ _).trans hb
  -- the committee count on the view retained through `D`
  set R := (rho.point.retain D).readyAt c t ∩ Sel t
  set F := (rho.point.retain D).faultyAt t ∩ Sel t
  have hRF : Disjoint R F := Finset.disjoint_left.2 fun v hvR hvF =>
    (Finset.mem_filter.mp (Finset.mem_inter.mp hvR).1).2.1 (Finset.mem_inter.mp hvF).1
  have hmain : θ * ((R.card : ℚ) + F.card) < R.card := by
    have hh := hsl t hat htb hne
    dsimp only at hh
    by_cases hη : η ≤ 0
    · simp only [hη, ↓reduceIte] at hh
      push_cast at hh
      exact hh
    · simp only [hη, ↓reduceIte] at hh
      have hsub : R ∪ F ⊆ ((rho.point.retain D).readyAt c t ∪
          (rho.point.retain D).awakeIn (max 0 (t - η)) t ∪ (rho.point.retain D).faultyAt t) ∩
          Sel t := by
        intro v hv
        rcases Finset.mem_union.mp hv with hv | hv <;>
          obtain ⟨hv, hvS⟩ := Finset.mem_inter.mp hv <;>
          simp [hv, hvS]
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hRF] at hcard
      exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by linarith)).trans_lt hh
  have hlt : F.card < R.card := by
    have h2 : (1 / 2 : ℚ) * ((R.card : ℚ) + F.card) ≤ θ * ((R.card : ℚ) + F.card) :=
      mul_le_mul_of_nonneg_right hθ (by positivity)
    have : (F.card : ℚ) < R.card := by linarith
    exact_mod_cast this
  -- the trace's compromised selected keys at `d'` are the engine's selected faults at `d' ≤ D`
  have hf : (rho.key ⁻¹' ↑(Sel t) ∩ (honestKeysAt S rho d')ᶜ).ncard ≤ F.card := by
    have heq : rho.key ⁻¹' ↑(Sel t) ∩ (honestKeysAt S rho d')ᶜ =
        rho.key ⁻¹' ↑(rho.faultyAt d' ∩ Sel t) := by
      ext k
      simp [mem_honestKeysAt_iff, min_eq_left hd'h, and_comm]
    rw [heq, Set.ncard_preimage_of_injective_subset_range rho.key.injective
      (by simp [rho.key.surjective.range_eq]), Set.ncard_coe_finset]
    exact Finset.card_le_card (Finset.inter_subset_inter (rho.faultyAt_mono hd'D) le_rfl)
  -- each selected retained-ready validator is honest at `d'`, awake and joined at `t`
  have hcount : R.card ≤ (rho.key ⁻¹' ↑(Sel t) ∩ {y | y ∈ honestKeysAt S rho d' ∧
      (simTraceAt S rho hn).awake y t ∧ (simTraceAt S rho hn).JoinedAt y t}).ncard := by
    rw [← Set.ncard_coe_finset]
    apply Set.ncard_le_ncard_of_injOn rho.ownKey
    · intro v hv'
      obtain ⟨hvr, hvS⟩ := Finset.mem_inter.mp (Finset.mem_coe.mp hv')
      have hr : (rho.point.retain D).Ready c v t := (Finset.mem_filter.mp hvr).2
      have hvD : v ∉ rho.faultyAt D := hr.1
      have hrt : rho.point.Ready c v t :=
        ⟨fun h => hvD (rho.faultyAt_mono (htd'.trans hd'D) h), hr.2⟩
      have hready := ready_transport_at S rho hn hv ht (htb.trans hb) hrt
      have hkey : rho.key (rho.ownKey v) = v := rho.key.apply_symm_apply v
      refine ⟨show rho.key (rho.ownKey v) ∈ (Sel t : Set V) by rw [hkey]; exact hvS,
        honest_ownKey_at S rho (fun h => hvD (rho.faultyAt_mono hd'D h)) hd'h, ?_⟩
      exact ready_implies_joined_at hrun hready.1 ht hc hready.2
    · exact rho.key.symm.injective.injOn
  exact hf.trans_lt (hlt.trans_le hcount)

/-- **The sleepy counts under growing faults.** Under the L0 sleepy budget with look-ahead `5Δ`
on `[a, b]` (`b ≤ horizon`), at every `t ∈ [max a 0, b]` the keys compromised by
`min (t + 5Δ) b` are fewer than the keys honest then, awake and joined at `t`: the full-selection
(`Sel = univ`, `η = 0`) instance of `committee_faultBoundAt`. -/
private theorem sleepy_faultBoundAt (hv : rho.ExecutionValid)
    {a b : Time} (hb : b ≤ rho.horizon)
    (hhalf : rho.point.SleepyOn (1 / 2) (Regimes.catchUp (S.params (pubOf E) hn))
      (5 * (S.params (pubOf E) hn).Δ) a b)
    {t : Time} (ht : 0 ≤ t) (hat : a ≤ t) (htb : t ≤ b) :
    (simTraceAt S rho hn).FaultBoundAt (honestKeysAt S rho) t
      (min (t + 5 * (S.params (pubOf E) hn).Δ) b) := by
  have hΔ := (S.params (pubOf E) hn).toParams.hΔ
  have hsl : rho.point.EtaSleepyOn (1 / 2) 0 (Regimes.catchUp (S.params (pubOf E) hn))
      (5 * (S.params (pubOf E) hn).Δ) a b := fun u hau hub =>
    EnvPoint.etaReadyAbove_zero_iff.2 (hhalf u hau hub)
  have h := committee_faultBoundAt S rho hn hv (simTraceAt_goldilocksRun S rho hn hv)
    (Sel := fun _ => Finset.univ) le_rfl (by dsimp [Regimes.catchUp]; linarith) le_rfl hb
    (hsl.committee_univ le_rfl (by norm_num) (by norm_num)) ht hat htb
    ⟨rho.key ⟨0, hn⟩, Finset.mem_univ _⟩
  simp only [Finset.coe_univ, Set.preimage_univ, Set.univ_inter] at h
  exact h

/-- **The sleepy count shapes under growing faults** through `b ≤ horizon`, from the L0 sleepy
budget with look-ahead `5Δ` on `[a, b]`, for the slots `s ≥ σ₀` with `a ≤ t_{σ₀} + Δ` (and
`a ≤ b` unless `a ≤ 0`). -/
theorem sleepy_bounds_at (hv : rho.ExecutionValid)
    {a b : Time} (hb : b ≤ rho.horizon)
    (hhalf : rho.point.SleepyOn (1 / 2) (Regimes.catchUp (S.params (pubOf E) hn))
      (5 * (S.params (pubOf E) hn).Δ) a b)
    {σ₀ : Nat} (hσ : a ≤ (S.params (pubOf E) hn).ts σ₀ + (S.params (pubOf E) hn).Δ)
    (hab : a ≤ max b 0) :
    Compose.Growing.SleepyBoundsFrom (simTraceAt S rho hn) (honestKeysAt S rho) σ₀ b :=
  sleepyBoundsFrom_of_faultBoundAt (honestKeysAt_antitone S rho) hσ hab
    fun _ ht hat htb => sleepy_faultBoundAt S rho hn hv hb hhalf ht hat htb

/-- **The committee count shapes under growing faults** through `b ≤ horizon`, for a slot
dictionary `K` whose slot-`slot t` committee is the selection at `t` (`hK`, nonempty committees),
from committee η-sleepy participation on `[a, b]` (`committee_faultBoundAt`), for the slots
`s ≥ σ₀` with `a ≤ t_{σ₀} + Δ`: CS at `d ∈ [t_s + Δ, min b (t_s + 6Δ)]` from the count at
`t_s + Δ`, and CS2 at `d ∈ [t_s, min b (t_s + 2Δ)]` from the count at `min (t_s + Δ) b`, both
charged at a time `≥ d` (compromise only grows). -/
theorem committee_bounds_at (hv : rho.ExecutionValid) {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun (runProposer S rho hn) (digestOf S rho)
      (honestKeysAt S rho) (simTraceAt S rho hn) ini)
    {Sel : Time → Finset V} {K : SA.CommitteeDict (Fintype.card V)}
    (hK : ∀ t, 0 ≤ t → ∀ y,
      y ∈ K.committee ((S.params (pubOf E) hn).slot t) ↔ rho.key y ∈ Sel t)
    (hne : ∀ s, (K.committee s).Nonempty)
    {θ : ℚ} {η c W a b : Time} (hθ : 1 / 2 ≤ θ) (hc : 8 * (S.params (pubOf E) hn).Δ ≤ c + 1)
    (hW : 5 * (S.params (pubOf E) hn).Δ ≤ W) (hb : b ≤ rho.horizon)
    (hsl : rho.point.CommitteeSleepyOn Sel θ η c W a b)
    {σ₀ : Nat} (hσ : a ≤ (S.params (pubOf E) hn).ts σ₀ + (S.params (pubOf E) hn).Δ)
    (hab : a ≤ max b 0) :
    Compose.Growing.CommitteeBoundsFrom (simTraceAt S rho hn) (honestKeysAt S rho) K σ₀ b := by
  have hΔ := (S.params (pubOf E) hn).toParams.hΔ
  set sp := S.params (pubOf E) hn
  have hanti := honestKeysAt_antitone S rho
  -- the count at a time `t ∈ [max a 0, b]`, on the committee of its slot
  have hcnt : ∀ (t : Time), 0 ≤ t → a ≤ t → t ≤ b →
      (K.committee (sp.slot t) ∩ (honestKeysAt S rho (min (t + 5 * sp.Δ) b))ᶜ).ncard <
        (K.committee (sp.slot t) ∩ {y | y ∈ honestKeysAt S rho (min (t + 5 * sp.Δ) b) ∧
          (simTraceAt S rho hn).awake y t ∧ (simTraceAt S rho hn).JoinedAt y t}).ncard := by
    intro t ht hat htb
    have hKS : K.committee (sp.slot t) = rho.key ⁻¹' ↑(Sel t) :=
      Set.ext fun y => (hK t ht y).trans Iff.rfl
    obtain ⟨y, hy⟩ := hne (sp.slot t)
    rw [hKS]
    exact committee_faultBoundAt S rho hn hv hrun hθ hc hW hb hsl ht hat htb
      ⟨rho.key y, (hK t ht y).1 hy⟩
  have hts1 : ∀ s : Nat, sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := fun s => by
    simp only [SA.SAParams.ts]; push_cast; ring
  refine ⟨fun s d hs h1 hdb h6 => ?_, fun s d hs h0 hdb h2 => ?_⟩
  · have hσs := Compose.ts_le_ts (sp := sp) hs
    have h0 := Compose.Growing.ts_natCast_nonneg (sp := sp) s
    have hsl' : sp.slot (sp.ts s + sp.Δ) = s :=
      SA.slot_of_mem sp s (by linarith) (by rw [hts1]; linarith)
    have h := hcnt (sp.ts s + sp.Δ) (by linarith) (by linarith) (h1.trans hdb)
    rw [hsl'] at h
    have hdd : d ≤ min (sp.ts s + sp.Δ + 5 * sp.Δ) b := le_min (by linarith) hdb
    exact (Set.ncard_le_ncard (Set.inter_subset_inter_right _
      (Set.compl_subset_compl.2 (hanti hdd)))).trans_lt (h.trans_le (Set.ncard_le_ncard
        fun y ⟨hyK, hyH, hyw⟩ => ⟨hyK, hanti hdd hyH, (Compose.Growing.mem_awakeJoined_projAC
          hrun).2 hyw⟩))
  · have hσs := Compose.ts_le_ts (sp := sp) hs
    have hs0 := Compose.Growing.ts_natCast_nonneg (sp := sp) s
    have hb0 : 0 ≤ b := by linarith
    have hab' : a ≤ b := (le_max_iff.mp hab).elim id fun h => h.trans hb0
    set t := min (sp.ts s + sp.Δ) b with ht
    have htl : sp.ts s ≤ t := le_min (by linarith) (by linarith)
    have htu : t ≤ sp.ts s + sp.Δ := min_le_left _ _
    have hsl' : sp.slot t = s := SA.slot_of_mem sp s htl (by rw [hts1]; linarith)
    have h := hcnt t (by linarith) (le_min (by linarith) hab') (min_le_right _ _)
    rw [hsl'] at h
    have hdd : d ≤ min (t + 5 * sp.Δ) b := by
      refine le_min ?_ hdb
      rw [ht, ← min_add_add_right]
      exact le_min (by linarith) (by linarith)
    have hle : (K.committee s ∩ (honestKeysAt S rho d)ᶜ).ncard ≤
        (K.committee s ∩ (honestKeysAt S rho (min (t + 5 * sp.Δ) b))ᶜ).ncard :=
      Set.ncard_le_ncard (Set.inter_subset_inter_right _ (Set.compl_subset_compl.2 (hanti hdd)))
    have hJ := Set.ncard_le_ncard (s := K.committee s ∩ {y | y ∈ honestKeysAt S rho
      (min (t + 5 * sp.Δ) b) ∧ (simTraceAt S rho hn).awake y t ∧
        (simTraceAt S rho hn).JoinedAt y t})
      (t := K.committee s ∩ honestKeysAt S rho (min (t + 5 * sp.Δ) b)) fun _ hy => ⟨hy.1, hy.2.1⟩
    have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard (K.committee s)
      (honestKeysAt S rho (min (t + 5 * sp.Δ) b))
    rw [Set.sdiff_eq] at hsplit
    omega

end Consensus.Goldilocks.Obligations.Growing

end
