module
public import ConsensusLean.Proofs.RegimesRealizable.Basic
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Growing-fault realizability witnesses

The transaction source is initially honest and is compromised strictly after
its submission and protected read. The selected proposer and the later reader
are different validators and stay honest throughout.
-/

namespace Consensus.Shape
open Blocks
open Consensus.Model (pubOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
variable {V : Type} [Fintype V] [DecidableEq V]

/-- A single compromise at `κ`, with the only transaction submitted to its source at zero. -/
def growthPoint (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V)
    (Δ : Time) (hΔ : 0 < Δ) (ΔF : Time) (hΔF : 0 < ΔF)
    (awake : V → Time → Bool) (H κ : Time) : EnvPoint V :=
  ⟨⟨Δ, hΔ, ΔF, hΔF, awake⟩, fun t => if κ ≤ t then {key ⟨0, by omega⟩} else ∅,
    by
      intro a b hab
      dsimp only
      split_ifs with ha hb
      · exact Finset.Subset.refl _
      · exact False.elim (hb (ha.trans hab))
      · exact Finset.empty_subset _
      · exact Finset.Subset.refl _,
    H, fun v t => if v = key ⟨0, by omega⟩ ∧ t = 0 then [42] else []⟩

theorem growthPoint_eq (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V)
    (Δ : Time) (hΔ : 0 < Δ) (ΔF : Time) (hΔF : 0 < ΔF)
    (awake : V → Time → Bool) (H κ : Time) :
    growthPoint key hn Δ hΔ ΔF hΔF awake H κ =
      { (realPoint key hn Δ hΔ ΔF hΔF awake H) with
        faultyAt := fun t => if κ ≤ t then {key ⟨0, by omega⟩} else ∅
        faultyAt_mono := by
          intro a b hab
          dsimp only
          split_ifs with ha hb
          · exact Finset.Subset.refl _
          · exact False.elim (hb (ha.trans hab))
          · exact Finset.empty_subset _
          · exact Finset.Subset.refl _
        submit := fun v t => if v = key ⟨0, by omega⟩ ∧ t = 0 then [42] else [] } := by
  rw [realPoint_eq]
  rfl

section Point
variable (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V)
  {Δ : Time} (hΔ : 0 < Δ) {ΔF : Time} (hΔF : 0 < ΔF)
  (awake : V → Time → Bool) (H κ : Time)

theorem growthPoint_faulty (t : Time) :
    (growthPoint key hn Δ hΔ ΔF hΔF awake H κ).faultyAt t =
      if κ ≤ t then {kv key hn 0 (by decide)} else ∅ := by rfl

/-- The nondecreasing profile has an actual strict increase inside the execution. -/
theorem growthPoint_strict_growth (hκ : 0 < κ) (hH : κ ≤ H) :
    ∃ t₁ t₂ : Time, 0 ≤ t₁ ∧ t₁ < t₂ ∧ t₂ ≤ H ∧
      (growthPoint key hn Δ hΔ ΔF hΔF awake H κ).faultyAt t₁ ⊂
        (growthPoint key hn Δ hΔ ΔF hΔF awake H κ).faultyAt t₂ := by
  refine ⟨0, κ, le_rfl, hκ, hH, ?_⟩
  simp only [growthPoint_faulty, not_le.mpr hκ, le_rfl, ↓reduceIte]
  exact Finset.empty_ssubset_singleton

theorem growthPoint_honest {j : Nat} (hj : j < 5) (h0 : j ≠ 0) (t : Time) :
    (growthPoint key hn Δ hΔ ΔF hΔF awake H κ).HonestAt (kv key hn j hj) t := by
  simp only [EnvPoint.HonestAt, growthPoint_faulty]
  split_ifs
  · simpa only [Finset.mem_singleton] using (kv_ne key hn (hj' := by decide) h0)
  · exact Finset.notMem_empty _

/-- Every validator ready in the fully charged static view is ready in every retained view. -/
theorem growthPoint_ready_subset (c t d : Time) :
    (realPoint key hn Δ hΔ ΔF hΔF awake H).readyAt c t ⊆
      ((growthPoint key hn Δ hΔ ΔF hΔF awake H κ).retain d).readyAt c t := by
  intro v hv
  simp only [EnvPoint.readyAt, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  rw [realPoint_eq] at hv
  refine ⟨?_, hv.2⟩
  change v ∉ (if κ ≤ d then {kv key hn 0 (by decide)} else ∅)
  split_ifs
  · exact hv.1
  · exact Finset.notMem_empty _

theorem growthPoint_eta {θ : ℚ} (hθ : 0 ≤ θ ∧ θ ≤ 1 / 2)
    (hready : ∀ c t, Fintype.card V ≤
      ((realPoint key hn Δ hΔ ΔF hΔF awake H).readyAt c t).card + 2)
    (η c W a b : Time) :
    (growthPoint key hn Δ hΔ ΔF hΔF awake H κ).EtaSleepyOn θ η c W a b := by
  intro t _ _
  apply etaReadyAbove_of_card hn hθ
  exact (hready c t).trans (Nat.add_le_add_right
    (Finset.card_le_card (growthPoint_ready_subset key hn hΔ hΔF awake H κ c t _)) 2)

end Point

section Activity
variable (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V)
  {Δ : Time} (hΔ : 0 < Δ) {ΔF : Time} (hΔF : 0 < ΔF) (H κ : Time)

/-- The permanently honest selected proposer satisfies every fitting recurrence, including hold. -/
theorem growthPoint_holds (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (hf : ProgressFits K F) (cap : Capability) (i : K.Idx) (c s e : Time) :
    shapeHolds F (K.progress cap i) c s e
      (growthPoint key hn Δ hΔ ΔF hΔF allAwake H κ)
      (key, extremalSel F (growthPoint key hn Δ hΔ ΔF hΔF allAwake H κ).env) := by
  have hfit := hf cap i (pubOf (growthPoint key hn Δ hΔ ΔF hΔF allAwake H κ).env)
  cases hreq : K.progress cap i with
  | recur ρ =>
    rw [hreq] at hfit
    change ∀ s, (F _).skel.proposerSel s = .sized 1 at hfit
    apply patternRecurrence_of_all
    intro sl j _
    have hmem := extremalSel_proposer_mem F hfit (by omega) (sl + j)
    refine ⟨⟨⟨1, by omega⟩, (hmem _).mpr rfl⟩, fun k hk => ?_⟩
    have hk1 : k = ⟨1, by omega⟩ := Fin.ext ((hmem k).mp hk)
    subst hk1
    exact ⟨⟨growthPoint_honest key hn hΔ hΔF allAwake H κ (by decide) (by decide) _,
      fun _ _ _ => allAwake_apply _ _⟩,
      growthPoint_honest key hn hΔ hΔF allAwake H κ (by decide) (by decide) _⟩
  | notReadyAtMost m =>
    intro t _ _ _
    have hr := growthPoint_ready_subset key hn hΔ hΔF allAwake H κ c t t
    have hc := Finset.card_le_card hr
    have he : ((growthPoint key hn Δ hΔ ΔF hΔF allAwake H κ).retain t).readyAt c t =
        (growthPoint key hn Δ hΔ ΔF hΔF allAwake H κ).readyAt c t := by rfl
    rw [he] at hc
    have hm := m.pos
    exact (allAwake_readyAt key hn hΔ hΔF H c t).trans
      (by omega)

/-- The source's pre-compromise read and its sole submission remain active at a later reader. -/
theorem growthPoint_active (c start D : Time) (hκ : 0 < κ) (hκΔ : κ < Δ) (hκH : κ ≤ H)
    (hH : max 0 start + Δ + D ≤ H) :
    GrowthActive c start D (growthPoint key hn Δ hΔ ΔF hΔF allAwake H κ) := by
  refine ⟨kv key hn 0 (by decide), kv key hn 1 (by decide), 42, 0, 0, κ, H,
    kv_ne key hn (by decide), le_rfl, le_rfl, hκ,
    by simpa only [growthPoint_eq, realPoint_eq, zero_add] using hκΔ, hκH, le_rfl, hH,
    ⟨?_, fun _ _ _ => allAwake_apply _ _⟩, allAwake_apply _ _, ?_, ?_, ?_, ?_,
    ⟨growthPoint_honest key hn hΔ hΔF allAwake H κ (by decide) (by decide) _,
      fun _ _ _ => allAwake_apply _ _⟩,
    ⟨growthPoint_honest key hn hΔ hΔF allAwake H κ (by decide) (by decide) _,
      fun _ _ _ => allAwake_apply _ _⟩⟩
  · simp only [EnvPoint.HonestAt, growthPoint_faulty, not_le.mpr hκ, ↓reduceIte,
      Finset.notMem_empty, not_false_eq_true]
  · simp only [growthPoint_eq, and_self, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false]
  · intro v t hx
    simp only [growthPoint_eq] at hx
    split_ifs at hx with h
    · exact h.1
    · exact False.elim (List.not_mem_nil hx)
  · simp only [growthPoint_faulty, not_le.mpr hκ, ↓reduceIte, Finset.notMem_empty,
      not_false_eq_true]
  · simp only [growthPoint_faulty, le_rfl, ↓reduceIte, Finset.mem_singleton]

/-- The same sole submission is an active liveness query. -/
theorem growthPoint_txLiveActive (c start D : Time) (hκ : 0 < κ)
    (hH : max 0 start + Δ + D ≤ H) :
    (growthPoint key hn Δ hΔ ΔF hΔF allAwake H κ).TxLiveActive c start D := by
  refine ⟨42, 0, H, kv key hn 0 (by decide), kv key hn 1 (by decide), le_rfl,
    ?_, allAwake_apply _ _, ?_, kv_ne key hn (by decide), ?_, hH, le_rfl,
    growthPoint_honest key hn hΔ hΔF allAwake H κ (by decide) (by decide) _,
    fun _ _ _ => allAwake_apply _ _⟩
  · simp only [EnvPoint.HonestAt, growthPoint_faulty, not_le.mpr hκ, ↓reduceIte,
      Finset.notMem_empty, not_false_eq_true]
  · simp only [growthPoint_eq, and_self, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false]
  · intro t
    have hne : kv key hn 1 (by decide) ≠ key ⟨0, by omega⟩ :=
      kv_ne key hn (hj' := by decide) (by decide)
    simp only [growthPoint_eq, hne, false_and,
      ↓reduceIte, List.not_mem_nil, not_false_eq_true]

end Activity

/-- After the compromise the retained cohort is the ordinary one-fault cohort. -/
theorem growthPoint_cohort (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V)
    {Δ : Time} (hΔ : 0 < Δ) {ΔF : Time} (hΔF : 0 < ΔF)
    (H κ d a b : Time) (hκd : κ ≤ d) :
    let p := growthPoint key hn Δ hΔ ΔF hΔF (asleepAlways (kv key hn 2 (by decide))) H κ
    (p.retain d).NoSleepOn a b ∧ (p.retain d).CohortOn a b := by
  have h := asleepAlways_cohort key hn hΔ hΔF H a b
  rw [realPoint_eq] at h
  dsimp only
  simp only [growthPoint_eq, realPoint_eq, EnvPoint.retain, ite_eq_left hκd]
  exact h

/-- A canonical growing run, with active progress and a later reader after the source compromise. -/
theorem growing_live_witness (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V)
    (ha : K.params.Admissible) (hf : ProgressFits K F) (cap : Capability) (i : K.Idx)
    (Δ ΔF g start progressStart : Time) (hΔ1 : 1 < Δ) (hΔF1 : 1 < ΔF) :
    ∃ r : (Sys F V).Run, (Sys F V).Valid r ∧ ¬ (Sys F V).Excuse r ∧
      ((Sys F V).pt r).env.ΔAC = Δ ∧ ((Sys F V).pt r).env.ΔFG = ΔF ∧
      CommLog.EagerFrom ((Sys F V).pt r) ((Sys F V).log r) g ∧
      ((Sys F V).pt r).SleepyOn K.params.θ ((Sys F V).cDur K r)
        ((Sys F V).aheadDur K r) 0 ((Sys F V).pt r).horizon ∧
      ((Sys F V).pt r).HealthyOn K.params.β g ((Sys F V).pt r).horizon ∧
      (Sys F V).prog (shapeProgress F V) K cap i progressStart ((Sys F V).pt r).horizon r ∧
      ((Sys F V).pt r).TxLiveActive ((Sys F V).cDur K r) start ((Sys F V).lat K cap i r) ∧
      GrowthActive ((Sys F V).cDur K r) start ((Sys F V).lat K cap i r) ((Sys F V).pt r) ∧
      ProgressActive F K cap i progressStart r.2 := by
  have hΔ := zero_lt_one.trans hΔ1
  have hΔF := zero_lt_one.trans hΔF1
  let E : Env V := ⟨Δ, hΔ, ΔF, hΔF, allAwake⟩
  let H := max 0 start + max 0 progressStart + Δ + (K.params.latency cap i : Time) * Δ +
    progLen F K cap i E + 2
  have hL := progLen_nonneg F K cap i E
  have hlat : 0 ≤ (K.params.latency cap i : Time) * Δ := mul_nonneg (by positivity) hΔ.le
  have h0 : 0 ≤ max 0 start := le_max_left _ _
  have hp0 : 0 ≤ max 0 progressStart := le_max_left _ _
  have hH : 1 ≤ H := by dsimp [H]; linarith
  let p := growthPoint key hn Δ hΔ ΔF hΔF allAwake H 1
  obtain ⟨hash, relay, events, hv, hnc, he⟩ := real_run key F p
    (show 0 ≤ H from le_trans (by decide : (0 : Time) ≤ 1) hH) g
  let rho := Model.Run.mk (F := compiled F) (E := p.env) p.faultyAt p.faultyAt_mono H
    events key (extremalSel F p.env) p.submit relay hash
  refine ⟨⟨p.env, rho⟩, hv, hnc, rfl, rfl, Model.sysOf_eagerFrom rho he,
    ?_, ?_, growthPoint_holds key hn hΔ hΔF H 1 F K hf cap i _ _ _,
    growthPoint_txLiveActive key hn hΔ hΔF H 1 _ _ _ (by decide) ?_,
    growthPoint_active key hn hΔ hΔF H 1 _ _ _ (by decide) hΔ1 hH ?_, ?_⟩
  · have hη := growthPoint_eta key hn hΔ hΔF allAwake H 1 ha.θ_range
      (fun c t => (allAwake_readyAt key hn hΔ hΔF H c t).trans (Nat.le_succ _))
      0 ((Sys F V).cDur K ⟨p.env, rho⟩) ((Sys F V).aheadDur K ⟨p.env, rho⟩) 0 H
    intro t ht hb
    exact (hη t ht hb).readyAbove ha.θ_range.1
  · refine ⟨?_, fun v t _ _ _ => allAwake_apply v t⟩
    change ((p.faultyAt H).card : ℚ) < K.params.β * Fintype.card V
    rw [growthPoint_faulty, ite_eq_left hH, Finset.card_singleton]
    exact one_lt_beta_mul_card hn ha.β_range
  · change max 0 start + Δ + (K.params.latency cap i : Time) * Δ ≤ H
    dsimp [H]; linarith
  · change max 0 start + Δ + (K.params.latency cap i : Time) * Δ ≤ H
    dsimp [H]; linarith
  · change max progressStart 0 + progLen F K cap i E ≤ H
    rw [max_comm progressStart 0]
    dsimp [H]; linarith

/-- An outage with a protected source compromised after arming and a surviving reader. -/
theorem growing_outage_witness (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V)
    (ha : K.params.Admissible) (Δ ΔF : Time) (k : Nat)
    (hΔ1 : 1 < Δ) (hΔF1 : 1 < ΔF) :
    ∃ r T b₀ b₁ u κ, (Sys F V).Valid r ∧ ¬ (Sys F V).Excuse r ∧
      ((Sys F V).pt r).env.ΔAC = Δ ∧ ((Sys F V).pt r).env.ΔFG = ΔF ∧
      (Sys F V).Outage K T b₀ b₁ r ∧
      OutageActive ((Sys F V).cDur K r) ((K.params.recovery : Time) * Δ) T b₀ b₁
        ((Sys F V).pt r) ∧ (k : Time) * Δ ≤ T ∧
      ((Sys F V).pt r).Ready ((Sys F V).cDur K r) u T ∧ T < κ ∧
      u ∈ ((Sys F V).pt r).faultyAt κ ∧ ∃ w t, (Sys F V).recoveryAt K b₁ r ≤ t ∧
        t ≤ ((Sys F V).pt r).horizon ∧ κ ≤ t ∧
        ((Sys F V).pt r).Ready ((Sys F V).cDur K r) w t := by
  have hΔ := zero_lt_one.trans hΔ1
  have hΔF := zero_lt_one.trans hΔF1
  let T := (k : Time) * Δ
  let κ := T + 1
  let b₀ := T + (K.params.lag : Time) * Δ + Δ
  let b₁ := b₀ + Δ
  let H := b₁ + (K.params.recovery : Time) * Δ
  have hT : 0 ≤ T := mul_nonneg (by positivity) hΔ.le
  have hl : (0 : Time) ≤ (K.params.lag : Time) * Δ := mul_nonneg (by positivity) hΔ.le
  have hr : (0 : Time) ≤ (K.params.recovery : Time) * Δ := mul_nonneg (by positivity) hΔ.le
  have hnS : (0 : Time) ≤ (K.params.noSleep : Time) * Δ := mul_nonneg (by positivity) hΔ.le
  have hcA : (0 : Time) ≤ (K.params.cohortAhead : Time) * Δ := mul_nonneg (by positivity) hΔ.le
  have hκb : κ ≤ b₁ := by dsimp [κ, b₁, b₀]; linarith
  have hκH : κ ≤ H := by dsimp [H]; linarith
  have hH0 : 0 ≤ H := by dsimp [H, b₁, b₀]; linarith
  let awake := asleepAlways (kv key hn 2 (by decide))
  let p := growthPoint key hn Δ hΔ ΔF hΔF awake H κ
  obtain ⟨hash, relay, events, hv, hnc, he⟩ := real_run key F p hH0 0
  let rho := Model.Run.mk (F := compiled F) (E := p.env) p.faultyAt p.faultyAt_mono H
    events key (extremalSel F p.env) p.submit relay hash
  let r : (Sys F V).Run := ⟨p.env, rho⟩
  have haw (j : Nat) (hj : j < 5) (hj2 : j ≠ 2) (t : Time) :
      awake (kv key hn j hj) t = true := by
    simp only [awake, asleepAlways_apply, Bool.not_eq_true', decide_eq_false_iff_not]
    exact kv_ne key hn hj2
  have hready1 (t : Time) : p.Ready ((Sys F V).cDur K r) (kv key hn 1 (by decide)) t :=
    ⟨growthPoint_honest key hn hΔ hΔF awake H κ (by decide) (by decide) t,
      fun u _ _ => haw 1 (by decide) (by decide) u⟩
  have hready0 : p.Ready ((Sys F V).cDur K r) (kv key hn 0 (by decide)) T := by
    refine ⟨?_, fun u _ _ => haw 0 (by decide) (by decide) u⟩
    change kv key hn 0 (by decide) ∉ (growthPoint key hn Δ hΔ ΔF hΔF awake H κ).faultyAt T
    rw [growthPoint_faulty, ite_eq_right (show ¬ κ ≤ T by change ¬ T + 1 ≤ T; linarith)]
    exact Finset.notMem_empty _
  have hco := growthPoint_cohort key hn hΔ hΔF H κ ((Sys F V).cohortAt K b₁ r)
    ((Sys F V).outageStart K b₀ r) ((Sys F V).outageEnd K b₁ r) (by
      change κ ≤ min (min (b₁ + (K.params.noSleep : Time) * Δ) H +
        (K.params.cohortAhead : Time) * Δ) H
      apply le_min _ hκH
      have hh : κ ≤ min (b₁ + (K.params.noSleep : Time) * Δ) H :=
        le_min (by linarith) hκH
      linarith)
  have hse := Model.sysOf_eagerFrom (O := O) rho he
  refine ⟨r, T, b₀, b₁, kv key hn 0 (by decide), κ, hv, hnc, rfl, rfl,
    ⟨⟨hT, ?_, ?_, ?_⟩, ⟨?_, hse.psync (by dsimp [b₁, b₀]; linarith) hΔ1 hΔF1⟩,
      growthPoint_eta key hn hΔ hΔF awake H κ ha.θ_range
        (asleepAlways_readyAt key hn hΔ hΔF H) _ _ _ _ _, hco.1, hco.2⟩,
    ⟨hT, ?_, le_rfl, ⟨_, hready0⟩,
      ⟨kv key hn 2 (by decide), b₀, le_rfl, by dsimp [b₁]; linarith,
        growthPoint_honest key hn hΔ hΔF awake H κ (j := 2) (by decide) (by decide) _, ?_⟩,
      ⟨_, H, le_rfl, le_rfl, hready1 H⟩⟩,
    le_rfl, hready0, by change T < T + 1; linarith, ?_, _, H, le_rfl, le_rfl, hκH, hready1 H⟩
  · change T + (K.params.lag : Time) * Δ ≤ b₀
    dsimp [b₀]; linarith
  · dsimp [b₁]; linarith
  · have hb : (1 : Time) ≤ (K.params.budget : Time) := by exact_mod_cast ha.budget_pos
    change b₁ ≤ b₀ + (K.params.budget : Time) * Δ
    dsimp [b₁]; nlinarith
  · exact (Model.sysOf_delivers_iff (O := O) rho _ _ _).mpr
      (he.syncUntil (Model.Run.log_sendsFromZero rho hv) le_rfl hΔ1 hΔF1 b₀)
  · dsimp [b₀]; linarith
  · change asleepAlways (kv key hn 2 (by decide)) (kv key hn 2 (by decide)) b₀ = false
    simp only [asleepAlways_apply, decide_true, Bool.not_true]
  · change kv key hn 0 (by decide) ∈ (growthPoint key hn Δ hΔ ΔF hΔF awake H κ).faultyAt κ
    simp only [growthPoint_faulty, le_rfl, ↓reduceIte, Finset.mem_singleton]

end Consensus.Shape
end
