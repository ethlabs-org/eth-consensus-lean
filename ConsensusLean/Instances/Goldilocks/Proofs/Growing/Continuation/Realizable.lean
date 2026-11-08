module
public import ConsensusLean.Proofs.RegimesRealizable.Main
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Continuation
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
import ConsensusLean.Lemmas.Model.Causal
import ConsensusLean.Lemmas.Model.Laws
import ConsensusLean.Lemmas.Model.Adequate
import ConsensusLean.Lemmas.Problem.Facts.Network
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Non-vacuity of continuation after healing (`Continues.realizable`)

`handover_realizable`: for every chain-shape family whose progress requirements are recurrences
fitting its skeleton, at admissible numbers with `β ≤ ⅓`, and at least five validators, every
`ΔAC > 1`, `ΔFG > 1` within the FG delay bound and every GST `g` have a valid excuse-free run that
hands over to the sleepy regime at the heal point `T = max g 0 + heal·ΔAC`, with
`⌈n/3⌉ ≥ β·n` validators compromised from `κ = T + 1` on and both continuation claims active
after `κ`. `continues_realizable` is its Goldilocks instance, the `realizable` field of
`Continues` at the headline contract.

The witness point: everyone awake; the validators of the last `⌈n/3⌉ = (n + 2) / 3` keys
compromised at `κ`, nobody before; transaction `42` submitted to key `1` at `0`; the canonical
causal run from GST `g` under the extremal selection (key `1`, never compromised, proposes every
slot). Up to `T` there are no faults (healthy, full participation); from `T` on the retained view
of every look-ahead has at most `⌈n/3⌉ < n/2` faults (`n ≥ 5`) and every other validator ready,
so the sleepy bound holds at `θ ≤ ½`. The causal run convicts nobody on honest evidence, so no two
honest views convict anyone (`ConvictedBelow`). Keys `1` and `2` stay honest and awake: the
liveness reader and the two safety readers after `κ`. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (pubOf protoOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The validators of the last `(n + 2) / 3` keys. -/
private def lateKeys (key : Fin (Fintype.card V) ≃ V) : Finset V :=
  (Finset.univ.filter fun k : Fin (Fintype.card V) =>
    Fintype.card V - (Fintype.card V + 2) / 3 ≤ k.val).map key.toEmbedding

omit [DecidableEq V] in
private theorem lateKeys_card (key : Fin (Fintype.card V) ≃ V) :
    (lateKeys key).card = (Fintype.card V + 2) / 3 := by
  have h : (Finset.univ.filter fun k : Fin (Fintype.card V) =>
      Fintype.card V - (Fintype.card V + 2) / 3 ≤ k.val).map Fin.valEmbedding =
      Finset.Ico (Fintype.card V - (Fintype.card V + 2) / 3) (Fintype.card V) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact ⟨hk, k.isLt⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨x, h2⟩, h1, rfl⟩
  rw [lateKeys, Finset.card_map, ← Finset.card_map Fin.valEmbedding, h, Nat.card_Ico]
  omega

omit [DecidableEq V] in
private theorem kv_notMem_lateKeys (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V)
    {j : Nat} (hj : j < 5) (hj3 : j < 3) : kv key hn j hj ∉ lateKeys key := by
  rw [lateKeys, kv_eq]
  change key.toEmbedding ⟨j, _⟩ ∉ _
  rw [Finset.mem_map' key.toEmbedding, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, not_le]
  omega

/-- The hand-over witness point: everyone awake, the last `(n + 2) / 3` keys compromised at `κ`,
transaction `42` submitted to key `1` at `0`. -/
private def handoverPoint (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V)
    (Δ : Time) (hΔ : 0 < Δ) (ΔF : Time) (hΔF : 0 < ΔF) (H κ : Time) : EnvPoint V :=
  ⟨⟨Δ, hΔ, ΔF, hΔF, allAwake⟩, fun t => if κ ≤ t then lateKeys key else ∅,
    by
      intro a b hab
      dsimp only
      split_ifs with ha hb
      · exact Finset.Subset.refl _
      · exact False.elim (hb (ha.trans hab))
      · exact Finset.empty_subset _
      · exact Finset.Subset.refl _,
    H, fun v t => if v = key ⟨1, by omega⟩ ∧ t = 0 then [42] else []⟩

section Point

variable (key : Fin (Fintype.card V) ≃ V) (hn : 5 ≤ Fintype.card V)
  {Δ : Time} (hΔ : 0 < Δ) {ΔF : Time} (hΔF : 0 < ΔF) (H κ : Time)

private theorem handoverPoint_faulty (t : Time) :
    (handoverPoint key hn Δ hΔ ΔF hΔF H κ).faultyAt t =
      if κ ≤ t then lateKeys key else ∅ := by rfl

private theorem handoverPoint_submit (v : V) (t : Time) :
    (handoverPoint key hn Δ hΔ ΔF hΔF H κ).submit v t =
      if v = key ⟨1, by omega⟩ ∧ t = 0 then [42] else [] := by rfl

private theorem handoverPoint_honest {j : Nat} (hj : j < 5) (hj3 : j < 3) (t : Time) :
    (handoverPoint key hn Δ hΔ ΔF hΔF H κ).HonestAt (kv key hn j hj) t := by
  simp only [EnvPoint.HonestAt, handoverPoint_faulty]
  split_ifs
  · exact kv_notMem_lateKeys key hn hj hj3
  · exact Finset.notMem_empty _

private theorem handoverPoint_ready {j : Nat} (hj : j < 5) (hj3 : j < 3) (c t : Time) :
    (handoverPoint key hn Δ hΔ ΔF hΔF H κ).Ready c (kv key hn j hj) t :=
  ⟨handoverPoint_honest key hn hΔ hΔF H κ hj hj3 t, fun _ _ _ => allAwake_apply _ _⟩

/-- At `θ ≤ ½` the sleepy bound holds everywhere: every retained view has at most
`(n + 2) / 3 < n / 2` faults and every other validator ready. -/
private theorem handoverPoint_sleepy {θ : ℚ} (hθ : 0 ≤ θ ∧ θ ≤ 1 / 2) (c W a b : Time) :
    (handoverPoint key hn Δ hΔ ΔF hΔF H κ).SleepyOn θ c W a b := by
  intro t _ _
  set p := handoverPoint key hn Δ hΔ ΔF hΔF H κ
  set d := p.lookAhead W t
  have hsub : Finset.univ \ p.faultyAt d ⊆ (p.retain d).readyAt c t := by
    intro v hv
    simp only [EnvPoint.readyAt, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(Finset.mem_sdiff.mp hv).2, fun _ _ _ => allAwake_apply _ _⟩
  have hf : (p.faultyAt d).card ≤ (Fintype.card V + 2) / 3 := by
    rw [handoverPoint_faulty]
    split_ifs
    · rw [lateKeys_card]
    · rw [Finset.card_empty]; exact Nat.zero_le _
  have hR := Finset.card_le_card hsub
  rw [Finset.card_univ_sdiff] at hR
  have hRF : Fintype.card V ≤ ((p.retain d).readyAt c t).card + (p.faultyAt d).card := by omega
  have h2 : 2 * (p.faultyAt d).card + 1 ≤ Fintype.card V := by omega
  unfold EnvPoint.ReadyAbove EnvPoint.faultCount
  change θ * (((p.retain d).readyAt c t).card + (p.faultyAt d).card : ℚ) < _
  have hRF' : ((Fintype.card V : ℕ) : ℚ) ≤
      (((p.retain d).readyAt c t).card : ℚ) + ((p.faultyAt d).card : ℚ) := by exact_mod_cast hRF
  have h2' : 2 * ((p.faultyAt d).card : ℚ) + 1 ≤ ((Fintype.card V : ℕ) : ℚ) := by
    exact_mod_cast h2
  linarith only [hRF', h2', mul_le_mul_of_nonneg_right hθ.2
    (by positivity : (0 : ℚ) ≤ (((p.retain d).readyAt c t).card : ℚ) + (p.faultyAt d).card)]

/-- No faults before `κ`: healthy, with full participation, up to any `T < κ`. -/
private theorem handoverPoint_healthy {β : ℚ} (hβ : 1 / 3 ≤ β) (g T : Time) (hT : T < κ) :
    (handoverPoint key hn Δ hΔ ΔF hΔF H κ).HealthyOn β g T := by
  refine ⟨?_, fun _ _ _ _ _ => allAwake_apply _ _⟩
  unfold EnvPoint.faultCount
  rw [handoverPoint_faulty, ite_eq_right (not_le.mpr hT), Finset.card_empty, Nat.cast_zero]
  have hn' : (0 : ℚ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  exact mul_pos (lt_of_lt_of_le (by norm_num) hβ) hn'

/-- At `κ` at least fraction `β ≤ ⅓` of the validators are compromised. -/
private theorem handoverPoint_beta {β : ℚ} (hβ : β ≤ 1 / 3) :
    β * Fintype.card V ≤ ((handoverPoint key hn Δ hΔ ΔF hΔF H κ).faultCount κ : ℚ) := by
  unfold EnvPoint.faultCount
  rw [handoverPoint_faulty, ite_eq_left le_rfl, lateKeys_card]
  have h3 : ((Fintype.card V : ℕ) : ℚ) ≤ 3 * (((Fintype.card V + 2) / 3 : ℕ) : ℚ) := by
    exact_mod_cast (by omega : Fintype.card V ≤ 3 * ((Fintype.card V + 2) / 3))
  linarith only [h3, mul_le_mul_of_nonneg_right hβ (Nat.cast_nonneg (α := ℚ) (Fintype.card V))]

/-- Key `1`, never compromised and always awake, proposes every slot: every fitting recurrence
holds on every window. -/
private theorem handoverPoint_holds (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (hf : ProgressFits K F) (hrec : ∀ cap i, ∃ ρ, K.progress cap i = .recur ρ)
    (cap : Capability) (i : K.Idx) (c s e : Time) :
    shapeHolds F (K.progress cap i) c s e (handoverPoint key hn Δ hΔ ΔF hΔF H κ)
      (key, extremalSel F (handoverPoint key hn Δ hΔ ΔF hΔF H κ).env) := by
  obtain ⟨ρ, hρ⟩ := hrec cap i
  have hfit := hf cap i (pubOf (handoverPoint key hn Δ hΔ ΔF hΔF H κ).env)
  rw [hρ] at hfit ⊢
  change ∀ s, (F _).skel.proposerSel s = .sized 1 at hfit
  apply patternRecurrence_of_all
  intro sl j _
  have hmem := extremalSel_proposer_mem F hfit (by omega) (sl + j)
  refine ⟨⟨⟨1, by omega⟩, (hmem _).mpr rfl⟩, fun k hk => ?_⟩
  have hk1 : k = ⟨1, by omega⟩ := Fin.ext ((hmem k).mp hk)
  subst hk1
  exact ⟨handoverPoint_ready key hn hΔ hΔF H κ (j := 1) (by decide) (by decide) _ _,
    handoverPoint_honest key hn hΔ hΔF H κ (j := 1) (by decide) (by decide) _⟩

/-- Liveness is active after `start`: transaction `42`, submitted to key `1` at `0`, is owed to
key `2` at the horizon. -/
private theorem handoverPoint_txLiveActive (c start D : Time) (hH : max 0 start + Δ + D ≤ H) :
    (handoverPoint key hn Δ hΔ ΔF hΔF H κ).TxLiveActive c start D := by
  refine ⟨42, 0, H, kv key hn 1 (by decide), kv key hn 2 (by decide), le_rfl,
    handoverPoint_honest key hn hΔ hΔF H κ (by decide) (by decide) _, allAwake_apply _ _, ?_,
    kv_ne key hn (by decide), ?_, hH, le_rfl,
    handoverPoint_ready key hn hΔ hΔF H κ (by decide) (by decide) _ _⟩
  · simp only [handoverPoint_submit, kv_eq, and_self, ↓reduceIte, List.mem_cons,
      List.not_mem_nil, or_false]
  · intro τ
    have hne : kv key hn 2 (by decide) ≠ key ⟨1, by omega⟩ := kv_ne key hn (hj' := by decide)
      (by decide)
    simp only [handoverPoint_submit, hne, false_and, ↓reduceIte, List.not_mem_nil,
      not_false_eq_true]

/-- Safety is active after `t₀`: keys `1` and `2` ready at `t₀ + 1`, key `1` again at `t₀ + 2`. -/
private theorem handoverPoint_safeActive (c t₀ : Time) (hH : t₀ + 2 ≤ H) :
    SafeActive c t₀ (handoverPoint key hn Δ hΔ ΔF hΔF H κ) :=
  ⟨kv key hn 1 (by decide), kv key hn 2 (by decide), t₀ + 1, t₀ + 2,
    kv_ne key hn (by decide), lt_add_one t₀, add_lt_add_right one_lt_two t₀, hH,
    handoverPoint_ready key hn hΔ hΔF H κ (by decide) (by decide) _ _,
    handoverPoint_ready key hn hΔ hΔF H κ (by decide) (by decide) _ _,
    handoverPoint_ready key hn hΔ hΔF H κ (by decide) (by decide) _ _⟩

end Point

/-- **Hand-over witness**: for a family whose progress requirements are fitting recurrences, at
admissible numbers with `β ≤ ⅓` and at least five validators, every `ΔAC > 1`, `ΔFG > 1` within
the FG delay bound and every GST `g` have a valid excuse-free run that hands over at the heal
point `T`, with at least fraction `β` compromised by `κ = T + 1`, progress from `ready` to the
horizon, and liveness and safety active after `κ`. -/
theorem handover_realizable (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (ha : K.params.Admissible) (hβ : K.params.β ≤ 1 / 3) (hf : ProgressFits K F)
    (hrec : ∀ cap i, ∃ ρ, K.progress cap i = .recur ρ) (hn : 5 ≤ Fintype.card V)
    (cap : Capability) (i : K.Idx) (Δ ΔF g : Time) (hΔ1 : 1 < Δ) (hΔF1 : 1 < ΔF)
    (hr : ΔF ≤ (K.params.fgDelay : Time) * Δ) :
    ∃ r T κ, (Sys F V).Valid r ∧ ¬ (Sys F V).Excuse r ∧ ((Sys F V).pt r).env.ΔAC = Δ ∧
      ((Sys F V).pt r).env.ΔFG = ΔF ∧ (Sys F V).Handover K g T r ∧
      (Sys F V).heal K cap i g r ≤ T ∧
      (Sys F V).prog (shapeProgress F V) K cap i ((Sys F V).ready K g r)
        ((Sys F V).pt r).horizon r ∧
      K.params.β * Fintype.card V ≤ (((Sys F V).pt r).faultCount κ : ℚ) ∧
      ((Sys F V).pt r).TxLiveActive ((Sys F V).cDur K r) κ ((Sys F V).lat K cap i r) ∧
      SafeActive ((Sys F V).cDur K r) κ ((Sys F V).pt r) := by
  have hΔ := zero_lt_one.trans hΔ1
  have hΔF := zero_lt_one.trans hΔF1
  let key : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let T := max g 0 + (K.params.heal cap i : Time) * Δ
  let κ := T + 1
  let H := κ + Δ + (K.params.latency cap i : Time) * Δ + 2
  have hheal : 0 ≤ (K.params.heal cap i : Time) * Δ := mul_nonneg (by positivity) hΔ.le
  have hlat : 0 ≤ (K.params.latency cap i : Time) * Δ := mul_nonneg (by positivity) hΔ.le
  have hT0 : 0 ≤ T := add_nonneg (le_max_right _ _) hheal
  have hH : 0 ≤ H := by dsimp only [H, κ]; linarith
  let p := handoverPoint key hn Δ hΔ ΔF hΔF H κ
  obtain ⟨hash, hinj⟩ := Countable.exists_injective_nat (protoOf (compiled F) p.env).Item
  obtain ⟨relay, events, hv, he, hc⟩ :=
    Model.canonical_run_from_causal O (compiled F) V p.env p.faultyAt p.faultyAt_mono H hH key
      (extremalSel F p.env) (extremalSel_admits F p.env) p.submit hash g
  let rho := Model.Run.mk (F := compiled F) (E := p.env) p.faultyAt p.faultyAt_mono H events key
    (extremalSel F p.env) p.submit relay hash
  let r : (Sys F V).Run := ⟨p.env, rho⟩
  have hnc : ¬ rho.HashCollision :=
    Model.Run.not_hashCollision_of_injective (Model.Run.injectiveHash_iff.mpr hinj)
  have hconv := Model.convicted_honestEvidence_eq_empty (O := O) rho hv
    (rho.not_slashable_of_causal hc)
  have hse := Model.sysOf_eagerFrom (O := O) rho he
  have hL := Model.sysOf_laws O (compiled F) V
  refine ⟨r, T, κ, hv, hnc, rfl, rfl,
    ⟨hse.psync le_rfl hΔ1 hΔF1,
      handoverPoint_healthy key hn hΔ hΔF H κ ha.β_range g T (lt_add_one T), hr,
      handoverPoint_sleepy key hn hΔ hΔF H κ ha.θ_range _ _ _ _, ?_⟩,
    le_rfl, handoverPoint_holds key hn hΔ hΔF H κ F K hf hrec cap i _ _ _,
    handoverPoint_beta key hn hΔ hΔF H κ hβ,
    handoverPoint_txLiveActive key hn hΔ hΔF H κ _ _ _ ?_,
    handoverPoint_safeActive key hn hΔ hΔF H κ _ _ ?_⟩
  · intro u v i j hi hj hu hw
    have hsub : Consensus.convicted ((Sys F V).convicts r) ((Sys F V).view r u i ∪
        (Sys F V).view r v j) ⊆ Consensus.convicted ((Sys F V).convicts r)
          ((Sys F V).honestEvidenceBy r H) := by
      intro x hx
      unfold Consensus.convicted at hx ⊢
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      refine hL.convicts_mono r _ _ x ?_ hx
      rintro o (ho | ho)
      · exact ⟨u, i, hi, (hL.trace r hv).cutTime_le_horizon i hi, hu, ho⟩
      · exact ⟨v, j, hj, (hL.trace r hv).cutTime_le_horizon j hj, hw, ho⟩
    have hempty : Consensus.convicted ((Sys F V).convicts r) ((Sys F V).view r u i ∪
        (Sys F V).view r v j) = ∅ := Finset.subset_empty.mp (hconv ▸ hsub)
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    have hα : 0 < K.params.α :=
      lt_of_lt_of_le (by norm_num) (ha.β_range.trans ha.α_range.1)
    have hn' : (0 : ℚ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
    exact mul_pos hα hn'
  · change max 0 κ + Δ + (K.params.latency cap i : Time) * Δ ≤ H
    rw [max_eq_right (by dsimp only [κ]; linarith)]
    dsimp only [H]; linarith
  · dsimp only [H]; linarith

end Consensus.Shape

namespace Consensus.Goldilocks

open AsChainShape
open Blocks Shape

/-- **Continuation is not vacuous** for Goldilocks: the `realizable` field of `Continues` for the
compiled family at the headline contract, from `handover_realizable` (every Goldilocks progress
requirement is a recurrence with one proposer per slot, and `β = ⅓`). -/
theorem continues_realizable (S : Setup) (A : ContractAssumptions S)
    (V : Type) [Fintype V] [DecidableEq V] :
    let Sy := Model.sysOf schema (compiled (goldilocks S)) V
    let K := goldilocksContract A (contract_coefficients S A)
    5 ≤ Fintype.card V → ∀ cap i (ΔAC ΔFG g : Time), (cap = .available ∨ cap = .stable) →
      1 < ΔAC → 1 < ΔFG → ΔFG ≤ (K.params.fgDelay : Time) * ΔAC → 0 ≤ g →
      ∃ r T κ, Sy.Valid r ∧ ¬ Sy.Excuse r ∧ (Sy.pt r).env.ΔAC = ΔAC ∧
        (Sy.pt r).env.ΔFG = ΔFG ∧ Sy.Handover K g T r ∧ Sy.heal K cap i g r ≤ T ∧
        Sy.prog (shapeProgress (goldilocks S) V) K cap i (Sy.ready K g r) (Sy.pt r).horizon r ∧
        K.params.β * Fintype.card V ≤ ((Sy.pt r).faultCount κ : ℚ) ∧
        (Sy.pt r).TxLiveActive (Sy.cDur K r) κ (Sy.lat K cap i r) ∧
        SafeActive (Sy.cDur K r) κ (Sy.pt r) := by
  intro Sy K hn cap i ΔAC ΔFG g _ hΔ hΔF hr _
  have ha : K.params.Admissible :=
    { catchUp_pos := (contract_coefficients S A).catchUp.pos
      θ_range := by norm_num [K, Params.standard]
      β_range := by norm_num [K, Params.standard]
      cover_range := by norm_num [K, Params.standard]
      α_range := by norm_num [K, Params.standard]
      budget_pos := by have := S.two_le_k; dsimp [K, Params.standard]; omega }
  exact handover_realizable (goldilocks S) K ha (by norm_num [K, Params.standard])
    (fun _ _ _ _ => rfl) (fun _ _ => ⟨_, rfl⟩) hn cap i ΔAC ΔFG g hΔ hΔF hr

end Consensus.Goldilocks

end
