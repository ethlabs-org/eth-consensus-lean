module
public import ConsensusLean.Comparison.HealDefaults

public section

/-! # Comparison, Slice 1: the order lemma and the defaults (proofs)

* `healClassMono`: the coordinatewise order of `HealQ` implies class inclusion (`θ` and `catchUp`
  enter no class).
* `healDefault`: the Slice 1 heal defaults from `Behaviour.healedSafe` and `healthyLive` at GST
  `b₁`. The class at `fcap < β·n` is in `Healthy b₁` (`healthy_of_healClass`); a reader ready with
  the point's catch-up is ready with the contract's (`ready_of_catchUp_le`), so ready-reader safety
  and transaction liveness transfer to the point's readers (`readySafe_of_catchUp_le`,
  `txLive_of_catchUp_le`); past the horizon, ready-reader safety is vacuous. -/

namespace Consensus.Comparison

open Consensus.Model

theorem healClassMono : HealClassMono := by
  intro V _ _ O F fl Prog K q q' b₀ b₁ r hle hc
  obtain ⟨hL, hpre, hpost, hm, hf, ha, -, -⟩ := hle
  obtain ⟨hnet, hhold, h01, hlen, hapre, hapost, hcm, hcf, haw, hfg⟩ := hc
  have hΔ : (0 : Time) ≤ ((sysOf O F V).pt r).env.ΔAC := ((sysOf O F V).pt r).env.ΔAC_pos.le
  refine ⟨?_, ?_, h01, hlen.trans (Int.mul_le_mul_of_nonneg_right (by exact_mod_cast hL) hΔ),
    hapre.trans hpre, hapost.trans hpost, hm.trans hcm, hcf.trans hf, haw, hfg⟩
  · obtain ⟨hon, hg⟩ := hnet
    refine ⟨hon, ?_⟩
    rcases q with ⟨_, _, _, _, _, a, _, _⟩
    rcases q' with ⟨_, _, _, _, _, a', _, _⟩
    cases a <;> cases a' <;> simp_all [IncidentClass.le_def, IncidentClass.Le,
      IncidentClass.async, GroupSyncOn]
  · rcases q with ⟨_, _, _, _, _, a, _, _⟩
    rcases q' with ⟨_, _, _, _, _, a', _, _⟩
    cases a <;> cases a' <;> simp_all [IncidentClass.le_def, IncidentClass.Le, HoldOn]

variable {V : Type} [Fintype V] {Prog : Type}

private theorem ite_mono_top {p p' : Prop} [Decidable p] [Decidable p'] (h : p' → p)
    (x : WithTop ℕ) : (if p then x else ⊤) ≤ (if p' then x else ⊤) := by
  by_cases h' : p'
  · simp [h', h h']
  · simp [h']

private theorem eq_of_ite_coe {p : Prop} [Decidable p] {a c : ℕ}
    (h : (if p then (a : WithTop ℕ) else ⊤) = c) : p ∧ c = a := by
  by_cases hp : p
  · simp only [hp, ite_true] at h; exact ⟨hp, (WithTop.coe_injective h).symm⟩
  · simp only [hp, ite_false] at h; exact absurd h WithTop.top_ne_coe

omit [Fintype V] in
/-- Readiness at least the contract's is closed downward in the adverse order. -/
theorem readinessAtLeast_of_le (K : Contract Prog) {q q' : HealQ V} (hle : q ≤ q')
    (h : ReadinessAtLeast K q') : ReadinessAtLeast K q :=
  ⟨h.1.trans hle.2.2.2.2.2.2.2, h.2.trans hle.2.2.2.2.2.2.1⟩

/-- A cap below `β·n` stays below it at a less adverse point. -/
private theorem fcap_lt_of_le (K : Contract Prog) {q q' : HealQ V} (hle : q ≤ q')
    (h : (q'.fcap : ℚ) < K.params.β * Fintype.card V) :
    (q.fcap : ℚ) < K.params.β * Fintype.card V :=
  lt_of_le_of_lt (by exact_mod_cast hle.2.2.2.2.1) h

theorem healHsDefault_mono (K : Contract Prog) (cap : Capability) (i : K.Idx) :
    AdverseMonotone (healHsDefault (V := V) K cap i) := fun _ _ hle =>
  ite_mono_top (fun ⟨hc, hlt, hr⟩ =>
    ⟨hc, fcap_lt_of_le K hle hlt, readinessAtLeast_of_le K hle hr⟩) _

theorem healHlDefault_mono (K : Contract Prog) (cap : Capability) (i : K.Idx) :
    AdverseMonotone (healHlDefault (V := V) K cap i) := fun _ _ hle =>
  ite_mono_top (fun ⟨hlt, hr⟩ => ⟨fcap_lt_of_le K hle hlt, readinessAtLeast_of_le K hle hr⟩) _

theorem healLatDefault_mono (K : Contract Prog) (cap : Capability) (i : K.Idx) :
    AdverseMonotone (healLatDefault (V := V) K cap i) := fun _ _ hle =>
  ite_mono_top (fun ⟨hlt, hr⟩ => ⟨fcap_lt_of_le K hle hlt, readinessAtLeast_of_le K hle hr⟩) _

/-- A node ready with catch-up `c'` is ready with every shorter catch-up `c ≤ c'`. -/
theorem ready_of_catchUp_le {V : Type} {p : EnvPoint V} {c c' : Time} (hc : c ≤ c') {v : V}
    {t : Time} (h : p.Ready c' v t) : p.Ready c v t :=
  ⟨h.1, fun u hu hut => h.2 u
    (le_trans (max_le_max le_rfl (Int.sub_le_sub_right (Int.sub_le_sub_left hc t) 1)) hu) hut⟩

/-- Ready-reader safety for catch-up `c` gives it for every longer catch-up `c' ≥ c` (fewer
readers). -/
theorem readySafe_of_catchUp_le {V Id : Type} {tr : Trace V Tx Id} {c c' : Time} (hc : c ≤ c')
    {g : Id} {t₀ : Time} (h : tr.ReadySafe c g t₀) : tr.ReadySafe c' g t₀ :=
  ⟨fun u v i j hi hj hu hv => h.1 u v i j hi hj (ready_of_catchUp_le hc hu)
      (ready_of_catchUp_le hc hv),
    fun v i j hi hij hj hv hv' => h.2 v i j hi hij hj (ready_of_catchUp_le hc hv)
      (ready_of_catchUp_le hc hv')⟩

/-- Transaction liveness for catch-up `c` gives it for every longer catch-up `c' ≥ c`. -/
theorem txLive_of_catchUp_le {V Id : Type} {tr : Trace V Tx Id} {c c' : Time} (hc : c ≤ c')
    {g : Id} {start D : Time} (h : tr.TxLive c g start D) : tr.TxLive c' g start D :=
  fun x t t' hx ht ht' v hv => h x t t' hx ht ht' v (ready_of_catchUp_le hc hv)

/-- Ready-reader safety from a point past the horizon is vacuous on a lawful trace. -/
private theorem readySafe_of_horizon_lt {V Id : Type} {tr : Trace V Tx Id} (hl : tr.Laws)
    (c : Time) (g : Id) {t₀ : Time} (h : tr.point.horizon < t₀) : tr.ReadySafe c g t₀ := by
  refine ⟨fun u v i j hi _ _ _ => ?_, fun v i j hi _ _ _ _ => ?_⟩ <;>
  · exact absurd (hi.2.trans (hl.cutTime_le_horizon i hi.1)) (not_le.2 h)

variable [DecidableEq V] {O : OutputSchema} (F : ProtocolFamily O) (K : Contract Prog)

/-- The Slice 1 class at a cap below `β·n` is in the contract's healthy regime at GST `b₁`. -/
theorem healthy_of_healClass {fl : RoleFloor F V} {q : HealQ V} {b₀ b₁ : Time}
    {r : (sysOf O F V).Run} (h : HealClass F K fl q b₀ b₁ r)
    (hq : (q.fcap : ℚ) < K.params.β * Fintype.card V) : (sysOf O F V).Healthy K b₁ r := by
  obtain ⟨⟨⟨-, hps⟩, -⟩, -, -, -, -, -, -, hfc, haw, hfg⟩ := h
  exact ⟨hps, ⟨lt_of_le_of_lt (by exact_mod_cast hfc) hq, haw⟩, hfg⟩

/-- The point's readers are among the contract's: `catchUp·ΔAC ≤ q.catchUp·ΔAC`. -/
private theorem cDur_le_readerDur {q : HealQ V} (hr : ReadinessAtLeast K q)
    (r : (sysOf O F V).Run) : (sysOf O F V).cDur K r ≤ q.readerDur (sysOf O F V) r :=
  Int.mul_le_mul_of_nonneg_right (by exact_mod_cast hr.1) ((sysOf O F V).pt r).env.ΔAC_pos.le

theorem healDefault : HealDefault := by
  intro V _ _ O F fl Prog X K hB cap i
  refine ⟨⟨healHsDefault_mono K cap i, healHlDefault_mono K cap i, healLatDefault_mono K cap i⟩,
    ?_, ?_⟩
  · intro q c hc g hg b₀ b₁ r hv ⟨hcl, hpr⟩
    obtain ⟨⟨hcap, hq, hr⟩, rfl⟩ := eq_of_ite_coe hc
    have hH := healthy_of_healClass F K hcl hq
    have heq : (sysOf O F V).heal K cap i b₁ r = healAt (sysOf O F V) b₁ (K.params.heal cap i) r :=
      rfl
    by_cases hle : (sysOf O F V).heal K cap i b₁ r ≤ ((sysOf O F V).pt r).horizon
    · rcases hB.healedSafe cap g hcap hg i b₁ r hv ⟨hH, X.mono le_rfl hle hpr⟩ with hs | he
      · exact Or.inl (readySafe_of_catchUp_le (cDur_le_readerDur F K hr r) hs)
      · exact Or.inr he
    · exact Or.inl (readySafe_of_horizon_lt (hB.laws.trace r hv) _ g
        (by rw [← heq]; exact not_le.1 hle))
  · intro q c d hc hd g hg b₀ b₁ r hv ⟨hcl, hpr⟩
    obtain ⟨⟨hq, hr⟩, rfl⟩ := eq_of_ite_coe hc
    obtain ⟨-, rfl⟩ := eq_of_ite_coe hd
    rcases hB.healthyLive cap g hg i b₁ r hv ⟨healthy_of_healClass F K hcl hq, hpr⟩ with hl | he
    · exact Or.inl (txLive_of_catchUp_le (cDur_le_readerDur F K hr r) hl)
    · exact Or.inr he

end Consensus.Comparison

end
