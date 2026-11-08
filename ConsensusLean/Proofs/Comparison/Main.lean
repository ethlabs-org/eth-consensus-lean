module
public import ConsensusLean.Comparison.Defaults
public import ConsensusLean.Proofs.Comparison.Protection
import Mathlib.Tactic.Linarith

public section

/-! # Comparison, Slice 0: the order lemmas and the defaults (proofs)

* `slice0Class_mono`, `sync0Class_mono`: the coordinatewise orders imply class inclusion.
* `healDefault0`: the heal defaults from `Behaviour.healedSafe` and `healthyLive` at GST `b₁`. The
  Slice 0 class with `fcap < β·n` is in `Healthy b₁` (`healthy_of_slice0Class`; `FullAwake` gives
  the full participation from `max b₁ 0`). Healed safety: when the heal point is within the horizon,
  progress to the horizon gives progress to the heal point (`Progress.mono`); when it is past the
  horizon, ready-reader safety from it is vacuous (`readySafe_of_horizon_lt`: every cut is within
  the horizon).
* `txLatencyDefault0`: the latency default from `Behaviour.sleepyLive`: with full participation
  every validator honest at the look-ahead is ready on the retained view, so `θ·n < n − f` gives
  the sleepy participation (`sleepyOn_of_fullAwake`).

The layer's entry module: Slice 2's order lemma and protection default are in
`Proofs/Comparison/Protection`, imported here. -/

namespace Consensus.Comparison

theorem slice0Class_mono : Slice0ClassMono := by
  intro V _ Prog S K q q' b₀ b₁ r ⟨hL, hf, ha⟩ ⟨⟨hnet, hgs⟩, hb, hlen, hfc, haw, hfg⟩
  refine ⟨⟨hnet, ?_⟩, hb, hlen.trans ?_, hfc.trans hf, haw, hfg⟩
  · rcases q with ⟨L, f, a⟩
    rcases q' with ⟨L', f', a'⟩
    cases a' with
    | any => trivial
    | split G' =>
      cases a with
      | any => exact absurd ha id
      | split G =>
        change G = G' at ha
        subst ha
        exact hgs
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hL) (S.pt r).env.ΔAC_pos.le

theorem sync0Class_mono : Sync0ClassMono :=
  fun _ _ _ _ _ _ hff ⟨hs, hfc, haw⟩ => ⟨hs, hfc.trans hff, haw⟩

variable {V : Type} [Fintype V] {Prog : Type}

private theorem ite_mono_top {p p' : Prop} [Decidable p] [Decidable p'] (h : p' → p)
    (x : WithTop ℕ) : (if p then x else ⊤) ≤ (if p' then x else ⊤) := by
  by_cases h' : p'
  · simp [h', h h']
  · simp [h']

theorem hsDefault_mono (K : Contract Prog) (cap : Capability) (i : K.Idx) :
    AdverseMonotone (hsDefault (V := V) K cap i) := fun q q' ⟨_, hf, _⟩ =>
  ite_mono_top (fun ⟨hc, hlt⟩ => ⟨hc, lt_of_le_of_lt (by exact_mod_cast hf) hlt⟩) _

theorem hlDefault_mono (K : Contract Prog) (cap : Capability) (i : K.Idx) :
    AdverseMonotone (hlDefault (V := V) K cap i) := fun q q' ⟨_, hf, _⟩ =>
  ite_mono_top (fun hlt => lt_of_le_of_lt (by exact_mod_cast hf) hlt) _

theorem latDefault_mono (K : Contract Prog) (cap : Capability) (i : K.Idx) :
    AdverseMonotone (latDefault (V := V) K cap i) := fun q q' ⟨_, hf, _⟩ =>
  ite_mono_top (fun hlt => lt_of_le_of_lt (by exact_mod_cast hf) hlt) _

theorem txLatDefault_mono (K : Contract Prog) (cap : Capability) (i : K.Idx) :
    AdverseMonotone (txLatDefault V K cap i) := fun f f' hff =>
  ite_mono_top (fun ⟨hc, hlt⟩ => ⟨hc, lt_of_lt_of_le hlt (by
    have : (f : ℚ) ≤ f' := by exact_mod_cast hff
    linarith)⟩) _

private theorem eq_of_ite_coe {p : Prop} [Decidable p] {a c : ℕ}
    (h : (if p then (a : WithTop ℕ) else ⊤) = c) : p ∧ c = a := by
  by_cases hp : p
  · simp only [hp, ite_true] at h; exact ⟨hp, (WithTop.coe_injective h).symm⟩
  · simp only [hp, ite_false] at h; exact absurd h WithTop.top_ne_coe

variable (S : System V) (X : Progress S Prog) (K : Contract Prog)

/-- Slice 0's class at a cap below `β·n` is in the contract's healthy regime at GST `b₁`. -/
theorem healthy_of_slice0Class {q : Slice0Q V} {b₀ b₁ : Time} {r : S.Run}
    (h : Slice0Class S K q b₀ b₁ r) (hq : (q.fcap : ℚ) < K.params.β * Fintype.card V) :
    S.Healthy K b₁ r := by
  obtain ⟨⟨⟨-, hps⟩, -⟩, -, -, hfc, haw, hfg⟩ := h
  refine ⟨hps, ⟨lt_of_le_of_lt (by exact_mod_cast hfc) hq, fun v t ht hth hv => ?_⟩, hfg⟩
  exact haw v t ((le_max_right _ _).trans ht) hth hv

/-- Ready-reader safety from a point past the horizon is vacuous on a lawful trace. -/
theorem readySafe_of_horizon_lt {V Id : Type} {tr : Trace V Tx Id} (hl : tr.Laws) (c : Time)
    (g : Id) {t₀ : Time} (h : tr.point.horizon < t₀) : tr.ReadySafe c g t₀ := by
  refine ⟨fun u v i j hi _ _ _ => ?_, fun v i j hi _ _ _ _ => ?_⟩ <;>
  · exact absurd (hi.2.trans (hl.cutTime_le_horizon i hi.1)) (not_le.2 h)

theorem healDefault0 : HealDefault0 := by
  intro V _ _ Prog S X K hB cap i
  refine ⟨⟨hsDefault_mono K cap i, hlDefault_mono K cap i, latDefault_mono K cap i⟩, ?_, ?_⟩
  · intro q c hc g hg b₀ b₁ r hv ⟨hcl, hpr⟩
    obtain ⟨⟨hcap, hq⟩, rfl⟩ := eq_of_ite_coe hc
    have hH := healthy_of_slice0Class S K hcl hq
    have heq : S.heal K cap i b₁ r = healAt S b₁ (K.params.heal cap i) r := rfl
    by_cases hle : S.heal K cap i b₁ r ≤ (S.pt r).horizon
    · have := hB.healedSafe cap g hcap hg i b₁ r hv ⟨hH, X.mono le_rfl hle hpr⟩
      simp only at this ⊢
      rwa [heq] at this
    · exact Or.inl (readySafe_of_horizon_lt (hB.laws.trace r hv) _ g
        (by rw [← heq]; exact not_le.1 hle))
  · intro q c d hc hd g hg b₀ b₁ r hv ⟨hcl, hpr⟩
    obtain ⟨hq, rfl⟩ := eq_of_ite_coe hc
    obtain ⟨-, rfl⟩ := eq_of_ite_coe hd
    exact hB.healthyLive cap g hg i b₁ r hv ⟨healthy_of_slice0Class S K hcl hq, hpr⟩

/-- With full participation, every validator honest at the look-ahead is ready on the retained
view at a time of `[0, horizon]`. -/
theorem sleepyOn_of_fullAwake {r : S.Run} {θ : ℚ} {f : ℕ}
    (hfc : (S.pt r).faultCount (S.pt r).horizon ≤ f) (haw : FullAwake S r) (c W : Time)
    (hW : 0 ≤ W) (hn : θ * Fintype.card V < (Fintype.card V : ℚ) - f) :
    (S.pt r).SleepyOn θ c W 0 (S.pt r).horizon := by
  classical
  intro t ht0 hth
  set p := S.pt r
  set d := p.lookAhead W t
  have hdh : d ≤ p.horizon := min_le_right _ _
  have htd : t ≤ d := le_min (by linarith) hth
  have hsub : Finset.univ \ p.faultyAt d ⊆ (p.retain d).readyAt c t := by
    intro v hv
    have hvd : v ∉ p.faultyAt d := (Finset.mem_sdiff.1 hv).2
    simp only [EnvPoint.readyAt, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hvd, fun u hu hut => ?_⟩
    have hu0 : 0 ≤ u := (le_max_left _ _).trans hu
    exact haw v u hu0 (hut.trans hth) (fun hvu => hvd (p.faultyAt_mono (hut.trans htd) hvu))
  have hRsub : (p.retain d).readyAt c t ⊆ Finset.univ \ p.faultyAt d := by
    intro v hv
    simp only [EnvPoint.readyAt, Finset.mem_filter] at hv
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ v, hv.2.1⟩
  have hcard := Finset.card_le_card hsub
  have hcard' := Finset.card_le_card hRsub
  rw [Finset.card_univ_sdiff] at hcard hcard'
  have hfd : p.faultCount d ≤ f := (Finset.card_le_card (p.faultyAt_mono hdh)).trans hfc
  have hle : (p.faultyAt d).card ≤ Fintype.card V := by
    simpa using Finset.card_le_card (Finset.subset_univ (p.faultyAt d))
  unfold EnvPoint.ReadyAbove
  change θ * (((p.retain d).readyAt c t).card + (p.faultyAt d).card : ℚ) <
    ((p.retain d).readyAt c t).card
  have h1 : (((p.retain d).readyAt c t).card : ℚ) = Fintype.card V - (p.faultyAt d).card := by
    have := le_antisymm hcard' hcard
    rw [this, Nat.cast_sub hle]
  have h2 : ((p.faultyAt d).card : ℚ) ≤ f := by exact_mod_cast hfd
  rw [h1]
  linarith

theorem txLatencyDefault0 : TxLatencyDefault0 := by
  intro V _ _ Prog S X K hB cap i
  refine ⟨txLatDefault_mono K cap i, ?_⟩
  intro f d hd g hg r hv ⟨⟨hps, hfc, haw⟩, hpr⟩
  obtain ⟨⟨hcap, hn⟩, rfl⟩ := eq_of_ite_coe hd
  have hW : 0 ≤ S.aheadDur K r :=
    Int.mul_nonneg (Int.natCast_nonneg _) (S.pt r).env.ΔAC_pos.le
  exact hB.sleepyLive cap g hcap hg i r hv
    ⟨⟨hps, sleepyOn_of_fullAwake S hfc haw _ _ hW hn⟩, hpr⟩

end Consensus.Comparison

end
