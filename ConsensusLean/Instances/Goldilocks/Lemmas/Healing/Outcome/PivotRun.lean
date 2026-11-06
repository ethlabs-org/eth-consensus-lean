module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Pivot
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: proposal run and walk facts

Prerequisites for the post-reset proposal pivot. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- An update of label `m` at `t_m + 6Δ` precedes the start of every slot `u ≥ m + 2`. -/
private theorem ts_add_six_lt {m u : Int} (h : m + 2 ≤ u) : sp.ts m + 6 * sp.Δ < sp.ts u := by
  have hΔ := sp.toParams.hΔ
  have := (SA.ts_le_iff sp).mpr h
  simp only [SAParams.ts] at this ⊢
  linarith

/-! ### Run facts -/

/-- `f < n/2` under `Healthy(g)`. -/
theorem faulty_lt_half (hp : ResetPremises tr H proposer dg g ΔF a) (x : Fin sp.n) :
    2 * Hᶜ.ncard < sp.n := by
  have := hp.healthy.2.2
  have := Fin.pos x
  have hn : sp.n = sp.toParams.n := rfl
  omega

/-- A fast lock of label `s` is written at or after `t_s`. -/
theorem ts_le_of_fastLock (hp : ResetPremises tr H proposer dg g ΔF a) {x : Fin sp.n}
    {i s : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC x i s D CV) : sp.ts s ≤ tr.time i := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hΔ := sp.toParams.hΔ
  rcases hfl with ⟨ℓ, C, ⟨-, -, ht, -⟩, -⟩ | ⟨ℓ, A, -, hsl, -⟩
  · have ht' : tr.time i = sp.ts s + 6 * sp.Δ := ht
    rw [ht']
    exact le_add_of_nonneg_right (mul_nonneg (Nat.ofNat_nonneg _) hΔ.le)
  · have hsl' : sp.slot (tr.time i) = s := hsl
    exact (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) s).2 (by omega)

/-- Bounded reset premises retain the operational timing of an older fast lock. -/
theorem ResetPremisesUpTo.fastLock_time_lt {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {x : Fin sp.n}
    {r m u : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC x r m D CV) (hmu : m < u)
    (htr : tr.time r ≤ sp.ts u + sp.Δ) : tr.time r < sp.ts u := by
  rcases hfl with ⟨ell, C, ⟨_, _, ht, _⟩, _⟩ | ⟨ell, A, _, hsl, _⟩
  · have ht' : tr.time r = sp.ts m + 6 * sp.Δ := ht
    rw [ht'] at htr ⊢
    exact ts_add_six_lt (by exact_mod_cast Compose.ts_add_two_le htr)
  · change sp.slot (tr.time r) = m at hsl
    by_contra h
    have := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg r) u).mp (not_lt.mp h)
    omega

/-- A fast lock of a label `m < u` written by `t_u + Δ` is written before `t_u` (an update of
`m` runs at `t_m + 6Δ`, so `m ≤ u − 2`; an optimistic check of `m` runs in slot `m`). -/
theorem fastLock_time_lt (hp : ResetPremises tr H proposer dg g ΔF a) {x : Fin sp.n}
    {r m u : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC x r m D CV) (hmu : m < u)
    (htr : tr.time r ≤ sp.ts u + sp.Δ) : tr.time r < sp.ts u :=
  (hp.toUpTo tr H le_rfl).fastLock_time_lt hfl hmu htr

/-- The reset seed precedes every post-drain slot and is bounded by the horizon. -/
theorem ResetPremisesUpTo.reset_seed_before_slot {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {u : Nat}
    (hR : drainTime sp a ≤ sp.ts u) :
    ∃ v r l O, HighOrigin tr H g v r l O ∧ tr.time r ≤ b ∧
      l < u ∧ tr.time r < sp.ts u := by
  obtain ⟨v, r, l, O, ho, hra, hl⟩ := hp.reset_seed
  have hlu : l + 2 ≤ u := by
    rw [drainTime_eq] at hR
    have := (SA.ts_le_iff sp).mp hR
    omega
  refine ⟨v, r, l, O, ho, hra.trans hp.reset_le, by omega, ?_⟩
  obtain ⟨_, D, CV, _, hf, _⟩ := hp.highOrigin_mem ho
  rcases hf with ⟨ell, C, ⟨_, _, ht, _⟩, _⟩ | ⟨ell, A, _, hsl, _⟩
  · have ht' : tr.time r = sp.ts l + 6 * sp.Δ := ht
    rw [ht']
    exact ts_add_six_lt (by exact_mod_cast hlu)
  · change sp.slot (tr.time r) = l at hsl
    by_contra h
    have := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg r) u).mp (not_lt.mp h)
    omega

/-- **The reset seed**: a high origin of a label `≤ slot(a)` written by `a` (as `Supplier`'s
`reset_seed`, keeping the write time). -/
theorem reset_seed (hp : ResetPremises tr H proposer dg g ΔF a) :
    ∃ v r l O, HighOrigin tr H g v r l O ∧ l ≤ sp.slot a ∧ tr.time r ≤ a := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨⟨y, hy, k, att, hs, hh, rfl⟩, -⟩ := hp.reset
  obtain ⟨r, hrk, l, O, ho, -⟩ := high_row_source hp hy hs hh.ge
  obtain ⟨-, D, CV, -, hfl, -⟩ := highOrigin_mem hp ho
  have h₀ : tr.time r ≤ tr.time k := hr.time_mono hrk.le
  have h₁ : sp.ts l ≤ tr.time k := (ts_le_of_fastLock hp hfl).trans h₀
  exact ⟨y, r, l, O, ho,
    by exact_mod_cast (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) l).1 h₁, h₀⟩

/-- The reset precedes every slot start after the drain. -/
theorem reset_lt_ts (hp : ResetPremises tr H proposer dg g ΔF a) {u : Nat}
    (hR : drainTime sp a ≤ sp.ts u) : a < sp.ts u := by
  have hΔ := sp.toParams.hΔ
  have hca := cutZ_lt_reset hp.run hp.healthy hp.reset
  have hlt := lt_cutZ sp g
  have hg0 := gbar_nonneg g
  have ha0 : 0 ≤ a := hg0.trans ((le_add_of_nonneg_right
    (mul_nonneg (Nat.ofNat_nonneg _) hΔ.le)).trans (hlt.trans hca).le)
  have h3 : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
    have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
    omega
  have h4 : sp.ts ((sp.slot a : Int) + 1) ≤ drainTime sp a := by
    rw [drainTime_eq]
    exact (SA.ts_le_iff sp).2 (by push_cast; omega)
  exact h3.trans_le (h4.trans hR)

/-- No honest optimistic check selects a block of the proposal's slot before its actual call. -/
theorem proposal_no_optimistic_of_run
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {p : Fin sp.n}
    (hpH : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt p i ℓp)
    (hcall : ℓp.call = .proposal)
    (hti : tr.time i = sp.ts s) :
    ∀ x ∈ H, ∀ k' < i, ∀ C CV, ¬ SA.OptimisticLockAt tr.projAC x k' s C CV :=
  Compose.proposal_no_optimistic_of hrun hnc hf hpH hc hcall hti

/-- Whole-run specialization of operational proposal ordering. -/
theorem proposal_no_optimistic (hp : ResetPremises tr H proposer dg g ΔF a) {p : Fin sp.n}
    (hpH : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt p i ℓp)
    (hcall : ℓp.call = .proposal) (hti : tr.time i = sp.ts s) :
    ∀ x ∈ H, ∀ k' < i, ∀ C CV, ¬ SA.OptimisticLockAt tr.projAC x k' s C CV :=
  proposal_no_optimistic_of_run hp.run hp.noColl (faulty_lt_half hp p) hpH hc hcall hti


end Consensus.Goldilocks.Healing
