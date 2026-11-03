module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealComposeDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Range
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.CallLag
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealBound

public section

/-! # Goldilocks Refinement: the reset from the drain on a generic finite run (#136, P7)

workbench `heal_bound.md` §1 steps 1–7, `healing_parallel_plan.md` P7,
`healing_supply_repair_contracts.md` S4. The drain-to-reset composition on a
generic trace, with no query type:

* the frame base `lo := r + 4Δ` for an abstract ready scalar `r ≥ ḡ`, and the pigeonhole window
  (`exists_frameWindow_of_noAdvance`);
* the slot alignment `s₀ := ⌈a_f / 4Δ⌉`, `N := s₀ + L_drain + 2ρ + 1`, `ρ = δ_t + G − 1`, and the
  whole frame `[t_{s₀}, t_N + 2Δ]` inside the window, before `B − 1` (`heal_bound_sufficient`);
* the gap `G` from a generic gap premise, needed only for frames `t_N + 2Δ < B`, so each caller
  pays its own endpoint (a horizon for `FinalQuery`, heal for a healthy preparation query);
* the drain (`DrainOutputs` at the service horizon `b`), and the rise (`FrameWindow.rise_reset`).

`B = resetBound r Δ λ δ_t G L_drain`. The coefficient scalars `G`, `L_drain` and the ready scalar
`r` stay abstract. `exists_reset_of_drain_awake` fixes `λ = 2Δ` and produces the calls and the
snapshot from wakefulness (`CallLag`), paying `c_z + Δ + 1 ≤ lo` explicitly. -/

namespace Consensus.Goldilocks.Refinement

open SA (gbar)
open Healing

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- **The reset from the drain** (heal_bound §1 steps 1–7) on a generic finite run: service up to
`b`, awake on `[ḡ, b]`, catch-up `2Δ`, no restart after `ḡ`, the calls `hcallZ`/`hcall` with lag
`λ` from `lo = r + 4Δ`, the gap `G` on every frame ending before `B`, and the drain at `b`, give a
reset at a time `a ≤ B = resetBound r Δ λ δ_t G L_drain`, provided `B ≤ b`. -/
theorem exists_reset_of_drain (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : 3 * Hᶜ.ncard ≤ sp.n - 1)
    {g ΔF b lam r : Time} {G Ld : Nat}
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hH : H.Nonempty) (hsnap : ∃ j, FirstCutAfter tr j (cutZ sp.toParams g))
    (hδ : 3 ≤ sp.toParams.fg.δt)
    (hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hlam : 0 ≤ lam) (hr : 0 ≤ r) (hgr : gbar g ≤ r) (hG : 1 ≤ G)
    (hcallZ : ∀ z ∈ H, ∀ m, r + 4 * sp.Δ ≤ tr.time m → tr.time m ≤ b → ∃ j < m,
      tr.IsCall z j ∧ tr.deadline z j (max (cutZ sp.toParams g) g) sp.Δ ≤ tr.time j)
    (hcall : ∀ z ∈ H, ∀ i m, r + 4 * sp.Δ ≤ tr.time i → tr.time i + lam ≤ tr.time m →
      tr.time m ≤ b → ∃ j < m, tr.IsCall z j ∧
        tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hb : resetBound r sp.Δ lam sp.toParams.fg.δt G Ld ≤ b)
    (hgp : ∀ s₀ N : Nat, r + 4 * sp.Δ ≤ sp.ts s₀ →
      sp.ts N + 2 * sp.Δ < resetBound r sp.Δ lam sp.toParams.fg.δt G Ld →
      ∀ x₀, s₀ ≤ x₀ → x₀ + G ≤ N + 1 → ∃ x, x₀ ≤ x ∧ x < x₀ + G ∧ proposer x ∈ H ∧
        ∃ k P, tr.ProposesAt (proposer x) k P ∧ P.slot = x)
    (hdrain : DrainOutputs tr proposer H g G Ld b) :
    ∃ a, IsReset tr H g a ∧ a ≤ resetBound r sp.Δ lam sp.toParams.fg.δt G Ld := by
  classical
  set D := sp.Δ with hDdef
  set δt := sp.toParams.fg.δt with hδdef
  have hD : 0 < D := sp.toParams.hΔ
  have hq : Hᶜ.ncard < sp.toParams.fg.q := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < (2 * sp.n + 2) / 3
    omega
  have hf2 : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  set lo : Time := r + 4 * D with hlodef
  set ρ : Nat := δt + G - 1 with hρdef
  have hρZ : (ρ : ℤ) = (δt : ℤ) + (G : ℤ) - 1 := by omega
  set len : Time := 4 * D * ((Ld : ℤ) + 2 * ((δt : ℤ) + (G : ℤ) - 1) + 2) + 2 * D with hlendef
  set B := resetBound r D lam δt G Ld with hBdef
  have hB : lo + 6 * (len + lam) = B := by
    rw [hBdef, resetBound_eq, hlodef, hlendef]; ring
  have hlen0 : 0 ≤ len := by
    have : (0 : ℤ) ≤ (δt : ℤ) + (G : ℤ) - 1 := by omega
    rw [hlendef]; positivity
  -- the advance case: an honest signature above `H_z` up to `B` is a reset
  by_cases hadv : ∃ y ∈ H, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ B ∧
      HZ tr H g + 1 ≤ att.h
  · obtain ⟨y, hy, k, att, hs, hkT, hh⟩ := hadv
    obtain ⟨a, ha, hak⟩ := reset_of_height_advance hrun hq hy hs hh
    exact ⟨a, ha, hak.trans hkT⟩
  have hna : ∀ v ∈ H, ∀ k att, tr.SignAt v k att → tr.time k < B + 1 →
      att.h ≤ HZ tr H g := fun v hv k att hs hkT => by
    by_contra h
    exact hadv ⟨v, hv, k, att, hs, Int.lt_add_one_iff.mp hkT, by omega⟩
  -- the pigeonhole window
  obtain ⟨af, haf, hafl, floor, contest, kindJ, J, hwin⟩ :=
    exists_frameWindow_of_noAdvance (lo := lo) (len := len) (lam := lam) (T := B + 1)
      hrun hnc hf2 hq hsvc hcatch hH hsnap hlen0 hlam hna (by rw [hlodef]; linarith)
      (fun z hz m hm hmT => hcallZ z hz m hm (by have := Int.lt_add_one_iff.mp hmT; linarith))
      (fun z hz i m hi him hmT =>
        hcall z hz i m hi him (by have := Int.lt_add_one_iff.mp hmT; linarith))
      (by rw [hB]; linarith)
  -- slot alignment
  have h4D : 0 < 4 * D := by linarith
  set s₀Z : ℤ := (af + 4 * D - 1) / (4 * D) with hs₀Z
  have hs₀lo := Int.ediv_mul_le (af + 4 * D - 1) h4D.ne'
  have hs₀hi := Int.lt_ediv_add_one_mul_self (af + 4 * D - 1) h4D
  rw [← hs₀Z] at hs₀lo hs₀hi
  have haf0 : 0 ≤ af := by linarith
  have hs₀nn : 0 ≤ s₀Z := Int.ediv_nonneg (by linarith) h4D.le
  set s₀ : Nat := s₀Z.toNat with hs₀def
  have hs₀c : (s₀ : ℤ) = s₀Z := Int.toNat_of_nonneg hs₀nn
  have hts₀lo : af ≤ sp.ts s₀ := by
    simp only [SA.SAParams.ts]; rw [hs₀c]; nlinarith
  have hts₀hi : 4 * D * (s₀ : ℤ) < af + 4 * D := by rw [hs₀c]; nlinarith
  set N : Nat := s₀ + Ld + 2 * ρ + 1 with hNdef
  have hpos : (0 : ℤ) ≤ ((s₀ : ℤ) + Ld) + 2 * ((δt : ℤ) + G - 1) + 1 := by omega
  -- the arithmetic of the frame (heal_bound_sufficient .1, .2.1)
  have hfitN : sp.ts N + 2 * D < af + len ∧ sp.ts N + 2 * D ≤ B - 1 := by
    have hk : (0 : ℤ) ≤ sp.k := by positivity
    obtain ⟨h1, -, -, -⟩ := heal_bound_sufficient (D := D) (ready := r) (lam := lam)
      (k := sp.k) (δt := δt) (X := G) (Ld := Ld) (s₀ := s₀) (u := s₀ + Ld)
      (a := 0) (sa := 0) (uMin := 0) (lo := lo) (af := af) (len := len)
      (heal := r + healBoundCoeff sp.k δt G Ld * D + 6 * lam - 2)
      (q := r + healBoundCoeff sp.k δt G Ld * D + 6 * lam - 2)
      hD hr hlam hk (by exact_mod_cast (show 1 ≤ δt by omega)) (by exact_mod_cast hG)
      (by positivity) le_rfl hlendef hafl hts₀hi le_rfl
      (by have := mul_nonneg h4D.le hpos; linarith) (by simp) (by linarith) le_rfl le_rfl
    have hN' : sp.ts N = 4 * D * ((s₀ : ℤ) + Ld + 2 * ((δt : ℤ) + G - 1) + 1) := by
      simp only [SA.SAParams.ts, hNdef]; push_cast; rw [hρZ]
    refine ⟨by rw [hN']; exact h1, ?_⟩
    rw [hN']
    have := hafl
    rw [hB] at this
    linarith
  have hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts N + 2 * D)
      floor contest kindJ J :=
    frameWindow_sub hwin hts₀lo (by linarith [hfitN.1])
  have hts₀r : r + 4 * D ≤ sp.ts s₀ := by linarith
  have hm : gbar g + 4 * D ≤ sp.ts s₀ := by linarith
  have hmb : sp.ts N + 2 * D ≤ b := by linarith [hfitN.2]
  -- the gap, on a frame ending before `B`
  have hgpN := hgp s₀ N hts₀r (by linarith [hfitN.2])
  -- the drain
  obtain ⟨u, hwarm, huLd, z, hz, hdes, kP, P, hP, hPs, hlow⟩ :=
    hdrain.warm hframe hm (by omega) hmb
      (fun v hv k att hs hk => hna v hv k att hs (by linarith [hfitN.2])) hgpN
  have hN2 : u + 2 * ρ + 1 ≤ N := by rw [hNdef]; omega
  -- the rise
  obtain ⟨a, ha, hab⟩ := hframe.rise_reset hrun hnc hsvc hawake hf hcatch hnr hm hwarm hδ hΔF
    hgpN hN2 hmb hz hdes hP hPs hlow
  refine ⟨a, ha, hab.trans ?_⟩
  have hts : sp.ts (u + 2 * (δt + G - 1) + 1 : Nat) ≤ sp.ts N :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast (show _ ≤ N by omega))
  linarith [hfitN.2]

/-- **The reset from the drain, from wakefulness** (`λ = 2Δ`). `exists_reset_of_drain` with the
snapshot, `hcallZ` and `hcall` produced by `CallLag` from wakefulness on `[ḡ, b]`; the snapshot
call condition `c_z + Δ + 1 ≤ r + 4Δ` is paid explicitly. -/
theorem exists_reset_of_drain_awake (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : 3 * Hᶜ.ncard ≤ sp.n - 1)
    {g ΔF b r : Time} {G Ld : Nat}
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hH : H.Nonempty) (hδ : 3 ≤ sp.toParams.fg.δt)
    (hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hr : 0 ≤ r) (hgr : gbar g ≤ r) (hG : 1 ≤ G)
    (hcz : cutZ sp.toParams g + sp.Δ + 1 ≤ r + 4 * sp.Δ)
    (hb : resetBound r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld ≤ b)
    (hgp : ∀ s₀ N : Nat, r + 4 * sp.Δ ≤ sp.ts s₀ →
      sp.ts N + 2 * sp.Δ < resetBound r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld →
      ∀ x₀, s₀ ≤ x₀ → x₀ + G ≤ N + 1 → ∃ x, x₀ ≤ x ∧ x < x₀ + G ∧ proposer x ∈ H ∧
        ∃ k P, tr.ProposesAt (proposer x) k P ∧ P.slot = x)
    (hdrain : DrainOutputs tr proposer H g G Ld b) :
    ∃ a, IsReset tr H g a ∧ a ≤ resetBound r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hrb : r + 4 * sp.Δ ≤ b := by
    have hc : (0 : ℤ) ≤ 24 * (Ld : ℤ) + 48 * ((sp.toParams.fg.δt : ℤ) + G - 1) + 64 := by omega
    have := mul_nonneg hc hΔ.le
    rw [resetBound_eq] at hb
    linarith
  obtain ⟨j, hj, -⟩ := snapshot_of_awake hrun hawake hH (by linarith)
  exact exists_reset_of_drain hrun hnc hf hsvc hawake hcatch hnr hH ⟨j, hj⟩ hδ hΔF
    (by linarith) hr hgr hG
    (fun z hz m hm hmb => snapshotCall_of_awake hrun hawake hcz (T := b + 1) le_rfl z hz m hm
      (by linarith))
    (fun z hz i m hi him hmb => callLag_of_awake hrun hawake (lo := r + 4 * sp.Δ) (T := b + 1)
      (by linarith) le_rfl z hz i m hi him (by linarith))
    hb hgp hdrain

end Consensus.Goldilocks.Refinement

end
