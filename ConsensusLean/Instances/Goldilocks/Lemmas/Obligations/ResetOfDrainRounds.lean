module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealComposeDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Range
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.CallLag
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameWindowExists
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.RiseWindow
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.RiseRounds
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.WarmFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealBoundRounds
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Obligations: the reset from the drain with key-dependent rise rounds

The five-window drain reset with the key-dependent window of `Healing.M1.RiseWindow` and the
`r`-round rise of `Healing.M1.RiseRounds`:

* the window of key value `v` has the length `len(v) = 4D(L_drain + 2) + r(v)·4Dρ + 2D`,
  `r(v) = 2 − ⌊(v − 2HZ)/2⌋`, `ρ = δ_t + G − 1`; the five attempts end by
  `lo + 5(4D(L_drain + 2) + 2D + λ) + 6·4Dρ` (`exists_frameWindow_seq_of_service`);
* at the vote cut of slot `s₀` the window floor has `HZ + 1 ≤ floor + r(v)`
  (`le_floor_add_riseRounds`), and the warm proposal is at or above the floor
  (`FrameWindow.floor_le_warm_proposal`), so `HZ + 1 ≤ σ[P].h + r(v)`;
* `FrameWindow.rise_reset_rounds` gives the reset by `t_{u + r(v)ρ + 1} + 2Δ`.

`B = resetBoundRounds r Δ λ δ_t G L_drain = r + (20 L_drain + 24ρ + 54)·Δ + 5λ`.

The window step is `exists_riseWindow_of_service` (`Healing.M1.RiseWindow`); the window length
and the round count are `riseLen` and `riseRounds` (`riseLen_eq`, `riseRounds_eq`). -/

namespace Consensus.Goldilocks.Obligations

open SA (gbar)
open Healing

/-- The reset bound of the key-dependent rise route: `lo + 5(4D(L_drain + 2) + 2D + λ) + 6·4Dρ`
at `lo = r + 4D`, `ρ = δ_t + X − 1`. -/
def resetBoundRounds (r D lam δt X Ld : ℤ) : ℤ :=
  r + (20 * Ld + 24 * (δt + X - 1) + 54) * D + 5 * lam

/-- Unfolding equation of `resetBoundRounds`. -/
theorem resetBoundRounds_eq (r D lam δt X Ld : ℤ) :
    resetBoundRounds r D lam δt X Ld = r + (20 * Ld + 24 * (δt + X - 1) + 54) * D + 5 * lam := by
  unfold resetBoundRounds
  rfl

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Slot alignment: `s₀ = ⌈a_f / 4D⌉` has `a_f ≤ t_{s₀} < a_f + 4D`. -/
theorem exists_slot_align (sp : SA.SAParams) {af : Time} (haf : 0 ≤ af) :
    ∃ s₀ : Nat, af ≤ sp.ts s₀ ∧ 4 * sp.Δ * (s₀ : ℤ) < af + 4 * sp.Δ := by
  have h4D : 0 < 4 * sp.Δ := by have := sp.toParams.hΔ; linarith
  set s₀Z : ℤ := (af + 4 * sp.Δ - 1) / (4 * sp.Δ) with hs₀Z
  have hs₀lo := Int.ediv_mul_le (af + 4 * sp.Δ - 1) h4D.ne'
  have hs₀hi := Int.lt_ediv_add_one_mul_self (af + 4 * sp.Δ - 1) h4D
  rw [← hs₀Z] at hs₀lo hs₀hi
  have hs₀nn : 0 ≤ s₀Z := Int.ediv_nonneg (by linarith) h4D.le
  have hs₀c : ((s₀Z.toNat : Nat) : ℤ) = s₀Z := Int.toNat_of_nonneg hs₀nn
  refine ⟨s₀Z.toNat, ?_, ?_⟩
  · change af ≤ 4 * sp.Δ * ((s₀Z.toNat : Nat) : ℤ)
    rw [hs₀c]; linarith
  · rw [hs₀c]; linarith

/-- **The rise rounds at the warm proposal.** On a window `[a_f, a_f + len]` with merged key
`v ≥ 2HZ` and a `FrameWindow`, the actual warm proposal `P` of slot `u` of a slot-aligned frame
`[t_{s₀}, t_N + 2Δ]` inside the window has `HZ + 1 ≤ σ[P].h + r(v)`: the window floor at the
vote cut of slot `s₀` (`le_floor_add_riseRounds`), and `floor ≤ σ[P].h`
(`FrameWindow.floor_le_warm_proposal`). -/
theorem rounds_le_warm_proposal
    {g ΔF b af len : Time} {s₀ u N floor v : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hwin : FrameWindow (tr := tr) (H := H) af (af + len) floor kindJ J)
    (hK : ∀ y ∈ H, ∀ i, af ≤ tr.time i → tr.time i ≤ af + len →
      frameKey' (tr.state y i).fg = v)
    (hv : 2 * HZ tr H g ≤ v) (haf : af ≤ sp.ts s₀) (hend : sp.ts N + 2 * sp.Δ ≤ af + len)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (huN : u ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u) :
    HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h + riseRounds (HZ tr H g) v := by
  have hΔ := sp.toParams.hΔ
  have hsN : sp.ts s₀ ≤ sp.ts N := (SA.ts_le_iff sp).2 (by exact_mod_cast (by omega : s₀ ≤ N))
  have hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts N + 2 * sp.Δ)
      floor kindJ J := frameWindow_sub hwin haf hend
  obtain ⟨c, e, hvc, hes, hchi⟩ := honest_votes_before_of_service hrun hnc hsvc hawake hf
    hcatch hnr (m := s₀) hm (by linarith) z hz
  obtain ⟨ell, hc, he⟩ := hvc
  have hcast : SA.CastAt tr.projAC z c ell e := ⟨hc, he⟩
  have hlr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hslot : sp.slot (tr.time c) = s₀ := (SA.castAt_spec hlr hz hcast).2.1.symm.trans hes
  have hsc : sp.ts s₀ ≤ tr.time c :=
    (SA.ts_le_iff_le_slot sp (hlr.time_nonneg c) _).2 (by
      change (s₀ : Int) ≤ sp.slot (tr.time c)
      rw [hslot])
  have hc1 : af ≤ tr.time c := by linarith
  have hc2 : tr.time c ≤ af + len := by linarith
  have hkey := hK z hz c hc1 hc2
  have h1 : 1 ≤ (tr.state z c).fg.hmax := by
    have := hj_lt_hmax hrun hz c
    omega
  have hZf := le_floor_add_riseRounds (tr.state z c).fg h1 (HZ := HZ tr H g)
    (by rw [hkey]; exact hv)
  rw [hkey, hwin.floor_eq z hz c hc1 hc2] at hZf
  have hPf := hframe.floor_le_warm_proposal hrun hnc hsvc hawake hf hcatch hnr hm hwarm
    huN hmb hz hdes hP hPs
  omega

/-- **The reset from the drain, key-dependent rise rounds.** The premises of
the five-window drain reset with `resetBoundRounds` for its bound: the reset is at a time
`a ≤ B = resetBoundRounds r Δ λ δ_t G L_drain`, provided `B ≤ b`. -/
theorem exists_reset_of_drain_rounds (hrun : GoldilocksRun proposer dg H tr)
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
    (hb : resetBoundRounds r sp.Δ lam sp.toParams.fg.δt G Ld ≤ b)
    (hgp : ∀ s₀ N : Nat, r + 4 * sp.Δ ≤ sp.ts s₀ →
      sp.ts N + 2 * sp.Δ < resetBoundRounds r sp.Δ lam sp.toParams.fg.δt G Ld →
      ∀ x₀, s₀ ≤ x₀ → x₀ + G ≤ N + 1 → ∃ x, x₀ ≤ x ∧ x < x₀ + G ∧ proposer x ∈ H ∧
        ∃ k P, tr.ProposesAt (proposer x) k P ∧ P.slot = x)
    (hdrain : DrainOutputs tr proposer H g G Ld b) :
    ∃ a, IsReset tr H g a ∧ a ≤ resetBoundRounds r sp.Δ lam sp.toParams.fg.δt G Ld := by
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
  set d : Time := 4 * D * ((Ld : ℤ) + 2) with hddef
  set ρt : Time := 4 * D * (ρ : ℤ) with hρtdef
  set B := resetBoundRounds r D lam δt G Ld with hBdef
  have hsum : 5 * (d + 2 * D + lam) + 6 * ρt =
      5 * (4 * D * ((Ld : ℤ) + 2) + 2 * D + lam) + 6 * (4 * D * ((δt : ℤ) + G - 1)) := by
    rw [hddef, hρtdef, hρZ]
  have hB : lo + (5 * (d + 2 * D + lam) + 6 * ρt) = B := by
    rw [hsum, hBdef, resetBoundRounds_eq, hlodef]; ring
  have hd0 : 0 ≤ d :=
    mul_nonneg (mul_nonneg zero_le_four hD.le) (add_nonneg (Int.natCast_nonneg _) zero_le_two)
  have hρt0 : 0 ≤ ρt := mul_nonneg (mul_nonneg zero_le_four hD.le) (Int.natCast_nonneg _)
  have h2D : (0 : Time) ≤ 2 * D := by linarith only [hD]
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
  -- the key-dependent window
  have hlo2 : gbar g + 2 * D ≤ lo := by rw [hlodef]; linarith only [hgr, hD]
  have hrange := hmax_range (T := B + 1) (lo := lo) hrun hnc hf2 hq hsvc hcatch hH hsnap hna
    hlo2
      (fun z hz m hm hmT => hcallZ z hz m hm ((Int.lt_add_one_iff.mp hmT).trans hb))
  obtain ⟨v, hv1, hv2, af, haf, -, hwinE0, hK, floor, kindJ, J, hwin, -⟩ :=
    exists_riseWindow_of_service hrun hnc hf2 hsvc hcatch (lo := lo) (lam := lam)
      (T := B + 1) (HZ := HZ tr H g) hd0 hρt0 h2D hlam hlo2 hrange
      (fun z hz i m hi him hmT =>
        hcall z hz i m hi him ((Int.lt_add_one_iff.mp hmT).trans hb))
      (by rw [hB]; exact lt_add_one B)
  obtain ⟨rr, hrrdef⟩ : ∃ rr, riseRounds (HZ tr H g) v = rr := ⟨_, rfl⟩
  have hrr2 : rr ≤ 2 := hrrdef ▸ riseRounds_le_two _ _
  set len : Time := riseLen d ρt (2 * D) (HZ tr H g) v with hlendef
  have hlenE : len = 4 * D * ((Ld : ℤ) + (rr : ℤ) * ((δt : ℤ) + G - 1) + 2) + 2 * D := by
    rw [hlendef, riseLen_eq, hrrdef, hddef, hρtdef, hρZ]; ring
  -- slot alignment
  have h4D : 0 < 4 * D := by linarith only [hD]
  obtain ⟨s₀, hts₀lo, hts₀hi⟩ := exists_slot_align sp (af := af)
    (by linarith only [haf, hlodef, hr, hD, hlam])
  set N : Nat := s₀ + Ld + rr * ρ + 1 with hNdef
  have hpos : (0 : ℤ) ≤ ((s₀ : ℤ) + Ld) + (rr : ℤ) * ((δt : ℤ) + G - 1) + 1 := by
    have : (0 : ℤ) ≤ (rr : ℤ) * ((δt : ℤ) + G - 1) := by
      apply mul_nonneg <;> omega
    omega
  -- the arithmetic of the frame (heal_bound_sufficient_rounds .1)
  have hfitN : sp.ts N + 2 * D < af + len ∧ sp.ts N + 2 * D ≤ B - 1 := by
    have hk : (0 : ℤ) ≤ sp.k := Int.natCast_nonneg _
    have hwinE : af + len ≤ lo + (5 * (4 * D * ((Ld : ℤ) + 2) + 2 * D + lam) +
        6 * (4 * D * ((δt : ℤ) + G - 1))) := by
      rw [← hsum]; exact hwinE0
    obtain ⟨h1, -, -, -⟩ := heal_bound_sufficient_rounds (D := D) (ready := r) (lam := lam)
      (k := sp.k) (δt := δt) (X := G) (Ld := Ld) (s₀ := s₀) (u := s₀ + Ld) (rr := rr)
      (a := 0) (sa := 0) (uMin := 0) (lo := lo) (af := af) (len := len)
      (heal := r + healBoundCoeffRounds sp.k δt G Ld * D + 5 * lam - 2)
      (q := r + healBoundCoeffRounds sp.k δt G Ld * D + 5 * lam - 2)
      hD hr hlam hk (by exact_mod_cast (show 1 ≤ δt by omega)) (by exact_mod_cast hG)
      (Int.natCast_nonneg _) le_rfl hlenE hwinE hts₀hi
      le_rfl (by linarith only [mul_nonneg h4D.le hpos, hD]) (by simp) (by omega)
      le_rfl le_rfl
    have hN' : sp.ts N = 4 * D * ((s₀ : ℤ) + Ld + (rr : ℤ) * ((δt : ℤ) + G - 1) + 1) := by
      rw [show sp.ts N = 4 * D * (N : ℤ) from rfl, hNdef]; push_cast; rw [hρZ]
    refine ⟨by rw [hN']; exact h1, ?_⟩
    rw [hN']
    have := hwinE0
    rw [← hB] at ⊢
    linarith only [h1, this]
  have hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts N + 2 * D)
      floor kindJ J :=
    frameWindow_sub hwin hts₀lo hfitN.1.le
  have hts₀r : r + 4 * D ≤ sp.ts s₀ := by linarith only [hts₀lo, haf, hlam, hlodef]
  have hm : gbar g + 4 * D ≤ sp.ts s₀ := by linarith only [hts₀r, hgr]
  have hmb : sp.ts N + 2 * D ≤ b := by linarith only [hfitN.2, hb]
  have hts {x y : Nat} (h : x ≤ y) : sp.ts x ≤ sp.ts y :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast h)
  -- the gap, on a frame ending before `B`
  have hgpN := hgp s₀ N hts₀r (by linarith only [hfitN.2])
  -- the drain
  obtain ⟨u, hwarm, huLd, z, hz, hdes, kP, P, hP, hPs, -⟩ :=
    hdrain.warm hframe hm (by omega) hmb
      (fun v hv k att hs hk => hna v hv k att hs (by linarith only [hfitN.2, hk])) hgpN
  -- the rise rounds at the warm proposal
  have hrise := rounds_le_warm_proposal hwin hK hv1 hts₀lo (by linarith only [hfitN.1]) hrun hnc
    hsvc hawake hf hcatch hnr hm hwarm (by omega) hmb hz hdes hP hPs
  rw [hrrdef] at hrise
  -- the rise in `rr` rounds
  obtain ⟨a, ha, hab⟩ := hframe.rise_reset_rounds hrun hnc hsvc hawake hf hcatch hnr hm hwarm
    hδ hΔF hgpN hrr2 (show u + rr * ρ + 1 ≤ N by omega) hmb hz hdes hP hPs
    (by omega)
  refine ⟨a, ha, hab.trans ?_⟩
  have := hts (show u + rr * ρ + 1 ≤ N by omega)
  linarith only [hfitN.2, this]

/-- **The reset from the drain, key-dependent rise rounds, from wakefulness** (`λ = 2Δ`).
`exists_reset_of_drain_rounds` with the snapshot, `hcallZ` and `hcall` produced by `CallLag` from
wakefulness on `[ḡ, b]`; the snapshot call condition `c_z + Δ + 1 ≤ r + 4Δ` is paid explicitly. -/
theorem exists_reset_of_drain_rounds_awake (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : 3 * Hᶜ.ncard ≤ sp.n - 1)
    {g ΔF b r : Time} {G Ld : Nat}
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hH : H.Nonempty) (hδ : 3 ≤ sp.toParams.fg.δt)
    (hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hr : 0 ≤ r) (hgr : gbar g ≤ r) (hG : 1 ≤ G)
    (hcz : cutZ sp.toParams g + sp.Δ + 1 ≤ r + 4 * sp.Δ)
    (hb : resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld ≤ b)
    (hgp : ∀ s₀ N : Nat, r + 4 * sp.Δ ≤ sp.ts s₀ →
      sp.ts N + 2 * sp.Δ < resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld →
      ∀ x₀, s₀ ≤ x₀ → x₀ + G ≤ N + 1 → ∃ x, x₀ ≤ x ∧ x < x₀ + G ∧ proposer x ∈ H ∧
        ∃ k P, tr.ProposesAt (proposer x) k P ∧ P.slot = x)
    (hdrain : DrainOutputs tr proposer H g G Ld b) :
    ∃ a, IsReset tr H g a ∧
      a ≤ resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hrb : r + 4 * sp.Δ ≤ b := by
    have hc : (0 : ℤ) ≤ 20 * (Ld : ℤ) + 24 * ((sp.toParams.fg.δt : ℤ) + G - 1) + 60 := by omega
    have := mul_nonneg hc hΔ.le
    rw [resetBoundRounds_eq] at hb
    linarith
  obtain ⟨j, hj, -⟩ := snapshot_of_awake hrun hawake hH (by linarith)
  exact exists_reset_of_drain_rounds hrun hnc hf hsvc hawake hcatch hnr hH ⟨j, hj⟩ hδ hΔF
    (by linarith) hr hgr hG
    (fun z hz m hm hmb => snapshotCall_of_awake hrun hawake hcz (T := b + 1) le_rfl z hz m hm
      (by linarith))
    (fun z hz i m hi him hmb => callLag_of_awake hrun hawake (lo := r + 4 * sp.Δ) (T := b + 1)
      (by linarith) le_rfl z hz i m hi him (by linarith))
    hb hgp hdrain

end Consensus.Goldilocks.Obligations

end
