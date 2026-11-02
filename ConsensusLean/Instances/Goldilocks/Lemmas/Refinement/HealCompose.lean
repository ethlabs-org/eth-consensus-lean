module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Range
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.RiseGap
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealBound
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealComposeDefs

public section

/-! # Goldilocks Refinement: M1′ composition up to the reset, conditional on the drain (#136)

consensus-lean#136, workbench `heal_bound.md` §1 steps 1–7, `healing_parallel_plan.md` P7.
`reset_of_drain` composes the landed pieces:

* the frame base `lo := max ready 0 + 4Δ` and the pigeonhole window
  (`exists_frameWindow_of_noAdvance`, with `hmax_range` and `frameKey_lag_le` inside it);
* the slot alignment `s₀ := ⌈a_f / 4Δ⌉`, `N := s₀ + L_drain + 2ρ + 1`, and the frame
  `[t_{s₀}, t_N + 2Δ]` inside the window (`heal_bound_sufficient`);
* the honest-proposer gap `G = X` (`hgp_of_query`, duty → proposal in the leaf form (H2));
* the rise (`FrameWindow.rise_reset`, `ρ = δ_t + X − 1`).

The only open input is the drain, `DrainOutputs` (to be supplied by Sol's DrainWindow, P5).
If an honest node signs above `H_z` before the end of the pigeonhole horizon, that signature
gives the reset directly (`reset_of_height_advance`). `Δ_F` stays a parameter
(`6Δ + Δ_F ≤ 4Δ·δ_t`). The bound is `a ≤ max ready 0 + (24 L_drain + 48ρ + 64)·Δ + 6λ`. It is one
unit weaker than the card's `− 1`: the advance branch signs at a time `< lo + 6(len + λ) + 1`. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape
open SA (gbar)
open Healing

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **M1′ up to the reset, conditional on the drain** (heal_bound §1 steps 1–7). With the run
premises of `exists_frameWindow_of_noAdvance` and `FrameWindow.rise_reset` (service up to `b`,
awake on `[ḡ, b]`, catch-up `2Δ`, no restart after `ḡ`, the calls `hcallZ`/`hcall` with lag `λ`),
the duty → proposal premise (H2), and the drain (`DrainOutputs`, P5): a reset at a time
`a ≤ max ready 0 + (24 L_drain + 48ρ + 64)·Δ + 6λ`, `ρ = δ_t + X − 1`, `X = Q.index`. -/
theorem reset_of_drain (Q : FinalQuery S A V)
    {dg : Digest (List (FG.Att Q.params.n)) (SA.Payload Q.params.n)}
    (hrun : GoldilocksRun (runProposer S Q.run.2 Q.hn) dg (honestKeys S Q.run.2) Q.trace)
    (hnc : Compose.NoCollRun dg Q.trace)
    (hf : 3 * (honestKeys S Q.run.2)ᶜ.ncard ≤ Q.params.n - 1)
    {g ΔF b lam : Time} {Ld : Nat}
    (hsvc : ResetService Q.trace (honestKeys S Q.run.2) g ΔF b)
    (hawake : ∀ y ∈ honestKeys S Q.run.2, ∀ t, gbar g ≤ t → t ≤ b → Q.trace.awake y t)
    (hcatch : CatchRun Q.trace (honestKeys S Q.run.2) g (2 * Q.params.Δ))
    (hnr : NoRestartAfter Q.trace (honestKeys S Q.run.2) (gbar g))
    (hH : (honestKeys S Q.run.2).Nonempty)
    (hsnap : ∃ j, FirstCutAfter Q.trace j (cutZ Q.params.toParams g))
    (hδ : 3 ≤ Q.params.toParams.fg.δt)
    (hΔF : 6 * Q.params.Δ + ΔF ≤ 4 * Q.params.Δ * (Q.params.toParams.fg.δt : Time))
    (hlam : 0 ≤ lam)
    (hgr : gbar g ≤ max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0)
    (hcallZ : ∀ z ∈ honestKeys S Q.run.2, ∀ m,
      max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0 + 4 * Q.params.Δ ≤ Q.trace.time m →
      Q.trace.time m ≤ b → ∃ j < m, Q.trace.IsCall z j ∧
        Q.trace.deadline z j (max (cutZ Q.params.toParams g) g) Q.params.Δ ≤ Q.trace.time j)
    (hcall : ∀ z ∈ honestKeys S Q.run.2, ∀ i m,
      max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0 + 4 * Q.params.Δ ≤ Q.trace.time i →
      Q.trace.time i + lam ≤ Q.trace.time m → Q.trace.time m ≤ b → ∃ j < m,
        Q.trace.IsCall z j ∧
          Q.trace.deadline z j (max (Q.trace.time i) g) Q.params.Δ ≤ Q.trace.time j)
    (hb : resetBound (max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0) Q.params.Δ lam
      Q.params.toParams.fg.δt (Q.index : Nat) Ld ≤ b)
    (hhor : resetBound (max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0) Q.params.Δ lam
      Q.params.toParams.fg.δt (Q.index : Nat) Ld + 24 * Q.params.Δ ≤ Q.run.2.horizon)
    (hpropose : ∀ s, HonestReadyIn Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) s ((Sys (family S) V).cDur (K S A) Q.run)
      ((finalGrid S A V Q).slotTime s) →
      ∃ P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) s P)
    (hdrain : DrainOutputs Q.trace (runProposer S Q.run.2 Q.hn) (honestKeys S Q.run.2) g
      (Q.index : Nat) Ld b) :
    ∃ a, IsReset Q.trace (honestKeys S Q.run.2) g a ∧
      a ≤ resetBound (max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0) Q.params.Δ lam
        Q.params.toParams.fg.δt (Q.index : Nat) Ld := by
  classical
  set H := honestKeys S Q.run.2 with hHdef
  set r := max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0 with hr
  set D := Q.params.Δ with hDdef
  set δt := Q.params.toParams.fg.δt with hδdef
  set X : Nat := (Q.index : Nat) with hXdef
  have hD : 0 < D := Q.params.toParams.hΔ
  have hX1 : 1 ≤ X := Q.index.pos
  have hr0 : 0 ≤ r := le_max_right _ _
  have hq : Hᶜ.ncard < Q.params.toParams.fg.q := by
    have hn := Q.params.toParams.hn
    change 0 < Q.params.n at hn
    change Hᶜ.ncard < (2 * Q.params.n + 2) / 3
    omega
  have hf2 : Hᶜ.ncard < 2 * Q.params.toParams.fg.q - Q.params.n := by
    have hn := Q.params.toParams.hn
    change 0 < Q.params.n at hn
    change Hᶜ.ncard < 2 * ((2 * Q.params.n + 2) / 3) - Q.params.n
    omega
  set lo : Time := r + 4 * D with hlodef
  set ρ : Nat := δt + X - 1 with hρdef
  have hρZ : (ρ : ℤ) = (δt : ℤ) + (X : ℤ) - 1 := by omega
  set len : Time := 4 * D * ((Ld : ℤ) + 2 * ((δt : ℤ) + (X : ℤ) - 1) + 2) + 2 * D with hlendef
  set B := resetBound r D lam δt X Ld with hBdef
  have hB : lo + 6 * (len + lam) = B := by
    rw [hBdef, resetBound_eq, hlodef, hlendef]; ring
  have hlen0 : 0 ≤ len := by
    have : (0 : ℤ) ≤ (δt : ℤ) + (X : ℤ) - 1 := by omega
    rw [hlendef]; positivity
  have hbB : B ≤ b := hb
  have hhB : B + 24 * D ≤ Q.run.2.horizon := hhor
  -- the advance case: an honest signature above `H_z` up to `B` is a reset
  by_cases hadv : ∃ y ∈ H, ∃ k att, Q.trace.SignAt y k att ∧ Q.trace.time k ≤ B ∧
      HZ Q.trace H g + 1 ≤ att.h
  · obtain ⟨y, hy, k, att, hs, hkT, hh⟩ := hadv
    obtain ⟨a, ha, hak⟩ := reset_of_height_advance hrun hq hy hs hh
    exact ⟨a, ha, hak.trans hkT⟩
  have hna : ∀ v ∈ H, ∀ k att, Q.trace.SignAt v k att → Q.trace.time k < B + 1 →
      att.h ≤ HZ Q.trace H g := fun v hv k att hs hkT => by
    by_contra h
    exact hadv ⟨v, hv, k, att, hs, Int.lt_add_one_iff.mp hkT, by omega⟩
  -- the pigeonhole window
  obtain ⟨af, haf, hafl, floor, contest, kindJ, J, hwin⟩ :=
    exists_frameWindow_of_noAdvance (lo := lo) (len := len) (lam := lam) (T := B + 1)
      hrun hnc hf2 hq hsvc hcatch hH hsnap hlen0 hlam hna
      (by rw [hlodef]; unfold gbar at hgr ⊢; linarith)
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
  have hts₀lo : af ≤ Q.params.ts s₀ := by
    simp only [SA.SAParams.ts]; rw [hs₀c]; nlinarith
  have hts₀hi : 4 * D * (s₀ : ℤ) < af + 4 * D := by rw [hs₀c]; nlinarith
  set N : Nat := s₀ + Ld + 2 * ρ + 1 with hNdef
  have hpos : (0 : ℤ) ≤ ((s₀ : ℤ) + Ld) + 2 * ((δt : ℤ) + X - 1) + 1 := by omega
  -- the arithmetic of the frame (heal_bound_sufficient .1, .2.1)
  have hfitN : Q.params.ts N + 2 * D < af + len ∧ Q.params.ts N + 2 * D ≤ B - 1 := by
    have hk : (0 : ℤ) ≤ Q.params.k := by positivity
    obtain ⟨h1, -, -, -⟩ := heal_bound_sufficient (D := D) (ready := r) (lam := lam)
      (k := Q.params.k) (δt := δt) (X := X) (Ld := Ld) (s₀ := s₀) (u := s₀ + Ld)
      (a := 0) (sa := 0) (uMin := 0) (lo := lo) (af := af) (len := len)
      (heal := r + healBoundCoeff Q.params.k δt X Ld * D + 6 * lam - 2)
      (q := r + healBoundCoeff Q.params.k δt X Ld * D + 6 * lam - 2)
      hD hr0 hlam hk (by exact_mod_cast (show 1 ≤ δt by omega)) (by exact_mod_cast hX1)
      (by positivity) le_rfl hlendef hafl hts₀hi le_rfl
      (by have := mul_nonneg h4D.le hpos; linarith) (by simp) (by linarith) le_rfl le_rfl
    have hN' : Q.params.ts N = 4 * D * ((s₀ : ℤ) + Ld + 2 * ((δt : ℤ) + X - 1) + 1) := by
      simp only [SA.SAParams.ts, hNdef]; push_cast; rw [hρZ]
    refine ⟨by rw [hN']; exact h1, ?_⟩
    rw [hN']
    have := hafl
    rw [hB] at this
    linarith
  have hframe : FrameWindow (tr := Q.trace) (H := H) (Q.params.ts s₀)
      (Q.params.ts N + 2 * D) floor contest kindJ J :=
    frameWindow_sub hwin hts₀lo (by linarith [hfitN.1])
  have hts₀r : r + 4 * D ≤ Q.params.ts s₀ := by linarith
  have hm : gbar g + 4 * D ≤ Q.params.ts s₀ := by linarith
  -- the gap
  have hgp := hgp_of_query S A V Q hrun hpropose (s₀ := s₀) (N := N) hts₀r (by
    have : Q.params.ts (N + 6 : Nat) = Q.params.ts N + 24 * D := by
      simp only [SA.SAParams.ts]; push_cast; ring
    rw [this]; linarith [hfitN.2])
  -- the drain
  obtain ⟨u, hwarm, huLd, z, hz, hdes, kP, P, hP, hPs, hlow⟩ :=
    hdrain.warm hframe hm (by omega) (by linarith [hfitN.2])
      (fun v hv k att hs hk => hna v hv k att hs (by linarith [hfitN.2])) hgp
  have hN2 : u + 2 * ρ + 1 ≤ N := by rw [hNdef]; omega
  -- the rise
  obtain ⟨a, ha, hab⟩ := hframe.rise_reset hrun hnc hsvc hawake hf hcatch hnr hm hwarm hδ hΔF
    hgp hN2 (by linarith [hfitN.2]) hz hdes hP hPs hlow
  refine ⟨a, ha, hab.trans ?_⟩
  have hts : Q.params.ts (u + 2 * (δt + X - 1) + 1 : Nat) ≤ Q.params.ts N :=
    (SA.ts_le_iff Q.params).2 (by exact_mod_cast (show _ ≤ N by omega))
  linarith [hfitN.2]

end Consensus.Goldilocks.Refinement
