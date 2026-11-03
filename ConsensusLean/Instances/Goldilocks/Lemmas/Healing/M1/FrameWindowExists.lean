module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLag
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance

public section

/-! # M1′ B2/B3: at most 5 global frame changes, and the pigeonhole to a `FrameWindow`

pre_advance_finality §23.2 (O2) and §6 (window). Two layers:

* `exists_const_window` is pure counting. A per-node monotone key in `[base, base + 5]`
  (6 values, so at most 5 global rises) with lag `Δ` (a value held by one node at `t` is held by
  every node at a cut strictly before `t + Δ`) is constant over all nodes on one of 6 disjoint
  windows of length `len` inside `[lo, lo + 6(len + Δ)]`.
* `exists_frameWindow` applies it to `frameKey` (MONO) and builds a
  `FrameWindow` from the constant key (`frameKey_eq_*`).

The range (F1 and the lower bound `h_max ≥ HZ` after `cutZ + Δ`) and the lag (L-H/L-J/L-C) are
hypotheses here. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- **Pigeonhole (O2, counting).** A monotone key with 6 values and lag `Δ` is constant on
one of 6 disjoint windows. -/
theorem exists_const_window {α : Type*} (H : Set α) (time : Nat → Time)
    (key : α → Nat → Nat) (base : Nat) {lo len Δ T : Time} (hlen : 0 ≤ len) (hΔ : 0 ≤ Δ)
    (hrange : ∀ y ∈ H, ∀ i, lo ≤ time i → time i < T → base ≤ key y i ∧ key y i ≤ base + 5)
    (hlag : ∀ x ∈ H, ∀ z ∈ H, ∀ i m, lo ≤ time i → time i < T → time i + Δ ≤ time m →
      time m < T → key x i ≤ key z m)
    (hT : lo + 6 * (len + Δ) < T) :
    ∃ a, lo + Δ ≤ a ∧ a + len ≤ lo + 6 * (len + Δ) ∧
      ∀ y ∈ H, ∀ z ∈ H, ∀ i m, a ≤ time i → time i ≤ a + len → a ≤ time m →
        time m ≤ a + len → key y i = key z m := by
  classical
  -- `E v t`: some node holds a key `≥ base + v + 1` at a cut in `[lo, t]` before `T`
  let E : Nat → Time → Prop := fun v t =>
    ∃ x ∈ H, ∃ i, lo ≤ time i ∧ time i ≤ t ∧ time i < T ∧ base + (v + 1) ≤ key x i
  let D : Time := len + Δ
  have hD : 0 ≤ D := by positivity
  let bad : Nat → Nat → Prop := fun v k => E v (lo + (k + 1) * D) ∧ ¬E v (lo + k * D)
  have huniq : ∀ v k k', bad v k → bad v k' → k = k' := by
    intro v k k' hk hk'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨x, hx, i, h1, h2, h3, h4⟩ := hk.1
      refine hk'.2 ⟨x, hx, i, h1, h2.trans ?_, h3, h4⟩
      have : ((k : Time) + 1) ≤ k' := by exact_mod_cast hlt
      nlinarith
    · obtain ⟨x, hx, i, h1, h2, h3, h4⟩ := hk'.1
      refine hk.2 ⟨x, hx, i, h1, h2.trans ?_, h3, h4⟩
      have : ((k' : Time) + 1) ≤ k := by exact_mod_cast hlt
      nlinarith
  have hgood : ∃ k : Fin 6, ∀ v < 5, ¬bad v k := by
    by_contra hall
    push Not at hall
    choose f hf using hall
    have hinj : Function.Injective fun k : Fin 6 => (⟨f k, (hf k).1⟩ : Fin 5) := by
      intro k k' he
      exact Fin.ext (huniq _ _ _ (hf k).2 ((Fin.mk.inj_iff.1 he) ▸ (hf k').2))
    have := Fintype.card_le_of_injective _ hinj
    simp at this
  obtain ⟨k, hk⟩ := hgood
  have hk6 : (k : Time) + 1 ≤ 6 := by exact_mod_cast k.isLt
  have hk0 : (0 : Time) ≤ k := by positivity
  refine ⟨lo + k * D + Δ, by nlinarith, by nlinarith, ?_⟩
  have hle : ∀ y ∈ H, ∀ z ∈ H, ∀ i m, lo + k * D + Δ ≤ time i →
      time i ≤ lo + k * D + Δ + len → lo + k * D + Δ ≤ time m →
      time m ≤ lo + k * D + Δ + len → key y i ≤ key z m := by
    intro y hy z hz i m hi1 hi2 hm1 hm2
    have hloi : lo ≤ time i := by nlinarith
    have hTi : time i < T := by nlinarith
    have hlom : lo ≤ time m := by nlinarith
    obtain ⟨hb, hu⟩ := hrange y hy i hloi hTi
    by_contra hlt
    push Not at hlt
    have hTm : time m < T := by nlinarith
    have hbz := (hrange z hz m hlom hTm).1
    have hv : key y i - base - 1 < 5 := by omega
    have hE : E (key y i - base - 1) (lo + (k + 1) * D) :=
      ⟨y, hy, i, hloi, by nlinarith, hTi, by omega⟩
    have hE0 : E (key y i - base - 1) (lo + k * D) := by
      by_contra hn
      exact hk _ hv ⟨hE, hn⟩
    obtain ⟨x, hx, i', hlo', hti', hT', hkey'⟩ := hE0
    have := hlag x hx z hz i' m hlo' hT' (by nlinarith) hTm
    omega
  intro y hy z hz i m hi1 hi2 hm1 hm2
  have hm2' : time m ≤ lo + k * D + Δ + len := hm2
  exact le_antisymm (hle y hy z hz i m hi1 hi2 hm1 hm2')
    (hle z hz y hy m i hm1 hm2' hi1 hi2)

/-- **Pigeonhole (O2, counting).** A monotone key with 5 values and lag `Δ` is constant on
one of 5 disjoint windows. -/
theorem exists_const_window5 {α : Type*} (H : Set α) (time : Nat → Time)
    (key : α → Nat → Nat) (base : Nat) {lo len Δ T : Time} (hlen : 0 ≤ len) (hΔ : 0 ≤ Δ)
    (hrange : ∀ y ∈ H, ∀ i, lo ≤ time i → time i < T → base ≤ key y i ∧ key y i ≤ base + 4)
    (hlag : ∀ x ∈ H, ∀ z ∈ H, ∀ i m, lo ≤ time i → time i < T → time i + Δ ≤ time m →
      time m < T → key x i ≤ key z m)
    (hT : lo + 5 * (len + Δ) < T) :
    ∃ a, lo + Δ ≤ a ∧ a + len ≤ lo + 5 * (len + Δ) ∧
      ∀ y ∈ H, ∀ z ∈ H, ∀ i m, a ≤ time i → time i ≤ a + len → a ≤ time m →
        time m ≤ a + len → key y i = key z m := by
  classical
  -- `E v t`: some node holds a key `≥ base + v + 1` at a cut in `[lo, t]` before `T`
  let E : Nat → Time → Prop := fun v t =>
    ∃ x ∈ H, ∃ i, lo ≤ time i ∧ time i ≤ t ∧ time i < T ∧ base + (v + 1) ≤ key x i
  let D : Time := len + Δ
  have hD : 0 ≤ D := by positivity
  let bad : Nat → Nat → Prop := fun v k => E v (lo + (k + 1) * D) ∧ ¬E v (lo + k * D)
  have huniq : ∀ v k k', bad v k → bad v k' → k = k' := by
    intro v k k' hk hk'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨x, hx, i, h1, h2, h3, h4⟩ := hk.1
      refine hk'.2 ⟨x, hx, i, h1, h2.trans ?_, h3, h4⟩
      have : ((k : Time) + 1) ≤ k' := by exact_mod_cast hlt
      nlinarith
    · obtain ⟨x, hx, i, h1, h2, h3, h4⟩ := hk'.1
      refine hk.2 ⟨x, hx, i, h1, h2.trans ?_, h3, h4⟩
      have : ((k' : Time) + 1) ≤ k := by exact_mod_cast hlt
      nlinarith
  have hgood : ∃ k : Fin 5, ∀ v < 4, ¬bad v k := by
    by_contra hall
    push Not at hall
    choose f hf using hall
    have hinj : Function.Injective fun k : Fin 5 => (⟨f k, (hf k).1⟩ : Fin 4) := by
      intro k k' he
      exact Fin.ext (huniq _ _ _ (hf k).2 ((Fin.mk.inj_iff.1 he) ▸ (hf k').2))
    have := Fintype.card_le_of_injective _ hinj
    simp at this
  obtain ⟨k, hk⟩ := hgood
  have hk6 : (k : Time) + 1 ≤ 5 := by exact_mod_cast k.isLt
  have hk0 : (0 : Time) ≤ k := by positivity
  refine ⟨lo + k * D + Δ, by nlinarith, by nlinarith, ?_⟩
  have hle : ∀ y ∈ H, ∀ z ∈ H, ∀ i m, lo + k * D + Δ ≤ time i →
      time i ≤ lo + k * D + Δ + len → lo + k * D + Δ ≤ time m →
      time m ≤ lo + k * D + Δ + len → key y i ≤ key z m := by
    intro y hy z hz i m hi1 hi2 hm1 hm2
    have hloi : lo ≤ time i := by nlinarith
    have hTi : time i < T := by nlinarith
    have hlom : lo ≤ time m := by nlinarith
    obtain ⟨hb, hu⟩ := hrange y hy i hloi hTi
    by_contra hlt
    push Not at hlt
    have hTm : time m < T := by nlinarith
    have hbz := (hrange z hz m hlom hTm).1
    have hv : key y i - base - 1 < 4 := by omega
    have hE : E (key y i - base - 1) (lo + (k + 1) * D) :=
      ⟨y, hy, i, hloi, by nlinarith, hTi, by omega⟩
    have hE0 : E (key y i - base - 1) (lo + k * D) := by
      by_contra hn
      exact hk _ hv ⟨hE, hn⟩
    obtain ⟨x, hx, i', hlo', hti', hT', hkey'⟩ := hE0
    have := hlag x hx z hz i' m hlo' hT' (by nlinarith) hTm
    omega
  intro y hy z hz i m hi1 hi2 hm1 hm2
  have hm2' : time m ≤ lo + k * D + Δ + len := hm2
  exact le_antisymm (hle y hy z hz i m hi1 hi2 hm1 hm2')
    (hle z hz y hy m i hm1 hm2' hi1 hi2)

/-- **Sequential pigeonhole (generic).** A key in `[base, base + m]` with lag `Δ` and a window
length `len v` per key value `v`. Attempt `j` starts at `lo + S j`, with
`S j = ∑_{i<j} (len (base + i) + Δ)`, and tests the window `[lo + S j + Δ, lo + S (j + 1)]` for
the value `base + j`. If the test fails, some node holds a key above `base + j` in that window,
so after the lag every node does. Thus one of the `m + 1` attempts succeeds: some value `v`
holds at every honest cut of a window of length `len v` that ends by `lo + S (v - base + 1)`. -/
theorem exists_const_window_seq {α : Type*} (H : Set α) (time : Nat → Time)
    (key : α → Nat → Nat) (base m : Nat) (len : Nat → Time) {lo Δ T : Time}
    (hlen : ∀ v, 0 ≤ len v) (hΔ : 0 ≤ Δ)
    (hrange : ∀ y ∈ H, ∀ i, lo ≤ time i → time i < T → base ≤ key y i ∧ key y i ≤ base + m)
    (hlag : ∀ x ∈ H, ∀ z ∈ H, ∀ i k, lo ≤ time i → time i < T → time i + Δ ≤ time k →
      time k < T → key x i ≤ key z k)
    (hT : lo + ∑ j ∈ Finset.range (m + 1), (len (base + j) + Δ) < T) :
    ∃ v, base ≤ v ∧ v ≤ base + m ∧ ∃ a, lo + Δ ≤ a ∧
      a + len v ≤ lo + ∑ j ∈ Finset.range (v - base + 1), (len (base + j) + Δ) ∧
      ∀ y ∈ H, ∀ i, a ≤ time i → time i ≤ a + len v → key y i = v := by
  classical
  obtain ⟨S, hSdef⟩ : ∃ S : Nat → Time,
      ∀ j, S j = ∑ i ∈ Finset.range j, (len (base + i) + Δ) := ⟨_, fun _ => rfl⟩
  have hS0 : ∀ j, 0 ≤ S j := fun j => by
    rw [hSdef]
    exact Finset.sum_nonneg fun i _ => add_nonneg (hlen _) hΔ
  have hSmono : ∀ j k, j ≤ k → S j ≤ S k := fun j k hjk => by
    rw [hSdef, hSdef]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjk)
      fun i _ _ => add_nonneg (hlen _) hΔ
  have hSsucc : ∀ j, S (j + 1) = S j + (len (base + j) + Δ) := fun j => by
    rw [hSdef, hSdef, Finset.sum_range_succ]
  rw [← hSdef] at hT
  by_contra hno
  -- a failed attempt `j` leaves a key above `base + j` in its window
  have step : ∀ j ≤ m,
      (∀ z ∈ H, ∀ k, lo + S j + Δ ≤ time k → time k < T → base + j ≤ key z k) →
      ∃ y ∈ H, ∃ i, lo + S j + Δ ≤ time i ∧ time i ≤ lo + S (j + 1) ∧ time i < T ∧
        base + j + 1 ≤ key y i := by
    intro j hj hinvj
    have hTj : lo + S (j + 1) < T := by
      have := hSmono (j + 1) (m + 1) (by omega)
      linarith
    by_contra hall
    push Not at hall
    apply hno
    refine ⟨base + j, by omega, by omega, lo + S j + Δ, by linarith [hS0 j], ?_, ?_⟩
    · rw [show base + j - base + 1 = j + 1 by omega, ← hSdef, hSsucc]
      linarith
    · intro y hy i hi1 hi2
      have hiT : time i < T := by linarith [hSsucc j]
      have h1 := hinvj y hy i hi1 hiT
      have h2 := hall y hy i hi1 (by linarith [hSsucc j]) hiT
      omega
  have hinv : ∀ j, j ≤ m →
      ∀ z ∈ H, ∀ k, lo + S j + Δ ≤ time k → time k < T → base + j ≤ key z k := by
    intro j
    induction j with
    | zero =>
      intro _ z hz k hk hkT
      have := (hrange z hz k (by linarith [hS0 0]) hkT).1
      omega
    | succ j ih =>
      intro hj z hz k hk hkT
      obtain ⟨y, hy, i, hi1, hi2, hiT, hkey⟩ := step j (by omega) (ih (by omega))
      have := hlag y hy z hz i k (by linarith [hS0 j]) hiT (by linarith) hkT
      omega
  obtain ⟨y, hy, i, hi1, -, hiT, hkey⟩ := step m le_rfl (hinv m le_rfl)
  have := (hrange y hy i (by linarith [hS0 m]) hiT).2
  omega

/-- `exists_const_window_seq` with a constant length: some value `v` holds on a window of
length `len` that ends by `lo + (v - base + 1)(len + Δ)`. For `m = 4` this gives the
conclusion of `exists_const_window5`, with the key value. -/
theorem exists_const_window_seq_const {α : Type*} (H : Set α) (time : Nat → Time)
    (key : α → Nat → Nat) (base m : Nat) {lo len Δ T : Time} (hlen : 0 ≤ len) (hΔ : 0 ≤ Δ)
    (hrange : ∀ y ∈ H, ∀ i, lo ≤ time i → time i < T → base ≤ key y i ∧ key y i ≤ base + m)
    (hlag : ∀ x ∈ H, ∀ z ∈ H, ∀ i k, lo ≤ time i → time i < T → time i + Δ ≤ time k →
      time k < T → key x i ≤ key z k)
    (hT : lo + (m + 1) * (len + Δ) < T) :
    ∃ v, base ≤ v ∧ v ≤ base + m ∧ ∃ a, lo + Δ ≤ a ∧
      a + len ≤ lo + ((v - base : Nat) + 1) * (len + Δ) ∧
      a + len ≤ lo + (m + 1) * (len + Δ) ∧
      ∀ y ∈ H, ∀ i, a ≤ time i → time i ≤ a + len → key y i = v := by
  have hsum : ∀ n, ∑ _j ∈ Finset.range n, (len + Δ) = (n : Time) * (len + Δ) := fun n => by
    simp
  obtain ⟨v, hv1, hv2, a, ha1, ha2, hK⟩ := exists_const_window_seq H time key base m
    (fun _ => len) (fun _ => hlen) hΔ hrange hlag (by rw [hsum]; push_cast; exact hT)
  rw [hsum] at ha2
  push_cast at ha2
  have hc : ((v - base : Nat) : Time) ≤ m := by exact_mod_cast (by omega : v - base ≤ m)
  refine ⟨v, hv1, hv2, a, ha1, ha2, ?_, hK⟩
  nlinarith

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A frame key that is constant over the honest cuts of `[lo, hi]` gives a `FrameWindow`. -/
theorem frameWindow_of_frameKey_eq (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {lo hi : Time}
    (hK : ∀ y ∈ H, ∀ z ∈ H, ∀ i m, lo ≤ tr.time i → tr.time i ≤ hi → lo ≤ tr.time m →
      tr.time m ≤ hi → frameKey (tr.state y i).fg = frameKey (tr.state z m).fg) :
    ∃ floor kindJ J, FrameWindow (tr := tr) (H := H) lo hi floor kindJ J := by
  classical
  by_cases hex : ∃ y ∈ H, ∃ i, lo ≤ tr.time i ∧ tr.time i ≤ hi
  · obtain ⟨y₀, hy₀, i₀, h₁, h₂⟩ := hex
    let st := (tr.state y₀ i₀).fg
    refine ⟨st.headHeightFloor, st.hmax = st.hj + 1 ∧ ¬st.Contest, st.J, ⟨?_, ?_, ?_⟩⟩
    · intro y hy i hlo hhi
      exact frameKey_eq_floor (hK y hy y₀ hy₀ i i₀ hlo hhi h₁ h₂)
    · intro y hy i hlo hhi
      exact frameKey_eq_kind (hK y hy y₀ hy₀ i i₀ hlo hhi h₁ h₂)
    · intro y hy i hlo hhi hk
      have he := hK y hy y₀ hy₀ i i₀ hlo hhi h₁ h₂
      exact frameKey_eq_J hrun hnc hf hy hy₀ he ((frameKey_eq_kind he).2 hk).1
  · push Not at hex
    refine ⟨0, True, sp.toParams.genesisBlock ([], []), ⟨?_, ?_, ?_⟩⟩ <;>
      intro y hy i hlo hhi <;> exact absurd hhi (not_le.2 (hex y hy i hlo))

/-- **O2 + pigeonhole → ∃ FrameWindow (B2/B3).** Premises: per-node range `HZ ≤ h_max ≤ HZ + 1`
on `[lo, T)` (F1 and the post-`cutZ + Δ` lower bound) and the key lag `Δ` (L-H/L-J/L-C).
Then some window `[a, a + len]` with `lo + Δ ≤ a` and `a + len ≤ lo + 6(len + Δ)` is a
`FrameWindow`. -/
theorem exists_frameWindow (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {lo len Δ T : Time} {HZ : Nat} (hlen : 0 ≤ len) (hΔ : 0 ≤ Δ)
    (hrange : ∀ y ∈ H, ∀ i, lo ≤ tr.time i → tr.time i < T →
      HZ ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ HZ + 1)
    (hlag : ∀ x ∈ H, ∀ z ∈ H, ∀ i m, lo ≤ tr.time i → tr.time i < T →
      tr.time i + Δ ≤ tr.time m → tr.time m < T →
        frameKey (tr.state x i).fg ≤ frameKey (tr.state z m).fg)
    (hT : lo + 6 * (len + Δ) < T) :
    ∃ a, lo + Δ ≤ a ∧ a + len ≤ lo + 6 * (len + Δ) ∧
      ∃ floor kindJ J,
        FrameWindow (tr := tr) (H := H) a (a + len) floor kindJ J := by
  obtain ⟨a, h1, h2, hK⟩ := exists_const_window H tr.time
    (fun y i => frameKey (tr.state y i).fg) (3 * HZ) hlen hΔ
    (fun y hy i h1 h2 => by
      have := hrange y hy i h1 h2
      have := frameKey_bounds (tr.state y i).fg
      omega)
    hlag hT
  exact ⟨a, h1, h2, frameWindow_of_frameKey_eq hrun hnc hf hK⟩

/-- **B2 + B3 from the service (§23.2).** `exists_frameWindow` with the lag discharged by
`frameKey_lag`. The remaining premises: the range (F1 and the lower bound), a call of every
honest node in `[deadline, m)` for each cut `m` at least `λ` after the source cut (awake nodes
with no restart after `ḡ` have one), and `ḡ + κ ≤ lo` for the catch-up route. -/
theorem exists_frameWindow_of_service (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {g ΔF b κ : Time} (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {lo len lam T : Time} {HZ : Nat} (hlen : 0 ≤ len) (hlam : 0 ≤ lam)
    (hlo : gbar g + κ ≤ lo)
    (hrange : ∀ y ∈ H, ∀ i, lo ≤ tr.time i → tr.time i < T →
      HZ ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ HZ + 1)
    (hcall : ∀ z ∈ H, ∀ i m, lo ≤ tr.time i → tr.time i + lam ≤ tr.time m → tr.time m < T →
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hT : lo + 6 * (len + lam) < T) :
    ∃ a, lo + lam ≤ a ∧ a + len ≤ lo + 6 * (len + lam) ∧
      ∃ floor kindJ J,
        FrameWindow (tr := tr) (H := H) a (a + len) floor kindJ J :=
  exists_frameWindow hrun hnc hf hlen hlam hrange
    (fun x hx z hz i m hi _ him hmT => frameKey_lag hrun hnc hf hsvc hcatch hx hz
      (hcall z hz i m hi him hmT) (by linarith)) hT

/-- A merged key that is constant over the honest cuts of `[lo, hi]` gives a `FrameWindow`. -/
theorem frameWindow_of_frameKey'_eq (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {lo hi : Time}
    (hK : ∀ y ∈ H, ∀ z ∈ H, ∀ i m, lo ≤ tr.time i → tr.time i ≤ hi → lo ≤ tr.time m →
      tr.time m ≤ hi → frameKey' (tr.state y i).fg = frameKey' (tr.state z m).fg) :
    ∃ floor kindJ J, FrameWindow (tr := tr) (H := H) lo hi floor kindJ J := by
  classical
  have hpos : ∀ y ∈ H, ∀ i, 1 ≤ (tr.state y i).fg.hmax := fun y hy i => by
    have := hj_lt_hmax hrun hy i
    omega
  by_cases hex : ∃ y ∈ H, ∃ i, lo ≤ tr.time i ∧ tr.time i ≤ hi
  · obtain ⟨y₀, hy₀, i₀, h₁, h₂⟩ := hex
    let st := (tr.state y₀ i₀).fg
    refine ⟨st.headHeightFloor, st.hmax = st.hj + 1 ∧ ¬st.Contest, st.J, ⟨?_, ?_, ?_⟩⟩
    · intro y hy i hlo hhi
      exact (frameKey'_eq_floor_kind (hpos y hy i) (hpos y₀ hy₀ i₀)
        (hK y hy y₀ hy₀ i i₀ hlo hhi h₁ h₂)).1
    · intro y hy i hlo hhi
      exact (frameKey'_eq_floor_kind (hpos y hy i) (hpos y₀ hy₀ i₀)
        (hK y hy y₀ hy₀ i i₀ hlo hhi h₁ h₂)).2
    · intro y hy i hlo hhi hk
      have he := hK y hy y₀ hy₀ i i₀ hlo hhi h₁ h₂
      exact frameKey'_eq_J hrun hnc hf hy hy₀ he
        ((frameKey'_eq_floor_kind (hpos y hy i) (hpos y₀ hy₀ i₀) he).2.2 hk)
  · push Not at hex
    refine ⟨0, True, sp.toParams.genesisBlock ([], []), ⟨?_, ?_, ?_⟩⟩ <;>
      intro y hy i hlo hhi <;> exact absurd hhi (not_le.2 (hex y hy i hlo))

/-- **O2′ + 5-window pigeonhole → ∃ FrameWindow.** `exists_frameWindow` on the merged key
`frameKey'` (5 values on `HZ ≤ h_max ≤ HZ + 1`): the window is `a + len ≤ lo + 5(len + Δ)`. -/
theorem exists_frameWindow5 (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {lo len Δ T : Time} {HZ : Nat} (hlen : 0 ≤ len) (hΔ : 0 ≤ Δ)
    (hrange : ∀ y ∈ H, ∀ i, lo ≤ tr.time i → tr.time i < T →
      HZ ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ HZ + 1)
    (hlag : ∀ x ∈ H, ∀ z ∈ H, ∀ i m, lo ≤ tr.time i → tr.time i < T →
      tr.time i + Δ ≤ tr.time m → tr.time m < T →
        frameKey' (tr.state x i).fg ≤ frameKey' (tr.state z m).fg)
    (hT : lo + 5 * (len + Δ) < T) :
    ∃ a, lo + Δ ≤ a ∧ a + len ≤ lo + 5 * (len + Δ) ∧
      ∃ floor kindJ J, FrameWindow (tr := tr) (H := H) a (a + len) floor kindJ J := by
  obtain ⟨a, h1, h2, hK⟩ := exists_const_window5 H tr.time
    (fun y i => frameKey' (tr.state y i).fg) (2 * HZ) hlen hΔ
    (fun y hy i h1 h2 => by
      have := hrange y hy i h1 h2
      exact frameKey'_bounds this.1 this.2)
    hlag hT
  exact ⟨a, h1, h2, frameWindow_of_frameKey'_eq hrun hnc hf hK⟩

/-- `exists_frameWindow5` with the lag discharged by `frameKey'_lag`. -/
theorem exists_frameWindow5_of_service (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {g ΔF b κ : Time} (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {lo len lam T : Time} {HZ : Nat} (hlen : 0 ≤ len) (hlam : 0 ≤ lam)
    (hlo : gbar g + κ ≤ lo)
    (hrange : ∀ y ∈ H, ∀ i, lo ≤ tr.time i → tr.time i < T →
      HZ ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ HZ + 1)
    (hcall : ∀ z ∈ H, ∀ i m, lo ≤ tr.time i → tr.time i + lam ≤ tr.time m → tr.time m < T →
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hT : lo + 5 * (len + lam) < T) :
    ∃ a, lo + lam ≤ a ∧ a + len ≤ lo + 5 * (len + lam) ∧
      ∃ floor kindJ J, FrameWindow (tr := tr) (H := H) a (a + len) floor kindJ J :=
  exists_frameWindow5 hrun hnc hf hlen hlam hrange
    (fun x hx z hz i m hi _ him hmT => frameKey'_lag hrun hnc hf hsvc hcatch hx hz
      (hcall z hz i m hi him hmT) (by linarith)) hT

/-- **Sequential pigeonhole → ∃ FrameWindow.** `exists_const_window_seq` on the merged key
`frameKey'` (5 values `2HZ, …, 2HZ + 4` on `HZ ≤ h_max ≤ HZ + 1`), with a window length
`len v` per key value. It returns the key value `v` of the window, the window `[a, a + len v]`
with `a + len v ≤ lo + ∑_{j ≤ v - 2HZ} (len (2HZ + j) + Δ)`, and a `FrameWindow` on it. -/
theorem exists_frameWindow_seq (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {lo Δ T : Time} {HZ : Nat} (len : Nat → Time) (hlen : ∀ v, 0 ≤ len v) (hΔ : 0 ≤ Δ)
    (hrange : ∀ y ∈ H, ∀ i, lo ≤ tr.time i → tr.time i < T →
      HZ ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ HZ + 1)
    (hlag : ∀ x ∈ H, ∀ z ∈ H, ∀ i m, lo ≤ tr.time i → tr.time i < T →
      tr.time i + Δ ≤ tr.time m → tr.time m < T →
        frameKey' (tr.state x i).fg ≤ frameKey' (tr.state z m).fg)
    (hT : lo + ∑ j ∈ Finset.range 5, (len (2 * HZ + j) + Δ) < T) :
    ∃ v, 2 * HZ ≤ v ∧ v ≤ 2 * HZ + 4 ∧ ∃ a, lo + Δ ≤ a ∧
      a + len v ≤ lo + ∑ j ∈ Finset.range (v - 2 * HZ + 1), (len (2 * HZ + j) + Δ) ∧
      (∀ y ∈ H, ∀ i, a ≤ tr.time i → tr.time i ≤ a + len v →
        frameKey' (tr.state y i).fg = v) ∧
      ∃ floor kindJ J, FrameWindow (tr := tr) (H := H) a (a + len v) floor kindJ J := by
  obtain ⟨v, hv1, hv2, a, h1, h2, hK⟩ := exists_const_window_seq H tr.time
    (fun y i => frameKey' (tr.state y i).fg) (2 * HZ) 4 len hlen hΔ
    (fun y hy i h1 h2 => by
      have := hrange y hy i h1 h2
      exact frameKey'_bounds this.1 this.2)
    hlag hT
  refine ⟨v, hv1, hv2, a, h1, h2, hK, frameWindow_of_frameKey'_eq hrun hnc hf ?_⟩
  intro y hy z hz i m hi1 hi2 hm1 hm2
  rw [hK y hy i hi1 hi2, hK z hz m hm1 hm2]

/-- `exists_frameWindow_seq` with the lag discharged by `frameKey'_lag`. -/
theorem exists_frameWindow_seq_of_service (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {g ΔF b κ : Time} (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {lo lam T : Time} {HZ : Nat} (len : Nat → Time) (hlen : ∀ v, 0 ≤ len v) (hlam : 0 ≤ lam)
    (hlo : gbar g + κ ≤ lo)
    (hrange : ∀ y ∈ H, ∀ i, lo ≤ tr.time i → tr.time i < T →
      HZ ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ HZ + 1)
    (hcall : ∀ z ∈ H, ∀ i m, lo ≤ tr.time i → tr.time i + lam ≤ tr.time m → tr.time m < T →
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hT : lo + ∑ j ∈ Finset.range 5, (len (2 * HZ + j) + lam) < T) :
    ∃ v, 2 * HZ ≤ v ∧ v ≤ 2 * HZ + 4 ∧ ∃ a, lo + lam ≤ a ∧
      a + len v ≤ lo + ∑ j ∈ Finset.range (v - 2 * HZ + 1), (len (2 * HZ + j) + lam) ∧
      (∀ y ∈ H, ∀ i, a ≤ tr.time i → tr.time i ≤ a + len v →
        frameKey' (tr.state y i).fg = v) ∧
      ∃ floor kindJ J, FrameWindow (tr := tr) (H := H) a (a + len v) floor kindJ J :=
  exists_frameWindow_seq hrun hnc hf len hlen hlam hrange
    (fun x hx z hz i m hi _ him hmT => frameKey'_lag hrun hnc hf hsvc hcatch hx hz
      (hcall z hz i m hi him hmT) (by linarith)) hT

end Consensus.Goldilocks.Healing

end
