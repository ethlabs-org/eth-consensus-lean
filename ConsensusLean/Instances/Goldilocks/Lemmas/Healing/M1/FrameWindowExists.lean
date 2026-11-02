module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameKey
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance

public section

/-! # M1′ B2/B3: at most 5 global frame changes, and the pigeonhole to a `FrameWindow`

pre_advance_finality §23.2 (O2) and §6 (window). Two layers:

* `exists_const_window` is pure counting. A per-node monotone key in `[base, base + 5]`
  (6 values, so at most 5 global rises) with lag `Δ` (a value held by one node at `t` is held by
  every node at a cut strictly before `t + Δ`) is constant over all nodes on one of 6 disjoint
  windows of length `len` inside `[lo, lo + 6(len + Δ)]`.
* `exists_frameWindow` applies it to `frameKey` (MONO, `frameKey_mono`) and builds a
  `FrameWindow` from the constant key (`frameKey_eq_*`).

The range (F1 and the lower bound `h_max ≥ HZ` after `cutZ + Δ`) and the lag (L-H/L-J/L-C) are
hypotheses here. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

/-- **Pigeonhole (O2, counting).** A monotone key with 6 values and lag `Δ` is constant on
one of 6 disjoint windows. -/
theorem exists_const_window {α : Type*} (H : Set α) (time : Nat → Time) (htime : Monotone time)
    (key : α → Nat → Nat) (base : Nat) {lo len Δ T : Time} (hlen : 0 ≤ len) (hΔ : 0 ≤ Δ)
    (hmono : ∀ y ∈ H, Monotone (key y))
    (hrange : ∀ y ∈ H, ∀ i, lo ≤ time i → time i < T → base ≤ key y i ∧ key y i ≤ base + 5)
    (hlag : ∀ x ∈ H, ∀ z ∈ H, ∀ i, lo ≤ time i → time i < T →
      ∃ j, time j < time i + Δ ∧ key x i ≤ key z j)
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
    obtain ⟨j, hj, hkj⟩ := hlag x hx z hz i' hlo' hT'
    have hjm : j ≤ m := by
      by_contra hn
      have := htime (Nat.le_of_not_le hn)
      linarith
    have := hmono z hz hjm
    omega
  intro y hy z hz i m hi1 hi2 hm1 hm2
  have hm2' : time m ≤ lo + k * D + Δ + len := hm2
  exact le_antisymm (hle y hy z hz i m hi1 hi2 hm1 hm2')
    (hle z hz y hy m i hm1 hm2' hi1 hi2)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A frame key that is constant over the honest cuts of `[lo, hi]` gives a `FrameWindow`. -/
theorem frameWindow_of_frameKey_eq (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {lo hi : Time}
    (hK : ∀ y ∈ H, ∀ z ∈ H, ∀ i m, lo ≤ tr.time i → tr.time i ≤ hi → lo ≤ tr.time m →
      tr.time m ≤ hi → frameKey (tr.state y i).fg = frameKey (tr.state z m).fg) :
    ∃ floor contest kindJ J, FrameWindow (tr := tr) (H := H) lo hi floor contest kindJ J := by
  classical
  by_cases hex : ∃ y ∈ H, ∃ i, lo ≤ tr.time i ∧ tr.time i ≤ hi
  · obtain ⟨y₀, hy₀, i₀, h₁, h₂⟩ := hex
    let st := (tr.state y₀ i₀).fg
    refine ⟨st.headHeightFloor, st.Contest, st.hmax = st.hj + 1 ∧ ¬st.Contest, st.J,
      ⟨?_, ?_, ?_, ?_⟩⟩
    · intro y hy i hlo hhi
      exact frameKey_eq_floor (hK y hy y₀ hy₀ i i₀ hlo hhi h₁ h₂)
    · intro y hy i hlo hhi
      exact frameKey_eq_contest (hK y hy y₀ hy₀ i i₀ hlo hhi h₁ h₂)
    · intro y hy i hlo hhi
      exact frameKey_eq_kind (hK y hy y₀ hy₀ i i₀ hlo hhi h₁ h₂)
    · intro y hy i hlo hhi hk
      have he := hK y hy y₀ hy₀ i i₀ hlo hhi h₁ h₂
      exact frameKey_eq_J hrun hnc hf hy hy₀ he ((frameKey_eq_kind he).2 hk).1
  · push Not at hex
    refine ⟨0, True, True, sp.toParams.genesisBlock ([], []), ⟨?_, ?_, ?_, ?_⟩⟩ <;>
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
    (hlag : ∀ x ∈ H, ∀ z ∈ H, ∀ i, lo ≤ tr.time i → tr.time i < T →
      ∃ j, tr.time j < tr.time i + Δ ∧
        frameKey (tr.state x i).fg ≤ frameKey (tr.state z j).fg)
    (hT : lo + 6 * (len + Δ) < T) :
    ∃ a, lo + Δ ≤ a ∧ a + len ≤ lo + 6 * (len + Δ) ∧
      ∃ floor contest kindJ J,
        FrameWindow (tr := tr) (H := H) a (a + len) floor contest kindJ J := by
  obtain ⟨a, h1, h2, hK⟩ := exists_const_window H tr.time (fun _ _ h => hrun.time_mono h)
    (fun y i => frameKey (tr.state y i).fg) (3 * HZ) hlen hΔ
    (fun y hy _ _ h => frameKey_mono hrun hnc hf hy h)
    (fun y hy i h1 h2 => by
      have := hrange y hy i h1 h2
      have := frameKey_bounds (tr.state y i).fg
      omega)
    hlag hT
  exact ⟨a, h1, h2, frameWindow_of_frameKey_eq hrun hnc hf hK⟩

end Consensus.Goldilocks.Healing

end
