module
public import ConsensusProblem.Properties

@[expose] public section

/-! # Prefixes of traces (L0 facts)

Lemmas about `Trace.PrefixOf`: a prefix up to `b` has the same environment,
cuts, end-of-time reads up to `b`, and its ready-reader safety and resilience
are those of the full trace up to `b`. -/

namespace Consensus

namespace Trace

variable {V α Id : Type}

namespace PrefixOf

variable {tr' tr : Trace V α Id} {b : Time}

/-- The prefix has the same environment. -/
theorem env (h : tr'.PrefixOf tr b) : tr'.point.env = tr.point.env := by
  rw [h.point]

/-- A cut of the full trace at a time `≤ b` is a cut of the prefix. -/
theorem le_cuts (h : tr'.PrefixOf tr b) {i : Nat} (hi : i ≤ tr.cuts) (hb : tr.cutTime i ≤ b) :
    i ≤ tr'.cuts := by
  rw [h.cuts]; exact Nat.le_findGreatest hi hb

/-- Ends of times `≤ b` agree. -/
theorem endCut_eq (h : tr'.PrefixOf tr b) {t : Time} (ht : t ≤ b) :
    tr'.endCut t = tr.endCut t := by
  have hle : tr'.cuts ≤ tr.cuts := by rw [h.cuts]; exact Nat.findGreatest_le _
  have hk := (Nat.findGreatest_eq_iff (P := fun i => tr.cutTime i ≤ t)).mp
    (rfl : tr.endCut t = tr.endCut t)
  have hkb : tr'.cuts = Nat.findGreatest (fun i => tr.cutTime i ≤ b) tr.cuts := h.cuts
  change Nat.findGreatest (fun i => tr'.cutTime i ≤ t) tr'.cuts = tr.endCut t
  rw [Nat.findGreatest_eq_iff]
  obtain ⟨hk1, hk2, hk3⟩ := hk
  have hkc : tr.endCut t ≤ tr'.cuts := by
    by_cases h0 : tr.endCut t = 0
    · rw [h0]; exact Nat.zero_le _
    · rw [hkb]; exact Nat.le_findGreatest hk1 (le_trans (hk2 h0) ht)
  refine ⟨hkc, fun h0 => ?_, fun n hn hn' => ?_⟩
  · rw [h.cutTime _ hkc]; exact hk2 h0
  · rw [h.cutTime _ hn']; exact hk3 hn (le_trans hn' hle)

/-- Reads at the end of times `≤ b` agree. -/
theorem readAt_eq (h : tr'.PrefixOf tr b) {t : Time} (ht : t ≤ b) (g : Id) (v : V) :
    tr'.readAt g v t = tr.readAt g v t := by
  unfold readAt
  rw [h.endCut_eq ht, h.read]
  rw [← h.endCut_eq ht]; exact Nat.findGreatest_le _

/-- Ready-reader safety of the prefix is safety of the full trace up to `b`. -/
theorem readySafeUpTo (h : tr'.PrefixOf tr b) {c : Time} {g : Id} {t₀ : Time}
    (hs : tr'.ReadySafe c g t₀) : tr.ReadySafeUpTo c g t₀ b := by
  have hR : ∀ c v t, tr'.point.Ready c v t ↔ tr.point.Ready c v t := by
    intro c v t; rw [h.point]; rfl
  have hin : ∀ i, tr.InCuts t₀ i → tr.cutTime i ≤ b → tr'.InCuts t₀ i ∧ i ≤ tr'.cuts := by
    intro i hi hb
    have hc := h.le_cuts hi.1 hb
    exact ⟨⟨hc, by rw [h.cutTime i hc]; exact hi.2⟩, hc⟩
  constructor
  · intro u v i j hi hj hbi hbj hu hv
    obtain ⟨hi', hic⟩ := hin i hi hbi
    obtain ⟨hj', hjc⟩ := hin j hj hbj
    have := hs.1 u v i j hi' hj' (by rw [hR, h.cutTime i hic]; exact hu)
      (by rw [hR, h.cutTime j hjc]; exact hv)
    rwa [h.read g u i hic, h.read g v j hjc] at this
  · intro v i j hi hij hj hbj hvi hvj
    obtain ⟨hj', hjc⟩ := hin j hj hbj
    have hic : i ≤ tr'.cuts := le_trans hij hjc
    have hi' : tr'.InCuts t₀ i := ⟨hic, by rw [h.cutTime i hic]; exact hi.2⟩
    have := hs.2 v i j hi' hij hj' (by rw [hR, h.cutTime i hic]; exact hvi)
      (by rw [hR, h.cutTime j hjc]; exact hvj)
    rwa [h.read g v i hic, h.read g v j hjc] at this

/-- Resilience of the prefix is resilience of the full trace at reading times
in `[b₀, b]` (for a protected time `T ≤ b₀`). -/
theorem protectedUpTo (h : tr'.PrefixOf tr b) {c : Time} {src dst : Id} {T b₀ b₁ : Time}
    (hT : T ≤ b₀) (hp : tr'.ProtectedThrough c src dst T b₀ b₁) :
    tr.ProtectedUpTo c src dst T b₀ b₁ b := by
  intro v hv t ht htb w hw hr
  have hpt := h.point
  have hhz : tr'.point.horizon = b := by rw [hpt]
  have := hp v (by rw [hpt]; exact hv) t ht (by rw [hhz]; exact htb) w (by rw [hpt]; exact hw)
    (by unfold ResilienceReader at hr ⊢; rw [hpt]; exact hr)
  rwa [h.readAt_eq (le_trans hT (le_trans ht htb)), h.readAt_eq htb] at this

end PrefixOf

end Trace

end Consensus

end
