module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Compat
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Saved
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor

public section

/-! # Goldilocks Healing: the live locks at a vote after a slow origin (T1 §4)

For an honest slow lock of slot `s` on `D` (window `≥ r`): at every honest slot-`(s+1)` vote,
every live lock block after the unlocking is compatible with `D` (`slow_live_locks`), provided
the earlier honest slot-`(s+1)` votes extend `D`. A live lock of label `j ≤ s` has
`j ≥ s − k + 1 ≥ r` and sits below an origin of slot `j` (a result or an optimistic
confirmation, `fast_lock_provenance`, `slow_lock_provenance`), compatible with the writer's own
result of slot `j` (T1 §2), which extends `D` (`slow_window_results`: the saved results of the
slow test, and the result `C` itself for `j = s`); one of label `s + 1` is optimistic over earlier
honest slot-`(s+1)` votes. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time}
  {proposer : Nat → Fin sp.n}

/-- A deepest block of a set is the one `deepest` returns. -/
private theorem deepest_eq_of_isDeepest {Φ : Frm sp.n FGP} {S : Set (Blk sp.n FGP)}
    {D : Blk sp.n FGP} (h : IsDeepest Φ S D) : deepest Φ S = some D := by
  have hex : ∃ B, IsDeepest Φ S B := ⟨D, h⟩
  cases hd : deepest Φ S with
  | none =>
    unfold deepest at hd
    simp only [hex, ↓reduceDIte, reduceCtorEq] at hd
  | some D' =>
    have h' := deepest_mem hd
    by_contra hne
    have hne' : D' ≠ D := fun h => hne (congrArg some h)
    rcases h.2 D' h'.1 hne' with h₁ | ⟨h₁, h₂⟩ <;>
      rcases h'.2 D h.1 (Ne.symm hne') with h₃ | ⟨h₃, h₄⟩ <;> omega

/-- Compatibility of `L ⪯ O` with `D ⪯ R` when `O` and `R` are compatible. -/
private theorem compat_of_below (hU : Coherent U) {L O D R : Blk sp.n FGP} (hLO : Anc U L O)
    (hDR : Anc U D R) (h : Compatible U O R) : Compatible U L D := by
  rcases h with h | h
  · exact anc_total hU (hLO.trans h) hDR
  · exact anc_total hU hLO (hDR.trans h)

/-- **The writer's results over a slow lock's window**: for an honest slow lock of slot `s` on
`D`, the writer's update of every slot `j` with `s − k < j ≤ s` has a result extending `D`. -/
theorem slow_window_results (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i₀ s : Nat} {D : Blk sp.n FGP} (hsl : SlowLockAt tr x i₀ s D) :
    ∀ j : Nat, (s : Int) - sp.k < j → j ≤ s →
      ∃ k R CV, ResultAt tr x k j R CV ∧ Anc U D R := by
  sorry

/-- Every stored lock of an honest node sits below an origin of its slot, written at an earlier
cut: a result or an optimistic confirmation of the node. -/
theorem lock_below_origin (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state y i).locks, ∃ L ∈ U, L.root = l.block ∧ ∃ O, Anc U L O ∧
      ∃ k < i, ∃ CV, ResultAt tr y k l.slot O CV ∨ OptimisticLockAt tr y k l.slot O CV := by
  sorry

/-- **The stored locks after a slow origin** (T1 §4): for an honest slow lock of slot `s` on `D`
whose window is `≥ r`, at any cut of an honest node in a slot after `s`, every stored lock of slot
at most `s` that is live there is compatible with `D`: its slot is in the window, so its origin is
compatible with the writer's saved result of that slot (T1 §2), which extends `D`. -/
theorem slow_stored_locks (hS : HealthyBase tr H U proposer g) {x : Fin sp.n} (hx : x ∈ H)
    {i₀ s : Nat} {D : Blk sp.n FGP} (hsl : SlowLockAt tr x i₀ s D)
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts ((s : Int) - sp.k + 1)) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} (hi : s + 1 ≤ sp.slot (tr.time i)) :
    ∀ l ∈ (tr.state y i).locks, sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
      ∀ Y ∈ U, Y.root = l.block → Compatible U Y D := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  intro l hl hlive hle Y hY hYr
  obtain ⟨L, hL, hLr, O, hLO, k, -, CV, hO⟩ := lock_below_origin hr hy i l hl
  obtain rfl : Y = L := hU.1 hY hL (hYr.trans hLr.symm)
  obtain ⟨kx, R, CVx, hR, hDR⟩ := slow_window_results hr hx hsl (U := U) l.slot (by omega) hle
  have hjr : gbar g + 4 * sp.Δ ≤ sp.ts l.slot := hs.trans ((ts_le_iff sp).2 (by omega))
  have hcomp : Compatible U O R := by
    rcases hO with hO | hO
    · exact result_result_compatible hS hy hO hx hR hjr
    · exact (result_optimistic_compatible hS hx hR hy hO hjr).symm
  exact compat_of_below hU hLO hDR hcomp

/-- Saved-result comparison on a finite service prefix. The selected slow lock
and each receiver origin keep their actual observation cutoffs. -/
theorem slow_stored_locks_before {b : Time} (hS : HealthyBaseUpTo tr H U proposer g b)
    (hnr : ∀ y ∈ H, ∀ r, tr.RestartAt y r → tr.time r ≤ gbar g)
    {x : Fin sp.n} (hx : x ∈ H) {i₀ s : Nat} {D : Blk sp.n FGP}
    (hsl : SlowLockAt tr x i₀ s D) (hi₀ : tr.time i₀ ≤ b)
    (hs : gbar g ≤ sp.ts ((s : Int) - sp.k + 1))
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    (hi : s + 1 ≤ sp.slot (tr.time i)) (hib : tr.time i ≤ b) :
    ∀ l ∈ (tr.state y i).locks, sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
      ∀ Y ∈ U, Y.root = l.block → Compatible U Y D := by
  sorry

/-- **T1 §4, the live locks at a vote after a slow origin.** -/
theorem slow_live_locks (hS : HealthyBase tr H U proposer g) {x : Fin sp.n} (hx : x ∈ H)
    {i₀ s : Nat} {D : Blk sp.n FGP} (hsl : SlowLockAt tr x i₀ s D)
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts ((s : Int) - sp.k + 1)) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e)
    (hes : e.msg.slot = s + 1) (hE : EarlierVotesExtend tr H U i (s + 1) D) :
    ∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L D := by
  have hrun := hS.run
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc.1
  have hsi : e.msg.slot = sp.slot (tr.time i) := (castAt_spec hr hy hc).2.1
  have down : ∀ {X Y}, Anc U X Y → Compatible U Y D → Compatible U X D := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact anc_total hU hXY h
  have hwin := slow_window_results hr hx hsl (U := U)
  rintro L ⟨hL, l, ⟨l₀, hl₀, B₀, hB₀, hB₀r, hlive, rfl⟩, hlL⟩
  have hLe : L = ℓ.frame.viableAncestor B₀ :=
    hU.1 (hΦU hL) (hΦU (viableAncestor_anc hΦ hB₀).1) hlL.symm
  subst hLe
  refine down (Anc.mono hΦU (anc_viableAncestor _ B₀)) ?_
  rcases le_or_gt l₀.slot s with hle | hlt
  · -- a lock of slot at most `s` sits below a stored lock, below an origin of its slot
    obtain ⟨l₁, hl₁, hsl₁, B₁, hB₁, hB₁r, B₀', hB₀', hB₀'r, hA⟩ :=
      readPoint_locks_below_stored hr hy hc (show 0 < sp.slot (tr.time i) by omega) l₀ hl₀
        (show l₀.slot ≠ sp.slot (tr.time i) by omega)
    obtain rfl : B₀' = B₀ := hΦ.coherent.1 hB₀' hB₀ (hB₀'r.trans hB₀r.symm)
    have hlive := hlive.trans ((castAt_readPoint_locksWF hr hy hc).cap hl₀)
    exact down (Anc.mono hΦU hA) (slow_stored_locks hS hx hsl hs hy (by omega) l₁ hl₁
      (by omega) (by omega) B₁ (hΦU hB₁) hB₁r)
  · -- a lock of slot `s + 1` or later is optimistic, over earlier honest slot-`(s+1)` votes
    obtain ⟨Φ', A, D', -, hΦ'U, -, h34, hpool, -, L₀, hL₀, hL₀r, hL₀D⟩ :=
      lock_origin_readPoint hrun hy hc l₀ hl₀ (by rw [hes]; push_cast; omega)
    obtain rfl : L₀ = B₀ := hU.1 hL₀ (hΦU hB₀) (hL₀r.trans hB₀r.symm)
    refine down hL₀D (origin_compatible hU hΦ'U h34 hS.two_faulty_lt fun v hv hvH => ?_)
    obtain ⟨hvs, j, hj, e', hvote, rfl⟩ := hpool v hv hvH
    obtain ⟨ℓ', hcj⟩ := id hvote
    have hsj : e'.msg.slot = sp.slot (tr.time j) := (castAt_spec hr hvH hcj).2.1
    have : sp.slot (tr.time j) ≤ sp.slot (tr.time i) :=
      slot_mono sp (hr.time_nonneg j) (hr.time_mono hj.le)
    exact hE _ hvH j hj e' hvote (by omega)

/-- Read-point lock comparison needs only stored-lock comparisons at this cut,
the fault bound, and earlier votes. In particular it does not require whole-run
health or use a future writer update as an earlier state transition. -/
theorem live_locks_of_stored_before (hrun : ACRun proposer tr H U)
    (hf : 2 * Hᶜ.ncard < sp.n) {s : Nat} {D : Blk sp.n FGP}
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hes : e.msg.slot = s + 1)
    (hstored : ∀ l ∈ (tr.state y i).locks,
      sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
      ∀ Y ∈ U, Y.root = l.block → Compatible U Y D)
    (hE : EarlierVotesExtend tr H U i (s + 1) D) :
    ∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L D := by
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc.1
  have hsi := (castAt_spec hr hy hc).2.1
  have down : ∀ {X Y}, Anc U X Y → Compatible U Y D → Compatible U X D := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact anc_total hU hXY h
  rintro L ⟨hL, l, ⟨l₀, hl₀, B₀, hB₀, hB₀r, hlive, rfl⟩, hlL⟩
  have hLe : L = ℓ.frame.viableAncestor B₀ :=
    hU.1 (hΦU hL) (hΦU (viableAncestor_anc hΦ hB₀).1) hlL.symm
  subst hLe
  refine down (Anc.mono hΦU (anc_viableAncestor _ B₀)) ?_
  rcases le_or_gt l₀.slot s with hle | hlt
  · obtain ⟨l₁, hl₁, hsl₁, B₁, hB₁, hB₁r, B₀', hB₀', hB₀'r, hA⟩ :=
      readPoint_locks_below_stored hr hy hc (show 0 < sp.slot (tr.time i) by omega) l₀ hl₀
        (show l₀.slot ≠ sp.slot (tr.time i) by omega)
    obtain rfl : B₀' = B₀ := hΦ.coherent.1 hB₀' hB₀ (hB₀'r.trans hB₀r.symm)
    have hlive := hlive.trans ((castAt_readPoint_locksWF hr hy hc).cap hl₀)
    exact down (Anc.mono hΦU hA)
      (hstored l₁ hl₁ (by omega) (by omega) B₁ (hΦU hB₁) hB₁r)
  · obtain ⟨Φ', A, D', -, hΦ'U, -, h34, hpool, -, L₀, hL₀, hL₀r, hL₀D⟩ :=
      lock_origin_readPoint hrun hy hc l₀ hl₀ (by rw [hes]; push_cast; omega)
    obtain rfl : L₀ = B₀ := hU.1 hL₀ (hΦU hB₀) (hL₀r.trans hB₀r.symm)
    refine down hL₀D (origin_compatible hU hΦ'U h34 hf fun v hv hvH => ?_)
    obtain ⟨hvs, j, hj, e', hvote, rfl⟩ := hpool v hv hvH
    obtain ⟨ℓ', hcj⟩ := id hvote
    have hsj := (castAt_spec hr hvH hcj).2.1
    have : sp.slot (tr.time j) ≤ sp.slot (tr.time i) :=
      slot_mono sp (hr.time_nonneg j) (hr.time_mono hj.le)
    exact hE _ hvH j hj e' hvote (by omega)

end Consensus.Goldilocks.SA

end
