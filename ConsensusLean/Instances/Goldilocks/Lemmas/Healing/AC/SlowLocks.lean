module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Compat
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Saved
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint

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
  have hU := hr.coherent
  obtain ⟨ℓX, C, hupd, hconf, -, hdeep, hneq⟩ := hsl
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hupd.1
  have hD := deepest_mem hdeep
  obtain ⟨⟨hDt, -, hDC⟩, hcond⟩ := hD.1
  intro j hj hjs
  rcases hjs.lt_or_eq with hjs | rfl
  swap
  · exact ⟨i₀, C, _, ⟨ℓX, hupd, hconf, rfl⟩, Anc.mono hΦU hDC⟩
  rcases hcond with hfast | hslow
  · -- a block of the path that passes the fast test is the fast test's selection
    exfalso
    refine hneq (deepest_eq_of_isDeepest ⟨⟨hD.1.1, hfast⟩, fun X hX hne => ?_⟩)
    exact hD.2 X ⟨hX.1, Or.inl hX.2⟩ hne
  · obtain ⟨S, hS, hSr, hDS⟩ := hslow j hj (by exact_mod_cast hjs)
    obtain ⟨k, -, R, CV, hR, hRr⟩ := saved_result hr hx i₀ j hSr
    have hRU : R ∈ U := by
      obtain ⟨ℓ', hu', hR', -⟩ := hR
      exact (frameIn_of_callAt hr hx hu'.1).2 (deepest_mem hR').1.1
    obtain rfl : R = S := hU.1 hRU (hΦU hS) hRr
    exact ⟨k, R, CV, hR, Anc.mono hΦU hDS⟩

/-- Every stored lock of an honest node sits below an origin of its slot: a result or an
optimistic confirmation of an honest node. -/
theorem lock_below_origin (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state y i).locks, ∃ L ∈ U, L.root = l.block ∧ ∃ O, Anc U L O ∧
      ∃ k CV, ResultAt tr y k l.slot O CV ∨ OptimisticLockAt tr y k l.slot O CV := by
  intro l hl
  cases hf : l.fast
  · obtain ⟨j, -, B, hsl, L, hL, hLr, hLB⟩ := slow_lock_provenance hr hy i l hl hf
    obtain ⟨ℓX, C, hupd, hconf, -, hdeep, -⟩ := hsl
    have hΦU := (frameIn_of_callAt hr hy hupd.1).2
    obtain ⟨⟨-, -, hBC⟩, -⟩ := (deepest_mem hdeep).1
    exact ⟨L, hL, hLr, C, hLB.trans (Anc.mono hΦU hBC), j, _,
      Or.inl ⟨ℓX, hupd, hconf, rfl⟩⟩
  · obtain ⟨j, -, B, CV, hfl, L, hL, hLr, hLB⟩ := fast_lock_provenance hr hy i l hl hf
    rcases hfl with ⟨ℓX, C, hupd, hconf, -, hfs, -⟩ | hopt
    · have hΦU := (frameIn_of_callAt hr hy hupd.1).2
      obtain ⟨⟨-, -, hBC⟩, -⟩ := (deepest_mem hfs).1
      exact ⟨L, hL, hLr, C, hLB.trans (Anc.mono hΦU hBC), j, _,
        Or.inl ⟨ℓX, hupd, hconf, rfl⟩⟩
    · exact ⟨L, hL, hLr, B, hLB, j, CV, Or.inr hopt⟩

/-- **T1 §4, the live locks at a vote after a slow origin.** -/
theorem slow_live_locks (hS : StandaloneRun tr H U g) {x : Fin sp.n} (hx : x ∈ H)
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
    obtain ⟨L₁, hL₁, hL₁r, O, hL₁O, k, CV, hO⟩ := lock_below_origin hr hy i l₁ hl₁
    obtain rfl : L₁ = B₁ := hU.1 hL₁ (hΦU hB₁) (hL₁r.trans hB₁r.symm)
    have hj₁ : ((s : Int) - sp.k) < (l₁.slot : Int) := by
      simp only at hlive
      omega
    obtain ⟨kx, R, CVx, hR, hDR⟩ := hwin l₁.slot hj₁ (by omega)
    have hΔ := sp.toParams.hΔ
    have hjr : gbar g + 4 * sp.Δ ≤ sp.ts l₁.slot :=
      hs.trans ((ts_le_iff sp).2 (by omega))
    have hcomp : Compatible U O R := by
      rcases hO with hO | hO
      · exact result_result_compatible hS hy hO hx hR hjr
      · exact (result_optimistic_compatible hS hx hR hy hO hjr).symm
    exact compat_of_below hU ((Anc.mono hΦU hA).trans hL₁O) hDR hcomp
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

end Consensus.Goldilocks.SA

end
