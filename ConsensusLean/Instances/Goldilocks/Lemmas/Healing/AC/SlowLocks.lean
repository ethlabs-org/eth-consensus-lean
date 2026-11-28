module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Saved
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: the live locks at a vote after a slow origin

For an honest slow lock of slot `s` on `D` (window `≥ r`): at every honest slot-`(s+1)` vote, every
live lock block after the unlocking is compatible with `D`, provided the
earlier honest slot-`(s+1)` votes extend `D`. A live lock of label `j ≤ s` has
`j ≥ s − k + 1 ≥ r` and sits
below an origin of slot `j` (a result or an optimistic confirmation, `fast_lock_provenance`,
`slow_lock_provenance`), compatible with the writer's own result of slot `j` (same-slot
compatibility), which extends `D` (`slow_window_results`: the saved results of the slow test, and
the result `C` itself for `j = s`); one of label `s + 1` is optimistic over earlier honest
slot-`(s+1)` votes. -/

namespace Consensus.Goldilocks.AC

variable {wm : AC.WriteMode}

variable {FGP : Type} {sp : ACParams} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP} {g : Time}
  {proposer : Nat → Fin sp.n}

/-- `slow_window_results` with the unlock given. -/
theorem slow_window_resultsU
    {u : Nat → Set Lock} {ini} (hr : ACLocalRunU wm u H U tr ini)
    (hini : ∀ y, AC.VoteStart sp.genesisRoot (ini y)) {x : Fin sp.n}
    (hx : x ∈ H) {i₀ s : Nat} {D : Blk sp.n FGP} (hsl : SlowLockAt tr x i₀ s D) :
    ∀ j : Nat, (s : Int) - sp.k < j → j ≤ s →
      ∃ k R CV, ResultAt tr x k j R CV ∧ Anc U D R := by
  have hU := hr.coherent
  obtain ⟨ℓX, C, hupd, hconf, hdeep⟩ := hsl
  obtain ⟨-, hΦU⟩ := frameIn_of_callAtU hr hx hupd.1
  obtain ⟨⟨-, -, hDC⟩, -, hslow⟩ := (deepest_mem hdeep).1
  intro j hj hjs
  rcases hjs.lt_or_eq with hjs | rfl
  swap
  · exact ⟨i₀, C, _, ⟨ℓX, hupd, hconf, rfl⟩, Anc.mono hΦU hDC⟩
  obtain ⟨S, hS, hSr, hDS⟩ := hslow j hj (by exact_mod_cast hjs)
  obtain ⟨k, -, R, CV, hR, hRr⟩ := saved_resultU hr hini hx i₀ j hSr
  have hRU : R ∈ U := by
    obtain ⟨ℓ', hu', hR', -⟩ := hR
    exact (frameIn_of_callAtU hr hx hu'.1).2 (deepest_mem hR').1.1
  obtain rfl : R = S := hU.1 hRU (hΦU hS) hRr
  exact ⟨k, R, CV, hR, Anc.mono hΦU hDS⟩

/-- **The writer's results over a slow lock's window**: for an honest slow lock of slot `s` on
`D`, the writer's update of every slot `j` with `s − k < j ≤ s` has a result extending `D`. -/
theorem slow_window_results {ini} (hr : ACLocalRun (goldilocksAC sp FGP) H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y)) {x : Fin sp.n}
    (hx : x ∈ H) {i₀ s : Nat} {D : Blk sp.n FGP} (hsl : SlowLockAt tr x i₀ s D) :
    ∀ j : Nat, (s : Int) - sp.k < j → j ≤ s →
      ∃ k R CV, ResultAt tr x k j R CV ∧ Anc U D R :=
  slow_window_resultsU (hr := hr.toU) (hini := hini) (x := x) (hx := hx)
    (i₀ := i₀) (s := s) (D := D) (hsl := hsl)

/-- `lock_below_origin` with the unlock given. -/
theorem lock_below_originU
    {u : Nat → Set Lock} {ini} (hr : ACLocalRunU wm u H U tr ini)
    (hini : ∀ y, AC.VoteStart sp.genesisRoot (ini y)) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state y i).locks, ∃ L ∈ U, L.root = l.block ∧ ∃ O, Anc U L O ∧
      ∃ k < i, ∃ CV, ResultAt tr y k l.slot O CV ∨ OptimisticLockAt tr y k l.slot O CV := by
  intro l hl
  cases hf : l.fast
  · obtain ⟨j, hj, B, hsl, L, hL, hLr, hLB⟩ := slow_lock_provenanceM hr hini hy i l hl hf
    obtain ⟨ℓX, C, hupd, hconf, hdeep⟩ := slowLockAtW_iff.1 hsl
    have hΦU := (frameIn_of_callAtU hr hy hupd.1).2
    obtain ⟨⟨-, -, hBC⟩, -⟩ := (deepest_mem hdeep).1
    exact ⟨L, hL, hLr, C, hLB.trans (Anc.mono hΦU hBC), j, hj, _,
      Or.inl ⟨ℓX, hupd, hconf, rfl⟩⟩
  · obtain ⟨j, hj, B, CV, hfl, L, hL, hLr, hLB⟩ := fast_lock_provenanceU hr
      hini hy i l hl hf
    rcases hfl with ⟨ℓX, C, hupd, hconf, hfs, -⟩ | hopt
    · have hΦU := (frameIn_of_callAtU hr hy hupd.1).2
      obtain ⟨⟨-, -, hBC⟩, -⟩ := (deepest_mem hfs).1
      exact ⟨L, hL, hLr, C, hLB.trans (Anc.mono hΦU hBC), j, hj, _,
        Or.inl ⟨ℓX, hupd, hconf, rfl⟩⟩
    · exact ⟨L, hL, hLr, B, hLB, j, hj, CV, Or.inr hopt⟩

/-- Every stored lock of an honest node sits below an origin of its slot, written at an earlier
cut: a result or an optimistic confirmation of the node. -/
theorem lock_below_origin {ini} (hr : ACLocalRun (goldilocksAC sp FGP) H U tr ini)
    (hini : ∀ y, AC.VoteStart sp.genesisRoot (ini y)) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state y i).locks, ∃ L ∈ U, L.root = l.block ∧ ∃ O, Anc U L O ∧
      ∃ k < i, ∃ CV, ResultAt tr y k l.slot O CV ∨ OptimisticLockAt tr y k l.slot O CV :=
  lock_below_originU (hr := hr.toU) (hini := hini) (y := y) (hy := hy) (i := i)

/-- Read-point lock comparison needs only stored-lock comparisons at this cut,
the fault bound, and earlier votes. In particular it does not require whole-run
health or use a future writer update as an earlier state transition. -/
theorem live_locks_of_stored_before {ini}
    (hrun : ACRun proposer tr H U ini) (K : CommitteeDict sp.n) (hP : CommitteeP K tr H)
    {s : Nat} (hf : 2 * (K.committee (s + 1) ∩ Hᶜ).ncard < sp.committeeSize) {D : Blk sp.n FGP}
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksAC sp FGP)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hes : e.msg.slot = s + 1)
    (hstored : ∀ l ∈ (tr.state y i).locks,
      sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
      ∀ Y ∈ U, Y.root = l.block → Compatible U Y D)
    (hE : EarlierVotesExtend tr H U i (s + 1) D) :
    ∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L D := by
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc.1
  have hsi := (castAt_specU hr.toU hy hc).2.1
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
    have hlive := hlive.trans ((castAt_readPoint_locksWFU hr.toU hrun.vstart hy hc).cap hl₀)
    exact down (Anc.mono hΦU hA)
      (hstored l₁ hl₁ (by omega) (by omega) B₁ (hΦU hB₁) hB₁r)
  · obtain ⟨Φ', A, D', -, hΦ'U, -, h34, hpool, ⟨k, -, hAk⟩, L₀, hL₀, hL₀r, hL₀D⟩ :=
      lock_origin_readPoint hrun hy hc l₀ hl₀ (by rw [hes]; push_cast; omega)
    obtain rfl : L₀ = B₀ := hU.1 hL₀ (hΦU hB₀) (hL₀r.trans hB₀r.symm)
    -- the read-point lock is of the vote's own slot, whose committee holds the origin's pool
    have hl₀s : l₀.slot = s + 1 := by
      have := readPoint_lock_slot_leU hr.toU hrun.vstart hy hc l₀ hl₀
      omega
    rw [hl₀s] at h34 hpool hAk
    refine down hL₀D (origin_compatible hU hΦ'U K h34
      (fun _ ⟨v, hv, hvu, _⟩ => hvu ▸ hP.1 y hy (k + 1) (s + 1) v (hAk hv)) hf
      fun v hv hvH => ?_)
    obtain ⟨hvs, j, hj, e', hvote, rfl⟩ := hpool v hv hvH
    obtain ⟨ℓ', hcj⟩ := id hvote
    have hsj := (castAt_specU hr.toU hvH hcj).2.1
    have : sp.slot (tr.time j) ≤ sp.slot (tr.time i) :=
      slot_mono sp (hr.time_nonneg j) (hr.time_mono hj.le)
    exact hE _ hvH j hj e' hvote (by omega)

end Consensus.Goldilocks.AC

end
