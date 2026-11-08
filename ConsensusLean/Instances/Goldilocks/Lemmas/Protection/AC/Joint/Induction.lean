module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Joint.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Joint.Prot
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Rows.Locks

public section

/-! # Tier A protection, the joint invariant over AC traces: the cut induction

**The joint induction** (`outage_inv_AC`): over an AC trace with the unlock given by a lawful
oracle `u` at a write mode `wm` (`ACRunU wm u`), under trivial frames, from the premise package
`OutagePremisesAC`, the keep `FloorKeepAC` and the step `OutageS5StepAC`, the outage lock invariant
`OutageInvAC` holds at every cut. The cohort's floors (`protPrev`, `protCover`), the vote extension
(H), the result compatibility (R) and the stored-lock compatibility (i) are proved together.

The step from `i` to `i + 1` follows `Compose.outage_lock_inv`, steps 1–3 and 6: (H) for the casts
at cut `i` (within `b₀` by the frontier, by `A₀` after it through the protection at `i`,
`OutageInvAC.cohort_vote_extendsAC`), S5V at cut `i` (`hS5 i`), (R) for the results at cut `i`
(`OutageVoteInvAC.result_compatibleAC`), (i) at `i + 1` (`locks_compatibleAC`, with OL-W at
`i + 1`), and the protections at `i + 1`: carried from `i` by the keep at the cut-`i` call
(`prot_stepAC`), or founded at the update's next cut by the bases (`prot_of_prevBaseAC`,
`prot_of_coverBaseAC`). The composite's steps 4–5, the FG sources and the caches `Σ.F`, `Σ.J`
with the viability of `P`, have no AC counterpart under trivial frames: `Φ.F` is genesis and every
frame block is viable. -/

namespace Consensus.Goldilocks.Comparison

open SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {wm : WriteMode} {u : Nat → Set Lock}
  {proposer : Nat → Fin sp.n}

/-- **The outage lock invariant over AC traces at every cut**: from the premise package, the
per-call lock retention `FloorKeepAC` (the lock rule's own input) and the step `OutageS5StepAC`
at each cut. -/
theorem outage_inv_AC (D : OutagePremisesAC wm u proposer tr H U) (hkeep : FloorKeepAC D)
    (hS5 : OutageS5StepAC D) : ∀ i, OutageInvAC D i := by
  have hr := D.hrun.localRun
  have hσ := D.hσ
  have hK := sp.two_le_k
  have hpreC : ∀ C s, OriginWithinAC tr H C s D.b₀ → C ∈ U → Compatible U C D.P :=
    fun _ _ hC _ => D.compatible_of_withinAC hC
  intro i
  induction i with
  | zero =>
    have hv0 : OutageVoteInvAC D 0 := ⟨fun _ _ k hk => absurd hk (Nat.not_lt_zero k),
      fun _ _ k hk => absurd hk (Nat.not_lt_zero k)⟩
    refine ⟨hv0, fun _ _ k hk => absurd hk (Nat.not_lt_zero k), fun y hy k hk l hl => ?_,
      fun _ _ _ _ _ _ k hck hk => absurd (hck.trans_le hk) (Nat.not_lt_zero _),
      fun _ _ _ _ _ _ k hck hk => absurd (hck.trans_le hk) (Nat.not_lt_zero _)⟩
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    exact locks_compatibleAC D.hrun D.hw D.hj₀ D.hr.2 D.hgap hpreC
      (fun _ _ k hk => absurd hk (Nat.not_lt_zero k))
      (fun _ _ _ k hk => absurd hk (Nat.not_lt_zero k)) D.two_mul_lt hy hl
  | succ i hinv =>
    -- 1. (H) and 1′. S5V at cut `i`
    have hvotes : ∀ x ∈ H, ∀ e, VoteAt tr x i e → D.σ < e.msg.slot →
        e.msg.slot ≤ D.j₀ + sp.k → (tr.time i ≤ D.b₀ ∨ x ∈ D.A₀) →
        VoteExtends U e.msg D.P := by
      intro x hx e hv hs hsK hpre
      by_cases hb : tr.time i ≤ D.b₀
      · exact D.vote_extends_preAC hx hv hb hs
      · exact hinv.cohort_vote_extendsAC hkeep (hpre.resolve_left hb) hv hsK (not_le.1 hb)
    have hvi : OutageVoteInvAC D (i + 1) :=
      ⟨fun x hx k hk e hv hs hsK hpre => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
          · exact hinv.votes x hx k hk e hv hs hsK hpre
          · exact hvotes x hx e hv hs hsK hpre,
        fun x hx k hk e hv hs => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
          · exact hinv.late x hx k hk e hv hs
          · exact outageS5StepAC_iff.1 hS5 k hinv x hx e hv hs⟩
    -- 2. (R) at cut `i`
    have hres : ∀ y ∈ H, ∀ k < i + 1, ∀ m C CV, ResultAt tr y k m C CV →
        (m ≤ D.j₀ ∨ D.r ≤ m) → Compatible U C D.P := by
      intro y hy k hk m C CV hR hm
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact hinv.results y hy k hk m C CV hR hm
      · exact hinv.toOutageVoteInvAC.result_compatibleAC hy hR hm
    -- 3. (i) at `i + 1`
    have hlocks : ∀ y ∈ H, ∀ k ≤ i + 1, ∀ l ∈ (tr.state y k).locks,
        ∃ L ∈ U, L.root = l.block ∧ Compatible U L D.P := by
      intro y hy k hk l hl
      rcases Nat.le_succ_iff.1 hk with hk | rfl
      · exact hinv.locks y hy k hk l hl
      · exact locks_compatibleAC D.hrun D.hw D.hj₀ D.hr.2 D.hgap hpreC hres
          (fun x hx hxW k hk e hv hs => hvi.voteCompat_of_not_lateWakerAC hx hxW hk hv hs)
          D.two_mul_lt hy hl
    have hslot_mono : sp.slot (tr.time (i - 1)) ≤ sp.slot (tr.time i) :=
      slot_mono sp (hr.time_nonneg _) (hr.time_mono (Nat.sub_le i 1))
    -- 6. the protections at `i + 1`
    refine ⟨hvi, hres, hlocks, ?_, ?_⟩
    · intro x hx c ℓ hu hbase k hck hk hkK
      rcases Nat.le_succ_iff.1 hk with hk | rfl
      · exact hinv.protPrev x hx c ℓ hu hbase k hck hk hkK
      replace hkK : sp.slot (tr.time i) ≤ D.j₀ - 1 + sp.k := hkK
      rcases Nat.lt_succ_iff_lt_or_eq.1 hck with hci | rfl
      · have hsl := slot_after_updateAC hr hu hci.le
        exact prot_stepAC hkeep hinv.toOutageVoteInvAC hx (Or.inl rfl) hkK (by omega)
          (hinv.protPrev x hx c ℓ hu hbase i hci le_rfl (hslot_mono.trans hkK))
      · exact prot_of_prevBaseAC (D.hA₀ hx) hu hbase
    · intro x hx c ℓ hu hbase k hck hk hkK
      rcases Nat.le_succ_iff.1 hk with hk | rfl
      · exact hinv.protCover x hx c ℓ hu hbase k hck hk hkK
      replace hkK : sp.slot (tr.time i) ≤ D.j₀ + sp.k := hkK
      rcases Nat.lt_succ_iff_lt_or_eq.1 hck with hci | rfl
      · have hsl := slot_after_updateAC hr hu hci.le
        exact prot_stepAC hkeep hinv.toOutageVoteInvAC hx (Or.inr rfl) hkK (by omega)
          (hinv.protCover x hx c ℓ hu hbase i hci le_rfl (hslot_mono.trans hkK))
      · exact prot_of_coverBaseAC (D.hA₀ hx) hu hbase

end Consensus.Goldilocks.Comparison

end
