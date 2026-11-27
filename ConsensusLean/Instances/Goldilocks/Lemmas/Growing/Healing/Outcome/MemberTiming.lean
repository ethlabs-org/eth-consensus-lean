module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
import ConsensusLean.Lemmas.Tactic.Linarith

public section

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b hold : Time}
  {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

/-- A member of an earlier label written before the cast deadline was already written before
the proposal. Adjacent-label updates occur after that deadline; optimistic writes stay within
their own slot. -/
theorem member_before_proposal_of_cast_deadline_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {i k u s : Nat} (hti : tr.time i = sp.ts u) (hk : tr.time k ≤ sp.ts u + sp.Δ)
    {C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hC : HealedMemberBefore tr H g a b C s k) (hs : s < u) :
    HealedMemberBefore tr H g a b C s i := by
  have before {r : Nat} (hrt : tr.time r < sp.ts u) : r < i := by
    exact lt_of_not_ge fun hir => (hp.run.time_mono hir).not_gt (hrt.trans_eq hti.symm)
  have update_time {x r ell} (hu : AC.UpdateAt tr.projAC x r s ell)
      (hrk : r < k) : tr.time r < sp.ts u := by
    have ht : tr.time r = sp.ts s + 6 * sp.Δ := hu.2.2.1
    have hr := (hp.run.time_mono hrk.le).trans hk
    have htwo : (s : Int) + 2 ≤ u := by
      exact_mod_cast Compose.ts_add_two_le (ht ▸ hr)
    simp only [ACParams.ts] at ht ⊢
    have hΔ := sp.toParams.hΔ
    linarith [mul_le_mul_of_nonneg_left htwo (show (0 : Time) ≤ 4 * sp.Δ by linarith)]
  rcases healedMemberBefore_iff.1 hC with
    ⟨hfloor, x, r, CV, hrk, hx, hrb, hres⟩ |
      ⟨hfloor, x, r, hrk, hx, hrb, hlock⟩ | ⟨x, r, hrk, hrb, ho⟩
  · refine healedMemberBefore_iff.2 (Or.inl ⟨hfloor, x, r, CV, ?_, hx, hrb, hres⟩)
    apply before
    rcases hres with ⟨ell, hu, _⟩ | hop
    · exact update_time hu hrk
    · exact Outcome.fastLock_time_lt_at hp.run (Or.inr hop) hs
        ((hp.run.time_mono hrk.le).trans hk)
  · refine healedMemberBefore_iff.2 (Or.inr (Or.inl
      ⟨hfloor, x, r, ?_, hx, hrb, hlock⟩))
    exact before (Outcome.lock_time_lt_at hp.run hlock hs
      ((hp.run.time_mono hrk.le).trans hk))
  · refine healedMemberBefore_iff.2 (Or.inr (Or.inr ⟨x, r, ?_, hrb, ho⟩))
    obtain ⟨CV, ell, D, _, hf, _⟩ := ho.2.2.1
    exact before (Outcome.fastLock_time_lt_at hp.run hf hs
      ((hp.run.time_mono hrk.le).trans hk))

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
