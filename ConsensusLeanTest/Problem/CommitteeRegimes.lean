module
public import ConsensusLean.Lemmas.Problem.Facts.Regimes

public section

namespace Consensus.Tests.CommitteeRegimes

variable {V : Type} [Fintype V] [DecidableEq V] {S : System V}
  {Prog : Type} (X : External S) (K : Contract Prog) (r : S.Run)

/-- Full selection adds no restriction when the population bound implies the committee bound. -/
theorem healthy_stock (hfull : ∀ t, X.selected (S.pt r).env (X.ext r) t = Finset.univ)
    (hβ : K.params.β ≤ K.params.βK) (g : Time) :
    S.Healthy X K g r ↔ (S.log r).PSync (S.pt r) g ∧
      (S.pt r).HealthyOn K.params.β g (S.pt r).horizon ∧
      (S.pt r).env.ΔFG ≤ K.params.fgDelay.val * (S.pt r).env.ΔAC := by
  exact System.healthy_iff_of_full_selection X K r hfull hβ g

/-- Full selection recovers sleepy participation when its look-ahead is no larger. -/
theorem sleepy_stock (hfull : ∀ t, X.selected (S.pt r).env (X.ext r) t = Finset.univ)
    (hlook : K.params.committeeAhead ≤ K.params.ahead)
    (hθ : K.params.θ ≤ 1) (h0 : 0 ≤ K.params.θ) :
    S.Sleepy X K r ↔ (S.log r).PSync (S.pt r) 0 ∧
      (S.pt r).SleepyOn K.params.θ (S.cDur K r) (S.aheadDur K r) 0 (S.pt r).horizon := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · rintro ⟨hn, hp⟩
    refine ⟨hn, hp, ?_⟩
    have he : (S.pt r).EtaSleepyOn K.params.θ 0 (S.cDur K r)
        (S.aheadDur K r) 0 (S.pt r).horizon := by
      intro t ht hb
      exact EnvPoint.etaReadyAbove_zero_iff.mpr (hp t ht hb)
    have hw : S.committeeAheadDur K r ≤ S.aheadDur K r :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hlook) (S.pt r).env.ΔAC_pos.le
    simpa only [show X.selected (S.pt r).env (X.ext r) = (fun _ => Finset.univ) from
      funext hfull] using he.committee_univ hw hθ h0

end Consensus.Tests.CommitteeRegimes
