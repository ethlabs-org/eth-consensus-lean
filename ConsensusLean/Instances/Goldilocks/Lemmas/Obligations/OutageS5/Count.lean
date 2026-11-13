module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutageMajority
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Count
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # `OutageS5`: the extending majority at the first restored label

The `q = r` arm of `restored_majority`. Given an honest call at or after `t_r + Δ`:

* every member of the cohort `A₀` casts a slot-`r` vote (it is awake and joined at `t_r + Δ`,
  `OutageVoteInv.cohort_ready`), and that vote extends `P` (lock safety's (H) for `A₀`, at any
  cast time, since `σ < r ≤ j₀ + k`);
* an honest slot-`r` caster whose vote does not extend `P` casts within the no-sleep window, so it
  is in `A₀ ∪ W` (`hawake`), and not in `A₀`, so it is a late waker;
* hence the opponents lie in `Hᶜ ∪ W`, and `|Hᶜ ∪ W| < |A₀|` (`hcohort`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **`ExtendingMajority` at the first restored label**: `A₀` casts and extends `P`; the opponents
lie in `Hᶜ ∪ W`. -/
theorem restored_majority_at_r (D : OutageLockPremises tr H proposer dg)
    (hinv : ∀ i, OutageLockInv D i)
    (hcall : ∃ x ∈ H, ∃ i, tr.IsCall x i ∧ sp.ts D.r + sp.Δ ≤ tr.time i) :
    ExtendingMajority tr H D.P D.r := by
  have hσ := D.hσ
  have hrk := D.hrk
  -- `a ≤ t_{j₀}` from `D.ha`, stated with `0 < Δ` in context so that it also reads the form
  -- `a + Δ ≤ t_{j₀}`
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have ha := D.ha
  have hslot : D.σ < D.r ∧ D.r ≤ D.j₀ + sp.k := ⟨by omega, hrk.2⟩
  rw [extendingMajority_iff]
  -- `A₀` casts in slot `r` and extends `P`
  have hA : D.A₀ ⊆ ExtendingCasters tr H D.P D.r := by
    intro x hx
    obtain ⟨haw, hjn⟩ := OutageVoteInv.cohort_ready D hx hrk.1 hrk.2 hcall
    obtain ⟨k, e, hv, hs, -⟩ := vote_of_awake_joined D.hrun D.hnc (D.hA₀ hx)
      (mayVote_stock D.hrun D.hnc (D.hA₀ hx) _) haw hjn
    exact extendingCasters_iff.2 ⟨D.hA₀ hx, k, e, hv, hs,
      (hinv (k + 1)).votes x (D.hA₀ hx) k (Nat.lt_succ_self k) e hv (hs ▸ hslot.1)
        (hs ▸ hslot.2) (Or.inr hx)⟩
  -- an honest slot-`r` caster that does not extend `P` is a late waker
  have hO : Opponents tr H D.P D.r ⊆ Hᶜ ∪ D.W := by
    intro x hx
    rcases opponents_iff.1 hx with hx | ⟨hx, k, e, hv, hs, hne⟩
    · exact Or.inl hx
    refine Or.inr ?_
    obtain ⟨hts, hte⟩ := OutageVoteInv.ts_le_cast D hx hv
    rw [hs] at hts hte
    have hcallk : tr.IsCall x k := by
      obtain ⟨ℓ, hc, -⟩ := hv
      exact ⟨_, projAC_callAt.1 hc⟩
    have hrK := ts_le_ts (sp := sp) hrk.2
    have hjr := ts_le_ts (sp := sp) (show D.j₀ ≤ D.r by omega)
    have hz := D.hz (tr.time k) (by linarith) ⟨x, hx, k, hcallk, le_rfl⟩
    rcases D.hawake x hx (tr.time k) (by linarith) hz (D.hrun.awake_of_call x hx k hcallk)
      with hA₀ | hW
    · exact absurd ((hinv (k + 1)).votes x hx k (Nat.lt_succ_self k) e hv (hs ▸ hslot.1)
        (hs ▸ hslot.2) (Or.inr hA₀)) hne
    · exact hW
  exact (Set.ncard_le_ncard hO (Set.toFinite _)).trans_lt
    (D.hcohort.trans_le (Set.ncard_le_ncard hA (Set.toFinite _)))

end Consensus.Goldilocks.Compose

end
