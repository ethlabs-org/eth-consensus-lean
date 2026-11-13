module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Regimes
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Count
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage under growing faults: the extending majority at the first restored label

The `q = r` arm of the restored majority, a cohort count charged at the window end `z`. Given an
honest call at or after `t_r + Δ`:

* every member of the cohort `A₀` in the slot-`r` committee `K_r` casts a slot-`r` vote while
  honest (it is awake and joined at `t_r + Δ ≤ z`, `OutageVoteInv.cohort_ready_at`, and the gate
  permits it), and that vote extends `P` (lock safety's (H) for `A₀`, since `σ < r ≤ j₀ + k`);
  `A₀ ⊆ H z`, so these are extending casters at `z`;
* a slot-`r` caster still honest at `z` whose vote does not extend `P` casts in `[a, z]`, so it is
  a late waker (`cohort_classify`, and not `A₀`);
* hence the opponents at `z` in `K_r` lie in `K_r ∩ ((H z)ᶜ ∪ W)`, and
  `|K_r ∩ ((H z)ᶜ ∪ W)| < |K_r ∩ A₀|` (`hcohortK`). The majority at `z` is one at every `d ≤ z`
  (`ExtendingMajorityAt.anti_time`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- **The extending majority at the first restored label**, charged at every `d ≤ z`: the members
of `A₀` in `K_r` cast and extend `P`; the opponents at `z` in `K_r` lie in `(H z)ᶜ ∪ W`. -/
theorem restored_majority_at_r_at (D : OutageLockPremises tr H proposer dg ini)
    (hinv : ∀ i, OutageLockInv D i)
    (hcall : ∃ x i, x ∈ H (tr.time i) ∧ tr.IsCall x i ∧ sp.ts D.r + sp.Δ ≤ tr.time i) :
    ∀ d ≤ D.z, ExtendingMajorityAt tr H D.K D.P D.r d := by
  have hσ := D.hσ
  have hrk := D.hrk
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have ha := D.ha
  have hslot : D.σ < D.r ∧ D.r ≤ D.j₀ + sp.k := ⟨by omega, hrk.2⟩
  have hrK := ts_le_ts (sp := sp) hrk.2
  have hjr := ts_le_ts (sp := sp) (show D.j₀ ≤ D.r by omega)
  have hrz : sp.ts D.r + sp.Δ ≤ D.z := D.hzc _ (by linarith) hcall
  have hmaj : ExtendingMajorityAt tr H D.K D.P D.r D.z := by
    rw [extendingMajorityAt_iff]
    -- the members of `A₀` cast in slot `r` while honest and extend `P`
    have hA : D.K.committee D.r ∩ D.A₀ ⊆ ExtendingCastersAt tr H D.P D.r D.z := by
      intro x hx
      obtain ⟨haw, hjn⟩ := OutageVoteInv.cohort_ready_at D hx.2 hrk.1 hrk.2 hcall
      have hxr : x ∈ H (sp.ts D.r + sp.Δ) := D.hrun.antitone hrz (D.hA₀ hx.2)
      obtain ⟨k, e, hv, hs, -⟩ := vote_of_awake_joined_at D.hrun D.hnc hxr
        (mayVote_of_committee D.facts.hGate (ts_add_delta_nonneg _) hxr hx.1) haw hjn
      exact extendingCastersAt_iff.2 ⟨D.hA₀ hx.2, k, e, hv, hs,
        (hinv (k + 1)).votes x k (Nat.lt_succ_self k) e hv (hs ▸ hslot.1) (hs ▸ hslot.2)
          (Or.inr hx.2)⟩
    -- a slot-`r` caster still honest at `z` that does not extend `P` is a late waker
    have hO : D.K.committee D.r ∩ OpponentsAt tr H D.P D.r D.z ⊆
        D.K.committee D.r ∩ ((H D.z)ᶜ ∪ D.W) := by
      rintro x ⟨hxK, hx⟩
      refine ⟨hxK, ?_⟩
      rcases opponentsAt_iff.1 hx with hx | ⟨hxz, k, e, hv, hs, hne⟩
      · exact Or.inl hx
      obtain ⟨hts, hte⟩ := hv.ts_le_cast D.hrun D.hnc
      rw [hs] at hts hte
      have hz := D.hzc (tr.time k) (by linarith)
        ⟨x, k, (hVoteAt_iff.1 hv).1, hv.isCall, le_rfl⟩
      rcases D.cohort_classify hv (by linarith) hz with hA₀ | hW | hn
      · exact absurd ((hinv (k + 1)).votes x k (Nat.lt_succ_self k) e hv (hs ▸ hslot.1)
          (hs ▸ hslot.2) (Or.inr hA₀)) hne
      · exact Or.inr hW
      · exact absurd hxz hn
    exact (Set.ncard_le_ncard hO (Set.toFinite _)).trans_lt
      ((D.hcohortK D.r (by omega) hrk.2 (honestCall_mono hcall (by linarith))).trans_le
        (Set.ncard_le_ncard hA (Set.toFinite _)))
  exact fun d hd => hmaj.anti_time D.hrun.antitone hd

end Consensus.Goldilocks.Compose.Growing

end
