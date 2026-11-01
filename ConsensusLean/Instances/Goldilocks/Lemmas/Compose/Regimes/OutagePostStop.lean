module
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Outage
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest

public section

/-! # Conditional post-stop outage adapters -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

/-- Among a slow lock's consecutive labels, at least one is outside the outage pollution
window, under the engine gap budget. -/
theorem exists_unpolluted_label (sp : SA.SAParams) {start stop : Time}
    (hΔ : 2 ≤ sp.Δ)
    (hgap : stop - start ≤ (4 * (sp.k : Time) - 6) * (sp.Δ - 1)) (s : Int) :
    ∃ m : Int, s - (sp.k : Int) < m ∧ m ≤ s ∧
      (sp.ts m + 2 * sp.Δ ≤ start ∨ stop ≤ sp.ts m + sp.Δ) := by
  have hk : (2 : Int) ≤ sp.k := by exact_mod_cast sp.two_le_k
  by_contra hn
  have hfirst : start < sp.ts (s - sp.k + 1) + 2 * sp.Δ := by
    by_contra h
    exact hn ⟨s - sp.k + 1, by omega, by omega, Or.inl (le_of_not_gt h)⟩
  have hlast : sp.ts s + sp.Δ < stop := by
    by_contra h
    exact hn ⟨s, by omega, le_rfl, Or.inr (le_of_not_gt h)⟩
  simp only [SA.SAParams.ts] at hfirst hlast
  nlinarith

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- Every honest voter in a successor vote's merged view was awake during the preceding
slot's voting window. The lookback bound is an explicit hypothesis. -/
theorem merged_voters_recently_awake (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {c η : Time} (hη : sp.Δ ≤ η) {s : Nat}
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (_hs : e.msg.slot = s + 1) :
    SA.voters (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes ⊆
      {x | Regimes.ReadyAt tr H c x (sp.ts s + sp.Δ) ∨
        Regimes.RecentlyAwake tr H η x (sp.ts s + sp.Δ) ∨ x ∉ H} := by
  have hr := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  rintro x ⟨v, hv, rfl⟩
  by_cases hx : v.val ∈ H
  · obtain ⟨j, -, e', hv', he'⟩ := SA.honest_merged_vote hr hy hc hv hx
    obtain ⟨ℓ', hc'⟩ := hv'
    have hslot : e'.msg.slot = s := by
      rw [he']
      exact SA.merged_vote_slot hr.localRun hy hc v hv
    have hspec := SA.castAt_spec hr.localRun hx hc'
    have hupper := SA.vote_time_le hr.localRun hx ⟨ℓ', hc'⟩
    have hlower := (SA.ts_le_iff_le_slot sp (hr.localRun.time_nonneg j)
      (sp.slot (tr.projAC.time j) : Int)).2 le_rfl
    rw [← hspec.2.1, hslot] at hupper hlower
    change sp.ts s ≤ tr.time j at hlower
    refine Or.inr (Or.inl ⟨hx, tr.time j, ?_, hupper, ?_⟩)
    · exact max_le (hr.localRun.time_nonneg j) (by linarith)
    · exact hr.localRun.awake_of_call v.val hx j ℓ' hc'.1
  · exact Or.inr (Or.inr hx)

end Consensus.Goldilocks.Compose
