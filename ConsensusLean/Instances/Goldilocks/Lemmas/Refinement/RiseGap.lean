module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Rise
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.FinalWindowAssembly
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedC4
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ProposerGap
import ConsensusLean.Lemmas.Blocks.Facts

public section

/-! # Goldilocks Refinement: the honest-proposer gap of the rise (#136)

consensus-lean#136. The premise `hgp` of `Healing.FrameWindow.rise_reset` (GP: every slot window
`[a, a + G)` inside `[s₀, N]` has an actual honest designated proposal), from the query's
recurrence.

* `recurrence_gap` (now in `ProposerGap`, statement unchanged): offset `0` gives an
  honest-ready duty in every window `[a, a + gap)` inside `[s₀, N]`; `G = gap`.
* `hgp_of_query`: for a `FinalQuery` (pattern `finalWindow`, gap `X = Q.index`, span `3c`), with
  the duty → proposal premise in the leaf form of `final_window_extract_of` (H2), the premise
  `hgp` of `rise_reset` with `G = X`. The rise bound of `rise_reset` is then
  `ρ = δ_t + X − 1`. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape
open SA (gbar)

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The premise GP of the rise from a query.** For a `FinalQuery` with the duty → proposal
premise (`hpropose`, the leaf form (H2) of `final_window_extract_of`), every slot window
`[a, a + X)` with `X = Q.index` inside `[s₀, N]` has an actual honest designated proposal, when
`max ready 0 + 4Δ ≤ t_{s₀}` and `t_{N + 3c} ≤ horizon` (`3c` is the span of `finalWindow`). This
is the premise `hgp` of `Healing.FrameWindow.rise_reset` at `G = X`; its rise bound is
`ρ = δ_t + X − 1`. -/
theorem hgp_of_query (Q : FinalQuery S A V)
    {dg : Digest (List (FG.Att Q.params.n)) (SA.Payload Q.params.n)}
    (hrun : GoldilocksRun (runProposer S Q.run.2 Q.hn) dg (honestKeys S Q.run.2) Q.trace)
    (hpropose : ∀ s, HonestReadyIn Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) s ((Sys (family S) V).cDur (K S A) Q.run)
      ((finalGrid S A V Q).slotTime s) →
      ∃ P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) s P)
    {s₀ N : Nat}
    (hs : max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0 + 4 * Q.params.Δ ≤
      Q.params.ts s₀)
    (hN : Q.params.ts (N + 3 * cF A.rowRatio : Nat) ≤ Q.run.2.horizon) :
    ∀ a, s₀ ≤ a → a + (Q.index : Nat) ≤ N + 1 → ∃ x, a ≤ x ∧ x < a + (Q.index : Nat) ∧
      runProposer S Q.run.2 Q.hn x ∈ honestKeys S Q.run.2 ∧
      ∃ k P, Q.trace.ProposesAt (runProposer S Q.run.2 Q.hn x) k P ∧ P.slot = x := by
  have hrec : PatternRecurrence Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) (finalGrid S A V Q) ⟨finalWindow A, Q.index⟩
      ((Sys (family S) V).cDur (K S A) Q.run) ((Sys (family S) V).ready (K S A) Q.gst Q.run)
      Q.run.2.horizon := by
    simpa only [System.prog, shapeProgress, shapeHolds, acceptanceContract, ↓reduceIte,
      Model.sysExternal, System.pt, Sys, Model.sysOf, Model.Run.point] using Q.progress
  have hL : (finalGrid S A V Q).slotLen = 4 * Q.params.Δ := by
    have h1 := finalGrid_slotTime S A V Q 1
    simp only [TimeGrid.slotTime, SA.SAParams.ts] at h1
    push_cast at h1
    linarith
  have hspan : (finalGrid S A V Q).slotTime N +
      (((⟨finalWindow A, Q.index⟩ : Recurrence).pattern.span : Nat) : Time) *
        (finalGrid S A V Q).slotLen = Q.params.ts (N + 3 * cF A.rowRatio : Nat) := by
    rw [← finalGrid_slotTime S A V Q, (finalGrid S A V Q).slotTime_add]
    simp [finalWindow_span]
  have hgap := recurrence_gap hrec (by simp [finalWindow_offsets]) (s₀ := s₀) (N := N)
    (by rw [hL, finalGrid_slotTime]; exact hs) (by rw [hspan]; exact hN)
    (by rw [hspan]; exact hN)
  intro a ha haN
  obtain ⟨x, hxl, hxr, hx⟩ := hgap a ha haN
  obtain ⟨P, hP⟩ := hpropose x hx
  obtain ⟨k, hk⟩ := proposesAt_of_honestProposalRun hrun hP
  obtain ⟨-, -, -, -, -, -, -, -, -, hPs, -⟩ := hP.2
  exact ⟨x, hxl, hxr, hP.1, k, P, hk, hPs⟩

end Consensus.Goldilocks.Refinement
