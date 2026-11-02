module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Rise
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.FinalWindowAssembly
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedC4
import ConsensusLean.Lemmas.Blocks.Facts

public section

/-! # Goldilocks Refinement: the honest-proposer gap of the rise (#136)

consensus-lean#136. The premise `hgp` of `Healing.FrameWindow.rise_reset` (GP: every slot window
`[a, a + G)` inside `[s₀, N]` has an actual honest designated proposal), from the query's
recurrence.

* `recurrence_gap`: a recurrence whose pattern has offset `0` gives an honest-ready duty in every
  window `[a, a + gap)` inside `[s₀, N]`. The query is at `t = slotTime a − slotLen`: the start
  slot `s` has `t < slotTime s ≤ t + gap · slotLen`, so `a ≤ s ≤ a + gap − 1`. The window gap is
  `G = gap`, not `gap + span + 1`: the span enters only the margin
  `slotTime N + span · slotLen ≤ min stop horizon`.
* `hgp_of_query`: for a `FinalQuery` (pattern `finalWindow`, gap `X = Q.index`, span `6`), with
  the duty → proposal premise in the leaf form of `final_window_extract_of` (H2), the premise
  `hgp` of `rise_reset` with `G = X`. The rise bound of `rise_reset` is then
  `ρ = δ_t + X − 1`. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape
open SA (gbar)

section Gap

variable {V : Type} [Fintype V] {p : EnvPoint V} {key : Fin (Fintype.card V) ≃ V}
  {sel : Slot → Finset (Fin (Fintype.card V))} {G : TimeGrid} {ρ : Recurrence}
  {c start stop : Time}

/-- **The duty gap of a recurrence.** With offset `0` in the pattern, every slot window
`[a, a + gap)` inside `[s₀, N]` has a slot whose selected keys are honest and ready, when
`max start 0 + slotLen ≤ slotTime s₀` and the pattern of slot `N` ends by `stop` and by the
horizon. -/
theorem recurrence_gap (h : PatternRecurrence p key sel G ρ c start stop)
    (h0 : 0 ∈ ρ.pattern.offsets) {s₀ N : Nat}
    (hs : max start 0 + G.slotLen ≤ G.slotTime s₀)
    (hstop : G.slotTime N + (ρ.pattern.span : Time) * G.slotLen ≤ stop)
    (hhor : G.slotTime N + (ρ.pattern.span : Time) * G.slotLen ≤ p.horizon) :
    ∀ a, s₀ ≤ a → a + (ρ.gap : Nat) ≤ N + 1 → ∃ x, a ≤ x ∧ x < a + (ρ.gap : Nat) ∧
      HonestReadyIn p key sel x c (G.slotTime x) := by
  intro a ha haN
  have hL := G.slotLen_pos
  have hlen : (ρ.len : Time) = ((ρ.gap : Nat) : Time) + (ρ.pattern.span : Time) := by
    simp [Recurrence.len]
  have hg1 : 1 ≤ (ρ.gap : Nat) := ρ.gap.pos
  have haN' : ((a : Time) + ((ρ.gap : Nat) : Time)) ≤ (N : Time) + 1 := by exact_mod_cast haN
  have hsa : G.slotTime s₀ ≤ G.slotTime a := by
    unfold TimeGrid.slotTime
    have : (s₀ : Time) ≤ (a : Time) := by exact_mod_cast ha
    nlinarith
  have hend : G.slotTime a - G.slotLen + (ρ.len : Time) * G.slotLen ≤
      G.slotTime N + (ρ.pattern.span : Time) * G.slotLen := by
    unfold TimeGrid.slotTime
    rw [hlen]
    nlinarith
  obtain ⟨s, hs₁, hs₂, hall⟩ := h (G.slotTime a - G.slotLen) (by linarith)
    (hend.trans hstop) (hend.trans hhor)
  have hall0 := hall 0 h0
  rw [Nat.add_zero] at hall0
  unfold TimeGrid.slotTime at hs₁ hs₂
  have hlo : ((a : Time) - 1) * G.slotLen < (s : Time) * G.slotLen := by linarith
  have hhi : (s : Time) * G.slotLen ≤ ((a : Time) - 1 + ((ρ.gap : Nat) : Time)) * G.slotLen := by
    linarith
  have hlo' : (a : Int) - 1 < (s : Int) := lt_of_mul_lt_mul_right hlo hL.le
  have hhi' : (s : Int) ≤ (a : Int) - 1 + ((ρ.gap : Nat) : Int) :=
    le_of_mul_le_mul_right hhi hL
  refine ⟨s, ?_, ?_, hall0⟩
  · omega
  · omega

end Gap

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The premise GP of the rise from a query.** For a `FinalQuery` with the duty → proposal
premise (`hpropose`, the leaf form (H2) of `final_window_extract_of`), every slot window
`[a, a + X)` with `X = Q.index` inside `[s₀, N]` has an actual honest designated proposal, when
`max ready 0 + 4Δ ≤ t_{s₀}` and `t_{N + 6} ≤ horizon` (`6` is the span of `finalWindow`). This
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
    (hN : Q.params.ts (N + 6 : Nat) ≤ Q.run.2.horizon) :
    ∀ a, s₀ ≤ a → a + (Q.index : Nat) ≤ N + 1 → ∃ x, a ≤ x ∧ x < a + (Q.index : Nat) ∧
      runProposer S Q.run.2 Q.hn x ∈ honestKeys S Q.run.2 ∧
      ∃ k P, Q.trace.ProposesAt (runProposer S Q.run.2 Q.hn x) k P ∧ P.slot = x := by
  have hrec : PatternRecurrence Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) (finalGrid S A V Q) ⟨finalWindow S, Q.index⟩
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
      (((⟨finalWindow S, Q.index⟩ : Recurrence).pattern.span : Nat) : Time) *
        (finalGrid S A V Q).slotLen = Q.params.ts (N + 6 : Nat) := by
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
