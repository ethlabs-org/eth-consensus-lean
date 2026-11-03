module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.AcceptanceDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Run
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Regimes.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Suffix

public section

/-! # Goldilocks Refinement: the proposer gap core (#136, S3)

The upstream core of the honest-proposer gap. It does not import `RiseGap`,
`FinalWindowAssembly`, `FinalWindowDefs` or `HealedSafety`.

* `recurrence_gap`: a recurrence whose pattern has offset `0` gives an honest-ready duty in every
  window `[a, a + gap)` inside `[s₀, N]`. The query is at `t = slotTime a − slotLen`: the start
  slot `s` has `t < slotTime s ≤ t + gap · slotLen`, so `a ≤ s ≤ a + gap − 1`. The window gap is
  `G = gap`, not `gap + span + 1`: the span enters only the margin
  `slotTime N + span · slotLen ≤ min stop horizon`.
* `duty_proposal_run`: in a valid, collision-free run, an honest-ready proposer duty at a slot
  `s > 0` with `t_s ≤ horizon` gives the designated proposer's actual proposal at `t_s`. The run
  catch-up duration covers the protocol catch-up `18 Δp` through `accepted_catchUp_ge_sleepy`.
  `FinalQuery` and `HealthyPreparationQuery` use it as thin instances. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape

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

/-- The run catch-up duration covers the protocol catch-up `18 Δp`. -/
theorem catchUp_le_cDur (run : (Sys (family S) V).Run) (hn : 1 ≤ Fintype.card V) :
    Regimes.catchUp (S.params (Model.pubOf run.1) hn) ≤ (Sys (family S) V).cDur (K S A) run := by
  sorry

/-- **Duty to actual proposal, run level.** In a valid, collision-free run, an honest-ready
proposer duty at a slot `s > 0` with `t_s ≤ horizon` gives the run proposer's actual proposal `P`
of slot `s` at a cut of time `t_s`, accepted by its proposer, ready there for the run catch-up
duration, and an `HonestProposalRun`. -/
theorem duty_proposal_run (run : (Sys (family S) V).Run) (hn : 1 ≤ Fintype.card V)
    (hv : (Sys (family S) V).Valid run) (hnc : ¬ run.2.HashCollision) {s : Nat} (hs : 0 < s)
    (hth : (S.params (Model.pubOf run.1) hn).ts s ≤ run.2.horizon)
    (hduty : HonestReadyIn run.2.point run.2.key (fun s => run.2.sel (.proposer s)) s
      ((Sys (family S) V).cDur (K S A) run)
      ((family S (Model.pubOf run.1)).skel.grid.slotTime s)) :
    ∃ k P, Healing.HonestProposalRun (simTrace S run.2 hn) (honestKeys S run.2)
        (runProposer S run.2 hn) s P ∧
      (simTrace S run.2 hn).ProposesAt (runProposer S run.2 hn s) k P ∧
      (simTrace S run.2 hn).AcceptAt (runProposer S run.2 hn s) k P ∧
      (simTrace S run.2 hn).time k = (S.params (Model.pubOf run.1) hn).ts s ∧ P.slot = s ∧
      Regimes.ReadyAt (simTrace S run.2 hn) (honestKeys S run.2)
        ((Sys (family S) V).cDur (K S A) run)
        (runProposer S run.2 hn s) ((S.params (Model.pubOf run.1) hn).ts s) := by
  sorry

end Consensus.Goldilocks.Refinement

end
