module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationDefs
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ProposerGap
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Actual proposals from healthy preparation duties -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- A ready designated duty produces a proposal, with honesty at its actual production cut. -/
theorem duty_proposal_run_at (run : (Sys (goldilocks S) V).Run)
    (hn : 1 ≤ Fintype.card V)
    (hv : (Sys (goldilocks S) V).Valid run) (hnc : ¬ run.2.HashCollision)
    {s : Nat} {hold : Time} (hs : 0 < s)
    (hth : (S.params (Model.pubOf run.1) hn).ts s ≤ run.2.horizon)
    (hduty : HonestReadyIn run.2.point run.2.key (fun s => run.2.sel (.proposer s)) s
      ((Sys (goldilocks S) V).cDur (K S A) run)
      ((goldilocks S (Model.pubOf run.1)).skel.grid.slotTime s) hold) :
    ∃ k P, runProposer S run.2 hn s ∈
        honestKeysAt S run.2 ((S.params (Model.pubOf run.1) hn).ts s + hold) ∧
      (simTraceAt S run.2 hn).ProposesAt (runProposer S run.2 hn s) k P ∧
      (simTraceAt S run.2 hn).time k = (S.params (Model.pubOf run.1) hn).ts s ∧
      P.slot = s := by
  have htime : (goldilocks S (Model.pubOf run.1)).skel.grid.slotTime s =
      (S.params (Model.pubOf run.1) hn).ts s := by
    change (s : Time) * (4 * run.1.ΔAC) = 4 * run.1.ΔAC * s
    ring
  have hmem : runProposer S run.2 hn s ∈ run.2.sel (.proposer s) := by
    rw [runProposer_eq S run.2 hn]
    split
    · exact Finset.min'_mem _ _
    · exact absurd hduty.1 ‹_›
  have hR := (hduty.2 _ hmem).1
  rw [htime] at hR
  have h0 : (0 : Time) ≤ (S.params (Model.pubOf run.1) hn).ts s := by
    have := (S.params (Model.pubOf run.1) hn).toParams.hΔ
    simp only [AC.ACParams.ts]
    positivity
  have hnode := ready_transport_at S run.2 hn hv h0 hth hR
  rw [show run.2.ownKey (run.2.key (runProposer S run.2 hn s)) =
    runProposer S run.2 hn s from run.2.key.symm_apply_apply _] at hnode
  have hshort : Regimes.Growing.ReadyAt (simTraceAt S run.2 hn)
      (honestKeysAt S run.2) (Regimes.catchUp (S.params (Model.pubOf run.1) hn))
      (runProposer S run.2 hn s) ((S.params (Model.pubOf run.1) hn).ts s) := by
    refine ⟨hnode.1, fun t ht hts => hnode.2 t ?_ hts⟩
    apply le_trans _ ht
    apply max_le_max_left
    have := catchUp_le_cDur S A V run hn
    linarith
  obtain ⟨k, P, hP, ht⟩ := Regimes.Growing.ready_proposer_proposes_at
    (simTraceAt_goldilocksRun S run.2 hn hv)
    (noCollRun_simTraceAt S run.2 hn hv hnc) hs hshort
  refine ⟨k, P, ?_, hP, ht, ?_⟩
  · have hh := (hduty.2 _ hmem).2
    rw [htime] at hh
    simp only [EnvPoint.HonestAt, EnvPoint.lookAhead, Model.Run.point] at hh
    rw [mem_honestKeysAt_iff S run.2]
    exact hh
  · have h := hP.2.2
    rw [ht, (S.params (Model.pubOf run.1) hn).slotTime_eq] at h
    simp only [AC.ACParams.ts] at h
    exact_mod_cast (mul_left_cancel₀
      (mul_pos four_pos (S.params (Model.pubOf run.1) hn).toParams.hΔ).ne' h).symm

/-- The advertised nonfinal recurrence supplies actual proposals at any vote binding.
The pattern is `[0]`, with span zero and hold one; the end budget is exactly `ts N ≤ heal`.
This does not assert a supplier for arbitrary contracts or progress forms. -/
theorem healthy_preparation_gap_at (run : (Sys (goldilocks S) V).Run)
    (hn : 1 ≤ Fintype.card V) (hv : (Sys (goldilocks S) V).Valid run)
    (hnc : ¬ run.2.HashCollision) {cap : Capability} {idx : ℕ+} {ready heal : Time}
    (hcap : cap = .available ∨ cap = .stable) (hb : heal ≤ run.2.horizon)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V)
      (K S A) cap idx ready heal run)
    {s₀ N : Nat}
    (hs : max ready 0 + 4 * (S.params (Model.pubOf run.1) hn).Δ ≤
      (S.params (Model.pubOf run.1) hn).ts s₀)
    (hN : (S.params (Model.pubOf run.1) hn).ts N ≤ heal) :
    ∀ a, s₀ ≤ a → a + (idx : Nat) ≤ N + 1 →
      ∃ x, a ≤ x ∧ x < a + (idx : Nat) ∧
        ∃ k P, runProposer S run.2 hn x ∈
            honestKeysAt S run.2
              ((S.params (Model.pubOf run.1) hn).ts x + (S.params (Model.pubOf run.1) hn).Δ) ∧
          (simTraceAt S run.2 hn).ProposesAt (runProposer S run.2 hn x) k P ∧
          (simTraceAt S run.2 hn).time k = (S.params (Model.pubOf run.1) hn).ts x ∧
          P.slot = x := by
  let sp := S.params (Model.pubOf run.1) hn
  have hcap' : cap ≠ .final := by rcases hcap with h | h <;> simp [h]
  have hrec : PatternRecurrence run.2.point run.2.key
      (fun s => run.2.sel (.proposer s)) (goldilocks S (Model.pubOf run.1)).skel.grid
      ⟨Pattern.single, idx, 1⟩ ((Sys (goldilocks S) V).cDur (K S A) run) ready heal := by
    simpa only [System.prog, shapeProgress, shapeHolds, goldilocksContract, ite_eq_right hcap',
      Model.sysExternal, System.pt, Sys, Model.sysOf, Model.Run.point] using hp
  have htime : ∀ s : Nat,
      (goldilocks S (Model.pubOf run.1)).skel.grid.slotTime s = sp.ts s := fun s => by
    change (s : Time) * (4 * run.1.ΔAC) = 4 * run.1.ΔAC * s
    ring
  have hL : (goldilocks S (Model.pubOf run.1)).skel.grid.slotLen = 4 * sp.Δ := by
    have h1 := htime 1
    simp only [TimeGrid.slotTime, AC.ACParams.ts] at h1
    push_cast at h1
    linarith
  have hspan : (goldilocks S (Model.pubOf run.1)).skel.grid.slotTime N +
      (((⟨Pattern.single, idx, 1⟩ : Recurrence).pattern.span : Nat) : Time) *
        (goldilocks S (Model.pubOf run.1)).skel.grid.slotLen = sp.ts N := by
    simp [htime, Pattern.single, Pattern.span]
  have hgap := recurrence_gap hrec (by simp [Pattern.single]) (s₀ := s₀) (N := N)
    (by rw [hL, htime]; exact hs) (by rw [hspan]; exact hN)
    (by rw [hspan]; exact hN.trans hb)
  have hΔ := sp.toParams.hΔ
  intro a ha haN
  obtain ⟨x, hxl, hxr, hx⟩ := hgap a ha haN
  have hxr : x < a + (idx : Nat) := hxr
  have haN : a + (idx : Nat) ≤ N + 1 := haN
  have hx0 : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · exfalso
      have hs0 : s₀ = 0 := by omega
      subst hs0
      have := le_max_right ready 0
      simp only [AC.ACParams.ts] at hs
      push_cast at hs
      linarith
    · exact h
  have hxN : sp.ts x ≤ sp.ts N := by
    have : (x : Time) ≤ (N : Time) := by exact_mod_cast (show x ≤ N by omega)
    simp only [AC.ACParams.ts]
    exact mul_le_mul_of_nonneg_left this (mul_nonneg zero_le_four hΔ.le)
  exact ⟨x, hxl, hxr, duty_proposal_run_at S A V run hn hv hnc
    hx0 ((hxN.trans hN).trans hb) (by simpa [Model.Run.point] using hx)⟩

end Consensus.Goldilocks.Obligations.Growing

end
