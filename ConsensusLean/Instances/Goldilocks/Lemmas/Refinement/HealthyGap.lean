module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthySuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ProposerGap

public section

/-! # Goldilocks Refinement: the honest-proposer gap of a healthy query (#136, S3)

`hgp_of_healthyQuery`: for a `HealthyPreparationQuery` with nonfinal progress on `[ready, heal]`,
every slot window `[a, a + X)` with `X = Q.index` inside `[s₀, N]` has an actual honest designated
proposal. This is the premise `hgp` of `Healing.FrameWindow.rise_reset` at `G = X`.

The proof uses only the nonfinal `Pattern.single` recurrence (span `0`) from `hp`, with
`recurrence_gap` at start `ready` and stop `heal`. The endpoint is `ts N ≤ heal ≤ horizon`. The
duty gives the proposal through `duty_proposal_run`. The guards `0 < x` and `ts x ≤ horizon`
follow from `hs`, `x ≤ N`, `hN` and `hb`. No reset, frame, coefficient or whole-run progress is
assumed. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The premise GP of the rise from a healthy query.** Nonfinal progress on `[ready, heal]`,
`heal ≤ horizon`, `max ready 0 + 4Δ ≤ t_{s₀}` and `t_N ≤ heal` give, in every slot window
`[a, a + X)` with `X = Q.index` inside `[s₀, N]`, a slot `x` whose designated proposer is honest
and actually proposes a block of slot `x`. -/
theorem hgp_of_healthyQuery (Q : HealthyPreparationQuery S A V)
    (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A)
      Q.cap Q.index Q.ready Q.heal Q.run)
    {s₀ N : Nat} (hs : max Q.ready 0 + 4 * Q.params.Δ ≤ Q.params.ts s₀)
    (hN : Q.params.ts N ≤ Q.heal) :
    ∀ a, s₀ ≤ a → a + (Q.index : Nat) ≤ N + 1 → ∃ x, a ≤ x ∧ x < a + (Q.index : Nat) ∧
      runProposer S Q.run.2 Q.hn x ∈ honestKeys S Q.run.2 ∧
      ∃ k P, Q.trace.ProposesAt (runProposer S Q.run.2 Q.hn x) k P ∧ P.slot = x := by
  have hcap : Q.cap ≠ .final := by rcases Q.nonfinal with h | h <;> simp [h]
  have hrec : PatternRecurrence Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) (family S (Model.pubOf Q.run.1)).skel.grid
      ⟨Pattern.single, Q.index⟩ ((Sys (family S) V).cDur (K S A) Q.run) Q.ready Q.heal := by
    simpa only [System.prog, shapeProgress, shapeHolds, acceptanceContract, ite_eq_right hcap,
      Model.sysExternal, System.pt, Sys, Model.sysOf, Model.Run.point] using hp
  have htime : ∀ s : Nat, (family S (Model.pubOf Q.run.1)).skel.grid.slotTime s =
      Q.params.ts s := fun s => by
    change (s : Time) * (4 * Q.run.1.Δ) = 4 * Q.run.1.Δ * s
    ring
  have hL : (family S (Model.pubOf Q.run.1)).skel.grid.slotLen = 4 * Q.params.Δ := by
    have h1 := htime 1
    simp only [TimeGrid.slotTime, SA.SAParams.ts] at h1
    push_cast at h1
    linarith
  have hspan : (family S (Model.pubOf Q.run.1)).skel.grid.slotTime N +
      (((⟨Pattern.single, Q.index⟩ : Recurrence).pattern.span : Nat) : Time) *
        (family S (Model.pubOf Q.run.1)).skel.grid.slotLen = Q.params.ts N := by
    simp [htime, Pattern.single, Pattern.span]
  have hgap := recurrence_gap hrec (by simp [Pattern.single]) (s₀ := s₀) (N := N)
    (by rw [hL, htime]; exact hs) (by rw [hspan]; exact hN)
    (by rw [hspan]; exact hN.trans hb)
  have hΔ := Q.params.toParams.hΔ
  intro a ha haN
  obtain ⟨x, hxl, hxr, hx⟩ := hgap a ha haN
  have hxr : x < a + (Q.index : Nat) := hxr
  have haN : a + (Q.index : Nat) ≤ N + 1 := haN
  have hx0 : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · exfalso
      have hs0 : s₀ = 0 := by omega
      subst hs0
      have := le_max_right Q.ready 0
      simp only [SA.SAParams.ts] at hs
      push_cast at hs
      linarith
    · exact h
  have hxN : Q.params.ts x ≤ Q.params.ts N := by
    have : (x : Time) ≤ (N : Time) := by exact_mod_cast (show x ≤ N by omega)
    simp only [SA.SAParams.ts]
    nlinarith
  obtain ⟨k, P, hP, hk, -, -, hPs, -⟩ := duty_proposal_run S A V Q.run Q.hn Q.valid
    Q.noCollision hx0 ((hxN.trans hN).trans hb) hx
  exact ⟨x, hxl, hxr, hP.1, k, P, hk, hPs⟩

end Consensus.Goldilocks.Refinement

end
