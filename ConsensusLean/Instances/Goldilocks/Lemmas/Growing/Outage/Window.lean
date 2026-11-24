module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageArmingSteps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Population
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Layer1Proofs
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage windows and local input adapters on the node trace -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams ReplayOrder)
open Generic

/-- The outage window starts one arming lag before the outage, clamped to the horizon. -/
def outageWinStart (sp : ACParams) (b₀ hor : Time) : Time :=
  min (max 0 (b₀ - (4 * sp.k + 6) * sp.Δ)) hor

/-- The outage window ends one arming lag after the stop, clamped to the horizon. -/
def outageWinEnd (sp : ACParams) (b₁ hor : Time) : Time :=
  min (b₁ + (4 * sp.k + 6) * sp.Δ) hor

theorem outageWinStart_eq (sp : ACParams) (b₀ hor : Time) :
    outageWinStart sp b₀ hor = min (max 0 (b₀ - (4 * sp.k + 6) * sp.Δ)) hor := by rfl

theorem outageWinEnd_eq (sp : ACParams) (b₁ hor : Time) :
    outageWinEnd sp b₁ hor = min (b₁ + (4 * sp.k + 6) * sp.Δ) hor := by rfl

theorem outageWinEnd_le_horizon (sp : ACParams) (b₁ hor : Time) :
    outageWinEnd sp b₁ hor ≤ hor := by rw [outageWinEnd_eq]; exact min_le_right _ _

/-- The first slot label whose vote offset reaches the stop. -/
noncomputable def outageRestoredLabel (sp : ACParams) (b₁ : Time) : Nat := by
  classical
  exact if h : ∃ s : Nat, b₁ ≤ sp.ts s + sp.Δ then Nat.find h else 0

theorem outageRestoredLabel_eq (sp : ACParams) (b₁ : Time) :
    outageRestoredLabel sp b₁ = (by
      classical
      exact if h : ∃ s : Nat, b₁ ≤ sp.ts s + sp.Δ then Nat.find h else 0) := by
  classical
  rfl

variable {sp : ACParams} {T b₀ b₁ hor : Time}

/-- The cover-label gates, budget, widened window and retained look-back in node units. -/
theorem outage_window_numbers (hT : 0 ≤ T) (hlag : T + (4 * sp.k + 6) * sp.Δ ≤ b₀)
    (hb : b₀ ≤ b₁) (hbud : b₁ ≤ b₀ + (4 * (sp.k : Time) - 5) * sp.Δ)
    (hhor : 0 ≤ hor) :
    let j₀ := coverLabel sp b₀
    (sp.ts j₀ + 2 * sp.Δ ≤ b₀ ∧ b₀ < sp.ts (j₀ + 1 : Nat) + 2 * sp.Δ ∧
      b₁ - b₀ ≤ (4 * (sp.k : Time) - 5) * sp.Δ ∧ b₀ ≤ b₁ ∧
      b₁ ≤ sp.ts (j₀ + sp.k : Nat) + sp.Δ ∧ sp.ts j₀ + sp.Δ < b₁ ∧
      ∀ t, t ≤ sp.ts (j₀ + sp.k : Nat) + 6 * sp.Δ → t ≤ hor →
        t ≤ outageWinEnd sp b₁ hor) ∧
    (0 ≤ outageWinStart sp b₀ hor ∧
      outageWinStart sp b₀ hor ≤ sp.ts ((j₀ : Int) - sp.k) ∧
      ∀ d ≤ 6 * sp.Δ, sp.ts j₀ + d ≤ hor → sp.ts j₀ + d ≤ outageWinEnd sp b₁ hor) ∧
    max 0 (outageWinEnd sp b₁ hor - (12 * sp.k + 7) * sp.Δ) ≤
      outageWinStart sp b₀ hor := by
  intro j₀
  have hΔ := sp.toParams.hΔ
  have hk : (0 : Time) ≤ sp.k := by positivity
  have hb0 : 2 * sp.Δ ≤ b₀ := by linarith [mul_nonneg hk hΔ.le]
  obtain ⟨hg₁, hg₂⟩ := coverLabel_gates (sp := sp) hb0
  have hkj := (armed_label_lt (σ := 0) hT hlag
    (by simpa [AC.ACParams.ts] using hT)).2
  have hkj' : (sp.k : Int) < j₀ := by exact_mod_cast hkj
  have hjnonneg : (0 : Time) ≤ (j₀ : Int) - sp.k := by
    exact_mod_cast (show (0 : Int) ≤ (j₀ : Int) - sp.k by omega)
  change 4 * sp.Δ * (j₀ : Int) + 2 * sp.Δ ≤ b₀ at hg₁
  change b₀ < 4 * sp.Δ * (j₀ : Int) + 6 * sp.Δ at hg₂
  rw [outageWinStart_eq, outageWinEnd_eq]
  simp only [AC.ACParams.ts]
  push_cast
  refine ⟨⟨hg₁, by linarith, by linarith, hb, by linarith, by linarith,
    fun t ht hth => le_min (by linarith) hth⟩,
    ⟨le_min (le_max_left _ _) hhor, (min_le_left _ _).trans (max_le ?_ ?_),
      fun d hd hdh => le_min (by linarith [mul_nonneg hk hΔ.le]) hdh⟩, ?_⟩
  · exact mul_nonneg (by positivity) hjnonneg
  · linarith
  · have hz := min_le_left (b₁ + (4 * sp.k + 6) * sp.Δ) hor
    have hzh := min_le_right (b₁ + (4 * sp.k + 6) * sp.Δ) hor
    have hη : (0 : Time) ≤ (12 * sp.k + 7) * sp.Δ := by positivity
    exact le_min (max_le (le_max_left _ _) (le_trans (by linarith) (le_max_right _ _)))
      (max_le hhor (by linarith))

theorem outageRestoredLabel_spec (hT : 0 ≤ T)
    (hlag : T + (4 * sp.k + 6) * sp.Δ ≤ b₀) (hb : b₀ ≤ b₁)
    (hbud : b₁ ≤ b₀ + (4 * (sp.k : Time) - 5) * sp.Δ) :
    b₁ ≤ sp.ts (outageRestoredLabel sp b₁) + sp.Δ ∧
      ∀ s : Nat, b₁ ≤ sp.ts s + sp.Δ → outageRestoredLabel sp b₁ ≤ s := by
  classical
  have hn := (outage_window_numbers hT hlag hb hbud (hor := 0) le_rfl).1.2.2.2.2.1
  have h : ∃ s : Nat, b₁ ≤ sp.ts s + sp.Δ := ⟨_, hn⟩
  simp only [outageRestoredLabel_eq, h, ↓reduceDIte]
  exact ⟨Nat.find_spec h, fun s hs => Nat.find_min' h hs⟩

variable {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {C : ACCorrectLocal (goldilocksNode sp ro) (fun v => v.val)}
  {cm : Time → Finset (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The local outage durations in node units, with the budget written without Nat subtraction. -/
theorem outage_durations_of_local {sign : Fin sp.n → Time → Bool} {G : Nat}
    (hC : GoldilocksLocalData sp ro C sign G) :
    C.catchUp = 18 * sp.Δ ∧ C.outageEta = (12 * sp.k + 7) * sp.Δ ∧
      C.outageLag = (4 * sp.k + 6) * sp.Δ ∧
      C.outageBudget = (4 * (sp.k : Time) - 5) * sp.Δ ∧ C.recovery = 9 * sp.Δ := by
  have hk2 : (2 : Int) ≤ sp.k := by exact_mod_cast sp.two_le_k
  have hbcast : ((4 * sp.k - 5 : Nat) : Int) = 4 * (sp.k : Int) - 5 := by omega
  refine ⟨hC.catchUp, ?_, ?_, ?_, hC.recovery⟩
  · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      hC.outageEta
  · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      hC.outageLag
  · simpa only [hbcast] using hC.outageBudget

/-- The L9 local run supplies its canonical committee start and membership facts. -/
theorem outage_inputs_of_local {sign : Fin sp.n → Time → Bool} {G : Nat}
    (hC : GoldilocksLocalData sp ro C sign G)
    (hrun : C.run.Run cm proposer dg H tr) (hnc : NoCollRun dg tr)
    {p : EnvPoint (Fin sp.n)} (hb : RunPointBinding tr H p)
    {ΔF b₀ : Time} (hs : ACServiceBefore C tr H ΔF b₀) :
    (∃ ini, Growing.GoldilocksRun proposer dg H tr ini) ∧
      CommitteeFacts tr H (dictOfTime sp cm) ∧
      (∀ x k, tr.IsCall x k → tr.time k ≤ p.horizon) ∧
      SleepyServiceBefore tr H sp.Δ b₀ := by
  rw [hC.healing.1.1] at hrun
  obtain ⟨hrun, -, -, hfacts, -, -⟩ := hrun
  refine ⟨⟨_, hrun⟩, hfacts hnc, ?_, ?_⟩
  · intro x k hk
    obtain ⟨ℓ, _, hl⟩ := hk
    exact (hb.2.2.2 _).1 ⟨k, Or.inl (by rw [hl]; simp), le_rfl⟩
  · exact SleepyLayer1.sleepyServiceBefore_of_acService hrun
      hC.served hs

end Consensus.Goldilocks.Compose.Growing

end
