module
public import AvailableChainGridCO.Proofs.Snapshot

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- A release tick cannot also be a confirmation gate. -/
theorem releaseTime_ne_gateTime (p : Params) (r s : Slot) :
    releaseTime p r ≠ gateTime p s := by
  intro he
  have hm : (4 * (r : Time) + 5) * p.Δ = (4 * (s : Time) + 6) * p.Δ := by
    dsimp [releaseTime, gateTime, proposalTime] at he
    nlinarith
  have hn : 4 * (r : ℤ) + 5 = 4 * (s : ℤ) + 6 :=
    mul_right_cancel₀ (ne_of_gt p.deltaPos) hm
  omega

/-- The actual release clock first expires rows and then applies the
release count from the strict input. Changes to the clock and snapshots
cannot change that count, because stored receipts have fixed stamps. -/
theorem clock_release_obligations (p : Params) {n : Nat} (st : State n) (r : Slot)
    (hs : ReceiptStamped st) :
    (clock p st (releaseTime p r)).obligations =
      st.obligations.filter (fun (B, g, deadline) =>
        releaseTime p r < deadline && releaseCount p st r B < g) := by
  have hd : 4 * p.Δ ≠ 0 := ne_of_gt (by linarith [p.deltaPos])
  have ht : releaseTime p r - 5 * p.Δ = 4 * p.Δ * (r : Time) := by
    simp [releaseTime, proposalTime]
  have hslot : ((releaseTime p r - 5 * p.Δ) / (4 * p.Δ)).toNat = r := by
    simp [ht, hd]
  have hn : 0 ≤ releaseTime p r - 5 * p.Δ := by
    rw [ht]
    exact mul_nonneg (by linarith [p.deltaPos]) (Int.natCast_nonneg r)
  have hgate : ∀ s, (releaseTime p r == gateTime p s) = false := by
    intro s
    exact beq_eq_false_iff_ne.mpr (releaseTime_ne_gateTime p r s)
  rw [clock_eq_gate_prestate]
  simp only [hgate, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  unfold clockPreGate
  dsimp only
  simp only [hslot, hn, decide_true, beq_self_eq_true, Bool.and_self, ↓reduceIte]
  have hc : ∀ st', receiptData st' = receiptData st → ∀ B,
      releaseCount p st' r B = releaseCount p st r B := by
    intro st' he B
    exact releaseCount_eq_of_receiptData p st' st he hs r B
  split <;> split
  all_goals
    simp only [release, expire, freeze]
    simp only [List.filter_filter]
    apply List.filter_congr
    intro row _
    rw [Bool.and_comm]
    congr 2
    apply congrArg (fun count => count < row.2.1)
    apply hc
    rfl

/-- A row present for the next HEAD survived the actual expiry and
release phases. The raw strict-input release uses the same count. -/
theorem nextHeadState_row_survives_release {V : Type} [DecidableEq V]
    (p : Params) (rho : Run V (gridCO p)) (r : Slot) (reader : V)
    (K : Block) (g : Nat) (deadline : Time)
    (hm : (K, g, deadline) ∈ (nextHeadState p rho r reader).obligations) :
    (K, g, deadline) ∈ (release p (releaseInput p rho r reader) r).obligations ∧
      releaseTime p r < deadline := by
  change (K, g, deadline) ∈ (clock p (releaseInput p rho r reader) (releaseTime p r)).obligations
    at hm
  have hst : ReceiptStamped (releaseInput p rho r reader) :=
    run_time_receiptStamped p rho (releaseTime p r) reader
  rw [clock_release_obligations p (releaseInput p rho r reader) r hst] at hm
  obtain ⟨hold, htest⟩ := List.mem_filter.mp hm
  have ht : releaseTime p r < deadline ∧
      releaseCount p (releaseInput p rho r reader) r K < g := by simpa using htest
  exact ⟨List.mem_filter.mpr ⟨hold, decide_eq_true ht.2⟩, ht.1⟩

/-- A conflicting row still present at the next ordinary HEAD must be
strictly stronger than the genuine prefix support. This includes rows
acquired by the preceding pending gate. -/
theorem nextHeadState_conflict_stronger {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (B C K : Block) (g : Nat) (deadline : Time)
    (hc : confirmation p (gateInput p rho r source) r = some C)
    (hp : Block.Preceq B C) (hk : Block.compatible K B = false)
    (hm : (K, g, deadline) ∈ (nextHeadState p rho r reader).obligations) :
    prefixSupport p (gateInput p rho r source) r B < g := by
  exact surviving_conflict_stronger_from_engine p E rho hΔ r hsync source reader hs hr
    B C K g deadline hc hp hk
    (nextHeadState_row_survives_release p rho r reader K g deadline hm).1

/-- If all stronger rows are compatible with a genuine prefix, release
leaves only compatible live targets for the next ordinary HEAD. -/
theorem nextHeadState_targets_compatible {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source : V) (hs : source ∈ rho.honest) (B C : Block)
    (hc : confirmation p (gateInput p rho r source) r = some C)
    (hp : Block.Preceq B C)
    (hstrong : ∀ reader ∈ rho.honest, ∀ K g deadline,
      (K, g, deadline) ∈ (nextHeadState p rho r reader).obligations →
      prefixSupport p (gateInput p rho r source) r B < g → Block.Compatible K B) :
    ∀ reader ∈ rho.honest, ∀ K ∈ liveTargets (nextHeadState p rho r reader),
      Block.Compatible K B := by
  intro reader hr K hK
  simp only [liveTargets] at hK
  obtain ⟨⟨target, g, deadline⟩, hm, htarget⟩ := List.mem_filterMap.mp hK
  dsimp only at htarget
  split at htarget
  · have he : target = K := by simpa using htarget
    subst target
    cases hcompat : Block.compatible K B with
    | true => exact hcompat
    | false =>
        exact hstrong reader hr K g deadline hm
          (nextHeadState_conflict_stronger p E rho hΔ r hsync source reader hs hr
            B C K g deadline hc hp hcompat hm)
  · simp at htarget

end AvailableChain.GridCO
end
