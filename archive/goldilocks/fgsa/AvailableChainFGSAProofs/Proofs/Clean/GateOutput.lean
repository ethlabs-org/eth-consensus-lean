module
public import AvailableChainFGSAProofs.Proofs.Clean.Action

public section

namespace AvailableChain.FGSA.Run

variable {ΔF : Time}

open AvailableChain.SimplexFG
open AvailableChain.Gen.Pure

variable (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 §§8.2, 8.7; bp02 §5.5 (567–592). Class B: this conditional
run theorem uses one fixed history and the actual FG-SA gate write.
DC counterpart: Legacy/Definitions/SafetyRegimes.lean:61–75, confirmationFields
and liveAtConfirmation. DIVERGES, INTENTIONAL: FG-SA has an optional raw
result and a whole-result lease guard, unlike DC's SG/live confirmation.
The fresh genuine slot excludes skip; compatible advance puts the result
below S, and NestOK makes normalization inert. No history closure is used.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_gateOutput_body (b₀ : Time) :
    CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
    FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
    ∀ i, i ≤ timeIdx rho b₀ → CleanHist p c E rho i →
      ∀ j v s, j < i → v ∈ rho.honest → enabledGateAt p c E rho j v s →
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          gatePassedAt p c E rho j ∧ Block.Preceq B (S_at p c E rho (j + 1) v) := by
  intro h hq hf hsrc i hi hh j v s hji _ ht
  have hs := cleanState_of_hist h hq hf hsrc (clean_actionStep p c E rho)
    (Nat.le_trans (Nat.le_of_lt hji) hi) (cleanHist_restrict (Nat.le_of_lt hji) hh)
  have hsch := h.base.valid.toScheduleWellFormed
  obtain ⟨B, hB, _⟩ := hh.nonempty j v s hji ht
  refine ⟨B, hB, clean_gate_passed hsch hji hh hs ht, ?_⟩
  have hc := Option.some.inj ((clean_gate_raw hsch ht).symm.trans hB)
  rw [clockPre_fg] at hc
  have hview := fgsa_clockPre_gateView p (storeAt p c E rho j v) s
  have hraw : (fgsaAC E rho).raw j s v = some B := by
    have hb := congrArg (fun w => SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho j v).fg.F) w s) hview
    exact hb.symm.trans hc
  have hguard : ∀ lease ∈ ((fgsaAC E rho).gateView j v s).obligations,
      Block.Compatible (Gen.AC.Lease.target lease) B := by
    intro lease hm
    have he : (clockPre p (storeAt p c E rho j v) (SA.gateTime p.toParams s)).base.obligations =
        ((fgsaAC E rho).gateView j v s).obligations := by
      have he' := congrArg GridCO.State.obligations hview
      exact he'
    rw [← he] at hm
    have hg := List.any_eq_false.mp (clean_state_gate_guard hsch hji hh hs ht.1 hB) lease hm
    simpa only [Gen.AC.Lease.target, Block.Compatible, Bool.not_eq_true',
      Bool.not_eq_false] using hg
  have hcompat := clean_gate_output_compatible hsch hji hh hs ht.1 hB
  have hadv : Block.Preceq (S_at p c E rho j v)
      (GridCO.advance (S_at p c E rho j v) B) := by
    unfold GridCO.advance
    split
    · exact block_preceq_refl _
    · next hn =>
      rcases Bool.or_eq_true_iff.mp hcompat with hSC | hBS
      · exact hSC
      · exact (hn hBS).elim
  have hresult : Block.Preceq B (GridCO.advance (S_at p c E rho j v) B) := by
    unfold GridCO.advance
    split
    · assumption
    · exact block_preceq_refl _
  have hj : joinedNow p (clockPre p (storeAt p c E rho j v)
      (SA.gateTime p.toParams s)) = true := by
    rw [clockPre_joined]
    exact fgsa_gate_joined_of_enabled E rho ht
  rcases (fgsaAC_gate_write E rho j s v hj ht.1).effects with hskip | hrun
  · obtain ⟨result, hsaved⟩ := hskip.1
    have hfresh := fgsa_gate_fresh E rho hsch ht.1
    change GridCO.savedGenuine (storeAt p c E rho j v).base s = some result at hsaved
    change GridCO.savedGenuine (storeAt p c E rho j v).base s = none at hfresh
    rw [hfresh] at hsaved
    cases hsaved
  · have hw := (hrun.accept B hraw hguard).1
    change (storeAt p c E rho (j + 1) v).base.stableRecord =
      Gen.AC.normalizeOutput (F_at p c E rho j v)
        (GridCO.advance (storeAt p c E rho j v).base.stableRecord B) at hw
    rw [← S_at_def p c E rho (j + 1) v, ← S_at_def p c E rho j v] at hw
    rw [hw, Gen.AC.normalizeOutput_def]
    have hnest : Block.Preceq (F_at p c E rho j v) (S_at p c E rho j v) :=
      nestOK_stateBefore E rho j v
    rw [ite_eq_left (show Block.preceq (F_at p c E rho j v)
      (GridCO.advance (S_at p c E rho j v) B) = true from block_preceq_trans hnest hadv)]
    exact hresult


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 §8.7 F2.7 S1; bp02 §5.5. The frozen conditional gate-output statement,
from `clean_gateOutput_body` through the first-unfold equation. DC counterpart:
none for this FG-SA statement (the gate result is F-anchored and optional;
spec/fgsa-protocol.tex:2500–2525); INTENTIONAL.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_gateOutput (b₀ : Time) : CleanGateOutputStmt (ΔF := ΔF) p c E rho b₀ := by
  rw [CleanGateOutputStmt_def (ΔF := ΔF)]
  exact clean_gateOutput_body p c E rho b₀

end AvailableChain.FGSA.Run
end
