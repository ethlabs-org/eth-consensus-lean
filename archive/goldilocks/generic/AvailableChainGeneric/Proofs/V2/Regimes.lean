module
public import AvailableChainGeneric.Statements.V2.Regimes
public import AvailableChainGeneric.Proofs.V2.Receipt

public section

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine
open AvailableChain.Gen.Pure

namespace AvailableChain.Gen.V2

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}

-- GLY:1567–1568.
omit [DecidableEq V] in
theorem LabelSync.dl_vt_le (E : Generic.Env V) {dl : Time → Time} {vt dt : Time}
    (hsync : ∀ t, dl t ≤ max t vt + E.Δ) (hvd : vt + E.Δ ≤ dt) : dl vt ≤ dt := by
  have hdl : dl vt ≤ vt + E.Δ := by simpa only [max_self] using hsync vt
  exact hdl.trans hvd

-- GLY:1569–1572.
omit [DecidableEq V] in
theorem LabelSync.relayBy (E : Generic.Env V) {dl : Time → Time} {vt dt : Time}
    (hsync : ∀ t, dl t ≤ max t vt + E.Δ) (hvd : vt + E.Δ ≤ dt) :
    ∀ t', t' + E.Δ ≤ dt → dl t' ≤ dt := by
  intro t' ht
  rcases le_total vt t' with h | h
  · have hdl : dl t' ≤ t' + E.Δ := by simpa only [max_eq_left h] using hsync t'
    exact hdl.trans ht
  · have hdl : dl t' ≤ vt + E.Δ := by simpa only [max_eq_right h] using hsync t'
    exact hdl.trans hvd

-- GLY:1575–1578 (E6).
theorem LabelSync.of_cleanCut (E : Generic.Env V) (rho : Run V P) (b₀ vt dt : Time)
    (hHPD : HealthyPrefixDelivery E rho b₀)
    (hvd : vt + E.Δ ≤ dt) (hb : dt ≤ b₀) (hb₀ : b₀ ≤ rho.horizon) :
    LabelSync E rho vt dt := by
  rw [LabelSync_def]
  refine ⟨(fun t => t + E.Δ), b₀, deliveryWithin_of_healthyPrefix b₀ hHPD,
    ?_, ?_, ?_, hvd, hb, hb.trans hb₀⟩
  · exact fun _ _ h => add_le_add h le_rfl
  · exact fun t => lt_add_of_pos_right t E.Δ_pos
  · exact fun t => add_le_add (le_max_left t vt) le_rfl

-- GLY:1579–1582 (E6).
theorem LabelSync.of_recovery (E : Generic.Env V) (rho : Run V P) (vt dt : Time)
    (hPS : PartialSynchrony E rho)
    (hG : E.t_GST ≤ vt) (hvd : vt + E.Δ ≤ dt) (hh : dt ≤ rho.horizon) :
    LabelSync E rho vt dt := by
  rw [LabelSync_def]
  refine ⟨(fun t => max t E.t_GST + E.Δ), rho.horizon,
    deliveryWithin_of_partialSynchrony hPS, ?_, ?_, ?_, hvd, hh, hh⟩
  · exact fun _ _ h => add_le_add (max_le_max h le_rfl) le_rfl
  · exact fun t => (le_max_left t E.t_GST).trans_lt
      (lt_add_of_pos_right (max t E.t_GST) E.Δ_pos)
  · exact fun _ => add_le_add (max_le_max le_rfl hG) le_rfl

-- GLY:1586–1589.
theorem LabelFacts.of_cleanCut (E : Generic.Env V) (rho : Run V P) (b₀ vt dt : Time) (h m : Nat)
    (hHPD : HealthyPrefixDelivery E rho b₀)
    (hvd : vt + E.Δ ≤ dt) (hb : dt ≤ b₀) (hb₀ : b₀ ≤ rho.horizon) (hB : Batch h m) :
    LabelFacts E rho vt dt h m :=
  ⟨LabelSync.of_cleanCut E rho b₀ vt dt hHPD hvd hb hb₀, hB⟩

-- GLY:1590–1593.
theorem LabelFacts.of_recovery (E : Generic.Env V) (rho : Run V P) (vt dt : Time) (h m : Nat)
    (hPS : PartialSynchrony E rho)
    (hG : E.t_GST ≤ vt) (hvd : vt + E.Δ ≤ dt) (hh : dt ≤ rho.horizon) (hB : Batch h m) :
    LabelFacts E rho vt dt h m :=
  ⟨LabelSync.of_recovery E rho vt dt hPS hG hvd hh, hB⟩

end AvailableChain.Gen.V2
