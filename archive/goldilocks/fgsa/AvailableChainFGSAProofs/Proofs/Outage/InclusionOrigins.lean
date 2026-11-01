module
public import AvailableChainFGSAProofs.Proofs.Outage.ExactProposalReceipts
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingArith

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- The latest gate at an inclusive read is at or after each earlier gate. -/
theorem inclusion_last_gate_label (p : Params) {s : Slot} {t : Time}
    (ht : SA.gateTime p.toParams s ≤ t) :
    ∃ q : Slot, s ≤ q ∧ SA.gateTime p.toParams q ≤ t ∧
      t < SA.gateTime p.toParams (q + 1) := by
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have hn : 0 ≤ t - 6 * p.Δ := by
    rw [arming_gate_eq] at ht
    have hs : 0 ≤ 4 * p.Δ * (s : Int) := by positivity
    linarith
  let q : Slot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  have hq : (q : Int) = (t - 6 * p.Δ) / (4 * p.Δ) :=
    Int.toNat_of_nonneg (Int.ediv_nonneg hn hd.le)
  have hlow := Int.emod_nonneg (t - 6 * p.Δ) (ne_of_gt hd)
  have heq := Int.emod_add_mul_ediv (t - 6 * p.Δ) (4 * p.Δ)
  have hhigh := Int.emod_lt_of_pos (t - 6 * p.Δ) hd
  have hg : SA.gateTime p.toParams q ≤ t := by
    rw [arming_gate_eq, hq]
    nlinarith
  have hnext : t < SA.gateTime p.toParams (q + 1) := by
    rw [arming_gate_eq]
    push_cast
    rw [hq]
    nlinarith
  refine ⟨q, ?_, hg, hnext⟩
  by_contra hs
  have hsq : q + 1 ≤ s := by dsimp only [Slot] at *; omega
  exact (not_lt_of_ge (ht.trans' ((arming_gate_le_iff p _ _).mpr hsq))) hnext

/-- A caught-up reader was joined at its latest gate, even after a wake restart. -/
theorem inclusion_last_gate_reader
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hV : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    {s : Slot} {t : Time} {x : V} (hst : SA.gateTime p.toParams s ≤ t)
    (hhor : t ≤ rho.horizon) (hx : confirmedReader p c E rho x t) :
    ∃ q i, s ≤ q ∧ SA.gateTime p.toParams q ≤ t ∧ enabledGateAt p c E rho i x q := by
  have hs := hV.toScheduleWellFormed
  obtain ⟨q, hsq, hqt, hnext⟩ := inclusion_last_gate_label p hst
  have hq0 : 0 ≤ slotStartZ p (q : Int) := by
    change 0 ≤ 4 * p.Δ * (q : Int)
    have := p.deltaPos
    positivity
  have hMarker : ∀ w, (storeAt p c E rho (timeIdx rho t) x).restartTime = some w →
      w ≤ slotStartZ p (q : Int) := by
    intro w hw
    have hc := hx.2.2
    rw [hw] at hc
    obtain ⟨r, _, hwr, hrt, _⟩ := hc
    have hrq : r ≤ q := by
      by_contra hn
      have hqr : q + 1 ≤ r := by dsimp only [Slot] at *; omega
      have hg := (arming_gate_le_iff p _ _).mpr hqr
      exact (not_lt_of_ge (hg.trans hrt)) hnext
    exact hwr.trans (by
      change 4 * p.Δ * (r : Int) ≤ 4 * p.Δ * (q : Int)
      exact mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr hrq) (by linarith [p.deltaPos]))
  have hRestarts : ∀ (j : Nat) (w : Time),
      rho.events[j]? = some (V2.Event.restart x w) → w ≤ t →
      w ≤ slotStartZ p (q : Int) := by
    intro j w hj hwt
    have hji := (V2.D.Engine.index_lt_read_length_iff hs t hj).mpr hwt
    obtain ⟨u, hu, hwu⟩ := fgsa_restartTime_ge E rho hs hj hji
    exact hwu.trans (hMarker u hu)
  have hAw : E.awake x (SA.gateTime p.toParams q) = true := by
    by_contra hn
    obtain ⟨w, hgw, hwt, hw⟩ := V2.D.Engine.wake_between hqt
      (Bool.eq_false_iff.mpr hn) hx.2.1
    have hw0 : 0 < w := lt_of_le_of_lt (by
      rw [arming_gate_eq]; have := p.deltaPos; positivity) hgw
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp
      (hV.wake_restart x hx.1 w hw0 (hwt.trans hhor) hw)
    have hb := hRestarts j w hj hwt
    have hstart : slotStartZ p (q : Int) ≤ SA.gateTime p.toParams q := by
      change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
      linarith [p.deltaPos]
    exact (not_lt_of_ge hb (hstart.trans_lt hgw)).elim
  have htime : ((4 * q + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams q := by
    rw [arming_gate_eq]
    push_cast
    ring
  obtain ⟨i, hi, _⟩ := fgsa_tick_total E rho hs hDelta x hx.1 (4 * q + 6)
    (htime ▸ hqt.trans hhor) (htime ▸ hAw)
  rw [htime] at hi
  refine ⟨q, i, hsq, hqt, hi, ?_⟩
  have hBound := fgsa_restartTime_bound E rho i x (slotStartZ p (q : Int)) (by
    intro j w hji hj
    have hwt : w ≤ SA.gateTime p.toParams q := by
      by_contra hn
      have hij := V2.D.Engine.eventIndex_lt_of_time_lt hs hi hj (lt_of_not_ge hn)
      omega
    exact hRestarts j w hj (hwt.trans hqt))
  cases hw : (storeAt p c E rho i x).restartTime with
  | none => trivial
  | some w => exact hBound w hw

/-- Clean gate output and scoped public monotonicity close the later-reader origin.
Both suppliers are Clean assembly inputs; no origin is assumed at the later read. -/
theorem inclusion_later_reader_origin
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hV : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    (hGate : ∀ q i x, x ∈ rho.honest → SA.gateTime p.toParams q ≤ rho.horizon →
      enabledGateAt p c E rho i x q →
      ∃ C, gateResultAt p c E rho i = some (some C) ∧
        Block.Preceq C (S_at p c E rho (timeIdx rho (SA.gateTime p.toParams q)) x))
    (hMono : ScopedMono (confirmedReader p c E rho)
      (fun t x => S_at p c E rho (timeIdx rho t) x)
      (fun t => 0 ≤ t ∧ t ≤ rho.horizon))
    {s : Slot} {t : Time} {x : V} (hst : SA.gateTime p.toParams s ≤ t)
    (hhor : t ≤ rho.horizon) (hx : confirmedReader p c E rho x t) :
    ∃ q i B, s ≤ q ∧ SA.gateTime p.toParams q ≤ t ∧
      enabledGateAt p c E rho i x q ∧ gateResultAt p c E rho i = some (some B) ∧
      Block.Preceq B (S_at p c E rho (timeIdx rho t) x) := by
  obtain ⟨q, i, hsq, hqt, hG⟩ := inclusion_last_gate_reader E rho hV hDelta hst hhor hx
  obtain ⟨C, hC, hCS⟩ := hGate q i x hx.1 (hqt.trans hhor) hG
  have hq0 : 0 ≤ SA.gateTime p.toParams q := by
    rw [arming_gate_eq]; have := p.deltaPos; positivity
  refine ⟨q, i, C, hsq, hqt, hG, hC, block_preceq_trans hCS ?_⟩
  exact hMono _ _ x ⟨hq0, hqt.trans hhor⟩ ⟨hq0.trans hqt, hhor⟩ hqt
    (inclusion_confirmedReader_of_enabledGate E rho hV hx.1 hG) hx

end AvailableChain.FGSA.Run
end
