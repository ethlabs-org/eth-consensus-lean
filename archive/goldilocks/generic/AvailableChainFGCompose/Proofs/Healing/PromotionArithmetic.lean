module
public import AvailableChainFGCompose.Statements.Bounds
public import AvailableChainFGCompose.Statements.Channels
public import AvailableChainGeneric.Proofs.V2.Duty.Reads
public import Mathlib.Tactic.Linarith -- shake: keep (arithmetic tactics)
public import Mathlib.Tactic.Ring -- shake: keep (ring tactic)

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}

private theorem p0d3_proposal (T : FGTiming) (hT : FGTimingLaws T) (s : Slot) :
    T.proposal s = 4 * T.delta * (s : Time) := by rw [hT.proposal_eq]; ring

private theorem p0d3_action_period (T : FGTiming) (hT : FGTimingLaws T) (r : Nat) :
    T.action r = (r : Time) * FGCompose.P T + 6 * T.delta := by
  rw [hT.action_eq, hT.gate_eq, hT.proposal_eq]
  unfold FGCompose.P
  push_cast
  ring

private theorem p0d3_kappa_ceiling (T : FGTiming) (hT : FGTimingLaws T)
    (ΔF : Time) (hF : 0 ≤ ΔF) :
    6 * T.delta + ΔF ≤ (kappaF T ΔF : Time) * (4 * T.delta) := by
  have hd : 0 < 4 * T.delta := by linarith [hT.delta_pos]
  have hn : 0 ≤ 6 * T.delta + ΔF + 4 * T.delta - 1 := by
    have hd1 : (1 : Time) ≤ T.delta := hT.delta_pos
    linarith
  delta kappaF
  rw [Int.toNat_of_nonneg (Int.ediv_nonneg hn hd.le)]
  have hhi := Int.lt_ediv_add_one_mul_self (6 * T.delta + ΔF + 4 * T.delta - 1) hd
  nlinarith

private theorem p0d3_kappa_two (T : FGTiming) (hT : FGTimingLaws T)
    (ΔF : Time) (hF : 0 ≤ ΔF) : 2 ≤ kappaF T ΔF := by
  have h := p0d3_kappa_ceiling T hT ΔF hF
  have hd := hT.delta_pos
  by_contra hn
  have hk : (kappaF T ΔF : Time) ≤ 1 := by exact_mod_cast (show kappaF T ΔF ≤ 1 by omega)
  nlinarith

private theorem p0d3_beta_period (T : FGTiming) (hT : FGTimingLaws T)
    (ΔF : Time) (hbound : LivenessBoundW T ΔF) : betaF T ΔF ≤ FGCompose.P T := by
  have hk : (kappaF T ΔF : Time) ≤ T.roundSlots := by exact_mod_cast hbound.kappa_le_R
  delta betaF FGCompose.P
  nlinarith [hT.delta_pos]

private theorem p0d3_delivery_bounds (T : FGTiming) (hT : FGTimingLaws T)
    (ΔF : Time) (r : Nat) (hF : 0 ≤ ΔF) (hbound : LivenessBoundW T ΔF) :
    ActionDeliveryBoundsW T ΔF r := by
  unfold ActionDeliveryBoundsW
  delta carrierTimeW
  rw [p0d3_action_period T hT]
  have hbeta : 6 * T.delta + ΔF ≤ betaF T ΔF := by
    have := p0d3_kappa_ceiling T hT ΔF hF
    delta betaF
    nlinarith
  have hperiod := p0d3_beta_period T hT ΔF hbound
  exact ⟨rfl, by linarith, by nlinarith⟩

private theorem p0d3_period_pos (T : FGTiming) (hT : FGTimingLaws T) : 0 < FGCompose.P T := by
  have hR : (2 : Time) ≤ T.roundSlots := by exact_mod_cast hT.rounds
  change 0 < 4 * (T.roundSlots : Time) * T.delta
  have := hT.delta_pos
  nlinarith

/-- Blueprint 21:1356–1370; plan §3.2 step 2.
DC: INTENTIONAL GUP r2 rounds the gap up by less than one proposal-grid interval. -/
theorem healing_promotion_gap_remainder (T : FGTiming) (hT : FGTimingLaws T) (G : Time) :
    G ≤ Γ T G ∧ Γ T G < G + 4 * T.delta := by
  have hd : 0 < 4 * T.delta := by linarith [hT.delta_pos]
  have hlo := Int.ediv_mul_le (G + 4 * T.delta - 1) (ne_of_gt hd)
  have hhi := Int.lt_ediv_add_one_mul_self (G + 4 * T.delta - 1) hd
  unfold Γ
  constructor <;> nlinarith

private theorem p0d3_grid_upper (T : FGTiming) (hT : FGTimingLaws T) (G z : Time) (s : Slot)
    (hs : T.proposal s ≤ 4 * T.delta * z + G) :
    T.proposal s ≤ 4 * T.delta * z + Γ T G := by
  linarith [(healing_promotion_gap_remainder T hT G).1]

/-- A row held before one deadline remains held before each later deadline. -/
theorem healing_promotion_held_mono
    (R : FGCoreReads Prot n Base Proposal Wire) (E : Generic.Env V)
    (rho : V2.D.Run V Prot) (blockRows : Prot.State → List Wire)
    (hs : V2.D.ScheduleWellFormed E rho)
    (keep : ∀ i j x a, i ≤ j →
      rowHeld R blockRows (V2.D.Run.stateBefore E rho i x) a →
      rowHeld R blockRows (V2.D.Run.stateBefore E rho j x) a)
    {d d' : Time} (hdd : d ≤ d') {x : V} {a : Wire}
    (ha : HeldBefore R E rho blockRows x a d) :
    HeldBefore R E rho blockRows x a d' := by
  change rowHeld R blockRows (V2.D.Run.stateBeforeTime E rho d x) a at ha
  change rowHeld R blockRows (V2.D.Run.stateBeforeTime E rho d' x) a
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hs] at ha
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d' hs]
  apply keep _ _ x a _ ha
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true
    (lt_of_lt_of_le (of_decide_eq_true he) hdd))

omit [DecidableEq V] in
/-- Blueprint 21:1356–1370; plan §3.2 step 2.
DC: INTENTIONAL the full G window fits inside the supplied gate horizon.
The result retains the honest slot; it does not assert proposal emission. -/
theorem healing_promotion_gap (T : FGTiming) (hT : FGTimingLaws T) (I : V2.D.Interface Prot)
    (E : Generic.Env V) (rho : V2.D.Run V Prot) {G : Time}
    (gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
      ∃ s, t < T.proposal s ∧ T.proposal s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s) (r : Nat)
    (hgst : E.t_GST ≤ T.action r)
    (hhor : T.action r + 2 * FGCompose.P T + Γ T G - 4 * T.delta ≤ rho.horizon) :
    (r : Time) * FGCompose.P T + 2 * FGCompose.P T - 4 * T.delta + G ≤ rho.horizon ∧
    ∃ s, (r : Time) * FGCompose.P T + 2 * FGCompose.P T ≤ T.proposal s ∧
      T.proposal s ≤
        T.action r + 2 * FGCompose.P T + Γ T G - 10 * T.delta ∧
      Gen.V2.Duty.HonestSlot rho I s ∧
      T.gate s ≤
        T.action r + 2 * FGCompose.P T + Γ T G - 4 * T.delta := by
  have hrem := (healing_promotion_gap_remainder T hT G).1
  have hR : (2 : Time) ≤ T.roundSlots := by exact_mod_cast hT.rounds
  have hP : 8 * T.delta ≤ FGCompose.P T := by
    change 8 * T.delta ≤ 4 * (T.roundSlots : Time) * T.delta
    nlinarith [hT.delta_pos]
  have ha := p0d3_action_period T hT r
  have hwindow :
      (r : Time) * FGCompose.P T + 2 * FGCompose.P T - 4 * T.delta + G ≤ rho.horizon := by
    linarith [hT.delta_pos]
  have hstart : E.t_GST ≤ (r : Time) * FGCompose.P T + 2 * FGCompose.P T - 4 * T.delta := by
    linarith [hT.delta_pos]
  obtain ⟨s, hlo, hhi, hs⟩ := gap _ hstart hwindow
  have hgrid : (r : Time) * FGCompose.P T + 2 * FGCompose.P T - 4 * T.delta =
      4 * T.delta * ((r : Time) * T.roundSlots + 2 * T.roundSlots - 1) := by
    change (r : Time) * (4 * (T.roundSlots : Time) * T.delta) +
      2 * (4 * (T.roundSlots : Time) * T.delta) - 4 * T.delta = _
    ring
  have hup := p0d3_grid_upper T hT G ((r : Time) * T.roundSlots + 2 * T.roundSlots - 1) s
    (by rw [← hgrid]; exact hhi)
  rw [← hgrid] at hup
  have hlow : (r : Time) * FGCompose.P T + 2 * FGCompose.P T ≤ T.proposal s := by
    rw [hgrid] at hlo
    rw [p0d3_proposal T hT] at hlo
    change 4 * T.delta * ((r : Time) * T.roundSlots + 2 * T.roundSlots - 1) <
      4 * T.delta * (s : Time) at hlo
    have hc : (r : Time) * T.roundSlots + 2 * T.roundSlots ≤ s := by
      have := hT.delta_pos
      have : (r : Time) * T.roundSlots + 2 * T.roundSlots - 1 < s := by nlinarith
      linarith only [Int.add_one_le_iff.mpr this]
    rw [p0d3_proposal T hT]
    change (r : Time) * (4 * (T.roundSlots : Time) * T.delta) +
      2 * (4 * (T.roundSlots : Time) * T.delta) ≤ 4 * T.delta * (s : Time)
    nlinarith [hT.delta_pos]
  refine ⟨hwindow, s, hlow, by linarith, hs, ?_⟩
  rw [hT.gate_eq]
  linarith

omit [DecidableEq V] in
/-- Blueprint 21:1371–1384; plan §3.2 step 3.
DC: SAME the earlier row's deadline is bounded without a later row selection. -/
theorem healing_promotion_row_deadline (T : FGTiming) (hT : FGTimingLaws T) (E : Generic.Env V)
    {ΔF : Time} (hF : 0 ≤ ΔF) (hbound : LivenessBoundW T ΔF)
    {r rSent : Nat} (hr : rSent ≤ r) (hgst : E.t_GST ≤ T.action r)
    {s : Slot} (hs : carrierTimeW T ΔF r ≤ T.proposal s) :
    max (T.action rSent) E.t_GST + ΔF ≤ T.action r + ΔF ∧
    T.action r + ΔF ≤ carrierTimeW T ΔF r ∧
    carrierTimeW T ΔF r ≤ ((r : Time) + 1) * FGCompose.P T ∧
    max (T.action rSent) E.t_GST + ΔF ≤ T.proposal s ∧
    max (T.action r) E.t_GST + ΔF ≤ T.proposal s ∧
    r * T.roundSlots + 2 ≤ s := by
  have hcast : (rSent : Time) ≤ r := by exact_mod_cast hr
  have htime : T.action rSent ≤ T.action r := by
    rw [p0d3_action_period T hT, p0d3_action_period T hT]
    have := p0d3_period_pos T hT
    nlinarith
  have hb := p0d3_delivery_bounds T hT ΔF r hF hbound
  change _ ∧ _ ∧ _ at hb
  have h1 : max (T.action rSent) E.t_GST + ΔF ≤ T.action r + ΔF := by
    have := max_le htime hgst
    linarith
  have hdeadline := hb.2.1.trans hs
  have hk : (2 : Time) ≤ kappaF T ΔF := by exact_mod_cast p0d3_kappa_two T hT ΔF hF
  have hcast : ((r * T.roundSlots + 2 : Nat) : Time) ≤ s := by
    delta carrierTimeW betaF at hs
    rw [p0d3_proposal T hT] at hs
    change (r : Time) * (4 * (T.roundSlots : Time) * T.delta) +
      4 * (kappaF T ΔF : Time) * T.delta ≤ 4 * T.delta * (s : Time) at hs
    push_cast
    nlinarith [hT.delta_pos]
  exact ⟨h1, hb.2.1, hb.2.2, h1.trans hdeadline,
    by rw [max_eq_left hgst]; exact hdeadline, by exact_mod_cast hcast⟩

omit [DecidableEq V] in
/-- The H.9(b) trigger keeps the earlier strict deadline chain. -/
theorem healing_promotion_row_deadline_strict (T : FGTiming) (hT : FGTimingLaws T)
    (E : Generic.Env V)
    {ΔF : Time} (hF : 0 ≤ ΔF) (hbound : LivenessBoundW T ΔF)
    {r rSent : Nat} (hr : rSent ≤ r) (hgst : E.t_GST ≤ T.action r)
    {s : Slot} (hs : (r : Time) * FGCompose.P T + 2 * FGCompose.P T ≤ T.proposal s) :
    max (T.action rSent) E.t_GST + ΔF ≤ T.action r + ΔF ∧
    T.action r + ΔF ≤ carrierTimeW T ΔF r ∧
    carrierTimeW T ΔF r ≤ ((r : Time) + 1) * FGCompose.P T ∧
    ((r : Time) + 1) * FGCompose.P T < T.proposal s := by
  have hc : carrierTimeW T ΔF r ≤ T.proposal s := by
    delta carrierTimeW
    have := p0d3_beta_period T hT ΔF hbound
    have := p0d3_period_pos T hT
    linarith
  obtain ⟨h1, h2, h3, _⟩ := healing_promotion_row_deadline T hT E hF hbound hr hgst hc
  exact ⟨h1, h2, h3, by have := p0d3_period_pos T hT; linarith⟩

/-- Blueprint 21:1371–1384; plan §3.2 step 3.
DC: SAME strict receipt at max(send,GST)+ΔF, for the original signed row.
Assembly supplies rowsReceipt with RowService.fgsa_tRowsReceipt. -/
theorem healing_promotion_row_receipt (T : FGTiming) (hT : FGTimingLaws T)
    (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
    (E : Generic.Env V) (rho : V2.D.Run V Prot) (blockRows : Prot.State → List Wire)
    (hsched : V2.D.ScheduleWellFormed E rho)
    (keep : ∀ i j x a, i ≤ j →
      rowHeld R blockRows (V2.D.Run.stateBefore E rho i x) a →
      rowHeld R blockRows (V2.D.Run.stateBefore E rho j x) a)
    {ΔF : Time} (hF : 0 ≤ ΔF) (hbound : LivenessBoundW T ΔF)
    (rowsReceipt : ∀ j y r (a : Wire),
      HonestRowAt S E rho T j y r a →
      max (T.action r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest,
        HeldBefore R E rho blockRows x a (max (T.action r) E.t_GST + ΔF))
    {r j rSent : Nat} {y : V} {a : Wire}
    (hr : rSent ≤ r) (ha : HonestRowAt S E rho T j y rSent a)
    (hgst : E.t_GST ≤ T.action r) {s : Slot}
    (hs : carrierTimeW T ΔF r ≤ T.proposal s)
    (hhor : T.proposal s ≤ rho.horizon) :
    max (T.action rSent) E.t_GST + ΔF ≤ T.proposal s ∧
    max (T.action r) E.t_GST + ΔF ≤ T.proposal s ∧
    r * T.roundSlots + 2 ≤ s ∧
    ∀ x ∈ rho.honest,
      HeldBefore R E rho blockRows x a (max (T.action rSent) E.t_GST + ΔF) ∧
      HeldBefore R E rho blockRows x a (T.action r + ΔF) := by
  obtain ⟨h1, _, _, hd, hbatch, hslot⟩ :=
    healing_promotion_row_deadline T hT E hF hbound hr hgst hs
  refine ⟨hd, hbatch, hslot, ?_⟩
  intro x hx
  have hheld := rowsReceipt j y rSent a ha (hd.trans hhor) x hx
  exact ⟨hheld, healing_promotion_held_mono R E rho blockRows hsched keep h1 hheld⟩

/-- The H.9(b) trigger keeps the strict deadline and the original signed row. -/
theorem healing_promotion_row_receipt_strict (T : FGTiming) (hT : FGTimingLaws T)
    (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
    (E : Generic.Env V) (rho : V2.D.Run V Prot) (blockRows : Prot.State → List Wire)
    (hsched : V2.D.ScheduleWellFormed E rho)
    (keep : ∀ i j x a, i ≤ j →
      rowHeld R blockRows (V2.D.Run.stateBefore E rho i x) a →
      rowHeld R blockRows (V2.D.Run.stateBefore E rho j x) a)
    {ΔF : Time} (hF : 0 ≤ ΔF) (hbound : LivenessBoundW T ΔF)
    (rowsReceipt : ∀ j y r (a : Wire),
      HonestRowAt S E rho T j y r a →
      max (T.action r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest,
        HeldBefore R E rho blockRows x a (max (T.action r) E.t_GST + ΔF))
    {r j rSent : Nat} {y : V} {a : Wire}
    (hr : rSent ≤ r) (ha : HonestRowAt S E rho T j y rSent a)
    (hgst : E.t_GST ≤ T.action r) {s : Slot}
    (hs : (r : Time) * FGCompose.P T + 2 * FGCompose.P T ≤ T.proposal s)
    (hhor : T.proposal s ≤ rho.horizon) :
    max (T.action rSent) E.t_GST + ΔF < T.proposal s ∧
    ∀ x ∈ rho.honest,
      HeldBefore R E rho blockRows x a (max (T.action rSent) E.t_GST + ΔF) ∧
      HeldBefore R E rho blockRows x a (T.action r + ΔF) := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    healing_promotion_row_deadline_strict T hT E hF hbound hr hgst hs
  have hd := lt_of_le_of_lt (h1.trans (h2.trans h3)) h4
  obtain ⟨_, _, _, hheld⟩ :=
    healing_promotion_row_receipt T hT R S E rho blockRows hsched keep hF hbound
      rowsReceipt hr ha hgst
      ((h3.trans h4.le)) hhor
  exact ⟨hd, hheld⟩

/-- Blueprint 21:1385–1410; plan §3.2 steps 4–5.
DC: SAME two full periods give the maturity required by K-HEIGHT. -/
theorem healing_promotion_maturity (T : FGTiming) (hT : FGTimingLaws T)
    {δt : Nat} (hδ : δt = 2 * T.roundSlots)
    {s : Nat} {U : FGBlock (Fin n)}
    (hs : T.proposal U.slot + 2 * FGCompose.P T ≤ T.proposal s) :
    U.slot + δt ≤ s := by
  have hcast : ((U.slot + 2 * T.roundSlots : Nat) : Time) ≤ s := by
    push_cast
    rw [p0d3_proposal T hT, p0d3_proposal T hT] at hs
    change 4 * T.delta * (U.slot : Time) +
      2 * (4 * (T.roundSlots : Time) * T.delta) ≤ 4 * T.delta * (s : Time) at hs
    have := hT.delta_pos
    nlinarith
  rw [hδ]
  exact_mod_cast hcast

/-- The entry-slot bound supplies the old action-based maturity case. -/
theorem healing_promotion_maturity_of_action (T : FGTiming) (hT : FGTimingLaws T)
    {δt : Nat} (hδ : δt = 2 * T.roundSlots)
    {r s : Nat} {U : FGBlock (Fin n)} (hU : U.slot ≤ r * T.roundSlots)
    (hs : (r : Time) * FGCompose.P T + 2 * FGCompose.P T ≤ T.proposal s) :
    U.slot + δt ≤ s := by
  apply healing_promotion_maturity T hT hδ
  have hcast : (U.slot : Time) ≤ (r : Time) * T.roundSlots := by exact_mod_cast hU
  rw [p0d3_proposal T hT]
  change 4 * T.delta * (U.slot : Time) + 2 * FGCompose.P T ≤ _
  rw [p0d3_proposal T hT] at hs
  change (r : Time) * (4 * (T.roundSlots : Time) * T.delta) +
    2 * (4 * (T.roundSlots : Time) * T.delta) ≤ _ at hs
  change _ + 2 * (4 * (T.roundSlots : Time) * T.delta) ≤ _
  rw [p0d3_proposal T hT]
  nlinarith [hT.delta_pos]

omit [DecidableEq V] in
/-- Blueprint 21:1592–1638; plan §3.2 step 7.
DC: INTENTIONAL the age-sensitive trigger is on the proposal grid.
This is the deadline component, not an acceptance or service producer. -/
theorem healing_promotion_age_gap (T : FGTiming) (hT : FGTimingLaws T) (I : V2.D.Interface Prot)
    (E : Generic.Env V) (rho : V2.D.Run V Prot) {G : Time}
    (gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
      ∃ s, t < T.proposal s ∧ T.proposal s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s)
    {ΔF : Time} (hF : 0 ≤ ΔF) (r : Nat) (q : Slot)
    (hgst : E.t_GST ≤ (r : Time) * FGCompose.P T)
    (hwin : max ((r : Time) * FGCompose.P T + betaF T ΔF - 4 * T.delta)
      (T.proposal q + 2 * FGCompose.P T - 4 * T.delta) + G ≤ rho.horizon) :
    let U_F := max ((r : Time) * FGCompose.P T + betaF T ΔF - 4 * T.delta)
      (T.proposal q + 2 * FGCompose.P T - 4 * T.delta)
    U_F + G ≤ rho.horizon ∧
    ∃ s, U_F < T.proposal s ∧
      T.proposal s ≤ U_F + Γ T G ∧
      Gen.V2.Duty.HonestSlot rho I s ∧
      T.proposal s + T.delta ≤
        max (T.action r + Γ T G - T.delta + epsF T ΔF)
          (T.proposal q + 2 * FGCompose.P T + Γ T G - 3 * T.delta) ∧
      T.gate s ≤
        max (T.action r + Γ T G + 4 * T.delta + epsF T ΔF)
          (T.proposal q + 2 * FGCompose.P T + Γ T G + 2 * T.delta) := by
  let a := (r : Time) * FGCompose.P T + betaF T ΔF - 4 * T.delta
  let b := T.proposal q + 2 * FGCompose.P T - 4 * T.delta
  let U_F := max a b
  have hk : (2 : Time) ≤ kappaF T ΔF := by exact_mod_cast p0d3_kappa_two T hT ΔF hF
  have ha : E.t_GST ≤ a := by
    dsimp only [a]
    delta betaF
    nlinarith [hT.delta_pos]
  have hstart : E.t_GST ≤ U_F := ha.trans (le_max_left a b)
  have hgate : max (T.action r + Γ T G + 4 * T.delta + epsF T ΔF)
      (T.proposal q + 2 * FGCompose.P T + Γ T G + 2 * T.delta) =
      U_F + Γ T G + 6 * T.delta := by
    rw [p0d3_action_period T hT]
    delta epsF
    change max _ _ = max a b + _ + _
    rw [← max_add_add_right, ← max_add_add_right]
    congr 1 <;> dsimp only [a, b] <;> ring
  have hterminal : max (T.action r + Γ T G - T.delta + epsF T ΔF)
      (T.proposal q + 2 * FGCompose.P T + Γ T G - 3 * T.delta) =
      U_F + Γ T G + T.delta := by
    rw [p0d3_action_period T hT]
    delta epsF
    change max _ _ = max a b + _ + _
    rw [← max_add_add_right, ← max_add_add_right]
    congr 1 <;> dsimp only [a, b] <;> ring
  have hwindow : U_F + G ≤ rho.horizon := hwin
  obtain ⟨s, hlo, hhi, hs⟩ := gap U_F hstart hwindow
  have hgrid : U_F = 4 * T.delta * max
      ((r : Time) * T.roundSlots + kappaF T ΔF - 1) ((q : Time) + 2 * T.roundSlots - 1) := by
    dsimp only [U_F, a, b]
    rw [mul_max_of_nonneg _ _ (by linarith [hT.delta_pos])]
    congr 1
    · change (r : Time) * (4 * (T.roundSlots : Time) * T.delta) + betaF T ΔF - 4 * T.delta = _
      delta betaF
      ring
    · rw [p0d3_proposal T hT]
      change 4 * T.delta * (q : Time) + 2 * (4 * (T.roundSlots : Time) * T.delta) - 4 * T.delta = _
      ring
  have hup := p0d3_grid_upper T hT G _ s (by rw [← hgrid]; exact hhi)
  rw [← hgrid] at hup
  refine ⟨hwindow, s, hlo, hup, hs, ?_, ?_⟩
  · rw [hterminal]; linarith
  · rw [hgate]
    rw [hT.gate_eq]
    linarith

end AvailableChain.FGCompose
end
