module
public import AvailableChainFGCompose.Statements.Attempt
public import AvailableChainFGCompose.Proofs.Healing.AttemptSettle
public import AvailableChainFGCompose.Proofs.Healing.AttemptStop
public import AvailableChainFGCompose.Proofs.Healing.CommonEntry
public import AvailableChainFGCompose.Proofs.Healing.PromotionArithmetic

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot)
variable (O : FGObservationReads R) (T : FGTiming) (I : V2.D.Interface Prot)
variable (A : FGAttemptGateReads Prot) (pair : Wire → NamedHeightPair) (Jst : Time)

variable (Ef : Electorate (Fin n)) (obs : FGObservationLaws R O)
variable (cert : FGCertificateLaws Ef O.height O.finality)
variable (inv : ∀ i x, FGStoreInvariant O.height O.finality (R.core (rho.stateBefore E i x)).fg)
variable (justif : FGJustificationLaws O.height)
variable (keep : ∀ i j, i ≤ j → ∀ x, TFAt R E rho i x ⊆ TFAt R E rho j x)
variable (hT : FGTimingLaws T) (coreLaws : FGCoreLaws R)
variable (erasePreceq : ∀ {B C}, FGBlock.Preceq B C → Block.Preceq (R.erase B) (R.erase C))
variable (joined : Prot.State → Bool) (receipt : Block → Time → V → Prop)
variable (hs : V2.D.ScheduleWellFormed E rho) (mono : FGRunOrderLaws E rho R)
variable (hdelta : E.Δ = T.delta) (gst : E.t_GST ≤ Jst)
variable (awake : ∀ y ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon → E.awake y t = true)
variable (joinedTick : ∀ iy y t, y ∈ rho.honest → rho.events[iy]? = some (.tick y t) →
  t ≤ rho.horizon → E.t_GST ≤ slotStartZ T (((slotAt T t : Slot) : Int) - 1) →
  joined (Prot.clock (rho.stateBefore E iy y) t) = true)
variable (readyCut : ∀ t, Jst ≤ t →
  E.t_GST ≤ slotStartZ T (((slotAt T t : Slot) : Int) - 1))
variable (heldServices : ∀ i (ev : V2.Event V Prot.Object) m,
  rho.events[i]? = some ev → Jst ≤ ev.time → 1 ≤ m →
  frontierAtIdx R E rho (i + 1) = m → ev.time + T.delta ≤ rho.horizon →
  PhaseWitnessReceiptScope R E rho O joined receipt (i + 1) m (ev.time + T.delta))
variable (receiptHeld : ∀ W d y, y ∈ rho.honest → receipt (R.erase W) d y →
  W ∈ (R.core (rho.stateBeforeTime E d y)).fg.TF)

variable (crossing : RXing R E rho O)
variable (G repairAllowance : Time) (leaseSlots : Nat) (leaseLarge : 2 ≤ leaseSlots)
variable (allowanceNonneg : 0 ≤ repairAllowance) (gapPos : 4 * T.delta ≤ G)
variable (repair : AttemptRepairService R E rho O T I A Jst G repairAllowance leaseSlots)
variable (opening : AttemptOpeningService R S E rho O T I A pair Jst)
variable (nextOpening : AttemptNextOpeningService R E rho O T I A Jst)
variable (proposalFloor : AttemptProposalFloor R E rho O T I Jst)
variable (gateCopy : AttemptGateCopy R E rho O T I A Jst)
variable (exactCarrier : ∀ q Q, HonestProposal E rho I q Q → Jst ≤ T.proposal q →
  AttemptExactService R E rho T I A q Q → T.gate q ≤ rho.horizon →
  ∃ Qfg, R.erase Qfg = Q)
variable (honestNonempty : rho.honest.Nonempty)
variable [Fintype V]
variable (faultQ : Gen.Pure.FaultQ n (Gen.V2.Duty.faulty rho).card)
variable (honestQuorum : Ef.q ≤ Ef.weightOf (Finset.univ.filter (fun i => safetyHolder S rho i
      ∈ rho.honest)))
variable (renewed : Gen.Pure.FaultQ n (Gen.V2.Duty.faulty rho).card →
  Ef.q ≤ Ef.weightOf (Finset.univ.filter (fun i => safetyHolder S rho i ∈ rho.honest)) →
  AttemptRenewedPromotion R S E rho O T I A pair Jst G)
variable (terminal : Gen.Pure.FaultQ n (Gen.V2.Duty.faulty rho).card →
  Ef.q ≤ Ef.weightOf (Finset.univ.filter (fun i => safetyHolder S rho i ∈ rho.honest)) →
  AttemptTerminalPromotion R S E rho O T I pair Jst G)

omit [DecidableEq V] [Fintype V] in
private theorem p0d4_period (hT : FGTimingLaws T) : 8 * T.delta ≤ FGCompose.P T := by
  have hR : (2 : Time) ≤ T.roundSlots := by exact_mod_cast hT.rounds
  change 8 * T.delta ≤ 4 * (T.roundSlots : Time) * T.delta
  nlinarith [hT.delta_pos]

omit [DecidableEq V] [Fintype V] in
include hT in
private theorem p0d4_action (r : Nat) : T.action r = (r : Time) * FGCompose.P T + 6 * T.delta := by
  rw [hT.action_eq, hT.gate_eq, hT.proposal_eq]
  push_cast
  change 4 * ((r : Time) * T.roundSlots) * T.delta + 6 * T.delta =
    (r : Time) * (4 * (T.roundSlots : Time) * T.delta) + 6 * T.delta
  ring

omit [DecidableEq V] [Fintype V] in
include hT in
private theorem p0d4_grid (u : Time) :
    ∃ β, u < T.proposal β ∧ ∀ b, u < T.proposal b → β ≤ b := by
  have hex : ∃ β, u < T.proposal β := by
    refine ⟨u.toNat + 1, ?_⟩
    rw [hT.proposal_eq]
    have hu : u ≤ (u.toNat : Time) := Int.self_le_toNat u
    have hn : (0 : Time) ≤ u.toNat := Int.natCast_nonneg _
    have hd0 : (0 : Time) < T.delta := hT.delta_pos
    have hd : (1 : Time) ≤ T.delta := Int.add_one_le_iff.mpr hd0
    push_cast
    nlinarith
  exact ⟨Nat.find hex, Nat.find_spec hex, fun b hb => Nat.find_min' hex hb⟩

omit [DecidableEq V] [Fintype V] in
include hT in
private theorem p0d4_first_time (q r : Nat) (hle : q ≤ r * T.roundSlots)
    (hfirst : ∀ r', q ≤ r' * T.roundSlots → r ≤ r') :
    0 ≤ T.action r - T.gate q ∧ T.action r - T.gate q ≤ FGCompose.P T - 4 * T.delta := by
  have hb : r * T.roundSlots < q + T.roundSlots := by
    by_cases hz : r = 0
    · subst r; have := hT.rounds; omega
    · have hn : ¬ q ≤ (r - 1) * T.roundSlots := by
        intro h; have := hfirst (r - 1) h; omega
      have he : r * T.roundSlots = (r - 1) * T.roundSlots + T.roundSlots := by
        rw [← Nat.succ_mul]; congr 1; omega
      omega
  have haI : (q : Time) ≤ ((r * T.roundSlots : Nat) : Time) := by exact_mod_cast hle
  have hbI : ((r * T.roundSlots : Nat) : Time) < (q : Time) + (T.roundSlots : Time) := by
    exact_mod_cast hb
  have hbI' : ((r * T.roundSlots : Nat) : Time) ≤ (q : Time) + (T.roundSlots : Time) - 1 := by
    have hb1 := Int.add_one_le_iff.mpr hbI
    nlinarith only [hb1]
  rw [hT.action_eq, hT.gate_eq, hT.gate_eq, hT.proposal_eq, hT.proposal_eq]
  change 0 ≤ 4 * ((r * T.roundSlots : Nat) : Time) * T.delta + 6 * T.delta -
    (4 * (q : Time) * T.delta + 6 * T.delta) ∧
    4 * ((r * T.roundSlots : Nat) : Time) * T.delta + 6 * T.delta -
    (4 * (q : Time) * T.delta + 6 * T.delta) ≤ 4 * (T.roundSlots : Time) * T.delta - 4 * T.delta
  constructor <;> nlinarith [hT.delta_pos]

omit [DecidableEq V] [Fintype V] in
private theorem p0d4_time_mono {u v : Time} (huv : u ≤ v) : timeIdx rho u ≤ timeIdx rho v := by
  rw [timeIdx_def, timeIdx_def]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true ((of_decide_eq_true he).trans huv))

omit [Fintype V] in
private theorem p0d4_phase_restrict {u v w : Time} {m : Nat}
    {J : Option (FGBlock (Fin n))} {contested : Bool}
    (hp : PhaseInterval R E rho O u v m J contested) (hu : u ≤ w) (hw : w ≤ v) :
    PhaseInterval R E rho O u w m J contested := by
  refine ⟨hu, hw.trans hp.2.1, hp.2.2.1, ?_⟩
  intro i x hui hiw hx
  exact hp.2.2.2 i x hui (hiw.trans (p0d4_time_mono rho hw)) hx

omit [DecidableEq V] [Fintype V] in
include hs in
private theorem p0d4_time_le {i : Nat} {ev : V2.Event V Prot.Object}
    (hi : rho.events[i]? = some ev) {D : Time} (hD : i < timeIdx rho D) : ev.time ≤ D := by
  have he : rho.events.filter (fun e => decide (e.time < D + 1)) =
      rho.events.filter (fun e => decide (e.time ≤ D)) :=
    List.filter_congr (fun e _ => by simp only [Int.lt_add_one_iff])
  have hiD : i < rho.idxBefore (D + 1) := by
    rw [V2.D.Run.idxBefore_def, he]
    exact hD
  exact Int.lt_add_one_iff.mp ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi (D + 1)).mp hiD)

omit [Fintype V] in
include hs in
private theorem p0d4_quiet {k : AttemptKey} {ev : V2.Event V Prot.Object} {budget : Time}
    (hstart : rho.events[k.start]? = some ev)
    (hstop : ¬ AttemptEndsBy R S E rho O T pair k budget) :
    ∀ j, k.start < j → j < timeIdx rho (ev.time + budget) →
      ¬ EffectiveEvent R E rho O j := by
  intro j hj hcut
  have hjlen : j < rho.events.length := hcut.trans_le (List.length_filter_le _ _)
  have hev := List.getElem?_eq_getElem hjlen
  exact healing_attempt_no_event R S E rho O T pair hstart hstop hj hev
    (p0d4_time_le E rho hs hev hcut)

omit [Fintype V] in
include hT in
private theorem p0d4_row_high {k : AttemptKey} {ev : V2.Event V Prot.Object}
    {budget : Time} {r : Nat} {Q : Block}
    (hvalid : AttemptValid R S E rho O T I A pair Jst k)
    (hstart : rho.events[k.start]? = some ev) (htask : k.task = .firstRow)
    (hr : T.action r ≤ ev.time + budget)
    (hcovered : OpeningCovered R S E rho O.height T pair r Q)
    {x : V} {K : FGBlock (Fin n)} (hx : x ∈ rho.honest)
    (hK : actionSourceFG R E rho T x r = some (some K))
    (hh : (O.height K).h = k.frontier) : AttemptEndsBy R S E rho O T pair k budget := by
  obtain ⟨L, nd, j, rSent, a, _hnd, hL, _hmem, _hQ, hrr, ha, hn⟩ := hcovered x hx
  have he : L = K := Option.some.inj (Option.some.inj (hL.symm.trans hK))
  subst L
  rw [hh] at hn
  have hj : k.start < j := by
    by_contra h
    obtain ⟨_, _, _, _, _, _, _, _, hnone⟩ := hvalid
    exact hnone htask j x rSent a k.frontier _ (Nat.le_of_not_gt h) ha hn rfl
  have hsend : T.action rSent ≤ T.action r := by
    rw [p0d4_action T hT, p0d4_action T hT]
    have hrr' : (rSent : Time) ≤ r := by exact_mod_cast hrr
    have hP := p0d4_period T hT
    nlinarith [hT.delta_pos]
  exact healing_attempt_ends_of_row R S E rho O T pair hstart hj ha.2.1
    (hsend.trans hr) htask ha hn

omit [Fintype V] in
include hT honestNonempty in
private theorem p0d4_row_covered {k : AttemptKey} {ev : V2.Event V Prot.Object}
    {budget : Time} {r : Nat} {Q : Block}
    (hvalid : AttemptValid R S E rho O T I A pair Jst k)
    (hstart : rho.events[k.start]? = some ev) (htask : k.task = .firstRow)
    (hr : T.action r ≤ ev.time + budget)
    (hcovered : OpeningCovered R S E rho O.height T pair r Q)
    (hentry : OpeningEntry R E rho O.height T r k.frontier) :
    AttemptEndsBy R S E rho O T pair k budget := by
  obtain ⟨x, hx⟩ := honestNonempty
  obtain ⟨K, nd, j, rSent, a, hnd, hK, _⟩ := hcovered x hx
  obtain ⟨e, he⟩ := hentry
  exact p0d4_row_high R S E rho O T I A pair Jst hT hvalid hstart htask hr hcovered hx hK
    (he x K hx hK).1

include obs cert inv in
omit [Fintype V] in
include proposalFloor gateCopy in
private theorem p0d4_proposal_heights {u D : Time} {m q : Nat}
    {J : Option (FGBlock (Fin n))} {contested : Bool} {Q : Block} {Qfg : FGBlock (Fin n)}
    (hready : Jst ≤ u) (hp : PhaseInterval R E rho O u D m J contested)
    (hu : u ≤ T.proposal q) (hgate : T.gate q ≤ D) (hQ : HonestProposal E rho I q Q)
    (heq : R.erase Qfg = Q) (hexact : AttemptExactService R E rho T I A q Q) :
    (if contested then m else m - 1) ≤ (O.height Qfg).h ∧ (O.height Qfg).h ≤ m := by
  have hlo := proposalFloor u D m J contested q Q Qfg hready hp hu hgate hQ heq
  have hparent : FGBlock.Preceq Qfg.parent Qfg := by
    cases Qfg with
    | genesis => exact KitFG.preceq_refl _
    | node P s root body rows => exact KitFG.preceq_parent_node _ _ _ _ _
  obtain ⟨i, x, hui, hiD, hx, hheld⟩ :=
    gateCopy u D m J contested q Q Qfg hready hp hu hgate hQ heq hexact
  have hcap := (hp.2.2.2 i x hui hiD hx).1
  have hh := healing_phase_height_le
    (R := R)
    (E := E)
    (rho := rho)
    (O := O)
    (inv := inv) hheld
  rw [obs.controls_eq] at hcap
  change (R.core (rho.stateBefore E i x)).fg.h_max = m at hcap
  exact ⟨hlo.trans (cert.height.h_mono hparent), hcap ▸ hh⟩

include obs cert inv justif keep hT coreLaws erasePreceq hs mono hdelta gst awake
  joinedTick readyCut heldServices receiptHeld allowanceNonneg gapPos
  repair opening proposalFloor gateCopy exactCarrier leaseLarge in
omit [Fintype V] in
private theorem p0d4_repair_opening (crossing : RXing R E rho O)
    {k : AttemptKey} {ev : V2.Event V Prot.Object} {budget : Time}
    (hvalid : AttemptValid R S E rho O T I A pair Jst k)
    (hstart : rho.events[k.start]? = some ev)
    (hstop : ¬ AttemptEndsBy R S E rho O T pair k budget)
    (hhor : ev.time + budget ≤ rho.horizon)
    (hbudget : ev.time + 3 * T.delta + repairAllowance +
      (FGCompose.P T - 4 * T.delta) ≤ ev.time + budget) :
    ∃ (β q : Nat) (Q : Block) (Qfg : FGBlock (Fin n)) (r : Nat)
      (root : Option (FGBlock (Fin n))) (contested : Bool),
      let u := ev.time + 3 * T.delta
      PhaseInterval R E rho O u (ev.time + budget) k.frontier root contested ∧
      (contested = true ↔ k.phase = .contest) ∧ Jst ≤ u ∧ u ≤ T.proposal q ∧
      T.proposal (β + 2 * leaseSlots - 1) < T.proposal q ∧
      T.gate q ≤ u + repairAllowance ∧ HonestProposal E rho I q Q ∧
      AttemptExactService R E rho T I A q Q ∧ R.erase Qfg = Q ∧
      (if contested then k.frontier else k.frontier - 1) ≤ (O.height Qfg).h ∧
      (O.height Qfg).h ≤ k.frontier ∧ q ≤ r * T.roundSlots ∧
      T.action r ≤ u + repairAllowance + (FGCompose.P T - 4 * T.delta) ∧
      OpeningCovered R S E rho O.height T pair r Q ∧
      (∀ v, PhaseInterval R E rho O u v k.frontier root contested →
        AttemptRepairAfter R E rho T I A (β + 2 * leaseSlots - 1) v) := by
  have hP := p0d4_period T hT
  have huD : ev.time + 3 * T.delta ≤ ev.time + budget := by
    linarith [hT.delta_pos]
  obtain ⟨J, hp, _hframe⟩ := healing_attempt_settle_start R S E rho O T I A pair Jst Ef
    obs cert inv justif keep hT coreLaws erasePreceq joined receipt hs mono hdelta gst awake
    joinedTick readyCut heldServices receiptHeld crossing hvalid hstart huD hhor
    (p0d4_quiet R S E rho O T pair hs hstart hstop)
  let u := ev.time + 3 * T.delta
  have hsettled : ∃ (root : Option (FGBlock (Fin n))) (contested : Bool),
      PhaseInterval R E rho O u (ev.time + budget) k.frontier root contested ∧
      (contested = true ↔ k.phase = .contest) := by
    refine ⟨_, _, hp, ?_⟩
    cases k.phase with
    | gap => constructor <;> intro h <;> cases h
    | topJ => constructor <;> intro h <;> cases h
    | contest => exact ⟨fun _ => rfl, fun _ => rfl⟩
  obtain ⟨root, contested, hp, hcont⟩ := hsettled
  have hgst0 : Jst ≤ ev.time := by
    obtain ⟨ev0, hi0, hgst0, _⟩ := hvalid
    have he : ev0 = ev := Option.some.inj (hi0.symm.trans hstart)
    exact he ▸ hgst0
  have hgst : Jst ≤ u := by dsimp only [u]; linarith [hT.delta_pos]
  obtain ⟨β, hβ, hmin⟩ := p0d4_grid T hT u
  have hafter := (repair gapPos u _ _ root contested hgst hp β hβ hmin).1
  obtain ⟨q, Q, hq, hgate, hQ, hexact⟩ :=
    (repair gapPos u _ _ root contested hgst hp β hβ hmin).2
      (by dsimp only [u]; linarith [hT.delta_pos])
  have hβl : β ≤ β + 2 * leaseSlots - 1 := by
    have hk : 1 ≤ 2 * leaseSlots :=
      (by decide : 1 ≤ 4).trans (Nat.mul_le_mul_left 2 leaseLarge)
    exact Nat.le_sub_of_add_le (Nat.add_le_add_left hk β)
  have hβI : (β : Time) ≤ ((β + 2 * leaseSlots - 1 : Nat) : Time) := by
    exact_mod_cast hβl
  have hβt : T.proposal β ≤ T.proposal (β + 2 * leaseSlots - 1) := by
    rw [hT.proposal_eq, hT.proposal_eq]
    nlinarith [hT.delta_pos]
  have huq := hβ.le.trans (hβt.trans hq.le)
  have hgateD : T.gate q ≤ ev.time + budget := by
    dsimp only [u] at hgate
    linarith [hT.delta_pos]
  obtain ⟨Qfg, heq⟩ := exactCarrier q Q hQ (hgst.trans huq) hexact (hgateD.trans hhor)
  obtain ⟨hlo, hhi⟩ := p0d4_proposal_heights R E rho O T I A Jst Ef obs cert inv
    proposalFloor gateCopy hgst hp huq hgateD hQ heq hexact
  have hex : ∃ r, q ≤ r * T.roundSlots := by
    refine ⟨q, le_mul_of_one_le_right (Nat.zero_le q) ?_⟩
    exact le_trans (by decide : 1 ≤ (2 : Nat)) hT.rounds
  let r := Nat.find hex
  have hqr : q ≤ r * T.roundSlots := Nat.find_spec hex
  have hfirst : ∀ r', q ≤ r' * T.roundSlots → r ≤ r' := fun r' hr' => Nat.find_min' hex hr'
  obtain ⟨h0, h1⟩ := p0d4_first_time T hT q r hqr hfirst
  have har : T.action r ≤ u + repairAllowance + (FGCompose.P T - 4 * T.delta) := by
    linarith
  have hqg : T.proposal q ≤ T.gate q := by rw [hT.gate_eq]; linarith [hT.delta_pos]
  have hur : u ≤ T.action r := by linarith
  have hpr := p0d4_phase_restrict R E rho O hp hur (har.trans hbudget)
  have hc := (opening u k.frontier root contested q Q Qfg r hgst hQ heq hexact huq hqr hpr).1
  refine ⟨β, q, Q, Qfg, r, root, contested, hp, hcont, hgst, huq, hq, hgate, hQ, hexact,
    heq, hlo, hhi, hqr, har, hc, ?_⟩
  intro v hv
  exact (repair gapPos u v _ root contested hgst hv β hβ hmin).1

omit [DecidableEq V] [Fintype V] in
private theorem p0d4_budget_raise_contest (k : AttemptKey)
    (htask : k.task = .raise) (hphase : k.phase = .contest) :
    attemptBudget T G repairAllowance k = repairAllowance + 3 * FGCompose.P T + Γ T G - 10 *
      T.delta := by
  rw [p0d4_attemptBudget_def, htask]
  rw [hphase]

omit [DecidableEq V] [Fintype V] in
private theorem p0d4_budget_raise_other (k : AttemptKey)
    (htask : k.task = .raise) (hphase : k.phase ≠ .contest) :
    attemptBudget T G repairAllowance k = repairAllowance + 6 * FGCompose.P T + 2 * Γ T G - 18
      * T.delta := by
  rw [p0d4_attemptBudget_def, htask]
  cases hp : k.phase with
  | gap => rfl
  | topJ => rfl
  | contest => exact (hphase hp).elim

omit [DecidableEq V] [Fintype V] in
private theorem p0d4_budget_firstRow_contest (k : AttemptKey)
    (htask : k.task = .firstRow) (hphase : k.phase = .contest) :
    attemptBudget T G repairAllowance k = repairAllowance + FGCompose.P T - T.delta := by
  rw [p0d4_attemptBudget_def, htask]
  rw [hphase]

omit [DecidableEq V] [Fintype V] in
private theorem p0d4_budget_firstRow_other (k : AttemptKey)
    (htask : k.task = .firstRow) (hphase : k.phase ≠ .contest) :
    attemptBudget T G repairAllowance k = repairAllowance + 4 * FGCompose.P T + Γ T G - 9 *
      T.delta := by
  rw [p0d4_attemptBudget_def, htask]
  cases hp : k.phase with
  | gap => rfl
  | topJ => rfl
  | contest => exact (hphase hp).elim

omit [DecidableEq V] [Fintype V] in
private theorem p0d4_cut_mono {u v : Time} (huv : u ≤ v) :
    rho.idxBefore u ≤ rho.idxBefore v := by
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true ((of_decide_eq_true he).trans_le huv))

omit [DecidableEq V] [Fintype V] in
private theorem p0d4_cut_le_time {u v : Time} (huv : u ≤ v) :
    rho.idxBefore u ≤ timeIdx rho v := by
  rw [V2.D.Run.idxBefore_def, timeIdx_def]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true ((of_decide_eq_true he).le.trans huv))

omit [DecidableEq V] [Fintype V] in
private theorem p0d4_pre_after (t : Time) :
    rho.idxBefore t ≤ afterTicksIdx rho t ∧ afterTicksIdx rho t ≤ timeIdx rho t := by
  rw [V2.D.Run.idxBefore_def, afterTicksIdx_def, timeIdx_def]
  constructor
  · rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro e _ he
    exact decide_eq_true (Prod.Lex.toLex_le_toLex.mpr (Or.inl (of_decide_eq_true he)))
  · rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro e _ he
    rcases Prod.Lex.toLex_le_toLex.mp (of_decide_eq_true he) with h | ⟨h, _⟩
    · exact decide_eq_true (le_of_lt h)
    · exact decide_eq_true (le_of_eq h)

include opening in
omit [Fintype V] in
private theorem p0d4_opening_covered {u : Time} {m : Nat}
    {J : Option (FGBlock (Fin n))} {contested : Bool} {q r : Nat}
    {Q : Block} {Qfg : FGBlock (Fin n)} (hready : Jst ≤ u)
    (hQ : HonestProposal E rho I q Q) (heq : R.erase Qfg = Q)
    (hexact : AttemptExactService R E rho T I A q Q) (hu : u ≤ T.proposal q)
    (hqr : q ≤ r * T.roundSlots) (hp : PhaseInterval R E rho O u (T.action r) m J contested) :
    OpeningCovered R S E rho O.height T pair r Q :=
      (opening u m J contested q Q Qfg r hready hQ heq hexact hu hqr hp).1

include cert opening in
omit [Fintype V] in
private theorem p0d4_common_high {u : Time} {m : Nat}
    {J : Option (FGBlock (Fin n))} {contested : Bool} {q r : Nat}
    {Q : Block} {Qfg : FGBlock (Fin n)} (hready : Jst ≤ u)
    (hQ : HonestProposal E rho I q Q) (heq : R.erase Qfg = Q)
    (hexact : AttemptExactService R E rho T I A q Q) (hu : u ≤ T.proposal q)
    (hqr : q ≤ r * T.roundSlots) (hp : PhaseInterval R E rho O u (T.action r) m J contested)
    (hh : (O.height Qfg).h = m) : OpeningEntry R E rho O.height T r m :=
  common_entry_at_high R E rho O.height T Ef cert.height
    (opening u m J contested q Q Qfg r hready hQ heq hexact hu hqr hp).2 hh

include cert opening nextOpening in
omit [Fintype V] in
private theorem p0d4_common_low {u : Time} {m : Nat}
    {J : Option (FGBlock (Fin n))} {contested : Bool} {q r : Nat}
    {Q : Block} {Qfg : FGBlock (Fin n)} (hready : Jst ≤ u)
    (hQ : HonestProposal E rho I q Q) (heq : R.erase Qfg = Q)
    (hexact : AttemptExactService R E rho T I A q Q) (hu : u ≤ T.proposal q)
    (hqr : q ≤ r * T.roundSlots) (hp : PhaseInterval R E rho O u (T.action r) m J contested)
    (hh : (O.height Qfg).h = m - 1) :
    OpeningEntry R E rho O.height T r (m - 1) ∨
    ((∃ x K, x ∈ rho.honest ∧ actionSourceFG R E rho T x r = some (some K) ∧
      (O.height K).h = m) ∧
    (PhaseInterval R E rho O u (T.action (r + 1)) m J contested →
      OpeningEntry R E rho O.height T (r + 1) m)) := by
  apply common_entry_at_low R E rho O.height T Ef cert.height O hh
    (opening u m J contested q Q Qfg r hready hQ heq hexact hu hqr hp).2
  intro y K hy hK hp'
  exact nextOpening u m J contested q Q Qfg r hready hQ heq hexact hu hqr hp' y K hy hK

include obs cert inv justif keep hT coreLaws erasePreceq hs mono hdelta gst awake
  joinedTick readyCut heldServices receiptHeld allowanceNonneg gapPos repair opening
  proposalFloor gateCopy exactCarrier leaseLarge crossing in
include honestNonempty in
omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
H.10 firstRow / contest, with the standing ports and exact INLINE bodies.
The SO producer is rowPermission_covered. Both AttemptValid start arms are covered. -/
theorem healing_attempt_firstRow_contest
    {k : AttemptKey} {ev : V2.Event V Prot.Object}
    (hvalid : AttemptValid R S E rho O T I A pair Jst k) (hstart : rho.events[k.start]? = some ev)
    (hhor : ev.time + attemptBudget T G repairAllowance k ≤ rho.horizon)
    (htask : k.task = .firstRow) (hphase : k.phase = .contest) :
    AttemptEndsBy R S E rho O T pair k (attemptBudget T G repairAllowance k) := by
  classical
  by_contra hstop
  have hbudget := p0d4_budget_firstRow_contest T G repairAllowance k htask hphase
  obtain ⟨β, q, Q, Qfg, r, root, contested, hp, hcont, hgst, huq, _hq, _hgate, hQ, hexact, heq,
    hlo, hhi, hqr, har, hc, _hrepair⟩ := p0d4_repair_opening
      (R := R)
      (S := S)
      (E := E)
      (rho := rho)
      (O := O)
      (T := T)
      (I := I)
      (A := A)
      (pair := pair)
      (Jst := Jst)
      (Ef := Ef)
      (obs := obs)
      (cert := cert)
      (inv := inv)
      (justif := justif)
      (keep := keep)
      (hT := hT)
      (coreLaws := coreLaws)
      (erasePreceq := erasePreceq)
      (joined := joined)
      (receipt := receipt)
      (hs := hs)
      (mono := mono)
      (hdelta := hdelta)
      (gst := gst)
      (awake := awake)
      (joinedTick := joinedTick)
      (readyCut := readyCut)
      (heldServices := heldServices)
      (receiptHeld := receiptHeld)
      (G := G)
      (repairAllowance := repairAllowance)
      (leaseSlots := leaseSlots)
      (leaseLarge := leaseLarge)
      (allowanceNonneg := allowanceNonneg)
      (gapPos := gapPos)
      (repair := repair)
      (opening := opening)
      (proposalFloor := proposalFloor)
      (gateCopy := gateCopy)
      (exactCarrier := exactCarrier) crossing hvalid hstart hstop hhor (by
        rw [hbudget]; ring_nf; rfl)
  have hctrue : contested = true := hcont.mpr hphase
  rw [hctrue] at hp hlo
  have hh : (O.height Qfg).h = k.frontier := Nat.le_antisymm hhi hlo
  have hqg : T.proposal q ≤ T.gate q := by
    rw [hT.gate_eq]
    linarith [hT.delta_pos]
  have hur : ev.time + 3 * T.delta ≤ T.action r := by
    have hqrI : (q : Time) ≤ ((r * T.roundSlots : Nat) : Time) := by exact_mod_cast hqr
    rw [hT.action_eq, hT.gate_eq, hT.proposal_eq]
    change ev.time + 3 * T.delta ≤ 4 * ((r * T.roundSlots : Nat) : Time) * T.delta + 6 * T.delta
    rw [hT.proposal_eq] at huq
    nlinarith [hT.delta_pos]
  have hpr := p0d4_phase_restrict R E rho O hp hur (by rw [hbudget]; linarith)
  have he := p0d4_common_high
    (R := R)
    (S := S)
    (E := E)
    (rho := rho)
    (O := O)
    (T := T)
    (I := I)
    (A := A)
    (pair := pair)
    (Jst := Jst)
    (Ef := Ef)
    (cert := cert)
    (opening := opening)
    hgst hQ heq hexact huq
    hqr hpr hh
  exact hstop (p0d4_row_covered
    (R := R)
    (S := S)
    (E := E)
    (rho := rho)
    (O := O)
    (T := T)
    (I := I)
    (A := A)
    (pair := pair)
    (Jst := Jst)
    (hT := hT)
    (honestNonempty := honestNonempty) hvalid hstart htask
                              (by rw [hbudget]; linarith) hc he)

include obs cert inv justif keep hT coreLaws erasePreceq hs mono hdelta gst awake
  joinedTick readyCut heldServices receiptHeld allowanceNonneg gapPos repair opening
  proposalFloor gateCopy exactCarrier leaseLarge crossing in
include renewed faultQ honestQuorum nextOpening honestNonempty in
-- FaultQ names the actual finite node population; its instance is required.
set_option linter.unusedSectionVars false in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
H.10 firstRow / gap or topJ, with standing ports and the exact INLINE facts.
The low-entry branch uses renewed promotion within its existing gate horizon. -/
theorem healing_attempt_firstRow_other
    {k : AttemptKey} {ev : V2.Event V Prot.Object}
    (hvalid : AttemptValid R S E rho O T I A pair Jst k) (hstart : rho.events[k.start]? = some ev)
    (hhor : ev.time + attemptBudget T G repairAllowance k ≤ rho.horizon)
    (htask : k.task = .firstRow) (hphase : k.phase ≠ .contest) :
    AttemptEndsBy R S E rho O T pair k (attemptBudget T G repairAllowance k) := by
  classical
  by_contra hstop
  have hbudget := p0d4_budget_firstRow_other T G repairAllowance k htask hphase
  have hP := p0d4_period T hT
  have hΓ : 0 ≤ Γ T G := by
    have := (healing_promotion_gap_remainder T hT G).1
    linarith [gapPos, hT.delta_pos]
  obtain ⟨β, q, Q, Qfg, r, root, contested, hp, hcont, hgst, huq, hq, hgate, hQ, hexact, heq,
    hlo, hhi, hqr, har, hc, hrepair⟩ := p0d4_repair_opening
      (R := R)
      (S := S)
      (E := E)
      (rho := rho)
      (O := O)
      (T := T)
      (I := I)
      (A := A)
      (pair := pair)
      (Jst := Jst)
      (Ef := Ef)
      (obs := obs)
      (cert := cert)
      (inv := inv)
      (justif := justif)
      (keep := keep)
      (hT := hT)
      (coreLaws := coreLaws)
      (erasePreceq := erasePreceq)
      (joined := joined)
      (receipt := receipt)
      (hs := hs)
      (mono := mono)
      (hdelta := hdelta)
      (gst := gst)
      (awake := awake)
      (joinedTick := joinedTick)
      (readyCut := readyCut)
      (heldServices := heldServices)
      (receiptHeld := receiptHeld)
      (G := G)
      (repairAllowance := repairAllowance)
      (leaseSlots := leaseSlots)
      (leaseLarge := leaseLarge)
      (allowanceNonneg := allowanceNonneg)
      (gapPos := gapPos)
      (repair := repair)
      (opening := opening)
      (proposalFloor := proposalFloor)
      (gateCopy := gateCopy)
      (exactCarrier := exactCarrier) crossing hvalid hstart hstop hhor (by
        rw [hbudget]; linarith [hT.delta_pos])
  let u := ev.time + 3 * T.delta
  have hcfalse : contested = false := Bool.eq_false_iff.mpr (fun ht => hphase (hcont.mp ht))
  rw [hcfalse] at hp hlo hrepair
  have hqg : T.proposal q ≤ T.gate q := by
    rw [hT.gate_eq]
    linarith [hT.delta_pos]
  have hur : u ≤ T.action r := by
    have hqrI : (q : Time) ≤ ((r * T.roundSlots : Nat) : Time) := by exact_mod_cast hqr
    dsimp only [u]
    rw [hT.action_eq, hT.gate_eq, hT.proposal_eq]
    change ev.time + 3 * T.delta ≤ 4 * ((r * T.roundSlots : Nat) : Time) * T.delta + 6 * T.delta
    rw [hT.proposal_eq] at huq
    nlinarith [hT.delta_pos]
  have hrD : T.action r ≤ ev.time + attemptBudget T G repairAllowance k := by
    rw [hbudget]; linarith [hT.delta_pos]
  have hpr := p0d4_phase_restrict R E rho O hp hur hrD
  by_cases hh : (O.height Qfg).h = k.frontier
  · have he := p0d4_common_high
      (R := R)
      (S := S)
      (E := E)
      (rho := rho)
      (O := O)
      (T := T)
      (I := I)
      (A := A)
      (pair := pair)
      (Jst := Jst)
      (Ef := Ef)
      (cert := cert)
      (opening := opening)
      hgst hQ heq hexact huq
      hqr hpr hh
    exact hstop (p0d4_row_covered
      (R := R)
      (S := S)
      (E := E)
      (rho := rho)
      (O := O)
      (T := T)
      (I := I)
      (A := A)
      (pair := pair)
      (Jst := Jst)
      (hT := hT)
      (honestNonempty := honestNonempty) hvalid hstart htask hrD hc he)
  have hlow : (O.height Qfg).h = k.frontier - 1 := by
    simp only [Bool.false_eq_true, ↓reduceIte, Height] at hlo hhi hh ⊢
    omega
  rcases p0d4_common_low
    (R := R)
    (S := S)
    (E := E)
    (rho := rho)
    (O := O)
    (T := T)
    (I := I)
    (A := A)
    (pair := pair)
    (Jst := Jst)
    (Ef := Ef)
    (cert := cert)
    (opening := opening)
    (nextOpening := nextOpening)
    hgst hQ heq hexact huq hqr
      hpr hlow with he | ⟨⟨x, K, hx, hK, hhigh⟩, _hnext⟩
  · have hpromotionHor : T.action r + 2 * FGCompose.P T + Γ T G - 4 * T.delta ≤ rho.horizon := by
      apply le_trans _ hhor
      rw [hbudget]
      linarith [hT.delta_pos]
    rcases (renewed faultQ honestQuorum) r hpromotionHor u k.frontier root false
        (β + 2 * leaseSlots - 1) q Q (k.frontier - 1) hgst hpr huq hqr hq hQ hexact he hc
        hrepair with hevent | hcarrier
    · obtain ⟨i, ev', hi, hev', heff, ht⟩ := hevent
      have hsi : k.start < V2.D.Run.idxBefore rho (T.action r) :=
        (Gen.V2.Duty.index_lt_idxBefore_iff hs hstart _).mpr
          (by
            dsimp only [u] at hur
            exact (lt_add_of_pos_right ev.time
              (mul_pos (by decide : (0 : Time) < 3) hT.delta_pos)).trans_le hur)
      have hj : k.start < i := hsi.trans_le
        ((p0d4_pre_after rho _).1.trans hi)
      exact hstop (healing_attempt_ends_of_event R S E rho O T pair hstart hj hev'
        (by
          calc
            ev'.time ≤ T.action r + 2 * FGCompose.P T + Γ T G - 9 * T.delta := ht
            _ ≤ ev.time + attemptBudget T G repairAllowance k := by
              rw [hbudget]
              linarith only [har, hP, hT.delta_pos]) heff)
    · obtain ⟨s, X, hnew, hslot, hslo, hshi, hheight, _hreceipt, hservice⟩ := hcarrier
      have ha := p0d4_action T hT r
      have hurS : u ≤ T.proposal s := by linarith [hT.delta_pos]
      have hsGate : T.gate s ≤
          T.action r + 2 * FGCompose.P T + Γ T G - 4 * T.delta := by
        rw [hT.gate_eq]
        linarith
      have hsD : T.gate s ≤ ev.time + attemptBudget T G repairAllowance k := by
        rw [hbudget]; linarith [hT.delta_pos]
      have hps := p0d4_phase_restrict R E rho O hp
        (by rw [hT.gate_eq]; linarith [hT.delta_pos]) hsD
      obtain ⟨hexactS, _⟩ := hservice hps
      have hheights := p0d4_proposal_heights
        (R := R)
        (E := E)
        (rho := rho)
        (O := O)
        (T := T)
        (I := I)
        (A := A)
        (Jst := Jst)
        (Ef := Ef)
        (cert := cert)
        (inv := inv)
        (proposalFloor := proposalFloor)
        (gateCopy := gateCopy)
        (obs := obs)
        hgst hp hurS hsD hnew rfl hexactS
      have hm : 1 ≤ k.frontier := by obtain ⟨_, _, _, _, _, hm, _⟩ := hvalid; exact hm
      have hhS : (O.height X).h = k.frontier := by
        have hXhigh : k.frontier ≤ (O.height X).h := by
          simpa only [Nat.sub_add_cancel hm] using hheight
        exact Nat.le_antisymm hheights.2 hXhigh
      have hex : ∃ r', s ≤ r' * T.roundSlots := by
        refine ⟨s, le_mul_of_one_le_right (Nat.zero_le s) ?_⟩
        exact le_trans (by decide : 1 ≤ (2 : Nat)) hT.rounds
      let r' := Nat.find hex
      have hsr : s ≤ r' * T.roundSlots := Nat.find_spec hex
      have hfirst : ∀ r'', s ≤ r'' * T.roundSlots → r' ≤ r'' :=
        fun r'' hr'' => Nat.find_min' hex hr''
      obtain ⟨h0, h1⟩ := p0d4_first_time T hT s r' hsr hfirst
      have hr'D : T.action r' ≤ ev.time + attemptBudget T G repairAllowance k := by
        rw [hbudget]; linarith [hT.delta_pos]
      have hur' : u ≤ T.action r' := by
        have hsg : T.gate s = T.proposal s + 6 * T.delta := hT.gate_eq s
        rw [hsg] at h0
        linarith [hT.delta_pos]
      have hpr' := p0d4_phase_restrict R E rho O hp hur' hr'D
      have hc' := p0d4_opening_covered
        (R := R)
        (S := S)
        (E := E)
        (rho := rho)
        (O := O)
        (T := T)
        (I := I)
        (A := A)
        (pair := pair)
        (Jst := Jst)
        (opening := opening) hgst
        hnew rfl hexactS hurS hsr hpr'
      have he' := p0d4_common_high
        (R := R)
        (S := S)
        (E := E)
        (rho := rho)
        (O := O)
        (T := T)
        (I := I)
        (A := A)
        (pair := pair)
        (Jst := Jst)
        (Ef := Ef)
        (cert := cert)
        (opening := opening) hgst hnew
        rfl hexactS
        hurS hsr hpr' hhS
      exact hstop (p0d4_row_covered
        (R := R)
        (S := S)
        (E := E)
        (rho := rho)
        (O := O)
        (T := T)
        (I := I)
        (A := A)
        (pair := pair)
        (Jst := Jst)
        (hT := hT)
        (honestNonempty := honestNonempty) hvalid hstart htask hr'D hc' he')
  · exact hstop (p0d4_row_high
      (R := R)
      (S := S)
      (E := E)
      (rho := rho)
      (O := O)
      (T := T)
      (I := I)
      (A := A)
      (pair := pair)
      (Jst := Jst)
      (hT := hT)
      hvalid hstart htask hrD hc hx hK hhigh)

include obs inv hT hs gapPos in
omit [Fintype V] in
private theorem p0d4_terminal_contradiction
    (promote : AttemptTerminalPromotion R S E rho O T I pair Jst G)
    {k : AttemptKey} {ev : V2.Event V Prot.Object} {budget u : Time}
    {root : Option (FGBlock (Fin n))} {contested : Bool} {q r : Nat} {Q : Block}
    (hstart : rho.events[k.start]? = some ev)
    (hstop : ¬ AttemptEndsBy R S E rho O T pair k budget)
    (hp : PhaseInterval R E rho O u (ev.time + budget) k.frontier root contested)
    (hu : ev.time + 3 * T.delta ≤ u) (hgst : Jst ≤ u)
    (huq : u ≤ T.proposal q) (hqr : q ≤ r * T.roundSlots)
    (he : OpeningEntry R E rho O.height T r k.frontier)
    (hc : OpeningCovered R S E rho O.height T pair r Q)
    (hterminal : T.action r + 2 * FGCompose.P T + Γ T G - 9 * T.delta ≤ ev.time + budget) :
    False := by
  have hP := p0d4_period T hT
  have hΓ : 0 ≤ Γ T G := by
    have := (healing_promotion_gap_remainder T hT G).1
    linarith [gapPos, hT.delta_pos]
  have hur : u ≤ T.action r := by
    have hqrI : (q : Time) ≤ ((r * T.roundSlots : Nat) : Time) := by exact_mod_cast hqr
    rw [hT.action_eq, hT.gate_eq, hT.proposal_eq]
    change u ≤ 4 * ((r * T.roundSlots : Nat) : Time) * T.delta + 6 * T.delta
    rw [hT.proposal_eq] at huq
    nlinarith [hT.delta_pos]
  have hrD : T.action r ≤ ev.time + budget := by linarith [hT.delta_pos]
  have hpr := p0d4_phase_restrict R E rho O hp hur hrD
  rcases promote r (hterminal.trans hp.2.1)
      u k.frontier root contested q Q k.frontier hgst hpr huq hqr he hc
      with hevent | hcarrier
  · obtain ⟨i, ev', hi, hev', heff, ht⟩ := hevent
    have hsi : k.start < V2.D.Run.idxBefore rho (T.action r) :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hs hstart _).mpr (by
        linarith [hT.delta_pos])
    have hj : k.start < i := hsi.trans_le ((p0d4_pre_after rho _).1.trans hi)
    exact hstop (healing_attempt_ends_of_event R S E rho O T pair hstart hj hev'
      (ht.trans hterminal) heff)
  · obtain ⟨s, X, _hnew, _hslot, hslo, hshi, hh, y, hy, hheld⟩ := hcarrier
    let d := T.proposal s + T.delta
    have ha := p0d4_action T hT r
    have hud : u ≤ d := by dsimp only [d]; linarith [hT.delta_pos]
    have hdD : d ≤ ev.time + budget := by dsimp only [d]; linarith
    change X ∈ (R.core (V2.D.Run.stateBeforeTime E rho d y)).fg.TF at hheld
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hs] at hheld
    have hcap := (hp.2.2.2 (V2.D.Run.idxBefore rho d) y
      (p0d4_cut_mono rho hud)
      (p0d4_cut_le_time rho hdD) hy).1
    have hle := healing_phase_height_le
      (R := R)
      (E := E)
      (rho := rho)
      (O := O)
      (inv := inv) hheld
    rw [obs.controls_eq] at hcap
    change (R.core (rho.stateBefore E (V2.D.Run.idxBefore rho d) y)).fg.h_max =
      k.frontier at hcap
    rw [hcap] at hle
    simp only [Height] at hh hle
    omega

include obs cert inv justif keep hT coreLaws erasePreceq hs mono hdelta gst awake
  joinedTick readyCut heldServices receiptHeld allowanceNonneg gapPos repair opening
  proposalFloor gateCopy exactCarrier leaseLarge crossing in
include terminal faultQ honestQuorum in
-- FaultQ names the actual finite node population; its instance is required.
set_option linter.unusedSectionVars false in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
H.10 raise / contest, with the standing ports and exact INLINE bodies.
Terminal promotion uses the first high opening within the frozen budget. -/
theorem healing_attempt_raise_contest
    {k : AttemptKey} {ev : V2.Event V Prot.Object}
    (hvalid : AttemptValid R S E rho O T I A pair Jst k) (hstart : rho.events[k.start]? = some ev)
    (hhor : ev.time + attemptBudget T G repairAllowance k ≤ rho.horizon)
    (htask : k.task = .raise) (hphase : k.phase = .contest) :
    AttemptEndsBy R S E rho O T pair k (attemptBudget T G repairAllowance k) := by
  classical
  by_contra hstop
  have hbudget := p0d4_budget_raise_contest T G repairAllowance k htask hphase
  have hP := p0d4_period T hT
  have hΓ : 0 ≤ Γ T G := by
    have := (healing_promotion_gap_remainder T hT G).1
    linarith [gapPos, hT.delta_pos]
  obtain ⟨β, q, Q, Qfg, r, root, contested, hp, hcont, hgst, huq, hq, _hgate, hQ, hexact,
    heq, hlo, hhi, hqr, har, hc, hrepair⟩ := p0d4_repair_opening
      (R := R)
      (S := S)
      (E := E)
      (rho := rho)
      (O := O)
      (T := T)
      (I := I)
      (A := A)
      (pair := pair)
      (Jst := Jst)
      (Ef := Ef)
      (obs := obs)
      (cert := cert)
      (inv := inv)
      (justif := justif)
      (keep := keep)
      (hT := hT)
      (coreLaws := coreLaws)
      (erasePreceq := erasePreceq)
      (joined := joined)
      (receipt := receipt)
      (hs := hs)
      (mono := mono)
      (hdelta := hdelta)
      (gst := gst)
      (awake := awake)
      (joinedTick := joinedTick)
      (readyCut := readyCut)
      (heldServices := heldServices)
      (receiptHeld := receiptHeld)
      (G := G)
      (repairAllowance := repairAllowance)
      (leaseSlots := leaseSlots)
      (leaseLarge := leaseLarge)
      (allowanceNonneg := allowanceNonneg)
      (gapPos := gapPos)
      (repair := repair)
      (opening := opening)
      (proposalFloor := proposalFloor)
      (gateCopy := gateCopy)
      (exactCarrier := exactCarrier) crossing hvalid hstart hstop hhor (by
        rw [hbudget]; linarith [hT.delta_pos])
  have hctrue : contested = true := hcont.mpr hphase
  rw [hctrue] at hp hlo hrepair
  have hh : (O.height Qfg).h = k.frontier := Nat.le_antisymm hhi hlo
  have hur : ev.time + 3 * T.delta ≤ T.action r := by
    have hqrI : (q : Time) ≤ ((r * T.roundSlots : Nat) : Time) := by exact_mod_cast hqr
    rw [hT.action_eq, hT.gate_eq, hT.proposal_eq]
    change ev.time + 3 * T.delta ≤ 4 * ((r * T.roundSlots : Nat) : Time) * T.delta + 6 * T.delta
    rw [hT.proposal_eq] at huq
    nlinarith [hT.delta_pos]
  have hpr := p0d4_phase_restrict R E rho O hp hur (by rw [hbudget]; linarith [hT.delta_pos])
  have he := p0d4_common_high
    (R := R)
    (S := S)
    (E := E)
    (rho := rho)
    (O := O)
    (T := T)
    (I := I)
    (A := A)
    (pair := pair)
    (Jst := Jst)
    (Ef := Ef)
    (cert := cert)
    (opening := opening)
    hgst hQ heq hexact huq
    hqr hpr hh
  exact p0d4_terminal_contradiction
    (R := R)
    (S := S)
    (E := E)
    (rho := rho)
    (O := O)
    (T := T)
    (I := I)
    (pair := pair)
    (Jst := Jst)
    (inv := inv)
    (hT := hT)
    (hs := hs)
    (G := G)
    (obs := obs)
    (gapPos := gapPos) (terminal faultQ honestQuorum) hstart hstop hp
    le_rfl hgst huq hqr he hc (by rw [hbudget]; linarith only [har])

include obs cert inv justif keep hT coreLaws erasePreceq hs mono hdelta gst awake
  joinedTick readyCut heldServices receiptHeld allowanceNonneg gapPos repair opening
  proposalFloor gateCopy exactCarrier leaseLarge crossing in
include renewed terminal faultQ honestQuorum nextOpening in
-- FaultQ names the actual finite node population; its instance is required.
set_option linter.unusedSectionVars false in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
H.10 raise / gap or topJ, with the standing ports and exact INLINE bodies.
The low pivot uses existing gate service. Terminal promotion then uses a high opening. -/
theorem healing_attempt_raise_other
    {k : AttemptKey} {ev : V2.Event V Prot.Object}
    (hvalid : AttemptValid R S E rho O T I A pair Jst k) (hstart : rho.events[k.start]? = some ev)
    (hhor : ev.time + attemptBudget T G repairAllowance k ≤ rho.horizon)
    (htask : k.task = .raise) (hphase : k.phase ≠ .contest) :
    AttemptEndsBy R S E rho O T pair k (attemptBudget T G repairAllowance k) := by
  classical
  by_contra hstop
  have hbudget := p0d4_budget_raise_other T G repairAllowance k htask hphase
  have hP := p0d4_period T hT
  have hΓ : 0 ≤ Γ T G := by
    have := (healing_promotion_gap_remainder T hT G).1
    linarith [gapPos, hT.delta_pos]
  obtain ⟨β, q, Q, Qfg, r, root, contested, hp, hcont, hgst, huq, hq, _hgate, hQ, hexact,
    heq, hlo, hhi, hqr, har, hc, hrepair⟩ := p0d4_repair_opening
      (R := R)
      (S := S)
      (E := E)
      (rho := rho)
      (O := O)
      (T := T)
      (I := I)
      (A := A)
      (pair := pair)
      (Jst := Jst)
      (Ef := Ef)
      (obs := obs)
      (cert := cert)
      (inv := inv)
      (justif := justif)
      (keep := keep)
      (hT := hT)
      (coreLaws := coreLaws)
      (erasePreceq := erasePreceq)
      (joined := joined)
      (receipt := receipt)
      (hs := hs)
      (mono := mono)
      (hdelta := hdelta)
      (gst := gst)
      (awake := awake)
      (joinedTick := joinedTick)
      (readyCut := readyCut)
      (heldServices := heldServices)
      (receiptHeld := receiptHeld)
      (G := G)
      (repairAllowance := repairAllowance)
      (leaseSlots := leaseSlots)
      (leaseLarge := leaseLarge)
      (allowanceNonneg := allowanceNonneg)
      (gapPos := gapPos)
      (repair := repair)
      (opening := opening)
      (proposalFloor := proposalFloor)
      (gateCopy := gateCopy)
      (exactCarrier := exactCarrier) crossing hvalid hstart hstop hhor (by
        rw [hbudget]; linarith [hT.delta_pos])
  let u := ev.time + 3 * T.delta
  have hcfalse : contested = false := Bool.eq_false_iff.mpr (fun ht => hphase (hcont.mp ht))
  rw [hcfalse] at hp hlo hrepair
  have hur : u ≤ T.action r := by
    have hqrI : (q : Time) ≤ ((r * T.roundSlots : Nat) : Time) := by exact_mod_cast hqr
    dsimp only [u]
    rw [hT.action_eq, hT.gate_eq, hT.proposal_eq]
    change ev.time + 3 * T.delta ≤ 4 * ((r * T.roundSlots : Nat) : Time) * T.delta + 6 * T.delta
    rw [hT.proposal_eq] at huq
    nlinarith [hT.delta_pos]
  have hrD : T.action r ≤ ev.time + attemptBudget T G repairAllowance k := by
    rw [hbudget]; linarith [hT.delta_pos]
  have hpr := p0d4_phase_restrict R E rho O hp hur hrD
  by_cases hh : (O.height Qfg).h = k.frontier
  · have he := p0d4_common_high
      (R := R)
      (S := S)
      (E := E)
      (rho := rho)
      (O := O)
      (T := T)
      (I := I)
      (A := A)
      (pair := pair)
      (Jst := Jst)
      (Ef := Ef)
      (cert := cert)
      (opening := opening)
      hgst hQ heq hexact huq
      hqr hpr hh
    exact p0d4_terminal_contradiction
      (R := R)
      (S := S)
      (E := E)
      (rho := rho)
      (O := O)
      (T := T)
      (I := I)
      (pair := pair)
      (Jst := Jst)
      (inv := inv)
      (hT := hT)
      (hs := hs)
      (G := G)
      (obs := obs)
      (gapPos := gapPos) (terminal faultQ honestQuorum) hstart hstop hp
      le_rfl hgst huq hqr he hc (by rw [hbudget]; linarith [hT.delta_pos])
  have hlow : (O.height Qfg).h = k.frontier - 1 := by
    simp only [Bool.false_eq_true, ↓reduceIte, Height] at hlo hhi hh ⊢
    omega
  rcases p0d4_common_low
    (R := R)
    (S := S)
    (E := E)
    (rho := rho)
    (O := O)
    (T := T)
    (I := I)
    (A := A)
    (pair := pair)
    (Jst := Jst)
    (Ef := Ef)
    (cert := cert)
    (opening := opening)
    (nextOpening := nextOpening)
    hgst hQ heq hexact huq hqr
      hpr hlow with he | ⟨⟨x, K, hx, hK, hhigh⟩, hnext⟩
  · have hpromotionHor : T.action r + 2 * FGCompose.P T + Γ T G - 4 * T.delta ≤ rho.horizon := by
      apply le_trans _ hhor
      rw [hbudget]
      linarith [hT.delta_pos]
    rcases (renewed faultQ honestQuorum) r hpromotionHor u k.frontier root false
        (β + 2 * leaseSlots - 1) q Q (k.frontier - 1) hgst hpr huq hqr hq hQ hexact he hc
        hrepair with hevent | hcarrier
    · obtain ⟨i, ev', hi, hev', heff, ht⟩ := hevent
      have hsi : k.start < V2.D.Run.idxBefore rho (T.action r) :=
        (Gen.V2.Duty.index_lt_idxBefore_iff hs hstart _).mpr
          (by dsimp only [u] at hur; linarith [hT.delta_pos])
      have hj : k.start < i := hsi.trans_le
        ((p0d4_pre_after rho _).1.trans hi)
      exact hstop (healing_attempt_ends_of_event R S E rho O T pair hstart hj hev'
        (by
          calc
            ev'.time ≤ T.action r + 2 * FGCompose.P T + Γ T G - 9 * T.delta := ht
            _ ≤ ev.time + attemptBudget T G repairAllowance k := by
              rw [hbudget]
              linarith only [har, hP, hΓ, hT.delta_pos]) heff)
    · obtain ⟨s, X, hnew, _hslot, hslo, hshi, hheight, _hreceipt, hservice⟩ := hcarrier
      have ha := p0d4_action T hT r
      have hurS : u ≤ T.proposal s := by linarith [hT.delta_pos]
      have hsGate : T.gate s ≤
          T.action r + 2 * FGCompose.P T + Γ T G - 4 * T.delta := by
        rw [hT.gate_eq]
        linarith
      have hsD : T.gate s ≤ ev.time + attemptBudget T G repairAllowance k := by
        rw [hbudget]; linarith [hT.delta_pos]
      have hps := p0d4_phase_restrict R E rho O hp
        (by rw [hT.gate_eq]; linarith [hT.delta_pos]) hsD
      obtain ⟨hexactS, _⟩ := hservice hps
      have hheights := p0d4_proposal_heights
        (R := R)
        (E := E)
        (rho := rho)
        (O := O)
        (T := T)
        (I := I)
        (A := A)
        (Jst := Jst)
        (Ef := Ef)
        (cert := cert)
        (inv := inv)
        (proposalFloor := proposalFloor)
        (gateCopy := gateCopy)
        (obs := obs) hgst hp hurS hsD hnew rfl
        hexactS
      have hm : 1 ≤ k.frontier := by obtain ⟨_, _, _, _, _, hm, _⟩ := hvalid; exact hm
      have hhS : (O.height X).h = k.frontier := by
        have hXhigh : k.frontier ≤ (O.height X).h := by
          simpa only [Nat.sub_add_cancel hm] using hheight
        exact Nat.le_antisymm hheights.2 hXhigh
      have hex : ∃ r', s ≤ r' * T.roundSlots := by
        refine ⟨s, le_mul_of_one_le_right (Nat.zero_le s) ?_⟩
        exact le_trans (by decide : 1 ≤ (2 : Nat)) hT.rounds
      let r' := Nat.find hex
      have hsr : s ≤ r' * T.roundSlots := Nat.find_spec hex
      have hfirst : ∀ r'', s ≤ r'' * T.roundSlots → r' ≤ r'' :=
        fun r'' hr'' => Nat.find_min' hex hr''
      obtain ⟨h0, h1⟩ := p0d4_first_time T hT s r' hsr hfirst
      have hr'D : T.action r' ≤ ev.time + attemptBudget T G repairAllowance k := by
        rw [hbudget]; linarith [hT.delta_pos]
      have hur' : u ≤ T.action r' := by
        have hsg : T.gate s = T.proposal s + 6 * T.delta := hT.gate_eq s
        rw [hsg] at h0
        linarith [hT.delta_pos]
      have hpr' := p0d4_phase_restrict R E rho O hp hur' hr'D
      have hc' := p0d4_opening_covered
        (R := R)
        (S := S)
        (E := E)
        (rho := rho)
        (O := O)
        (T := T)
        (I := I)
        (A := A)
        (pair := pair)
        (Jst := Jst)
        (opening := opening) hgst
        hnew rfl hexactS hurS hsr hpr'
      have he' := p0d4_common_high
        (R := R)
        (S := S)
        (E := E)
        (rho := rho)
        (O := O)
        (T := T)
        (I := I)
        (A := A)
        (pair := pair)
        (Jst := Jst)
        (Ef := Ef)
        (cert := cert)
        (opening := opening) hgst hnew
        rfl hexactS
        hurS hsr hpr' hhS
      exact p0d4_terminal_contradiction
        (R := R)
        (S := S)
        (E := E)
        (rho := rho)
        (O := O)
        (T := T)
        (I := I)
        (pair := pair)
        (Jst := Jst)
        (inv := inv)
        (hT := hT)
        (hs := hs)
        (G := G)
        (obs := obs)
        (gapPos := gapPos) (terminal faultQ honestQuorum) hstart hstop hp
        le_rfl hgst hurS hsr he' hc'
        (by rw [hbudget]; linarith only [har, hsGate, h1])
  · have hanext : T.action (r + 1) = T.action r + FGCompose.P T := by
      rw [p0d4_action T hT, p0d4_action T hT]
      push_cast
      ring
    have hur' : u ≤ T.action (r + 1) := by rw [hanext]; linarith [hT.delta_pos]
    have hr'D : T.action (r + 1) ≤ ev.time + attemptBudget T G repairAllowance k := by
      rw [hanext, hbudget]; linarith [hT.delta_pos]
    have hpr' := p0d4_phase_restrict R E rho O hp hur' hr'D
    have hqr' : q ≤ (r + 1) * T.roundSlots := hqr.trans (Nat.mul_le_mul_right _ (Nat.le_succ r))
    have hc' := p0d4_opening_covered
      (R := R)
      (S := S)
      (E := E)
      (rho := rho)
      (O := O)
      (T := T)
      (I := I)
      (A := A)
      (pair := pair)
      (Jst := Jst)
      (opening := opening) hgst
      hQ heq hexact huq hqr' hpr'
    exact p0d4_terminal_contradiction
      (R := R)
      (S := S)
      (E := E)
      (rho := rho)
      (O := O)
      (T := T)
      (I := I)
      (pair := pair)
      (Jst := Jst)
      (inv := inv)
      (hT := hT)
      (hs := hs)
      (G := G)
      (obs := obs)
      (gapPos := gapPos) (terminal faultQ honestQuorum) hstart hstop hp
      le_rfl hgst huq hqr' (hnext hpr') hc'
      (by rw [hanext, hbudget]; linarith [hT.delta_pos])

end AvailableChain.FGCompose
end
