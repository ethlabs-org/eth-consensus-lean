module
public import AvailableChainFGCompose.Statements.Attempt
public import AvailableChainFGCompose.Proofs.Healing.PhaseSettle

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

include obs cert inv justif keep hT coreLaws erasePreceq hs mono hdelta gst awake
  joinedTick readyCut heldServices receiptHeld

/-- ROOT-DIGEST W2b. H.8 settlement for either frozen AttemptValid start arm. -/
theorem healing_attempt_settle_start
    (crossing : RXing R E rho O)
    {k : AttemptKey}
    {ev : V2.Event V Prot.Object} {v : Time}
    (hvalid : AttemptValid R S E rho O T I A pair Jst k) (hstart : rho.events[k.start]? = some ev)
    (hu : ev.time + 3 * T.delta ≤ v) (hv : v ≤ rho.horizon)
    (hquiet : ∀ j, k.start < j → j < timeIdx rho v → ¬ EffectiveEvent R E rho O j) :
    ∃ J,
      let root := match k.phase with | .gap => none | .topJ => some J | .contest => none
      let contested := match k.phase with | .gap => false | .topJ => false | .contest => true
      PhaseInterval R E rho O (ev.time + 3 * T.delta) v k.frontier root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * T.delta ≤ T.vote s →
        T.vote s ≤ v →
        postClock E rho y (T.vote s) = some nd →
        SettledPhaseFrame R O nd k.frontier root contested) := by
  obtain ⟨ev0, hi0, hgst, _hstart, hfront, hm, hkind, _⟩ := hvalid
  have he : ev0 = ev := Option.some.inj (hi0.symm.trans hstart)
  subst ev0
  obtain ⟨J, hsettled⟩ := healing_settle_start_on (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef)
    (obs := obs) (cert := cert) (inv := inv) (justif := justif) (keep := keep)
    (Jst := Jst) (T := T) (positive := hT.delta_pos) (coreLaws := coreLaws)
    (erasePreceq := erasePreceq) (joined := joined) (receipt := receipt)
    crossing hs mono hdelta gst awake joinedTick readyCut heldServices receiptHeld
    k.start ev v k.frontier k.phase hstart hgst hu hv hm hfront.symm hkind hquiet
  refine ⟨J, ?_⟩
  cases hp : k.phase <;> simpa only [hp] using hsettled

/-- Settlement for the raise / contest row, including the cut start. -/
theorem healing_attempt_raise_contest_settle
    (crossing : RXing R E rho O)
    {k : AttemptKey}
    {ev : V2.Event V Prot.Object} {v : Time}
    (hvalid : AttemptValid R S E rho O T I A pair Jst k) (hstart : rho.events[k.start]? = some ev)
    (hu : ev.time + 3 * T.delta ≤ v) (hv : v ≤ rho.horizon)
    (hquiet : ∀ j, k.start < j → j < timeIdx rho v → ¬ EffectiveEvent R E rho O j)
    (_htask : k.task = .raise) (_hphase : k.phase = .contest) :
    ∃ J,
      let root := match k.phase with | .gap => none | .topJ => some J | .contest => none
      let contested := match k.phase with | .gap => false | .topJ => false | .contest => true
      PhaseInterval R E rho O (ev.time + 3 * T.delta) v k.frontier root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * T.delta ≤ T.vote s →
        T.vote s ≤ v →
        postClock E rho y (T.vote s) = some nd →
        SettledPhaseFrame R O nd k.frontier root contested) :=
  healing_attempt_settle_start R S E rho O T I A pair Jst Ef obs cert inv justif keep hT
    coreLaws erasePreceq joined receipt hs mono hdelta gst awake joinedTick readyCut
    heldServices receiptHeld crossing hvalid hstart hu hv hquiet

/-- Settlement for the raise / other row, including the cut start. -/
theorem healing_attempt_raise_other_settle
    (crossing : RXing R E rho O)
    {k : AttemptKey}
    {ev : V2.Event V Prot.Object} {v : Time}
    (hvalid : AttemptValid R S E rho O T I A pair Jst k) (hstart : rho.events[k.start]? = some ev)
    (hu : ev.time + 3 * T.delta ≤ v) (hv : v ≤ rho.horizon)
    (hquiet : ∀ j, k.start < j → j < timeIdx rho v → ¬ EffectiveEvent R E rho O j)
    (_htask : k.task = .raise) (_hphase : k.phase ≠ .contest) :
    ∃ J,
      let root := match k.phase with | .gap => none | .topJ => some J | .contest => none
      let contested := match k.phase with | .gap => false | .topJ => false | .contest => true
      PhaseInterval R E rho O (ev.time + 3 * T.delta) v k.frontier root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * T.delta ≤ T.vote s →
        T.vote s ≤ v →
        postClock E rho y (T.vote s) = some nd →
        SettledPhaseFrame R O nd k.frontier root contested) :=
  healing_attempt_settle_start R S E rho O T I A pair Jst Ef obs cert inv justif keep hT
    coreLaws erasePreceq joined receipt hs mono hdelta gst awake joinedTick readyCut
    heldServices receiptHeld crossing hvalid hstart hu hv hquiet

/-- Settlement for the firstRow / contest row, including the cut start. -/
theorem healing_attempt_firstRow_contest_settle
    (crossing : RXing R E rho O)
    {k : AttemptKey}
    {ev : V2.Event V Prot.Object} {v : Time}
    (hvalid : AttemptValid R S E rho O T I A pair Jst k) (hstart : rho.events[k.start]? = some ev)
    (hu : ev.time + 3 * T.delta ≤ v) (hv : v ≤ rho.horizon)
    (hquiet : ∀ j, k.start < j → j < timeIdx rho v → ¬ EffectiveEvent R E rho O j)
    (_htask : k.task = .firstRow) (_hphase : k.phase = .contest) :
    ∃ J,
      let root := match k.phase with | .gap => none | .topJ => some J | .contest => none
      let contested := match k.phase with | .gap => false | .topJ => false | .contest => true
      PhaseInterval R E rho O (ev.time + 3 * T.delta) v k.frontier root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * T.delta ≤ T.vote s →
        T.vote s ≤ v →
        postClock E rho y (T.vote s) = some nd →
        SettledPhaseFrame R O nd k.frontier root contested) :=
  healing_attempt_settle_start R S E rho O T I A pair Jst Ef obs cert inv justif keep hT
    coreLaws erasePreceq joined receipt hs mono hdelta gst awake joinedTick readyCut
    heldServices receiptHeld crossing hvalid hstart hu hv hquiet

/-- Settlement for the firstRow / other row, including the cut start. -/
theorem healing_attempt_firstRow_other_settle
    (crossing : RXing R E rho O)
    {k : AttemptKey}
    {ev : V2.Event V Prot.Object} {v : Time}
    (hvalid : AttemptValid R S E rho O T I A pair Jst k) (hstart : rho.events[k.start]? = some ev)
    (hu : ev.time + 3 * T.delta ≤ v) (hv : v ≤ rho.horizon)
    (hquiet : ∀ j, k.start < j → j < timeIdx rho v → ¬ EffectiveEvent R E rho O j)
    (_htask : k.task = .firstRow) (_hphase : k.phase ≠ .contest) :
    ∃ J,
      let root := match k.phase with | .gap => none | .topJ => some J | .contest => none
      let contested := match k.phase with | .gap => false | .topJ => false | .contest => true
      PhaseInterval R E rho O (ev.time + 3 * T.delta) v k.frontier root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * T.delta ≤ T.vote s →
        T.vote s ≤ v →
        postClock E rho y (T.vote s) = some nd →
        SettledPhaseFrame R O nd k.frontier root contested) :=
  healing_attempt_settle_start R S E rho O T I A pair Jst Ef obs cert inv justif keep hT
    coreLaws erasePreceq joined receipt hs mono hdelta gst awake joinedTick readyCut
    heldServices receiptHeld crossing hvalid hstart hu hv hquiet

end AvailableChain.FGCompose
end
