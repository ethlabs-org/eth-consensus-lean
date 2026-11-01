module
public import AvailableChainFGCompose.Statements.FrontierSearch
public import AvailableChainFGCompose.Proofs.Healing.PhaseOrder
public import AvailableChainGeneric.Proofs.V2.Duty.Reads

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot)
variable (O : FGObservationReads R) (T : FGTiming) (Jst : Time)
variable (pair : Wire → NamedHeightPair)
variable (chainRows : Prot.State → Block → List Wire)
variable (Ef : Electorate (Fin n)) (obs : FGObservationLaws R O)
variable (cert : FGCertificateLaws Ef O.height O.finality)
variable (inv : ∀ i x, FGStoreInvariant O.height O.finality
  (R.core (rho.stateBefore E i x)).fg)
variable (justif : FGJustificationLaws O.height)
variable (keep : ∀ i j, i ≤ j → ∀ x, TFAt R E rho i x ⊆ TFAt R E rho j x)

private theorem p0d5a_frontier_mono (mono : FGRunOrderLaws E rho R) {i j : Nat}
    (hij : i ≤ j) : frontierAtIdx R E rho i ≤ frontierAtIdx R E rho j := by
  apply Finset.sup_le
  intro x hx
  exact (mono.mono i j x hx hij).2.2.trans
    (Finset.le_sup (f := fun y => (R.core (rho.stateBefore E j y)).fg.h_max) hx)

omit [DecidableEq V] in
/-- Blueprint 21 H.10; plan §4 closed horizon.
DC: SAME an actual event in the inclusive prefix has time at most its cut. -/
theorem frontierSearch_event_time_le (hs : V2.D.ScheduleWellFormed E rho)
    {j : Nat} {ev : V2.Event V Prot.Object} {deadline : Time}
    (hj : rho.events[j]? = some ev) (hcut : j < timeIdx rho deadline) :
    ev.time ≤ deadline := by
  have hc : V2.D.Run.idxBefore rho (deadline + 1) = timeIdx rho deadline := by
    change (rho.events.filter (fun e => decide (e.time < deadline + 1))).length =
      (rho.events.filter (fun e => decide (e.time ≤ deadline))).length
    simp only [Int.lt_add_one_iff]
  exact Int.lt_add_one_iff.mp
    ((Gen.V2.Duty.index_lt_idxBefore_iff hs hj _).mp (hc ▸ hcut))

/-- Blueprint 21 H.10 and HG.3; plan gap 6.
DC: SAME construct the least actual event in the closed deadline prefix. -/
theorem frontierSearch_first_effective_split (hs : V2.D.ScheduleWellFormed E rho)
    (i : Nat) (deadline : Time) :
    FirstEffectiveBy R E rho O i deadline ∨
      (∀ j, i < j → j < timeIdx rho deadline → ¬ EffectiveEvent R E rho O j) := by
  classical
  by_cases hex : ∃ j, i < j ∧ j < timeIdx rho deadline ∧ EffectiveEvent R E rho O j
  · left
    apply (FirstEffectiveBy_def R E rho O i deadline).mpr
    let j := Nat.find hex
    obtain ⟨hij, hjd, heff⟩ := Nat.find_spec hex
    have hjlen : j < rho.events.length := hjd.trans_le (List.length_filter_le ..)
    let ev := rho.events[j]
    have hj : rho.events[j]? = some ev := List.getElem?_eq_getElem hjlen
    have htime := frontierSearch_event_time_le E rho hs hj hjd
    refine ⟨j, ev, hij, hj, htime, heff, ?_⟩
    intro k hik hkj he
    exact Nat.find_min hex hkj ⟨hik, hkj.trans hjd, he⟩
  · right
    intro j hij hjd he
    exact hex ⟨j, hij, hjd, he⟩

/-- Blueprint 21 HG.3; plan Q1.
DC: SAME classify the finite first stop by its actual frontier. -/
theorem frontierSearch_classify_stop (mono : FGRunOrderLaws E rho R)
    {i m : Nat} {deadline : Time}
    (hfront : frontierAtIdx R E rho (i + 1) = m)
    (hstop : FirstEffectiveBy R E rho O i deadline) :
    FirstPhaseStopBy R E rho O i m deadline ∨
      FirstRiseStopBy R E rho O i m deadline := by
  obtain ⟨j, ev, hij, hj, ht, heff, hfirst⟩ := (FirstEffectiveBy_def R E rho O i deadline).mp hstop
  have hmono := p0d5a_frontier_mono R E rho mono
    (show i + 1 ≤ j + 1 by omega)
  rw [hfront] at hmono
  by_cases heq : frontierAtIdx R E rho (j + 1) = m
  · exact Or.inl ((FirstPhaseStopBy_def R E rho O i m deadline).mpr
      ⟨j, ev, hij, hj, ht, heff, heq, hfirst⟩)
  · exact Or.inr ((FirstRiseStopBy_def R E rho O i m deadline).mpr
      ⟨j, ev, hij, hj, ht, heff, by omega, hfirst⟩)

/-- Blueprint 21 HG.1/HG.4; plan §4.
DC: SAME first rise selection permits earlier same-frontier events. -/
theorem frontierSearch_first_rise (hs : V2.D.ScheduleWellFormed E rho)
    {i m : Nat} {deadline : Time}
    (hex : ∃ j, i < j ∧ j < timeIdx rho deadline ∧
      m < frontierAtIdx R E rho (j + 1))
    (hstart : frontierAtIdx R E rho (i + 1) ≤ m) :
    FrontierRiseBy R E rho i m deadline := by
  classical
  apply (FrontierRiseBy_def R E rho i m deadline).mpr
  let j := Nat.find hex
  obtain ⟨hij, hjd, hheight⟩ := Nat.find_spec hex
  have hjlen : j < rho.events.length := hjd.trans_le (List.length_filter_le ..)
  let ev := rho.events[j]
  have hj : rho.events[j]? = some ev := List.getElem?_eq_getElem hjlen
  refine ⟨j, ev, hij, hj, frontierSearch_event_time_le E rho hs hj hjd, hheight, ?_⟩
  intro k hik hkj
  by_cases hk : k = i + 1
  · exact hk ▸ hstart
  · by_contra hn
    have hkpos : 0 < k := by omega
    have hpred : i < k - 1 := by omega
    have hpredj : k - 1 < j := by omega
    apply Nat.find_min hex hpredj
    exact ⟨hpred, hpredj.trans hjd, by simpa only [Nat.sub_add_cancel hkpos] using
      (lt_of_not_ge hn)⟩

/-- Blueprint 21 HG.4/H.11; plan §3.3.
DC: SAME select one first row from an actual emitted row. -/
theorem frontierSearch_first_row (hT : FGTimingLaws T) {m r : Nat} {deadline : Time}
    (hrow : HeightRow S E rho T (fun a => namedEntry (pair a)) r m)
    (htime : T.action r ≤ deadline) :
    FirstHeightRowBy S E rho T pair m deadline := by
  classical
  apply (FirstHeightRowBy_def S E rho T pair m deadline).mpr
  have hex : ∃ r', HeightRow S E rho T (fun a => namedEntry (pair a)) r' m := ⟨r, hrow⟩
  have hfirst : Nat.find hex ≤ r := Nat.find_min' hex hrow
  refine ⟨Nat.find hex, Nat.find_spec hex, fun r' hr' => Nat.find_min' hex hr', ?_⟩
  have ha : Monotone T.action := by
    intro a b hab
    have hc : (a : Time) ≤ b := by exact_mod_cast hab
    rw [hT.action_eq, hT.action_eq, hT.gate_eq, hT.gate_eq,
      hT.proposal_eq, hT.proposal_eq]
    push_cast
    have hd := hT.delta_pos
    have hR : 0 ≤ (T.roundSlots : Time) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hc hR
    have hfour := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : Time) ≤ 4)
    have hprod := mul_le_mul_of_nonneg_right hfour hd.le
    linarith only [hprod]
  exact (ha hfirst).trans htime

/-- Blueprint 21 H.11; plan §3.3 reset minimization.
DC: SAME both repair allowances must select this same first round. -/
theorem frontierSearch_first_row_unique {m r r' : Nat}
    (hr : HeightRow S E rho T (fun a => namedEntry (pair a)) r m)
    (hfirst : ∀ s, HeightRow S E rho T (fun a => namedEntry (pair a)) s m → r ≤ s)
    (hr' : HeightRow S E rho T (fun a => namedEntry (pair a)) r' m)
    (hfirst' : ∀ s, HeightRow S E rho T (fun a => namedEntry (pair a)) s m → r' ≤ s) : r = r' :=
  Nat.le_antisymm (hfirst r' hr') (hfirst' r hr)

/-- Blueprint 21 HG.5 and IF.3(a); plan §3.3.
DC: SAME a skipped frontier supplies a real earlier honest M+1 row via RCap.
The height inequality alone is never used as a row witness. -/
theorem frontierSearch_skipped_row
    (cap : RCap R S E rho O T (fun a => namedEntry (pair a)) chainRows)
    {M i : Nat} {x : V} {W : FGBlock (Fin n)}
    (hW : HeldAt R E rho i x W) (hskip : M + 2 ≤ (O.height W).h) :
    ∃ j z r a e, j < i ∧ HonestRowAt S E rho T j z r a ∧
      namedEntry (pair a) = some (M + 1, e) := by
  obtain ⟨j, z, r, a, e, hji, hr, hn, _⟩ := cap M i x W hW hskip
  exact ⟨j, z, r, a, e, hji, hr, hn⟩

include obs cert inv justif keep in
/-- Blueprint 21 HG.5; phase-order composition.
DC: SAME a same-frontier effective stop strictly advances the phase.
Thus the gap and top-J charge cannot be repeated at this frontier. -/
theorem frontierSearch_phase_step_of_crossing (crossing : RXing R E rho O)
    (mono : FGRunOrderLaws E rho R)
    (hs : V2.D.ScheduleWellFormed E rho) {i m : Nat} {kind : PhaseKind}
    {ev : V2.Event V Prot.Object} {deadline : Time}
    (hstart : FrontierSearchStart R E rho O T Jst i ev m kind)
    (hstop : FirstPhaseStopBy R E rho O i m deadline) :
    ∃ j nextEv nextKind, i < j ∧ nextEv.time ≤ deadline ∧
      FrontierSearchStart R E rho O T Jst j nextEv m nextKind ∧
      frontierSearch_phaseRank nextKind > frontierSearch_phaseRank kind := by
  classical
  obtain ⟨j, nextEv, hij, hj, ht, heff, hf, _⟩ :=
    (FirstPhaseStopBy_def R E rho O i m deadline).mp hstop
  obtain ⟨hi, hgst, _, hf0, hm, hk⟩ :=
    (FrontierSearchStart_def R E rho O T Jst i ev m kind).mp hstart
  have hjlen : j < rho.events.length := (List.getElem?_eq_some_iff.mp hj).1
  have hfixed : ∀ k, i + 1 ≤ k → k ≤ j + 1 → frontierAtIdx R E rho k = m := by
    intro k hik hkj
    apply Nat.le_antisymm
    · exact (p0d5a_frontier_mono R E rho mono hkj).trans_eq hf
    · exact hf0 ▸ p0d5a_frontier_mono R E rho mono hik
  have horder := healing_phase_order_of_crossing_all (R := R) (E := E) (rho := rho)
    (O := O) (Ef := Ef) (obs := obs) (cert := cert) (inv := inv)
    (justif := justif) (keep := keep) crossing mono (i + 1) (j + 1) m
    (by omega) (by omega) hm hfixed
  have hbits := horder.1 (i + 1) j le_rfl (by omega) (by omega)
  have heff' : (¬ TopEvidence R E rho j m ∧ TopEvidence R E rho (j + 1) m) ∨
      (¬ ContestEvidence R E rho O j m ∧ ContestEvidence R E rho O (j + 1) m) := by
    rcases heff with h | h
    · rw [hfixed j (by omega) (by omega), hf] at h
      exact (lt_irrefl m h).elim
    · simpa only [hf] using h
  have htime : ev.time ≤ nextEv.time := by
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
    have hkey := (List.pairwise_iff_getElem.mp hs.sorted) i j hil hjl hij
    rw [hie, hje] at hkey
    exact V2.D.Engine.time_le_of_key_le _ _ hkey
  have finish (nextKind : PhaseKind) (hnext : AttemptPhaseAt R E rho O (j + 1) m nextKind)
      (hrank : frontierSearch_phaseRank kind < frontierSearch_phaseRank nextKind) :
      ∃ j nextEv nextKind, i < j ∧ nextEv.time ≤ deadline ∧
        FrontierSearchStart R E rho O T Jst j nextEv m nextKind ∧
        frontierSearch_phaseRank nextKind > frontierSearch_phaseRank kind := by
    exact ⟨j, nextEv, nextKind, hij, ht,
      (FrontierSearchStart_def R E rho O T Jst j nextEv m nextKind).mpr
        ⟨hj, hgst.trans htime, Or.inl heff, hf, hm, hnext⟩, hrank⟩
  cases kind with
  | gap =>
    rcases heff' with ⟨_, ht⟩ | ⟨_, hc⟩
    · by_cases hc : ContestEvidence R E rho O (j + 1) m
      · exact finish .contest hc (by decide)
      · exact finish .topJ ⟨ht, hc⟩ (by decide)
    · exact finish .contest hc (by decide)
  | topJ =>
    have htj := hbits.1 hk.1
    rcases heff' with ⟨hn, _⟩ | ⟨_, hc⟩
    · exact (hn htj).elim
    · exact finish .contest hc (by decide)
  | contest =>
    have hcj := hbits.2 hk
    have ht0 := horder.2 (i + 1) le_rfl (by omega) hk
    have htj := hbits.1 ht0
    rcases heff' with ⟨hn, _⟩ | ⟨hn, _⟩
    · exact (hn htj).elim
    · exact (hn hcj).elim

/-- Blueprint 21:1592–1638; S5 H2, route step 1.
DC: SAME choose the first rise strictly before D, or cap the strict cut.
A rise at exactly D does not enter the strict prefix. Same-frontier events do not stop it. -/
theorem frontierSearch_strict_cap_or_rise
    (hs : V2.D.ScheduleWellFormed E rho) (mono : FGRunOrderLaws E rho R)
    (i m : Nat) (D : Time) (hstart : frontierAtIdx R E rho (i + 1) ≤ m) :
    FrontierRiseBy R E rho i m D ∨
      (∀ k x, k ≤ V2.D.Run.idxBefore rho D → x ∈ rho.honest →
        (R.core (rho.stateBefore E k x)).fg.h_max ≤ m) := by
  classical
  by_cases hc : frontierAtIdx R E rho (V2.D.Run.idxBefore rho D) ≤ m
  · right
    intro k x hk hx
    exact (healing_phase_local_le_frontier R E rho hx).trans
      ((p0d5a_frontier_mono R E rho mono hk).trans hc)
  · left
    have hcut : i + 1 < V2.D.Run.idxBefore rho D := by
      by_contra hn
      exact hc ((p0d5a_frontier_mono R E rho mono (by omega)).trans hstart)
    have hex : ∃ j, i < j ∧ j < V2.D.Run.idxBefore rho D ∧
        m < frontierAtIdx R E rho (j + 1) := by
      refine ⟨V2.D.Run.idxBefore rho D - 1, by omega, by omega, ?_⟩
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ V2.D.Run.idxBefore rho D)] using
        (lt_of_not_ge hc)
    let j := Nat.find hex
    obtain ⟨hij, hjD, hh⟩ := Nat.find_spec hex
    have hjlen : j < rho.events.length := hjD.trans_le (List.length_filter_le ..)
    let ev := rho.events[j]
    have hj : rho.events[j]? = some ev := List.getElem?_eq_getElem hjlen
    apply (FrontierRiseBy_def R E rho i m D).mpr
    refine ⟨j, ev, hij, hj,
      ((Gen.V2.Duty.index_lt_idxBefore_iff hs hj D).mp hjD).le, hh, ?_⟩
    intro k hik hkj
    by_cases hk : k = i + 1
    · exact hk ▸ hstart
    · by_contra hn
      have hkpos : 0 < k := by omega
      apply Nat.find_min hex (show k - 1 < j by omega)
      exact ⟨by omega, by omega, by
        simpa only [Nat.sub_add_cancel hkpos] using (lt_of_not_ge hn)⟩

omit [DecidableEq V] in
/-- Blueprint 21:1592–1638; S5 H2, route step 4.
DC: SAME an inclusive earlier read lies inside the strict later cut. -/
theorem frontierSearch_timeIdx_le_idxBefore {t D : Time} (ht : t < D) :
    timeIdx rho t ≤ V2.D.Run.idxBefore rho D := by
  change (rho.events.filter (fun e => decide (e.time ≤ t))).length ≤
    (rho.events.filter (fun e => decide (e.time < D))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true ((of_decide_eq_true he).trans_lt ht))

/-- Blueprint 21:1695–1720; S5 F2.
DC: SAME a longer deadline retains the same first rise and earlier frontier cap. -/
theorem frontierSearch_rise_mono {i m : Nat} {d D : Time} (hd : d ≤ D)
    (hr : FrontierRiseBy R E rho i m d) : FrontierRiseBy R E rho i m D := by
  obtain ⟨j, ev, hij, hj, ht, hh, hf⟩ := (FrontierRiseBy_def R E rho i m d).mp hr
  exact (FrontierRiseBy_def R E rho i m D).mpr ⟨j, ev, hij, hj, ht.trans hd, hh, hf⟩

include inv keep in
/-- Blueprint 21:1695–1720; S5 F2.
DC: SAME strict honest high receipt forces a first rise before the receipt deadline. -/
theorem frontierSearch_rise_of_receipt (hs : V2.D.ScheduleWellFormed E rho)
    (mono : FGRunOrderLaws E rho R) {i m : Nat} {d D : Time} {x : V}
    {X : FGBlock (Fin n)} (hstart : frontierAtIdx R E rho (i + 1) ≤ m)
    (hx : x ∈ rho.honest) (hh : m + 1 ≤ (O.height X).h)
    (hheld : Gen.V2.Duty.HoldsBefore E rho (fun nd => X ∈ (R.core nd).fg.TF) d x)
    (hd : d ≤ D) : FrontierRiseBy R E rho i m D := by
  rcases frontierSearch_strict_cap_or_rise R E rho hs mono i m D hstart with hr | hc
  · exact hr
  · change X ∈ (R.core (V2.D.Run.stateBeforeTime E rho d x)).fg.TF at hheld
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hs] at hheld
    have hidx : rho.idxBefore d ≤ rho.idxBefore D := by
      change (rho.events.filter (fun e => decide (e.time < d))).length ≤
        (rho.events.filter (fun e => decide (e.time < D))).length
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      exact List.countP_mono_left fun e _ he =>
        decide_eq_true ((of_decide_eq_true he).trans_le hd)
    have hX := keep _ _ hidx x hheld
    have hhi := healing_phase_height_le (R := R) (E := E) (rho := rho) (O := O) (inv := inv) hX
    have hcap := hc _ x le_rfl hx
    simp only [Height] at *
    omega

/-- The qualified seed lies after the actual prior-slot join/read cutoff. -/
theorem frontier_seed_prior_cut (T : FGTiming) (hT : FGTimingLaws T)
    (leaseSlots : Nat) (hkLarge : 2 ≤ leaseSlots) (GST Jst : Time)
    {u : Time} {q : Slot} (hGST : GST ≤ Jst) (hready : Jst ≤ u)
    (hseed : FrontierSeedQualification T leaseSlots GST u q) :
    GST ≤ slotStartZ T ((q : Int) - 1) := by
  have hGSTu : GST ≤ u := hGST.trans hready
  have hk : (2 : Int) ≤ leaseSlots := by exact_mod_cast hkLarge
  have hd := hT.delta_pos
  rcases hseed with ⟨β, hβ, _, hlate⟩ | ⟨b, hb, _, _, _, hlate⟩
  · simp only [hT.proposal_eq] at hβ hlate
    have hq : β + 2 * leaseSlots - 1 < q := by
      by_contra hn
      have hle : (q : Int) ≤ (β + 2 * leaseSlots - 1 : Nat) := by exact_mod_cast Nat.le_of_not_gt hn
      nlinarith
    have hcast : ((β + 2 * leaseSlots - 1 : Nat) : Int) = (β : Int) + 2 * leaseSlots - 1 := by
      have hkNat := hkLarge
      omega
    have hqI : ((β + 2 * leaseSlots - 1 : Nat) : Int) < (q : Int) := by exact_mod_cast hq
    rw [hcast] at hqI
    change GST ≤ 4 * T.delta * ((q : Int) - 1)
    nlinarith
  · simp only [hT.vote_eq, hT.proposal_eq] at hb hlate
    have hq : b + leaseSlots < q := by
      by_contra hn
      have hle : (q : Int) ≤ (b + leaseSlots : Nat) := by exact_mod_cast Nat.le_of_not_gt hn
      nlinarith
    have hqI : ((b + leaseSlots : Nat) : Int) < (q : Int) := by exact_mod_cast hq
    push_cast at hqI
    change GST ≤ 4 * T.delta * ((q : Int) - 1)
    nlinarith

end AvailableChain.FGCompose
end
