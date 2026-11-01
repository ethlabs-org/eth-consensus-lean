module
public import AvailableChainFGCompose.Proofs.Healing.PhaseOrder
public import AvailableChainFGCompose.Statements.PhaseReceipts
public import AvailableChainGeneric.Proofs.V2.Duty.Reads
public import AvailableChainKitFG.Correspondence

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)
variable (O : FGObservationReads R) (Ef : Electorate (Fin n))
variable (obs : FGObservationLaws R O)
variable (cert : FGCertificateLaws Ef O.height O.finality)
variable (inv : ∀ i x, FGStoreInvariant O.height O.finality
  (R.core (V2.D.Run.stateBefore E rho i x)).fg)
variable (justif : FGJustificationLaws O.height)
variable (keep : ∀ i j, i ≤ j → ∀ x, TFAt R E rho i x ⊆ TFAt R E rho j x)
variable (Jst : Time)

variable (T : FGTiming) (positive : 0 < T.delta)
variable (coreLaws : FGCoreLaws R)
variable (erasePreceq : ∀ {A B}, FGBlock.Preceq A B → Block.Preceq (R.erase A) (R.erase B))
variable (joined : P.State → Bool) (receipt : Block → Time → V → Prop)

/-- Selected held evidence enters the protocol's frozen HEAD input at the same read. -/
theorem healing_phase_head_inclusion
    (voterBlocks : P.State → Slot → Finset (FGBlock (Fin n)))
    (frozenHeadMem : ∀ d y (W : FGBlock (Fin n)) s nd,
      Jst ≤ d → 0 < d → y ∈ rho.honest →
      frontierAtIdx R E rho (timeIdx rho (T.vote s)) ≤ (O.height W).h →
      d ≤ T.vote s → d ≤ T.freeze (s - 1) →
      W ∈ (R.core (rho.stateBefore E (rho.idxBefore d) y)).fg.TF →
      postClock E rho y (T.vote s) = some nd →
      W ∈ voterBlocks nd s)
    {d : Time} {y : V} {W : FGBlock (Fin n)} {s : Slot} {nd : P.State}
    (hready : Jst ≤ d) (hdpos : 0 < d) (hy : y ∈ rho.honest)
    (hcap : frontierAtIdx R E rho (timeIdx rho (T.vote s)) ≤ (O.height W).h)
    (hdt : d ≤ T.vote s) (hdf : d ≤ T.freeze (s - 1))
    (hW : W ∈ (R.core (rho.stateBefore E (rho.idxBefore d) y)).fg.TF)
    (hpost : postClock E rho y (T.vote s) = some nd) :
    W ∈ voterBlocks nd s :=
  frozenHeadMem d y W s nd hready hdpos hy hcap hdt hdf hW hpost

omit [DecidableEq V] in
private theorem phase_cut_le_time {d t : Time} (hdt : d ≤ t) :
    V2.D.Run.idxBefore rho d ≤ timeIdx rho t := by
  change (rho.events.filter (fun e => decide (e.time < d))).length ≤
    (rho.events.filter (fun e => decide (e.time ≤ t))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true ((of_decide_eq_true he).le.trans hdt))

omit [DecidableEq V] in
private theorem phase_cut_mono {d d' : Time} (hdd : d ≤ d') :
    V2.D.Run.idxBefore rho d ≤ V2.D.Run.idxBefore rho d' := by
  change (rho.events.filter (fun e => decide (e.time < d))).length ≤
    (rho.events.filter (fun e => decide (e.time < d'))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true ((of_decide_eq_true he).trans_le hdd))

omit [DecidableEq V] in
private theorem phase_index_lt_time (hs : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {e : V2.Event V (P.Object)} (hk : rho.events[k]? = some e) {t : Time}
    (ht : e.time ≤ t) : k < timeIdx rho t := by
  have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hs hk (t + 1)).mpr (Int.lt_add_one_iff.mpr ht)
  refine hlt.trans_le ?_
  change (rho.events.filter (fun e => decide (e.time < t + 1))).length ≤
    (rho.events.filter (fun e => decide (e.time ≤ t))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true (Int.lt_add_one_iff.mp (of_decide_eq_true he)))

include cert inv justif in
theorem phase_top_carrier (crossing : RXing R E rho O) {k m : Nat} {y : V}
    {C : FGBlock (Fin n)} (hy : y ∈ rho.honest)
    (hC : C ∈ (R.core (V2.D.Run.stateBefore E rho k y)).fg.TF) (hh : (O.height C).h = m)
    (hj : (O.height C).h_j + 1 = m) (hcap : frontierAtIdx R E rho k ≤ m) :
    (R.core (V2.D.Run.stateBefore E rho k y)).fg.h_max = m ∧ (R.core (V2.D.Run.stateBefore E rho k
      y)).fg.h_j + 1 = m ∧
      (FGBlock.Preceq (R.core (V2.D.Run.stateBefore E rho k y)).fg.J C →
        (R.core (V2.D.Run.stateBefore E rho k y)).fg.J = (O.height C).J) := by
  have hs : KitFG.FGStoreInvariant (O.height) (O.finality)
      (R.core (V2.D.Run.stateBefore E rho k y)).fg := (inv k y)
  have hmax : (R.core (V2.D.Run.stateBefore E rho k y)).fg.h_max = m := le_antisymm
    ((healing_phase_local_le_frontier (R := R) (E := E) (rho := rho) hy).trans hcap)
    (hh ▸ healing_phase_height_le (R := R) (E := E) (rho := rho) (O := O) (inv := inv) hC)
  have hlt := healing_phase_justified_lt (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef) (cert
    := cert) (inv := inv) k y
  have hJC : FGBlock.Preceq (O.height C).J C :=
    KitFG.preceq_trans ((cert).height.justified_preceq_entry C)
      ((cert).height.entry_preceq C)
  obtain ⟨K, hK, hKF⟩ := hs.Fcar
  have hFK := healing_phase_finality_le (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef) (cert
    := cert) (inv := inv) hK hKF
  have hlo : m - 1 ≤ (R.core (V2.D.Run.stateBefore E rho k y)).fg.h_j := by
    by_cases hF : m - 1 ≤ (O.finality K).h_F
    · (simp only [Height] at *; omega)
    · have hjne : (O.height C).h_j ≠ 0 := by (simp only [Height] at *; omega)
      have hJh := (justif).J_height C hjne
      have hJmem := KitFG.ancestor_closed_of_parent_closed _ hs.closed C hC _ hJC
      have hFJ := crossing k k y y K _ hy le_rfl hK hKF ⟨hy, hJmem⟩
        (by (simp only [Height] at *; omega))
      have hkey := KitFG.fst_le_of_lexKey_le (hs.pair.2 C hC hFJ)
      (simp only [Height] at *; omega)
  refine ⟨hmax, by (simp only [Height] at *; omega), ?_⟩
  intro hJ
  obtain ⟨D, _, _, hjD, hJD⟩ := hs.pair.1
  rw [hJD]
  apply healing_phase_entries_eq (H := O.height) (f := O.finality) (Ef := Ef) (cert := cert)
    (justif := justif) (W := C)
  · (simp only [Height] at *; omega)
  · exact hJD ▸ hJ
  · exact hJC

include obs in
/-- SAME: the settled frame depends only on the FG store. -/
private theorem phase_frame_store_eq {nd nd' : P.State}
    (h : (R.core nd).fg = (R.core nd').fg)
    {m : Nat} {J : Option (FGBlock (Fin n))} {contested : Bool}
    (hf : SettledPhaseFrame R O nd m J contested) :
    SettledPhaseFrame R O nd' m J contested := by
  cases J <;> delta SettledPhaseFrame at * <;>
    simp only [obs.controls_eq] at * <;> rw [← h] <;> exact hf

include obs cert inv positive coreLaws in
private theorem phase_finish (crossing : RXing R E rho O)
    (hs : V2.D.ScheduleWellFormed E rho) {ev : V2.Event V (P.Object)}
    {v : Time} {m : Nat} {J : Option (FGBlock (Fin n))} {contested : Bool}
    (hu : ev.time + 3 * T.delta ≤ v) (hv : v ≤ rho.horizon) (hm : 1 ≤ m)
    (hcore : ∀ k y, V2.D.Run.idxBefore rho (ev.time + T.delta) ≤ k → k ≤ timeIdx rho v →
      y ∈ rho.honest →
      (O.controls (V2.D.Run.stateBefore E rho k y)).H = m ∧ (O.controls (V2.D.Run.stateBefore E
        rho k y)).contest = contested ∧
      (match J with
        | some B => (O.controls (V2.D.Run.stateBefore E rho k y)).rootIsJ = true ∧ (O.controls
          (V2.D.Run.stateBefore E rho k y)).J = B
        | none => (O.controls (V2.D.Run.stateBefore E rho k y)).rootIsJ = false)) :
    PhaseInterval R E rho O (ev.time + 3 * T.delta) v m J contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * T.delta ≤ T.vote s →
        T.vote s ≤ v →
        postClock E rho y (T.vote s) = some nd →
        SettledPhaseFrame R O nd m J contested) := by
  have hpos := positive
  have hd3 : ev.time + T.delta ≤ ev.time + 3 * T.delta := by
    simp only [Time] at *
    omega
  refine ⟨⟨by simp only [Time] at *; omega, hv, hm, ?_⟩, ?_⟩
  · intro k x hk hkv hx
    exact hcore k x ((phase_cut_mono rho hd3).trans hk) hkv hx
  · intro y s nd hy hvote hvs hpost
    rw [postClock_def, preTick_def] at hpost
    cases hk : V2.D.Run.tickIdx? rho y (T.vote s) with
    | none => simp only [hk, Option.map_none, reduceCtorEq] at hpost
    | some k =>
      rw [hk] at hpost
      have hnd := Option.some.inj hpost
      subst nd
      have htick := V2.D.Run.tickIdx?_spec hk
      have hjk : V2.D.Run.idxBefore rho (ev.time + T.delta) ≤ k := by
        by_contra hn
        have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hs htick (ev.time + T.delta)).mp (by omega)
        change T.vote s < ev.time + T.delta at hlt
        simp only [Time] at *
        omega
      have hkv : k ≤ timeIdx rho v :=
        (phase_index_lt_time E rho hs htick (t := v) hvs).le
      obtain ⟨hH, hc, hr⟩ := hcore k y hjk hkv hy
      have hf := healing_phase_frame (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef) (obs :=
        obs) (cert := cert) (inv := inv) crossing hy hm hH hc hr
      exact phase_frame_store_eq (R := R) (O := O) obs (coreLaws.clock_fg _ _).symm hf

theorem healing_phase_window_all (mono : FGRunOrderLaws E rho R) {i m : Nat} {v : Time}
    (hfront : frontierAtIdx R E rho (i + 1) = m)
    (hquiet : ∀ j, i < j → j < timeIdx rho v → ¬ EffectiveEvent R E rho O j) :
    ∀ k, i + 1 ≤ k → k ≤ timeIdx rho v →
      frontierAtIdx R E rho k = m ∧
      (TopEvidence R E rho k m → TopEvidence R E rho (i + 1) m) ∧
      (ContestEvidence R E rho O k m → ContestEvidence R E rho O (i + 1) m) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact fun _ => ⟨hfront, id, id⟩
  | succ k hk ih =>
    intro hkv
    obtain ⟨hf, ht, hc⟩ := ih (by omega)
    have hq := hquiet k (by omega) (by omega)
    have hmono := (Finset.sup_mono_fun (fun x hx => (mono.mono k (k + 1) x hx (Nat.le_add_right k
      1)).2.2))
    change frontierAtIdx R E rho k ≤ frontierAtIdx R E rho (k + 1) at hmono
    have hf' : frontierAtIdx R E rho (k + 1) = m := by
      by_contra hne
      exact hq (Or.inl (by omega))
    refine ⟨hf', fun h => ht ?_, fun h => hc ?_⟩
    · by_contra hn
      exact hq (Or.inr (show (¬ TopEvidence R E rho k (frontierAtIdx R E rho (k + 1)) ∧
        TopEvidence R E rho (k + 1) (frontierAtIdx R E rho (k + 1))) ∨ _ from
        Or.inl (by rw [hf']; exact ⟨hn, h⟩)))
    · by_contra hn
      exact hq (Or.inr (show _ ∨
        (¬ ContestEvidence R E rho O k (frontierAtIdx R E rho (k + 1)) ∧
        ContestEvidence R E rho O (k + 1) (frontierAtIdx R E rho (k + 1))) from
        Or.inr (by rw [hf']; exact ⟨hn, h⟩)))

include obs cert inv justif keep positive coreLaws in
/-- DC: INTENTIONAL. Selected carriers held at the strict deadline settle all three phases.
This pure step keeps the original source witnesses. Protocol receipt proofs supply their
membership at the cut; it does not assume the resulting phase or a fixed F root. -/
theorem phase_settle_from_carriers (crossing : RXing R E rho O)
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {ev : V2.Event V P.Object}
    {v : Time} {m : Nat} {kind : PhaseKind}
    (hu : ev.time + 3 * T.delta ≤ v) (hv : v ≤ rho.horizon) (hm : 1 ≤ m)
    (hcut : i + 1 ≤ V2.D.Run.idxBefore rho (ev.time + T.delta))
    (hwin : ∀ k, i + 1 ≤ k → k ≤ timeIdx rho v →
      frontierAtIdx R E rho k = m ∧
      (TopEvidence R E rho k m → TopEvidence R E rho (i + 1) m) ∧
      (ContestEvidence R E rho O k m → ContestEvidence R E rho O (i + 1) m))
    (hkind : AttemptPhaseAt R E rho O (i + 1) m kind)
    (front : ∃ x W, HeldAt R E rho (i + 1) x W ∧ (O.height W).h = m ∧
      ∀ y ∈ rho.honest,
        W ∈ (R.core (rho.stateBefore E (rho.idxBefore (ev.time + T.delta)) y)).fg.TF)
    (top : TopEvidence R E rho (i + 1) m →
      ∃ x C, HeldAt R E rho (i + 1) x C ∧ (O.height C).h = m ∧
        (O.height C).h_j + 1 = m ∧
        (O.height C).J = (R.core (rho.stateBefore E (i + 1) x)).fg.J ∧
        ∀ y ∈ rho.honest,
          C ∈ (R.core (rho.stateBefore E (rho.idxBefore (ev.time + T.delta)) y)).fg.TF)
    (contest : ContestEvidence R E rho O (i + 1) m →
      ∃ x C W, HeldAt R E rho (i + 1) x C ∧ HeldAt R E rho (i + 1) x W ∧
        (O.height C).h = m ∧ (O.height W).h = m ∧ (O.height C).h_j + 1 = m ∧
        ¬ FGBlock.Preceq (O.height C).J W ∧
        (∀ y ∈ rho.honest,
          C ∈ (R.core (rho.stateBefore E (rho.idxBefore (ev.time + T.delta)) y)).fg.TF) ∧
        (∀ y ∈ rho.honest,
          W ∈ (R.core (rho.stateBefore E (rho.idxBefore (ev.time + T.delta)) y)).fg.TF)) :
      ∃ J,
        let root := match kind with | .gap => none | .topJ => some J | .contest => none
        let contested := match kind with | .gap => false | .topJ => false | .contest => true
        PhaseInterval R E rho O (ev.time + 3 * T.delta) v m root contested ∧
        (∀ y s nd, y ∈ rho.honest → ev.time + 3 * T.delta ≤ T.vote s →
          T.vote s ≤ v →
          postClock E rho y (T.vote s) = some nd →
          SettledPhaseFrame R O nd m root contested) := by
  rcases O with ⟨height, finality, controls, viable⟩
  have hc0 : controls = fun nd => treeStoreControlsView height (R.core nd).fg :=
    funext obs.controls_eq
  have hv0 : viable = fun nd X => treeStoreFrameView height (R.core nd).fg X :=
    funext fun nd => funext (obs.viable_eq nd)
  subst controls viable
  let O : FGObservationReads R :=
    ⟨height, finality, (fun nd => treeStoreControlsView height (R.core nd).fg),
      fun nd X => treeStoreFrameView height (R.core nd).fg X⟩
  have hcap (k : Nat) (hk : rho.idxBefore (ev.time + T.delta) ≤ k)
      (hkv : k ≤ timeIdx rho v) : frontierAtIdx R E rho k = m :=
    (hwin k (hcut.trans hk) hkv).1
  have hH {W : FGBlock (Fin n)} (hh : (O.height W).h = m)
      (held : ∀ y ∈ rho.honest,
        W ∈ (R.core (rho.stateBefore E (rho.idxBefore (ev.time + T.delta)) y)).fg.TF)
      {k : Nat} {y : V} (hk : rho.idxBefore (ev.time + T.delta) ≤ k)
      (hkv : k ≤ timeIdx rho v) (hy : y ∈ rho.honest) :
      (O.controls (rho.stateBefore E k y)).H = m :=
    le_antisymm ((healing_phase_local_le_frontier (R := R) (E := E) (rho := rho) hy).trans_eq
      (hcap k hk hkv))
      (hh ▸ healing_phase_height_le (R := R) (E := E) (rho := rho) (O := O)
        (inv := inv) (keep _ _ hk y (held y hy)))
  cases kind with
  | gap =>
    obtain ⟨hnt, _⟩ := hkind
    obtain ⟨x, W, hW, hh, hReceipt⟩ := front
    refine ⟨.genesis, phase_finish (R := R) (E := E) (rho := rho) (O := O)
      (Ef := Ef) (obs := obs) (cert := cert) (inv := inv)
      (T := T) (positive := positive) (coreLaws := coreLaws) crossing hs hu hv hm ?_⟩
    intro k y hk hkv hy
    have hHk := hH hh hReceipt hk hkv hy
    have hnj : (R.core (V2.D.Run.stateBefore E rho k y)).fg.h_j + 1 ≠ m :=
      fun ht => hnt ((hwin k (by omega) hkv).2.1 ⟨y, hy, ht⟩)
    change (R.core (V2.D.Run.stateBefore E rho k y)).fg.h_max = m at hHk
    have hc : (O.controls (V2.D.Run.stateBefore E rho k y)).contest = false := by
      change (decide ((R.core (V2.D.Run.stateBefore E rho k y)).fg.h_max =
        (R.core (V2.D.Run.stateBefore E rho k y)).fg.h_j + 1) && _) = false
      rw [hHk]
      simp only [Ne.symm hnj, decide_false, Bool.false_and]
    refine ⟨hHk, hc, ?_⟩
    change (decide ((O.controls (V2.D.Run.stateBefore E rho k y)).H = (O.controls
      (V2.D.Run.stateBefore E rho k y)).j + 1) &&
      !(O.controls (V2.D.Run.stateBefore E rho k y)).contest) = false
    change (decide ((R.core (V2.D.Run.stateBefore E rho k y)).fg.h_max =
      (R.core (V2.D.Run.stateBefore E rho k y)).fg.h_j + 1) && _) = false
    rw [hHk]
    simp only [Ne.symm hnj, decide_false, Bool.false_and]
  | topJ =>
    obtain ⟨ht, hnc⟩ := hkind
    obtain ⟨x, C, hC, hh, hj, _, hReceipt⟩ := top ht
    refine ⟨(O.height C).J, phase_finish (R := R) (E := E) (rho := rho) (O := O)
      (Ef := Ef) (obs := obs) (cert := cert) (inv := inv)
      (T := T) (positive := positive) (coreLaws := coreLaws) crossing hs hu hv hm ?_⟩
    intro k y hk hkv hy
    have hCk := keep _ _ hk y (hReceipt y hy)
    obtain ⟨hmax, htop, hJ⟩ := phase_top_carrier (R := R) (E := E) (rho := rho) (O := O)
      (Ef := Ef) (cert := cert) (inv := inv) (justif := justif) crossing hy hCk hh hj
      (hcap k hk hkv).le
    have hc : (O.controls (V2.D.Run.stateBefore E rho k y)).contest = false := by
      cases he : (O.controls (V2.D.Run.stateBefore E rho k y)).contest with
      | false => rfl
      | true => exact (hnc ((hwin k (by omega) hkv).2.2 ⟨y, hy, hmax, he⟩)).elim
    have hc' := hc
    change (decide ((R.core (V2.D.Run.stateBefore E rho k y)).fg.h_max =
      (R.core (V2.D.Run.stateBefore E rho k y)).fg.h_j + 1) && decide (∃ W ∈ (R.core
        (V2.D.Run.stateBefore E rho k y)).fg.TF,
        FGBlock.Preceq (R.core (V2.D.Run.stateBefore E rho k y)).fg.F W ∧
        (O.height W).h = (R.core (V2.D.Run.stateBefore E rho k y)).fg.h_max ∧
        ¬ FGBlock.Preceq (R.core (V2.D.Run.stateBefore E rho k y)).fg.J W)) = false at hc'
    have hJC : FGBlock.Preceq (R.core (V2.D.Run.stateBefore E rho k y)).fg.J C := by
      by_contra hn
      rcases Bool.and_eq_false_iff.mp hc' with h | h
      · exact of_decide_eq_false h (hmax.trans htop.symm)
      · exact of_decide_eq_false h ⟨C, hCk,
          (healing_phase_frontier_root (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef) (obs :=
            obs) (cert := cert) (inv := inv) crossing hy hCk
            (hh.trans hmax.symm)).1, hh.trans hmax.symm, hn⟩
    refine ⟨hmax, hc, ?_, hJ hJC⟩
    change (decide ((R.core (V2.D.Run.stateBefore E rho k y)).fg.h_max =
      (R.core (V2.D.Run.stateBefore E rho k y)).fg.h_j + 1) && !(O.controls (V2.D.Run.stateBefore
        E rho k y)).contest) = true
    rw [hc, hmax, htop]
    simp only [decide_true, Bool.not_false, Bool.and_self]
  | contest =>
    obtain ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff, hReceiptC, hReceiptW⟩ := contest hkind
    refine ⟨.genesis, phase_finish (R := R) (E := E) (rho := rho) (O := O)
      (Ef := Ef) (obs := obs) (cert := cert) (inv := inv)
      (T := T) (positive := positive) (coreLaws := coreLaws) crossing hs hu hv hm ?_⟩
    intro k y hk hkv hy
    have hCk := keep _ _ hk y (hReceiptC y hy)
    have hWk := keep _ _ hk y (hReceiptW y hy)
    obtain ⟨hmax, htop, hJ⟩ := phase_top_carrier (R := R) (E := E) (rho := rho) (O := O)
      (Ef := Ef) (cert := cert) (inv := inv) (justif := justif) crossing hy hCk hhC hj
      (hcap k hk hkv).le
    have hc : (O.controls (V2.D.Run.stateBefore E rho k y)).contest = true := by
      change (decide ((R.core (V2.D.Run.stateBefore E rho k y)).fg.h_max =
        (R.core (V2.D.Run.stateBefore E rho k y)).fg.h_j + 1) && decide (∃ W ∈ (R.core
          (V2.D.Run.stateBefore E rho k y)).fg.TF,
          FGBlock.Preceq (R.core (V2.D.Run.stateBefore E rho k y)).fg.F W ∧
          (O.height W).h = (R.core (V2.D.Run.stateBefore E rho k y)).fg.h_max ∧
          ¬ FGBlock.Preceq (R.core (V2.D.Run.stateBefore E rho k y)).fg.J W)) = true
      refine Bool.and_eq_true_iff.mpr ⟨decide_eq_true (hmax.trans htop.symm),
        decide_eq_true ?_⟩
      by_cases hJC : FGBlock.Preceq (R.core (V2.D.Run.stateBefore E rho k y)).fg.J C
      · exact ⟨W, hWk,
          (healing_phase_frontier_root (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef) (obs :=
            obs) (cert := cert) (inv := inv) crossing hy hWk
            (hhW.trans hmax.symm)).1, hhW.trans hmax.symm,
          by rw [hJ hJC]; exact hoff⟩
      · exact ⟨C, hCk,
          (healing_phase_frontier_root (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef) (obs :=
            obs) (cert := cert) (inv := inv) crossing hy hCk
            (hhC.trans hmax.symm)).1, hhC.trans hmax.symm, hJC⟩
    refine ⟨hmax, hc, ?_⟩
    change (decide ((O.controls (V2.D.Run.stateBefore E rho k y)).H = (O.controls
      (V2.D.Run.stateBefore E rho k y)).j + 1) &&
      !(O.controls (V2.D.Run.stateBefore E rho k y)).contest) = false
    rw [hc]
    simp only [Bool.not_true, Bool.and_false]


include obs cert inv justif keep positive coreLaws erasePreceq in
/-- DC: INTENTIONAL. Settlement uses the actual selected receipt at ev.time + delta.
The joined tick stays between delta and two delta after the event; the result starts at 3 delta. -/
theorem healing_settle_start_on (crossing : RXing R E rho O)
    (hs : V2.D.ScheduleWellFormed E rho) (mono : FGRunOrderLaws E rho R)
    (hdelta : E.Δ = T.delta) (gst : E.t_GST ≤ Jst)
    (awake : ∀ y ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake y t = true)
    (joinedTick : ∀ iy y t, y ∈ rho.honest →
      rho.events[iy]? = some (.tick y t) → t ≤ rho.horizon →
      E.t_GST ≤ slotStartZ T (((slotAt T t : Slot) : Int) - 1) →
      joined (P.clock (V2.D.Run.stateBefore E rho iy y) t) = true)
    (readyCut : ∀ t, Jst ≤ t →
      E.t_GST ≤ slotStartZ T (((slotAt T t : Slot) : Int) - 1))
    (hServices : ∀ i (ev : V2.Event V (P.Object)) m,
      rho.events[i]? = some ev → Jst ≤ ev.time → 1 ≤ m →
      frontierAtIdx R E rho (i + 1) = m → ev.time + T.delta ≤ rho.horizon →
      PhaseWitnessReceiptScope R E rho O joined receipt (i + 1) m (ev.time + T.delta))
    (receiptHeld : ∀ W d y, y ∈ rho.honest → receipt (R.erase W) d y →
      W ∈ (R.core (rho.stateBeforeTime E d y)).fg.TF) :
    ∀ i ev v m kind, rho.events[i]? = some ev →
      Jst ≤ ev.time → ev.time + 3 * T.delta ≤ v → v ≤ rho.horizon → 1 ≤ m →
      frontierAtIdx R E rho (i + 1) = m → AttemptPhaseAt R E rho O (i + 1) m kind →
      (∀ j, i < j → j < timeIdx rho v → ¬ EffectiveEvent R E rho O j) →
      ∃ J,
        let root := match kind with | .gap => none | .topJ => some J | .contest => none
        let contested := match kind with | .gap => false | .topJ => false | .contest => true
        PhaseInterval R E rho O (ev.time + 3 * T.delta) v m root contested ∧
        (∀ y s nd, y ∈ rho.honest → ev.time + 3 * T.delta ≤ T.vote s →
          T.vote s ≤ v →
          postClock E rho y (T.vote s) = some nd →
          SettledPhaseFrame R O nd m root contested) := by
  rcases O with ⟨height, finality, controls, viable⟩
  have hc0 : controls = fun nd => treeStoreControlsView height (R.core nd).fg :=
    funext obs.controls_eq
  have hv0 : viable = fun nd X => treeStoreFrameView height (R.core nd).fg X :=
    funext fun nd => funext (obs.viable_eq nd)
  subst controls viable
  let O : FGObservationReads R :=
    ⟨height, finality, (fun nd => treeStoreControlsView height (R.core nd).fg),
      fun nd X => treeStoreFrameView height (R.core nd).fg X⟩
  intro i (ev : V2.Event V (P.Object)) v m kind hi hready hu hv hm hfront hkind hquiet
  -- Restate the event times at the object type of the relay lemmas.
  have hready : Jst ≤ ev.time := hready
  have hu : ev.time + 3 * T.delta ≤ v := hu
  have hgst : E.t_GST ≤ ev.time := gst.trans hready
  have hpos := positive
  have hij0 : i < V2.D.Run.idxBefore rho (ev.time + T.delta) :=
    (Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mpr (lt_add_of_pos_right _ hpos)
  have hdv : ev.time + T.delta ≤ v := by
    simp only [Time] at *
    omega
  have hj0v : V2.D.Run.idxBefore rho (ev.time + T.delta) ≤ timeIdx rho v :=
    phase_cut_le_time rho hdv
  have hhor : ev.time + T.delta ≤ rho.horizon := hdv.trans hv
  have hwin := healing_phase_window_all (R := R) (E := E) (rho := rho) (O := O) mono hfront hquiet
  have hcap (k : Nat) (hk : V2.D.Run.idxBefore rho (ev.time + T.delta) ≤ k)
      (hkv : k ≤ timeIdx rho v) :
      frontierAtIdx R E rho k = m := (hwin k (by omega) hkv).1
  -- Every carrier held at i + 1 is held by every honest node in the window.
  have relay {x : V} {W : FGBlock (Fin n)} (hW : HeldAt R E rho (i + 1) x W)
      (hh : (O.height W).h = m)
      (hReceipt : WitnessReceiptScope R E rho joined receipt W (ev.time + T.delta)) {k : Nat} {y :
        V}
      (hk : V2.D.Run.idxBefore rho (ev.time + T.delta) ≤ k) (hy : y ∈ rho.honest) :
      W ∈ (R.core (V2.D.Run.stateBefore E rho k y)).fg.TF := by
    let d := V2.D.Run.idxBefore rho (ev.time + T.delta)
    have hMax : (R.core (V2.D.Run.stateBefore E rho d y)).fg.h_max ≤ m := by
      have hm0 := healing_phase_local_le_frontier (R := R) (E := E) (rho := rho) (i := d) hy
      exact hm0.trans_eq (hcap d le_rfl hj0v)
    obtain ⟨Kc, hKc, hKcF⟩ := (inv d y).Fcar
    have hLow := (healing_phase_finality_le (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef)
      (cert := cert) (inv := inv) hKc hKcF).trans_lt
      (healing_phase_justified_lt (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef) (cert :=
        cert) (inv := inv) d y)
    have hWD := keep (i + 1) d (show i + 1 ≤ d from by
      dsimp [d]; omega) x hW.2
    have hFW := crossing d d y x Kc W hy le_rfl hKc hKcF ⟨hW.1, hWD⟩
      (by simp only [Height, O] at *; omega)
    let n := ((ev.time + T.delta) / T.delta).toNat + 1
    let t := (n : Time) * T.delta
    have hnonneg : 0 ≤ ev.time + T.delta := by linarith [E.t_GST_nonneg]
    have hquot := Int.ediv_nonneg hnonneg positive.le
    have hrem := Int.emod_nonneg (ev.time + T.delta) (ne_of_gt positive)
    have hremLt := Int.emod_lt_of_pos (ev.time + T.delta) positive
    have he := Int.mul_ediv_add_emod (ev.time + T.delta) T.delta
    have ht : ev.time + T.delta ≤ t ∧ t ≤ ev.time + 2 * T.delta := by
      dsimp [t, n]
      rw [Int.toNat_of_nonneg hquot]
      constructor <;> nlinarith
    have hth : t ≤ rho.horizon := by linarith [positive]
    obtain ⟨iy, hiy⟩ := List.mem_iff_getElem?.mp
      (hs.tick_total y hy t ⟨n, by rw [hdelta]⟩
        (by dsimp [t]; exact mul_nonneg (Int.natCast_nonneg n) positive.le) hth
        (awake y hy t (by linarith [positive]) hth))
    have hjoin := joinedTick iy y t hy hiy hth (readyCut t (by linarith [positive]))
    have hFloor' : Block.Preceq
        (R.erase (R.core (rho.stateBeforeTime E (ev.time + T.delta) y)).fg.F) (R.erase W) := by
      rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
      exact erasePreceq hFW
    have h0 := receiptHeld W (ev.time + T.delta) y hy
      (hReceipt.atRead iy y t hy hiy hjoin ht.1 hFloor')
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at h0
    exact keep _ _ hk y h0
  have wit := hServices i ev m hi hready hm hfront hhor
  have result := phase_settle_from_carriers (R := R) (E := E) (rho := rho) (O := O)
    (Ef := Ef) (T := T) (i := i) (ev := ev) (v := v) (m := m) (kind := kind)
    (obs := obs) (cert := cert) (inv := inv) (justif := justif) (keep := keep)
    (positive := positive) (coreLaws := coreLaws) crossing hs hu hv hm
    (by omega) hwin hkind
    (by
      obtain ⟨x, W, hW, hh, hr⟩ := wit.frontier
      exact ⟨x, W, hW, hh, fun y hy => relay hW hh hr le_rfl hy⟩)
    (by
      intro ht
      obtain ⟨x, C, hC, hh, hj, hJ, hr⟩ := wit.top ht
      exact ⟨x, C, hC, hh, hj, hJ, fun y hy => relay hC hh hr le_rfl hy⟩)
    (by
      intro hc
      obtain ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff, hrC, hrW⟩ := wit.contest hc
      exact ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff,
        fun y hy => relay hC hhC hrC le_rfl hy, fun y hy => relay hW hhW hrW le_rfl hy⟩)
  cases kind <;> exact result

end AvailableChain.FGCompose
end
