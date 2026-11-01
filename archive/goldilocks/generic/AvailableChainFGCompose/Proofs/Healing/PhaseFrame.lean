module
public import AvailableChainFGCompose.Statements.ChannelLaws
public import AvailableChainFGCompose.Statements.Phase
public import AvailableChainKitFG.StoreBounds
public import AvailableChainKitFG.FrameGeometry

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

omit [DecidableEq V] in
/-- SAME: a strict time prefix is contained in its inclusive prefix. -/
private theorem phase_strict_le_inclusive (rho : V2.D.Run V P) (t : Time) :
    V2.D.Run.idxBefore rho t ≤ timeIdx rho t := by
  change (rho.events.filter (fun e => decide (e.time < t))).length ≤
    (rho.events.filter (fun e => decide (e.time ≤ t))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left fun e _ he => decide_eq_true (of_decide_eq_true he).le

include inv in
/-- Blueprint 21:1193–1209; plan S20, H-PHASE/P4. DC: SAME cache height bound. -/
theorem healing_phase_height_le {i : Nat} {x : V} {W : FGBlock (Fin n)}
    (hW : W ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF) :
    (O.height W).h ≤ (R.core (V2.D.Run.stateBefore E rho i x)).fg.h_max := by
  exact KitFG.store_height_le (O.height) (O.finality)
    (R.core (V2.D.Run.stateBefore E rho i x)).fg (inv i x) hW

include cert inv in
/-- Blueprint 21:1193–1209; plan S20, H-PHASE/P4. DC: SAME strict cache bound. -/
theorem healing_phase_justified_lt (i : Nat) (x : V) :
    (R.core (V2.D.Run.stateBefore E rho i x)).fg.h_j < (R.core (V2.D.Run.stateBefore E rho i
      x)).fg.h_max := by
  exact KitFG.store_justified_lt Ef (O.height) (O.finality)
    (cert) (R.core (V2.D.Run.stateBefore E rho i x)).fg
    (inv i x)

include cert inv in
/-- Blueprint 21:1222–1235; plan S20, H-PHASE/P4.
DC: INTENTIONAL the bound reads the accepted W certificate, not the block F. -/
theorem healing_phase_finality_le {i : Nat} {x : V} {K : FGBlock (Fin n)}
    (hK : K ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF)
    (hF : (O.finality K).F = (R.core (V2.D.Run.stateBefore E rho i x)).fg.F) :
    (O.finality K).h_F ≤ (R.core (V2.D.Run.stateBefore E rho i x)).fg.h_j := by
  exact KitFG.store_finality_le Ef (O.height) (O.finality)
    (cert) (R.core (V2.D.Run.stateBefore E rho i x)).fg
    (inv i x) hK hF

include cert inv in
/-- Blueprint 21:1193–1209; plan S20, H-PHASE/P4.
DC: SAME a nonempty cumulative store attains its frontier, including height one. -/
theorem healing_phase_frontier_witness (i : Nat) (x : V) :
    ∃ W ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF,
      (O.height W).h = (R.core (V2.D.Run.stateBefore E rho i x)).fg.h_max := by
  exact KitFG.store_frontier_witness Ef (O.height) (O.finality)
    (cert) (R.core (V2.D.Run.stateBefore E rho i x)).fg
    (inv i x)

include obs cert inv in
/-- Blueprint 21:1153–1171, 1200–1209; plan S20, H-PHASE/P5.
DC: INTENTIONAL live controls and accepted W finality carrier.
Assembly supplies RXing from the foundation final-lock producer. -/
theorem healing_phase_frontier_root (crossing : RXing R E rho O)
    {i : Nat} {x : V} {B : FGBlock (Fin n)} (hx : x ∈ rho.honest)
    (hB : B ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF)
    (hh : (O.height B).h = (O.controls (V2.D.Run.stateBefore E rho i x)).H) :
    FGBlock.Preceq (R.core (V2.D.Run.stateBefore E rho i x)).fg.F B ∧
      FGBlock.Preceq (O.controls (V2.D.Run.stateBefore E rho i x)).Z B := by
  rcases O with ⟨height, finality, controls, viable⟩
  have hc0 : controls = fun nd => treeStoreControlsView height (R.core nd).fg :=
    funext obs.controls_eq
  have hv0 : viable = fun nd X => treeStoreFrameView height (R.core nd).fg X :=
    funext fun nd => funext (obs.viable_eq nd)
  subst controls viable
  let O : FGObservationReads R :=
    ⟨height, finality, (fun nd => treeStoreControlsView height (R.core nd).fg),
      fun nd X => treeStoreFrameView height (R.core nd).fg X⟩
  let st := R.core (V2.D.Run.stateBefore E rho i x)
  obtain ⟨K, hK, hKF⟩ := (inv i x).Fcar
  have hlt := (healing_phase_finality_le (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef) (cert
    := cert) (inv := inv) hK hKF).trans_lt
    (healing_phase_justified_lt (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef) (cert := cert)
      (inv := inv) i x)
  have hFB : FGBlock.Preceq st.fg.F B := crossing i i x x K B hx le_rfl hK hKF
    ⟨hx, hB⟩ (hlt.trans_eq hh.symm)
  refine ⟨hFB, ?_⟩
  change FGBlock.Preceq (treeStoreControlsView O.height st.fg).Z B
  unfold Controls.Z
  split
  · rename_i hroot
    have hr := Bool.and_eq_true_iff.mp hroot
    have ht : st.fg.h_max = st.fg.h_j + 1 := of_decide_eq_true hr.1
    have hn : (treeStoreControlsView O.height st.fg).contest = false := by
      simpa using congrArg Bool.not hr.2
    by_contra hnot
    have hc : (treeStoreControlsView O.height st.fg).contest = true := by
      change (decide (st.fg.h_max = st.fg.h_j + 1) && decide _) = true
      exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true ht, decide_eq_true ⟨B, hB, hFB, hh, hnot⟩⟩
    rw [hn] at hc
    contradiction
  · exact hFB

include obs cert inv in
/-- Blueprint 21:1153–1171, 1200–1209; plan S20, H-PHASE/P5.
DC: INTENTIONAL membership uses the supplied view and the live controls.
This proves the fifth frozen RPhase clause; its path premise is not needed. -/
theorem healing_frontier_mem (crossing : RXing R E rho O)
    (i : Nat) (x : V) (m : Nat) (X : Finset (FGBlock (Fin n))) (B : FGBlock (Fin n))
    (hx : x ∈ rho.honest) (_hi : i ≤ rho.events.length) (_hm : 1 ≤ m)
    (hH : (O.controls (V2.D.Run.stateBefore E rho i x)).H = m) (hX : X ⊆ (R.core
      (V2.D.Run.stateBefore E rho i x)).fg.TF)
    (hB : B ∈ X) (_hpath : ∀ A, FGBlock.Preceq A B → A ∈ X)
    (hh : (O.height B).h = m) :
    FGBlock.Preceq (O.controls (V2.D.Run.stateBefore E rho i x)).Z B ∧ B ∈ O.viable
      (V2.D.Run.stateBefore E rho i x) X := by
  rcases O with ⟨height, finality, controls, viable⟩
  have hc0 : controls = fun nd => treeStoreControlsView height (R.core nd).fg :=
    funext obs.controls_eq
  have hv0 : viable = fun nd X => treeStoreFrameView height (R.core nd).fg X :=
    funext fun nd => funext (obs.viable_eq nd)
  subst controls viable
  let O : FGObservationReads R :=
    ⟨height, finality, (fun nd => treeStoreControlsView height (R.core nd).fg),
      fun nd X => treeStoreFrameView height (R.core nd).fg X⟩
  obtain ⟨hF, hZ⟩ := healing_phase_frontier_root (R := R) (E := E) (rho := rho) (O := O) (Ef :=
    Ef) (obs := obs) (cert := cert) (inv := inv) crossing hx (hX hB) (hh.trans hH.symm)
  refine ⟨hZ, (KitFG.mem_filteredFromView _ _ _ _).mpr ⟨hB, hF, hZ, B, hB,
    KitFG.preceq_refl B, ?_⟩⟩
  change (if (O.controls (V2.D.Run.stateBefore E rho i x)).contest then (O.controls
    (V2.D.Run.stateBefore E rho i x)).H
    else (O.controls (V2.D.Run.stateBefore E rho i x)).H - 1) ≤ (O.height B).h
  rw [hH, hh]
  split <;> (simp only [Height] at *; omega)

include obs cert inv in
/-- Blueprint 21:1193–1235; plan S20, H-PHASE/P4.
DC: INTENTIONAL the frame includes a W certificate below its floor.
This local form does not require a settlement time or a height-two bootstrap. -/
theorem healing_phase_frame (crossing : RXing R E rho O)
    {i : Nat} {x : V} {m : Nat} {J : Option (FGBlock (Fin n))} {contested : Bool}
    (hx : x ∈ rho.honest) (hm : 1 ≤ m)
    (hH : (O.controls (V2.D.Run.stateBefore E rho i x)).H = m)
    (hc : (O.controls (V2.D.Run.stateBefore E rho i x)).contest = contested)
    (hr : match J with
      | some B => (O.controls (V2.D.Run.stateBefore E rho i x)).rootIsJ = true ∧ (O.controls
        (V2.D.Run.stateBefore E rho i x)).J = B
      | none => (O.controls (V2.D.Run.stateBefore E rho i x)).rootIsJ = false) :
    SettledPhaseFrame R O (V2.D.Run.stateBefore E rho i x) m J contested := by
  rcases O with ⟨height, finality, controls, viable⟩
  have hc0 : controls = fun nd => treeStoreControlsView height (R.core nd).fg :=
    funext obs.controls_eq
  have hv0 : viable = fun nd X => treeStoreFrameView height (R.core nd).fg X :=
    funext fun nd => funext (obs.viable_eq nd)
  subst controls viable
  let O : FGObservationReads R :=
    ⟨height, finality, (fun nd => treeStoreControlsView height (R.core nd).fg),
      fun nd X => treeStoreFrameView height (R.core nd).fg X⟩
  let st := R.core (V2.D.Run.stateBefore E rho i x)
  have hj := healing_phase_justified_lt (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef) (cert
    := cert) (inv := inv) i x
  change st.fg.h_max = m at hH
  change (treeStoreControlsView O.height st.fg).contest = contested at hc
  change st.fg.h_j < st.fg.h_max at hj
  refine ⟨hH, hc, ?_, ?_, ?_⟩
  · change (if (treeStoreControlsView O.height st.fg).contest then st.fg.h_max else st.fg.h_max -
    1) = _
    rw [hc, hH]
  · cases J with
    | some B =>
      change (treeStoreControlsView O.height st.fg).rootIsJ = true ∧ (treeStoreControlsView
        O.height st.fg).J = B at hr
      obtain ⟨hr, hJ⟩ := hr
      have hb := Bool.and_eq_true_iff.mp hr
      have ht : st.fg.h_max = st.fg.h_j + 1 := of_decide_eq_true hb.1
      have hn : (treeStoreControlsView O.height st.fg).contest = false := by
        simpa using congrArg Bool.not hb.2
      refine ⟨hr, hJ, ?_, ?_, hc.symm.trans hn, ?_⟩
      · change (if (treeStoreControlsView O.height st.fg).rootIsJ then _ else _) = B
        rw [hr]
        exact hJ
      · change st.fg.h_j + 1 = m
        (simp only [Height] at *; omega)
      · exact hJ ▸ (inv i x).FJ
    | none =>
      change (treeStoreControlsView O.height st.fg).rootIsJ = false at hr
      have hZ : (treeStoreControlsView O.height st.fg).Z = st.fg.F := by
        change (if (treeStoreControlsView O.height st.fg).rootIsJ then _ else _) = _
        rw [hr]
        rfl
      have hcases : (contested = false ∧ st.fg.h_j + 2 ≤ m) ∨
          (contested = true ∧ st.fg.h_j + 1 = m) := by
        cases he : contested with
        | true =>
          have ht : st.fg.h_max = st.fg.h_j + 1 :=
            of_decide_eq_true (Bool.and_eq_true_iff.mp (hc.trans he)).1
          exact Or.inr ⟨rfl, ht.symm.trans hH⟩
        | false =>
          left
          refine ⟨rfl, ?_⟩
          by_contra hnot
          have ht : st.fg.h_max = st.fg.h_j + 1 := by (simp only [Height] at *; omega)
          have hrt : (treeStoreControlsView O.height st.fg).rootIsJ = true := by
            change (decide (st.fg.h_max = st.fg.h_j + 1) &&
              !(treeStoreControlsView O.height st.fg).contest) = true
            rw [hc, he]
            simp only [ht, decide_true, Bool.not_false, Bool.and_self]
          rw [hr] at hrt
          contradiction
      refine ⟨hr, hZ, ?_, hcases⟩
      obtain ⟨K, hK, hKF⟩ := (inv i x).Fcar
      refine ⟨K, hK, hKF, ?_⟩
      have hf := healing_phase_finality_le (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef)
        (cert := cert) (inv := inv) hK hKF
      change (O.finality K).h_F ≤ st.fg.h_j at hf
      change (O.finality K).h_F <
        (if (treeStoreControlsView O.height st.fg).contest then st.fg.h_max else st.fg.h_max - 1)
      rw [hc]
      rcases hcases with ⟨rfl, hl⟩ | ⟨rfl, hl⟩ <;>
        simp only [Bool.false_eq_true, ↓reduceIte] <;> (simp only [Height] at *; omega)
  · obtain ⟨W, hW, hh⟩ := healing_phase_frontier_witness (R := R) (E := E) (rho := rho) (O := O)
      (Ef := Ef) (cert := cert) (inv := inv) i x
    exact ⟨W, hW, hh.trans hH,
      (healing_phase_frontier_root (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef) (obs := obs)
        (cert := cert) (inv := inv) crossing hx hW hh).2⟩

include obs cert inv in
/-- Blueprint 21:1193–1235; plan S20, H-PHASE/P4.
DC: INTENTIONAL live settled frame with an accepted finality carrier.
This is the fourth frozen RPhase clause. Assembly supplies RXing. -/
theorem healing_settled_frame (crossing : RXing R E rho O)
    (u v : Time) (m : Nat) (J : Option (FGBlock (Fin n))) (contested : Bool)
    (_hgst : E.t_GST ≤ u) (hp : PhaseInterval R E rho O u v m J contested)
    (i : Nat) (x : V) (hui : timeIdx rho u ≤ i) (hiv : i ≤ timeIdx rho v)
    (hx : x ∈ rho.honest) :
    SettledPhaseFrame R O (V2.D.Run.stateBefore E rho i x) m J contested := by
  have hui' : V2.D.Run.idxBefore rho u ≤ i := (phase_strict_le_inclusive rho u).trans hui
  obtain ⟨hH, hc, hr⟩ := hp.2.2.2 i x hui' hiv hx
  exact healing_phase_frame (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef) (obs := obs) (cert
    := cert) (inv := inv) crossing hx hp.2.2.1 hH hc hr

include obs cert inv in
/-- The fourth RPhase clause uses the joined healing phase domain. -/
theorem healing_settled_frame_ready (crossing : RXing R E rho O)
    (u v : Time) (m : Nat) (J : Option (FGBlock (Fin n))) (contested : Bool)
    (_hready : Jst ≤ u) (hp : PhaseInterval R E rho O u v m J contested)
    (i : Nat) (x : V) (hui : timeIdx rho u ≤ i) (hiv : i ≤ timeIdx rho v)
    (hx : x ∈ rho.honest) :
    SettledPhaseFrame R O (V2.D.Run.stateBefore E rho i x) m J contested := by
  have hui' : V2.D.Run.idxBefore rho u ≤ i := (phase_strict_le_inclusive rho u).trans hui
  obtain ⟨hH, hc, hr⟩ := hp.2.2.2 i x hui' hiv hx
  exact healing_phase_frame (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef) (obs := obs) (cert
    := cert) (inv := inv) crossing hx hp.2.2.1 hH hc hr


end AvailableChain.FGCompose
end
