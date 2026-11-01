module
public import AvailableChainFGCompose.Proofs.Healing.PhaseFrame

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

/-- Blueprint 21:1193–1209; plan S20, H-PHASE/P1. DC: SAME global cache bound. -/
theorem healing_phase_local_le_frontier {i : Nat} {x : V} (hx : x ∈ rho.honest) :
    (R.core (V2.D.Run.stateBefore E rho i x)).fg.h_max ≤ frontierAtIdx R E rho i := by
  change (R.core (V2.D.Run.stateBefore E rho i x)).fg.h_max ≤
    rho.honest.sup (fun x => (R.core (V2.D.Run.stateBefore E rho i x)).fg.h_max)
  exact Finset.le_sup (f := fun x => (R.core (V2.D.Run.stateBefore E rho i x)).fg.h_max) hx

include cert inv in
/-- Blueprint 21:1193–1209; plan S20, H-PHASE/P1.
DC: SAME a top cache persists below a fixed global cap. Assembly supplies RMono. -/
theorem healing_phase_top_persist_all (mono : FGRunOrderLaws E rho R)
    {i j m : Nat} {x : V} (hx : x ∈ rho.honest) (hij : i ≤ j)
    (hcap : frontierAtIdx R E rho j = m)
    (htop : (R.core (V2.D.Run.stateBefore E rho i x)).fg.h_j + 1 = m) :
    (R.core (V2.D.Run.stateBefore E rho j x)).fg.h_j + 1 = m ∧
      (R.core (V2.D.Run.stateBefore E rho j x)).fg.h_max = m := by
  have hlo := KitFG.fst_le_of_lexKey_le (mono.mono i j x hx hij).2.1
  have hhi := healing_phase_justified_lt (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef) (cert
    := cert) (inv := inv) j x
  have hb := healing_phase_local_le_frontier (R := R) (E := E) (rho := rho) (i := j) hx
  (simp only [Height] at *; omega)

include cert inv in
theorem healing_phase_top_persist (mono : V2.D.NoRestart rho → FGRunOrderLaws E rho R) (hnr :
  V2.D.NoRestart rho)
    {i j m : Nat} {x : V} (hx : x ∈ rho.honest) (hij : i ≤ j)
    (hcap : frontierAtIdx R E rho j = m)
    (htop : (R.core (V2.D.Run.stateBefore E rho i x)).fg.h_j + 1 = m) :
    (R.core (V2.D.Run.stateBefore E rho j x)).fg.h_j + 1 = m ∧
      (R.core (V2.D.Run.stateBefore E rho j x)).fg.h_max = m :=
  healing_phase_top_persist_all (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef) (cert := cert)
    (inv := inv) (mono hnr) hx hij hcap htop

omit [DecidableEq V] in
/-- Blueprint 21:1105–1113, 1193–1209; plan S20, H-PHASE/P1.
DC: SAME two equal-height entries on one path are equal.
At justified height zero both entries are genesis (B21, m = 1). -/
theorem healing_phase_entries_eq (H : FGHeightView (Fin n)) (f : FGFinalityView (Fin n))
    (cert : FGCertificateLaws Ef H f) (justif : FGJustificationLaws H) {C D W : FGBlock (Fin n)}
    (hh : (H C).h_j = (H D).h_j)
    (hC : FGBlock.Preceq (H C).J W)
    (hD : FGBlock.Preceq (H D).J W) :
    (H C).J = (H D).J := by
  exact KitFG.store_entries_eq Ef (H) (f)
    (cert) (justif) hh hC hD

include obs cert inv justif keep in
/-- Blueprint 21:1105–1113, 1193–1209; plan S20, H-PHASE/P1.
DC: INTENTIONAL a contest uses cumulative live evidence.
If the cached J changes, its old carrier supplies the off-J witness. -/
theorem healing_phase_contest_persist_of_crossing_all (crossing : RXing R E rho O)
    (mono : FGRunOrderLaws E rho R)
    {i j m : Nat} {x : V}
    (hx : x ∈ rho.honest) (hij : i ≤ j)
    (hcap : frontierAtIdx R E rho j = m)
    (hH : (O.controls (V2.D.Run.stateBefore E rho i x)).H = m)
    (hcontest : (O.controls (V2.D.Run.stateBefore E rho i x)).contest = true) :
    (O.controls (V2.D.Run.stateBefore E rho j x)).H = m ∧ (O.controls (V2.D.Run.stateBefore E rho
      j x)).contest = true := by
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
  let st' := R.core (V2.D.Run.stateBefore E rho j x)
  change (decide (st.fg.h_max = st.fg.h_j + 1) && decide _) = true at hcontest
  obtain ⟨ht, he⟩ := Bool.and_eq_true_iff.mp hcontest
  have ht : st.fg.h_max = st.fg.h_j + 1 := of_decide_eq_true ht
  have he : ∃ W ∈ st.fg.TF, FGBlock.Preceq st.fg.F W ∧ (O.height W).h = st.fg.h_max ∧
      ¬ FGBlock.Preceq st.fg.J W := of_decide_eq_true he
  have htop : st.fg.h_j + 1 = m := ht.symm.trans hH
  obtain ⟨htop', hmax'⟩ := healing_phase_top_persist_all (R := R) (E := E) (rho := rho) (O := O)
    (Ef := Ef) (cert := cert) (inv := inv) mono hx hij hcap htop
  refine ⟨hmax', ?_⟩
  change (decide (st'.fg.h_max = st'.fg.h_j + 1) && decide _) = true
  refine Bool.and_eq_true_iff.mpr ⟨decide_eq_true (hmax'.trans htop'.symm), decide_eq_true ?_⟩
  have hsub := keep i j hij x
  by_cases hJ : st.fg.J = st'.fg.J
  · obtain ⟨W, hW, _hFW, hh, hn⟩ := he
    have hh' := hh.trans (hH.trans hmax'.symm)
    exact ⟨W, hsub hW,
      (healing_phase_frontier_root (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef) (obs := obs)
        (cert := cert) (inv := inv) crossing hx (hsub hW) hh').1,
      hh', hJ ▸ hn⟩
  · obtain ⟨C, hC, _, hjC, hJC⟩ := (inv i x).pair.1
    obtain ⟨D, _, _, hjD, hJD⟩ := (inv j x).pair.1
    change st.fg.J = _ at hJC
    change st'.fg.J = _ at hJD
    change st.fg.h_j = _ at hjC
    change st'.fg.h_j = _ at hjD
    change st'.fg.h_j + 1 = m at htop'
    have hhC := (cert).height.justified_below_height C
    have hhCm := healing_phase_height_le (R := R) (E := E) (rho := rho) (O := O) (inv := inv) hC
    have hc : (O.height C).h = st'.fg.h_max := by
      change st.fg.h_j = _ at hjC
      change (O.height C).h ≤ st.fg.h_max at hhCm
      change st.fg.h_max = m at hH
      change st'.fg.h_max = m at hmax'
      (simp only [Height, O] at *; omega)
    refine ⟨C, hsub hC,
      (healing_phase_frontier_root (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef) (obs := obs)
        (cert := cert) (inv := inv) crossing hx (hsub hC) hc).1, hc, ?_⟩
    intro hDC
    apply hJ
    rw [hJC, hJD]
    apply healing_phase_entries_eq (H := O.height) (f := O.finality) (Ef := Ef) (cert := cert)
      (justif := justif) (W := C)
    · (simp only [Height, O] at *; omega)
    · exact KitFG.preceq_trans ((cert).height.justified_preceq_entry C)
        ((cert).height.entry_preceq C)
    · exact hJD ▸ hDC

include obs cert inv justif keep in
theorem healing_phase_contest_persist_of_crossing (crossing : RXing R E rho O)
    (mono : V2.D.NoRestart rho → FGRunOrderLaws E rho R)
    (hnr : V2.D.NoRestart rho) {i j m : Nat} {x : V}
    (hx : x ∈ rho.honest) (hij : i ≤ j)
    (hcap : frontierAtIdx R E rho j = m)
    (hH : (O.controls (V2.D.Run.stateBefore E rho i x)).H = m)
    (hcontest : (O.controls (V2.D.Run.stateBefore E rho i x)).contest = true) :
    (O.controls (V2.D.Run.stateBefore E rho j x)).H = m ∧ (O.controls (V2.D.Run.stateBefore E rho
      j x)).contest = true :=
  healing_phase_contest_persist_of_crossing_all (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef)
    (obs := obs) (cert := cert) (inv := inv) (justif := justif) (keep := keep) crossing (mono hnr)
    hx hij hcap hH hcontest

include obs cert inv justif keep in
/-- Blueprint 21:1091–1113, 1193–1209; plan S20, H-PHASE/P1.
DC: INTENTIONAL gap, top J, contest are the live cumulative phase bits.
This is the first frozen RPhase clause. Assembly supplies RMono. -/
theorem healing_phase_order_of_crossing_all (crossing : RXing R E rho O)
    (mono : FGRunOrderLaws E rho R)
    (a b m : Nat) (_hab : a ≤ b) (_hb : b ≤ rho.events.length) (_hm : 1 ≤ m)
    (hfixed : ∀ i, a ≤ i → i ≤ b → frontierAtIdx R E rho i = m) :
    (∀ i j, a ≤ i → i ≤ j → j ≤ b →
      (TopEvidence R E rho i m → TopEvidence R E rho j m) ∧
      (ContestEvidence R E rho O i m → ContestEvidence R E rho O j m)) ∧
    (∀ i, a ≤ i → i ≤ b → ContestEvidence R E rho O i m → TopEvidence R E rho i m) := by
  rcases O with ⟨height, finality, controls, viable⟩
  have hc0 : controls = fun nd => treeStoreControlsView height (R.core nd).fg :=
    funext obs.controls_eq
  have hv0 : viable = fun nd X => treeStoreFrameView height (R.core nd).fg X :=
    funext fun nd => funext (obs.viable_eq nd)
  subst controls viable
  let O : FGObservationReads R :=
    ⟨height, finality, (fun nd => treeStoreControlsView height (R.core nd).fg),
      fun nd X => treeStoreFrameView height (R.core nd).fg X⟩
  constructor
  · intro i j hai hij hjb
    have hcap := hfixed j (hai.trans hij) hjb
    constructor
    · rintro ⟨x, hx, ht⟩
      exact ⟨x, hx, (healing_phase_top_persist_all (R := R) (E := E) (rho := rho) (O := O) (Ef :=
        Ef) (cert := cert) (inv := inv) mono hx hij hcap ht).1⟩
    · rintro ⟨x, hx, hH, hc⟩
      exact ⟨x, hx, healing_phase_contest_persist_of_crossing_all
        (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef) (obs := obs)
        (cert := cert) (inv := inv) (justif := justif) (keep := keep)
        crossing mono hx hij hcap hH hc⟩
  · rintro i _ _ ⟨x, hx, hH, hc⟩
    have ht : (R.core (V2.D.Run.stateBefore E rho i x)).fg.h_max = (R.core (V2.D.Run.stateBefore E
      rho i x)).fg.h_j + 1 :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
    exact ⟨x, hx, ht.symm.trans hH⟩

include obs cert inv justif keep in
theorem healing_phase_order_of_crossing (crossing : RXing R E rho O)
    (mono : V2.D.NoRestart rho → FGRunOrderLaws E rho R) (hnr : V2.D.NoRestart rho)
    (a b m : Nat) (_hab : a ≤ b) (_hb : b ≤ rho.events.length) (_hm : 1 ≤ m)
    (hfixed : ∀ i, a ≤ i → i ≤ b → frontierAtIdx R E rho i = m) :
    (∀ i j, a ≤ i → i ≤ j → j ≤ b →
      (TopEvidence R E rho i m → TopEvidence R E rho j m) ∧
      (ContestEvidence R E rho O i m → ContestEvidence R E rho O j m)) ∧
    (∀ i, a ≤ i → i ≤ b → ContestEvidence R E rho O i m → TopEvidence R E rho i m) :=
  healing_phase_order_of_crossing_all (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef) (obs :=
    obs) (cert := cert) (inv := inv) (justif := justif) (keep := keep) crossing (mono hnr) a b m
    _hab _hb _hm hfixed


end AvailableChain.FGCompose
end
