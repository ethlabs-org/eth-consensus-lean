module
public import AvailableChainFGCompose.Statements.FinalityHistory
public import AvailableChainKitFG.CausalCapCore
public import AvailableChainKitFG.HeightHistoryTransfer
public import AvailableChainKitFG.WindowRetention
public import AvailableChainKitFG.WindowSelection -- shake: keep (G0 window certificate producer)
public import AvailableChainGeneric.Proofs.V2.Duty.Reads

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P) (T : FGTiming) (D : FGHistoryWireReads S)
variable (Ef : Electorate (Fin n)) (cfg : FGConfig) (H : FGHeightView (Fin n))
variable (f : FGFinalityView (Fin n)) (hb : HeightBridge Ef cfg H)
variable (hc : FGCertificateLaws Ef H f) (horigin : RawHistoryOrigin R S E rho T D)

private theorem d7_honest_seat (u : Row (Fin n))
    (hf : u.signer ∉ historyFaulty S rho) : safetyHolder S rho u.signer ∈ rho.honest := by
  classical
  delta historyFaulty at hf
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
    not_not] using hf

private theorem d7_event_time {j r : Nat} {z : V} {a : Wire}
    (hj : HonestRowAt S E rho T j z r a) : eventTime rho j = some (T.action r) := by
  delta eventTime
  rw [hj.2.1]
  rfl

private theorem d7_matching_height {u : Row (Fin n)} {a : Wire} {y : Nat} {root : BlockId}
    (ha : S.decode a = some u) (hm : u.height_pair.matchesEntry y root = true) :
    historyRowHeight S D a = some y := by
  delta historyRowHeight
  rw [D.decode_height a u ha]
  cases hp : u.height_pair with
  | empty => simp only [hp, NamedHeightPair.matchesEntry] at hm; contradiction
  | vote h U timeout =>
    have hh : h = y := by
      simp only [hp, NamedHeightPair.matchesEntry, decide_eq_true_eq] at hm
      exact hm.1
    exact congrArg some hh

include horigin in
/-- FINAL 22:954–956. Authenticate each raw carrier before its strict cut.
DC: ProposalBridge.lean:324; FG-SA retains the delivery witness. -/
private theorem d7_raw_origin (hs : V2.D.ScheduleWellFormed E rho)
    (B W : FGBlock (Fin n)) (cut : Time) (u : Row (Fin n))
    (hraw : ChainRowsBefore R E rho B cut) (hpath : FGBlock.Preceq W B)
    (hocc : u ∈ W.rows) (hh : safetyHolder S rho u.signer ∈ rho.honest) :
    ∃ j r a t, HonestRowAt S E rho T j (safetyHolder S rho u.signer) r a ∧
      S.decode a = some u ∧ eventTime rho j = some t ∧ t < cut := by
  obtain ⟨x, s, hx, hscut, hW⟩ := hraw W hpath u hocc
  have held : HeldAt R E rho (V2.D.Run.idxBefore rho s) x W := by
    refine ⟨hx, ?_⟩
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho s hs]
    exact hW
  obtain ⟨a, r, ha, har, k, o, t, hki, hk, he⟩ :=
    horigin _ x W held u (mem_chainRows_of_carrier (preceq_refl _) hocc)
  have hsign : RowSigner S rho D.signer a (safetyHolder S rho u.signer) :=
    ⟨u.signer, har, rfl⟩
  obtain ⟨hb, ht⟩ := he _ hsign hh
  obtain ⟨j, _hji, hj⟩ := hb
  have hts := (Gen.V2.Duty.index_lt_idxBefore_iff
    hs hk s).mp hki
  exact ⟨j, r, a, T.action r, hj, ha, d7_event_time S E rho T hj,
    (ht.trans_lt hts).trans hscut⟩

include horigin hb in
/-- FINAL 22:1771–1780. No honest height-y row precedes the first action.
DC: CarrierTimeoutGate.lean:121; FG-SA uses a raw parent-chain cut. -/
theorem noMixedPreBatchParent (q y : Nat) (U X : FGBlock (Fin n))
    (h : PreBatchPrem R S E rho T D Ef H q y U X) : NoMixedOnPath H X y := by
  intro W hWP hm
  obtain ⟨hp, hw, _hj⟩ := hm
  have hne : W ≠ .genesis := by
    intro heq
    subst W
    change (H .genesis).h = y at hp
    rw [hp] at hw
    simp only [Height] at hw
    omega
  obtain ⟨C, u, hCW, hu, hf, hmatch⟩ := crossing_honest_matching_row_of_bridge
    Ef cfg (H) (hb) (historyFaulty S rho)
    y hne hp hw (h.fault_weight)
  obtain ⟨j, r, a, t, hj, ha, ht, hearly⟩ := d7_raw_origin R S E rho T D horigin
    h.schedule X.parent C h.cut u h.rows (preceq_trans hCW hWP) hu
    (d7_honest_seat S rho u hf)
  have hlate := h.noRow j _ r a y t hj (d7_matching_height S D ha hmatch)
    (le_refl _) ht
  exact (not_lt.mpr hlate) (hearly.trans_le h.early)


/-- ROOT-DIGEST W2b. FINAL 22:954–956. Expose the carrier of a raw chain row.
DC: INTENTIONAL: the endpoint need not be held. -/
private theorem d7_carrier (B : FGBlock (Fin n)) (u : Row (Fin n))
    (hu : u ∈ chainRows B) : ∃ W, FGBlock.Preceq W B ∧ u ∈ W.rows := by
  induction B with
  | genesis => exact (Finset.notMem_empty u hu).elim
  | node P s root x rs ih =>
    change u ∈ rs.toFinset ∪ chainRows P at hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact ⟨.node P s root x rs, preceq_refl _, List.mem_toFinset.mp hu⟩
    · obtain ⟨W, hWP, hu⟩ := ih hu
      exact ⟨W, preceq_node_of_preceq s root x rs hWP, hu⟩

include horigin hc in
/-- FINAL 22:948–958. Raw rows before a cut bound the endpoint height.
DC: INTENTIONAL: each raw carrier is authenticated separately. -/
private theorem d7_chain_height_le (hs : V2.D.ScheduleWellFormed E rho)
    (hweight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    (B : FGBlock (Fin n)) (cut : Time) (m : Nat)
    (hraw : ChainRowsBefore R E rho B cut)
    (hrows : ∀ j z r a h t, HonestRowAt S E rho T j z r a →
      historyRowHeight S D a = some h → eventTime rho j = some t → t < cut → h ≤ m) :
    (H B).h ≤ m + 1 := by
  by_contra hn
  obtain ⟨C, _hCB, _hC, Q, hQ, hw⟩ := (hc).height.height_crossing
    B (m + 1) (by simp only [Height]; omega) (by simp only [Height] at *; omega)
  obtain ⟨seat, hseat, hf⟩ := honest_in_quorum Ef (historyFaulty S rho)
    hQ (hweight)
  obtain ⟨W, u, hWB, hu, hsign, hm⟩ := hw seat hseat
  have hfu : u.signer ∉ historyFaulty S rho := hsign ▸ hf
  obtain ⟨j, r, a, t, hj, ha, ht, hearly⟩ := d7_raw_origin R S E rho T D horigin
    hs B W cut u hraw hWB hu (d7_honest_seat S rho u hfu)
  have hb := hrows j _ r a (m + 1) t hj (d7_matching_height S D ha hm) ht hearly
  omega

include horigin hc in
/-- FINAL 22:952–958. A positive W certificate has an honest raw row before the cut.
DC: INTENTIONAL: the active W certificate supplies the exact finality height. -/
private theorem d7_finality_origin (hs : V2.D.ScheduleWellFormed E rho)
    (hweight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    (X : FGBlock (Fin n)) (cut : Time) (y : Nat)
    (hraw : ChainRowsBefore R E rho X cut)
    (hy : 0 < y) (hF : y ≤ (f X).h_F) :
    ∃ j z r a t, HonestRowAt S E rho T j z r a ∧
      historyFinHeight S D a = some (f X).h_F ∧ eventTime rho j = some t ∧ t < cut := by
  let release := fun u : Row (Fin n) => ∃ j r a t,
    HonestRowAt S E rho T j (safetyHolder S rho u.signer) r a ∧
      S.decode a = some u ∧ eventTime rho j = some t ∧ t < cut
  obtain ⟨u, _hu, _hf, ho, hp⟩ := finalityCap_row_of_certificate Ef
    (H) (f) (hc)
    (historyFaulty S rho) (hweight)
    y X release (by
      intro u hu hf
      obtain ⟨W, hWX, hu⟩ := d7_carrier X u hu
      exact d7_raw_origin R S E rho T D horigin hs X W cut u hraw hWX hu
        (d7_honest_seat S rho u hf)) hy hF
  obtain ⟨j, r, a, t, hj, ha, ht, hearly⟩ := ho
  refine ⟨j, _, r, a, t, hj, ?_, ht, hearly⟩
  delta historyFinHeight
  rw [D.decode_finality a u ha, hp]
  rfl


private theorem d7_retained_cross (Ef : Electorate (Fin n)) (cfg : FGConfig)
    (K : Nat) (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K) (H : FGHeightView (Fin n))
    (hH : H = KitFG.Window.certificateHeight Ef cfg K) (y : Nat) (U C : FGBlock (Fin n))
    (hc : JustifiedCross H C U y) : KitFG.Window.RetainedW Ef cfg K C y U := by
  subst H
  obtain ⟨hp, hh, hJ, hj⟩ := hc
  have hCne : C ≠ .genesis := by
    intro heq
    subst C
    change (KitFG.Window.certificateHeight Ef cfg K .genesis).h = y at hp
    rw [hp] at hh
    simp only [Height] at hh
    omega
  cases C with
  | genesis => exact (hCne rfl).elim
  | node P s root x rs =>
    change (KitFG.Window.certificateHeight Ef cfg K P).h = y at hp
    have hp' : (SimplexFG.Window.derive Ef cfg K P).h = y := by
      simpa only [KitFG.Window.certificateHeight_def, KitFG.Window.projectHeight_def] using hp
    have hj' : (SimplexFG.Window.derive Ef cfg K (.node P s root x rs)).h_j = y := by
      simpa only [KitFG.Window.certificateHeight_def, KitFG.Window.projectHeight_def] using hj
    have hJ' : (SimplexFG.Window.derive Ef cfg K (.node P s root x rs)).J = U := by
      simpa only [KitFG.Window.certificateHeight_def, KitFG.Window.projectHeight_def] using hJ
    have ht : SimplexFG.Window.targetQuorum Ef
        (SimplexFG.Window.finalizeWindow Ef
          (KitFG.Window.certificateFolded Ef cfg K (.node P s root x rs))) =
          true := by
      rcases KitFG.Window.window_latest_pair_kept Ef cfg K P s root x rs with kept | crossed
      · have below := (KitFG.Window.windowHeightLaws Ef cfg K hK).justified_below_height P
        simp only [KitFG.Window.projectHeight_def] at below
        rw [← kept.1, hj', hp'] at below
        exact (Nat.lt_irrefl y below).elim
      · exact crossed.2.2
    have latest : (SimplexFG.Window.derive Ef cfg K (.node P s root x rs)).h_j =
        (SimplexFG.Window.finalizeWindow Ef
          (KitFG.Window.certificateFolded Ef cfg K (.node P s root x rs))).h ∧
        (SimplexFG.Window.derive Ef cfg K (.node P s root x rs)).J =
        (SimplexFG.Window.finalizeWindow Ef
          (KitFG.Window.certificateFolded Ef cfg K (.node P s root x rs))).T_h := by
      rw [SimplexFG.Window.derive_def Ef cfg K (.node P s root x rs)]
      dsimp only
      rw [SimplexFG.Window.transition_def]
      change (SimplexFG.Window.process_height_events Ef cfg K
          (KitFG.Window.certificateFolded Ef cfg K (.node P s root x rs))).h_j = _ ∧
        (SimplexFG.Window.process_height_events Ef cfg K
          (KitFG.Window.certificateFolded Ef cfg K (.node P s root x rs))).J = _
      rw [SimplexFG.Window.process_height_events_def, ite_eq_left ht]
      exact ⟨rfl, rfl⟩
    obtain ⟨_hw, older, appended, _hord, _hf⟩ :=
      KitFG.Window.window_target_appended_newest Ef cfg K hne hK P s root x rs ht
    rw [latest.1.symm.trans hj', latest.2.symm.trans hJ'] at appended
    rw [KitFG.Window.RetainedW_def]
    refine ⟨⟨y, U, ∅⟩, ?_, rfl, rfl⟩
    rw [appended]
    exact List.mem_append_right _ (List.mem_singleton_self _)

include horigin hc hb in
/-- FINAL 22:945–958,1218–1223. Fresh raw history fixes the endpoint and retains its W key.
DC: W4FKChainJustification.lean:185; FG-SA also proves the strict W finality bound. -/
theorem justifyFresh_W (K : Nat) (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K)
    (hH : H = KitFG.Window.certificateHeight Ef cfg K)
    (hf_eq : f = KitFG.Window.certificateFinality Ef cfg K)
    (target : TargetJustification Ef H) (q y : Nat) (U X : FGBlock (Fin n)) (hX : X ≠ .genesis)
    (hentry : EntryAt H U y) (hpath : FGBlock.Preceq U X.parent)
    (hcover : (H X.parent).h = y → TargetCoveredByChild Ef H X U y)
    (hnomix : NoMixedOnPath H X y) (h : FreshPrem R S E rho T D Ef q y X) :
    (H X).h = y + 1 ∧ (H X).J = U ∧
      (H X).h_j = y ∧ (f X).h_F < y ∧
      KitFG.Window.RetainedW Ef cfg K X y U := by
  obtain ⟨C, hCX, hc'⟩ := target y U X hX hentry hpath hcover hnomix
  have hy : 0 < y := by
    have hb := (hc).height.one_le_h U
    rw [hentry.1] at hb
    simp only [Height] at *
    omega
  have hlo := (hc).height.h_mono hCX
  rw [hc'.2.1] at hlo
  have hhi := d7_chain_height_le (R := R) (S := S) (E := E) (rho := rho) (T := T) (D := D)
    (Ef := Ef) (H := H) (f := f) (hc := hc) (horigin := horigin) h.schedule h.fault_weight X h.cut y
    h.rows (by
      intro j z r a H t hj ha ht hearly
      by_contra hn
      have hlate := h.noNextRow j z r a H t hj ha (by omega) ht
      exact (not_lt.mpr hlate) (hearly.trans_le h.early))
  have hh : (H X).h = y + 1 := by simp only [Height] at *; omega
  obtain ⟨hJ, hj⟩ := justification_eq_on_plateau_of_bridge Ef cfg
    (H) (hb) hCX (hc'.2.1.trans hh.symm)
  have hJU := hJ.trans hc'.2.2.1
  have hjy := hj.trans hc'.2.2.2
  have hf : (f X).h_F < y := by
    by_contra hn
    obtain ⟨j, z, r, a, t, hj, ha, ht, hearly⟩ :=
      d7_finality_origin (R := R) (S := S) (E := E) (rho := rho) (T := T) (D := D)
        (Ef := Ef) (H := H) (f := f) (hc := hc) (horigin := horigin)
        h.schedule h.fault_weight X h.cut y h.rows hy
        (Nat.le_of_not_gt hn)
    have hlate := h.noFinRow j z r a _ t hj ha (Nat.le_of_not_gt hn) ht
    exact (not_lt.mpr hlate) (hearly.trans_le h.early)
  obtain ⟨e, he, hey, heU⟩ := d7_retained_cross Ef cfg K hne hK H hH y U C hc'
  have hfW : (SimplexFG.Window.derive Ef cfg K X).h_F < y := by
    simpa only [hf_eq, KitFG.Window.certificateFinality_def,
      KitFG.Window.projectFinality_def] using hf
  have hjW : (SimplexFG.Window.derive Ef cfg K X).h_j = y := by
    simpa only [hH, KitFG.Window.certificateHeight_def,
      KitFG.Window.projectHeight_def] using hjy
  obtain ⟨d, hd, hdy, hdU, _⟩ := KitFG.Window.window_retained_of_scalar Ef cfg K hne hK
    C X hCX e he (by rw [hey]; exact hfW)
    (by rw [hjW, hey]; exact Nat.lt_add_of_pos_right (by omega : 0 < K))
  exact ⟨hh, hJU, hjy, hf, d, hd, hdy.trans hey, hdU.trans heU⟩


include horigin hc in
/-- FINAL 22:923–938. A held chain has no crossing above its honest row bound.
DC: INTENTIONAL: timed raw origin replaces a selected-pool bound. -/
private theorem d7_held_height_le (_hs : V2.D.ScheduleWellFormed E rho)
    (hweight : Ef.weightOf (historyFaulty S rho) < Ef.q) (m : Nat) (cut : Time)
    (hrows : ∀ j z r a h t, HonestRowAt S E rho T j z r a →
      historyRowHeight S D a = some h → eventTime rho j = some t → t < cut → h ≤ m)
    (i : Nat) (x : V) (B : FGBlock (Fin n)) (hheld : HeldAt R E rho i x B)
    (hbefore : ∀ k o t, k < i → rho.events[k]? = some (.deliver x o t) → t < cut) :
    (H B).h ≤ m + 1 := by
  by_contra hn
  obtain ⟨C, _hCB, _hC, Q, hQ, hw⟩ := (hc).height.height_crossing
    B (m + 1) (by simp only [Height]; omega) (by simp only [Height] at *; omega)
  obtain ⟨seat, hseat, hf⟩ := honest_in_quorum Ef (historyFaulty S rho)
    hQ (hweight)
  obtain ⟨W, u, hWB, hu, hsign, hm⟩ := hw seat hseat
  have hfu : u.signer ∉ historyFaulty S rho := hsign ▸ hf
  have hhonest := d7_honest_seat S rho u hfu
  obtain ⟨a, r, ha, har, k, o, t, hki, hk, he⟩ :=
    horigin i x B hheld u (mem_chainRows_of_carrier hWB hu)
  have hsigner : RowSigner S rho D.signer a (safetyHolder S rho u.signer) :=
    ⟨u.signer, har, rfl⟩
  obtain ⟨hb, hrt⟩ := he _ hsigner hhonest
  obtain ⟨j, _hji, hj⟩ := hb
  have ht := hrt.trans_lt (hbefore k o t hki hk)
  have bound := hrows j _ r a (m + 1) (T.action r) hj
    (d7_matching_height S D ha hm) (d7_event_time S E rho T hj) ht
  omega

include horigin hc in
/-- FINAL 22:923–938. Strict raw history caps a held block before the cut.
DC: INTENTIONAL: a delivery witness makes the event cut strict. -/
theorem raw_causal_cap_before (hs : V2.D.ScheduleWellFormed E rho)
    (hweight : Ef.weightOf (historyFaulty S rho) < Ef.q) (m : Nat) (cut : Time)
    (hrows : ∀ j z r a h t, HonestRowAt S E rho T j z r a →
      historyRowHeight S D a = some h → eventTime rho j = some t → t < cut → h ≤ m)
    (i : Nat) (x : V) (B : FGBlock (Fin n))
    (hcut : i ≤ V2.D.Run.idxBefore rho cut) (hheld : HeldAt R E rho i x B) :
    (H B).h ≤ m + 1 := by
  apply d7_held_height_le (R := R) (S := S) (E := E) (rho := rho) (T := T) (D := D)
    (Ef := Ef) (H := H) (f := f) (hc := hc) (horigin := horigin) hs hweight m cut hrows i x B hheld
  intro k o t hki hk
  exact (Gen.V2.Duty.index_lt_idxBefore_iff hs hk cut).mp
    (hki.trans_le hcut)

include horigin hc in
/-- FINAL 22:923–938. The tick read precedes every delivery at the same time.
DC: INTENTIONAL: event phases give a strict cut across different nodes' ticks. -/
theorem raw_causal_cap_at_tick (hs : V2.D.ScheduleWellFormed E rho)
    (hweight : Ef.weightOf (historyFaulty S rho) < Ef.q) (m : Nat) (cut : Time)
    (hrows : ∀ j z r a h t, HonestRowAt S E rho T j z r a →
      historyRowHeight S D a = some h → eventTime rho j = some t → t < cut → h ≤ m)
    (i : Nat) (x : V) (B : FGBlock (Fin n)) (v : V)
    (htick : rho.events[i]? = some (.tick v cut)) (hheld : HeldAt R E rho i x B) :
    (H B).h ≤ m + 1 := by
  apply d7_held_height_le (R := R) (S := S) (E := E) (rho := rho) (T := T) (D := D)
    (Ef := Ef) (H := H) (f := f) (hc := hc) (horigin := horigin) hs hweight m cut hrows i x B hheld
  intro k o t hki hk
  by_contra hn
  have hik := V2.D.Engine.tick_index_lt_delivery E rho
    hs htick hk (le_of_not_gt hn)
  exact (Nat.lt_asymm hki hik)

include horigin hc in
/-- FINAL 22:923–944,1188–1208. Include action q rows up to the strict next-action cut.
DC: INTENTIONAL: the current-action bound is explicit and has no source circularity. -/
theorem raw_causal_cap_through_action (hs : V2.D.ScheduleWellFormed E rho)
    (hweight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    (hmono : StrictMono T.action) (q m : Nat)
    (hpre : ∀ j z r a h t, HonestRowAt S E rho T j z r a →
      historyRowHeight S D a = some h → eventTime rho j = some t → t < T.action q → h ≤ m)
    (haction : ∀ j z a h, HonestRowAt S E rho T j z q a → historyRowHeight S D a = some h → h ≤ m)
    (i : Nat) (x : V) (B : FGBlock (Fin n))
    (hcut : i ≤ V2.D.Run.idxBefore rho (T.action (q + 1)))
    (hheld : HeldAt R E rho i x B) : (H B).h ≤ m + 1 := by
  apply raw_causal_cap_before (R := R) (S := S) (E := E) (rho := rho) (T := T) (D := D)
    (Ef := Ef) (H := H) (f := f) (hc := hc) (horigin := horigin) hs hweight m (T.action (q + 1))
    _ i x B hcut hheld
  intro j z r a H t hj ha ht hearly
  have heq : T.action r = t :=
    Option.some.inj ((d7_event_time S E rho T hj).symm.trans ht)
  have hrq : r ≤ q := by
    have hlt : T.action r < T.action (q + 1) := heq ▸ hearly
    have := hmono.lt_iff_lt.mp hlt
    omega
  rcases Nat.lt_or_eq_of_le hrq with hlt | rfl
  · exact hpre j z r a H t hj ha ht
      (heq ▸ hmono hlt)
  · exact haction j z a H hj ha

end AvailableChain.FGCompose
end
