module
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceDefs
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingSleep
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceHistory
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceRelease
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Shared.HonestQuorum -- shake: keep
public import AvailableChainFGSAClaims.Statements.OutageSleep

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- P16: the joined honest set outside W is disjoint from A union W. -/
theorem outage_good_bad_disjoint [Fintype V] (fast : Bool) (b₀ : Time) (r s : Slot) :
    Disjoint (outageH p E rho s \ outageW p E rho fast b₀ r)
      (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hu
  obtain ⟨hh, hw⟩ := Finset.mem_sdiff.mp hx
  have hxH : x ∈ rho.honest := (Finset.mem_filter.mp hh).1
  rcases Finset.mem_union.mp hu with ha | hW
  · exact (Finset.mem_sdiff.mp ha).2 hxH
  · exact hw hW

/-- P16: E implies the strict release bound for the opponent set U=A union W. -/
theorem outage_opponents_lt_release [Fintype V]
    (hBase : Base₂ p c E rho) {fast : Bool} {b₀ : Time} {r s : Slot}
    (hCount : (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card <
      (outageH p E rho s \ outageW p E rho fast b₀ r).card) :
    (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card <
      SA.releaseThreshold p.toParams := by
  classical
  obtain ⟨e, _⟩ := fgsa_linked_seats rho hBase.linked
  have hn : Fintype.card V = p.n := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hSum := Finset.card_le_univ
    ((outageH p E rho s \ outageW p E rho fast b₀ r) ∪
      (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r))
  rw [Finset.card_union_of_disjoint (outage_good_bad_disjoint fast b₀ r s), hn] at hSum
  apply outage_fault_lt_release p hCount
  omega

/-- P16: E gives E1 without a good-vote or receipt premise. -/
theorem outage_e1_of_e (p : Params) : OutageE1DerivedClaim p := by
  intro In V _ _ c E rho fast b₀ b₁ hBase hE
  classical
  obtain ⟨r, hr, hCount⟩ := hE
  have hc := hCount r le_rfl ((Nat.le_add_right r p.k).trans (Nat.le_succ _))
  obtain ⟨e, _⟩ := fgsa_linked_seats rho hBase.linked
  have hn : Fintype.card V = p.n := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hSum := Finset.card_le_univ
    ((outageH p E rho r \ outageW p E rho fast b₀ r) ∪
      (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r))
  rw [Finset.card_union_of_disjoint (outage_good_bad_disjoint fast b₀ r r), hn] at hSum
  exact ⟨r, hr, by omega⟩

/-- P12/P17: restart keeps coverage of B and its covering lock deadline. -/
theorem outage_restart_protection {B : Block} {j : Slot} {st : State p.n} (w : Time)
    (h : OutageProtection p B j st) : OutageProtection p B j (acRestart p st w) := by
  rw [OutageProtection_def] at h ⊢
  rwa [acRestart_stableRecord, acRestart_fg, acRestart_obligations]

/-- The kept-state restart case for a joint event induction. -/
theorem outage_restart_protection_at {B : Block} {j : Slot} {i : Nat} {x : V} {w : Time}
    (hi : rho.events[i]? = some (.restart x w))
    (h : OutageProtection p B j (storeAt p c E rho i x)) :
    OutageProtection p B j (storeAt p c E rho (i + 1) x) := by
  change OutageProtection p B j (V2.D.Run.stateBefore E rho (i + 1) x).st
  rw [V2.D.Run.stateBefore_succ E rho hi]
  simp only [V2.D.World.step, Function.update_self]
  exact outage_restart_protection w h

/-- A restart adds no source or duty. These two histories are global;
protection is preserved only on the selected receiver scope. This is the
restart case shared by the pre-expiry and continuation joint inductions. -/
theorem outage_joint_restart {B : Block} {j : Slot} {i : Nat} {x : V} {w : Time}
    (he : rho.events[i]? = some (.restart x w)) (R : V → Prop)
    (hSource : OutageSourceHistory p c E rho B i)
    (hDuty : OutageDutyHistory p c E rho B j i)
    (hProtected : ∀ y, R y → OutageProtection p B j (storeAt p c E rho i y)) :
    OutageSourceHistory p c E rho B (i + 1) ∧
      OutageDutyHistory p c E rho B j (i + 1) ∧
      ∀ y, R y → OutageProtection p B j (storeAt p c E rho (i + 1) y) := by
  refine ⟨⟨?_⟩, ⟨?_⟩, ?_⟩
  · intro k y r C hk hy ht hC
    have hki : k < i := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with h | rfl
      · exact h
      · rw [he] at ht
        cases ht
    exact hSource.history k y r C hki hy ht hC
  · intro k y t o hk hy hj ht ho
    have hki : k < i := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with h | rfl
      · exact h
      · rw [he] at ht
        cases ht
    exact hDuty.history k y t o hki hy hj ht ho
  · intro y hy
    by_cases hxy : x = y
    · subst y
      exact outage_restart_protection_at he (hProtected x hy)
    · have hs : storeAt p c E rho (i + 1) y = storeAt p c E rho i y := by
        unfold storeAt
        rw [V2.D.Run.stateBefore_succ E rho he]
        simp only [V2.D.World.step, Function.update_of_ne (Ne.symm hxy)]
      rw [hs]
      exact hProtected y hy

/-- P17: the covering-lock exception is limited to the live deadline. -/
theorem outage_restart_live_lock {B : Block} {g : Nat} {dl : Time} {st : State p.n}
    {w : Time} (hRow : (B, g, dl) ∈ st.base.obligations) (hLive : w < dl) :
    (B, g, dl) ∈ (acRestart p st w).base.obligations ∧
      (acRestart p st w).base.now < dl := by
  rw [acRestart_obligations, acRestart_now]
  exact ⟨hRow, hLive⟩

/-- P-Ar's scoped pending gate seeds protection only for covered receivers.
The current-finality branch is retained; no all-honest seed is constructed. -/
theorem outage_arming_local_on
    (hvalid : V2.D.ExecutionValid E rho) (hdelta : E.Δ = p.Δ)
    {fast : Bool} {T b₀ : Time} {B : Block} (hne : B ≠ .genesis)
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    (hgate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon) :
    ∀ y ∈ coveredNodes p E rho fast b₀,
      OutageProtection p B (l + 1)
        (storeAt p c E rho (afterTicksIdx rho (SA.gateTime p.toParams (l + 1))) y) := by
  intro y hy
  obtain ⟨hS, hF | ⟨_, _, dl, hlease, _, hlong, _⟩⟩ :=
    arming_sleep_gate_core hvalid hdelta hne hc hgate y hy
  · exact ⟨hS, Or.inl hF⟩
  exact ⟨hS, Or.inr ⟨dl, outage_row_of_lease p _
    (cstoreInv_stateBefore E rho _ y) hlease, hlong⟩⟩

/-- The global source history supplies P-Ar's exact named-row boundary.
The certificate does not assume this boundary. -/
theorem outage_arming_domain_on
    (hvalid : V2.D.ExecutionValid E rho) (hdelta : E.Δ = p.Δ)
    (hf : FGFoundation p c E rho) (hroots : NamedRootCollisionFree p c E rho)
    {fast : Bool} {T b₀ : Time} {B : Block} (hne : B ≠ .genesis)
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    (hgate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon)
    (hSource : OutageSourceHistory p c E rho B
      (afterTicksIdx rho (SA.gateTime p.toParams (l + 1))))
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C)) :
    ∀ y ∈ coveredNodes p E rho fast b₀,
      let I := afterTicksIdx rho (SA.gateTime p.toParams (l + 1))
      let st := storeAt p c E rho I y
      Block.Preceq B (F_at p c E rho I y) ∨
        ((∃ X ∈ FGSA.fullTree p st, eraseFG X = B) ∨
          Block.Preceq B (eraseFG (FGSA.controls p st).Z)) := by
  have hRows : ∀ y r (a : RowWire p.n) (e Bh : FGBlock (Fin p.n)), eraseFG Bh = B →
      HonestRowBefore p c E rho (afterTicksIdx rho (SA.gateTime p.toParams (l + 1))) y r a →
      namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
      RootBlockInRun p c E rho (eraseFG e) → FGBlock.Preceq e Bh ∨ FGBlock.Preceq Bh e := by
    intro y r a e Bh hBh ha he hScope
    exact (outage_named_of_source_history hroots hBh hSource hnamed).history y r a e
      ha he hScope
  intro y hy I st
  obtain ⟨_, hF | ⟨_, _, _, _, _, _, hdom⟩⟩ :=
    pending_gate_lease_or_F_on hvalid hdelta hf hne hc hgate hRows y hy
  · exact Or.inl hF
  · exact Or.inr hdom

/-- The scoped certificate supplies the strict pre-pending global source seed. -/
theorem outage_arming_sources_before_on
    (hs : V2.D.ScheduleWellFormed E rho) {fast : Bool} {T b₀ : Time} {B : Block}
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh) :
    OutageSourceHistory p c E rho B (rho.idxBefore (SA.gateTime p.toParams (l + 1))) := by
  constructor
  intro k y r C hk hy ht hC
  have htime := (Gen.V2.Duty.index_lt_idxBefore_iff hs ht _).mp hk
  exact block_compatible_of_common (hc.source_below y r C hy htime hC) hc.max_read

/-- An enabled gate keeps each strict read after its label start in the same epoch. -/
theorem outage_enabled_gate_read_epoch (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot} (hG : enabledGateAt p c E rho i x s)
    {D : Time} (hD : slotStartZ p (s : Int) < D) :
    V2.D.restartFree rho x (rho.idxBefore D) i := by
  intro j w hcut hji hj
  have hw : D ≤ w := by
    by_contra hn
    exact (Nat.not_lt.mpr hcut)
      ((Gen.V2.Duty.index_lt_idxBefore_iff hs hj _).mpr (lt_of_not_ge hn))
  obtain ⟨u, hu, hwu⟩ := fgsa_restartTime_ge E rho hs hj hji
  have hb := hG.2
  change (match (rho.stateBefore E i x).st.restartTime with
    | none => True | some t => t ≤ slotStartZ p (s : Int)) at hb
  rw [hu] at hb
  exact (not_lt_of_ge (hw.trans (hwu.trans hb)) hD).elim

/-- An enabled gate has no receiver restart between its strict cut and its tick. -/
theorem outage_enabled_gate_tick_epoch (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot} (hG : enabledGateAt p c E rho i x s) :
    V2.D.restartFree rho x (rho.idxBefore (SA.gateTime p.toParams s)) i := by
  apply outage_enabled_gate_read_epoch hs hG
  change 4 * p.Δ * (s : Int) < 4 * p.Δ * (s : Int) + 6 * p.Δ
  linarith [p.deltaPos]

/-- The actual enabled honest tick supplies the environment join guard.
Its last restart bounds all earlier restarts and all wakes through this tick. -/
theorem outage_enabled_gate_joined (hvalid : V2.D.ExecutionValid E rho)
    {i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hG : enabledGateAt p c E rho i x s) :
    joinedAt p E rho x (s + 1) (SA.gateTime p.toParams s) := by
  have hs := hvalid.toScheduleWellFormed
  have hslot : slotStartZ p (((s + 1 : Nat) : Int) - 1) = slotStartZ p (s : Int) := by
    congr 1
    omega
  have hBound : ∀ w, 0 ≤ w → w ≤ SA.gateTime p.toParams s →
      V2.Event.restart x w ∈ rho.events → w ≤ slotStartZ p (s : Int) := by
    intro w _ hw hr
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
    have hji := V2.D.Engine.restart_index_lt_event hs hj hG.1 hw
      (by change (0 : Nat) < 1; decide)
    obtain ⟨u, hu, hwu⟩ := fgsa_restartTime_ge E rho hs hj hji
    have hb := hG.2
    change (match (rho.stateBefore E i x).st.restartTime with
      | none => True | some t => t ≤ slotStartZ p (s : Int)) at hb
    rw [hu] at hb
    exact hwu.trans hb
  refine ⟨hvalid.tick_awake x _ (List.mem_of_getElem? hG.1), ?_, ?_⟩
  · intro w hw hwt hW
    rw [hslot]
    exact hBound w hw.le hwt (hvalid.wake_restart x hx w hw
      (hwt.trans (hs.in_horizon _ (List.mem_of_getElem? hG.1)).2) hW)
  · intro w hw hwt hr
    rw [hslot]
    exact hBound w hw hwt hr

/-- The certificate's strict-cut F bound holds at every enabled pending tick,
including a receiver in W. Same-time restart is excluded by the enabled guard. -/
theorem outage_pending_frame_below
    (hs : V2.D.ScheduleWellFormed E rho) {fast : Bool} {T b₀ : Time} {B : Block}
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hG : enabledGateAt p c E rho i x (l + 1)) :
    Block.Preceq (F_at p c E rho i x) D := by
  change Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) D
  rw [arming_tick_store_on hs hG.1 (outage_enabled_gate_tick_epoch hs hG)]
  exact hc.f_below _ x le_rfl hx

/-- Only the actual pending action sources remain at the all-ticks seed boundary.
This field is P-Ou's joint-induction obligation, not a public claim premise. -/
theorem outage_arming_sources_on
    (hs : V2.D.ScheduleWellFormed E rho) {fast : Bool} {T b₀ : Time} {B : Block}
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    (hPending : ∀ y r C, y ∈ rho.honest →
      p.actionTime r = SA.gateTime p.toParams (l + 1) →
      actionSource p c E rho y r = some (some C) → Block.Compatible C B) :
    OutageSourceHistory p c E rho B (afterTicksIdx rho (SA.gateTime p.toParams (l + 1))) := by
  constructor
  intro k y r C hk hy ht hC
  have htime := arming_tick_le hs ht
    (hk.trans_le (preIdx_le_afterTicksIdx E rho hs _).2)
  rcases htime.lt_or_eq with hlt | heq
  · exact block_compatible_of_common (hc.source_below y r C hy hlt hC) hc.max_read
  · exact hPending y r C hy heq hC

/-- Rows whose deadlines are at or before handover are absent from the expired view.
The joint induction must bound the deadlines of the old conflicting rows. -/
theorem outage_handover_expired {n : Nat} (st : GridCO.State n .root) (r : Slot)
    (row : Block × Nat × Time) (hOld : row.2.2 ≤ OutageEnd p r) :
    row ∉ (GridCO.expire { st with now := OutageEnd p r } (OutageEnd p r)).obligations := by
  intro hm
  have hLive : OutageEnd p r < row.2.2 := of_decide_eq_true (List.mem_filter.mp hm).2
  exact (not_lt_of_ge hOld) hLive

end AvailableChain.FGSA.Run
end
