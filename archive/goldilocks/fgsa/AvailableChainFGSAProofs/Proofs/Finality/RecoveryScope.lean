module
public import AvailableChainFGSAProofs.Proofs.Shared.CatchUp
public import AvailableChainFGSAClaims.Statements.Regimes
public import AvailableChainFGSAClaims.Statements.Channels

public section

namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Exact services for each honest HEAD seat at an action receiver.
This is an internal supplier contract, separate from Recovery and its join bounds. -/
structure FinalityActionReceipts : Prop where
  service : ∀ q x, x ∈ rho.honest → E.t_GST < p.actionTime q →
    E.t_GST ≤ slotStartZ p (((q * p.R + 1 : Nat) : Int) - 1) →
    p.actionTime q ≤ rho.horizon → ∀ nd,
    postClock E rho x (p.actionTime q) = some nd → ∀ a K,
    rho.seatOf (.base (.head (q * p.R + 1))) a ∈ rho.honest →
    headAtLabel p c E rho (rho.seatOf (.base (.head (q * p.R + 1))) a)
      (q * p.R + 1) = some K →
    Block.Preceq (eraseFG nd.st.fg.F) K →
    Nonempty (FreshHeadService E rho (q * p.R + 1) a K.root (p.actionTime q) x) ∧
      TargetReceiptService E rho K (p.actionTime q) x

omit [DecidableEq V] [Fintype V] in
/-- Two full slots after the GST cutoff are beyond the recovery start. -/
theorem finality_recoveryStart_le_vote (s : Slot) (hs : 2 ≤ s)
    (hGST : E.t_GST ≤ slotStartZ p ((s : Int) - 2)) :
    recoveryStart p E ≤ SA.voteTime p.toParams s := by
  let a := max 0 E.t_GST + 4 * p.Δ - 1
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have hn : 0 ≤ (s : Int) - 2 := by
    have hsI : (2 : Int) ≤ s := by exact_mod_cast hs
    linarith
  have hm : max 0 E.t_GST ≤ 4 * p.Δ * ((s : Int) - 2) :=
    max_le (mul_nonneg hd.le hn) hGST
  have hdelta : 1 ≤ p.Δ := by
    have hp := p.deltaPos
    dsimp [Time] at *
    omega
  have ha : 0 ≤ a := by dsimp [a]; linarith [le_max_left 0 E.t_GST]
  have hq := Int.ediv_nonneg ha hd.le
  have he := Int.mul_ediv_add_emod a (4 * p.Δ)
  have hr := Int.emod_nonneg a (by linarith : 4 * p.Δ ≠ 0)
  have hupper : a / (4 * p.Δ) ≤ (s : Int) - 2 := by
    by_contra hnot
    have hle : (s : Int) - 1 ≤ a / (4 * p.Δ) := by
      dsimp [Time] at hnot ⊢
      omega
    have hl := mul_le_mul_of_nonneg_left hle hd.le
    dsimp [a] at he
    linarith
  change 4 * p.Δ * ((a / (4 * p.Δ)).toNat : Int) + 6 * p.Δ ≤
    4 * p.Δ * (s : Int) + p.Δ
  rw [Int.toNat_of_nonneg hq]
  nlinarith [p.deltaPos]

/-- Recovery permits a wake at GST, but no later honest restart. -/
theorem finality_recovery_restart_bound {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) {x : V} (hx : x ∈ rho.honest)
    {t : Time} (ht : V2.Event.restart x t ∈ rho.events) : t ≤ E.t_GST := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ht
  exact V2.D.Engine.noRestartAfter_of_awakeOnClosed h.base.valid.toScheduleWellFormed
    h.base.restartsAtWakes (fun u ha hb => h.awake x hx u ha hb) i t hi

/-- A receiver interval that starts after GST contains no local restart. -/
theorem finality_recovery_restartFree {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) {x : V} (hx : x ∈ rho.honest)
    {i j : Nat} (hcut : ∀ k t, i ≤ k → k < j →
      rho.events[k]? = some (.restart x t) → E.t_GST < t) :
    V2.D.restartFree rho x i j := by
  intro k t hik hkj hk
  exact (not_lt_of_ge (finality_recovery_restart_bound p c E rho h hx
    (List.mem_of_getElem? hk))) (hcut k t hik hkj hk)

/-- The inclusive join cutoff, with the required receiver and time. -/
theorem finality_recovery_joined {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) {x : V} (hx : x ∈ rho.honest)
    {s : Slot} {t : Time} (hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1))
    (hGST : E.t_GST ≤ t) (hhor : t ≤ rho.horizon) : joinedAt p E rho x s t := by
  refine ⟨h.awake x hx t hGST hhor, ?_, ?_⟩
  · intro u hu hut hw
    exact (finality_recovery_restart_bound p c E rho h hx
      (h.base.valid.wake_restart x hx u hu (hut.trans hhor) hw)).trans hcut
  · intro u _ _ hu
    exact (finality_recovery_restart_bound p c E rho h hx hu).trans hcut

/-- All honest voters are joined once GST is before the previous slot start. -/
theorem finality_recovery_joinedHonest {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) {s : Slot}
    (hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1))
    (hhor : SA.voteTime p.toParams s ≤ rho.horizon) :
    joinedHonest p E rho (SA.voteTime p.toParams s) = rho.honest := by
  classical
  have hGST : E.t_GST ≤ SA.voteTime p.toParams s := by
    apply hcut.trans
    change 4 * p.Δ * ((s : Int) - 1) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  apply Finset.filter_eq_self.mpr
  intro x hx
  have hs : slotAt p (SA.voteTime p.toParams s) = s :=
    slotOf_offset p s p.Δ p.deltaPos.le
      (by have hd := p.deltaPos; dsimp [Time] at *; omega)
  rw [hs]
  exact finality_recovery_joined p c E rho h hx hcut hGST hhor

/-- A read cut strictly after GST permits earlier honest restarts. -/
theorem finality_recovery_readEpoch {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) {x : V} (hx : x ∈ rho.honest)
    {t : Time} (hGST : E.t_GST < t) (j : Nat) :
    V2.D.restartFree rho x (V2.D.Run.idxBefore rho t) j := by
  apply finality_recovery_restartFree p c E rho h hx
  intro k u hk _ he
  have htu : t ≤ u := by
    by_contra hn
    have hki := (Gen.V2.Duty.index_lt_idxBefore_iff
      h.base.valid.toScheduleWellFormed he t).mpr (lt_of_not_ge hn)
    omega
  exact hGST.trans_le htu

/-- An applied enabled gate supplies a confirmed reader in the Recovery suffix. -/
theorem finality_recovery_confirmed {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) {x : V} (hx : x ∈ rho.honest)
    (s : Slot) (i : Nat) (t : Time)
    (hcut : E.t_GST ≤ slotStartZ p (s : Int))
    (hgate : SA.gateTime p.toParams s ≤ t) (hhor : t ≤ rho.horizon)
    (hidx : ∀ j, rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) → j < i) :
    confirmedReaderAtIdx p c E rho x i t := by
  have hs := h.base.valid.toScheduleWellFormed
  have hst : slotStartZ p (s : Int) ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hbound : ∀ (j : Nat) (w : Time), rho.events[j]? = some (.restart x w) →
      w ≤ slotStartZ p (s : Int) := by
    intro j w he
    exact (finality_recovery_restart_bound p c E rho h hx
      (List.mem_of_getElem? he)).trans hcut
  have htime : ((4 * s + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams s := by
    change ((4 * s + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hs h.base.delta x hx (4 * s + 6)
    (htime ▸ (hgate.trans hhor))
    (htime ▸ h.awake x hx _ (hcut.trans hst) (hgate.trans hhor))
  rw [htime] at hj
  have hEnabled : enabledGateAt p c E rho j x s := by
    refine ⟨hj, ?_⟩
    have hb := fgsa_restartTime_bound E rho j x (slotStartZ p (s : Int))
      (fun k w _ he => hbound k w he)
    cases hr : (storeAt p c E rho j x).restartTime with
    | none => trivial
    | some w => exact hb w hr
  refine ⟨hx, h.awake x hx t (hcut.trans (hst.trans hgate)) hhor, ?_⟩
  cases hr : (storeAt p c E rho i x).restartTime with
  | none => trivial
  | some w =>
    have hb := fgsa_restartTime_bound E rho i x (slotStartZ p (s : Int))
      (fun k w _ he => hbound k w he)
    refine ⟨s, j, hb w hr, hgate, hidx j hj, hEnabled, ?_, ?_⟩
    · intro u _ hlu hut
      exact h.awake x hx u (hcut.trans hlu) (hut.trans hhor)
    · intro u hlu _ he
      exact (not_lt_of_ge ((finality_recovery_restart_bound p c E rho h hx he).trans
        hcut)) hlu

omit [DecidableEq V] [Fintype V] in
/-- Each event in a prefix is at or before its last event time. -/
theorem finality_prefixTime_bounds (hs : V2.D.ScheduleWellFormed E rho)
    {i j : Nat} {e : V2.Event V (Obj p)}
    (hj : rho.events[j]? = some e) (hji : j < i) :
    e.time ≤ prefixTime rho i ∧ prefixTime rho i ≤ rho.horizon := by
  have hjlen := List.getElem?_eq_some_iff.mp hj
  let n := min i rho.events.length
  have hjn : j < n := lt_min hji hjlen.1
  have hn : n - 1 < rho.events.length := by dsimp [n]; omega
  have hni : n - 1 < i := by dsimp [n] at *; omega
  have he : rho.events[n - 1]? = some rho.events[n - 1] := List.getElem?_eq_getElem hn
  have hp : prefixTime rho i = rho.events[n - 1].time := by
    unfold prefixTime
    rw [List.getLast?_eq_getElem?, List.length_take, List.getElem?_take,
      ite_eq_left hni, he]
    rfl
  rw [hp]
  refine ⟨?_, (hs.in_horizon _ (List.mem_of_getElem? he)).2⟩
  have hle : j ≤ n - 1 := by omega
  rcases hle.eq_or_lt with hEq | hLt
  · have hj' : rho.events[n - 1]? = some e := by simpa only [hEq] using hj
    have heq := Option.some.inj (he.symm.trans hj')
    rw [heq]
    exact le_rfl
  · have hk := hs.sorted.rel_getElem_of_lt hjlen.1 hn hLt
    rw [hjlen.2] at hk
    exact V2.D.Engine.time_le_of_key_le _ _ hk

/-- A Recovery prefix after an enabled gate is a confirmed index reader.
All earlier wakes have their restart event in the same prefix. -/
theorem finality_recovery_confirmedIdx {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) {x : V} (hx : x ∈ rho.honest)
    (s : Slot) (i : Nat) (hcut : E.t_GST ≤ slotStartZ p (s : Int))
    (hhor : SA.gateTime p.toParams s ≤ rho.horizon)
    (hidx : ∀ j, rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) → j < i) :
    confirmedReaderIdx p c E rho x i := by
  have hs := h.base.valid.toScheduleWellFormed
  have hst : slotStartZ p (s : Int) < SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) < 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have htime : ((4 * s + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams s := by
    change ((4 * s + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hs h.base.delta x hx (4 * s + 6)
    (htime ▸ hhor) (htime ▸ h.awake x hx _ (hcut.trans hst.le) hhor)
  rw [htime] at hj
  have hb := finality_prefixTime_bounds p c E rho hs hj (hidx j hj)
  refine ⟨finality_recovery_confirmed p c E rho h hx s i _ hcut hb.1 hb.2 hidx, ?_⟩
  intro w hw hwt hW
  have he := h.base.valid.wake_restart x hx w hw (hwt.trans hb.2) hW
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
  refine ⟨k, ?_, hk⟩
  have hwg := (finality_recovery_restart_bound p c E rho h hx he).trans_lt
    (hcut.trans_lt hst)
  have hkcut := (Gen.V2.Duty.index_lt_idxBefore_iff hs hk _).mpr hwg
  have hjcut : V2.D.Run.idxBefore rho (SA.gateTime p.toParams s) ≤ j := by
    by_contra hn
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hs hj _).mp (Nat.lt_of_not_ge hn)
    exact (lt_irrefl _) ht
  exact hkcut.trans_le (hjcut.trans (hidx j hj).le)

end AvailableChain.FGSA.Run
end
