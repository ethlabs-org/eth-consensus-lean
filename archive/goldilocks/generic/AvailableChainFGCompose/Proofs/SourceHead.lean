module
public import AvailableChainFGCompose.Statements.CoreReads
public import AvailableChainKitV2.DutyStable
public import AvailableChainKitFG.Correspondence

public section
namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {V In : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal RowWire : Type}
variable (R : FGCoreReads P n Base Proposal RowWire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)
theorem postClock_tick {x : V} {t : Time} {nd : P.State}
    (hnd : postClock E rho x t = some nd) :
    ∃ i, rho.events[i]? = some (.tick x t) ∧ P.clock (V2.D.Run.stateBefore E rho i x) t = nd := by
  unfold postClock preTick at hnd
  cases hi : V2.D.Run.tickIdx? rho x t with
  | none => simp [hi] at hnd
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hnd
    exact ⟨i, V2.D.Run.tickIdx?_spec hi, hnd⟩
omit [DecidableEq V] in
theorem tick_lt_afterTicks (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {t' t : Time}
    (hi : rho.events[i]? = some (.tick x t')) (ht : t' ≤ t) : i < afterTicksIdx rho t := by
  have hcut : cutPred t (V2.Event.tick x t' : V2.Event V P.Object) = true :=
    decide_eq_true (Prod.Lex.toLex_le_toLex.mpr (ht.lt_or_eq.imp id (fun h => ⟨h, le_rfl⟩)))
  by_contra hn
  have hfalse := V2.D.Engine.filter_false_of_index_ge hs (cutPred t)
    (fun e f hk hf => decide_eq_true (hk.trans (of_decide_eq_true hf))) (Nat.le_of_not_gt hn) hi
  rw [hcut] at hfalse
  contradiction
theorem tf_cumulative (L : FGCoreLaws R) (hnr : V2.D.NoRestart rho) {i j : Nat}
    (hij : i ≤ j) (x : V) : TFAt R E rho i x ⊆ TFAt R E rho j x := by
  intro B hB
  exact V2.D.Engine.stateBefore_stable (fun nd => B ∈ (R.core nd).fg.TF)
    (fun st t h => by simpa only [L.clock_fg] using h)
    (fun st o h => L.process_tf st o h)
    (fun st o h => by simpa only [L.own_core] using h)
    E rho hij x (fun k t _ _ => hnr k x t) hB
theorem source_mem_TF (L : FGCoreLaws R) {nd : P.State} {C : FGBlock (Fin n)}
    (h : R.source nd = some C) : C ∈ (R.core nd).fg.TF := by
  exact L.source_mem nd C h
theorem head_held (L : FGCoreLaws R) (HL : FGHeadLaws R E rho) {s : Slot} {t : Time}
    {X : FGBlock (Fin n)} {x : V}
    (hh : (postClock E rho x t).map (fun nd => R.headVote nd s) = some (R.erase X)) :
    ∃ i, rho.events[i]? = some (.tick x t) ∧ X ∈ TFAt R E rho i x := by
  obtain ⟨nd, hnd, hv⟩ := Option.map_eq_some_iff.mp hh
  obtain ⟨i, hi, rfl⟩ := postClock_tick E rho hnd
  obtain ⟨B, hB, he⟩ := HL.head_mem i x t s
  rw [hv] at he
  have hBX := L.erase_inj he
  subst B
  refine ⟨i, hi, ?_⟩
  unfold TFAt
  rw [← L.clock_fg _ t]
  exact hB
theorem head_held_from (L : FGCoreLaws R) (HL : FGHeadLaws R E rho)
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    {s : Slot} {t : Time} {X : FGBlock (Fin n)} {x : V}
    (hh : (postClock E rho x t).map (fun nd => R.headVote nd s) = some (R.erase X))
    (k : Nat) (cut : Time) (ht : t ≤ cut) (hk : afterTicksIdx rho cut ≤ k) :
    X ∈ TFAt R E rho k x := by
  obtain ⟨i, hi, hX⟩ := head_held R E rho L HL hh
  exact tf_cumulative R E rho L hnr
    ((tick_lt_afterTicks E rho hs hi ht).le.trans hk) x hX
theorem chainRows_of_head (L : FGCoreLaws R) (HL : FGHeadLaws R E rho)
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    {s : Slot} {t : Time} {X : FGBlock (Fin n)} {x : V} (hx : x ∈ rho.honest)
    (hh : (postClock E rho x t).map (fun nd => R.headVote nd s) = some (R.erase X))
    (cut : Time) (hcut : t < cut) : ChainRowsBefore R E rho X cut := by
  obtain ⟨i, hi, hX⟩ := head_held R E rho L HL hh
  intro W hW _row _hrow
  refine ⟨x, t, hx, hcut, ?_⟩
  have hanc := ancestor_closed_of_parent_closed _ (HL.parent_closed i x) X hX W hW
  rw [Gen.V2.Duty.HoldsBefore_def]
  rw [← V2.D.Engine.stateBefore_tick_eq_stateBeforeTime hs hnr hi]
  exact hanc
theorem source_height_entry (Ef : Electorate (Fin n)) (H : FGHeightView (Fin n))
    (laws : FGHeightLaws Ef H) {D C : FGBlock (Fin n)} {y : Nat}
    (hDC : FGBlock.Preceq D C) (hD : (H D).h = y + 1) (hC : (H C).h ≤ y + 1) :
    (H C).h = y + 1 ∧ (H C).T_h = (H D).T_h := by
  have hCh : (H C).h = y + 1 := Nat.le_antisymm hC (hD ▸ laws.h_mono hDC)
  exact ⟨hCh, (laws.entry_plateau hDC (hD.trans hCh.symm)).symm⟩
theorem action_source_capped (L : FGCoreLaws R) (Ef : Electorate (Fin n)) (H : FGHeightView (Fin n))
    (laws : FGHeightLaws Ef H) (x : V) (t : Time) (opening roundSlot y : Nat) (D : FGBlock (Fin n))
    (service : FGSourceService R E rho x t opening roundSlot D) (hbefore : opening ≤ roundSlot)
    (hDh : (H D).h = y + 1)
    (hcap : ∀ nd, postClock E rho x t = some nd → ∀ B ∈ (R.core nd).fg.TF, (H B).h ≤ y + 1) :
    ∃ nd C, postClock E rho x t = some nd ∧ R.source nd = some C ∧ FGBlock.Preceq D C ∧
      (H C).h = y + 1 ∧ (H C).T_h = (H D).T_h := by
  rcases Nat.lt_or_eq_of_le hbefore with hlt | heq
  · obtain ⟨nd, C, hnd, hs, hDC⟩ := service.coveredSource hlt
    exact ⟨nd, C, hnd, hs, hDC,
      source_height_entry Ef H laws hDC hDh (hcap nd hnd C (L.source_mem nd C hs))⟩
  · obtain ⟨nd, hnd, hs⟩ := service.openingSource heq
    exact ⟨nd, D, hnd, hs, KitFG.preceq_refl D, hDh, rfl⟩

end AvailableChain.FGCompose
end
