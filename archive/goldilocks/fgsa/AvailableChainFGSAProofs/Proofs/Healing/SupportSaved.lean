module
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

public section

/-! H-SUPPORT saved-result origin (plan §5 step 1; G3 slow). A non-empty saved result of
a label is the node's own raw result at that gate: later steps append other labels, and
a reconcile can only empty a saved result. The private helper restates the private
`fgsa_grid_proposal_genuine` of AvailableChainFGSARun/Proofs/Schedule.lean. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem saved_proposal_genuine (q : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (o : GridCO.Wire n .root) (b : Block) (raw : List
        (GridCO.HeadWire n .root)) :
    (GridCO.admitProposal q st o b raw).genuine = st.genuine := by
  obtain ⟨auth, msg⟩ := o
  cases auth <;> unfold GridCO.admitProposal <;> dsimp only <;> split
  all_goals first
    | rfl
    | exact (foldVotes_fields q raw _).2.2.2.2.1

private theorem saved_process (st : State p.n) (o : Wire p.n) (w : Slot) (C : Block)
    (h : GridCO.savedGenuine (FGSA.process p st o).base w = some (some C)) :
    GridCO.savedGenuine st.base w = some (some C) := by
  obtain ⟨auth, msg⟩ := o
  rcases auth with ⟨(_ | _), _⟩ | _ | _ <;> cases msg <;> try exact h
  · change GridCO.savedGenuine (admitHead p st _ _ _).base w = _ at h
    rwa [savedGenuine_congr (admitHead_genuine p st _ _ _)] at h
  · change GridCO.savedGenuine (admitRow p st _).base w = _ at h
    rcases admitRow_eq p st _ with he | he <;> rw [he] at h <;> exact h
  · rename_i s N
    change GridCO.savedGenuine (admitBlock p st s N).base w = _ at h
    cases hn : namedParentHeld st N with
    | false =>
      rw [admitBlock_refused p st s N (Or.inl hn)] at h
      exact h
    | true =>
      cases hp : parentFG st N.erase with
      | none =>
        rw [admitBlock_refused p st s N (Or.inr (Or.inl hp))] at h
        exact h
      | some P =>
        cases ha : blockAccepted p st s N P with
        | false =>
          rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hp, ha⟩))] at h
          exact h
        | true =>
          obtain ⟨pool, he, -⟩ := admitBlock_accepted_eq p st s N P hn hp ha
          rw [he] at h
          dsimp only at h
          split at h
          · rwa [savedGenuine_congr (saved_proposal_genuine _ _ _ _ _)] at h
          · rw [reconcile_savedGenuine] at h
            obtain ⟨c', hc, hf⟩ := Option.map_eq_some_iff.mp h
            have hc' : c' = some C := (Option.filter_eq_some_iff.mp hf).1
            subst hc'
            dsimp only at hc
            rwa [savedGenuine_congr (saved_proposal_genuine _ _ _ _ _)] at hc

private theorem saved_clock (st : State p.n) (t : Time) (w : Slot)
    (hne : t ≠ SA.gateTime p.toParams w) (C : Block)
    (h : GridCO.savedGenuine (FGSA.clock p st t).base w = some (some C)) :
    GridCO.savedGenuine st.base w = some (some C) := by
  have hpre : GridCO.savedGenuine (clockPre p st t).base w = some (some C) →
      GridCO.savedGenuine st.base w = some (some C) := by
    intro h'
    rwa [savedGenuine_congr (clockPre_genuine p st t)] at h'
  unfold FGSA.clock at h
  dsimp only at h
  split at h
  · rename_i hg
    let k := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
    have ht : t = SA.gateTime p.toParams k :=
      beq_iff_eq.mp (Bool.and_eq_true_iff.mp hg).2
    have hwk : w ≠ k := by
      intro he
      apply hne
      rw [ht, he]
    apply hpre
    rwa [gateStep_other p _ k w hwk] at h
  · exact hpre h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:650–680 (H.4-S saved window); plan H-SUPPORT §5 step 1, G3.
DC: INTENTIONAL a non-empty saved result of label w at a later index is the raw result
of the node's own gate at w. FG-SA saves the raw result once; a reconcile can only
empty it (`reconcile_savedGenuine`). -/
theorem healing_saved_origin (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (hN : V2.D.NoRestart rho)
    {i : Nat} {x : V} {w : Slot} {C : Block}
    (h : GridCO.savedGenuine (storeAt p c E rho i x).base w = some (some C)) :
    ∃ j < i, IsGateTick p c rho j x w ∧ gateResult p c E rho x w = some (some C) := by
  have hm : w ∈ (V2.D.Run.stateBefore E rho i x).st.base.genuine.map Prod.fst :=
    List.mem_map.mpr ⟨_, mem_genuine_of_saved h, rfl⟩
  obtain ⟨j, hji, hj⟩ := fgsa_saved_label_origin E rho i x w hm
  refine ⟨j, hji, hj, ?_⟩
  rw [gateResult_eq_saved p c E rho hs hj]
  have hpost : ((fgsa p c).clock (V2.D.Run.stateBefore E rho j x)
      (SA.gateTime p.toParams w)).st = storeAt p c E rho (j + 1) x := by
    change _ = (V2.D.Run.stateBefore E rho (j + 1) x).st
    rw [V2.D.Run.stateBefore_succ E rho hj]
    simp only [V2.D.World.step, Function.update_self]
    exact (tick_st (c := c) E rho _ x _).symm
  rw [hpost]
  let R := GridCO.savedGenuine (storeAt p c E rho (j + 1) x).base w = some (some C)
  let Q := fun nd : Node p => GridCO.savedGenuine nd.st.base w = some (some C) → R
  have hQ := V2.D.Engine.stateBefore_step_induction E rho Q (show j + 1 ≤ i by omega) x ?_
    (fun h' => h')
  · exact hQ h
  intro k e hjk _ he hv hQk
  cases e with
  | restart y t =>
    change y = x at hv
    subst y
    exact absurd he (hN k _ t)
  | deliver y o t =>
    change y = x at hv
    subst y
    simp only [Q, V2.D.World.step, Function.update_self]
    intro h'
    exact hQk (saved_process _ (toWire p o) w C h')
  | tick y t =>
    change y = x at hv
    subst y
    simp only [Q, V2.D.World.step, Function.update_self]
    intro h'
    rw [tick_st (c := c) E rho (V2.D.Run.stateBefore E rho k x) x t] at h'
    have hne : t ≠ SA.gateTime p.toParams w := by
      intro ht
      subst ht
      exact lt_irrefl _ (fgsa_tick_time_strict E rho hs hj he (by omega))
    exact hQk (saved_clock _ t w hne C h')

/-- A wake clears saved results; a surviving nonempty result has its actual gate origin. -/
theorem healing_saved_origin_on (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {w : Slot} {C : Block}
    (h : GridCO.savedGenuine (storeAt p c E rho i x).base w = some (some C)) :
    ∃ j < i, IsGateTick p c rho j x w ∧ gateResult p c E rho x w = some (some C) := by
  have hm : w ∈ (V2.D.Run.stateBefore E rho i x).st.base.genuine.map Prod.fst :=
    List.mem_map.mpr ⟨_, mem_genuine_of_saved h, rfl⟩
  obtain ⟨j, hji, hj⟩ := fgsa_saved_label_origin E rho i x w hm
  refine ⟨j, hji, hj, ?_⟩
  rw [gateResult_eq_saved p c E rho hs hj]
  have hpost : ((fgsa p c).clock (V2.D.Run.stateBefore E rho j x)
      (SA.gateTime p.toParams w)).st = storeAt p c E rho (j + 1) x := by
    change _ = (V2.D.Run.stateBefore E rho (j + 1) x).st
    rw [V2.D.Run.stateBefore_succ E rho hj]
    simp only [V2.D.World.step, Function.update_self]
    exact (tick_st (c := c) E rho _ x _).symm
  rw [hpost]
  let R := GridCO.savedGenuine (storeAt p c E rho (j + 1) x).base w = some (some C)
  let Q := fun nd : Node p => GridCO.savedGenuine nd.st.base w = some (some C) → R
  have hQ := V2.D.Engine.stateBefore_step_induction E rho Q (show j + 1 ≤ i by omega) x ?_
    (fun h' => h')
  · exact hQ h
  intro k e hjk _ he hv hQk
  cases e with
  | restart y t =>
    change y = x at hv
    subst y
    simp only [Q, V2.D.World.step, Function.update_self]
    intro h'
    change GridCO.savedGenuine (acRestart p (rho.stateBefore E k x).st t).base w =
      some (some C) at h'
    unfold GridCO.savedGenuine at h'
    rw [acRestart_genuine] at h'
    cases h'
  | deliver y o t =>
    change y = x at hv
    subst y
    simp only [Q, V2.D.World.step, Function.update_self]
    intro h'
    exact hQk (saved_process _ (toWire p o) w C h')
  | tick y t =>
    change y = x at hv
    subst y
    simp only [Q, V2.D.World.step, Function.update_self]
    intro h'
    rw [tick_st (c := c) E rho (V2.D.Run.stateBefore E rho k x) x t] at h'
    have hne : t ≠ SA.gateTime p.toParams w := by
      intro ht
      subst ht
      exact lt_irrefl _ (fgsa_tick_time_strict E rho hs hj he (by omega))
    exact hQk (saved_clock _ t w hne C h')

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:689–699; plan H-SUPPORT §3.
DC: SAME a row that survives the clock before a tick is live at that tick. -/
theorem healing_clockPre_live (st : State p.n) (t : Time) (row : Block × Nat × Time)
    (h : row ∈ (clockPre p st t).base.obligations) : t < row.2.2 := by
  obtain ⟨K, g, d⟩ := row
  unfold clockPre at h
  dsimp only at h
  split_ifs at h <;>
    first
    | exact of_decide_eq_true (List.mem_filter.mp h).2
    | exact of_decide_eq_true (List.mem_filter.mp (List.mem_filter.mp h).1).2

end AvailableChain.FGSA.Run
end
