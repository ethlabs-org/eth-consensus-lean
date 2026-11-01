module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingArith
public import AvailableChainFGSAProofs.Proofs.Shared.HeadAdmit -- shake: keep (source declarations)

public section

/-! Plan O-ARM §6.2 step 5, §6.4, §11 obligation 4: one local step of an
honest store strictly between the cut and the pending gate. Off the gate
times a tick is the pre-gate clock. A delivery keeps the leases and the saved
results, or filters both by the new F. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.4. Class (iii). DC: INTENTIONAL; the SA proposal admission
writes no saved result. -/
theorem arming_proposal_genuine (q : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (o : GridCO.Wire n .root) (b : Block) (raw : List
        (GridCO.HeadWire n .root)) :
    (GridCO.admitProposal q st o b raw).genuine = st.genuine := by
  obtain ⟨auth, msg⟩ := o
  cases auth <;> unfold GridCO.admitProposal <;> dsimp only <;> split
  all_goals first
    | rfl
    | exact (foldVotes_fields q raw _).2.2.2.2.1

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Plan O-ARM §6.2 step 5, §6.4. Class (iii). DC: INTENTIONAL; a delivery
keeps the leases and the saved results, or filters both by the new F. -/
theorem arming_process_lease (p : Params) (st : State p.n) (w : Wire p.n) :
    ((FGSA.process p st w).base.obligations = st.base.obligations ∧
      (FGSA.process p st w).base.genuine = st.base.genuine) ∨
    ((FGSA.process p st w).base.obligations = st.base.obligations.filter
        (fun row => Block.compatible row.1 (eraseFG (FGSA.process p st w).fg.F)) ∧
      (FGSA.process p st w).base.genuine = st.base.genuine.map (fun row =>
        (row.1, row.2.filter (fun b =>
          Block.compatible b (eraseFG (FGSA.process p st w).fg.F))))) := by
  obtain ⟨auth, msg⟩ := w
  rcases auth with ⟨(_ | _), _⟩ | _ | _ <;> cases msg <;> try exact Or.inl ⟨rfl, rfl⟩
  · left
    change (admitHead p st _ _ _).base.obligations = _ ∧ (admitHead p st _ _ _).base.genuine = _
    exact ⟨admitHead_obligations .., admitHead_genuine ..⟩
  · rename_i i body
    left
    change (admitRow p st _).base.obligations = _ ∧ (admitRow p st _).base.genuine = _
    rcases admitRow_eq p st ⟨.seat .fg i, body⟩ with he | he <;> rw [he] <;> exact ⟨rfl, rfl⟩
  · rename_i s N
    change ((admitBlock p st s N).base.obligations = _ ∧
        (admitBlock p st s N).base.genuine = _) ∨
      ((admitBlock p st s N).base.obligations = st.base.obligations.filter
        (fun row => Block.compatible row.1 (eraseFG (admitBlock p st s N).fg.F)) ∧
      (admitBlock p st s N).base.genuine = st.base.genuine.map (fun row =>
        (row.1, row.2.filter (fun b' =>
          Block.compatible b' (eraseFG (admitBlock p st s N).fg.F)))))
    cases hn : namedParentHeld st N with
    | false =>
      rw [admitBlock_refused p st s N (Or.inl hn)]
      exact Or.inl ⟨rfl, rfl⟩
    | true =>
      cases hp : parentFG st N.erase with
      | none =>
        left
        rw [admitBlock_refused p st s N (Or.inr (Or.inl hp))]
        exact ⟨rfl, rfl⟩
      | some P =>
        cases ha : blockAccepted p st s N P with
        | false =>
          left
          rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hp, ha⟩))]
          exact ⟨rfl, rfl⟩
        | true =>
          obtain ⟨pool, he, -⟩ := admitBlock_accepted_eq p st s N P hn hp ha
          rw [he]
          dsimp only
          split
          · left
            exact ⟨admitProposal_obligations_slow _ _ _ _ _, arming_proposal_genuine _ _ _ _ _⟩
          · right
            rw [reconcile_obligations, reconcile_genuine, reconcile_fg,
              admitProposal_obligations_slow, arming_proposal_genuine]
            exact ⟨rfl, rfl⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.2 step 5. Class (iii). DC: INTENTIONAL; one event changes
the store of `y` by nothing, by its own clock, or by one delivery. A restart
of this receiver is excluded by the exact index interval. -/
theorem arming_store_succ_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {k : Nat} {e : V2.Event V (Obj p)}
    (he : rho.events[k]? = some e) (y : V)
    (hnr : V2.D.restartFree rho y k (k + 1)) :
    storeAt p c E rho (k + 1) y = storeAt p c E rho k y ∨
      (∃ t, e = .tick y t ∧ storeAt p c E rho (k + 1) y = clock p (storeAt p c E rho k y) t) ∨
      (∃ o t, e = .deliver y o t ∧
        storeAt p c E rho (k + 1) y = FGSA.process p (storeAt p c E rho k y) (toWire p o)) := by
  have hst : storeAt p c E rho (k + 1) y =
      (V2.D.World.step E rho (V2.D.Run.stateBefore E rho k) e y).st := by
    change (V2.D.Run.stateBefore E rho (k + 1) y).st = _
    rw [V2.D.Run.stateBefore_succ E rho he]
  rw [hst]
  by_cases hv : e.node = y
  · cases e with
    | restart u t =>
      change u = y at hv
      subst u
      exact hnr k t le_rfl (Nat.lt_succ_self k) he |>.elim
    | tick u t =>
      change u = y at hv
      subst u
      right; left
      refine ⟨t, rfl, ?_⟩
      simp only [V2.D.World.step, Function.update_self]
      exact tick_st (c := c) E rho _ y t
    | deliver u o t =>
      change u = y at hv
      subst u
      right; right
      refine ⟨o, t, rfl, ?_⟩
      simp only [V2.D.World.step, Function.update_self]
      rfl
  · left
    rw [V2.D.World.step_apply_of_node_ne E rho _ hv]
    rfl
/-- The global no-restart form follows from the receiver epoch form. -/
theorem arming_store_succ {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hnr : V2.D.NoRestart rho) {k : Nat} {e : V2.Event V (Obj p)}
    (he : rho.events[k]? = some e) (y : V) :
    storeAt p c E rho (k + 1) y = storeAt p c E rho k y ∨
      (∃ t, e = .tick y t ∧ storeAt p c E rho (k + 1) y = clock p (storeAt p c E rho k y) t) ∨
      (∃ o t, e = .deliver y o t ∧
        storeAt p c E rho (k + 1) y = FGSA.process p (storeAt p c E rho k y) (toWire p o)) :=
  arming_store_succ_on he y (hnr.restartFree y k (k + 1))

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.2 step 5. Class (iii). DC: INTENTIONAL; an event strictly
between the cut and the pending gate has its time in that open interval. -/
theorem arming_event_window {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {b d : Time} {k : Nat}
    {e : V2.Event V (Obj p)} (he : rho.events[k]? = some e)
    (hlo : timeIdx rho b ≤ k) (hhi : k < V2.D.Run.idxBefore rho d) :
    b < e.time ∧ e.time < d := by
  refine ⟨?_, (Gen.V2.Duty.index_lt_idxBefore_iff hs he d).mp hhi⟩
  by_contra hn
  have := (arming_lt_timeIdx_iff hs b he).mpr (le_of_not_gt hn)
  omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.2 step 5. Class (iii). DC: INTENTIONAL; no gate time lies
strictly after the cut and strictly before the pending gate. -/
theorem arming_offGate (p : Params) (l : Slot) {b₀ t : Time}
    (hl : SA.gateTime p.toParams l ≤ b₀) (hb : b₀ < t)
    (ht : t < SA.gateTime p.toParams (l + 1)) :
    ∀ r : Slot, SA.gateTime p.toParams r ≠ t := by
  intro r hr
  have := arming_gate_window p l r (hl.trans (hb.trans_eq hr.symm).le) (hr.trans_lt ht)
  subst this
  exact absurd (hr ▸ hb) (not_lt.mpr hl)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.2 step 5. Class (iii). DC: INTENTIONAL; off the gate times
the clock keeps F, S and the saved results, and keeps a sublist of leases. -/
theorem arming_clock_offGate_fields (p : Params) (st : State p.n) (t : Time)
    (h : ∀ r : Slot, SA.gateTime p.toParams r ≠ t) :
    (clock p st t).fg = st.fg ∧
      (clock p st t).base.stableRecord = st.base.stableRecord ∧
      (clock p st t).base.genuine = st.base.genuine ∧
      (clock p st t).base.obligations.Sublist st.base.obligations := by
  have hoff : clock p st t = clockPre p st t := by
    unfold clock
    rw [ite_eq_right (by
      intro hg
      obtain ⟨r, hr⟩ := (isGateTime_iff p t).mp hg
      exact h r hr)]
  rw [hoff]
  exact ⟨clockPre_fg p st t, clockPre_stable p st t, clockPre_genuine p st t,
    clockPre_obligations_sublist p st t⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.5. Class (iii). DC: INTENTIONAL; one lease write leaves a
row of its key with at least the written deadline. -/
theorem arming_write_row {n : Nat} (st : GridCO.State n .root) (b : Block) (g : Nat) (lim : Time) :
    ∃ d, (b, g, d) ∈ (GridCO.writeObligation st b g lim).obligations ∧ lim ≤ d :=
  ⟨max ((GridCO.deadlineOf st b g).getD lim) lim,
    List.mem_append_right _ (List.mem_singleton_self _), le_max_right _ _⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.5. Class (iii). DC: INTENTIONAL; a later lease write with the
same deadline keeps a row of each key with at least that deadline. -/
theorem arming_write_keep {n : Nat} (st : GridCO.State n .root) (b : Block) (g : Nat)
    (lim : Time) (b' : Block) (g' : Nat) (d : Time) (hm : (b, g, d) ∈ st.obligations)
    (hd : lim ≤ d) :
    ∃ d', (b, g, d') ∈ (GridCO.writeObligation st b' g' lim).obligations ∧ lim ≤ d' := by
  by_cases hk : b' = b ∧ g' = g
  · obtain ⟨rfl, rfl⟩ := hk
    exact arming_write_row st b' g' lim
  · refine ⟨d, List.mem_append_left _ (List.mem_filter.mpr ⟨hm, ?_⟩), hd⟩
    change (!(b == b' && g == g')) = true
    cases h : (b == b' && g == g') with
    | false => rfl
    | true =>
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
      exact absurd ⟨(beq_iff_eq.mp h1).symm, (beq_iff_eq.mp h2).symm⟩ hk

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.5. Class (iii). DC: INTENTIONAL; a sequence of lease writes
with one deadline keeps a row of each key with at least that deadline. -/
theorem arming_writeKeys_keep {n : Nat} (keys : List (Block × Nat)) (lim : Time) :
    ∀ (st : GridCO.State n .root) b g d, (b, g, d) ∈ st.obligations → lim ≤ d →
      ∃ d', (b, g, d') ∈ (GridCO.writeKeys st keys lim).obligations ∧ lim ≤ d' := by
  induction keys with
  | nil => exact fun st b g d hm hd => ⟨d, hm, hd⟩
  | cons k ks ih =>
    intro st b g d hm hd
    obtain ⟨d', hm', hd'⟩ := arming_write_keep st b g lim k.1 k.2 d hm hd
    rw [@GridCO.writeKeys_def GridCO.slowLeasePolicy, List.foldl_cons,
      ← @GridCO.writeKeys_def GridCO.slowLeasePolicy]
    exact ih _ b g d' hm' hd'

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.5. Class (iii). DC: INTENTIONAL; every written key has a row
with at least the written deadline. -/
theorem arming_writeKeys_row {n : Nat} (lim : Time) (b : Block) (g : Nat) :
    ∀ (keys : List (Block × Nat)) (st : GridCO.State n .root), (b, g) ∈ keys →
      ∃ d, (b, g, d) ∈ (GridCO.writeKeys st keys lim).obligations ∧ lim ≤ d := by
  intro keys
  induction keys with
  | nil => exact fun _ hk => absurd hk List.not_mem_nil
  | cons k ks ih =>
    intro st hk
    rw [@GridCO.writeKeys_def GridCO.slowLeasePolicy, List.foldl_cons,
      ← @GridCO.writeKeys_def GridCO.slowLeasePolicy]
    rcases List.mem_cons.mp hk with he | hk
    · subst he
      obtain ⟨d, hm, hd⟩ := arming_write_row st b g lim
      exact arming_writeKeys_keep ks lim _ b g d hm hd
    · exact ih _ hk

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.5. Class (iii). DC: INTENTIONAL; lease writes keep S. -/
theorem arming_writeKeys_stable {n : Nat} (lim : Time) :
    ∀ (keys : List (Block × Nat)) (st : GridCO.State n .root),
      (GridCO.writeKeys st keys lim).stableRecord = st.stableRecord := by
  intro keys
  induction keys with
  | nil => exact fun _ => rfl
  | cons k ks ih =>
    intro st
    rw [@GridCO.writeKeys_def GridCO.slowLeasePolicy, List.foldl_cons,
      ← @GridCO.writeKeys_def GridCO.slowLeasePolicy, ih]
    rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.5. Class (iii). DC: INTENTIONAL; the raw result at an actual
gate tick is the confirmation of its pre-gate clock. -/
theorem arming_gateResult_tick {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {k : Nat} {y : V} {j : Slot}
    (hk : enabledGateAt p c E rho k y j) :
    gateResult p c E rho y j = some (SA.Root.confirmationFrom p.toParams
      (eraseFG (FGSA.clockPre p (storeAt p c E rho k y) (SA.gateTime p.toParams j)).fg.F)
      (FGSA.actView (FGSA.clockPre p (storeAt p c E rho k y) (SA.gateTime p.toParams j))) j) := by
  rw [gateResult_eq_saved p c E rho hs hk.1]
  change GridCO.savedGenuine (FGSA.clock p (V2.D.Run.stateBefore E rho k y).st
    (SA.gateTime p.toParams j)).base j = _
  rw [fgsa_gate_saved_guarded E rho hs hk.1, fgsa_gate_joined_of_enabled E rho hk,
    ite_eq_left rfl, clockPre_fg]
  rfl

end AvailableChain.FGSA.Run
end
