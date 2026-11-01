module
public import AvailableChainSAPC.Proofs.Handling

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- A new archive member came from an actual handler call. Structural
containment of a rejected proposal is not sufficient. -/
theorem process_new_head_handled (p : Params) {n : Nat} (st : State n)
    (o : Wire n) (h : HeadWire n) (hnew : h ∉ st.receivedHeads)
    (hm : h ∈ (process p st o).receivedHeads) : handles p st o (fromHead h) := by
  unfold process at hm
  split at hm
  · rename_i r i data ha hp
    rw [admitHead, collectPCs_archive] at hm
    rcases receiveHead_archive_origin p st _ h hm with hold | rfl
    · exact (hnew hold).elim
    · left; cases o; simp_all [fromHead]
  · rename_i s b raw support c ha hp
    unfold admitProposal at hm
    split at hm
    · rename_i henter
      rw [collectPCs_archive] at hm
      rcases receiveHeads_archive_origin p _ _ h hm with hold | hmem
      · exact (hnew hold).elim
      · right
        simp only [ha, hp]
        exact ⟨henter, List.mem_map.mpr ⟨h, hmem, rfl⟩⟩
    · exact (hnew hm).elim
  · rename_i c ha hp
    split at hm
    · rename_i hready
      rw [collectPCs_archive] at hm
      rcases receiveHeads_archive_origin p _ _ h hm with hold | hmem
      · exact (hnew hold).elim
      · right
        simp only [ha, hp]
        exact ⟨hready, List.mem_map.mpr ⟨h, hmem, rfl⟩⟩
    · exact (hnew hm).elim
  · exact (hnew hm).elim

theorem stateBefore_archive_mono {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) {i j : Nat} (hij : i ≤ j) (v : V) :
    (Run.stateBefore (sapc p) rho i v).receivedHeads ⊆
      (Run.stateBefore (sapc p) rho j v).receivedHeads := by
  induction j with
  | zero => rw [Nat.le_zero.mp hij]
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · exact List.Subset.refl _
      · apply List.Subset.trans (ih (by omega))
        cases hj : rho.events[j]? with
        | none => simp [Run.stateBefore, List.take_add_one, hj]
        | some e =>
            rw [stateBefore_succ_event hj]
            cases e with
            | tick u t =>
                by_cases hv : v = u
                · subst u; simp [World.step, sapc, clock_archive]
                · simp [World.step, hv]
            | deliver u o t =>
                by_cases hv : v = u
                · subst u
                  simpa [World.step, sapc] using process_archive_mono p
                    (Run.stateBefore (sapc p) rho j v) o
                · simp [World.step, hv]

/-- Every archived HEAD has a first accepted call at its reader. The
acceptance can be inside a proposal or PC envelope. -/
theorem stored_head_accepted {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (index : Nat) (v : V) (h : HeadWire p.n)
    (hm : h ∈ (Run.stateBefore (sapc p) rho index v).receivedHeads) :
    ∃ j < index, ∃ t, Run.acceptsAt (sapc p) rho j v (fromHead h) t := by
  induction index with
  | zero => simp [Run.stateBefore, World.init, sapc, initial] at hm
  | succ index ih =>
      by_cases hold : h ∈ (Run.stateBefore (sapc p) rho index v).receivedHeads
      · obtain ⟨j, hj, t, ha⟩ := ih hold
        exact ⟨j, by omega, t, ha⟩
      · cases hi : rho.events[index]? with
        | none => simp [Run.stateBefore, List.take_add_one, hi] at hm; exact (hold hm).elim
        | some e =>
            rw [stateBefore_succ_event hi] at hm
            cases e with
            | tick u t =>
                by_cases hv : v = u
                · subst u
                  exact (hold (by simpa [World.step, sapc, clock_archive] using hm)).elim
                · exact (hold (by simpa [World.step, hv] using hm)).elim
            | deliver u o t =>
                by_cases hv : v = u
                · subst u
                  have hnew : h ∈
                      (process p (Run.stateBefore (sapc p) rho index v) o).receivedHeads := by
                    simpa [World.step, sapc] using hm
                  refine ⟨index, by omega, t, ⟨o, hi,
                    process_new_head_handled p _ o h hold hnew⟩, ?_, ?_⟩
                  · simpa [sapc, processed, fromHead] using hold
                  · rw [stateBefore_succ_event hi]
                    simpa [World.step, sapc, processed, fromHead] using hnew
                · exact (hold (by simpa [World.step, hv] using hm)).elim

theorem time_input_eq_event_prefix {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho) (t : Time) :
    Run.stateBeforeTime (sapc p) rho t = Run.stateBefore (sapc p) rho
      (rho.events.filter (fun e => decide (e.time ≤ t - 1))).length := by
  have he : Run.stateBeforeTime (sapc p) rho t = Run.readAt (sapc p) rho (t - 1) := by
    simp only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
  exact he.trans (readAt_eq_stateBefore hs (t - 1))

/-- An accepted member remains available at every later strict read. -/
theorem accepted_head_before_cut {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (index : Nat) (v : V) (h : HeadWire p.n) (t cut : Time)
    (ha : Run.acceptsAt (sapc p) rho index v (fromHead h) t) (ht : t < cut) :
    h ∈ (Run.stateBeforeTime (sapc p) rho cut v).receivedHeads := by
  obtain ⟨parent, hi, _⟩ := ha.1
  have hm : h ∈ (Run.stateBefore (sapc p) rho (index + 1) v).receivedHeads := by
    simpa [sapc, processed, fromHead] using ha.2.2
  rw [time_input_eq_event_prefix p E rho hs]
  apply stateBefore_archive_mono p rho (v := v) _ hm
  exact Nat.succ_le_of_lt ((index_lt_read_length_iff hs (cut - 1) hi).mpr
    (Int.le_sub_one_iff.mpr ht))

/-- The accepted-object relay premise transfers complete raw evidence.
It applies to old certificates and sleeping readers. -/
theorem accepted_head_relay {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hrelay : AcceptedObjectRelay (sapc p) E rho)
    (index : Nat) (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (h : HeadWire p.n) (t : Time)
    (ha : Run.acceptsAt (sapc p) rho index v (fromHead h) t)
    (horizon : max t E.t_GST + E.Δ ≤ rho.horizon) :
    h ∈ (Run.stateBeforeTime (sapc p) rho (max t E.t_GST + E.Δ) w).receivedHeads := by
  by_cases hm : h ∈ (Run.stateBefore (sapc p) rho (index + 1) w).receivedHeads
  · obtain ⟨parent, hi, _⟩ := ha.1
    rw [time_input_eq_event_prefix p E rho hs]
    apply stateBefore_archive_mono p rho (v := w) _ hm
    apply Nat.succ_le_of_lt
    apply (index_lt_read_length_iff hs _ hi).mpr
    apply Int.le_sub_one_iff.mpr
    change t < max t E.t_GST + E.Δ
    have := E.Δ_pos
    have := le_max_left t E.t_GST
    linarith
  · obtain ⟨t', _, ht', j, hj⟩ := hrelay v hv index (fromHead h) t ha w hw
      (by simpa [sapc, processed, fromHead] using hm) horizon
    exact accepted_head_before_cut p E rho hs j w h t' _ hj ht'

/-- The same raw-evidence transfer holds on a healthy outage prefix. -/
theorem accepted_head_healthy_relay {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho) (cut : Time)
    (hrelay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (index : Nat) (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (h : HeadWire p.n) (t : Time)
    (ha : Run.acceptsAt (sapc p) rho index v (fromHead h) t)
    (hcut : t + E.Δ ≤ cut) :
    h ∈ (Run.stateBeforeTime (sapc p) rho (t + E.Δ) w).receivedHeads := by
  by_cases hm : h ∈ (Run.stateBefore (sapc p) rho (index + 1) w).receivedHeads
  · obtain ⟨parent, hi, _⟩ := ha.1
    rw [time_input_eq_event_prefix p E rho hs]
    apply stateBefore_archive_mono p rho (v := w) _ hm
    apply Nat.succ_le_of_lt
    apply (index_lt_read_length_iff hs _ hi).mpr
    exact Int.le_sub_one_iff.mpr (by simpa [Event.time] using E.Δ_pos)
  · obtain ⟨t', _, ht', j, hj⟩ := hrelay v hv index (fromHead h) t ha w hw
      (by simpa [sapc, processed, fromHead] using hm) hcut
    exact accepted_head_before_cut p E rho hs j w h t' _ hj ht'

end AvailableChain.SAPC
end
