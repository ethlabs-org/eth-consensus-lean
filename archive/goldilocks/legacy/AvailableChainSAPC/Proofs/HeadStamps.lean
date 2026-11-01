module
public import AvailableChainSAPC.Proofs.Acceptance
public import AvailableChainGridCO.Proofs.Receipts

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

def ArchiveStamped {n : Nat} (st : State n) : Prop :=
  ∀ o ∈ st.receivedHeads, ∃ t, (o, t) ∈ st.headStamp

theorem collectPCs_headStamp (p : Params) {n : Nat} (st : State n) :
    (collectPCs p st).headStamp = st.headStamp :=
  collectPCs_field p State.headStamp (by intros; rfl) st

theorem clock_headStamp (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clock p st t).headStamp = st.headStamp := by
  unfold clock
  dsimp only
  split_ifs <;> simp only [gate, saveTimely]
  all_goals (try split_ifs) <;> rfl

theorem receiveHead_stamp_prefix (p : Params) {n : Nat} (st : State n) (o : HeadWire n) :
    st.headStamp <+: (receiveHead p st o).headStamp := by
  unfold receiveHead
  split
  · dsimp only
    split
    · exact List.prefix_refl _
    · split
      · exact List.prefix_refl _
      · exact List.prefix_append _ _
  · exact List.prefix_refl _

private theorem receiveHeads_stamp_prefix (p : Params) {n : Nat} (st : State n)
    (xs : List (HeadWire n)) : st.headStamp <+: (xs.foldl (receiveHead p) st).headStamp := by
  induction xs generalizing st with
  | nil => exact List.prefix_refl _
  | cons x xs ih => exact (receiveHead_stamp_prefix p st x).trans (ih _)

theorem process_stamp_prefix (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    st.headStamp <+: (process p st o).headStamp := by
  unfold process
  split
  · simpa only [admitHead, collectPCs_headStamp] using receiveHead_stamp_prefix p st _
  · unfold admitProposal
    split
    · rename_i s b raw support c ha hp henter
      rw [collectPCs_headStamp]
      exact receiveHeads_stamp_prefix p
        { st with base := proposalBase p st o b raw support, proposals := st.proposals ++ [o] }
        (raw ++ pcMembers c)
    · exact List.prefix_refl _
  · split
    · rw [collectPCs_headStamp]
      exact receiveHeads_stamp_prefix p _ _
    · exact List.prefix_refl _
  · exact List.prefix_refl _

theorem receiveHead_stamped (p : Params) {n : Nat} (st : State n) (o : HeadWire n)
    (h : ArchiveStamped st) : ArchiveStamped (receiveHead p st o) := by
  unfold receiveHead
  split
  · dsimp only
    split
    · exact h
    · split
      · exact h
      · intro x hx
        rcases List.mem_append.mp hx with hold | hnew
        · obtain ⟨t, ht⟩ := h x hold
          exact ⟨t, List.mem_append_left _ ht⟩
        · have he := List.mem_singleton.mp hnew
          subst x
          exact ⟨st.base.now, by simp⟩
  · exact h

private theorem receiveHeads_stamped (p : Params) {n : Nat} (st : State n)
    (xs : List (HeadWire n)) (h : ArchiveStamped st) :
    ArchiveStamped (xs.foldl (receiveHead p) st) := by
  induction xs generalizing st with
  | nil => exact h
  | cons x xs ih => exact ih _ (receiveHead_stamped p st x h)

private theorem collectPCs_stamped (p : Params) {n : Nat} (st : State n)
    (h : ArchiveStamped st) : ArchiveStamped (collectPCs p st) := by
  simpa only [ArchiveStamped, collectPCs_archive, collectPCs_headStamp] using h

theorem process_stamped (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (h : ArchiveStamped st) : ArchiveStamped (process p st o) := by
  unfold process
  split
  · exact collectPCs_stamped p _ (receiveHead_stamped p st _ h)
  · unfold admitProposal
    split
    · exact collectPCs_stamped p _ (receiveHeads_stamped p _ _ h)
    · exact h
  · split
    · exact collectPCs_stamped p _ (receiveHeads_stamped p st _ h)
    · exact h
  · exact h

theorem archiveStamped_at_fold {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (sapc p).Object)) (v : V) :
    ArchiveStamped ((events.foldl World.step World.init) v) := by
  apply fold_invariant p ArchiveStamped
  · simp [ArchiveStamped, initial]
  · intro st t h
    simpa only [ArchiveStamped, clock_archive, clock_headStamp] using h
  · exact process_stamped p

/-- A stamped signature keeps its first receipt stamp under every
append-only extension. Later changes of the fallback clock are irrelevant. -/
theorem stampHead_eq_of_prefix {n : Nat} (before after : State n)
    (h : ArchiveStamped before) (hp : before.headStamp <+: after.headStamp)
    (o : HeadWire n) (ho : o ∈ before.receivedHeads) :
    stampHead after o = stampHead before o :=
  GridCO.stamp_eq_of_prefix _ _ o _ _ hp (h o ho)

theorem stateBefore_stamp_prefix {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) {i j : Nat} (hij : i ≤ j) (v : V) :
    (Run.stateBefore (sapc p) rho i v).headStamp <+:
      (Run.stateBefore (sapc p) rho j v).headStamp := by
  induction j with
  | zero => rw [Nat.le_zero.mp hij]
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · exact List.prefix_refl _
      · apply (ih (by omega)).trans
        cases hj : rho.events[j]? with
        | none => simp [Run.stateBefore, List.take_add_one, hj]
        | some e =>
            rw [stateBefore_succ_event hj]
            cases e with
            | tick u t =>
                by_cases hv : v = u
                · subst u; simp [World.step, sapc, clock_headStamp]
                · simp [World.step, hv]
            | deliver u o t =>
                by_cases hv : v = u
                · subst u
                  simpa [World.step, sapc] using process_stamp_prefix p
                    (Run.stateBefore (sapc p) rho j v) o
                · simp [World.step, hv]

theorem stampHead_eq_at_later_input {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) {i j : Nat} (hij : i ≤ j) (v : V) (o : HeadWire p.n)
    (ho : o ∈ (Run.stateBefore (sapc p) rho i v).receivedHeads) :
    stampHead (Run.stateBefore (sapc p) rho j v) o =
      stampHead (Run.stateBefore (sapc p) rho i v) o :=
  stampHead_eq_of_prefix _ _ (archiveStamped_at_fold p _ v)
    (stateBefore_stamp_prefix p rho hij v) o ho

theorem stampHead_eq_at_later_read {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (v : V) (t t' : Time) (ht : t ≤ t') (o : HeadWire p.n)
    (ho : o ∈ (Run.readAt (sapc p) rho t v).receivedHeads) :
    stampHead (Run.readAt (sapc p) rho t' v) o = stampHead (Run.readAt (sapc p) rho t v) o := by
  rw [readAt_eq_stateBefore hs] at ho
  rw [readAt_eq_stateBefore hs, readAt_eq_stateBefore hs]
  exact stampHead_eq_at_later_input p rho (read_length_mono t t' ht) v o ho

end AvailableChain.SAPC
end
