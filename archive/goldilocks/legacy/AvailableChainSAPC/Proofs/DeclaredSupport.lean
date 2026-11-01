module
public import AvailableChainSAPC.Proofs.BaseViews

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- Stored proposal metadata cannot declare support outside its raw view. -/
def DeclaredSupport {n : Nat} (st : GridCO.State n) : Prop :=
  ∀ o ∈ st.proposals, ∀ b raw support, o.payload = .proposal b raw support → support ⊆ raw

theorem wellFormed_support_subset (p : Params) {n : Nat} (o : Wire n)
    (b : Block) (raw support : List (HeadWire n)) (c : Option (PC n))
    (hp : o.payload = .proposal b raw support c) (hw : wellFormed p o = true) :
    support ⊆ raw := by
  cases ha : o.auth <;> simp only [wellFormed, ha, hp] at hw
  all_goals first
    | contradiction
    | intro h hh
      exact of_decide_eq_true (List.all_eq_true.mp
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).2 h hh)

theorem process_declaredSupport (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (h : DeclaredSupport st.base) (hw : wellFormed p o = true) :
    DeclaredSupport (process p st o).base := by
  have hcollect (st : State n) (h : DeclaredSupport st.base) :
      DeclaredSupport (collectPCs p st).base := by simpa only [collectPCs_base] using h
  have hfold (st : State n) (xs : List (HeadWire n)) (h : DeclaredSupport st.base) :
      DeclaredSupport (xs.foldl (receiveHead p) st).base := by
    simpa only [DeclaredSupport, receiveHeads_base_proposals] using h
  unfold process
  split
  · apply hcollect
    simpa only [DeclaredSupport, receiveHead_base_proposals] using h
  · rename_i slot b raw support c ha hp
    unfold admitProposal
    split
    · rename_i he
      apply hcollect
      apply hfold
      intro key hk B R S hkey
      rw [(proposalEnters_data p st o b raw support he).1] at hk
      rcases List.mem_append.mp hk with hold | hnew
      · exact h key hold B R S hkey
      · have heq := List.mem_singleton.mp hnew
        subst key
        have he : b = B ∧ raw.map baseHead = R ∧ support.map baseHead = S := by
          simpa only [baseProposal, GridCO.Msg.proposal.injEq] using hkey
        rw [← he.2.1, ← he.2.2]
        exact List.map_subset _ (wellFormed_support_subset p o b raw support c hp hw)
    · exact h
  · split
    · apply hcollect
      exact hfold st _ h
    · exact h
  · exact h

theorem declaredSupport_before {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (index : Nat) (v : V) : DeclaredSupport (Run.stateBefore (sapc p) rho index v).base := by
  induction index with
  | zero => simp [DeclaredSupport, Run.stateBefore, World.init, sapc, initial, GridCO.initial]
  | succ index ih =>
      cases hi : rho.events[index]? with
      | none => simpa [Run.stateBefore, List.take_add_one, hi] using ih
      | some e =>
          rw [stateBefore_succ_event hi]
          cases e with
          | tick u t =>
              by_cases hv : v = u
              · subst u
                simpa only [World.step, Function.update_self, sapc, DeclaredSupport,
                  clock_base_proposals] using ih
              · simpa [World.step, hv] using ih
          | deliver u o t =>
              by_cases hv : v = u
              · subst u
                simpa only [World.step, Function.update_self, sapc] using
                  process_declaredSupport p _ o ih (hx.wire index v o t hi)
              · simpa [World.step, hv] using ih

theorem declaredSupport_beforeTime {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (t : Time) (v : V) : DeclaredSupport (Run.stateBeforeTime (sapc p) rho t v).base := by
  rw [time_input_eq_event_prefix p E rho hx.toScheduleWellFormed]
  exact declaredSupport_before p E rho hx _ v

theorem carriedSupport_subset_raw {n : Nat} (st : GridCO.State n)
    (h : DeclaredSupport st) (s : Slot) :
    GridCO.carriedSupport st s ⊆ GridCO.carriedRaw st s := by
  intro o ho
  obtain ⟨hm, ht⟩ := List.mem_filter.mp ho
  apply List.mem_filter.mpr
  refine ⟨?_, (Bool.and_eq_true_iff.mp ht).1⟩
  obtain ⟨parent, hp, hm⟩ := List.mem_flatMap.mp hm
  refine List.mem_flatMap.mpr ⟨parent, hp, ?_⟩
  cases he : parent.payload with
  | head b => simp [he] at hm
  | proposal b raw support =>
      simp only [he] at hm ⊢
      exact List.map_subset _ (h parent (List.mem_filter.mp hp).1 b raw support he) hm

/-- A later resolution can only filter the declared support; it cannot
promote an undeclared raw member into support. -/
theorem voterSupport_subset_raw (p : Params) {n : Nat} (st : State n)
    (hf : FrozenViewsStored st.base) (hp : DeclaredSupport st.base) (s : Slot) :
    GridCO.voterSupportView p.engine st.base s ⊆ GridCO.voterView p.engine st.base s := by
  intro o ho
  apply List.mem_eraseDups.mpr
  rcases List.mem_append.mp (List.mem_eraseDups.mp ho) with hfr | hc
  · apply List.mem_append_left
    cases he : GridCO.frozenAt st.base (s - 1) with
    | none => simp [he] at hfr
    | some view =>
        simpa only [he] using
          (frozenAt_stored st.base hf _ view.1 view.2.1 view.2.2 he).2.1
            (by simpa only [he] using hfr)
  · exact List.mem_append_right _ (carriedSupport_subset_raw st.base hp s hc)

theorem voterSupport_subset_before {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (index : Nat) (v : V) (s : Slot) :
    GridCO.voterSupportView p.engine (Run.stateBefore (sapc p) rho index v).base s ⊆
      GridCO.voterView p.engine (Run.stateBefore (sapc p) rho index v).base s :=
  voterSupport_subset_raw p _ (frozenViewsStored_at_fold p _ v)
    (declaredSupport_before p E rho hx index v) s

theorem voterSupport_subset_beforeTime {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (t : Time) (v : V) (s : Slot) :
    GridCO.voterSupportView p.engine (Run.stateBeforeTime (sapc p) rho t v).base s ⊆
      GridCO.voterView p.engine (Run.stateBeforeTime (sapc p) rho t v).base s :=
  voterSupport_subset_raw p _ (frozenViewsStored_at_fold p _ v)
    (declaredSupport_beforeTime p E rho hx t v) s

end AvailableChain.SAPC
end
