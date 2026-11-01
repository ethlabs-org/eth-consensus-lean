module
public import AvailableChainPCSAProofs.Proofs.Clean.AckTargetBody
public import AvailableChainPCSAProofs.Proofs.Shared.PCViews
public import AvailableChainPCSAProofs.Proofs.Clean.BodyStamps

public section

/-! C6 PCScope: concrete receipt and count support. -/
namespace AvailableChain.PCSA
variable {n : Nat}
private theorem pcscope_norm (st : State n) :
    (normalizeS st).pcs = st.pcs ∧ (normalizeS st).base.blocks = st.base.blocks := by
  delta normalizeS
  split <;> exact ⟨rfl, rfl⟩
private theorem pcscope_reconcile (st : State n) :
    (reconcile st).pcs ⊆ st.pcs ∧ (reconcile st).base.blocks = st.base.blocks := by
  delta reconcile
  rw [(pcscope_norm _).1, (pcscope_norm _).2]
  exact ⟨fun _ hm => (List.mem_filter.mp hm).1, rfl⟩
private theorem pcscope_row (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).pcs = st.pcs ∧ (admitRow p st a).base.blocks = st.base.blocks := by
  delta admitRow
  cases a.decode? with
  | none => exact ⟨rfl, rfl⟩
  | some v => dsimp only; split <;> exact ⟨rfl, rfl⟩
private theorem pcscope_raw (st : State n) (a : AckWire n) :
    (poolAckRaw st a).pcs = st.pcs ∧ (poolAckRaw st a).base.blocks = st.base.blocks := by
  delta poolAckRaw
  cases a.decode? with
  | none => exact ⟨rfl, rfl⟩
  | some v => dsimp only; split <;> exact ⟨rfl, rfl⟩
private theorem pcscope_pool (p : Params) (st : State p.n) (a : AckWire p.n) :
    (poolAck p st a).pcs = st.pcs := by
  delta poolAck
  cases a.decode? with
  | none => rfl
  | some v =>
    rcases v with ⟨s, i, r⟩
    dsimp only
    split
    · rfl
    · split <;> rfl
private theorem pcscope_rows (p : Params) (st : State p.n) (rows : List (RowWire p.n)) :
    (rows.foldl (admitRow p) st).pcs = st.pcs ∧
      (rows.foldl (admitRow p) st).base.blocks = st.base.blocks := by
  apply List.foldlRecOn (motive := fun acc : State p.n =>
    acc.pcs = st.pcs ∧ acc.base.blocks = st.base.blocks)
  · exact ⟨rfl, rfl⟩
  · intro acc hh a _
    exact ⟨((pcscope_row p acc a).1).trans hh.1, ((pcscope_row p acc a).2).trans hh.2⟩
private theorem pcscope_raws (st : State n) (acks : List (AckWire n)) :
    (acks.foldl poolAckRaw st).pcs = st.pcs := by
  apply List.foldlRecOn (motive := fun acc : State n => acc.pcs = st.pcs)
  · rfl
  · intro acc hh a _
    exact ((pcscope_raw acc a).1).trans hh
/-- A collected PC was already held or has a target in the resulting body pool. -/
theorem pcsa_collect_pc_target_origin (st : State n) (C : PC n)
    (hm : C ∈ (collectPCs st).pcs) : C ∈ st.pcs ∨ C.target ∈ (collectPCs st).base.blocks := by
  have h := collectPCs_invariant
    (fun acc : State n => ∀ C ∈ acc.pcs, C ∈ st.pcs ∨ C.target ∈ acc.base.blocks)
    (by
      intro acc D hh hv C hc
      rw [(installPC_frame acc D).2.1]
      rcases mem_installPC_pcs acc D C hc with hc | rfl
      · exact hh C hc
      · right
        exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).2)
    st (fun C hc => Or.inl hc)
  exact h C hm
/-- Every newly installed target is in the completed delivery's body pool. -/
theorem pcsa_process_pc_target_origin (p : Params) (st : State p.n) (o : Wire p.n)
    (C : PC p.n) (hm : C ∈ (process p st o).pcs) :
    C ∈ st.pcs ∨ C.target ∈ (process p st o).base.blocks := by
  delta process at hm ⊢
  cases hd : o.decode with
  | none => rw [hd] at hm; exact Or.inl hm
  | some msg =>
    rw [hd] at hm
    cases msg with
    | vote s i r => exact Or.inl hm
    | row i body =>
      rw [(pcscope_row p st _).1] at hm
      exact Or.inl hm
    | ack s i r =>
      rcases pcsa_collect_pc_target_origin (poolAck p st _) C hm with ho | hb
      · rw [pcscope_pool] at ho
        exact Or.inl ho
      · exact Or.inr hb
    | pc D =>
      dsimp only at hm ⊢
      delta admitPC at hm ⊢
      split at hm
      · rename_i hw
        rw [ite_eq_left hw]
        rcases pcsa_collect_pc_target_origin _ C hm with ho | hb
        · rw [pcscope_raws] at ho
          exact Or.inl ho
        · exact Or.inr hb
      · rename_i hw
        rw [ite_eq_right hw]
        exact Or.inl hm
    | block s N =>
      dsimp only at hm ⊢
      delta admitBlock at hm ⊢
      split at hm
      · rename_i hn
        rw [ite_eq_left hn]
        exact Or.inl hm
      · rename_i hn
        rw [ite_eq_right hn]
        cases hp : parentFG st N.erase with
        | none => rw [hp] at hm; exact Or.inl hm
        | some P =>
          rw [hp] at hm
          change C ∈ (if blockAccepted p st s N P then _ else st).pcs at hm
          change C ∈ st.pcs ∨ C.target ∈ (if blockAccepted p st s N P then _ else st).base.blocks
          split at hm
          · rename_i ha
            rw [ite_eq_left ha, (pcscope_rows p _ N.rows).2]
            rw [(pcscope_rows p _ N.rows).1] at hm
            rcases pcsa_collect_pc_target_origin _ C hm with ho | hb
            · rw [pcscope_raws] at ho
              let st1 : State p.n := { st with
                base := GridCO.admitProposal p.toParams.engine st.base
                  (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) }
              let st2 := match N.pc with
                | none => st1
                | some D => if pcValid st1 D && !st1.pcs.any
                    (fun old => old.slot == D.slot && old.target == D.target)
                  then deleteConflictingLeases st1 D else st1
              let st3 : State p.n := { st2 with
                fg := FGSA.Window.on_block p p.K_W st2.fg (fgBlock P N.erase N.rows)
                proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
              change C ∈ (if st3.fg.F = st.fg.F then st3 else reconcile st3).pcs at ho
              have hpcs : st3.pcs = st.pcs := by
                change st2.pcs = st.pcs
                dsimp only [st2]
                cases N.pc with
                | none => rfl
                | some D => dsimp only; split <;> rfl
              split at ho
              · exact Or.inl (hpcs ▸ ho)
              · have hkeep := (pcscope_reconcile st3).1 ho
                exact Or.inl (hpcs ▸ hkeep)
            · exact Or.inr hb
          · rename_i ha
            rw [ite_eq_right ha]
            exact Or.inl hm
/-- Every held PC target remains in the cumulative body pool. -/
theorem pcsa_pc_targets_held (p : Params) (st : State p.n) (h : Reachable p st) :
    ∀ C ∈ st.pcs, C.target ∈ st.base.blocks := by
  induction h with
  | init => intro C hc; exact (List.not_mem_nil hc).elim
  | tick t h ih =>
    rw [pcsa_clock_pcs, pcsa_clock_blocks]
    exact ih
  | @deliver st o h ih =>
    intro C hc
    rcases pcsa_process_pc_target_origin p st o C hc with hold | hnew
    · exact pcsa_body_process_keep p st o h (ih C hold)
    · exact hnew
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Every installed PC target belongs to the run's named-body collision scope. -/
theorem pcsa_clean_pc_scope (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (j : Nat) (x : V) (hx : x ∈ rho.honest) :
    ∀ C ∈ (V2.D.Run.stateBefore E rho j x).st.pcs, RootBlockInRun p c E rho C.target := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => ∀ C ∈ nd.st.pcs, RootBlockInRun p c E rho C.target)
    (Nat.zero_le j) x ?_ (by intro C hc; exact (List.not_mem_nil hc).elim)
  intro k e _ _ he hy ih
  cases e with
  | restart y t =>
    change y = x at hy
    subst y
    change ∀ C ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.pcs, _
    rw [Function.update_self]
    intro C hc
    exact (List.not_mem_nil hc).elim
  | tick y t =>
    change y = x at hy
    subst y
    change ∀ C ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.pcs, _
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t
    rw [ht, pcsa_clock_pcs]
    exact ih
  | deliver y o t =>
    change y = x at hy
    subst y
    change ∀ C ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.pcs, _
    rw [Function.update_self]
    intro C hc
    rcases pcsa_process_pc_target_origin p _ (toWire p o) C hc with hold | hnew
    · exact ih C hold
    · apply pcsa_body_scope E rho (k + 1) x hx C.target
      rw [V2.D.Run.stateBefore_succ E rho he]
      change C.target ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.blocks
      rw [Function.update_self]
      exact hnew
end AvailableChain.PCSA.Run

end
