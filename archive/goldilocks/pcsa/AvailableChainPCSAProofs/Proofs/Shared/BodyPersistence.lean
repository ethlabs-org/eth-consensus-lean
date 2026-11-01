module
public import AvailableChainPCSAProofs.Proofs.Shared.TreeReceipt

public section

/-! Body preservation for exact C3 receipt. -/

namespace AvailableChain.PCSA
open SimplexFG
variable {n : Nat}

private theorem pcsa_body_norm_fg (st : State n) : (normalizeS st).fg = st.fg := by
  delta normalizeS
  split <;> rfl
private theorem pcsa_body_reconcile_fg (st : State n) : (reconcile st).fg = st.fg := by
  delta reconcile
  rw [pcsa_body_norm_fg]
private theorem pcsa_body_row_fg (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).fg = st.fg := by
  delta admitRow
  cases a.decode? with
  | none => rfl
  | some v =>
    dsimp only
    split <;> rfl
private theorem pcsa_body_gate_fg (p : Params) (st : State n) (a : Block)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot) :
    (gateFrom p a cs rank st s).fg = st.fg := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => rfl
  | some X =>
    dsimp only
    split
    · rfl
    · apply List.foldlRecOn (motive := fun acc : State n => acc.fg = st.fg)
      · rfl
      · intro acc ha b _
        apply List.foldlRecOn (motive := fun acc : State n => acc.fg = st.fg)
        · exact ha
        · intro acc' ha' g _
          rw [(writeLease_frame acc' b g _ rank).2.2.2.2.2]
          exact ha'
/-- Clock steps keep the complete FG tree. -/
theorem pcsa_body_clock_fg (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).fg = st.fg := by
  have hp : (clockPre p st t).fg = st.fg := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> rfl
  delta clock
  dsimp only
  split
  · rw [gateStep_def, pcsa_body_norm_fg]
    split
    · exact hp
    · rw [pcsa_body_gate_fg]
      exact hp
  · exact hp

/-- Delivery steps keep every FG body, including through PC collection. -/
theorem pcsa_body_process_fg_mono (p : Params) (st : State p.n) (o : Wire p.n) :
    st.fg.TF ⊆ (process p st o).fg.TF := by
  let T := st.fg.TF
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : T ⊆ st.fg.TF) :
      T ⊆ (as.foldl poolAckRaw st).fg.TF := by
    apply List.foldlRecOn (motive := fun acc : State p.n => T ⊆ acc.fg.TF)
    · exact h
    · intro acc hh a _
      rw [(poolAckRaw_frame acc a).2.2.2]
      exact hh
  have hr (st : State p.n) (as : List (RowWire p.n)) (h : T ⊆ st.fg.TF) :
      T ⊆ (as.foldl (admitRow p) st).fg.TF := by
    apply List.foldlRecOn (motive := fun acc : State p.n => T ⊆ acc.fg.TF)
    · exact h
    · intro acc hh a _
      rw [pcsa_body_row_fg]
      exact hh
  delta process
  cases hd : o.decode with
  | none => exact Finset.Subset.refl _
  | some msg => cases msg with
    | vote s i r => exact Finset.Subset.refl _
    | row i body =>
      simpa only [pcsa_body_row_fg] using (Finset.Subset.refl st.fg.TF)
    | ack s i r =>
      change st.fg.TF ⊆ (collectPCs (poolAck p st (⟨o.auth, r⟩ : AckWire p.n))).fg.TF
      rw [(collectPCs_frame _).2.2.2.2]
      delta poolAck
      cases AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) with
      | none => exact Finset.Subset.refl _
      | some v =>
        rcases v with ⟨_, _, _⟩
        dsimp only
        split
        · exact Finset.Subset.refl _
        · split <;> exact Finset.Subset.refl _
    | pc C =>
      dsimp only
      delta admitPC
      split
      · rw [(collectPCs_frame _).2.2.2.2]
        exact ha st C.acks (Finset.Subset.refl _)
      · exact Finset.Subset.refl _
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact Finset.Subset.refl _
      · cases parentFG st N.erase with
        | none => exact Finset.Subset.refl _
        | some P =>
          dsimp only
          split
          · apply hr
            rw [(collectPCs_frame _).2.2.2.2]
            apply ha
            cases N.pc <;> dsimp only
            all_goals split_ifs <;> first
              | exact FGSA.Window.window_on_block_TF_subset p p.K_W st.fg _
              | (rw [pcsa_body_reconcile_fg]
                 exact FGSA.Window.window_on_block_TF_subset p p.K_W st.fg _)
          · exact Finset.Subset.refl _

/-- A reachable clock keeps every stored base body. -/
theorem pcsa_body_clock_keep (p : Params) (st : State p.n) (t : Time)
    (h : Reachable p st) : st.base.blocks ⊆ (clock p st t).base.blocks := by
  intro B hB
  obtain ⟨D, hD, he⟩ := (pcsa_tree_correspondence p st h B).mp hB
  exact (pcsa_tree_correspondence p _ (.tick t h) B).mpr
    ⟨D, by rwa [pcsa_body_clock_fg], he⟩
/-- A reachable delivery keeps every stored base body. -/
theorem pcsa_body_process_keep (p : Params) (st : State p.n) (o : Wire p.n)
    (h : Reachable p st) : st.base.blocks ⊆ (process p st o).base.blocks := by
  intro B hB
  obtain ⟨D, hD, he⟩ := (pcsa_tree_correspondence p st h B).mp hB
  exact (pcsa_tree_correspondence p _ (.deliver o h) B).mpr
    ⟨D, pcsa_body_process_fg_mono p st o hD, he⟩
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Without restarts, exact target bodies persist between event indices. -/
theorem pcsa_body_stateBefore_mono (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hn : V2.D.NoRestart rho)
    (y : V) {j k : Nat} (hjk : j ≤ k) :
    (V2.D.Run.stateBefore E rho j y).st.base.blocks ⊆
      (V2.D.Run.stateBefore E rho k y).st.base.blocks := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => (V2.D.Run.stateBefore E rho j y).st.base.blocks ⊆ nd.st.base.blocks)
    hjk y ?_ (List.Subset.refl _)
  intro l e _ _ he hy h
  cases e with
  | restart x t => exact (hn l x t he).elim
  | tick x t =>
    change x = y at hy
    subst x
    change _ ⊆ (Function.update (V2.D.Run.stateBefore E rho l) y _ y).st.base.blocks
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho l y) y t
    rw [ht]
    exact List.Subset.trans h (pcsa_body_clock_keep p _ t (pcsa_reachable_stateBefore E rho l y))
  | deliver x o t =>
    change x = y at hy
    subst x
    change _ ⊆ (Function.update (V2.D.Run.stateBefore E rho l) y _ y).st.base.blocks
    rw [Function.update_self]
    exact List.Subset.trans h
      (pcsa_body_process_keep p _ (toWire p o) (pcsa_reachable_stateBefore E rho l y))
end AvailableChain.PCSA.Run
end
