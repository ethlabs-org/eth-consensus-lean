module
public import AvailableChainPCSAProofs.Proofs.Clean.FormationFreeze
public import AvailableChainPCSAProofs.Proofs.Clean.FormationView
public import AvailableChainPCSAProofs.Proofs.Clean.PCScope
public import AvailableChainFGSA.Proofs.Metadata

public section

/-! FormationSource retention. Stored blocks grow without restart.
Stage 1 keeps frozen PC entries through deliveries and later ticks.
A stamped PC supplies its stored target and opening snapshot at the action
read. C1 target uniqueness stays an explicit connection input.
The stamped-PC part of C7 supplies the retained own-slot snapshot. -/

namespace AvailableChain.PCSA
variable {n : Nat}

private theorem formation_row_blocks (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).base.blocks = st.base.blocks := by
  delta admitRow
  cases a.decode? with
  | none => rfl
  | some val => dsimp only; split <;> rfl

private theorem formation_rows_blocks (p : Params) (st : State p.n) (as : List (RowWire p.n)) :
    (as.foldl (admitRow p) st).base.blocks = st.base.blocks := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, formation_row_blocks]

private theorem formation_raw_blocks (st : State n) (as : List (AckWire n)) :
    (as.foldl poolAckRaw st).base.blocks = st.base.blocks := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, (poolAckRaw_frame st a).2.2.1]

private theorem formation_normalize_blocks (st : State n) :
    (normalizeS st).base.blocks = st.base.blocks := by
  delta normalizeS
  split <;> rfl

private theorem formation_reconcile_blocks (st : State n) :
    (reconcile st).base.blocks = st.base.blocks := by
  delta reconcile
  rw [formation_normalize_blocks]

private abbrev formationAccepted (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n)) : State p.n :=
  let st1 : State p.n := { st with
    base := GridCO.admitProposal p.toParams.engine st.base
      (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) }
  let st1 := match N.pc with
    | none => st1
    | some C => if pcValid st1 C &&
        !st1.pcs.any (fun old => old.slot == C.slot && old.target == C.target)
      then deleteConflictingLeases st1 C else st1
  let st1 := { st1 with
    fg := FGSA.Window.on_block p p.K_W st1.fg (fgBlock P N.erase N.rows)
    proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
  let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
  N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw st2))

/-- Every handler keeps all stored target blocks. -/
theorem pcsa_formation_process_blocks_mono (p : Params) (st : State p.n) (o : Wire p.n) :
    st.base.blocks ⊆ (process p st o).base.blocks := by
  delta process
  cases o.decode with
  | none => exact List.Subset.refl _
  | some d =>
    cases d with
    | vote s i root =>
      change st.base.blocks ⊆ (GridCO.admitVote p.toParams.engine st.base _).blocks
      rw [GridCO.admitVote_blocks]
    | row i body => rw [formation_row_blocks]
    | ack s i root =>
      change st.base.blocks ⊆ (collectPCs (poolAck p st ⟨o.auth, root⟩)).base.blocks
      rw [(collectPCs_frame _).2.1]
      delta poolAck
      cases (AckWire.decode? (⟨o.auth, root⟩ : AckWire p.n)) with
      | none => exact List.Subset.refl _
      | some val => rcases val with ⟨s, i, root⟩; dsimp only; split_ifs <;> exact List.Subset.refl _
    | pc C =>
      change st.base.blocks ⊆ (admitPC st C).base.blocks
      delta admitPC
      split
      · rw [(collectPCs_frame _).2.1, formation_raw_blocks]
      · exact List.Subset.refl _
    | block s N =>
      change st.base.blocks ⊆ (admitBlock p st s N).base.blocks
      delta admitBlock
      split
      · exact List.Subset.refl _
      · cases parentFG st N.erase with
        | none => exact List.Subset.refl _
        | some P =>
          change st.base.blocks ⊆
            (if blockAccepted p st s N P then formationAccepted p st s N P else st).base.blocks
          split
          · delta formationAccepted
            rw [formation_rows_blocks, (collectPCs_frame _).2.1, formation_raw_blocks]
            cases N.pc <;> dsimp only <;> split_ifs <;>
              simp only [formation_reconcile_blocks, deleteConflictingLeases_def] <;>
              exact (FGSA.admitProposal_prefix p.toParams.engine st.base _ _ _).1.subset
          · exact List.Subset.refl _

private theorem formation_reconcile_fg (st : State n) : (reconcile st).fg = st.fg := by
  delta reconcile
  dsimp only
  delta normalizeS
  split <;> rfl

private theorem formation_reconcile_snapshot (st : State n) (hF : st.fg.F = .genesis) :
    (reconcile st).pcSnapshot = st.pcSnapshot := by
  delta reconcile
  rw [normalizeS_snapshot]
  change st.pcSnapshot.map (fun row =>
    (row.1, row.2.filter (fun C => activeCompatible st C.target))) = st.pcSnapshot
  have hall : ∀ C : PC n, activeCompatible st C.target = true := by
    intro C
    delta activeCompatible
    rw [hF]
    exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_genesis_preceq C.target))
  simp only [hall, List.filter_true, List.map_id']

/-- A stage-1 delivery keeps the complete frozen snapshot list. -/
theorem pcsa_formation_process_snapshot (p : Params) (st : State p.n) (o : Wire p.n)
    (hF : (process p st o).fg.F = .genesis) :
    (process p st o).pcSnapshot = st.pcSnapshot := by
  delta process at hF ⊢
  cases hd : o.decode with
  | none => rfl
  | some d =>
    rw [hd] at hF
    cases d with
    | vote s i root => rfl
    | row i body => rw [admitRow_snapshot]
    | ack s i root =>
      change (collectPCs (poolAck p st ⟨o.auth, root⟩)).pcSnapshot = st.pcSnapshot
      rw [(collectPCs_frame _).2.2.2.1]
      delta poolAck
      cases (AckWire.decode? (⟨o.auth, root⟩ : AckWire p.n)) with
      | none => rfl
      | some val => rcases val with ⟨s, i, root⟩; dsimp only; split_ifs <;> rfl
    | pc C =>
      change (admitPC st C).pcSnapshot = st.pcSnapshot
      delta admitPC
      split
      · rw [(collectPCs_frame _).2.2.2.1, fold_poolAckRaw_snapshot]
      · rfl
    | block s N =>
      change (admitBlock p st s N).pcSnapshot = st.pcSnapshot
      change (admitBlock p st s N).fg.F = .genesis at hF
      delta admitBlock at hF ⊢
      split
      · rfl
      · rename_i hnamed
        rw [ite_eq_right hnamed] at hF
        cases hp : parentFG st N.erase with
        | none => rfl
        | some P =>
          rw [hp] at hF
          change (if blockAccepted p st s N P then formationAccepted p st s N P else st).fg.F =
            .genesis at hF
          change (if blockAccepted p st s N P then
            formationAccepted p st s N P else st).pcSnapshot = st.pcSnapshot
          split
          · rename_i hacc
            rw [ite_eq_left hacc] at hF
            delta formationAccepted at hF ⊢
            rw [fold_admitRow_snapshot, (collectPCs_frame _).2.2.2.1, fold_poolAckRaw_snapshot]
            have hfgrow (st : State p.n) (as : List (RowWire p.n)) :
                (as.foldl (admitRow p) st).fg = st.fg := by
              induction as generalizing st with
              | nil => rfl
              | cons a as ih =>
                rw [List.foldl_cons, ih]
                delta admitRow
                cases a.decode? <;> dsimp only
                split <;> rfl
            have hfgraw (st : State p.n) (as : List (AckWire p.n)) :
                (as.foldl poolAckRaw st).fg = st.fg := by
              induction as generalizing st with
              | nil => rfl
              | cons a as ih => rw [List.foldl_cons, ih, (poolAckRaw_frame st a).2.2.2]
            rw [hfgrow, (collectPCs_frame _).2.2.2.2, hfgraw] at hF
            cases hpc : N.pc <;> rw [hpc] at hF <;> dsimp only at hF ⊢ <;> split_ifs at hF ⊢
            all_goals first
              | rfl
              | (rw [formation_reconcile_snapshot _] <;> first
                  | rfl
                  | simpa only [formation_reconcile_fg, deleteConflictingLeases_def] using hF)
          · rfl
/-- Every tick retains all entries of each existing frozen PC view. -/
theorem pcsa_formation_clock_snapshot_mono (p : Params) (st : State p.n) (t : Time) (s : Slot) :
    pcSnapshotAt st s ⊆ pcSnapshotAt (clock p st t) s := by
  have hclock : (clock p st t).pcSnapshot = (clockPre p st t).pcSnapshot := by
    delta clock
    dsimp only
    split
    · exact gateStep_snapshot p _ _
    · rfl
  have hframe := pcSnapshotAt_eq_of_list_eq (clock p st t) (clockPre p st t) s hclock
  rw [hframe]
  have hp := clockPre_snapshot p st t
  delta pcSnapshotAt
  rw [hp]
  dsimp only
  split
  · split
    · exact List.Subset.refl _
    · rw [List.find?_append]
      cases hf : st.pcSnapshot.find? (fun row => row.1 == s) with
      | none => exact List.nil_subset _
      | some row => exact List.Subset.refl _
  · exact List.Subset.refl _

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- NoRestart retains target blocks through all run steps. -/
theorem pcsa_formation_run_blocks_mono (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hNR : V2.D.NoRestart rho) (y : V) (i j : Nat) (hij : i ≤ j) :
    (V2.D.Run.stateBefore E rho i y).st.base.blocks ⊆
      (V2.D.Run.stateBefore E rho j y).st.base.blocks := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => (V2.D.Run.stateBefore E rho i y).st.base.blocks ⊆ nd.st.base.blocks)
    hij y ?_ (List.Subset.refl _)
  intro k e _ _ he hn hm
  cases e with
  | restart x t => exact (hNR k x t he).elim
  | tick x t =>
    change x = y at hn
    subst x
    change (V2.D.Run.stateBefore E rho i y).st.base.blocks ⊆
      (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.base.blocks
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k y) y t
    rw [ht, pcsa_clock_blocks]
    exact hm
  | deliver x o t =>
    change x = y at hn
    subst x
    change (V2.D.Run.stateBefore E rho i y).st.base.blocks ⊆
      (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.base.blocks
    rw [Function.update_self]
    exact List.Subset.trans hm (pcsa_formation_process_blocks_mono p _ (toWire p o))

/-- Stage 1 and NoRestart retain each frozen PC through all run steps. -/
theorem pcsa_formation_run_snapshot_mono (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hFrame : StageOneFrame p c E rho) (hNR : V2.D.NoRestart rho)
    (y : V) (hy : y ∈ rho.honest) (s : Slot) (i j : Nat) (hij : i ≤ j) :
    pcSnapshotAt (V2.D.Run.stateBefore E rho i y).st s ⊆
      pcSnapshotAt (V2.D.Run.stateBefore E rho j y).st s := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => pcSnapshotAt (V2.D.Run.stateBefore E rho i y).st s ⊆ pcSnapshotAt nd.st s)
    hij y ?_ (List.Subset.refl _)
  intro k e _ _ he hn hm
  cases e with
  | restart x t => exact (hNR k x t he).elim
  | tick x t =>
    change x = y at hn
    subst x
    change pcSnapshotAt (V2.D.Run.stateBefore E rho i y).st s ⊆
      pcSnapshotAt (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st s
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k y) y t
    rw [ht]
    exact List.Subset.trans hm (pcsa_formation_clock_snapshot_mono p _ t s)
  | deliver x o t =>
    change x = y at hn
    subst x
    have hOut : (PCSA.process p (V2.D.Run.stateBefore E rho k y).st (toWire p o)).fg.F =
        .genesis := by
      have hf := (hFrame y hy (k + 1)).1
      rw [V2.D.Run.stateBefore_succ E rho he] at hf
      delta V2.D.World.step at hf
      dsimp only at hf
      rw [Function.update_self] at hf
      exact hf
    change pcSnapshotAt (V2.D.Run.stateBefore E rho i y).st s ⊆
      pcSnapshotAt (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st s
    rw [Function.update_self]
    change pcSnapshotAt (V2.D.Run.stateBefore E rho i y).st s ⊆
      pcSnapshotAt (PCSA.process p (V2.D.Run.stateBefore E rho k y).st (toWire p o)) s
    rw [pcSnapshotAt_eq_of_list_eq _ _ s (pcsa_formation_process_snapshot p _ (toWire p o) hOut)]
    exact hm
/-- Later after-ticks reads retain all earlier target blocks. -/
theorem pcsa_formation_afterTicks_blocks_mono (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hBase : Base₂ p c E rho)
    (y : V) (t u : Time) (htu : t ≤ u) :
    (storeAfterTicks p c E rho y t).base.blocks ⊆
      (storeAfterTicks p c E rho y u).base.blocks := by
  change (FGSA.Run.afterTicks E rho t y).st.base.blocks ⊆
    (FGSA.Run.afterTicks E rho u y).st.base.blocks
  rw [FGSA.Run.afterTicks_eq_stateBefore E rho hBase.valid.toScheduleWellFormed,
    FGSA.Run.afterTicks_eq_stateBefore E rho hBase.valid.toScheduleWellFormed]
  exact pcsa_formation_run_blocks_mono E rho hBase.noRestart y _ _
    (FGSA.Run.afterTicksIdx_mono rho htu)

/-- Later after-ticks reads retain every earlier frozen PC entry. -/
theorem pcsa_formation_afterTicks_snapshot_mono (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hBase : Base₂ p c E rho)
    (hFrame : StageOneFrame p c E rho) (y : V) (hy : y ∈ rho.honest)
    (s : Slot) (t u : Time) (htu : t ≤ u) :
    pcSnapshotAt (storeAfterTicks p c E rho y t) s ⊆
      pcSnapshotAt (storeAfterTicks p c E rho y u) s := by
  change pcSnapshotAt (FGSA.Run.afterTicks E rho t y).st s ⊆
    pcSnapshotAt (FGSA.Run.afterTicks E rho u y).st s
  rw [FGSA.Run.afterTicks_eq_stateBefore E rho hBase.valid.toScheduleWellFormed,
    FGSA.Run.afterTicks_eq_stateBefore E rho hBase.valid.toScheduleWellFormed]
  exact pcsa_formation_run_snapshot_mono E rho hFrame hBase.noRestart y hy s _ _
    (FGSA.Run.afterTicksIdx_mono rho htu)

/-- A scheduled duty read has the same store as the after-ticks read. -/
theorem pcsa_formation_read_afterTicks (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.ScheduleWellFormed E rho)
    (y : V) (t : Time) (nd : Node p) (hr : pcsa_postClock E rho y t = some nd) :
    storeAfterTicks p c E rho y t = nd.st := by
  rw [pcsa_postClock_def] at hr
  obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hr
  rw [pcsa_preTick_def] at hp
  obtain ⟨k, hk, he⟩ := Option.map_eq_some_iff.mp hp
  subst pre
  subst nd
  change (FGSA.Run.afterTicks E rho t y).st = _
  rw [FGSA.Run.afterTicks_node E rho hv (V2.D.Run.tickIdx?_spec hk)]
  exact pcsa_tick_st E rho _ _ _

private theorem formation_clock_snapshot_eq (p : Params) (st : State p.n) (t : Time)
    (s : Slot) (hne : pcSnapshotAt st s ≠ []) :
    pcSnapshotAt (clock p st t) s = pcSnapshotAt st s := by
  have hclock : (clock p st t).pcSnapshot = (clockPre p st t).pcSnapshot := by
    delta clock
    dsimp only
    split
    · exact gateStep_snapshot p _ _
    · rfl
  rw [pcSnapshotAt_eq_of_list_eq _ _ s hclock]
  delta pcSnapshotAt
  rw [clockPre_snapshot]
  dsimp only
  split
  · split
    · rfl
    · rw [List.find?_append]
      cases hf : st.pcSnapshot.find? (fun row => row.1 == s) with
      | none => exact (hne (pcSnapshotAt_absent st s hf)).elim
      | some row => rfl
  · rfl

/-- A nonempty frozen view stays exact through stage-1 run steps. -/
theorem pcsa_formation_run_snapshot_eq (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hFrame : StageOneFrame p c E rho)
    (hNR : V2.D.NoRestart rho) (y : V) (hy : y ∈ rho.honest)
    (s : Slot) (i j : Nat) (hij : i ≤ j)
    (hne : pcSnapshotAt (V2.D.Run.stateBefore E rho i y).st s ≠ []) :
    pcSnapshotAt (V2.D.Run.stateBefore E rho j y).st s =
      pcSnapshotAt (V2.D.Run.stateBefore E rho i y).st s := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => pcSnapshotAt nd.st s =
      pcSnapshotAt (V2.D.Run.stateBefore E rho i y).st s) hij y ?_ rfl
  intro k e _ _ he hn hm
  cases e with
  | restart x t => exact (hNR k x t he).elim
  | tick x t =>
    change x = y at hn
    subst x
    change pcSnapshotAt (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st s = _
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k y) y t
    rw [ht, formation_clock_snapshot_eq p _ t s (hm.symm ▸ hne)]
    exact hm
  | deliver x o t =>
    change x = y at hn
    subst x
    have hOut : (PCSA.process p (V2.D.Run.stateBefore E rho k y).st (toWire p o)).fg.F =
        .genesis := by
      have hf := (hFrame y hy (k + 1)).1
      rw [V2.D.Run.stateBefore_succ E rho he] at hf
      delta V2.D.World.step at hf
      dsimp only at hf
      rw [Function.update_self] at hf
      exact hf
    change pcSnapshotAt (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st s = _
    rw [Function.update_self]
    change pcSnapshotAt (PCSA.process p (V2.D.Run.stateBefore E rho k y).st (toWire p o)) s = _
    rw [pcSnapshotAt_eq_of_list_eq _ _ s (pcsa_formation_process_snapshot p _ (toWire p o) hOut)]
    exact hm

/-- A nonempty frozen view stays exact at every later after-ticks read. -/
theorem pcsa_formation_afterTicks_snapshot_eq (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hBase : Base₂ p c E rho)
    (hFrame : StageOneFrame p c E rho) (y : V) (hy : y ∈ rho.honest)
    (s : Slot) (t u : Time) (htu : t ≤ u)
    (hne : pcSnapshotAt (storeAfterTicks p c E rho y t) s ≠ []) :
    pcSnapshotAt (storeAfterTicks p c E rho y u) s =
      pcSnapshotAt (storeAfterTicks p c E rho y t) s := by
  change pcSnapshotAt (FGSA.Run.afterTicks E rho u y).st s =
    pcSnapshotAt (FGSA.Run.afterTicks E rho t y).st s
  change pcSnapshotAt (FGSA.Run.afterTicks E rho t y).st s ≠ [] at hne
  rw [FGSA.Run.afterTicks_eq_stateBefore E rho hBase.valid.toScheduleWellFormed] at hne
  have heT := FGSA.Run.afterTicks_eq_stateBefore E rho hBase.valid.toScheduleWellFormed t
  have heU := FGSA.Run.afterTicks_eq_stateBefore E rho hBase.valid.toScheduleWellFormed u
  rw [heU, heT]
  exact pcsa_formation_run_snapshot_eq E rho hFrame hBase.noRestart y hy s _ _
    (FGSA.Run.afterTicksIdx_mono rho htu) hne

/-- A PC at an after-ticks read is still held at the inclusive read of that time. -/
theorem pcsa_formation_afterTicks_pcs_storeAt (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hBase : Base₂ p c E rho)
    (hFrame : StageOneFrame p c E rho) (y : V) (hy : y ∈ rho.honest) (t : Time) :
    (storeAfterTicks p c E rho y t).pcs ⊆ (storeAt p c E rho y t).pcs := by
  change (FGSA.Run.afterTicks E rho t y).st.pcs ⊆ (V2.D.Run.readAt E rho t y).st.pcs
  rw [FGSA.Run.afterTicks_eq_stateBefore E rho hBase.valid.toScheduleWellFormed,
    V2.D.Engine.readAt_eq_stateBefore hBase.valid.toScheduleWellFormed]
  exact pcsa_run_pcs_mono E rho hFrame hBase.noRestart y hy _ _
    (FGSA.Run.preIdx_le_afterTicksIdx E rho hBase.valid.toScheduleWellFormed t).2

variable [Fintype V]

omit [Fintype V] in
/-- A stamped Formation PC fixes the source under the C1 target-uniqueness input. -/
theorem pcsa_formation_source_of_retained_freeze (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hBase : Base₂ p c E rho)
    (hFrame : StageOneFrame p c E rho) (y : V) (hy : y ∈ rho.honest)
    (r : Nat) (P : Block) (nd : Node p)
    (hr : pcsa_postClock E rho y (p.actionTime r) = some nd)
    (hPC : PCStampedBefore p c E rho y (SA.freezeTime p.toParams (r * p.R)) (r * p.R) P)
    (hhor : SA.freezeTime p.toParams (r * p.R) ≤ rho.horizon)
    (hPCUnique : ∀ A ∈ (storeAt p c E rho y (SA.freezeTime p.toParams (r * p.R))).pcs,
      ∀ B ∈ (storeAt p c E rho y (SA.freezeTime p.toParams (r * p.R))).pcs,
      A.slot = B.slot → A.target = B.target) :
    ∃ B : SimplexFG.FGBlock (Fin p.n),
      actionSourceAt p c E rho y r = some (some B) ∧ eraseFG B = P := by
  have htime : SA.freezeTime p.toParams (r * p.R) ≤ p.actionTime r := by
    have hd : (0 : Int) < p.Δ := p.deltaPos
    change 4 * p.Δ * ((r * p.R : Nat) : Int) + 3 * p.Δ ≤
      4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    linarith
  have heq := pcsa_formation_read_afterTicks E rho hBase.valid.toScheduleWellFormed y _ nd hr
  rw [pcsa_PCStampedBefore_def] at hPC
  obtain ⟨C, hC, hs, ht⟩ := hPC
  have hHeld : P ∈ (storeAfterTicks p c E rho y
      (SA.freezeTime p.toParams (r * p.R))).base.blocks := by
    rw [← ht]
    exact pcsa_pc_targets_held p _ (reachable_storeAfterTicks E rho _ y) C hC
  have hheld := pcsa_formation_afterTicks_blocks_mono E rho hBase y _ _ htime hHeld
  rw [heq] at hheld
  have hsnap : C ∈ pcSnapshotAt (storeAfterTicks p c E rho y
      (SA.freezeTime p.toParams (r * p.R))) (r * p.R) := by
    rw [snapshot_afterTicks E rho hBase.valid.toScheduleWellFormed hBase.delta y hy _ hhor]
    exact hC
  have hne : pcSnapshotAt (storeAfterTicks p c E rho y
      (SA.freezeTime p.toParams (r * p.R))) (r * p.R) ≠ [] := by
    intro he
    rw [he] at hsnap
    exact List.not_mem_nil hsnap
  have hsnapEq := pcsa_formation_afterTicks_snapshot_eq E rho hBase hFrame y hy
    (r * p.R) _ _ htime hne
  rw [heq] at hsnapEq
  have hkeep : C ∈ pcSnapshotAt nd.st (r * p.R) := by rw [hsnapEq]; exact hsnap
  have hTarget : ∀ D ∈ pcSnapshotAt nd.st (r * p.R), D.slot = r * p.R → D.target = P := by
    intro D hD hDs
    rw [hsnapEq, snapshot_afterTicks E rho hBase.valid.toScheduleWellFormed
      hBase.delta y hy _ hhor] at hD
    have hmono := pcsa_formation_afterTicks_pcs_storeAt E rho hBase hFrame y hy
      (SA.freezeTime p.toParams (r * p.R))
    exact (hPCUnique D (hmono hD) C (hmono hC) (hDs.trans hs.symm)).trans ht
  have hreach : Reachable p nd.st := heq ▸ reachable_storeAfterTicks E rho _ y
  have hf := pcsa_formation_frame_read E rho hFrame y _ nd hy hr
  have hopen : p.round (nd.st.slot p) * p.R = r * p.R := by
    rw [pcsa_postClock_def] at hr
    obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hr
    subst nd
    exact pcsa_formation_source_opening p pre.st r
  obtain ⟨B, hb, he⟩ := pcsa_formation_fgSource_of_active_snapshot p nd.st r P hopen
    ⟨C, hkeep, hs, pcsa_formation_frame_active_of_target p nd.st C hreach hf (ht.symm ▸ hheld)⟩
    hTarget
  refine ⟨B, ?_, he⟩
  rw [pcsa_actionSourceAt_def, hr]
  exact congrArg (fun x => some x) hb
/-- The stamped-PC part of C7 supplies the source under the C1 uniqueness input. -/
theorem pcsa_formation_source_of_stamped_pc (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (r : Nat) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPrem p c E rho (r * p.R) N ΔF)
    (hPC : ∀ y ∈ rho.honest,
      PCStampedBefore p c E rho y (SA.freezeTime p.toParams (r * p.R)) (r * p.R) N.erase)
    (hPCUnique : ∀ y ∈ rho.honest,
      ∀ A ∈ (storeAt p c E rho y (SA.freezeTime p.toParams (r * p.R))).pcs,
      ∀ B ∈ (storeAt p c E rho y (SA.freezeTime p.toParams (r * p.R))).pcs,
      A.slot = B.slot → A.target = B.target) :
    ∀ y ∈ rho.honest, ∃ B : SimplexFG.FGBlock (Fin p.n),
      actionSourceAt p c E rho y r = some (some B) ∧ eraseFG B = N.erase := by
  intro y hy
  have hTime : p.actionTime r = SA.gateTime p.toParams (r * p.R) := rfl
  have hpub : V2.PublicTime E (p.actionTime r) := by
    refine ⟨4 * (r * p.R) + 6, ?_⟩
    rw [h.base.delta, hTime]
    change 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ =
      ((4 * (r * p.R) + 6 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hz : 0 ≤ p.actionTime r := by
    have hd : (0 : Int) < p.Δ := p.deltaPos
    change 0 ≤ 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    positivity
  have hm := h.base.valid.tick_total y hy _ hpub hz (hTime.symm ▸ h.horizon)
  have hsome : (V2.D.Run.tickIdx? rho y (p.actionTime r)).isSome = true := by
    delta V2.D.Run.tickIdx?
    rw [List.findIdx?_isSome, List.any_eq_true]
    exact ⟨_, hm, decide_eq_true ⟨rfl, rfl⟩⟩
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hsome
  let nd : Node p := (pcsaWith m p c).clock (V2.D.Run.stateBefore E rho k y) (p.actionTime r)
  have hr : pcsa_postClock E rho y (p.actionTime r) = some nd := by
    rw [pcsa_postClock_def, pcsa_preTick_def, hk]
    rfl
  exact pcsa_formation_source_of_retained_freeze E rho h.base h.frame y hy r N.erase nd hr
    (hPC y hy) (le_trans (le_of_lt (pcsa_freeze_lt_gate p _)) h.horizon) (hPCUnique y hy)

end AvailableChain.PCSA.Run

end
