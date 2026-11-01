module
public import AvailableChainFGSA.Proofs.WindowStore
public import AvailableChainPCSA.Model.Handlers
public import AvailableChainPCSAProofs.Proofs.Foundations.AckPool
public import AvailableChainPCSAProofs.Proofs.Foundations.Snapshot

public section

namespace AvailableChain.PCSA
open SimplexFG
variable {n : Nat}

/-- Normalization changes no FG field. -/
theorem pcsa_normalizeS_fg (st : State n) : (normalizeS st).fg = st.fg := by
  unfold normalizeS
  split <;> rfl

/-- Reconciliation changes no FG field. -/
theorem pcsa_reconcile_fg (st : State n) : (reconcile st).fg = st.fg := by
  unfold reconcile
  rw [pcsa_normalizeS_fg]

/-- A clock changes no FG field. -/
theorem pcsa_clock_fg (p : Params) (st : State p.n) (t : Time) : (clock p st t).fg = st.fg := by
  unfold clock
  dsimp only
  split
  · unfold gateStep
    rw [pcsa_normalizeS_fg]
    split
    · exact (clockPre_output_fields p st t).1
    · rw [(gateFrom_pc_frame _ _ _ _ _ _).2]
      exact (clockPre_output_fields p st t).1
  · exact (clockPre_output_fields p st t).1

/-- A row batch changes no FG field. -/
theorem pcsa_fold_admitRow_fg (p : Params) (st : State p.n) (as : List (RowWire p.n)) :
    (as.foldl (admitRow p) st).fg = st.fg := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih =>
    rw [List.foldl_cons, ih]
    delta admitRow
    cases hdecode : a.decode? <;> dsimp only
    split <;> rfl

/-- A raw ack batch changes no FG field. -/
theorem pcsa_fold_poolAckRaw_fg (st : State n) (as : List (AckWire n)) :
    (as.foldl poolAckRaw st).fg = st.fg := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, (poolAckRaw_frame st a).2.2.2]

/-- Block admission changes FG only through the existing window handler. -/
theorem pcsa_admitBlock_fg_cases (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) :
    (admitBlock p st s N).fg = st.fg ∨
      ∃ P, parentFG st N.erase = some P ∧
        (admitBlock p st s N).fg =
          FGSA.Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows) := by
  delta admitBlock
  split
  · exact Or.inl rfl
  · cases hP : parentFG st N.erase
    · exact Or.inl rfl
    · rename_i P
      dsimp only
      split
      · right
        refine ⟨P, rfl, ?_⟩
        rw [pcsa_fold_admitRow_fg, (collectPCs_frame _).2.2.2.2, pcsa_fold_poolAckRaw_fg]
        cases N.pc <;> dsimp only <;> split_ifs <;> simp only [pcsa_reconcile_fg] <;> rfl
      · exact Or.inl rfl

/-- A delivery moves finality only to a descendant, for every store. -/
theorem pcsa_process_F_mono (p : Params) (st : State p.n) (o : Wire p.n) :
    FGBlock.Preceq st.fg.F (process p st o).fg.F := by
  have pool_fg (a : AckWire p.n) : (poolAck p st a).fg = st.fg := by
    change (match a.decode? with
      | some (s, i, r) =>
          if st.slot p < s || !ackSlotOK st s r || a ∈ st.ackPool then st else
          if 2 ≤ (seatAcks st s i).length && !decide (r ∈ seatAcks st s i) then st else
          { st with ackPool := st.ackPool ++ [a] }
      | none => st).fg = st.fg
    cases hd : a.decode? with
    | none => rfl
    | some v =>
        rcases v with ⟨s, i, r⟩
        dsimp only
        split_ifs <;> rfl
  change FGBlock.Preceq st.fg.F (match o.decode with
    | some (.vote s i b) => admitHead p st s i b
    | some (.row _ body) => admitRow p st ⟨o.auth, body⟩
    | some (.block s N) => admitBlock p st s N
    | some (.ack _ _ b) => admitAck p st ⟨o.auth, b⟩
    | some (.pc c) => admitPC st c
    | none => st).fg.F
  cases hd : o.decode with
  | none =>
      dsimp only
      exact KitFG.preceq_refl _
  | some msg =>
      cases msg with
      | vote s i b =>
          dsimp only
          exact KitFG.preceq_refl _
      | row i body =>
          dsimp only
          have hr := pcsa_fold_admitRow_fg p st [⟨o.auth, body⟩]
          change (admitRow p st ⟨o.auth, body⟩).fg = st.fg at hr
          rw [hr]
          exact KitFG.preceq_refl _
      | block s N =>
          dsimp only
          rcases pcsa_admitBlock_fg_cases p st s N with he | ⟨P, _, he⟩
          · rw [he]
            exact KitFG.preceq_refl _
          · rw [he]
            exact FGSA.Window.window_on_block_F_mono p p.K_W st.fg _
      | ack s i b =>
          dsimp only
          change FGBlock.Preceq st.fg.F (collectPCs (poolAck p st ⟨o.auth, b⟩)).fg.F
          rw [(collectPCs_frame _).2.2.2.2, pool_fg]
          exact KitFG.preceq_refl _
      | pc cert =>
          dsimp only
          change FGBlock.Preceq st.fg.F
            (if cert.wellFormed then collectPCs (cert.acks.foldl poolAckRaw st) else st).fg.F
          cases hc : cert.wellFormed
          · exact KitFG.preceq_refl _
          · change FGBlock.Preceq st.fg.F (collectPCs (cert.acks.foldl poolAckRaw st)).fg.F
            rw [(collectPCs_frame _).2.2.2.2, pcsa_fold_poolAckRaw_fg]
            exact KitFG.preceq_refl _

/-- Admission records the original acceptance test with the FG update. -/
theorem pcsa_safety_admitBlock_fg_cases (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) :
    (admitBlock p st s N).fg = st.fg ∨
      ∃ P, parentFG st N.erase = some P ∧ blockAccepted p st s N P = true ∧
        (admitBlock p st s N).fg =
          FGSA.Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows) := by
  change let result := (if !namedParentHeld st N then st else
  match parentFG st N.erase with
  | none => st
  | some P =>
      if blockAccepted p st s N P then
        let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) }
        let st1 := match N.pc with
          | none => st1
          | some c =>
              if pcValid st1 c &&
                  !st1.pcs.any (fun o => o.slot == c.slot && o.target == c.target)
              then deleteConflictingLeases st1 c else st1
        let st1 := { st1 with
          fg := FGSA.Window.on_block p p.K_W st1.fg (fgBlock P N.erase N.rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
        let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
        let st3 := collectPCs (N.pcAcks.foldl poolAckRaw st2)
        N.rows.foldl (admitRow p) st3
      else st);
    result.fg = st.fg ∨ ∃ P, parentFG st N.erase = some P ∧
           blockAccepted p st s N P = true ∧ result.fg =
             FGSA.Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
  split
  · exact Or.inl rfl
  · cases hP : parentFG st N.erase
    · exact Or.inl rfl
    · rename_i P
      dsimp only
      split
      · rename_i hacc
        right
        refine ⟨P, rfl, hacc, ?_⟩
        rw [pcsa_fold_admitRow_fg, (collectPCs_frame _).2.2.2.2, pcsa_fold_poolAckRaw_fg]
        cases N.pc <;> dsimp only <;> split_ifs <;> simp only [pcsa_reconcile_fg] <;> rfl
      · exact Or.inl rfl

/-- Every changed FG store comes from an accepted proposal. -/
theorem pcsa_safety_process_fg_cases (p : Params) (st : State p.n) (o : Wire p.n) :
    (process p st o).fg = st.fg ∨
      ∃ s N P, o.decode = some (.block s N) ∧ parentFG st N.erase = some P ∧
        blockAccepted p st s N P = true ∧
        (process p st o).fg =
          FGSA.Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows) := by
  change let result := (match o.decode with
    | some (.vote s i b) => admitHead p st s i b
    | some (.row _ body) => admitRow p st ⟨o.auth, body⟩
    | some (.block s N) => admitBlock p st s N
    | some (.ack _ _ b) => admitAck p st ⟨o.auth, b⟩
    | some (.pc c) => admitPC st c
    | none => st);
    result.fg = st.fg ∨ ∃ s N P, o.decode = some (.block s N) ∧
           parentFG st N.erase = some P ∧ blockAccepted p st s N P = true ∧
           result.fg = FGSA.Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
  cases hd : o.decode with
  | none => exact Or.inl rfl
  | some msg =>
    cases msg with
    | vote s i b => exact Or.inl rfl
    | row i body => exact Or.inl (pcsa_fold_admitRow_fg p st [⟨o.auth, body⟩])
    | block s N =>
      rcases pcsa_safety_admitBlock_fg_cases p st s N with he | ⟨P, hp, ha, he⟩
      · exact Or.inl he
      · exact Or.inr ⟨s, N, P, rfl, hp, ha, he⟩
    | ack s i b =>
      left
      change (collectPCs (poolAck p st ⟨o.auth, b⟩)).fg = st.fg
      rw [(collectPCs_frame _).2.2.2.2]
      change (match AckWire.decode? (⟨o.auth, b⟩ : AckWire p.n) with
        | some (s, i, r) =>
            if st.slot p < s || !ackSlotOK st s r || (⟨o.auth, b⟩ : AckWire p.n) ∈ st.ackPool
            then st else
            if 2 ≤ (seatAcks st s i).length && !decide (r ∈ seatAcks st s i) then st else
            { st with ackPool := st.ackPool ++ [(⟨o.auth, b⟩ : AckWire p.n)] }
        | none => st).fg = st.fg
      cases ha : AckWire.decode? (⟨o.auth, b⟩ : AckWire p.n) with
      | none => rfl
      | some v =>
        rcases v with ⟨s, i, r⟩
        dsimp only
        split_ifs <;> rfl
    | pc cert =>
      left
      change (if cert.wellFormed then collectPCs (cert.acks.foldl poolAckRaw st) else st).fg = _
      split
      · rw [(collectPCs_frame _).2.2.2.2, pcsa_fold_poolAckRaw_fg]
      · rfl


/-- Normalization preserves both FG metadata lists. -/
theorem pcsa_safety_normalize_metadata (st : State n) :
    (normalizeS st).proposals = st.proposals ∧ (normalizeS st).rowPool = st.rowPool := by
  change let result := (if Block.preceq (eraseFG st.fg.F) st.base.stableRecord then st
    else { st with base := { st.base with stableRecord := eraseFG st.fg.F } });
    result.proposals = st.proposals ∧ result.rowPool = st.rowPool
  split <;> exact ⟨rfl, rfl⟩

/-- Reconciliation preserves both FG metadata lists. -/
theorem pcsa_safety_reconcile_metadata (st : State n) :
    (reconcile st).proposals = st.proposals ∧ (reconcile st).rowPool = st.rowPool := by
  exact pcsa_safety_normalize_metadata _

/-- PC installation and collection preserve both FG metadata lists. -/
theorem pcsa_safety_collect_metadata (st : State n) :
    (collectPCs st).proposals = st.proposals ∧ (collectPCs st).rowPool = st.rowPool := by
  constructor
  · apply collectPCs_preserves State.proposals _ st
    intro acc c
    rw [installPC_def]
    split <;> rfl
  · apply collectPCs_preserves State.rowPool _ st
    intro acc c
    rw [installPC_def]
    split <;> rfl

/-- Raw ack pooling preserves both FG metadata lists. -/
theorem pcsa_safety_poolAckRaw_metadata (st : State n) (a : AckWire n) :
    (poolAckRaw st a).proposals = st.proposals ∧ (poolAckRaw st a).rowPool = st.rowPool := by
  change let result := (match AckWire.decode? a with
    | some _ => if a ∈ st.ackPool then st else { st with ackPool := st.ackPool ++ [a] }
    | none => st);
    result.proposals = st.proposals ∧ result.rowPool = st.rowPool
  cases ha : AckWire.decode? a
  · exact ⟨rfl, rfl⟩
  · dsimp only
    split <;> exact ⟨rfl, rfl⟩

/-- A raw ack batch preserves both FG metadata lists. -/
theorem pcsa_safety_fold_poolAckRaw_metadata (st : State n) (as : List (AckWire n)) :
    (as.foldl poolAckRaw st).proposals = st.proposals ∧
      (as.foldl poolAckRaw st).rowPool = st.rowPool := by
  induction as generalizing st with
  | nil => exact ⟨rfl, rfl⟩
  | cons a as ih =>
    rw [List.foldl_cons]
    exact ⟨(ih _).1.trans (pcsa_safety_poolAckRaw_metadata st a).1,
      (ih _).2.trans (pcsa_safety_poolAckRaw_metadata st a).2⟩

/-- A row step keeps proposals and appends only to the row pool. -/
theorem pcsa_safety_admitRow_metadata (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).proposals = st.proposals ∧ st.rowPool <+: (admitRow p st a).rowPool := by
  change let result := (match a.decode? with
    | some _ => if a ∈ st.rowPool then st else { st with rowPool := st.rowPool ++ [a] }
    | none => st);
    result.proposals = st.proposals ∧ st.rowPool <+: result.rowPool
  cases ha : a.decode?
  · exact ⟨rfl, List.prefix_refl _⟩
  · dsimp only
    split
    · exact ⟨rfl, List.prefix_refl _⟩
    · exact ⟨rfl, List.prefix_append _ _⟩

/-- A row batch keeps proposals and appends only to the row pool. -/
theorem pcsa_safety_fold_admitRow_metadata (p : Params) (st : State p.n)
    (as : List (RowWire p.n)) :
    (as.foldl (admitRow p) st).proposals = st.proposals ∧
      st.rowPool <+: (as.foldl (admitRow p) st).rowPool := by
  induction as generalizing st with
  | nil => exact ⟨rfl, List.prefix_refl _⟩
  | cons a as ih =>
    rw [List.foldl_cons]
    exact ⟨(ih _).1.trans (pcsa_safety_admitRow_metadata p st a).1,
      (pcsa_safety_admitRow_metadata p st a).2.trans (ih _).2⟩

/-- Checked ack pooling preserves both FG metadata lists. -/
theorem pcsa_safety_poolAck_metadata (p : Params) (st : State p.n) (a : AckWire p.n) :
    (poolAck p st a).proposals = st.proposals ∧ (poolAck p st a).rowPool = st.rowPool := by
  change let result := (match AckWire.decode? a with
    | some (s, i, r) =>
        if st.slot p < s || !ackSlotOK st s r || a ∈ st.ackPool then st else
        if 2 ≤ (seatAcks st s i).length && !decide (r ∈ seatAcks st s i) then st else
        { st with ackPool := st.ackPool ++ [a] }
    | none => st);
    result.proposals = st.proposals ∧ result.rowPool = st.rowPool
  cases ha : AckWire.decode? a with
  | none => exact ⟨rfl, rfl⟩
  | some v =>
    rcases v with ⟨s, i, r⟩
    dsimp only
    split_ifs <;> exact ⟨rfl, rfl⟩

/-- Block processing appends to both FG metadata lists. -/
theorem pcsa_safety_admitBlock_metadata (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) :
    st.proposals <+: (admitBlock p st s N).proposals ∧
      st.rowPool <+: (admitBlock p st s N).rowPool := by
  change let result := (if !namedParentHeld st N then st else
  match parentFG st N.erase with
  | none => st
  | some P =>
      if blockAccepted p st s N P then
        let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) }
        let st1 := match N.pc with
          | none => st1
          | some c =>
              if pcValid st1 c &&
                  !st1.pcs.any (fun o => o.slot == c.slot && o.target == c.target)
              then deleteConflictingLeases st1 c else st1
        let st1 := { st1 with
          fg := FGSA.Window.on_block p p.K_W st1.fg (fgBlock P N.erase N.rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
        let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
        let st3 := collectPCs (N.pcAcks.foldl poolAckRaw st2)
        N.rows.foldl (admitRow p) st3
      else st);
    st.proposals <+: result.proposals ∧ st.rowPool <+: result.rowPool
  split
  · exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  · cases hp : parentFG st N.erase
    · exact ⟨List.prefix_refl _, List.prefix_refl _⟩
    · dsimp only
      split
      · have finish (acc : State p.n) (hp : st.proposals <+: acc.proposals)
            (hr : st.rowPool <+: acc.rowPool) :
            st.proposals <+: (N.rows.foldl (admitRow p)
              (collectPCs (N.pcAcks.foldl poolAckRaw acc))).proposals ∧
            st.rowPool <+: (N.rows.foldl (admitRow p)
              (collectPCs (N.pcAcks.foldl poolAckRaw acc))).rowPool := by
          have hrow := pcsa_safety_fold_admitRow_metadata p
            (collectPCs (N.pcAcks.foldl poolAckRaw acc)) N.rows
          have hcol := pcsa_safety_collect_metadata (N.pcAcks.foldl poolAckRaw acc)
          have hack := pcsa_safety_fold_poolAckRaw_metadata acc N.pcAcks
          constructor
          · rw [hrow.1, hcol.1, hack.1]
            exact hp
          · apply List.IsPrefix.trans _ hrow.2
            rw [hcol.2, hack.2]
            exact hr
        have rec_meta (q : Prop) [Decidable q] (acc : State p.n) :
            (if q then acc else reconcile acc).proposals = acc.proposals ∧
            (if q then acc else reconcile acc).rowPool = acc.rowPool := by
          split
          · exact ⟨rfl, rfl⟩
          · exact pcsa_safety_reconcile_metadata acc
        apply finish
        · rw [(rec_meta _ _).1]
          exact List.prefix_append _ _
        · rw [(rec_meta _ _).2]
          cases N.pc <;> dsimp only <;> (try split_ifs) <;> exact List.prefix_refl _
      · exact ⟨List.prefix_refl _, List.prefix_refl _⟩

/-- Delivery appends to both FG metadata lists. -/
theorem pcsa_safety_process_metadata (p : Params) (st : State p.n) (o : Wire p.n) :
    st.proposals <+: (process p st o).proposals ∧ st.rowPool <+: (process p st o).rowPool := by
  change let result := (match o.decode with
    | some (.vote s i b) => admitHead p st s i b
    | some (.row _ body) => admitRow p st ⟨o.auth, body⟩
    | some (.block s N) => admitBlock p st s N
    | some (.ack _ _ b) => admitAck p st ⟨o.auth, b⟩
    | some (.pc c) => admitPC st c
    | none => st);
    st.proposals <+: result.proposals ∧ st.rowPool <+: result.rowPool
  cases hd : o.decode with
  | none => exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | some msg =>
    cases msg with
    | vote s i b => exact ⟨List.prefix_refl _, List.prefix_refl _⟩
    | row i body =>
      have h := pcsa_safety_admitRow_metadata p st ⟨o.auth, body⟩
      exact ⟨h.1 ▸ List.prefix_refl _, h.2⟩
    | block s N => exact pcsa_safety_admitBlock_metadata p st s N
    | ack s i b =>
      change st.proposals <+: (collectPCs (poolAck p st ⟨o.auth, b⟩)).proposals ∧
        st.rowPool <+: (collectPCs (poolAck p st ⟨o.auth, b⟩)).rowPool
      rw [(pcsa_safety_collect_metadata _).1, (pcsa_safety_collect_metadata _).2,
        (pcsa_safety_poolAck_metadata p st _).1, (pcsa_safety_poolAck_metadata p st _).2]
      exact ⟨List.prefix_refl _, List.prefix_refl _⟩
    | pc cert =>
      change let result :=
        (if cert.wellFormed then collectPCs (cert.acks.foldl poolAckRaw st) else st);
        st.proposals <+: result.proposals ∧ st.rowPool <+: result.rowPool
      split
      · dsimp only
        rw [(pcsa_safety_collect_metadata _).1, (pcsa_safety_collect_metadata _).2,
          (pcsa_safety_fold_poolAckRaw_metadata st _).1,
          (pcsa_safety_fold_poolAckRaw_metadata st _).2]
        exact ⟨List.prefix_refl _, List.prefix_refl _⟩
      · exact ⟨List.prefix_refl _, List.prefix_refl _⟩

/-- A gate changes neither FG metadata list. -/
theorem pcsa_safety_gateFrom_metadata (p : Params) (a : Block) (cs : List (PC n))
    (ρ : Option PCRank) (st : State n) (s : Slot) :
    (gateFrom p a cs ρ st s).proposals = st.proposals ∧
      (gateFrom p a cs ρ st s).rowPool = st.rowPool := by
  rw [gateFrom_def]
  dsimp only
  cases hc : SA.Root.confirmationFrom p.toParams a (actView st) s
  · exact ⟨rfl, rfl⟩
  · dsimp only
    split
    · exact ⟨rfl, rfl⟩
    · apply List.foldlRecOn (motive := fun acc : State n =>
        acc.proposals = st.proposals ∧ acc.rowPool = st.rowPool)
      · exact ⟨rfl, rfl⟩
      · intro acc ha b _
        apply List.foldlRecOn (motive := fun acc : State n =>
          acc.proposals = st.proposals ∧ acc.rowPool = st.rowPool)
        · exact ha
        · intro acc' ha' g _
          exact ha'

/-- The pre-gate clock changes neither FG metadata list. -/
theorem pcsa_safety_clockPre_metadata (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).proposals = st.proposals ∧ (clockPre p st t).rowPool = st.rowPool := by
  change let result := (let q := p.toParams
  let st := { st with base := GridCO.expire { st.base with now := t } t }
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 3 * p.Δ && t == SA.freezeTime q fSlot then
    { onView (fun v => GridCO.freeze q.engine v fSlot) st with
      pcSnapshot := if (st.pcSnapshot.find? (fun row => row.1 == fSlot)).isSome then
        st.pcSnapshot else st.pcSnapshot ++ [(fSlot, st.pcs)] } else st
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 2 * p.Δ && t == SA.earlyTime q eSlot then
    onView (fun v =>
      { v with early := v.early ++ [(eSlot, GridCO.earlyVotes q.engine v eSlot)] }) st
    else st
  let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  if 0 ≤ t - 5 * p.Δ && t == SA.releaseTime q qSlot then
    onView (fun v => SA.Root.release q v qSlot) st else st);
    result.proposals = st.proposals ∧ result.rowPool = st.rowPool
  dsimp only
  split <;> split <;> split <;> exact ⟨rfl, rfl⟩

/-- The complete clock changes neither FG metadata list. -/
theorem pcsa_safety_clock_metadata (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).proposals = st.proposals ∧ (clock p st t).rowPool = st.rowPool := by
  change let result := (let st := clockPre p st t
  let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  if 0 ≤ t - 6 * p.Δ && t == SA.gateTime p.toParams dSlot then gateStep p st dSlot else st);
    result.proposals = st.proposals ∧ result.rowPool = st.rowPool
  dsimp only
  split
  · rw [gateStep_def]
    constructor
    · rw [(pcsa_safety_normalize_metadata _).1]
      split
      · exact (pcsa_safety_clockPre_metadata p st t).1
      · rw [(pcsa_safety_gateFrom_metadata _ _ _ _ _ _).1]
        exact (pcsa_safety_clockPre_metadata p st t).1
    · rw [(pcsa_safety_normalize_metadata _).2]
      split
      · exact (pcsa_safety_clockPre_metadata p st t).2
      · rw [(pcsa_safety_gateFrom_metadata _ _ _ _ _ _).2]
        exact (pcsa_safety_clockPre_metadata p st t).2
  · exact pcsa_safety_clockPre_metadata p st t

/-- A decoded block retains its exact raw proposal payload. -/
theorem pcsa_safety_decode_block_payload {n : Nat} (o : Wire n) (s : Slot)
    (N : NamedProposal n) (hd : o.decode = some (.block s N)) : o.payload = .proposal N := by
  rcases o with ⟨auth, msg⟩
  cases auth with
  | none => cases msg <;> cases hd
  | proposer r => cases msg <;> cases hd; rfl
  | seat l i => cases l <;> cases msg <;> cases hd

/-- Every delivery keeps the old FG tree. -/
theorem pcsa_safety_process_TF (p : Params) (st : State p.n) (o : Wire p.n) :
    st.fg.TF ⊆ (process p st o).fg.TF := by
  rcases pcsa_safety_process_fg_cases p st o with he | ⟨s, N, P, _, _, _, he⟩
  · rw [he]
  · rw [he]
    exact FGSA.Window.window_on_block_TF_subset p p.K_W st.fg _

end AvailableChain.PCSA
end
