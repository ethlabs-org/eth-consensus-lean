module
public import AvailableChainPCSAProofs.Proofs.Recovery.Exclusions

-- Keep the proposal handler matcher private in this proof module.
namespace AvailableChain.PCSA
private def sourceAdmitBlock (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) : State p.n :=
  if !namedParentHeld st N then st else
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
      else st

private theorem sourceAdmitBlock_eq : @admitBlock = @sourceAdmitBlock := rfl
end AvailableChain.PCSA

public section

/-! Source acceptance and immutable R6 witnesses for recovery paths. -/
namespace AvailableChain.PCSA
variable {n : Nat}

private theorem source_normalize_names (st : State n) :
    (normalizeS st).namedBodies = st.namedBodies := by
  delta normalizeS
  split <;> rfl

private theorem source_reconcile_names (st : State n) :
    (reconcile st).namedBodies = st.namedBodies := by
  delta reconcile
  rw [source_normalize_names]
  rfl

private theorem source_collect_names (st : State n) :
    (collectPCs st).namedBodies = st.namedBodies := by
  apply collectPCs_preserves State.namedBodies
  intro st pc
  rw [installPC_def]
  split <;> rfl

private theorem source_raw_names (st : State n) (a : AckWire n) :
    (poolAckRaw st a).namedBodies = st.namedBodies := by
  delta poolAckRaw
  cases a.decode? with
  | none => rfl
  | some v => dsimp only; split <;> rfl

private theorem source_acks_names (st : State n) (as : List (AckWire n)) :
    (as.foldl poolAckRaw st).namedBodies = st.namedBodies := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, source_raw_names]

private theorem source_row_names (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).namedBodies = st.namedBodies := by
  delta admitRow
  cases a.decode? with
  | none => rfl
  | some v => dsimp only; split <;> rfl

private theorem source_rows_names (p : Params) (st : State p.n) (as : List (RowWire p.n)) :
    (as.foldl (admitRow p) st).namedBodies = st.namedBodies := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, source_row_names]

private theorem source_append_names (st : State n) (s : Slot) (N : NamedProposal n)
    (base : GridCO.State n .root) (fg : SimplexFG.Store (Fin n)) :
    ({ st with
      base := base
      fg := fg
      proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] } : State n).namedBodies =
      st.namedBodies ++ [N] := by
  change (NamedProposal.genesis : NamedProposal n) ::
    (st.proposals ++ [(⟨.proposer s, .proposal N⟩ : Wire n)]).filterMap Wire.proposal? = _
  rw [List.filterMap_append]
  rfl

private theorem source_block_names (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) :
    admitBlock p st s N = st ∨
      (admitBlock p st s N).namedBodies = st.namedBodies ++ [N] := by
  rw [sourceAdmitBlock_eq]
  delta sourceAdmitBlock
  split
  · exact Or.inl rfl
  · cases hp : parentFG st N.erase with
    | none => exact Or.inl rfl
    | some P =>
      dsimp only
      split
      · right
        rw [source_rows_names, source_collect_names, source_acks_names]
        cases N.pc <;> dsimp only <;> split_ifs <;> first
          | exact source_append_names st s N _ _
          | (rw [source_reconcile_names]; exact source_append_names st s N _ _)
      · exact Or.inl rfl

private theorem source_process_names (p : Params) (st : State p.n) (o : Wire p.n)
    (N : NamedProposal p.n) (hn : N ∈ (process p st o).namedBodies)
    (hold : N ∉ st.namedBodies) :
    ∃ s, o.decode = some (.block s N) ∧ ∃ P, parentFG st N.erase = some P ∧
      blockAccepted p st s N P = true := by
  delta process at hn
  cases hd : o.decode with
  | none => rw [hd] at hn; exact (hold hn).elim
  | some msg =>
    rw [hd] at hn
    cases msg with
    | vote s i r => exact (hold hn).elim
    | row i body => exact (hold (by simpa only [source_row_names] using hn)).elim
    | ack s i r =>
      dsimp only at hn
      delta admitAck at hn
      rw [source_collect_names] at hn
      delta poolAck at hn
      cases hd : AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) with
      | none => rw [hd] at hn; exact (hold hn).elim
      | some v =>
        rw [hd] at hn
        rcases v with ⟨_, _, _⟩
        dsimp only at hn
        split at hn
        · exact (hold hn).elim
        · split at hn <;> exact (hold hn).elim
    | pc pc =>
      dsimp only at hn
      delta admitPC at hn
      split at hn
      · rw [source_collect_names, source_acks_names] at hn
        exact (hold hn).elim
      · exact (hold hn).elim
    | block s M =>
      dsimp only at hn
      have he : N = M := by
        rcases source_block_names p st s M with he | he
        · exact (hold (he ▸ hn)).elim
        · rw [he] at hn
          exact List.mem_singleton.mp ((List.mem_append.mp hn).resolve_left hold)
      subst M
      refine ⟨s, rfl, ?_⟩
      rw [sourceAdmitBlock_eq] at hn
      delta sourceAdmitBlock at hn
      split at hn
      · exact (hold hn).elim
      · cases hp : parentFG st N.erase with
        | none => rw [hp] at hn; exact (hold hn).elim
        | some P =>
          rw [hp] at hn
          dsimp only at hn
          split at hn
          · exact ⟨P, rfl, ‹blockAccepted p st s N P = true›⟩
          · exact (hold hn).elim

private theorem source_admit_fg (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n))
    (hp : parentFG st N.erase = some P) (ha : blockAccepted p st s N P = true)
    (hn : namedParentHeld st N = true) :
    (admitBlock p st s N).fg = FGSA.Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows) := by
  have hr (st : State p.n) : (reconcile st).fg = st.fg := by
    delta reconcile normalizeS
    dsimp only
    split <;> rfl
  have hrows (st : State p.n) (as : List (RowWire p.n)) :
      (as.foldl (admitRow p) st).fg = st.fg := by
    induction as generalizing st with
    | nil => rfl
    | cons a as ih =>
      rw [List.foldl_cons, ih]
      delta admitRow
      cases a.decode? with
      | none => rfl
      | some v => dsimp only; split <;> rfl
  have hacks (st : State p.n) (as : List (AckWire p.n)) :
      (as.foldl poolAckRaw st).fg = st.fg := by
    induction as generalizing st with
    | nil => rfl
    | cons a as ih => rw [List.foldl_cons, ih, (poolAckRaw_frame st a).2.2.2]
  rw [sourceAdmitBlock_eq]
  delta sourceAdmitBlock
  rw [hn, Bool.not_true, ite_eq_right Bool.false_ne_true, hp]
  dsimp only
  rw [ite_eq_left ha]
  rw [hrows, collectPCs_preserves State.fg (by
    intro st pc
    rw [installPC_def]
    split <;> rfl), hacks]
  cases N.pc <;> dsimp only <;> split_ifs <;> first | rfl | exact hr _

/-- A new named body supplies a first acceptance and an immutable R6 witness. -/
theorem recovery_new_named_source (p : Params) (st : State p.n) (o : Wire p.n)
    (N : NamedProposal p.n) (hn : N ∈ (process p st o).namedBodies)
    (hold : N ∉ st.namedBodies) :
    ∃ s, o.decode = some (.block s N) ∧
      Run.processedS p st (Run.ofWire p ⟨.proposer s, .proposal N⟩) = false ∧
      Run.processedS p (process p st o) (Run.ofWire p ⟨.proposer s, .proposal N⟩) = true ∧
      ∃ P : SimplexFG.FGBlock (Fin p.n),
        eraseFG P = N.erase.parent ∧ rowsValidForParent p P N.slot N.rows = true := by
  obtain ⟨s, hd, P, hp, ha⟩ := source_process_names p st o N hn hold
  have hparent := FGSA.pickPair_some_spec _ _ hp
  have hb := ha
  change (N.erase != .genesis && decide (N.erase.slot ≤ st.slot p) &&
    !decide (∃ Y ∈ st.fg.TF, Y.root = N.erase.root) &&
    SimplexFG.FGBlock.preceq st.fg.F (fgBlock P N.erase N.rows) &&
    decide (N.erase.parent.slot < N.erase.slot) && s == N.erase.slot &&
    rowsValidForParent p P N.erase.slot N.rows && (N.pc.map PC.wellFormed).getD true &&
    namedContentOk p N) = true at hb
  simp only [Bool.and_eq_true_iff, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at hb
  have hnone : ¬ ∃ Y ∈ st.fg.TF, Y.root = N.erase.root := hb.1.1.1.1.1.1.2
  have hpre : SimplexFG.FGBlock.preceq st.fg.F (fgBlock P N.erase N.rows) = true :=
    hb.1.1.1.1.1.2
  have hslot : N.erase.parent.slot < N.erase.slot := hb.1.1.1.1.2
  have hrows : rowsValidForParent p P N.erase.slot N.rows = true := hb.1.1.2
  have hnamed : namedParentHeld st N = true := by
    by_contra hh
    have he : process p st o = st := by
      delta process
      rw [hd]
      dsimp only
      rw [sourceAdmitBlock_eq]
      delta sourceAdmitBlock
      rw [Bool.eq_false_iff.mpr hh]
      rfl
    exact hold (he ▸ hn)
  have hfg : (process p st o).fg =
      FGSA.Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows) := by
    delta process
    rw [hd]
    exact source_admit_fg p st s N P hp ha hnamed
  have hmem : fgBlock P N.erase N.rows ∈ (process p st o).fg.TF := by
    rw [hfg, FGSA.Window.window_on_block_of_accepted, FGSA.Window.window_update_finality_TF]
    · exact Finset.mem_insert_self _ _
    · push Not
      refine ⟨?_, hparent.1, ?_, ?_⟩
      · intro hm
        exact hnone ⟨_, hm, rfl⟩
      · rw [hpre]; decide
      · change P.slot < N.erase.slot
        have he := of_decide_eq_true hparent.2
        have hs : P.slot = N.erase.parent.slot := by
          rw [← he]
          cases P <;> rfl
        rw [hs]
        exact hslot
  refine ⟨s, hd, ?_, ?_, P, of_decide_eq_true hparent.2, ?_⟩
  · change decide (∃ Y ∈ st.fg.TF, Y.root = N.root) = false
    exact decide_eq_false (by simpa only [Run.pcsa_named_erase_root] using hnone)
  · change decide (∃ Y ∈ (process p st o).fg.TF, Y.root = N.root) = true
    exact decide_eq_true ⟨_, hmem, Run.pcsa_named_erase_root N⟩
  · have he : N.erase.slot = N.slot := by cases N <;> rfl
    simpa only [he] using hrows

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

private theorem source_decoded_wire (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (hd : (toWire p o).decode = some (.block s N)) :
    o = ofWire p ⟨.proposer s, .proposal N⟩ := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> simp [toWire, toAuth, Wire.decode] at hd
  | seat l j =>
    cases l with
    | prop k =>
      cases payload <;> simp [toWire, toAuth, Wire.decode] at hd
      obtain ⟨rfl, rfl⟩ := hd
      change Fin 1 at j
      have hj : j = ⟨0, Nat.one_pos⟩ := Subsingleton.elim _ _
      subst j
      rfl
    | base l => cases l <;> cases payload <;>
        dsimp only [toWire, toAuth, Wire.decode, Label.ackSlot?] at hd <;> simp at hd

/-- Every stored non-genesis body has a prior acceptance with its R6 witness. -/
theorem recovery_named_source_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (x : V)
    (N : NamedProposal p.n) (hn : N ∈ (V2.D.Run.stateBefore E rho k x).st.namedBodies)
    (hne : N ≠ .genesis) :
    ∃ i < k, ∃ u r, V2.D.Run.acceptsAt E rho i x
      (ofWire p ⟨.proposer r, .proposal N⟩) u ∧
      ∃ P : SimplexFG.FGBlock (Fin p.n),
        eraseFG P = N.erase.parent ∧ rowsValidForParent p P N.slot N.rows = true := by
  let Q := fun nd : Node p => N ∈ nd.st.namedBodies →
    ∃ i < k, ∃ u r, V2.D.Run.acceptsAt E rho i x
      (ofWire p ⟨.proposer r, .proposal N⟩) u ∧
      ∃ P : SimplexFG.FGBlock (Fin p.n),
        eraseFG P = N.erase.parent ∧ rowsValidForParent p P N.slot N.rows = true
  have hi : Q (pcsaWith m p c).init := by
    intro hm
    exact (hne (List.mem_singleton.mp hm)).elim
  have hq : Q (V2.D.Run.stateBefore E rho k x) := by
    refine V2.D.Engine.stateBefore_step_induction E rho Q (Nat.zero_le k) x ?_ hi
    intro i e _ hik he hx ih
    cases e with
    | restart y t =>
      change y = x at hx
      subst y
      change Q (Function.update (V2.D.Run.stateBefore E rho i) x _ x)
      rw [Function.update_self]
      exact hi
    | tick y t =>
      change y = x at hx
      subst y
      change Q (Function.update (V2.D.Run.stateBefore E rho i) x _ x)
      rw [Function.update_self]
      intro hm
      rw [pcsa_tick_st E rho (V2.D.Run.stateBefore E rho i x) x t,
        recovery_clock_names] at hm
      exact ih hm
    | deliver y o t =>
      change y = x at hx
      subst y
      change Q (Function.update (V2.D.Run.stateBefore E rho i) x _ x)
      rw [Function.update_self]
      intro hm
      by_cases hold : N ∈ (V2.D.Run.stateBefore E rho i x).st.namedBodies
      · exact ih hold
      · obtain ⟨r, hd, hbefore, hafter, P, hp, hv⟩ :=
          recovery_new_named_source p _ (toWire p o) N hm hold
        have ho := source_decoded_wire o r N hd
        refine ⟨i, hik, t, r, ⟨⟨o, he, ?_⟩, hbefore, ?_⟩, P, hp, hv⟩
        · exact Or.inl ho
        · rw [V2.D.Run.stateBefore_succ E rho he]
          change (pcsaWith m p c).processed
            (Function.update (V2.D.Run.stateBefore E rho i) x _ x) _ = true
          rw [Function.update_self]
          exact hafter
  exact hq hn

/-- The post-clock source witness is no later than the read. -/
theorem recovery_postClock_source (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (x : V) (t : Time) (nd : Node p) (hnd : pcsa_postClock E rho x t = some nd)
    (N : NamedProposal p.n) (hn : N ∈ nd.st.namedBodies) (hne : N ≠ .genesis) :
    ∃ i u r, u ≤ t ∧ V2.D.Run.acceptsAt E rho i x
      (ofWire p ⟨.proposer r, .proposal N⟩) u ∧
      ∃ P : SimplexFG.FGBlock (Fin p.n),
        eraseFG P = N.erase.parent ∧ rowsValidForParent p P N.slot N.rows = true := by
  rw [pcsa_postClock_def, pcsa_preTick_def] at hnd
  obtain ⟨nd0, hnd0, rfl⟩ := Option.map_eq_some_iff.mp hnd
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hnd0
  have hkt := V2.D.Run.tickIdx?_spec hk
  change N ∈ (clock p (V2.D.Run.stateBefore E rho k x).st t).namedBodies at hn
  rw [recovery_clock_names] at hn
  obtain ⟨i, hik, u, r, ha, hp⟩ := recovery_named_source_origin E rho k x N hn hne
  obtain ⟨o, he, _⟩ := ha.1
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp he
  obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hkt
  have hord := (List.pairwise_iff_getElem.mp hs.sorted) i k hil hkl hik
  rw [hie, hke] at hord
  exact ⟨i, u, r, V2.D.Engine.time_le_of_key_le _ _ hord, ha, hp⟩

variable [Fintype V]

/-- Every stored path body has the source witnesses needed by F5 relay. -/
theorem recovery_path_source_receipt (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hframe : StageOneFrame p c E rho)
    (s : Slot) (hs : 0 < s) (ha : E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s)
    (hh : SA.gateTime p.toParams s ≤ rho.horizon)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (nd : Node p) (hnd : pcsa_postClock E rho x (SA.proposalTime p.toParams s) = some nd)
    (N : NamedProposal p.n) (hn : N ∈ nd.st.namedBodies) (hne : N ≠ .genesis) :
    ∃ i u r, u ≤ SA.proposalTime p.toParams s ∧
      V2.D.Run.acceptsAt E rho i x (ofWire p ⟨.proposer r, .proposal N⟩) u ∧
      (∃ P : SimplexFG.FGBlock (Fin p.n),
        eraseFG P = N.erase.parent ∧ rowsValidForParent p P N.slot N.rows = true) ∧
      ((pcsaWith m p c).processed (V2.D.Run.stateBefore E rho (i + 1) y)
          (ofWire p ⟨.proposer r, .proposal N⟩) = true ∨
        ∃ u', u ≤ u' ∧ u' < SA.voteTime p.toParams s ∧
          ∃ j, V2.D.Run.handlesAt E rho j y (ofWire p ⟨.proposer r, .proposal N⟩) u') := by
  obtain ⟨i, u, r, hu, hc, P, hp, hv⟩ := recovery_postClock_source E rho
    h.base.valid.toScheduleWellFormed x _ nd hnd N hn hne
  exact ⟨i, u, r, hu, hc, ⟨P, hp, hv⟩,
    recovery_accepted_path_receipt E rho h hframe s hs ha hh x y hx hy
      i u r N P hp hv hu hc⟩

end AvailableChain.PCSA.Run
end
