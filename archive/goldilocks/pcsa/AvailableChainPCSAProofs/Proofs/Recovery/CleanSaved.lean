module
public import AvailableChainPCSAProofs.Proofs.Recovery.RunInputs

-- Keep the proposal handler matcher private in this proof module.
namespace AvailableChain.PCSA
private def archiveAdmitBlock (p : Params) (st : State p.n) (s : Slot)
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

private theorem archiveAdmitBlock_eq : @admitBlock = @archiveAdmitBlock := rfl
end AvailableChain.PCSA

public section

/-! Saved-result transport for the clean anchor boundary. -/
namespace AvailableChain.PCSA

variable {Q : Slot → Block → Prop}

private def archive_ResultsBound {n : Nat} (Q : Slot → Block → Prop) (st : State n) : Prop :=
  ∀ row ∈ st.base.genuine, ∀ C, row.2 = some C →
    Q row.1 C

private theorem archive_grid_vote_genuine (p : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (o : GridCO.Wire n .root) :
    (GridCO.admitVote p st o).genuine = st.genuine := by
  rcases o with ⟨auth, payload⟩
  cases auth <;> cases payload <;> delta GridCO.admitVote <;> dsimp only
  all_goals first | rfl | (split <;> rfl)

private theorem archive_grid_proposal_genuine (p : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (o : GridCO.Wire n .root) (B : Block)
    (raw : List (GridCO.HeadWire n .root)) :
    (GridCO.admitProposal p st o B raw).genuine = st.genuine := by
  delta GridCO.admitProposal
  dsimp only
  cases o.auth <;> dsimp only <;> split
  all_goals first | rfl | skip
  all_goals
    apply List.foldlRecOn (motive := fun v : GridCO.State n .root => v.genuine = st.genuine)
    · rfl
    · intro acc hh a _
      rw [archive_grid_vote_genuine]
      exact hh

private theorem archive_collect_genuine {n : Nat} (st : State n) :
    (collectPCs st).base.genuine = st.base.genuine := by
  apply collectPCs_preserves (fun st : State n => st.base.genuine)
  intro st pc
  rw [installPC_def]
  split <;> rfl

private theorem archive_normalize_results {n : Nat} (st : State n) (h : archive_ResultsBound Q st) :
    archive_ResultsBound Q (normalizeS st) := by
  delta normalizeS
  split <;> exact h

private theorem archive_reconcile_results {n : Nat} (st : State n) (h : archive_ResultsBound Q st) :
    archive_ResultsBound Q (reconcile st) := by
  apply archive_normalize_results
  intro row hr C hc
  obtain ⟨old, hold, he⟩ := List.mem_map.mp hr
  cases he
  exact h old hold C (Option.filter_eq_some_iff.mp hc).1

private theorem archive_row_results (p : Params) (st : State p.n) (a : RowWire p.n)
    (h : archive_ResultsBound Q st) : archive_ResultsBound Q (admitRow p st a) := by
  delta admitRow
  cases a.decode? with
  | none => exact h
  | some v => dsimp only; split <;> exact h

private theorem archive_raw_results {n : Nat} (st : State n) (a : AckWire n)
    (h : archive_ResultsBound Q st) : archive_ResultsBound Q (poolAckRaw st a) := by
  delta poolAckRaw
  cases a.decode? with
  | none => exact h
  | some v => dsimp only; split <;> exact h

private theorem archive_process_results (p : Params) (st : State p.n) (o : Wire p.n)
    (h : archive_ResultsBound Q st) : archive_ResultsBound Q (process p st o) := by
  have hc (st : State p.n) (h : archive_ResultsBound Q st) :
      archive_ResultsBound Q (collectPCs st) := by
    delta archive_ResultsBound at h ⊢
    simpa only [archive_collect_genuine] using h
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : archive_ResultsBound Q st) :
      archive_ResultsBound Q (as.foldl poolAckRaw st) :=
    List.foldlRecOn as poolAckRaw h (fun acc hh a _ => archive_raw_results acc a hh)
  delta process
  cases hd : o.decode with
  | none => exact h
  | some msg => cases msg with
    | vote s i r =>
      delta archive_ResultsBound at h ⊢
      delta admitHead
      simpa only [archive_grid_vote_genuine] using h
    | row i body => exact archive_row_results p st _ h
    | block s N =>
      dsimp only
      rw [archiveAdmitBlock_eq]
      delta archiveAdmitBlock
      split
      · exact h
      · cases hp : parentFG st N.erase with
        | none => exact h
        | some P =>
          dsimp only
          split
          · apply List.foldlRecOn
            · apply hc
              apply ha
              have hb : archive_ResultsBound Q { st with base := (GridCO.admitProposal
                  p.toParams.engine st.base (baseProposal s N.erase N.raw N.support)
                    N.erase (N.raw.map baseHead)) } := by
                delta archive_ResultsBound at h ⊢
                simpa only [archive_grid_proposal_genuine] using h
              cases N.pc <;> dsimp only <;> split_ifs <;> first
                | (apply archive_reconcile_results; exact hb)
                | exact hb
            · intro acc hh a _
              exact archive_row_results p acc a hh
          · exact h
    | ack s i r =>
      dsimp only
      delta admitAck
      apply hc
      delta poolAck
      cases hd : AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) with
      | none => exact h
      | some v =>
        rcases v with ⟨_, _, _⟩
        dsimp only
        split
        · exact h
        · split <;> exact h
    | pc pc =>
      dsimp only
      delta admitPC
      split
      · exact hc _ (ha _ _ h)
      · exact h

private theorem archive_record_results (p : Params) (st : State p.n) (s : Slot)
    (oc : Option Block) (h : archive_ResultsBound Q st)
    (hn : ∀ C, oc = some C → Q s C) :
    ∀ row ∈ @GridCO.recordGenuine GridCO.slowLeasePolicy p.n .root (actView st) s oc,
      ∀ C, row.2 = some C → Q row.1 C := by
  delta GridCO.recordGenuine
  split
  · intro row hr C hc
    rcases List.mem_append.mp hr with hr | hr
    · exact h row hr C hc
    · cases List.mem_singleton.mp hr
      exact hn C hc
  · exact h

private theorem archive_gate_results (p : Params) (st : State p.n)
    (a : Block) (cs : List (PC p.n)) (rank : Option PCRank) (s : Slot)
    (hn : ∀ C, SA.Root.confirmationFrom p.toParams a (actView st) s = some C → Q s C)
    (h : archive_ResultsBound Q st) :
    archive_ResultsBound Q (gateFrom p a cs rank st s) := by
  rw [gateFrom_def]
  dsimp only
  cases hc : SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => exact archive_record_results p st s none h (by intro C he; cases he)
  | some C =>
    have hi := archive_record_results p st s (some C) h (by
      intro D hd
      cases Option.some.inj hd
      exact hn C hc)
    dsimp only
    split
    · exact hi
    · apply List.foldlRecOn
      · exact hi
      · intro acc hh b _
        apply List.foldlRecOn
        · exact hh
        · intro acc' hh' g _
          exact hh'

private theorem archive_clock (p : Params) (st : State p.n) (t : Time)
    (h : archive_ResultsBound Q st)
    (hn : ∀ s C, t = SA.gateTime p.toParams s →
      SA.Root.confirmationFrom p.toParams (eraseFG (clockPre p st t).fg.F)
        (actView (clockPre p st t)) s = some C → Q s C) :
    archive_ResultsBound Q (clock p st t) := by
  have hc : archive_ResultsBound Q (clockPre p st t) := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> exact h
  delta clock
  dsimp only
  split
  · rename_i ht
    have he := eq_of_beq (Bool.and_eq_true_iff.mp ht).2
    rw [gateStep_def]
    dsimp only
    apply archive_normalize_results
    split
    · exact hc
    · exact archive_gate_results p _ _ _ _ _ (fun C hC => hn _ C he hC) hc
  · exact hc

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

private theorem archive_tick_index (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (x : V) (t : Time) (i : Nat) (he : rho.events[i]? = some (.tick x t)) :
    V2.D.Run.tickIdx? rho x t = some i := by
  delta V2.D.Run.tickIdx?
  rw [List.findIdx?_eq_some_iff_getElem]
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp he
  refine ⟨hi, ?_, ?_⟩
  · rw [he]
    simp
  · intro j hj
    by_contra hh
    have hjl := Nat.lt_trans hj hi
    have hje : rho.events[j] = .tick x t := by
      cases he' : rho.events[j] <;> simp_all
    have hij : j = i := (List.Nodup.getElem_inj_iff hs.nodup).mp (hje.trans he.symm)
    omega

/-- Every retained saved result equals the raw result at its unique gate tick. -/
theorem recovery_saved_gate_result (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (x : V) (i : Nat) (r : Slot) (C : Block)
    (hc : GridCO.savedGenuine (V2.D.Run.stateBefore E rho i x).st.base r = some (some C)) :
    gateResultAt p c E rho x r = some (some C) := by
  let Q := fun r C => gateResultAt p c E rho x r = some (some C)
  have hi : archive_ResultsBound Q (initial p.n) := by
    intro row hr
    exact (List.not_mem_nil hr).elim
  have hh : archive_ResultsBound Q (V2.D.Run.stateBefore E rho i x).st := by
    refine V2.D.Engine.stateBefore_step_induction E rho
      (fun nd : Node p => archive_ResultsBound Q nd.st) (Nat.zero_le i) x ?_ hi
    intro k e _ _ he hx ih
    cases e with
    | restart y t =>
      change y = x at hx
      subst y
      change archive_ResultsBound Q (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st
      rw [Function.update_self]
      exact hi
    | deliver y o t =>
      change y = x at hx
      subst y
      change archive_ResultsBound Q (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st
      rw [Function.update_self]
      exact archive_process_results p _ _ ih
    | tick y t =>
      change y = x at hx
      subst y
      change archive_ResultsBound Q (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st
      rw [Function.update_self, pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t]
      apply archive_clock p _ t ih
      intro s C ht hC
      subst t
      have hk := archive_tick_index E rho hs x _ k he
      change gateResultAt p c E rho x s = some (some C)
      rw [pcsa_gateResultAt_def, pcsa_gateInAt_def, pcsa_preTick_def, hk]
      exact congrArg some hC
  change ((V2.D.Run.stateBefore E rho i x).st.base.genuine.find?
    (fun row => row.1 == r)).map Prod.snd = some (some C) at hc
  obtain ⟨row, hr, hv⟩ := Option.map_eq_some_iff.mp hc
  have hslot : row.1 = r := by simpa using List.find?_some hr
  simpa only [hslot] using hh row (List.mem_of_find?_eq_some hr) C hv

/-- The clean gate-result prefix contract supplies the complete saved archive contract. -/
theorem recovery_cleanSaved_of_gate_prefix (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (cA : Slot) (P : Block)
    (cleanResults : ∀ x ∈ rho.honest, ∀ r C, r < cA →
      gateResultAt p c E rho x r = some (some C) → Block.Preceq C P) :
    ∀ x ∈ rho.honest, ∀ (i : Nat) (r : Slot) (C : Block), r < cA →
      GridCO.savedGenuine (V2.D.Run.stateBefore E rho i x).st.base r = some (some C) →
      Block.Preceq C P := by
  intro x hx i r C hr hc
  exact cleanResults x hx r C hr (recovery_saved_gate_result E rho hs x i r C hc)

/-- Compatibility with a later-slot anchor puts an archive result below it. -/
theorem recovery_saved_below_of_compatible (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (i : Nat) (r cA : Slot) (C P : Block)
    (hr : r < cA) (hP : P.slot = cA)
    (hc : GridCO.savedGenuine (V2.D.Run.stateBefore E rho i x).st.base r = some (some C))
    (hcompat : Block.Compatible C P) : Block.Preceq C P := by
  rcases Bool.or_eq_true_iff.mp hcompat with h | h
  · exact h
  · change ((V2.D.Run.stateBefore E rho i x).st.base.genuine.find?
      (fun row => row.1 == r)).map Prod.snd = some (some C) at hc
    obtain ⟨row, hrow, hv⟩ := Option.map_eq_some_iff.mp hc
    have hslot : row.1 = r := by simpa using List.find?_some hrow
    have hb := recovery_saved_result_slot p _ (pcsa_reachable_stateBefore E rho i x)
      row (List.mem_of_find?_eq_some hrow) C hv P h
    rw [hP, hslot] at hb
    exact (Nat.not_le_of_lt hr hb).elim

/-- The prefix needs only gate-result compatibility, since earlier result slots are bounded. -/
theorem recovery_cleanSaved_of_gate_compatibility (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (cA : Slot) (P : Block) (hP : P.slot = cA)
    (prefixResultsCompatible : ∀ x ∈ rho.honest, ∀ r C, r < cA →
      gateResultAt p c E rho x r = some (some C) → Block.Compatible C P) :
    ∀ x ∈ rho.honest, ∀ (i : Nat) (r : Slot) (C : Block), r < cA →
      GridCO.savedGenuine (V2.D.Run.stateBefore E rho i x).st.base r = some (some C) →
      Block.Preceq C P := by
  intro x hx i r C hr hc
  exact recovery_saved_below_of_compatible E rho x i r cA C P hr hP hc
    (prefixResultsCompatible x hx r C hr (recovery_saved_gate_result E rho hs x i r C hc))

/-- The gate-prefix input bounds locks at both first-slot readers. -/
theorem recovery_anchor_locks_of_gate_prefix (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (cA s : Slot) (P : Block) (hwindow : s - 1 - cA ≤ p.k - 1) (horder : cA < s)
    (cleanResults : ∀ x ∈ rho.honest, ∀ r C, r < cA →
      gateResultAt p c E rho x r = some (some C) → Block.Preceq C P) :
    ∀ x ∈ rho.honest, ∀ t,
      t = SA.proposalTime p.toParams s ∨ t = SA.voteTime p.toParams s →
      ∀ nd, pcsa_postClock E rho x t = some nd →
        ∀ B, LiveLease nd.st B → Block.Preceq B P :=
  recovery_anchor_locks_of_clean_saved E rho hs cA s P hwindow horder
    (recovery_cleanSaved_of_gate_prefix E rho hs cA P cleanResults)

omit [DecidableEq V] in
/-- A prefix ending at the anchor freeze does not reach the anchor gate. -/
theorem recovery_anchor_gate_after_freeze (p : Params) (cA : Slot) :
    SA.freezeTime p.toParams cA < SA.gateTime p.toParams cA := by
  have hd := p.deltaPos
  change 4 * p.Δ * (cA : Int) + 3 * p.Δ < 4 * p.Δ * (cA : Int) + 6 * p.Δ
  linarith

end AvailableChain.PCSA.Run
end
