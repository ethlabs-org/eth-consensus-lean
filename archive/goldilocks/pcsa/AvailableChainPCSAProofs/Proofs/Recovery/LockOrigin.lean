module
public import AvailableChainPCSAClaims.Statements.LaneReads
public import AvailableChainPCSAProofs.Proofs.Foundations.Locks
public import AvailableChainPCSAProofs.Proofs.Foundations.Run
public import AvailableChainKitV2.DutyEngineClock

public section

/-! Slow-gate origins of stored lock targets. -/

namespace AvailableChain.PCSA

private def LockTargets {n : Nat} (Q : Block → Prop) (st : State n) : Prop :=
  ∀ row ∈ st.base.obligations, Q row.1

private theorem normalize_lockTargets {n : Nat} (Q : Block → Prop) (st : State n)
    (h : LockTargets Q st) : LockTargets Q (normalizeS st) := by
  delta normalizeS
  split <;> exact h

private theorem reconcile_lockTargets {n : Nat} (Q : Block → Prop) (st : State n)
    (h : LockTargets Q st) : LockTargets Q (reconcile st) := by
  apply normalize_lockTargets
  intro row hr
  exact h row (List.mem_filter.mp hr).1

private theorem install_lockTargets {n : Nat} (Q : Block → Prop) (st : State n)
    (pc : PC n) (h : LockTargets Q st) : LockTargets Q (installPC st pc) := by
  rw [installPC_def]
  split
  · exact h
  · intro row hr
    exact h row (deleteConflictingLeases_subset _ _ hr)

private theorem row_lockTargets (p : Params) (Q : Block → Prop) (st : State p.n)
    (a : RowWire p.n) (h : LockTargets Q st) : LockTargets Q (admitRow p st a) := by
  delta admitRow
  cases hd : a.decode? <;> dsimp only
  · exact h
  · split <;> exact h

private theorem rawAck_lockTargets {n : Nat} (Q : Block → Prop) (st : State n)
    (a : AckWire n) (h : LockTargets Q st) : LockTargets Q (poolAckRaw st a) := by
  delta poolAckRaw
  cases hd : a.decode? <;> dsimp only
  · exact h
  · split <;> exact h

private theorem process_lockTargets (p : Params) (Q : Block → Prop) (st : State p.n)
    (o : Wire p.n) (h : LockTargets Q st) : LockTargets Q (process p st o) := by
  have hc := collectPCs_invariant (n := p.n) (LockTargets Q)
    (fun st pc h _ => install_lockTargets Q st pc h)
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : LockTargets Q st) :
      LockTargets Q (as.foldl poolAckRaw st) :=
    List.foldlRecOn as poolAckRaw h (fun acc hh a _ => rawAck_lockTargets Q acc a hh)
  delta process
  cases hd : o.decode with
  | none => exact h
  | some msg => cases msg with
    | vote s i r =>
      intro row hr
      apply h row
      change row ∈ (GridCO.admitVote _ _ _).obligations at hr
      simpa only [GridCO.admitVote_obligations] using hr
    | row i body => exact row_lockTargets p Q st _ h
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact h
      · cases hp : parentFG st N.erase
        · exact h
        · dsimp only
          split
          · apply List.foldlRecOn
            · apply hc
              apply ha
              have hb : LockTargets Q { st with base := (GridCO.admitProposal
                    p.toParams.engine st.base (baseProposal s N.erase N.raw N.support)
                    N.erase (N.raw.map baseHead)) } := by
                intro row hr
                exact h row (by simpa only [GridCO.admitProposal_obligations] using hr)
              cases N.pc <;> dsimp only <;> split_ifs <;> first
                | (apply reconcile_lockTargets; exact hb)
                | (apply reconcile_lockTargets; intro row hr;
                    exact hb row (deleteConflictingLeases_subset _ _ hr))
                | exact hb
                | (intro row hr; exact hb row (deleteConflictingLeases_subset _ _ hr))
            · intro acc hh a _
              exact row_lockTargets p Q acc a hh
          · exact h
    | ack s i r =>
      dsimp only
      delta admitAck
      apply hc
      delta poolAck
      cases hd : AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) <;> dsimp only
      · exact h
      · rename_i v
        rcases v with ⟨_, _, _⟩
        split
        · exact h
        · split <;> exact h
    | pc pc =>
      dsimp only
      delta admitPC
      split
      · exact hc _ (ha _ _ h)
      · exact h

/-- A delivery cannot add a lock target. -/
theorem process_lock_targets_subset (p : Params) (st : State p.n) (o : Wire p.n) :
    (process p st o).base.obligations.map Prod.fst ⊆ st.base.obligations.map Prod.fst := by
  intro B hb
  obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hb
  exact process_lockTargets p (fun B => B ∈ st.base.obligations.map Prod.fst) st o
    (fun row hr => List.mem_map.mpr ⟨row, hr, rfl⟩) row hr

private theorem write_lockTargets {n : Nat} (Q : Block → Prop) (st : State n)
    (B : Block) (g : Nat) (d : Time) (rank : Option PCRank)
    (h : LockTargets Q st) (hb : Q B) : LockTargets Q (writeLease st B g d rank) := by
  intro row hr
  change row ∈ (GridCO.writeObligation st.base B g d).obligations at hr
  delta GridCO.writeObligation at hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h row (List.mem_filter.mp hr).1
  · cases List.mem_singleton.mp hr
    exact hb

/-- The gate creates only targets with a complete slow window. -/
theorem gate_lock_target_origin (p : Params) {n : Nat} (st : State n)
    (a : Block) (cs : List (PC n)) (rank : Option PCRank) (s : Slot) (B : Block)
    (h : B ∈ (gateFrom p a cs rank st s).base.obligations.map Prod.fst) :
    B ∈ st.base.obligations.map Prod.fst ∨
      ∃ v : GridCO.State n .root, SA.Root.slowEligible p.toParams v s B = true := by
  let Q := fun B => B ∈ st.base.obligations.map Prod.fst ∨
    ∃ v : GridCO.State n .root, SA.Root.slowEligible p.toParams v s B = true
  have hi : LockTargets Q st := fun row hr => Or.inl (List.mem_map.mpr ⟨row, hr, rfl⟩)
  have hg : LockTargets Q (gateFrom p a cs rank st s) := by
    rw [gateFrom_def]
    dsimp only
    cases hh : SA.Root.confirmationFrom p.toParams a (actView st) s
    · exact hi
    · dsimp only
      split
      · exact hi
      · apply List.foldlRecOn
        · exact hi
        · intro acc ha b _
          delta slowLevels
          split
          · rename_i hs
            simpa only [List.foldl_cons, List.foldl_nil] using
              write_lockTargets Q acc b _ _ rank ha (Or.inr ⟨actView acc, hs⟩)
          · exact ha
  obtain ⟨row, hr, rfl⟩ := List.mem_map.mp h
  exact hg row hr

/-- Expiry, freeze, early caching, and release add no lock target. -/
theorem clockPre_lock_targets_subset (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).base.obligations.map Prod.fst ⊆ st.base.obligations.map Prod.fst := by
  intro B hb
  obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hb
  apply List.mem_map.mpr
  refine ⟨row, ?_, rfl⟩
  delta clockPre at hr
  dsimp only at hr
  split at hr <;> split at hr <;> split at hr <;>
    dsimp only [onView, actView, SA.Root.release] at hr
  all_goals
    try delta GridCO.release at hr
    try delta GridCO.freeze at hr
    try delta GridCO.expire at hr
    simp only [List.mem_filter] at hr
    tauto

/-- A clock can add a target only at a slow gate. -/
theorem clock_lock_target_origin (p : Params) (st : State p.n) (t : Time) (B : Block)
    (h : B ∈ (clock p st t).base.obligations.map Prod.fst) :
    B ∈ st.base.obligations.map Prod.fst ∨ ∃ s,
      t = SA.gateTime p.toParams s ∧
      ∃ v : GridCO.State p.n .root, SA.Root.slowEligible p.toParams v s B = true := by
  delta clock at h
  dsimp only at h
  split at h
  · rename_i ht
    have ht' := (Bool.and_eq_true_iff.mp ht).2
    have he : t = SA.gateTime p.toParams ((t - 6 * p.Δ) / (4 * p.Δ)).toNat :=
      eq_of_beq ht'
    rw [gateStep_def] at h
    have hn (st : State p.n) : (normalizeS st).base.obligations = st.base.obligations := by
      delta normalizeS
      split <;> rfl
    dsimp only at h
    rw [hn] at h
    split at h
    · exact Or.inl (clockPre_lock_targets_subset p st t h)
    · rcases gate_lock_target_origin p _ _ _ _ _ B h with h | h
      · exact Or.inl (clockPre_lock_targets_subset p st t h)
      · exact Or.inr ⟨_, he, h⟩
  · exact Or.inl (clockPre_lock_targets_subset p st t h)

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Each stored lock target has a prior local slow-gate origin. -/
theorem lock_target_gate_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (i : Nat) (x : V) (B : Block)
    (h : B ∈ (V2.D.Run.stateBefore E rho i x).st.base.obligations.map Prod.fst) :
    ∃ j < i, ∃ s, rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) ∧
      ∃ v : GridCO.State p.n .root, SA.Root.slowEligible p.toParams v s B = true := by
  obtain ⟨j, hj, t, he, s, ht, hv⟩ := V2.D.Engine.clock_field_origin_of_subset
    (P := pcsaWith m p c) (fun nd : Node p => nd.st.base.obligations.map Prod.fst)
    rfl (fun nd o B h => process_lock_targets_subset p nd.st (toWire p o) h)
    (fun _ _ _ h => h) (by intro nd B h; exact False.elim (List.not_mem_nil h))
    (fun _ t B => ∃ s, t = SA.gateTime p.toParams s ∧
      ∃ v : GridCO.State p.n .root, SA.Root.slowEligible p.toParams v s B = true)
    (fun nd t B h => clock_lock_target_origin p nd.st t B h) E rho i x B h
  exact ⟨j, hj, s, ht ▸ he, hv⟩

/-- A live lock at a post-clock read has a slow-gate origin no later than the read. -/
theorem live_lock_gate_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (x : V) (t : Time) (nd : Node p) (hn : pcsa_postClock E rho x t = some nd)
    (B : Block) (hb : LiveLease nd.st B) :
    ∃ s, SA.gateTime p.toParams s ≤ t ∧ p.k ≤ s + 1 ∧
      ∃ v : GridCO.State p.n .root, SA.Root.slowEligible p.toParams v s B = true := by
  rw [pcsa_postClock_def, pcsa_preTick_def] at hn
  obtain ⟨nd0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hn
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hn0
  have hit := V2.D.Run.tickIdx?_spec hi
  obtain ⟨row, hr, he, _⟩ := hb
  have hm : B ∈ (clock p (V2.D.Run.stateBefore E rho i x).st t).base.obligations.map
      Prod.fst := List.mem_map.mpr ⟨row, hr, he⟩
  have ho : ∃ s, SA.gateTime p.toParams s ≤ t ∧
      ∃ v : GridCO.State p.n .root, SA.Root.slowEligible p.toParams v s B = true := by
    rcases clock_lock_target_origin p _ t B hm with hold | ⟨s, ht, hv⟩
    · obtain ⟨j, hj, s, hjs, hv⟩ := lock_target_gate_origin E rho i x B hold
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hjs
      obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hit
      have hk := (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hj
      rw [hje, hie] at hk
      exact ⟨s, V2.D.Engine.time_le_of_key_le _ _ hk, hv⟩
    · exact ⟨s, ht.ge, hv⟩
  obtain ⟨s, ht, v, hv⟩ := ho
  refine ⟨s, ht, ?_, v, hv⟩
  change (decide (p.k ≤ s + 1) && _) = true at hv
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp hv).1

end AvailableChain.PCSA.Run
end
