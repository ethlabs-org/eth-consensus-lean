module
public import AvailableChainPCSAProofs.Proofs.Foundations.Duties
public import AvailableChainPCSAProofs.Proofs.Foundations.SnapshotRun
public import AvailableChainPCSAProofs.Proofs.Recovery.Exclusions
public import AvailableChainPCSAProofs.Proofs.Recovery.FirstHonestSlot
public import AvailableChainPCSAProofs.Proofs.Recovery.LockWindow

-- Keep the proposal handler matcher private in this proof module.
namespace AvailableChain.PCSA
private def recoveryAdmitBlock (p : Params) (st : State p.n) (s : Slot)
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

private theorem recoveryAdmitBlock_eq : @admitBlock = @recoveryAdmitBlock := rfl
end AvailableChain.PCSA

public section

/-! Run inputs for recovery: PC readers, anchor history, and long-break timing.
The clean-prefix CI and Formation remain named lane inputs. -/

namespace AvailableChain.PCSA
variable {n : Nat}

private theorem normalize_pcs (st : State n) : (normalizeS st).pcs = st.pcs := by
  delta normalizeS
  split <;> rfl

private theorem reconcile_pcs_genesis (st : State n) (hf : st.fg.F = .genesis) :
    (reconcile st).pcs = st.pcs := by
  delta reconcile
  rw [normalize_pcs]
  apply List.filter_eq_self.mpr
  intro pc _
  change Block.compatible pc.target (eraseFG st.fg.F) = true
  rw [hf]
  exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_genesis_preceq _))

private theorem recovery_read_reconcile_fg (st : State n) : (reconcile st).fg = st.fg := by
  delta reconcile normalizeS
  dsimp only
  split <;> rfl

private theorem acks_fg (st : State n) (as : List (AckWire n)) :
    (as.foldl poolAckRaw st).fg = st.fg := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, (poolAckRaw_frame st a).2.2.2]

private theorem row_pcs_fg (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).pcs = st.pcs ∧ (admitRow p st a).fg = st.fg := by
  delta admitRow
  cases hd : a.decode? <;> dsimp only
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

private theorem rows_fg (p : Params) (st : State p.n) (as : List (RowWire p.n)) :
    (as.foldl (admitRow p) st).fg = st.fg := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, (row_pcs_fg p st a).2]

private theorem rows_pcs (p : Params) (st : State p.n) (as : List (RowWire p.n)) :
    (as.foldl (admitRow p) st).pcs = st.pcs := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, (row_pcs_fg p st a).1]

private theorem acks_pcs (st : State n) (as : List (AckWire n)) :
    (as.foldl poolAckRaw st).pcs = st.pcs := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, (poolAckRaw_frame st a).1]

/-- Delivery keeps every held PC when the resulting frame is at genesis. -/
theorem process_pcs_mono_genesis (p : Params) (st : State p.n) (o : Wire p.n)
    (hf : (process p st o).fg.F = .genesis) : st.pcs ⊆ (process p st o).pcs := by
  delta process at hf ⊢
  cases hd : o.decode with
  | none => exact List.Subset.refl _
  | some msg =>
    rw [hd] at hf
    cases msg with
    | vote s i r => exact List.Subset.refl _
    | row i body => simpa only [(row_pcs_fg p st _).1] using List.Subset.refl st.pcs
    | ack s i r =>
      dsimp only
      delta admitAck
      have hc := collectPCs_pcs_mono (poolAck p st ⟨o.auth, r⟩)
      apply List.Subset.trans _ hc
      delta poolAck
      cases hd : AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) <;> dsimp only
      · exact List.Subset.refl _
      · rename_i v
        rcases v with ⟨_, _, _⟩
        split
        · exact List.Subset.refl _
        · split <;> exact List.Subset.refl _
    | pc pc =>
      dsimp only
      delta admitPC
      split
      · rw [← acks_pcs st pc.acks]
        exact collectPCs_pcs_mono _
      · exact List.Subset.refl _
    | block s N =>
      dsimp only at hf ⊢
      rw [recoveryAdmitBlock_eq] at hf ⊢
      delta recoveryAdmitBlock at hf ⊢
      split
      · exact List.Subset.refl _
      · rename_i hn
        simp only [hn, Bool.false_eq_true, ite_false] at hf
        cases hp : parentFG st N.erase with
        | none => exact List.Subset.refl _
        | some P =>
          rw [hp] at hf
          dsimp only at hf ⊢
          split
          · rename_i ha
            simp only [ha, ite_true] at hf
            rw [rows_fg, (collectPCs_frame _).2.2.2.2,
              acks_fg] at hf
            rw [rows_pcs]
            apply List.Subset.trans _ (collectPCs_pcs_mono _)
            rw [acks_pcs]
            let st1 : State p.n := { st with base := (GridCO.admitProposal
              p.toParams.engine st.base (baseProposal s N.erase N.raw N.support)
                N.erase (N.raw.map baseHead)) }
            let st2 := match N.pc with
              | none => st1
              | some pc => if pcValid st1 pc &&
                  !st1.pcs.any (fun o => o.slot == pc.slot && o.target == pc.target)
                then deleteConflictingLeases st1 pc else st1
            let st3 : State p.n := { st2 with
              fg := FGSA.Window.on_block p p.K_W st2.fg (fgBlock P N.erase N.rows)
              proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
            have hm : st3.pcs = st.pcs := by
              change st2.pcs = st.pcs
              dsimp only [st2]
              cases N.pc with
              | none => rfl
              | some pc => dsimp only; split <;> rfl
            change st.pcs ⊆ (if st3.fg.F = st.fg.F then st3 else reconcile st3).pcs
            change (if st3.fg.F = st.fg.F then st3 else reconcile st3).fg.F = .genesis at hf
            by_cases he : st3.fg.F = st.fg.F
            · rw [ite_eq_left he, hm]
            · rw [ite_eq_right he, recovery_read_reconcile_fg] at hf
              rw [ite_eq_right he, reconcile_pcs_genesis st3 hf, hm]
          · exact List.Subset.refl _

/-- A clock does not change held PC membership. -/
theorem clock_pcs_eq (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).pcs = st.pcs := by
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    dsimp only
    rw [normalize_pcs]
    split
    · exact clockPre_pcs p st t
    · rw [(gateFrom_pc_frame _ _ _ _ _ _).1, clockPre_pcs]
  · exact clockPre_pcs p st t

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Stage one and no restart make held PCs monotone at event indices. -/
theorem recovery_pcs_mono (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hnr : V2.D.NoRestart rho) (hf : StageOneFrame p c E rho)
    (x : V) (hx : x ∈ rho.honest) {i j : Nat} (hij : i ≤ j) :
    (V2.D.Run.stateBefore E rho i x).st.pcs ⊆
      (V2.D.Run.stateBefore E rho j x).st.pcs := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => (V2.D.Run.stateBefore E rho i x).st.pcs ⊆ nd.st.pcs)
    hij x ?_ (List.Subset.refl _)
  intro k e _ _ he hn h
  cases e with
  | restart y t => exact (hnr k y t he).elim
  | tick y t =>
    change y = x at hn
    subst y
    change _ ⊆ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.pcs
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t
    rw [ht, clock_pcs_eq]
    exact h
  | deliver y o t =>
    change y = x at hn
    subst y
    change _ ⊆ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.pcs
    rw [Function.update_self]
    apply List.Subset.trans h
    apply process_pcs_mono_genesis
    have hh := (hf x hx (k + 1)).1
    rw [V2.D.Run.stateBefore_succ E rho he] at hh
    change (Function.update (V2.D.Run.stateBefore E rho k) x
      ((pcsaWith m p c).process (V2.D.Run.stateBefore E rho k x) o) x).st.fg.F = .genesis at hh
    rw [Function.update_self] at hh
    delta pcsaWith at hh
    exact hh

/-- A PC at the after-ticks cut is held by the inclusive reader in stage one. -/
theorem recovery_stampRead (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    (hf : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest)
    (t : Time) (s : Slot) (B : Block) (hp : PCStampedBefore p c E rho x t s B) :
    ∃ pc ∈ (storeAt p c E rho x t).pcs, pc.slot = s ∧ pc.target = B := by
  obtain ⟨pc, hc, hslot, hb⟩ := hp
  have hr : storeAfterTicks p c E rho x t =
      (V2.D.Run.stateBefore E rho (FGSA.Run.afterTicksIdx rho t) x).st := by
    change (FGSA.Run.afterTicks E rho t x).st = _
    rw [FGSA.Run.afterTicks_eq_stateBefore E rho hs]
  rw [hr] at hc
  refine ⟨pc, ?_, hslot, hb⟩
  rw [storeAt_def, V2.D.Engine.readAt_eq_stateBefore hs]
  exact recovery_pcs_mono E rho hnr hf x hx
    (FGSA.Run.preIdx_le_afterTicksIdx E rho hs t).2 hc

end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA

private theorem saved_record_other {n : Nat} (v : GridCO.State n .root) (s i : Slot)
    (oc : Option Block) (hi : i ≠ s) :
    GridCO.savedGenuine { v with
      genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .root v s oc } i =
      GridCO.savedGenuine v i := by
  change ((@GridCO.recordGenuine GridCO.slowLeasePolicy n .root v s oc).find?
    (fun row => row.1 == i)).map Prod.snd = (v.genuine.find? (fun row => row.1 == i)).map Prod.snd
  delta GridCO.recordGenuine
  split
  · have hn : (s == i) = false := beq_eq_false_iff_ne.mpr hi.symm
    rw [List.find?_append]
    cases hf : v.genuine.find? (fun row => row.1 == i) <;> simp [hn]
  · rfl

private theorem slow_saved_origin (p : Params) (old acc : State p.n) (s : Slot) (B : Block)
    (hh : ∀ i < s, GridCO.savedGenuine acc.base i = GridCO.savedGenuine old.base i)
    (he : SA.Root.slowEligible p.toParams (actView acc) s B = true) :
    p.k ≤ s + 1 ∧ ∃ C, GridCO.savedGenuine old.base (s - (p.k - 1)) = some (some C) ∧
      Block.Preceq B C := by
  try delta Slot Time at *
  have hk := p.kLarge
  change (decide (p.k ≤ s + 1) && (List.range (p.k - 1)).all (fun d =>
    match GridCO.savedGenuine (actView acc) (s - (d + 1)) with
    | some (some C) => Block.preceq B C
    | _ => false)) = true at he
  obtain ⟨hs, hall⟩ := Bool.and_eq_true_iff.mp he
  have hks := of_decide_eq_true hs
  refine ⟨hks, ?_⟩
  have ho := List.all_eq_true.mp hall (p.k - 2) (List.mem_range.mpr (by omega))
  rw [show p.k - 2 + 1 = p.k - 1 by omega] at ho
  have hlt : s - (p.k - 1) < s := by omega
  cases hc : GridCO.savedGenuine (actView acc) (s - (p.k - 1)) with
  | none => simp only [hc, Bool.false_eq_true] at ho
  | some oc => cases oc with
    | none => simp only [hc, Bool.false_eq_true] at ho
    | some C =>
      rw [hc] at ho
      exact ⟨C, (hh _ hlt).symm.trans hc, ho⟩

private theorem gate_saved_origin (p : Params) (st : State p.n)
    (a : Block) (cs : List (PC p.n)) (rank : Option PCRank) (s : Slot) (B : Block)
    (hb : B ∈ (gateFrom p a cs rank st s).base.obligations.map Prod.fst) :
    B ∈ st.base.obligations.map Prod.fst ∨ p.k ≤ s + 1 ∧
      ∃ C, GridCO.savedGenuine st.base (s - (p.k - 1)) = some (some C) ∧
        Block.Preceq B C := by
  let Q := fun B => B ∈ st.base.obligations.map Prod.fst ∨ p.k ≤ s + 1 ∧
    ∃ C, GridCO.savedGenuine st.base (s - (p.k - 1)) = some (some C) ∧ Block.Preceq B C
  have hi : ∀ row ∈ st.base.obligations, Q row.1 :=
    fun row hm => Or.inl (List.mem_map.mpr ⟨row, hm, rfl⟩)
  have hw (acc : State p.n) (b : Block) (g : Nat) (d : Time)
      (h : (∀ i < s, GridCO.savedGenuine acc.base i = GridCO.savedGenuine st.base i) ∧
        ∀ row ∈ acc.base.obligations, Q row.1) (hq : Q b) :
      (∀ i < s, GridCO.savedGenuine (writeLease acc b g d rank).base i =
        GridCO.savedGenuine st.base i) ∧
        ∀ row ∈ (writeLease acc b g d rank).base.obligations, Q row.1 := by
    refine ⟨h.1, ?_⟩
    intro row hm
    change row ∈ (GridCO.writeObligation acc.base b g d).obligations at hm
    delta GridCO.writeObligation at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h.2 row (List.mem_filter.mp hm).1
    · cases List.mem_singleton.mp hm
      exact hq
  have older (oc : Option Block) : ∀ i < s,
      GridCO.savedGenuine
        { st.base with genuine := (@GridCO.recordGenuine GridCO.slowLeasePolicy
            p.n .root (actView st) s oc) } i = GridCO.savedGenuine st.base i := by
    intro i hi
    exact saved_record_other (actView st) s i oc (Nat.ne_of_lt hi)
  have hg : (∀ i < s, GridCO.savedGenuine (gateFrom p a cs rank st s).base i =
        GridCO.savedGenuine st.base i) ∧
      ∀ row ∈ (gateFrom p a cs rank st s).base.obligations, Q row.1 := by
    rw [gateFrom_def]
    dsimp only
    cases SA.Root.confirmationFrom p.toParams a (actView st) s with
    | none => exact ⟨older none, hi⟩
    | some C =>
      dsimp only
      split
      · exact ⟨older (some C), hi⟩
      · apply List.foldlRecOn (motive := fun acc : State p.n =>
          (∀ i < s, GridCO.savedGenuine acc.base i = GridCO.savedGenuine st.base i) ∧
            ∀ row ∈ acc.base.obligations, Q row.1)
        · exact ⟨older (some C), hi⟩
        · intro acc ha b _
          delta slowLevels
          split
          · rename_i he
            simpa only [List.foldl_cons, List.foldl_nil] using
              hw acc b _ _ ha (Or.inr (slow_saved_origin p st acc s b ha.1 he))
          · exact ha
  obtain ⟨row, hm, rfl⟩ := List.mem_map.mp hb
  exact hg.2 row hm

private theorem clock_saved_origin (p : Params) (st : State p.n) (t : Time) (B : Block)
    (hb : B ∈ (clock p st t).base.obligations.map Prod.fst) :
    B ∈ st.base.obligations.map Prod.fst ∨ ∃ s,
      t = SA.gateTime p.toParams s ∧ p.k ≤ s + 1 ∧
      ∃ C, GridCO.savedGenuine st.base (s - (p.k - 1)) = some (some C) ∧ Block.Preceq B C := by
  have hgs : (clockPre p st t).base.genuine = st.base.genuine := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> rfl
  delta clock at hb
  dsimp only at hb
  split at hb
  · rename_i ht
    have he : t = SA.gateTime p.toParams ((t - 6 * p.Δ) / (4 * p.Δ)).toNat :=
      eq_of_beq (Bool.and_eq_true_iff.mp ht).2
    rw [gateStep_def] at hb
    have hn (st : State p.n) : (normalizeS st).base.obligations = st.base.obligations := by
      delta normalizeS
      split <;> rfl
    dsimp only at hb
    rw [hn] at hb
    split at hb
    · exact Or.inl (clockPre_lock_targets_subset p st t hb)
    · rcases gate_saved_origin p _ _ _ _ _ B hb with hb | ⟨hk, C, hc, hp⟩
      · exact Or.inl (clockPre_lock_targets_subset p st t hb)
      · refine Or.inr ⟨_, he, hk, C, ?_, hp⟩
        delta GridCO.savedGenuine at hc ⊢
        rw [hgs] at hc
        exact hc
  · exact Or.inl (clockPre_lock_targets_subset p st t hb)

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Each lock target lies below an actual saved result from its oldest window label. -/
theorem recovery_lock_saved_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (i : Nat) (x : V) (B : Block)
    (hm : B ∈ (V2.D.Run.stateBefore E rho i x).st.base.obligations.map Prod.fst) :
    ∃ j < i, ∃ s, rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) ∧
      p.k ≤ s + 1 ∧ ∃ C,
      GridCO.savedGenuine (V2.D.Run.stateBefore E rho j x).st.base (s - (p.k - 1)) =
        some (some C) ∧ Block.Preceq B C := by
  obtain ⟨j, hj, t, he, s, ht, hv⟩ := V2.D.Engine.clock_field_origin_of_subset
    (P := pcsaWith m p c) (fun nd : Node p => nd.st.base.obligations.map Prod.fst)
    rfl (fun nd o B h => process_lock_targets_subset p nd.st (toWire p o) h)
    (fun _ _ _ h => h) (by intro nd B h; exact False.elim (List.not_mem_nil h))
    (fun nd t B => ∃ s, t = SA.gateTime p.toParams s ∧ p.k ≤ s + 1 ∧
      ∃ C, GridCO.savedGenuine nd.st.base (s - (p.k - 1)) = some (some C) ∧ Block.Preceq B C)
    (fun nd t B h => clock_saved_origin p nd.st t B h) E rho i x B hm
  exact ⟨j, hj, s, ht ▸ he, hv⟩

omit [DecidableEq V] in
/-- A gate visible at either first-slot read is at least two labels earlier. -/
theorem recovery_gate_before_read (p : Params) (s j : Slot) (t : Time)
    (ht : t = SA.proposalTime p.toParams s ∨ t = SA.voteTime p.toParams s)
    (hj : SA.gateTime p.toParams j ≤ t) : j + 2 ≤ s := by
  try delta Slot Time at *
  have hd : (0 : Int) < p.Δ := p.deltaPos
  have hb : t ≤ 4 * p.Δ * (s : Int) + p.Δ := by
    rcases ht with rfl | rfl
    · change 4 * p.Δ * (s : Int) ≤ _
      linarith
    · exact le_rfl
  change 4 * p.Δ * (j : Int) + 6 * p.Δ ≤ t at hj
  by_contra hn
  have hge : (s : Int) ≤ (j : Int) + 1 := by omega
  have hm := mul_le_mul_of_nonneg_left hge (show (0 : Int) ≤ 4 * p.Δ by positivity)
  linarith

/-- Prefix CI on earlier saved results puts every recovery lock below the anchor.
The named CI contract concerns labels strictly before cA. -/
theorem recovery_anchor_locks_of_clean_saved (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (cA s : Slot) (P : Block) (hwindow : s - 1 - cA ≤ p.k - 1) (horder : cA < s)
    (cleanSaved : ∀ x ∈ rho.honest, ∀ (i : Nat) (r : Slot) (C : Block), r < cA →
      GridCO.savedGenuine (V2.D.Run.stateBefore E rho i x).st.base r = some (some C) →
      Block.Preceq C P) :
    ∀ x ∈ rho.honest, ∀ t,
      t = SA.proposalTime p.toParams s ∨ t = SA.voteTime p.toParams s →
      ∀ nd, pcsa_postClock E rho x t = some nd → ∀ B, LiveLease nd.st B → Block.Preceq B P := by
  try delta Slot Time at *
  intro x hx t ht nd hn B hb
  rw [pcsa_postClock_def, pcsa_preTick_def] at hn
  obtain ⟨nd0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hn
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hn0
  have hit := V2.D.Run.tickIdx?_spec hi
  obtain ⟨row, hr, he, _⟩ := hb
  have hm : B ∈ (clock p (V2.D.Run.stateBefore E rho i x).st t).base.obligations.map
      Prod.fst := List.mem_map.mpr ⟨row, hr, he⟩
  have finish (k j : Nat) (hj : SA.gateTime p.toParams j ≤ t) (hk : p.k ≤ j + 1)
      (C : Block) (hc : GridCO.savedGenuine (V2.D.Run.stateBefore E rho k x).st.base
        (j - (p.k - 1)) = some (some C)) (hB : Block.Preceq B C) : Block.Preceq B P := by
    have hjs : j + 2 ≤ s := recovery_gate_before_read p s j t ht hj
    change (j : Nat) + 2 ≤ (s : Nat) at hjs
    have hp := p.kLarge
    have hl : s ≤ cA + p.k := by omega
    have hjc : j + 2 ≤ cA + p.k := hjs.trans hl
    have hold : j - (p.k - 1) < cA := by omega
    exact Gen.Pure.block_preceq_trans hB (cleanSaved x hx k _ C hold hc)
  rcases clock_saved_origin p _ t B hm with hold | ⟨j, hj, hk, C, hc, hB⟩
  · obtain ⟨k, hki, j, hkj, hk, C, hc, hB⟩ := recovery_lock_saved_origin E rho i x B hold
    obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hkj
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hit
    have hs' := (List.pairwise_iff_getElem.mp hs.sorted) k i hkl hil hki
    rw [hke, hie] at hs'
    exact finish k j (V2.D.Engine.time_le_of_key_le _ _ hs') hk C hc hB
  · exact finish i j hj.ge hk C hc hB

/-- The named prefix-CI contract supplies the old anchor-compatibility input. -/
theorem recovery_anchor_compatible_of_clean_saved (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (cA s : Slot) (P : Block) (hwindow : s - 1 - cA ≤ p.k - 1) (horder : cA < s)
    (cleanSaved : ∀ x ∈ rho.honest, ∀ (i : Nat) (r : Slot) (C : Block), r < cA →
      GridCO.savedGenuine (V2.D.Run.stateBefore E rho i x).st.base r = some (some C) →
      Block.Preceq C P) :
    ∀ x ∈ rho.honest, ∀ t,
      t = SA.proposalTime p.toParams s ∨ t = SA.voteTime p.toParams s →
      ∀ nd, pcsa_postClock E rho x t = some nd → ∀ B, LiveLease nd.st B → Block.Compatible B P := by
  intro x hx t ht nd hn B hb
  exact Bool.or_eq_true_iff.mpr (Or.inl
    (recovery_anchor_locks_of_clean_saved E rho hs cA s P hwindow horder cleanSaved
      x hx t ht nd hn B hb))

end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA

/-- A proposer PC is active, so the proposer base is its target or Z. -/
theorem recovery_proposer_base (p : Params) (st : State p.n) :
    walkBase p st (proposerPC p st) =
      ((proposerPC p st).map PC.target).getD (eraseFG (controls p st).Z) := by
  cases hp : proposerPC p st with
  | none => rfl
  | some pc =>
    have hm := bestPC_mem (st.pcs.filter (frameActive p st)) pc hp
    have ha := (List.mem_filter.mp hm).2
    change (if frameActive p st pc then pc.target else _) = pc.target
    rw [ha]
    rfl

end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- The short-window lock bound has a complete genesis-anchor branch. -/
theorem recovery_genesis_anchor_locks (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (s : Slot) (hpos : 0 < s) (hwindow : s - 1 ≤ p.k - 1) :
    ∀ x ∈ rho.honest, ∀ t,
      t = SA.proposalTime p.toParams s ∨ t = SA.voteTime p.toParams s →
      ∀ nd, pcsa_postClock E rho x t = some nd →
      ∀ B, LiveLease nd.st B → Block.Preceq B .genesis := by
  apply recovery_lock_bound_from_run E rho hs 0 s .genesis rfl
    (by simpa only [Nat.sub_zero] using hwindow) hpos
  intro x hx t ht nd hn B hb
  exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_genesis_preceq B))

/-- Genesis-anchor locks cannot change the effective root at either read. -/
theorem recovery_genesis_live_root (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (s : Slot) (hpos : 0 < s) (hwindow : s - 1 ≤ p.k - 1)
    (x : V) (hx : x ∈ rho.honest) (t : Time)
    (ht : t = SA.proposalTime p.toParams s ∨ t = SA.voteTime p.toParams s)
    (nd : Node p) (hn : pcsa_postClock E rho x t = some nd) (pc : Option (PC p.n)) :
    liveRoot p nd.st pc = walkBase p nd.st pc :=
  liveRoot_eq_base_of_locks_below p nd.st pc .genesis (Gen.Pure.block_genesis_preceq _)
    (recovery_genesis_anchor_locks E rho hs s hpos hwindow x hx t ht nd hn)

end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Slot zero has no named honest proposal in any run. -/
theorem recovery_no_named_proposal_zero (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (N : NamedProposal p.n) :
    ¬ HonestNamedProposal p c E rho 0 N := by
  intro h
  obtain ⟨k, hk, ho⟩ := h.2
  rw [(V2.D.Run.step_tick_eq E rho hk).2] at ho
  obtain ⟨_, _, d, hl, _, ha⟩ := (V2.D.Engine.mem_tick_seat_iff E rho _ _ _
    (.prop 0) (V2.D.propSeat (pcsaInterface p c (m := m)).toInterface 0)
      (.proposal N)).mp ho
  have hd : d = .propAction 0 := by
    have aux (d : RunDuty) (hl : d.signLabel = .prop 0) : d = .propAction 0 := by
      cases d with
      | headAction s =>
        change RunLabel.base (.head s) = .prop 0 at hl
        cases hl
      | fgAction r =>
        change RunLabel.base .fg = .prop 0 at hl
        cases hl
      | ackAction s =>
        change RunLabel.base (.ack s) = .prop 0 at hl
        cases hl
      | propAction s =>
        change RunLabel.prop s = .prop 0 at hl
        cases RunLabel.prop.inj hl
        rfl
    exact aux d hl
  subst d
  have hz (nd : Node p) (x : In) : actWith m p c nd (.propAction 0) x = none := by
    cases m <;> rfl
  have he : (none : Option (Msg p.n)) = some (.proposal N) := (hz _ _).symm.trans ha
  cases he

end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

omit [DecidableEq V] [Fintype V] in
/-- A first synchronous HEAD label exists, including label zero. -/
theorem recovery_first_sync_label (E : Generic.Env V) :
    ∃ g : Slot, E.t_GST ≤ SA.voteTime p.toParams g ∧
      ∀ j : Slot, j < g → SA.voteTime p.toParams j < E.t_GST := by
  have hd : (0 : Int) < p.Δ := p.deltaPos
  have hn : ∃ g : Nat, E.t_GST ≤ SA.voteTime p.toParams g := by
    refine ⟨E.t_GST.toNat + 1, ?_⟩
    have ht : (E.t_GST.toNat : Int) = E.t_GST := Int.toNat_of_nonneg E.t_GST_nonneg
    change E.t_GST ≤ 4 * p.Δ * ((E.t_GST.toNat + 1 : Nat) : Int) + p.Δ
    push_cast
    rw [ht]
    nlinarith [E.t_GST_nonneg]
  refine ⟨Nat.find hn, Nat.find_spec hn, ?_⟩
  intro j hj
  exact lt_of_not_ge (Nat.find_min hn hj)

omit [DecidableEq V] [Fintype V] in
/-- The mix time is late enough for old locks to expire and has the stated bound. -/
theorem recovery_mix_time (E : Generic.Env V) (g : Slot)
    (hg : E.t_GST ≤ SA.voteTime p.toParams g)
    (hmin : ∀ j : Slot, j < g → SA.voteTime p.toParams j < E.t_GST) :
    SA.gateTime p.toParams (g + p.k - 2) + pcsaL p =
        SA.voteTime p.toParams (g + 2 * p.k - 1) ∧
      E.t_GST + 12 * p.Δ ≤ SA.voteTime p.toParams (g + 2 * p.k - 1) ∧
      SA.voteTime p.toParams (g + 2 * p.k - 1) < E.t_GST + 2 * pcsaL p + 2 * p.Δ := by
  have hd : (0 : Int) < p.Δ := p.deltaPos
  have hk : 2 ≤ p.k := p.kLarge
  have hki : (2 : Int) ≤ p.k := by exact_mod_cast hk
  try delta Slot Time at *
  have hc : ((g + p.k - 2 : Nat) : Int) = (g : Int) + p.k - 2 := by omega
  have hc' : ((g + 2 * p.k - 1 : Nat) : Int) = (g : Int) + 2 * p.k - 1 := by omega
  have ht : SA.proposalTime p.toParams g < E.t_GST + 3 * p.Δ := by
    by_cases hz : g = 0
    · subst g
      change 4 * p.Δ * (0 : Int) < _
      nlinarith [E.t_GST_nonneg]
    · have hp := hmin (g - 1) (by omega)
      have hcast : ((g - 1 : Nat) : Int) = (g : Int) - 1 := by omega
      change 4 * p.Δ * ((g - 1 : Nat) : Int) + p.Δ < E.t_GST at hp
      rw [hcast] at hp
      change 4 * p.Δ * (g : Int) < _
      linarith
  change 4 * p.Δ * (g : Int) + p.Δ ≥ E.t_GST at hg
  change 4 * p.Δ * (g : Int) < _ at ht
  rw [pcsaL_def]
  change (4 * p.Δ * ((g + p.k - 2 : Nat) : Int) + 6 * p.Δ +
        (4 * (p.k : Int) - 1) * p.Δ =
      4 * p.Δ * ((g + 2 * p.k - 1 : Nat) : Int) + p.Δ) ∧ _
  rw [hc, hc']
  constructor
  · ring
  · change E.t_GST + 12 * p.Δ ≤
        4 * p.Δ * ((g + 2 * p.k - 1 : Nat) : Int) + p.Δ ∧
      4 * p.Δ * ((g + 2 * p.k - 1 : Nat) : Int) + p.Δ < _
    rw [hc']
    constructor <;> nlinarith

/-- RECOVERY gives an honest slot after the mix time at its proposal read. -/
theorem long_recovery_slot (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {G ΔF : Time} (h : Recovery₂ p c E rho G ΔF)
    (hh : E.t_GST + 2 * pcsaL p + G + 8 * p.Δ ≤ rho.horizon) :
    ∃ g s : Slot,
      E.t_GST ≤ SA.voteTime p.toParams g ∧
      (∀ j : Slot, j < g → SA.voteTime p.toParams j < E.t_GST) ∧
      SA.voteTime p.toParams (g + 2 * p.k - 1) < SA.proposalTime p.toParams s ∧
      E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s ∧
      Gen.V2.Duty.HonestAwakeProposer E (pcsaInterface p c (m := m)).toInterface rho s ∧
      SA.gateTime p.toParams s ≤ E.t_GST + 2 * pcsaL p + G + 8 * p.Δ := by
  obtain ⟨g, hg, hm⟩ := recovery_first_sync_label (p := p) E
  obtain ⟨_, hlo, hup⟩ := recovery_mix_time E g hg hm
  have hd : (0 : Int) < p.Δ := p.deltaPos
  obtain ⟨s, hs, hu, hp⟩ := h.gap (SA.voteTime p.toParams (g + 2 * p.k - 1))
    (by linarith) (by linarith)
  have hs' : SA.voteTime p.toParams (g + 2 * p.k - 1) < SA.proposalTime p.toParams s := hs
  have hu' : SA.proposalTime p.toParams s ≤
      SA.voteTime p.toParams (g + 2 * p.k - 1) + G := hu
  refine ⟨g, s, hg, hm, hs', by linarith, ⟨hp.2, ?_⟩, ?_⟩
  · exact h.awake _ hp.2 _ (by change E.t_GST ≤ SA.proposalTime p.toParams s; linarith)
      (by change SA.proposalTime p.toParams s ≤ rho.horizon; linarith)
  · have he : SA.gateTime p.toParams s = SA.proposalTime p.toParams s + 6 * p.Δ := rfl
    linarith

end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- CLEAN through z_c supplies the proposed prefix Formation delivery field. -/
theorem recovery_prefix_delivery (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (cA : Slot) (ΔF : Time)
    (h : Clean₂ p c E rho (SA.freezeTime p.toParams cA) ΔF) :
    Gen.V2.Duty.DeliveryWithinOn E rho IsNonRow
      (fun t => max t (SA.freezeTime p.toParams (cA - 1)) + E.Δ)
      (SA.freezeTime p.toParams cA) := by
  have hd : ∀ o : Obj p, IsNonRow o → pcsaDelay p E.Δ ΔF o = E.Δ := by
    intro o ho
    rw [pcsaDelay_def]
    cases he : o.payload <;> simp only [pcsa_IsNonRow_def, he] at ho ⊢
  have hD := Gen.V2.Duty.deliveryWithinOn_of_healthyPrefixBy E rho _ h.healthy IsNonRow E.Δ hd
  have hb (t : Time) : t + E.Δ ≤ max t (SA.freezeTime p.toParams (cA - 1)) + E.Δ :=
    Int.add_le_add_right (le_max_left _ _) E.Δ
  have hn (y : V) (o : Obj p) (t : Time)
      (he : (pcsaWith m p c).excludes (V2.D.Run.stateBeforeTime E rho
        (max t (SA.freezeTime p.toParams (cA - 1)) + E.Δ) y) o = false) :
      (pcsaWith m p c).excludes (V2.D.Run.stateBeforeTime E rho (t + E.Δ) y) o = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    have hf := recovery_excludes_time_mono E rho h.base.valid.toScheduleWellFormed
      h.base.noRestart y o _ _ (hb t) hh
    rw [he] at hf
    cases hf
  constructor
  · intro x hx o ho t ht y hy hc he
    obtain ⟨u, hu, hd, hr⟩ := hD.broadcast x hx o ho t ht y hy
      ((hb t).trans hc) (hn y o t he)
    exact ⟨u, hu, hd.trans_le (hb t), hr⟩
  · intro x hx i o ho t ht y hy hp hc he
    obtain ⟨u, hu, hd, hr⟩ := hD.relay x hx i o ho t ht y hy hp
      ((hb t).trans hc) (hn y o t he)
    exact ⟨u, hu, hd.trans_le (hb t), hr⟩

end AvailableChain.PCSA.Run

end
