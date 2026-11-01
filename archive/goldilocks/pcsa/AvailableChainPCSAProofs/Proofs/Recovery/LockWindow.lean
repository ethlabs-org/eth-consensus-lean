module
public import AvailableChainPCSAProofs.Proofs.Recovery.LockOrigin
public import AvailableChainPCSAProofs.Proofs.Recovery.LockBound
public import AvailableChainFGSA.Proofs.Head.Pool
public import AvailableChainPCSAProofs.Proofs.Shared.SlotOrder

public section

/-! Slow-window bounds and strict slot order in PC-SA runs. -/
namespace AvailableChain.PCSA

/-- Every block in a reachable PC-SA tree has strictly increasing parent slots. -/
theorem recovery_reachable_slot_order (p : Params) (st : State p.n) (h : Reachable p st) :
    ∀ B ∈ st.base.blocks, RecoverySlotOrdered B :=
  pcsa_reachable_slot_order p st h

/-- A proper ancestor of a stored block has a strictly smaller slot. -/
theorem recovery_stored_strict_slots (p : Params) (st : State p.n) (h : Reachable p st)
    (P B : Block) (hb : B ∈ st.base.blocks) (hp : Block.Preceq P B) (hne : P ≠ B) :
    P.slot < B.slot :=
  pcsa_stored_strict_slots p st h P B hb hp hne

/-- Every prefix of a genuine result has slot at most the result label. -/
theorem recovery_result_prefix_slot (p : Params) (v : GridCO.State p.n .root)
    (a C B : Block) (s : Slot) (ho : ∀ D ∈ v.blocks, RecoverySlotOrdered D)
    (hc : SA.Root.confirmationFrom p.toParams a v s = some C)
    (hb : Block.Preceq B C) : B.slot ≤ s :=
  pcsa_result_prefix_slot p v a C B s ho hc hb

/-- Every prefix of a saved result is bounded by its label. -/
theorem recovery_saved_result_slot (p : Params) (st : State p.n) (h : Reachable p st) :
    ∀ row ∈ st.base.genuine, ∀ C, row.2 = some C →
      ∀ B, Block.Preceq B C → B.slot ≤ row.1 :=
  pcsa_saved_result_slot p st h


private def TreeOrdered {n : Nat} (st : State n) : Prop :=
  ∀ B ∈ st.base.blocks, RecoverySlotOrdered B

private def ResultsBound {n : Nat} (st : State n) : Prop :=
  ∀ row ∈ st.base.genuine, ∀ C, row.2 = some C →
    ∀ B, Block.Preceq B C → B.slot ≤ row.1

private def LocksOrdered {n : Nat} (st : State n) : Prop :=
  ∀ row ∈ st.base.obligations, RecoverySlotOrdered row.1

private theorem write_ordered {n : Nat} (st : State n) (B : Block) (g : Nat)
    (d : Time) (rank : Option PCRank) (h : LocksOrdered st) (hb : RecoverySlotOrdered B) :
    LocksOrdered (writeLease st B g d rank) := by
  intro row hr
  change row ∈ (GridCO.writeObligation st.base B g d).obligations at hr
  delta GridCO.writeObligation at hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h row (List.mem_filter.mp hr).1
  · cases List.mem_singleton.mp hr
    exact hb

private theorem gate_locks_ordered (p : Params) (st : State p.n)
    (a : Block) (cs : List (PC p.n)) (rank : Option PCRank) (s : Slot)
    (ht : TreeOrdered st) (h : LocksOrdered st) :
    LocksOrdered (gateFrom p a cs rank st s) := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => exact h
  | some B =>
    dsimp only
    split
    · exact h
    · apply List.foldlRecOn
      · exact h
      · intro acc hh b hb
        have hm : b ∈ st.base.blocks := (List.mem_filter.mp (List.mem_filter.mp hb).1).1
        apply List.foldlRecOn
        · exact hh
        · intro acc' hh' g _
          exact write_ordered acc' b g _ rank hh' (ht b hm)

private theorem clock_locks_ordered (p : Params) (st : State p.n) (t : Time)
    (ht : TreeOrdered st) (h : LocksOrdered st) : LocksOrdered (clock p st t) := by
  have hc : LocksOrdered (clockPre p st t) := by
    intro row hr
    obtain ⟨old, hold, he⟩ := List.mem_map.mp
      (clockPre_lock_targets_subset p st t (List.mem_map.mpr ⟨row, hr, rfl⟩))
    exact he ▸ h old hold
  have hct : TreeOrdered (clockPre p st t) := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> exact ht
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    dsimp only
    have hn (st : State p.n) (h : LocksOrdered st) : LocksOrdered (normalizeS st) := by
      delta normalizeS
      split <;> exact h
    apply hn
    split
    · exact hc
    · exact gate_locks_ordered p _ _ _ _ _ hct hc
  · exact hc

/-- Every stored lock target has increasing slots along its ancestry. -/
theorem recovery_reachable_lock_order (p : Params) (st : State p.n) (h : Reachable p st) :
    ∀ row ∈ st.base.obligations, RecoverySlotOrdered row.1 := by
  induction h with
  | init => intro row hr; exact (List.not_mem_nil hr).elim
  | tick t hh ih => exact clock_locks_ordered p _ t (pcsa_reachable_slot_order p _ hh) ih
  | deliver o _ ih =>
    intro row hr
    obtain ⟨old, hold, he⟩ := List.mem_map.mp
      (process_lock_targets_subset p _ o (List.mem_map.mpr ⟨row, hr, rfl⟩))
    exact he ▸ ih old hold

/-- Proper descendants among live locks have strictly greater slots. -/
theorem recovery_live_strict_slots (p : Params) (st : State p.n) (h : Reachable p st)
    (P B : Block) (hb : LiveLease st B) (hp : Block.Preceq P B) (hne : P ≠ B) :
    P.slot < B.slot := by
  obtain ⟨row, hr, he, _⟩ := hb
  have ho : RecoverySlotOrdered B := he ▸ recovery_reachable_lock_order p st h row hr
  by_contra hn
  exact hne (pcsa_prefix_eq_of_slot_ge P B ho hp (Nat.le_of_not_gt hn))


private theorem slow_result_bound (p : Params) (st : State p.n) (s : Slot) (B : Block)
    (h : ResultsBound st) (he : SA.Root.slowEligible p.toParams (actView st) s B = true) :
    p.k ≤ s + 1 ∧ B.slot ≤ s - (p.k - 1) := by
  try delta Slot Time at *
  have hk := p.kLarge
  change (decide (p.k ≤ s + 1) && (List.range (p.k - 1)).all (fun d =>
    match GridCO.savedGenuine (actView st) (s - (d + 1)) with
    | some (some C) => Block.preceq B C
    | _ => false)) = true at he
  obtain ⟨hs, hall⟩ := Bool.and_eq_true_iff.mp he
  refine ⟨of_decide_eq_true hs, ?_⟩
  have ho := List.all_eq_true.mp hall (p.k - 2) (List.mem_range.mpr (by omega))
  rw [show p.k - 2 + 1 = p.k - 1 by omega] at ho
  cases hc : GridCO.savedGenuine (actView st) (s - (p.k - 1)) with
  | none => simp only [hc, Bool.false_eq_true] at ho
  | some oc => cases oc with
    | none => simp only [hc, Bool.false_eq_true] at ho
    | some C =>
      rw [hc] at ho
      change (st.base.genuine.find? (fun row => row.1 == s - (p.k - 1))).map Prod.snd =
        some (some C) at hc
      obtain ⟨row, hf, hr⟩ := Option.map_eq_some_iff.mp hc
      have hl : row.1 = s - (p.k - 1) := by simpa using List.find?_some hf
      simpa only [hl] using h row (List.mem_of_find?_eq_some hf) C hr B ho

private theorem gate_window_origin (p : Params) (st : State p.n)
    (a : Block) (cs : List (PC p.n)) (rank : Option PCRank) (s : Slot)
    (ht : TreeOrdered st) (hr : ResultsBound st) (B : Block)
    (hb : B ∈ (gateFrom p a cs rank st s).base.obligations.map Prod.fst) :
    B ∈ st.base.obligations.map Prod.fst ∨
      p.k ≤ s + 1 ∧ B.slot ≤ s - (p.k - 1) := by
  let Q := fun B => B ∈ st.base.obligations.map Prod.fst ∨
    p.k ≤ s + 1 ∧ B.slot ≤ s - (p.k - 1)
  have hi : ∀ row ∈ st.base.obligations, Q row.1 :=
    fun row hm => Or.inl (List.mem_map.mpr ⟨row, hm, rfl⟩)
  have hw (acc : State p.n) (b : Block) (g : Nat) (d : Time)
      (h : ResultsBound acc ∧ ∀ row ∈ acc.base.obligations, Q row.1) (hq : Q b) :
      ResultsBound (writeLease acc b g d rank) ∧
        ∀ row ∈ (writeLease acc b g d rank).base.obligations, Q row.1 := by
    refine ⟨h.1, ?_⟩
    intro row hm
    change row ∈ (GridCO.writeObligation acc.base b g d).obligations at hm
    delta GridCO.writeObligation at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h.2 row (List.mem_filter.mp hm).1
    · cases List.mem_singleton.mp hm
      exact hq
  have hg : ResultsBound (gateFrom p a cs rank st s) ∧
      ∀ row ∈ (gateFrom p a cs rank st s).base.obligations, Q row.1 := by
    rw [gateFrom_def]
    dsimp only
    cases hc : SA.Root.confirmationFrom p.toParams a (actView st) s with
    | none => exact ⟨pcsa_record_results p st s none hr (by intro C he; cases he), hi⟩
    | some C =>
      have hn := pcsa_record_results p st s (some C) hr (by
        intro D hd B hb
        cases Option.some.inj hd
        exact pcsa_result_prefix_slot p (actView st) a C B s
          (fun D hd => ht D (List.mem_filter.mp hd).1) hc hb)
      dsimp only
      split
      · exact ⟨hn, hi⟩
      · apply List.foldlRecOn (motive := fun acc : State p.n => ResultsBound acc ∧
          ∀ row ∈ acc.base.obligations, Q row.1)
        · exact ⟨hn, hi⟩
        · intro acc ha b _
          delta slowLevels
          split
          · rename_i he
            simpa only [List.foldl_cons, List.foldl_nil] using
              hw acc b _ _ ha (Or.inr (slow_result_bound p acc s b ha.1 he))
          · exact ha
  obtain ⟨row, hm, rfl⟩ := List.mem_map.mp hb
  exact hg.2 row hm

private theorem clock_window_origin (p : Params) (st : State p.n) (t : Time)
    (h : Reachable p st) (B : Block)
    (hb : B ∈ (clock p st t).base.obligations.map Prod.fst) :
    B ∈ st.base.obligations.map Prod.fst ∨ ∃ s,
      t = SA.gateTime p.toParams s ∧ p.k ≤ s + 1 ∧ B.slot ≤ s - (p.k - 1) := by
  have ht := pcsa_reachable_slot_order p st h
  have hr := pcsa_saved_result_slot p st h
  have hct : TreeOrdered (clockPre p st t) := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> exact ht
  have hcr : ResultsBound (clockPre p st t) := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> exact hr
  delta clock at hb
  dsimp only at hb
  split at hb
  · rename_i hg
    have he : t = SA.gateTime p.toParams ((t - 6 * p.Δ) / (4 * p.Δ)).toNat :=
      eq_of_beq (Bool.and_eq_true_iff.mp hg).2
    rw [gateStep_def] at hb
    have hn (st : State p.n) : (normalizeS st).base.obligations = st.base.obligations := by
      delta normalizeS
      split <;> rfl
    dsimp only at hb
    rw [hn] at hb
    split at hb
    · exact Or.inl (clockPre_lock_targets_subset p st t hb)
    · rcases gate_window_origin p _ _ _ _ _ hct hcr B hb with hb | hb
      · exact Or.inl (clockPre_lock_targets_subset p st t hb)
      · exact Or.inr ⟨_, he, hb⟩
  · exact Or.inl (clockPre_lock_targets_subset p st t hb)

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- A stored lock target has an actual gate with the full oldest-label bound. -/
theorem recovery_lock_window_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (i : Nat) (x : V) (B : Block)
    (hm : B ∈ (V2.D.Run.stateBefore E rho i x).st.base.obligations.map Prod.fst) :
    ∃ j < i, ∃ s, rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) ∧
      p.k ≤ s + 1 ∧ B.slot ≤ s - (p.k - 1) := by
  induction i with
  | zero => exact (List.not_mem_nil hm).elim
  | succ i ih =>
    have old (h : B ∈ (V2.D.Run.stateBefore E rho i x).st.base.obligations.map Prod.fst) :
        ∃ j < i + 1, ∃ s, rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) ∧
          p.k ≤ s + 1 ∧ B.slot ≤ s - (p.k - 1) := by
      obtain ⟨j, hj, hs⟩ := ih h
      exact ⟨j, Nat.lt_succ_of_lt hj, hs⟩
    cases hi : rho.events[i]? with
    | none =>
      apply old
      simpa only [V2.D.Run.stateBefore, List.take_add_one, hi, Option.toList_none,
        List.append_nil] using hm
    | some e =>
      rw [V2.D.Run.stateBefore_succ E rho hi] at hm
      by_cases hn : e.node = x
      · cases e with
        | restart y t =>
          change y = x at hn
          subst y
          change B ∈ (Function.update (V2.D.Run.stateBefore E rho i) x _ x).st.base.obligations.map
            Prod.fst at hm
          rw [Function.update_self] at hm
          exact (List.not_mem_nil hm).elim
        | deliver y o t =>
          change y = x at hn
          subst y
          change B ∈ (Function.update (V2.D.Run.stateBefore E rho i) x _ x).st.base.obligations.map
            Prod.fst at hm
          rw [Function.update_self] at hm
          exact old (process_lock_targets_subset p _ (toWire p o) hm)
        | tick y t =>
          change y = x at hn
          subst y
          change B ∈ (Function.update (V2.D.Run.stateBefore E rho i) x _ x).st.base.obligations.map
            Prod.fst at hm
          rw [Function.update_self] at hm
          have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho i x) x t
          rw [ht] at hm
          rcases clock_window_origin p _ t (pcsa_reachable_stateBefore E rho i x) B hm with
            hm | ⟨s, hs, hb⟩
          · exact old hm
          · exact ⟨i, Nat.lt_succ_self i, s, hs ▸ hi, hb⟩
      · rw [V2.D.World.step_apply_of_node_ne E rho _ hn] at hm
        exact old hm

/-- The full lock-origin input at both recovery reads follows from the run. -/
theorem recovery_live_lock_window_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (x : V) (t : Time) (nd : Node p) (hn : pcsa_postClock E rho x t = some nd)
    (B : Block) (hb : LiveLease nd.st B) :
    ∃ s, SA.gateTime p.toParams s ≤ t ∧ p.k ≤ s + 1 ∧ B.slot ≤ s - (p.k - 1) := by
  rw [pcsa_postClock_def, pcsa_preTick_def] at hn
  obtain ⟨nd0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hn
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hn0
  have hit := V2.D.Run.tickIdx?_spec hi
  obtain ⟨row, hr, he, _⟩ := hb
  have hm : B ∈ (clock p (V2.D.Run.stateBefore E rho i x).st t).base.obligations.map
      Prod.fst := List.mem_map.mpr ⟨row, hr, he⟩
  rcases clock_window_origin p _ t (pcsa_reachable_stateBefore E rho i x) B hm with
    hold | ⟨s, ht, hv⟩
  · obtain ⟨j, hj, s, hjs, hv⟩ := recovery_lock_window_origin E rho i x B hold
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hjs
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hit
    have hk := (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hj
    rw [hje, hie] at hk
    exact ⟨s, V2.D.Engine.time_le_of_key_le _ _ hk, hv⟩
  · exact ⟨s, ht.ge, hv⟩

/-- A post-clock reader has a reachable store. -/
theorem recovery_postClock_reachable (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (t : Time) (nd : Node p)
    (hn : pcsa_postClock E rho x t = some nd) : Reachable p nd.st := by
  rw [pcsa_postClock_def, pcsa_preTick_def] at hn
  obtain ⟨nd0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hn
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp hn0
  exact Reachable.tick t (pcsa_reachable_stateBefore E rho i x)

/-- The two-read lock bound now needs only anchor compatibility. -/
theorem recovery_lock_bound_from_run (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (cA s₁ : Slot) (P : Block) (hslot : P.slot = cA)
    (hwindow : s₁ - 1 - cA ≤ p.k - 1) (horder : cA < s₁)
    (anchorCompatible : ∀ x ∈ rho.honest, ∀ t,
      t = SA.proposalTime p.toParams s₁ ∨ t = SA.voteTime p.toParams s₁ →
      ∀ nd, pcsa_postClock E rho x t = some nd → ∀ B, LiveLease nd.st B →
      Block.Compatible B P) :
    ∀ x ∈ rho.honest, ∀ t,
      t = SA.proposalTime p.toParams s₁ ∨ t = SA.voteTime p.toParams s₁ →
      ∀ nd, pcsa_postClock E rho x t = some nd →
      ∀ B, LiveLease nd.st B → Block.Preceq B P := by
  apply recovery_lock_bound E rho cA s₁ P hwindow horder
  · intro x _ t _ nd hn B hb
    exact recovery_live_lock_window_origin E rho hs x t nd hn B hb
  · exact anchorCompatible
  · intro x _ t _ nd hn B hb hp hne
    rw [← hslot]
    exact recovery_live_strict_slots p nd.st (recovery_postClock_reachable E rho x t nd hn)
      P B hb hp hne

end AvailableChain.PCSA.Run
end
