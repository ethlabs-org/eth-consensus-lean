module
public import AvailableChainSAPC.Proofs.CleanSteps
public import AvailableChainSAPC.Proofs.Cap

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- The full joint invariant starts at the actual engine initial state. -/
theorem cleanPathFacts_initial {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) :
    CleanPathFacts p E rho 0 (fun b => b = .genesis) := by
  have hc : CleanPath (fun b => b = .genesis) := by
    refine ⟨rfl, ?_, ?_⟩
    · intro a b hp hb
      subst b
      simpa [Block.Preceq, Block.preceq] using hp
    · intro a b ha hb
      subst a; subst b
      exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.genesis_prefix _))
  refine ⟨hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi v _
    have he : i = 0 := Nat.le_zero.mp hi
    subst i
    exact initial_clean hc
  · intro b hb
    exact Or.inl hb
  · intro v _ b g d hm
    simp [Run.stateBefore, World.init, sapc, initial, GridCO.initial] at hm
  · intro j hj; omega
  · intro j hj; omega
  · intro i hi v _ c hv
    have he : i = 0 := Nat.le_zero.mp hi
    subst i
    change pcValid p (initial p.n) c = true at hv
    have hwf := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).1
    have hw := (Bool.and_eq_true_iff.mp hv).2
    cases he : c.witnesses with
    | nil =>
      have hq := (quorum_bounds p).1
      simp [pcWellFormed, he] at hwf
      omega
    | cons o os => simp [initial, he] at hw
  · intro i hi v _ r b hv
    have he : i = 0 := Nat.le_zero.mp hi
    subst i
    simp [Run.stateBefore, World.init, sapc, initial, savedTimely] at hv
  · intro _ i hi v _
    have he : i = 0 := Nat.le_zero.mp hi
    subst i
    rfl
  · intro i hi v _ r seat data hm
    have he : i = 0 := Nat.le_zero.mp hi
    subst i
    simp [Run.stateBefore, World.init, sapc, initial] at hm
  · intro i hi; omega
  · intro i hi; omega
  · intro i hi; omega

/-- The common path supplies finite-root compatibility; this premise
does not have to be inferred from a false lease-below-S assertion. -/
theorem CleanStateOnPath.liveRoot {n : Nat} {path : Block → Prop}
    (hc : CleanPath path) (st : GridCO.State n) (hs : CleanStateOnPath path st) :
    path (GridCO.liveRoot st) := by
  rcases (GridCO.liveRoot_is_deepest st).1 with he | hm
  · rw [he]; exact hc.genesis
  · obtain ⟨row, hrow, he⟩ := List.mem_filterMap.mp hm
    dsimp only [GridCO.liveTargets] at he
    split at he
    · have hb := Option.some.inj he
      exact hb ▸ hs.finite row.1 row.2.1 row.2.2 hrow
    · contradiction

/-- One event preserves the record order once the joint invariant
supplies the new raw result. Delivery needs no additional premise. -/
theorem record_step_of_joint {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (last i : Nat)
    {path : Block → Prop} (h : CleanPathFacts p E rho last path)
    (hi : i < last) (v : V) (hv : v ∈ rho.honest) :
    Block.Preceq (stable (Run.stateBefore (sapc p) rho i v))
      (stable (Run.stateBefore (sapc p) rho (i + 1) v)) := by
  set_option backward.isDefEq.respectTransparency false in
  cases he : rho.events[i]? with
  | none =>
    simp only [Run.stateBefore, List.take_add_one, he, Option.toList_none, List.append_nil]
    exact GridCO.block_preceq_self _
  | some e =>
    rw [stateBefore_succ_event he]
    cases e with
    | tick w t =>
      by_cases hvw : v = w
      · subst w
        have hc := clock_clean p (Run.stateBefore (sapc p) rho i v) t h.chain
          (h.states i hi.le v hv) (base_receiptStamped_at_fold p _ v) (by
            intro r b ht hb
            subst t
            exact h.genuine i hi v hv r b he hb)
        simpa only [World.step, sapc, Function.update_self] using hc.2
      · simpa only [World.step, Function.update_of_ne hvw] using
          GridCO.block_preceq_self (stable (Run.stateBefore (sapc p) rho i v))
    | deliver w obj t =>
      by_cases hvw : v = w
      · subst w
        simp only [World.step, sapc, Function.update_self, process_stable]
        exact GridCO.block_preceq_self _
      · simpa only [World.step, Function.update_of_ne hvw] using
          GridCO.block_preceq_self (stable (Run.stateBefore (sapc p) rho i v))

theorem record_prefix_of_joint {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (last : Nat)
    {path : Block → Prop} (h : CleanPathFacts p E rho last path)
    (i j : Nat) (hij : i ≤ j) (hj : j ≤ last) (v : V) (hv : v ∈ rho.honest) :
    Block.Preceq (stable (Run.stateBefore (sapc p) rho i v))
      (stable (Run.stateBefore (sapc p) rho j v)) := by
  induction j with
  | zero =>
    have he := Nat.le_zero.mp hij
    subst i
    exact GridCO.block_preceq_self _
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with he | hlt
    · subst i; exact GridCO.block_preceq_self _
    · exact GridCO.prefix_trans _ _ _ (ih (by omega) (by omega))
        (record_step_of_joint p E rho last j h (by omega) v hv)

/-- Top-down safety reduction. This is conditional on the full joint
invariant; it is not a proof that Sleepy establishes that invariant. -/
theorem clean_safety_of_joint {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hs : ScheduleWellFormed E rho) {path : Block → Prop}
    (h : CleanPathFacts p E rho rho.events.length path) (t₀ : Time) :
    SafeFrom (sapc p) rho (sapcInterface p).stable t₀ ∧
      SafeFrom (sapc p) rho (sapcInterface p).confirmed t₀ := by
  have hsafe : SafeFrom (sapc p) rho (sapcInterface p).stable t₀ := by
    constructor
    · intro u hu v hv t t' _ _ _ _
      change Block.Compatible (stable (Run.readAt (sapc p) rho t u))
        (stable (Run.readAt (sapc p) rho t' v))
      rw [readAt_eq_stateBefore hs t, readAt_eq_stateBefore hs t']
      exact h.chain.comparable _ _
        (h.states _ (List.length_filter_le _ _) u hu).stable
        (h.states _ (List.length_filter_le _ _) v hv).stable
    · intro v hv t t' _ htt' _
      change Block.Preceq (stable (Run.readAt (sapc p) rho t v))
        (stable (Run.readAt (sapc p) rho t' v))
      rw [readAt_eq_stateBefore hs t, readAt_eq_stateBefore hs t']
      apply record_prefix_of_joint p E rho _ h _ _ _ (List.length_filter_le _ _) v hv
      apply List.Sublist.length_le
      apply List.monotone_filter_right
      intro e he
      exact of_decide_eq_true he |>.trans htt' |> decide_eq_true
  exact ⟨hsafe, hsafe⟩

end AvailableChain.SAPC
end
