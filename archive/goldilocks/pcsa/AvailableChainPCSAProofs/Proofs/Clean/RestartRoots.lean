module
public import AvailableChainPCSAProofs.Proofs.Clean.NRoot
public import AvailableChainPCSAProofs.Proofs.Clean.PCChain
public import AvailableChainPCSAProofs.Proofs.Shared.RestartSeed
public import AvailableChainPCSAProofs.Proofs.Clean.LockFromCut
public import AvailableChainPCSAProofs.Proofs.Clean.NNextHead
public import AvailableChainPCSAProofs.Proofs.Clean.GateBatch
public import AvailableChainPCSAProofs.Proofs.Clean.JointAux

public section

/-! The restart base reads of the CI restart at label `a` (pcsa34-r5 §5.5): every
honest ack of label `a` has target `A`, and every honest root for `v_{a+1}` is `A`. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- Every honest ack of the seed label has the seed target. -/
theorem pcsa_restart_ack_target (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho)
    {a : Slot} {A : Block} (hS : CleanRestartSeed p c E rho a A)
    (y : V) (B : Block) (hB : HonestAckAt p c E rho y a B) : B = A := by
  obtain ⟨z, hz⟩ := pcsa_ack_has_honest_head E rho h hF hFault y a B hB
  exact hS.heads z B hz

/-- From `z_s` with `s ≥ a`, the voter view of an honest node at `v_{s+1}` is a
frame-active PC of slot at least `a`: the frozen row of label `s` holds the seed PC. -/
theorem pcsa_restart_voterPC_slot (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho)
    {a : Slot} {A : Block} (hS : CleanRestartSeed p c E rho a A)
    (x : V) (hx : x ∈ rho.honest) (s : Slot) (has : a ≤ s)
    (hz : SA.freezeTime p.toParams s ≤ rho.horizon) (k : Nat)
    (hk : rho.events[k]? = some (.tick x (SA.voteTime p.toParams (s + 1)))) :
    ∃ D, voterPC p (clock p (V2.D.Run.stateBefore E rho
        (V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1))) x).st
          (SA.voteTime p.toParams (s + 1))) (s + 1) = some D ∧
      frameActive p (clock p (V2.D.Run.stateBefore E rho
        (V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1))) x).st
          (SA.voteTime p.toParams (s + 1))) D = true ∧ a ≤ D.slot := by
  have hs := h.valid.toScheduleWellFormed
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have hpre := V2.D.Engine.stateBefore_tick_eq_stateBeforeTime hs h.noRestart hk
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hpre
  let b := V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1))
  let st := clock p (V2.D.Run.stateBefore E rho b x).st (SA.voteTime p.toParams (s + 1))
  change ∃ D, voterPC p st (s + 1) = some D ∧ frameActive p st D = true ∧ a ≤ D.slot
  have hk1 : (V2.D.Run.stateBefore E rho (k + 1) x).st = st := by
    rw [V2.D.Run.stateBefore_succ E rho hk, pcsa_tick_step, hpre]
  have hzv : SA.freezeTime p.toParams s < SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 3 * p.Δ < 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hzav : SA.freezeTime p.toParams a < SA.voteTime p.toParams (s + 1) := by
    apply lt_of_le_of_lt _ hzv
    change 4 * p.Δ * (a : Int) + 3 * p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    have has' : (a : Int) ≤ s := by exact_mod_cast has
    nlinarith
  have hpub : V2.PublicTime E (SA.freezeTime p.toParams s) := by
    refine ⟨4 * s + 3, ?_⟩
    rw [h.delta]
    change 4 * p.Δ * (s : Int) + 3 * p.Δ = ((4 * s + 3 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hz0 : 0 ≤ SA.freezeTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    positivity
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hs.tick_total x hx _ hpub hz0 hz)
  have hik : i < k + 1 := by
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
    by_contra hn
    have hki : k ≤ i := by omega
    rcases hki.lt_or_eq with hlt | he
    · have ht := (List.pairwise_iff_getElem.mp hs.sorted) k i hkl hil hlt
      rw [hke, hie] at ht
      have := V2.D.Engine.time_le_of_key_le _ _ ht
      exact absurd hzv (not_lt.mpr this)
    · subst he
      rw [hke] at hie
      simp only [V2.Event.tick.injEq, true_and] at hie
      rw [hie] at hzv
      exact absurd hzv (lt_irrefl _)
  obtain ⟨C, hC, hCs, hCt⟩ := pcsa_restart_snapshot_held E rho hs h.noRestart hF x hx a A
    (hS.stamped x hx) s has i hi (k + 1) hik
  rw [hk1] at hC
  obtain ⟨C', hC', hC's, hC't⟩ := pcsa_stamped_held E rho hs h.noRestart hF x hx _ a A
    (hS.stamped x hx) (k + 1)
    ((pcsa_afterTicksIdx_le_tick E rho hs hk hzav).trans (Nat.le_succ k))
  have hact : frameActive p st C = true := by
    have ha := pcsa_held_frameActive E rho hF x hx (k + 1) C' hC'
    rw [hk1] at ha
    rw [frameActive_def] at ha ⊢
    rw [hCt, ← hC't]
    exact ha
  have hm : C ∈ (pcSnapshotAt st s ++ carriedPCs st (s + 1)).filter (frameActive p st) :=
    List.mem_filter.mpr ⟨List.mem_append_left _ hC, hact⟩
  have hv' : voterPC p st (s + 1) = bestPC ((pcSnapshotAt st s ++ carriedPCs st (s + 1)).filter
      (frameActive p st)) := by
    unfold voterPC
    rw [Nat.add_sub_cancel]
  cases hv : voterPC p st (s + 1) with
  | none =>
    rw [hv] at hv'
    have he := pcsa_bestPC_none _ hv'.symm
    rw [he] at hm
    exact absurd hm List.not_mem_nil
  | some D =>
    rw [hv] at hv'
    have hDm := bestPC_mem _ D hv'.symm
    exact ⟨D, rfl, (List.mem_filter.mp hDm).2, hCs ▸ pcsa_bestPC_slot_of_mem _ C D hm hv'.symm⟩

omit [DecidableEq V] [Fintype V] in
/-- The read index is monotone in time. -/
private theorem restart_idx_window (rho : V2.D.Run V (pcsaWith m p c)) {t u : Time}
    (htu : t ≤ u) : V2.D.Run.idxBefore rho t ≤ V2.D.Run.idxBefore rho u := by
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def, ← List.countP_eq_length_filter,
    ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro e _ he
  exact decide_eq_true ((of_decide_eq_true he).trans_le htu)

/-- The honest root for `v_{a+1}` is the seed block: the frozen seed PC has the
maximum slot, its slot has one honest target, and every stored lock is below `A`. -/
theorem pcsa_restart_root_base (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho)
    {a : Slot} {A : Block} (hS : CleanRestartSeed p c E rho a A)
    (hz : SA.freezeTime p.toParams a ≤ rho.horizon)
    (x : V) (hx : x ∈ rho.honest) (R : Block)
    (hR : liveRootAt p c E rho x (a + 1) = some R) : R = A := by
  have hs := h.valid.toScheduleWellFormed
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  rw [pcsa_liveRootAt_def] at hR
  obtain ⟨nd, hnd, hr⟩ := Option.map_eq_some_iff.mp hR
  obtain ⟨k, hk, hst⟩ := pcsa_postClock_source E rho x _ nd hnd
  have hpre := V2.D.Engine.stateBefore_tick_eq_stateBeforeTime hs h.noRestart hk
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hpre
  let b := V2.D.Run.idxBefore rho (SA.voteTime p.toParams (a + 1))
  let st := clock p (V2.D.Run.stateBefore E rho b x).st (SA.voteTime p.toParams (a + 1))
  have hroot : liveRoot p st (voterPC p st (a + 1)) = R := by
    rw [hst, hpre] at hr
    exact hr
  obtain ⟨D, hv, hDa, hlo⟩ := pcsa_restart_voterPC_slot E rho h hF hS x hx a le_rfl hz k hk
  obtain ⟨y, hay, hty⟩ := pcsa_voterPC_honest_ack_before E rho h hFault b x hx (a + 1)
    le_rfl D hv
  have hhi : D.slot ≤ a := pcsa_early_label_before_vote p D.slot a hty
  have hDs : D.slot = a := Nat.le_antisymm hhi hlo
  have hDt : D.target = A := pcsa_restart_ack_target E rho h hF hFault hS y D.target
    (hDs ▸ hay)
  have hbase : walkBase p st (some D) = A := by
    change (if frameActive p st D then D.target else _) = A
    simp only [show frameActive p st D = true from hDa, ↓reduceIte]
    exact hDt
  rw [hv] at hroot
  rcases pcsa_liveRoot_origin p st (some D) with he | hl
  · rw [← hroot, he, hbase]
  · rw [hroot] at hl
    obtain ⟨row, hrow, hrR, _, _, _, hdepth, _⟩ := (pcsa_walkLocks_mem p st _ R).mp hl
    have hrow' := pcsa_vote_locks_subset p _ (a + 1) hrow
    have hmono := restart_idx_window rho (t := SA.freezeTime p.toParams a)
      (u := SA.voteTime p.toParams (a + 1)) (by
        change 4 * p.Δ * (a : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((a + 1 : Nat) : Int) + p.Δ
        push_cast
        linarith)
    have hmono' := restart_idx_window rho (t := SA.voteTime p.toParams (a + 1))
      (u := SA.gateTime p.toParams a) (by
        change 4 * p.Δ * ((a + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (a : Int) + 6 * p.Δ
        push_cast
        linarith)
    have hRA := hS.locksFromFreeze x hx b hmono hmono' row hrow'
    rw [hrR, ← hbase] at hRA
    exact absurd (Gen.Pure.prefix_depth _ _ hRA) (not_le.mpr hdepth)

/-- The sources of an honest root for `v_{s+1}` with `s ≥ a`: a block below the
seed, an honest ack of a label at least `a`, or an own result of a label in `[a, s)`. -/
theorem pcsa_next_root_source_from (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho)
    {a : Slot} {A : Block} (hS : CleanRestartSeed p c E rho a A)
    (x : V) (hx : x ∈ rho.honest) (s : Slot) (has : a ≤ s)
    (hz : SA.freezeTime p.toParams s ≤ rho.horizon) (R : Block)
    (hR : liveRootAt p c E rho x (s + 1) = some R) :
    Block.Preceq R A ∨
      (∃ y i, a ≤ i ∧ HonestAckAt p c E rho y i R ∧
        SA.earlyTime p.toParams i < SA.voteTime p.toParams (s + 1)) ∨
      (∃ i X, a ≤ i ∧ i < s ∧ gateResultAt p c E rho x i = some (some X) ∧
        Block.Preceq R X) := by
  have hs := h.valid.toScheduleWellFormed
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  rw [pcsa_liveRootAt_def] at hR
  obtain ⟨nd, hnd, hr⟩ := Option.map_eq_some_iff.mp hR
  obtain ⟨k, hk, hst⟩ := pcsa_postClock_source E rho x _ nd hnd
  have hpre := V2.D.Engine.stateBefore_tick_eq_stateBeforeTime hs h.noRestart hk
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hpre
  let b := V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1))
  let st := clock p (V2.D.Run.stateBefore E rho b x).st (SA.voteTime p.toParams (s + 1))
  have hroot : liveRoot p st (voterPC p st (s + 1)) = R := by
    rw [hst, hpre] at hr
    exact hr
  obtain ⟨D, hv, hDa, hlo⟩ := pcsa_restart_voterPC_slot E rho h hF hS x hx s has hz k hk
  rw [hv] at hroot
  rcases pcsa_liveRoot_origin p st (some D) with he | hl
  · right; left
    have hbase : walkBase p st (some D) = D.target := by
      change (if frameActive p st D then D.target else _) = D.target
      simp only [show frameActive p st D = true from hDa, ↓reduceIte]
    obtain ⟨y, hay, hty⟩ := pcsa_voterPC_honest_ack_before E rho h hFault b x hx (s + 1)
      le_rfl D hv
    rw [← hroot, he, hbase]
    exact ⟨y, D.slot, hlo, hay, hty⟩
  · rw [hroot] at hl
    obtain ⟨row, hrow, hrR, _⟩ := (pcsa_walkLocks_mem p st _ R).mp hl
    have hrow' := pcsa_vote_locks_subset p _ (s + 1) hrow
    let cut := V2.D.Run.idxBefore rho (SA.gateTime p.toParams a)
    have hzb : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams a) ≤ b :=
      restart_idx_window rho (by
        change 4 * p.Δ * (a : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
        have has' : (a : Int) ≤ s := by exact_mod_cast has
        push_cast
        nlinarith)
    have hzc : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams a) ≤ cut :=
      restart_idx_window rho (by
        change 4 * p.Δ * (a : Int) + 3 * p.Δ ≤ 4 * p.Δ * (a : Int) + 6 * p.Δ
        linarith)
    rcases le_total b cut with hbc | hcb
    · left
      have hRA := hS.locksFromFreeze x hx b hzb hbc row hrow'
      rwa [hrR] at hRA
    · rcases pcsa_lock_stateBefore_origin_from E rho h cut b hcb x row hrow' with
        hold | ⟨j, hcj, hjb, s', X, hj, hX, hRX, _⟩
      · left
        have hRA := hS.locksFromFreeze x hx cut hzc le_rfl row hold
        rwa [hrR] at hRA
      · right; right
        have hge : ¬ SA.gateTime p.toParams s' < SA.gateTime p.toParams a := fun hlt =>
          absurd ((Gen.V2.Duty.index_lt_idxBefore_iff hs hj _).mpr hlt) (not_lt.mpr hcj)
        have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hs hj _).mp hjb
        have has' : a ≤ s' := by
          by_contra hn
          apply hge
          change 4 * p.Δ * (s' : Int) + 6 * p.Δ < 4 * p.Δ * (a : Int) + 6 * p.Δ
          have : (s' : Int) + 1 ≤ a := by exact_mod_cast Nat.lt_of_not_ge hn
          nlinarith
        exact ⟨s', X, has', pcsa_gate_label_lt_next_vote p s' s hlt, hX, hrR ▸ hRX⟩

/-- From label `a`: prior dissemination and prior-result coverage place the next root
below an ack target of a label `s ≥ a`. A result of label `a` supplies the seed. -/
theorem pcsa_ack_next_root_below_from (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho)
    {a : Slot} {A : Block} (hS : CleanRestartSeed p c E rho a A)
    (s : Slot) (has : a ≤ s) (hz : SA.freezeTime p.toParams s ≤ rho.horizon)
    (hseed : ∃ w ∈ rho.honest, ∃ W, gateResultAt p c E rho w a = some (some W))
    (hpast : ∀ y H, HonestHeadAt p c E rho y s H →
      ∀ x ∈ rho.honest, ∀ i X, a ≤ i → i < s →
        gateResultAt p c E rho x i = some (some X) → Block.Preceq X H)
    (hdis : ∀ i, a ≤ i → i < s → ∀ y A', HonestAckAt p c E rho y i A' →
      ∀ z H, HonestHeadAt p c E rho z s H → Block.Preceq A' H)
    (x y : V) (hx : x ∈ rho.honest) (B R : Block)
    (hB : HonestAckAt p c E rho y s B)
    (hR : liveRootAt p c E rho x (s + 1) = some R) : Block.Preceq R B := by
  obtain ⟨z, hz'⟩ := pcsa_ack_has_honest_head E rho h hF hFault y s B hB
  rcases pcsa_next_root_source_from E rho h hF hFault hS x hx s has hz R hR with
    hRA | ⟨u, i, hai, ha, ht⟩ | ⟨i, X, hai, hi, hX, hrX⟩
  · apply Gen.Pure.block_preceq_trans hRA
    rcases has.lt_or_eq with hlt | heq
    · obtain ⟨w, hw, W, hW⟩ := hseed
      have hWA : W = A := Option.some.inj (hS.result w hw _ hW)
      rw [← hWA]
      exact hpast z B hz' w hw a W le_rfl hlt hW
    · subst heq
      rw [hS.heads z B hz']
      exact Gen.Pure.block_preceq_refl _
  · have his : i ≤ s := by
      by_contra hn
      have hi : (s : Int) + 1 ≤ (i : Int) := by exact_mod_cast Nat.lt_of_not_ge hn
      change 4 * p.Δ * (i : Int) + 2 * p.Δ <
        4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ at ht
      push_cast at ht
      have hp := p.deltaPos
      nlinarith
    rcases his.lt_or_eq with hi | hi
    · exact hdis i hai hi u R ha z B hz'
    · subst i
      rw [pcsa_ack_targets_unique E rho h hF hFault u y s R B ha hB]
      exact Gen.Pure.block_preceq_refl _
  · exact Gen.Pure.block_preceq_trans hrX (hpast z B hz' x hx i X hai hi hX)

/-- From label `a`: prior dissemination and result coverage imply current-ack
dissemination to next HEADs in the delivery window. -/
theorem pcsa_ack_dissemination_step_from (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {T₀ cut : Time}
    {a : Slot} {A : Block} (h : CleanWindow E rho a T₀ cut) (hF : StageOneFrame p c E rho)
    (hFault : FaultsBelowQA p c rho) (hS : CleanRestartSeed p c E rho a A)
    (s : Slot) (has : a ≤ s) (hc : SA.gateTime p.toParams s ≤ cut)
    (hpast : ∀ y H, HonestHeadAt p c E rho y s H →
      ∀ x ∈ rho.honest, ∀ i X, a ≤ i → i < s →
        gateResultAt p c E rho x i = some (some X) → Block.Preceq X H)
    (hdis : ∀ i, a ≤ i → i < s → ∀ y A', HonestAckAt p c E rho y i A' →
      ∀ z H, HonestHeadAt p c E rho z s H → Block.Preceq A' H)
    (x y : V) (B H : Block) (hB : HonestAckAt p c E rho x s B)
    (hH : HonestHeadAt p c E rho y (s + 1) H) : Block.Preceq B H := by
  have hzs : SA.freezeTime p.toParams s ≤ rho.horizon := by
    apply le_trans _ (hc.trans h.cut.2)
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  obtain ⟨W, hW⟩ := pcsa_clean_result_exists_win E rho h hF x hB.1 a le_rfl
    ((pcsa_gate_time_mono p has).trans hc)
  apply pcsa_honestAck_next_head_of_root_win E rho h hF hFault x y s B H has hc hB hH
  intro R hR
  exact Bool.or_eq_true_iff.mpr (Or.inl
    (pcsa_ack_next_root_below_from E rho h.base hF hFault hS s has hzs ⟨x, hB.1, W, hW⟩
      hpast hdis y x hH.1 B R hB hR))
end AvailableChain.PCSA.Run

end
