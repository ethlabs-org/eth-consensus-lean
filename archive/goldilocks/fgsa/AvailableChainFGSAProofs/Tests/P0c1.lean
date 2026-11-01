module
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyClient
public import AvailableChainFGCompose.Proofs.ObservationTransport
public import AvailableChainFGSAProofs.Proofs.Foundations.Sources
public import AvailableChainFGSAProofs.Proofs.Finality.RowsBatch
public import AvailableChainFGSAInhabit.WitnessPositive

set_option linter.privateModule false

public section

namespace AvailableChain.FGSA.Run.Tests.P0c1
open AvailableChain.SimplexFG
open Gen.Pure

private def c1g0_observations (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (fgsaCoreReads p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def c1g0_selection (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGSelectionReads (fgsa p c) p.n where
  select nd := (FGSA.fgSource p nd.st, fgBlockOf nd.st (fgHead p nd.st))
  clientInputs nd := fgInputs p nd.st

private def c1g0_deeper (a b : Block) : Block :=
  if a.depth < b.depth || (a.depth == b.depth && a.root < b.root) then b else a

private theorem c1g0_deeper_depth (a b : Block) :
    a.depth ≤ (c1g0_deeper a b).depth ∧ b.depth ≤ (c1g0_deeper a b).depth := by
  unfold c1g0_deeper
  split
  · next h =>
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact ⟨Nat.le_of_lt (of_decide_eq_true h), le_rfl⟩
    · exact ⟨(beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).1).le, le_rfl⟩
  · next h =>
    have hn : ¬ a.depth < b.depth := by
      intro hab
      exact h (by simp only [hab, decide_true, Bool.true_or])
    exact ⟨le_rfl, Nat.le_of_not_gt hn⟩

private theorem c1g0_fold_depth (xs : List Block) (init : Block) :
    init.depth ≤ (xs.foldl c1g0_deeper init).depth ∧
      ∀ b ∈ xs, b.depth ≤ (xs.foldl c1g0_deeper init).depth := by
  induction xs generalizing init with
  | nil => exact ⟨le_rfl, fun _ h => (List.not_mem_nil h).elim⟩
  | cons x xs ih =>
    obtain ⟨hi, hb⟩ := ih (c1g0_deeper init x)
    refine ⟨(c1g0_deeper_depth init x).1.trans hi, ?_⟩
    intro b hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact (c1g0_deeper_depth init b).2.trans hi
    · exact hb b hm


private theorem c1g0_fold_covers (xs : List Block) (init B : Block) (hB : B ∈ xs)
    (hinit : Block.Compatible init B)
    (hxs : ∀ b ∈ xs, Block.Compatible b B) :
    Block.Preceq B (xs.foldl (fun a b =>
      if a.depth < b.depth || (a.depth == b.depth && a.root < b.root) then b else a) init) := by
  change Block.Preceq B (xs.foldl c1g0_deeper init)
  have hdepth := (c1g0_fold_depth xs init).2 B hB
  have hmem := foldl_select_mem (fun (a b : Block) =>
    a.depth < b.depth || (a.depth == b.depth && a.root < b.root)) xs init
  change xs.foldl c1g0_deeper init = init ∨ xs.foldl c1g0_deeper init ∈ xs at hmem
  have hcompat : Block.Compatible (xs.foldl c1g0_deeper init) B := by
    rcases hmem with he | hm
    · rw [he]; exact hinit
    · exact hxs _ hm
  rcases Bool.or_eq_true_iff.mp hcompat with h | h
  · have he := prefix_eq_of_depth _ _ h hdepth
    rw [he]
    exact block_preceq_refl _
  · exact h


private theorem c1g0_liveRoot_of_lease (p : Params) (st : State p.n) {B : Block}
    (hBS : Block.Preceq B st.base.stableRecord)
    (hbelow : LeaseBelowOutputStore p st) {dl : Time}
    (hlease : FGSA.leaseOf st B = some dl) (hlive : st.base.now < dl)
    (hdom : ∃ β ∈ FGSA.fullTree p st, eraseFG β = B) :
    Block.Preceq B (FGSA.liveRoot p st) := by
  obtain ⟨β, hβ, hβB⟩ := hdom
  have hZB : Block.Preceq (eraseFG (FGSA.controls p st).Z) B := by
    rw [← hβB]
    exact eraseFG_preceq
      ((KitFG.mem_filteredFromView (heightView p) _ _ β).mp hβ).2.2.1
  obtain ⟨row, hfind, hdl⟩ := Option.map_eq_some_iff.mp hlease
  have hrow := List.mem_of_find?_eq_some hfind
  have hp := List.find?_some hfind
  have hkey : row.1 = B := beq_iff_eq.mp hp
  let targets := st.base.obligations.filterMap (fun row =>
    if st.base.now < row.2.2 && decide (∃ β ∈ FGSA.fullTree p st, eraseFG β = row.1)
    then some row.1 else none)
  have hBm : B ∈ targets := by
    apply List.mem_filterMap.mpr
    refine ⟨row, hrow, ?_⟩
    have htime : st.base.now < row.2.2 := hdl ▸ hlive
    have hdB : ∃ β ∈ FGSA.fullTree p st, eraseFG β = B := ⟨β, hβ, hβB⟩
    simp only [htime, decide_true, hkey, hdB, Bool.and_self, ite_true]
  change Block.Preceq B (targets.foldl c1g0_deeper (eraseFG (FGSA.controls p st).Z))
  apply c1g0_fold_covers targets _ B hBm
  · exact block_compatible_of_common hZB (block_preceq_refl B)
  · intro b hb
    obtain ⟨row, hr, he⟩ := List.mem_filterMap.mp hb
    split at he
    · next hc =>
      have hl := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
      have hbe : row.1 = b := Option.some.inj he
      rw [← hbe]
      exact block_compatible_of_common (hbelow row hr hl) hBS
    · cases he


private theorem c1g0_source_head (p : Params) (st : State p.n)
    (hReach : Reachable p st) {C H : FGBlock (Fin p.n)}
    (hC : FGSA.fgSource p st = some C) (hH : fgBlockOf st (fgHead p st) = some H) :
    FGBlock.Preceq C H := by
  have hmem := Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ hC).1
  have hguard := Bool.and_eq_true_iff.mp hmem.2
  have hlive := hguard.2
  cases hl : leaseOf st (eraseFG C) with
  | none => simp only [hl, Bool.false_eq_true] at hlive
  | some dl =>
    simp only [hl, decide_eq_true_eq] at hlive
    have hbelow := leaseBelowOutputStore_of_reachable p st hReach
    obtain ⟨row, hfind, hdl⟩ := Option.map_eq_some_iff.mp hl
    have hp := List.find?_some hfind
    have hkey : row.1 = eraseFG C := beq_iff_eq.mp hp
    have hCS : Block.Preceq (eraseFG C) st.base.stableRecord := by
      rw [← hkey]
      exact hbelow row (List.mem_of_find?_eq_some hfind) (hdl ▸ hlive)
    have hroot := c1g0_liveRoot_of_lease p st hCS hbelow hl hlive ⟨C, hmem.1, rfl⟩
    have hhead : Block.Preceq (liveRoot p st) (fgHead p st) :=
      liveRoot_preceq_headInTree p st _ _ _
    have hHe := ((fgBlockOf_spec p st (storeBundle_of_reachable p st hReach).cstore
      (fgHead p st) H).mp hH).2
    exact eraseFG_preceq_iff.mp (hHe ▸ block_preceq_trans hroot hhead)

private theorem c1g0_selection_laws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGSelectionLaws (fgsaCoreReads p c) (c1g0_observations p c)
      (c1g0_selection p c) (fun nd => Reachable p nd.st) (Window.headFields p p.K_W) where
  source_eq _ _ := by rw [fgsaCoreReads_def]; rfl
  head_eq _ _ := by rw [fgsaCoreReads_def]; rfl
  head_held nd hReach := by
    have hinv := (storeBundle_of_reachable p nd.st hReach).cstore
    obtain ⟨H, hm, he⟩ := (hinv.baseTree _).mp (fgHead_stored p nd.st hinv)
    refine ⟨H, (fgBlockOf_spec p nd.st hinv _ H).mpr ⟨hm, he⟩, ?_⟩
    simpa only [fgsaCoreReads_def] using hm
  source_viable nd C _ hC := by
    change C ∈ domainR p nd.st ((fgsaCoreReads p c).core nd).fg.TF
    rw [fgsaCoreReads_def]
    exact (Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ hC).1).1
  source_head nd C H hReach he := by
    exact c1g0_source_head p nd.st hReach (congrArg Prod.fst he) (congrArg Prod.snd he)
  client_eq nd H _ hH := by
    change (fgSource p nd.st, _) = (fgSource p nd.st, Window.headFields p p.K_W H)
    change fgBlockOf nd.st (fgHead p nd.st) = some H at hH
    simp only [hH]

private theorem c1g0_action_selection_laws (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hvalid : V2.D.ExecutionValid E rho) :
    FGCompose.FGActionSelectionLaws E rho (c1g0_selection p c) p.actionTime
      (fun x r _ => x ∈ rho.honest ∧ E.awake x (p.actionTime r) = true)
      (fun _ _ nd => joinedNow p nd.st = true) where
  nonempty_joined x r nd C hread _ hC := by
    obtain ⟨pre, hpre, rfl⟩ := Option.map_eq_some_iff.mp hread
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hpre
    have ht := V2.D.Run.tickIdx?_spec hi
    cases hj : joinedNow p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
        (p.actionTime r)).st with
    | true => rfl
    | false =>
      have hn := fgsa_fgAction_unjoined_source_none E rho hvalid ht hj
      change FGSA.fgSource p _ = some C at hC
      rw [hn] at hC
      cases hC


open WeakContinuationWitness WitnessPositive

private theorem c1g0_real_nonempty : ∃ nd C H,
    postClock strongEnv source 0 (params.actionTime 1) = some nd ∧
    (c1g0_selection params unitCodec).select nd = (some C, some H) ∧
    H ∈ nd.st.fg.TF ∧ FGBlock.Preceq C H ∧
    (fgsaSafetyReads params unitCodec).inputs nd =
      (some C, Window.headFields params params.K_W H) ∧ joinedNow params nd.st = true := by
  have hrow : HonestRowAt params unitCodec strongEnv source 132 0 1 firstRow :=
    ⟨positive_signer_honest.1, positive_source_row.1, positive_source_row.2⟩
  obtain ⟨entry, hentry⟩ :=
    sourceDiscipline_emittedNonempty params unitCodec strongEnv source hrow
  obtain ⟨C, _, hsource, _⟩ := sourceDiscipline_emittedName params unitCodec strongEnv source
    witness_source_schedule hrow hentry
  obtain ⟨nd, hread, hC⟩ := Option.map_eq_some_iff.mp hsource
  obtain ⟨i, _, he⟩ := FGCompose.postClock_tick strongEnv source hread
  have hReach : Reachable params nd.st :=
    he ▸ reachable_postClock strongEnv source i 0 (params.actionTime 1)
  have laws := c1g0_selection_laws params unitCodec
  obtain ⟨H, hH, hm⟩ := laws.head_held nd hReach
  have hp : (c1g0_selection params unitCodec).select nd = (some C, some H) :=
    Prod.ext hC hH
  have hc := laws.client_eq nd H hReach hH
  have hj := (c1g0_action_selection_laws params unitCodec strongEnv source
    w1_source_execution).nonempty_joined 0 1 nd C hread
      ⟨positive_signer_honest.1, by decide⟩ hC
  have hc' : fgInputs params nd.st = (some C, Window.headFields params params.K_W H) := by
    change fgInputs params nd.st = (fgSource params nd.st, _) at hc
    rw [hC] at hc
    exact hc
  exact ⟨nd, C, H, hread, hp, by simpa only [fgsaCoreReads_def] using hm,
    laws.source_head nd C H hReach hp, by simpa only [fgsaSafetyReads_def] using hc', hj⟩

private theorem c1g0_fresh_gate : ∃ nd C i,
    source.events[i]? = some (.tick 0 (params.actionTime 1)) ∧
    (fgsa params unitCodec).clock (V2.D.Run.stateBefore strongEnv source i 0)
      (params.actionTime 1) = nd ∧ FGSA.fgSource params nd.st = some C ∧
    eraseFG C ∈ (fastWriteAt nd.st (1 * params.R)).getD [] ∧
    GridCO.savedGenuine (V2.D.Run.stateBefore strongEnv source i 0).st.base
      (1 * params.R) = none ∧ joinedNow params nd.st = true := by
  obtain ⟨nd, C, H, hread, hp, _, _, _, hj⟩ := c1g0_real_nonempty
  obtain ⟨i, hi, he⟩ := FGCompose.postClock_tick strongEnv source hread
  have hC : FGSA.fgSource params nd.st = some C := congrArg Prod.fst hp
  have hguard := Bool.and_eq_true_iff.mp
    (Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ hC).1).2
  have hmem := of_decide_eq_true hguard.1
  have hround : params.round (nd.st.slot params) = 1 := by
    rw [← he]
    exact (fgsa_action_slot_round (c := unitCodec)
      (V2.D.Run.stateBefore strongEnv source i 0) 1).2
  rw [hround] at hmem
  exact ⟨nd, C, i, hi, he, hC, hmem,
    fgsa_gate_fresh strongEnv source witness_source_schedule hi, hj⟩

private theorem c1g0_actual_client :
    FGCompose.FGSelectionClientLaws (c1g0_selection params unitCodec)
      (fgsaSafetyReads params unitCodec) := ⟨fun _ => by rw [fgsaSafetyReads_def]; rfl⟩

private theorem c1g0_actual_rows :
    let S := fgsaSafetyReads params unitCodec
    let Q := c1g0_selection params unitCodec
    let pre := V2.D.Run.stateBefore strongEnv source 132 0
    ((V2.D.tick strongEnv source pre 0 14).2.filter
      (fgsa params unitCodec).objSelfVisible).filterMap S.decodeObject =
      if strongEnv.awake 0 14 = true ∧ S.enabled 14 = true then
        (createRowOnce params.E params.cfg (S.record pre)
          ((Equiv.refl (Fin params.n)).symm (0 : Validator))
          (Q.clientInputs ((fgsa params unitCodec).clock pre 14)).1
          (Q.clientInputs ((fgsa params unitCodec).clock pre 14)).2).1.toList
      else [] := by
  exact FGCompose.selection_tick_rows (fgsaSafetyReads params unitCodec)
    (c1g0_selection params unitCodec) strongEnv source params.E params.cfg
    c1g0_actual_client (fgsaSafetyClientLaws params unitCodec) (Equiv.refl _)
    (fun _ => by rw [fgsaSafetyReads_def]; rfl) _ 0 14

private theorem c1g0_decoded_emission :
    firstRow.toRow? = some ⟨⟨0, params.nPos⟩, .vote 1 genesisRoot false, none⟩ ∧
    ofRow params firstRow ∈ V2.D.Run.emitsAt strongEnv source 132 :=
  ⟨rfl, positive_source_row.2⟩

-- Changing only the restart marker leaves an internal source but removes joining.
-- Such a state cannot be an actual valid action read with that source.
private theorem c1g0_stale_unjoined_control : ∃ nd C,
    FGSA.fgSource params nd.st = some C ∧ joinedNow params nd.st = false ∧
    ¬ ∃ (E : Generic.Env Validator) (rho : V2.D.Run Validator (fgsa params unitCodec)) (i : Nat),
      V2.D.ExecutionValid E rho ∧
      rho.events[i]? = some (.tick 0 (params.actionTime 1)) ∧
      (fgsa params unitCodec).clock (V2.D.Run.stateBefore E rho i 0)
        (params.actionTime 1) = nd := by
  obtain ⟨nd, C, H, hread, hp, _, _, _, _⟩ := c1g0_real_nonempty
  obtain ⟨i, _, he⟩ := FGCompose.postClock_tick strongEnv source hread
  have hn : nd.st.base.now = 14 := by
    rw [← he]
    exact (fgsa_postClock_slot (c := unitCodec)
      (V2.D.Run.stateBefore strongEnv source i 0) _).1
  let stale : Node params := { nd with st := { nd.st with restartTime := some 14 } }
  have hC : FGSA.fgSource params stale.st = some C := congrArg Prod.fst hp
  have hj : joinedNow params stale.st = false := by
    change decide (14 ≤ 4 * params.Δ * ((params.slotOf nd.st.base.now : Int) - 1)) = false
    rw [hn]
    rfl
  refine ⟨stale, C, hC, hj, ?_⟩
  rintro ⟨E, rho, j, hv, ht, heq⟩
  have hnone := fgsa_fgAction_unjoined_source_none E rho hv ht (heq ▸ hj)
  rw [heq, hC] at hnone
  cases hnone

private def c1g0_pool_head (s : Slot) : Obj params :=
  ⟨.seat (.base (.head s)) ⟨0, params.nPos⟩, .head genesisRoot⟩

private def c1g0_pool_trace : V2.D.Run Validator (fgsa params unitCodec) :=
  runData 14 [.tick 0 13, .deliver 0 (c1g0_pool_head 2) 13,
    .deliver 0 (c1g0_pool_head 3) 13, .tick 0 14]

private def c1g0_pool_node : Node params :=
  (fgsa params unitCodec).clock (V2.D.Run.stateBefore strongEnv c1g0_pool_trace 3 0) 14

private def c1g0_grid_head (s : Slot) : GridCO.Wire params.n .root :=
  ⟨.seat s ⟨0, params.nPos⟩, .head genesisRoot⟩

private theorem c1g0_distinct_pools :
    GridCO.votesAt c1g0_pool_node.st.base 2 = [c1g0_grid_head 2] ∧
    GridCO.votesAt c1g0_pool_node.st.base 3 = [c1g0_grid_head 3] ∧
    [c1g0_grid_head 2] ≠ [c1g0_grid_head 3] := by decide +kernel

private theorem c1g0_actual_pool_read :
    postClock strongEnv c1g0_pool_trace 0 (params.actionTime 1) = some c1g0_pool_node := rfl

private theorem c1g0_pool_walk :
    FGSA.fgHead params c1g0_pool_node.st = FGSA.getHead params c1g0_pool_node.st
      [c1g0_grid_head 3] [c1g0_grid_head 3] := by
  have h := (rowsPrem_action_pools params unitCodec strongEnv c1g0_pool_trace
    1 0 c1g0_pool_node c1g0_actual_pool_read).2
  have hs : ([c1g0_grid_head 3].filter (fun o =>
      match GridCO.resolvedHead? (FGSA.actView c1g0_pool_node.st) o with
      | some H => decide (H.slot ≤ 3)
      | none => false)) = [c1g0_grid_head 3] := by decide +kernel
  change FGSA.fgHead params c1g0_pool_node.st = FGSA.getHead params c1g0_pool_node.st
    (GridCO.votesAt c1g0_pool_node.st.base 3)
    ((GridCO.votesAt c1g0_pool_node.st.base 3).filter (fun o =>
      match GridCO.resolvedHead? (FGSA.actView c1g0_pool_node.st) o with
      | some H => decide (H.slot ≤ 3)
      | none => false)) at h
  rw [c1g0_distinct_pools.2.1, hs] at h
  exact h

#print axioms c1g0_source_head
#print axioms c1g0_action_selection_laws
#print axioms c1g0_fresh_gate
#print axioms c1g0_real_nonempty
#print axioms c1g0_actual_client
#print axioms c1g0_actual_rows
#print axioms c1g0_decoded_emission
#print axioms c1g0_stale_unjoined_control
#print axioms c1g0_distinct_pools
#print axioms c1g0_pool_walk

end AvailableChain.FGSA.Run.Tests.P0c1
end
