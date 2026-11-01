module
public import AvailableChainFGCompose.Proofs.Restart
public import AvailableChainFGCompose.Proofs.SafetyCount -- shake: keep (axioms)

set_option linter.privateModule false

public section

namespace AvailableChain.FGCompose.Tests.RestartKeep
open AvailableChain.SimplexFG

private theorem rows_nil (rs : List (Row (Fin 0))) : rs = [] := by
  cases rs with
  | nil => rfl
  | cons row _ => exact Fin.elim0 row.signer

private def erase : FGBlock (Fin 0) → Block
  | .genesis => .genesis
  | .node p s r x _ => .node (erase p) s r x

private theorem erase_inj : Function.Injective erase := by
  intro A
  induction A with
  | genesis => intro B h; cases B <;> simp [erase] at h ⊢
  | node p s r x rs ih =>
    intro B h
    cases B with
    | genesis => simp [erase] at h
    | node p' s' r' x' rs' =>
      simp only [erase, Block.node.injEq] at h
      obtain ⟨hp, hs, hr, hx⟩ := h
      have hpp := ih hp
      subst p' s' r' x'
      rw [rows_nil rs, rows_nil rs']

-- An interface model. It is not an ExecutionValid protocol fixture.
-- The volatile flag changes at restart; the held non-genesis block remains.
private abbrev protocol : V2.ProtocolSpecD Unit where
  State := Bool
  Label := Unit
  Duty := Empty
  signLabel := Empty.elim
  seats := fun _ => 1
  Payload := Unit
  Durable := Unit
  init := true
  clock := fun st _ => st
  actTime := Empty.elim
  duties := fun _ => []
  duties_spec := by intro d; cases d
  duties_nodup := by intro t; exact List.nodup_nil
  act := fun _ d _ => Empty.elim d
  gossip := fun _ _ => []
  process := fun st _ => st
  selfVisible := fun _ => false
  recordOwn := fun st _ => st
  durable := fun _ => ()
  restore := fun _ _ => false
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

private def held : FGBlock (Fin 0) := .node .genesis 1 ⟨1⟩ 0 []

private noncomputable abbrev reads : FGCoreReads protocol 0 Unit Unit Unit where
  core _ := ⟨(), ⟨{.genesis, held}, .genesis, .genesis, 0, 1⟩, [], []⟩
  erase := erase
  source := fun _ => some held
  headVote := fun _ _ => erase held
  finalityHead := fun _ => none
  proposalFG := fun _ _ => none

private theorem core_laws : FGCoreLaws reads where
  clock_fg _ _ := rfl
  clock_proposals _ _ := rfl
  clock_rowPool _ _ := rfl
  process_tf _ _ := fun _ h => h
  process_proposals _ _ := List.prefix_rfl
  process_rowPool _ _ := List.prefix_rfl
  own_core _ _ := rfl
  source_mem _ _ h := by cases Option.some.inj h; simp
  erase_inj := erase_inj

private theorem restore_laws : FGTreeRestoreLaws reads := ⟨fun _ _ => rfl⟩
private theorem keep_laws : FGTreeKeepLaws reads := ⟨fun _ _ => Finset.Subset.refl _⟩

private abbrev env : Generic.Env Unit where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ _ => false

private noncomputable abbrev trace : V2.D.Run Unit protocol where
  honest := {()}
  horizon := 1
  events := [.restart () 1, .tick () 1]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

private theorem schedule : V2.D.ScheduleWellFormed env trace where
  horizon_nonneg := by decide
  sorted := by decide
  nodup := by decide
  in_horizon := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> norm_num [V2.Event.time]
  honest_only := by intro e he; simp
  tick_public := by
    intro v t ht
    have ht' : t = 1 := by simpa using ht
    subst t
    exact ⟨1, by norm_num⟩
  tick_total := by intro v hv t ht hn hh ha; cases ha

private theorem retained_tree : TFAt reads env trace 0 () ⊆ TFAt reads env trace 2 () :=
  tf_cumulative_all reads env trace core_laws keep_laws (by decide) ()

private theorem retained_block : held ∈ TFAt reads env trace 2 () := by
  apply retained_tree
  change held ∈ ({.genesis, held} : Finset (FGBlock (Fin 0)))
  simp

private theorem equal_time_tree :
    TFAt reads env trace 1 () = (reads.core (V2.D.Run.stateBeforeTime env trace 1 ())).fg.TF :=
  tf_before_tick_eq_beforeTime reads env trace schedule restore_laws rfl

private theorem equal_time_state_differs :
    V2.D.Run.stateBefore env trace 1 () ≠ V2.D.Run.stateBeforeTime env trace 1 () := by
  decide

private theorem head_laws : FGHeadLaws reads env trace where
  head_mem _ _ _ _ := ⟨held, by simp, rfl⟩
  parent_closed _ _ B hB := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hB ⊢
    rcases hB with rfl | rfl <;> simp [held, FGBlock.parent]

private theorem retained_head : held ∈ TFAt reads env trace 2 () :=
  head_held_from_all reads env trace core_laws head_laws schedule keep_laws
    (s := 1) (t := 1) (by decide) 2 1 le_rfl (by decide)

private theorem strict_chain_read : ChainRowsBefore reads env trace held 2 :=
  chainRows_of_head_all reads env trace core_laws head_laws schedule restore_laws
    (x := ()) (by simp) (s := 1) (t := 1) (by decide) 2 (by norm_num)

-- A keep-only restore can add a block. It fails restore equality and tick/strict equality.
private noncomputable abbrev addingReads : FGCoreReads protocol 0 Unit Unit Unit :=
  { reads with core := fun st =>
      ⟨(), ⟨if st then {.genesis} else {.genesis, held}, .genesis, .genesis, 0, 1⟩, [], []⟩ }

private theorem adding_keep : FGTreeKeepLaws addingReads := by
  constructor
  intro st t B hB
  cases st <;> simp_all

private theorem adding_not_restore : ¬ FGTreeRestoreLaws addingReads := by
  intro h
  have he := h.restart_eq true 1
  have hm : held ∈ (addingReads.core (protocol.restore (protocol.durable true) 1)).fg.TF := by
    simp
  rw [he] at hm
  simp [held] at hm

private theorem adding_tick_not_strict :
    TFAt addingReads env trace 1 () ≠
      (addingReads.core (V2.D.Run.stateBeforeTime env trace 1 ())).fg.TF := by decide

-- Repeat Tests.Restart.restart_loses_tf with its original clearing-store behavior.
private noncomputable abbrev clearingReads : FGCoreReads protocol 0 Unit Unit Unit :=
  { reads with
    core := fun st => ⟨(), if st then Store.init else ⟨∅, .genesis, .genesis, 0, 1⟩, [], []⟩
    source := fun _ => none }

private theorem clearing_core_laws : FGCoreLaws clearingReads where
  clock_fg _ _ := rfl
  clock_proposals _ _ := rfl
  clock_rowPool _ _ := rfl
  process_tf _ _ := fun _ h => h
  process_proposals _ _ := List.prefix_rfl
  process_rowPool _ _ := List.prefix_rfl
  own_core _ _ := rfl
  source_mem _ _ h := by cases h
  erase_inj := erase_inj

private theorem restart_loses_tf :
    ¬ TFAt clearingReads env trace 0 () ⊆ TFAt clearingReads env trace 1 () := by
  intro h
  have hgen : (FGBlock.genesis : FGBlock (Fin 0)) ∈ TFAt clearingReads env trace 0 () := by
    decide
  have hlost := h hgen
  change (FGBlock.genesis : FGBlock (Fin 0)) ∈ (∅ : Finset (FGBlock (Fin 0))) at hlost
  simp at hlost

private theorem clearing_not_keep : ¬ FGTreeKeepLaws clearingReads := by
  intro K
  exact restart_loses_tf
    (tf_cumulative_all clearingReads env trace clearing_core_laws K (by decide) ())

#print axioms clearing_core_laws
#print axioms restart_loses_tf
#print axioms clearing_not_keep
#print axioms core_laws
#print axioms restore_laws
#print axioms keep_laws
#print axioms retained_tree
#print axioms retained_block
#print axioms equal_time_tree
#print axioms equal_time_state_differs
#print axioms retained_head
#print axioms strict_chain_read
#print axioms adding_keep
#print axioms adding_not_restore
#print axioms adding_tick_not_strict

end AvailableChain.FGCompose.Tests.RestartKeep
end
