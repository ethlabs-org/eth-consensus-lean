module
public import AvailableChainFGCompose.Statements.CoreReads
public section
namespace AvailableChain.FGCompose.Tests.Restart
open AvailableChain.SimplexFG

private theorem rows_nil (rs : List (Row (Fin 0))) : rs = [] := by
  cases rs with
  | nil => rfl
  | cons row _ => exact Fin.elim0 row.signer

def erase : FGBlock (Fin 0) → Block
  | .genesis => .genesis
  | .node p s r x _ => .node (erase p) s r x

theorem erase_inj : Function.Injective erase := by
  intro A
  induction A with
  | genesis =>
    intro B h
    cases B <;> simp [erase] at h ⊢
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

abbrev protocol : V2.ProtocolSpecD Unit where
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

abbrev reads : FGCoreReads protocol 0 Unit Unit Unit where
  core st := ⟨(), if st then Store.init else ⟨∅, .genesis, .genesis, 0, 1⟩, [], []⟩
  erase := erase
  source := fun _ => none
  headVote := fun _ _ => .genesis
  finalityHead := fun _ => none
  proposalFG := fun _ _ => none

theorem laws : FGCoreLaws reads where
  clock_fg _ _ := rfl
  clock_proposals _ _ := rfl
  clock_rowPool _ _ := rfl
  process_tf _ _ := fun _ h => h
  process_proposals _ _ := List.prefix_rfl
  process_rowPool _ _ := List.prefix_rfl
  own_core _ _ := rfl
  source_mem _ _ h := by cases h
  erase_inj := erase_inj

abbrev env : Generic.Env Unit where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ _ => false

abbrev trace : V2.D.Run Unit protocol where
  honest := {()}
  horizon := 1
  events := [.restart () 1]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

theorem restart_loses_tf :
    ¬ TFAt reads env trace 0 () ⊆ TFAt reads env trace 1 () := by
  intro h
  have hgen : (FGBlock.genesis : FGBlock (Fin 0)) ∈ TFAt reads env trace 0 () := by decide
  have hlost := h hgen
  change (FGBlock.genesis : FGBlock (Fin 0)) ∈ (∅ : Finset (FGBlock (Fin 0))) at hlost
  simp at hlost

example : ¬ V2.D.NoRestart trace := by
  intro h
  exact h 0 () 1 rfl

-- A source above the cap cannot satisfy the cap, even for a descendant.
example {n : Nat} (H : KitFG.FGHeightView (Fin n)) (C : FGBlock (Fin n)) (y : Nat)
    (hhigh : y + 1 < (H C).h) (hcap : (H C).h ≤ y + 1) : False :=
  Nat.not_lt_of_ge hcap hhigh

end AvailableChain.FGCompose.Tests.Restart
end
