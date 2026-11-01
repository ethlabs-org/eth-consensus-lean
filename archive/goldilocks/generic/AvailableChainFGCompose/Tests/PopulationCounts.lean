module
public import AvailableChainFGCompose.Proofs.Population.Seats

set_option linter.privateModule false

noncomputable section
public section

/-! Pure seat/count controls. No execution or client producer is claimed here. -/
namespace AvailableChain.FGCompose.Tests.PopulationCounts
open AvailableChain.SimplexFG AvailableChain.KitFG

private abbrev protocol (n : Nat) : V2.ProtocolSpecD Unit where
  State := Unit
  Label := Unit
  Duty := Empty
  signLabel := Empty.elim
  seats := fun _ => n
  Payload := Unit
  Durable := Unit
  init := ()
  clock := fun st _ => st
  actTime := Empty.elim
  duties := fun _ => []
  duties_spec := by intro d; cases d
  duties_nodup := fun _ => List.nodup_nil
  act := fun _ d _ => Empty.elim d
  gossip := fun _ _ => []
  process := fun st _ => st
  selfVisible := fun _ => true
  recordOwn := fun st _ => st
  durable := id
  restore := fun st _ => st
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False
private abbrev reads (n : Nat) : FGSafetyReads (protocol n) n Unit where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode := fun _ => ⟨.none, ()⟩
  decode := fun _ => none
  decodeObject := fun _ => none
  fgLabel := ()
  fgSeats := Equiv.refl _
  record := fun _ => RecordOnce.initial
  inputs := fun _ => (none, ⟨0, genesisRoot, 0⟩)
  enabled := fun _ => true
  finalizedOut := fun _ => .genesis
private abbrev run {V : Type} (n : Nat) (holder : Fin n → V) (honest : Finset V) :
    V2.D.Run V (protocol n) where
  honest := honest
  horizon := 20
  events := []
  seatOf := fun _ => holder
  input := fun _ _ => ()
private abbrev electorate (n : Nat) : Electorate (Fin n) :=
  ⟨fun _ => 1, fun _ => by decide⟩
private abbrev before := run 1 (fun _ => (9 : Fin 11)) {7, 9}
private abbrev extra := run 1 (fun _ => (9 : Fin 12)) {7, 9}
private abbrev faultySeat := run 1 (fun _ => (11 : Fin 12)) {7, 9}
private abbrev four := run 4 (fun i => i.val + 9) {7, 9, 10}
private abbrev frozen := run 4 (fun i : Fin 4 => i) {0, 1, 2}

private theorem counts_premises_sat :
    before.honest = {7, 9} ∧ extra.honest = {7, 9} ∧
    faultySeat.honest = {7, 9} ∧ four.honest = {7, 9, 10} ∧
    Function.Injective (safetyHolder (reads 4) four) ∧
    FGSafetyUnitLaws (electorate 4) ∧
    (∀ i, safetyHolder (reads 4) frozen i = (Equiv.refl (Fin 4)) i) ∧
    (Gen.V2.Duty.faulty frozen).card ≤ (4 - 1) / 3 := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, fun _ => rfl, by decide⟩
  · intro i j h
    apply Fin.ext
    change i.val + 9 = j.val + 9 at h
    omega
  · exact ⟨by decide, by decide, fun A => by simp [Electorate.weightOf], by decide⟩

private theorem node_faults_do_not_count_seats :
    (Gen.V2.Duty.faulty before).card = 9 ∧ (Gen.V2.Duty.faulty extra).card = 10 ∧
    historyFaulty (reads 1) before = ∅ ∧ historyFaulty (reads 1) extra = ∅ ∧
    historyFaulty (reads 1) faultySeat = {0} := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩ <;>
    ext i <;> have hi : i = 0 := Subsingleton.elim _ _
  all_goals subst i; simp [historyFaulty, safetyHolder]

/-- Two faults are below q=3, but leave only two honest votes. -/
private theorem fault_weight_not_honest_quorum :
    (electorate 4).weightOf (historyFaulty (reads 4) four) < (electorate 4).q ∧
    ¬ (electorate 4).IsQuorum (FGHonestSeats (reads 4) four) := by
  have hF : historyFaulty (reads 4) four = {2, 3} := by
    ext i
    simp only [historyFaulty, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases i with ⟨i, hi⟩
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> decide +revert
  have hH : FGHonestSeats (reads 4) four = {0, 1} := by
    ext i
    simp only [FGHonestSeats_def, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases i with ⟨i, hi⟩
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> decide +revert
  rw [hF, hH]
  change 2 < 3 ∧ ¬ 3 ≤ 2
  decide

private theorem all_holders_count_bridge :
    (historyFaulty (reads 4) frozen).card = (Gen.V2.Duty.faulty frozen).card ∧
    (electorate 4).IsQuorum (FGHonestSeats (reads 4) frozen) ∧
    FGHonestSeats (reads 4) frozen = (historyFaulty (reads 4) frozen)ᶜ := by
  have he := counts_premises_sat.2.2.2.2.2.2.1
  have hc := fg_fault_count_eq_nodes_of_equiv (reads 4) frozen (Equiv.refl _) he
  exact ⟨hc, high_target_honest_quorum_holder (reads 4) frozen (electorate 4)
    counts_premises_sat.2.2.2.2.2.1 (hc ▸ counts_premises_sat.2.2.2.2.2.2.2),
    fgHonestSeats_eq_compl (reads 4) frozen⟩

private theorem duplicate_holder_rejected :
    ¬ Function.Injective (fun _ : Fin 2 => (9 : Nat)) := by
  intro h
  have he : (0 : Fin 2) = 1 := h rfl
  exact (by decide : (0 : Fin 2) ≠ 1) he

#print axioms counts_premises_sat
#print axioms node_faults_do_not_count_seats
#print axioms fault_weight_not_honest_quorum
#print axioms all_holders_count_bridge
#print axioms duplicate_holder_rejected

end AvailableChain.FGCompose.Tests.PopulationCounts
end
