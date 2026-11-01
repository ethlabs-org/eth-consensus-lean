module
public import AvailableChainKitFG.WindowHeightBridge
public import AvailableChainFGCompose.Proofs.Healing.CommonEntry
public import AvailableChainFGCompose.Proofs.Healing.PromotionArithmetic
public import AvailableChainFGCompose.Proofs.Healing.PromotionRows

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.P0d3
open AvailableChain.SimplexFG AvailableChain.KitFG

-- An inhabited interface trace. This is not an ExecutionValid protocol fixture.
private noncomputable abbrev d3_row : Row (Fin 1) :=
  ⟨0, .vote 1 genesisRoot false, some ⟨0, genesisRoot⟩⟩
private noncomputable abbrev d3_protocol : V2.ProtocolSpecD Unit where
  State := List (Row (Fin 1))
  Label := Nat
  Duty := Nat
  signLabel := id
  seats _ := 1
  Payload := Row (Fin 1)
  Durable := List (Row (Fin 1))
  init := []
  clock st _ := st
  actTime s := (s : Time)
  duties t := if 0 ≤ t then [t.toNat] else []
  duties_spec s t := by
    split
    · next ht =>
      simp only [List.mem_singleton]
      constructor
      · intro hs; subst s; exact Int.toNat_of_nonneg ht
      · intro hs; subst t; simp
    · next ht =>
      constructor
      · intro hm; cases hm
      · intro hs; exact False.elim (ht (hs ▸ Int.natCast_nonneg s))
  duties_nodup t := by split <;> simp
  act _ _ _ := none
  gossip _ _ := [d3_row]
  process st o := o.payload :: st
  selfVisible _ := false
  recordOwn st _ := st
  durable := id
  restore st _ := st
  wellFormed _ := true
  depsPresent _ _ := true
  processed _ _ := false
  excludes _ _ := false
  handles _ _ _ := False
  carries _ _ := False

private noncomputable abbrev d3_env : Generic.Env Unit :=
  ⟨1, by decide, 0, by decide, fun _ _ => true⟩
private noncomputable abbrev d3_trace : V2.D.Run Unit d3_protocol where
  honest := {()}
  horizon := 40
  events := [.tick () 6, .tick () 8, .deliver () ⟨.none, d3_row⟩ 8]
  seatOf _ _ := ()
  input _ _ := ()
private noncomputable abbrev d3_clock : FGTiming where
  delta := 1
  roundSlots := 2
  proposal s := 4 * (s : Time)
  vote s := 4 * (s : Time) + 1
  early s := 4 * (s : Time) + 2
  freeze s := 4 * (s : Time) + 3
  release s := 4 * (s : Time) + 5
  gate s := 4 * (s : Time) + 6
  action r := 8 * (r : Time) + 6
private theorem d3_clock_laws : FGTimingLaws d3_clock where
  delta_pos := by decide
  rounds := by decide
  proposal_eq _ := by simp
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq r := by dsimp; ring
private noncomputable abbrev d3_core : FGCoreReads d3_protocol 1 Unit Unit (Row (Fin 1)) where
  core st := ⟨(), ⟨{.genesis}, .genesis, .genesis, 0, 1⟩, [], st⟩
  erase _ := .genesis
  source _ := some .genesis
  headVote _ _ := .genesis
  finalityHead _ := some .genesis
  proposalFG _ _ := none
private noncomputable abbrev d3_safety : FGSafetyReads d3_protocol 1 (Row (Fin 1)) where
  proposalErase _ := none
  proposalRows _ := []
  encode a := ⟨.none, a⟩
  decode := some
  decodeObject o := some o.payload
  fgLabel := 0
  fgSeats := Equiv.refl _
  record _ := RecordOnce.initial
  inputs _ := (some .genesis, ⟨0, genesisRoot, 0⟩)
  enabled _ := true
  finalizedOut _ := .genesis
private noncomputable abbrev d3_height : FGHeightView (Fin 1) :=
  fun _ => ⟨.genesis, 0, 1, .genesis, ∅, ∅, 0, .genesis⟩
private noncomputable abbrev d3_electorate : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private theorem d3_height_laws : FGHeightLaws d3_electorate d3_height where
  one_le_h _ := by change 1 ≤ (1 : Nat); decide
  h_mono _ := le_rfl
  node_cases _ _ _ _ _ := Or.inl ⟨rfl, rfl⟩
  entry_preceq B := genesis_preceq B
  entry_same_height _ := rfl
  entry_idem _ := rfl
  entry_plateau _ _ := rfl
  justified_preceq_entry _ := preceq_refl _
  justified_below_height _ := by change 0 < (1 : Nat); decide
  target_sub_progress _ := Finset.Subset.refl _
  target_origin _ _ hi := False.elim (Finset.notMem_empty _ hi)
  progress_origin _ _ hi := False.elim (Finset.notMem_empty _ hi)
  height_crossing _ y hy hlo := by
    change y < 1 at hlo
    exact ((Nat.not_lt_of_ge hy) hlo).elim
  justification_certificate _ hn := False.elim (hn rfl)

private theorem d3_source :
    actionSourceFG d3_core d3_env d3_trace d3_clock () 0 = some (some .genesis) := by
  decide +kernel
private theorem d3_sent : HonestRowAt d3_safety d3_env d3_trace d3_clock 0 () 0 d3_row := by
  refine ⟨by decide +kernel, rfl, ?_⟩
  change (⟨.none, d3_row⟩ : d3_protocol.Object) ∈ [⟨.none, d3_row⟩]
  exact List.mem_singleton_self _
private theorem d3_sources : ∀ x K, x ∈ d3_trace.honest →
    actionSourceFG d3_core d3_env d3_trace d3_clock x 0 = some (some K) →
    FGBlock.Preceq .genesis K ∧ (d3_height K).h ≤ 1 := by
  intro x K _ _
  exact ⟨genesis_preceq K, le_rfl⟩
private theorem d3_high_entry : OpeningEntry d3_core d3_env d3_trace d3_height d3_clock 0 1 :=
  common_entry_at_high d3_core d3_env d3_trace d3_height d3_clock
    d3_electorate d3_height_laws d3_sources rfl
private theorem d3_low_branch :
    OpeningEntry d3_core d3_env d3_trace d3_height d3_clock 0 (2 - 1) := by
  rcases common_low_or_high d3_core d3_env d3_trace d3_height d3_clock
      d3_electorate d3_height_laws 0 2 .genesis rfl
      (fun x K hx hK => ⟨(d3_sources x K hx hK).1, by change 1 ≤ (2 : Nat); decide⟩) with low | high
  · exact low
  · obtain ⟨x, K, _, _, hh⟩ := high
    change 1 = 2 at hh
    contradiction
private theorem d3_covered : OpeningCovered d3_core d3_safety d3_env d3_trace
    d3_height d3_clock Row.height_pair 0 .genesis := by
  intro x _
  cases x
  exact ⟨.genesis, [], 0, 0, d3_row, by decide +kernel, d3_source,
    by decide, by decide, le_rfl, d3_sent, rfl⟩
private theorem d3_fixed_batch : ∃ U, EntryAt d3_height U 1 ∧
    FixedRows d3_core d3_safety d3_env d3_trace d3_height d3_clock
      Row.height_pair 0 1 .genesis U := by
  apply healing_promotion_fixed_rows d3_core d3_safety d3_env d3_trace d3_height
    d3_clock Row.height_pair d3_electorate d3_height_laws
    (by simp) d3_high_entry d3_covered
  · intro x y K L hx hy hK hL he; rfl
  · intro x K hx hK
    cases x
    have he : K = .genesis := Option.some.inj (Option.some.inj (hK.symm.trans d3_source))
    subst K
    exact le_rfl

-- The fixed row retains its finality field; a different height pair cannot replace it.
private theorem d3_fixed_identity : NamesEntry Row.height_pair .progress d3_row 1
    (.genesis : FGBlock (Fin 1)) ∧ d3_row.finality_pair = some ⟨0, genesisRoot⟩ :=
  ⟨⟨false, rfl⟩, rfl⟩
private theorem d3_reject_replacement : ¬ NamesEntry Row.height_pair .progress
    ({d3_row with height_pair := .vote 2 genesisRoot false}) 1
      (.genesis : FGBlock (Fin 1)) := by
  rintro ⟨timeout, h⟩
  cases h
private theorem d3_reject_parent : ¬ FGBlock.Preceq
    (.node .genesis 1 ⟨7⟩ 0 [] : FGBlock (Fin 1)) .genesis := by decide

-- Delivery at the deadline is absent from the strict read; the next read holds that row.
private theorem d3_strict_receipt :
    ¬ HeldBefore d3_core d3_env d3_trace (fun _ => []) () d3_row 8 ∧
      HeldBefore d3_core d3_env d3_trace (fun _ => []) () d3_row 9 := by
  change ¬ (d3_row ∈ ([] : List (Row (Fin 1))) ∨ d3_row ∈ []) ∧
    (d3_row ∈ [d3_row] ∨ d3_row ∈ [])
  decide +kernel
private theorem d3_strict_deadline : PromotionRowDeadlineStrict d3_env d3_clock 1 0 0 4 :=
  healing_promotion_row_deadline_strict d3_clock d3_clock_laws d3_env
    (by decide) ⟨by decide⟩ (by decide) (by decide) (by decide)
private theorem d3_reject_deadline_equality : ¬ ((0 + 1 : Time) * FGCompose.P d3_clock <
    d3_clock.proposal 2) := by decide

private noncomputable abbrev d3_window : Window.State (Fin 1) :=
  { Window.initial with h := 3, W := [⟨1, .genesis, ∅⟩] }
private noncomputable abbrev d3_stale : Row (Fin 1) :=
  ⟨0, .vote 2 genesisRoot false, some ⟨1, genesisRoot⟩⟩
private theorem d3_finality_useful : Window.heightMatch d3_window d3_stale = false ∧
    Window.r6w d3_window d3_stale = true := by decide
private theorem d3_reject_finality_mismatch : Window.r6w d3_window
    ({d3_stale with finality_pair := some ⟨1, ⟨9⟩⟩}) = false := by decide

private noncomputable abbrev d3_interface : V2.D.Interface d3_protocol where
  confirmed _ := .genesis
  stable _ := .genesis
  block _ := some .genesis
  opening _ := True
  propLabel s := 4 * s
  propDuty s := 4 * s
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective := by
    intro a b h
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) h
private noncomputable abbrev d3_child : FGBlock (Fin 1) := .node .genesis 2 ⟨7⟩ 0 []
private noncomputable abbrev d3_parent (_ : List (Row (Fin 1))) (_ : Block) :=
  some (.genesis : FGBlock (Fin 1))
private noncomputable abbrev d3_parent_height (_ : List (Row (Fin 1))) (_ : Slot)
    (_ : FGBlock (Fin 1)) := (1, genesisRoot)
private noncomputable abbrev d3_valid (_ : List (Row (Fin 1))) (_ : Slot)
    (_ : FGBlock (Fin 1)) (a : Row (Fin 1)) := Window.r6w Window.initial a
private noncomputable abbrev d3_fold (_ : List (Row (Fin 1))) (_ : Slot)
    (_ : FGBlock (Fin 1)) : Window.State (Fin 1) := Window.initial
private theorem d3_parent_transfer :
    ValidForParent d3_env d3_trace d3_interface d3_parent d3_valid
      d3_child.slot (d3_core.erase d3_child) d3_row ∧
    HeightMatch d3_env d3_trace d3_interface (fun a => namedEntry a.height_pair)
      d3_parent d3_parent_height d3_child.slot (d3_core.erase d3_child) d3_row := by
  exact p0d3_same_row d3_core d3_safety d3_env d3_trace d3_height d3_interface
    Row.height_pair d3_parent d3_parent_height d3_valid d3_fold
    d3_electorate d3_height_laws (s := 2) (nd := []) (U := .genesis)
    rfl ⟨rfl, rfl⟩ (preceq_refl _) rfl (by decide +kernel) rfl ⟨rfl, rfl⟩ rfl
    ⟨d3_row, rfl, rfl⟩ ⟨false, rfl⟩ rfl

#print axioms d3_parent_transfer
#print axioms d3_height_laws
#print axioms d3_source
#print axioms d3_sent
#print axioms d3_high_entry
#print axioms d3_low_branch
#print axioms d3_fixed_batch
#print axioms d3_fixed_identity
#print axioms d3_reject_replacement
#print axioms d3_reject_parent
#print axioms d3_strict_receipt
#print axioms d3_strict_deadline
#print axioms d3_reject_deadline_equality
#print axioms d3_finality_useful
#print axioms d3_reject_finality_mismatch

-- Real window heights on a chain; two honest readers select different sources.
-- This fixture specifies interface reads. It does not assert ExecutionValid.
private noncomputable abbrev d3n_entry : FGBlock (Fin 1) :=
  .node .genesis 1 ⟨10⟩ 0 [⟨0, .vote 1 genesisRoot false, none⟩]
private noncomputable abbrev d3n_source2 : FGBlock (Fin 1) :=
  .node d3n_entry 2 ⟨11⟩ 0 []
private noncomputable abbrev d3n_parent_block : FGBlock (Fin 1) :=
  .node d3n_source2 3 ⟨12⟩ 0 []
private noncomputable abbrev d3n_child : FGBlock (Fin 1) :=
  .node d3n_parent_block 8 ⟨13⟩ 0 []
private noncomputable abbrev d3n_wrong : FGBlock (Fin 1) :=
  .node .genesis 3 ⟨19⟩ 0 []
private def d3n_erase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node P s root body _ => .node (d3n_erase P) s root body
private noncomputable abbrev d3n_row : Row (Fin 1) :=
  ⟨0, .vote 2 d3n_entry.root false, some ⟨0, genesisRoot⟩⟩
private noncomputable abbrev d3n_later : Row (Fin 1) :=
  { d3n_row with finality_pair := some ⟨1, ⟨99⟩⟩ }
private noncomputable abbrev d3n_protocol : V2.ProtocolSpecD Unit :=
  { d3_protocol with gossip := fun _ t => if t < 22 then [d3n_row] else [d3n_later] }
private noncomputable abbrev d3n_env : Generic.Env Bool :=
  ⟨1, by decide, 0, by decide, fun _ _ => true⟩
private noncomputable abbrev d3n_trace : V2.D.Run Bool d3n_protocol where
  honest := {false, true}
  horizon := 40
  events := [.deliver true ⟨.none, d3_row⟩ 1, .tick false 14, .tick true 14,
    .deliver false ⟨.none, d3_row⟩ 16, .tick false 22, .tick true 22, .tick false 32]
  seatOf _ _ := false
  input _ _ := ()
private noncomputable abbrev d3n_core :
    FGCoreReads d3n_protocol 1 Unit Unit (Row (Fin 1)) where
  core st := ⟨(), ⟨{.genesis, d3n_entry, d3n_source2, d3n_parent_block},
    .genesis, .genesis, 0, 2⟩, [], st⟩
  erase := d3n_erase
  source st := some (if st = [] then d3n_entry else d3n_source2)
  headVote _ _ := d3n_erase d3n_parent_block
  finalityHead _ := some d3n_parent_block
  proposalFG _ _ := some d3n_child
private noncomputable abbrev d3n_safety : FGSafetyReads d3n_protocol 1 (Row (Fin 1)) where
  proposalErase _ := none
  proposalRows _ := []
  encode a := ⟨.none, a⟩
  decode := some
  decodeObject o := some o.payload
  fgLabel := 0
  fgSeats := Equiv.refl _
  record _ := RecordOnce.initial
  inputs _ := (some .genesis, ⟨0, genesisRoot, 0⟩)
  enabled _ := true
  finalizedOut _ := .genesis
private noncomputable abbrev d3n_height : FGHeightView (Fin 1) :=
  fun B => Window.projectHeight (Window.derive d3_electorate ⟨0⟩ 2 B)
private theorem d3n_height_laws : FGHeightLaws d3_electorate d3n_height :=
  Window.windowHeightLaws d3_electorate ⟨0⟩ 2 (by decide)
private noncomputable abbrev d3n_selected (x : Bool) : FGBlock (Fin 1) :=
  if x then d3n_source2 else d3n_entry
private theorem d3n_sources (x : Bool) :
    actionSourceFG d3n_core d3n_env d3n_trace d3_clock x 1 =
      some (some (d3n_selected x)) := by cases x <;> decide +kernel
private theorem d3n_next_sources (x : Bool) :
    actionSourceFG d3n_core d3n_env d3n_trace d3_clock x 2 =
      some (some d3n_source2) := by cases x <;> decide +kernel
private theorem d3n_source_eq {x : Bool} {K : FGBlock (Fin 1)}
    (hK : actionSourceFG d3n_core d3n_env d3n_trace d3_clock x 1 = some (some K)) :
    K = d3n_selected x := Option.some.inj (Option.some.inj (hK.symm.trans (d3n_sources x)))
private theorem d3n_geometry : d3n_entry ≠ .genesis ∧ d3n_entry ≠ d3n_source2 ∧
    FGBlock.Preceq d3n_entry d3n_source2 ∧
    FGBlock.Preceq d3n_source2 d3n_parent_block ∧
    d3n_parent_block ≠ d3n_source2 ∧ EntryAt d3n_height d3n_entry 2 := by
  unfold EntryAt
  decide +kernel
private theorem d3n_caps : ∀ x K, x ∈ d3n_trace.honest →
    actionSourceFG d3n_core d3n_env d3n_trace d3_clock x 1 = some (some K) →
    FGBlock.Preceq d3n_entry K ∧ (d3n_height K).h ≤ 2 := by
  intro x K _ hK
  rw [d3n_source_eq hK]
  cases x <;> decide +kernel
private theorem d3n_opening : OpeningEntry d3n_core d3n_env d3n_trace d3n_height
    d3_clock 1 2 := common_entry_at_high d3n_core d3n_env d3n_trace d3n_height
      d3_clock d3_electorate d3n_height_laws d3n_caps (by decide +kernel)
private theorem d3n_low_arm : OpeningEntry d3n_core d3n_env d3n_trace d3n_height
    d3_clock 1 (3 - 1) := by
  rcases common_low_or_high d3n_core d3n_env d3n_trace d3n_height d3_clock
      d3_electorate d3n_height_laws 1 3 d3n_entry (by decide +kernel)
      (fun x K hx hK => ⟨(d3n_caps x K hx hK).1, (d3n_caps x K hx hK).2.trans
        (by decide)⟩) with low | high
  · exact low
  · obtain ⟨x, K, _, hK, hh⟩ := high
    rw [d3n_source_eq hK] at hh
    cases x <;> change 2 = 3 at hh <;> contradiction
private theorem d3n_genesis_caps : ∀ x K, x ∈ d3n_trace.honest →
    actionSourceFG d3n_core d3n_env d3n_trace d3_clock x 1 = some (some K) →
    FGBlock.Preceq .genesis K ∧ (d3n_height K).h ≤ 2 :=
  fun x K hx hK => ⟨genesis_preceq K, (d3n_caps x K hx hK).2⟩
private theorem d3n_not_low : ¬ OpeningEntry d3n_core d3n_env d3n_trace d3n_height
    d3_clock 1 1 := by
  rintro ⟨e, he⟩
  have hh := (he false d3n_entry (by decide) (d3n_sources false)).1
  change 2 = 1 at hh
  contradiction
private theorem d3n_high_arm : ∃ x K, x ∈ d3n_trace.honest ∧
    actionSourceFG d3n_core d3n_env d3n_trace d3_clock x 1 = some (some K) ∧
    (d3n_height K).h = 2 := by
  rcases common_low_or_high d3n_core d3n_env d3n_trace d3n_height d3_clock
    d3_electorate d3n_height_laws 1 2 .genesis (by decide +kernel)
    d3n_genesis_caps with low | high
  · exact (d3n_not_low low).elim
  · exact high
private noncomputable abbrev d3n_obs : FGObservationReads d3n_core where
  height := d3n_height
  finality _ := ⟨.genesis, 0⟩
  controls _ := ⟨.genesis, 2, 0, .genesis, false⟩
  viable _ X := X
private theorem d3n_phase : PhaseInterval d3n_core d3n_env d3n_trace d3n_obs
    14 (d3_clock.action (1 + 1)) 2 none false := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro i x _ _ _
  exact ⟨rfl, rfl, rfl⟩
private theorem d3n_conditional_next : OpeningEntry d3n_core d3n_env d3n_trace
    d3n_height d3_clock 2 2 := by
  have route := common_entry_at_low d3n_core d3n_env d3n_trace d3n_height d3_clock
    d3_electorate d3n_height_laws d3n_obs (u := 14) (J := none) (contested := false)
    (r := 1) (m := 2) (Qfg := .genesis) (by decide +kernel) d3n_genesis_caps (by
      intro y K _ hK _ x L _ hL
      have hLK : L = d3n_source2 :=
        Option.some.inj (Option.some.inj (hL.symm.trans (d3n_next_sources x)))
      rw [d3n_source_eq hK, hLK]
      cases y <;> decide +kernel)
  rcases route with low | high
  · exact (d3n_not_low low).elim
  · exact high.2 d3n_phase
private theorem d3n_sent (x : Bool) : HonestRowAt d3n_safety d3n_env d3n_trace
    d3_clock (if x then 2 else 1) x 1 d3n_row := by
  cases x <;> unfold HonestRowAt <;> decide +kernel
private theorem d3n_covered : OpeningCovered d3n_core d3n_safety d3n_env d3n_trace
    d3n_height d3_clock Row.height_pair 1 (d3n_erase d3n_entry) := by
  intro x _
  refine ⟨d3n_selected x, (if x then [d3_row] else []), (if x then 2 else 1),
    1, d3n_row, ?_, d3n_sources x, ?_, ?_, le_rfl, d3n_sent x, ?_⟩ <;>
    cases x <;> decide +kernel
private theorem d3n_agreement : ∀ x y K L, x ∈ d3n_trace.honest →
    y ∈ d3n_trace.honest →
    actionSourceFG d3n_core d3n_env d3n_trace d3_clock x 1 = some (some K) →
    actionSourceFG d3n_core d3n_env d3n_trace d3_clock y 1 = some (some L) →
    (d3n_height K).T_h.root = (d3n_height L).T_h.root →
    (d3n_height K).T_h = (d3n_height L).T_h := by
  intro x y K L _ _ hK hL _
  rw [d3n_source_eq hK, d3n_source_eq hL]
  cases x <;> cases y <;> decide +kernel
private theorem d3n_slots : ∀ x K, x ∈ d3n_trace.honest →
    actionSourceFG d3n_core d3n_env d3n_trace d3_clock x 1 = some (some K) →
    K.slot ≤ 1 * d3_clock.roundSlots := by
  intro x K _ hK
  rw [d3n_source_eq hK]
  cases x <;> decide
private theorem d3n_ancestor_slots : ∀ x K A, x ∈ d3n_trace.honest →
    actionSourceFG d3n_core d3n_env d3n_trace d3_clock x 1 = some (some K) →
    FGBlock.Preceq A K → A.slot ≤ K.slot := by
  intro x K A _ hK hAK
  rw [d3n_source_eq hK] at hAK ⊢
  cases x <;>
    simp only [d3n_selected, Bool.false_eq_true, ite_false, ite_true,
      d3n_source2, d3n_entry, FGBlock.Preceq, FGBlock.preceq,
      Bool.or_eq_true, decide_eq_true_eq] at hAK ⊢
  · rcases hAK with rfl | rfl <;> decide
  · rcases hAK with rfl | rfl | rfl <;> decide
private theorem d3n_bounded : ∃ U, EntryAt d3n_height U 2 ∧
    U.slot ≤ 1 * d3_clock.roundSlots ∧ FixedRows d3n_core d3n_safety d3n_env
      d3n_trace d3n_height d3_clock Row.height_pair 1 2 (d3n_erase d3n_entry) U :=
  healing_promotion_bounded_rows d3n_core d3n_safety d3n_env d3n_trace d3n_height
    d3_clock Row.height_pair d3_electorate d3n_height_laws (by simp)
    d3n_opening d3n_covered d3n_agreement d3n_slots d3n_ancestor_slots
private noncomputable abbrev d3n_interface : V2.D.Interface d3n_protocol where
  confirmed _ := .genesis
  stable _ := .genesis
  block _ := some (d3n_erase d3n_child)
  opening _ := True
  propLabel s := 4 * s
  propDuty s := 4 * s
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective := by
    intro a b h
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) h
private noncomputable abbrev d3n_parent (_ : List (Row (Fin 1))) (key : Block) :=
  if key = d3n_erase d3n_parent_block then some d3n_parent_block else none
private noncomputable abbrev d3n_fold (_ : List (Row (Fin 1))) (_ : Slot)
    (B : FGBlock (Fin 1)) := Window.derive d3_electorate ⟨0⟩ 2 B
private noncomputable abbrev d3n_parent_height (nd : List (Row (Fin 1))) (s : Slot)
    (B : FGBlock (Fin 1)) := ((d3n_fold nd s B).h, (d3n_fold nd s B).T_h.root)
private noncomputable abbrev d3n_valid (nd : List (Row (Fin 1))) (s : Slot)
    (B : FGBlock (Fin 1)) (a : Row (Fin 1)) := Window.r6w (d3n_fold nd s B) a
private theorem d3n_parents : ∀ x K, x ∈ d3n_trace.honest →
    actionSourceFG d3n_core d3n_env d3n_trace d3_clock x 1 = some (some K) →
    FGBlock.Preceq K d3n_child.parent := by
  intro x K _ hK
  rw [d3n_source_eq hK]
  cases x <;> decide
private theorem d3n_proposal : HonestProposal d3n_env d3n_trace d3n_interface
    8 (d3n_erase d3n_child) := by
  refine ⟨⟨by decide, by decide⟩, ⟨.none, d3n_later⟩, ⟨6, ?_, ?_⟩, rfl⟩
  · decide +kernel
  · decide +kernel

private theorem d3n_read : ∃ nd,
    proposalStateAt d3n_env d3n_trace d3n_interface 8 = some nd ∧
    d3n_parent nd (d3n_core.erase d3n_child).parent = some d3n_child.parent ∧
    (d3n_fold nd 8 d3n_child.parent).h = (d3n_height d3n_child.parent).h ∧
    (d3n_fold nd 8 d3n_child.parent).T_h = (d3n_height d3n_child.parent).T_h ∧
    d3n_parent_height nd 8 d3n_child.parent =
      ((d3n_fold nd 8 d3n_child.parent).h, (d3n_fold nd 8 d3n_child.parent).T_h.root) ∧
    ∀ a, d3n_valid nd 8 d3n_child.parent a =
      match d3n_safety.decode a with
      | none => false
      | some b => Window.r6w (d3n_fold nd 8 d3n_child.parent) b := by
  exact ⟨[d3_row], by decide +kernel, by decide, rfl, rfl, rfl, fun _ => rfl⟩

private theorem d3n_complete_on :
    ∃ U, EntryAt d3n_height U 2 ∧ U.slot ≤ 1 * d3_clock.roundSlots
      ∧ FGBlock.Preceq U d3n_child.parent ∧
    ∀ x ∈ d3n_trace.honest, ∃ K nd j rSent a,
      postClock d3n_env d3n_trace x (d3_clock.action 1) = some nd ∧
      actionSourceFG d3n_core d3n_env d3n_trace d3_clock x 1 = some (some K)
      ∧ K ∈ (d3n_core.core nd).fg.TF ∧
      Block.Preceq (d3n_erase d3n_entry) (d3n_core.erase K) ∧ FGBlock.Preceq U K
      ∧ K.slot ≤ 1 * d3_clock.roundSlots ∧
      (d3n_height K).h = 2 ∧ (d3n_height K).T_h = U ∧ rSent ≤ 1
      ∧ HonestRowAt d3n_safety d3n_env d3n_trace d3_clock j x rSent a ∧
      NamesEntry Row.height_pair .progress a 2 U ∧
      ((d3n_height d3n_child.parent).h = 2 →
        ValidForParent d3n_env d3n_trace d3n_interface d3n_parent d3n_valid d3n_child.slot
      (d3n_core.erase d3n_child) a ∧
        HeightMatch d3n_env d3n_trace d3n_interface (fun a => namedEntry (Row.height_pair a))
      d3n_parent d3n_parent_height
          d3n_child.slot (d3n_core.erase d3n_child) a) := by
  exact healing_promotion_same_rows_on d3n_core d3n_safety d3n_env d3n_trace d3n_height
    d3_clock d3n_interface Row.height_pair d3n_parent d3n_parent_height d3n_valid
    d3n_fold d3_electorate d3n_height_laws (by simp) d3n_opening d3n_covered
    d3n_agreement d3n_slots d3n_ancestor_slots d3n_parents rfl d3n_read
    (fun _ _ _ a _ => ⟨a, rfl, rfl⟩)

private theorem d3n_complete_service :
    ∃ U, EntryAt d3n_height U 2 ∧ U.slot ≤ 1 * d3_clock.roundSlots
      ∧ FGBlock.Preceq U d3n_child.parent ∧
    ∀ x ∈ d3n_trace.honest, ∃ K nd j rSent a,
      postClock d3n_env d3n_trace x (d3_clock.action 1) = some nd ∧
      actionSourceFG d3n_core d3n_env d3n_trace d3_clock x 1 = some (some K)
      ∧ K ∈ (d3n_core.core nd).fg.TF ∧
      Block.Preceq (d3n_erase d3n_entry) (d3n_core.erase K) ∧ FGBlock.Preceq U K
      ∧ K.slot ≤ 1 * d3_clock.roundSlots ∧
      (d3n_height K).h = 2 ∧ (d3n_height K).T_h = U ∧ rSent ≤ 1
      ∧ HonestRowAt d3n_safety d3n_env d3n_trace d3_clock j x rSent a ∧
      NamesEntry Row.height_pair .progress a 2 U ∧
      ((d3n_height d3n_child.parent).h = 2 →
        ValidForParent d3n_env d3n_trace d3n_interface d3n_parent d3n_valid d3n_child.slot
      (d3n_core.erase d3n_child) a ∧
        HeightMatch d3n_env d3n_trace d3n_interface (fun a => namedEntry (Row.height_pair a))
      d3n_parent d3n_parent_height
          d3n_child.slot (d3n_core.erase d3n_child) a) := by
  exact healing_promotion_same_rows d3n_core d3n_safety d3n_env d3n_trace d3n_height
    d3_clock d3n_interface Row.height_pair d3n_parent d3n_parent_height d3n_valid
    d3n_fold d3_electorate d3n_height_laws (by simp) d3n_opening d3n_covered
    d3n_agreement d3n_slots d3n_ancestor_slots d3n_parents rfl d3n_read
    (fun _ _ _ a _ => ⟨a, rfl, rfl⟩)

#print axioms d3n_height_laws
#print axioms d3n_sources
#print axioms d3n_next_sources
#print axioms d3n_source_eq
#print axioms d3n_geometry
#print axioms d3n_caps
#print axioms d3n_opening
#print axioms d3n_low_arm
#print axioms d3n_genesis_caps
#print axioms d3n_not_low
#print axioms d3n_high_arm
#print axioms d3n_phase
#print axioms d3n_conditional_next
#print axioms d3n_sent
#print axioms d3n_covered
#print axioms d3n_agreement
#print axioms d3n_slots
#print axioms d3n_ancestor_slots
#print axioms d3n_bounded
#print axioms d3n_parents
#print axioms d3n_proposal
#print axioms d3n_read
#print axioms d3n_complete_on
#print axioms d3n_complete_service

-- Only the two round-1 sends can supply the opening batch.
private theorem d3n_tick_identity {x : Bool} {j rSent : Nat} (hr : rSent ≤ 1)
    (he : d3n_trace.events[j]? = some (.tick x (d3_clock.action rSent))) :
    j = (if x then 2 else 1) ∧ rSent = 1 := by
  have hj : j < 7 := by
    by_contra hn
    have hh : d3n_trace.events[j]? = none := List.getElem?_eq_none (by
      change 7 ≤ j
      omega)
    rw [hh] at he
    contradiction
  revert he
  interval_cases j <;> interval_cases rSent <;> cases x <;> decide +kernel
private theorem d3n_wire_identity {x : Bool} {j rSent : Nat} {a : Row (Fin 1)}
    (hr : rSent ≤ 1) (ha : HonestRowAt d3n_safety d3n_env d3n_trace
      d3_clock j x rSent a) :
    j = (if x then 2 else 1) ∧ rSent = 1 ∧ a = d3n_row := by
  obtain ⟨hj, hrSent⟩ := d3n_tick_identity hr ha.2.1
  refine ⟨hj, hrSent, ?_⟩
  subst j
  have hem := ha.2.2
  cases x <;>
    change (⟨.none, a⟩ : d3n_protocol.Object) ∈ [⟨.none, d3n_row⟩] at hem <;>
    exact congrArg (fun o : d3n_protocol.Object => o.payload) (List.mem_singleton.mp hem)

-- The complete consumer keeps j, rSent and a through the terminal-parent call.
private theorem d3n_terminal_identity : ∀ x ∈ d3n_trace.honest,
    ∃ j rSent a, j = (if x then 2 else 1) ∧ rSent = 1 ∧ a = d3n_row ∧
      HonestRowAt d3n_safety d3n_env d3n_trace d3_clock j x rSent a ∧
      ValidForParent d3n_env d3n_trace d3n_interface d3n_parent d3n_valid
        d3n_child.slot (d3n_erase d3n_child) a ∧
      HeightMatch d3n_env d3n_trace d3n_interface (fun a => namedEntry a.height_pair)
        d3n_parent d3n_parent_height d3n_child.slot (d3n_erase d3n_child) a := by
  obtain ⟨U, _, _, _, rows⟩ := d3n_complete_on
  intro x hx
  obtain ⟨K, nd, j, rSent, a, _, _, _, _, _, _, _, _, hr, ha, _, hv⟩ := rows x hx
  obtain ⟨hj, hrSent, hwire⟩ := d3n_wire_identity hr ha
  exact ⟨j, rSent, a, hj, hrSent, hwire, ha, hv (by decide +kernel)⟩
private theorem d3n_later_matching :
    HonestRowAt d3n_safety d3n_env d3n_trace d3_clock 4 false 2 d3n_later ∧
    NamesEntry Row.height_pair .progress d3n_later 2 d3n_entry ∧
    d3n_later ≠ d3n_row ∧ d3n_later.finality_pair ≠ d3n_row.finality_pair := by
  exact ⟨by unfold HonestRowAt; decide +kernel, ⟨false, rfl⟩, by decide, by decide⟩
private theorem d3n_no_replacement :
    ¬ HonestRowAt d3n_safety d3n_env d3n_trace d3_clock 1 false 1 d3n_later ∧
    ¬ HonestRowAt d3n_safety d3n_env d3n_trace d3_clock 4 false 1 d3n_row ∧
    ¬ (2 ≤ (1 : Nat)) := by
  unfold HonestRowAt
  decide +kernel
private noncomputable abbrev d3n_missing (_ : List (Row (Fin 1))) (key : Block) :=
  if key = d3n_erase d3n_wrong then some d3n_wrong else none
private theorem d3n_lookup_control :
    proposalStateAt d3n_env d3n_trace d3n_interface 8 = some [d3_row] ∧
    d3n_parent [d3_row] (d3n_erase d3n_child).parent = some d3n_parent_block ∧
    d3n_parent [d3_row] (d3n_erase d3n_wrong) = none ∧
    d3n_missing [d3_row] (d3n_erase d3n_child).parent = none ∧
    ¬ FGBlock.Preceq d3n_entry d3n_wrong := by decide +kernel
private theorem d3n_missing_parent_rejected :
    ¬ ValidForParent d3n_env d3n_trace d3n_interface d3n_missing d3n_valid
      d3n_child.slot (d3n_erase d3n_child) d3n_row := by
  rintro ⟨nd, P, _, hp, _⟩
  have hn : d3n_missing nd (d3n_erase d3n_child).parent = none := by
    change (if d3n_erase d3n_parent_block = d3n_erase d3n_wrong then _ else _) = none
    decide
  rw [hn] at hp
  contradiction

#print axioms d3n_tick_identity
#print axioms d3n_wire_identity
#print axioms d3n_terminal_identity
#print axioms d3n_later_matching
#print axioms d3n_no_replacement
#print axioms d3n_lookup_control
#print axioms d3n_missing_parent_rejected

end AvailableChain.FGCompose.Tests.P0d3
end
