module
public import AvailableChainFGCompose.Proofs.Population.Middle -- shake: keep (private controls)
public import AvailableChainFGCompose.Proofs.Population.KernelBridges -- shake: keep (controls)
public import AvailableChainFGCompose.Statements.Population.Seats -- shake: keep (private controls)

set_option linter.privateModule false
noncomputable section
public section

/-! Generic ordinary event-fold controls for the full selected middle and action records.
The mixed run has both honest receivers; FG label 0 belongs only to holder 9. -/
namespace AvailableChain.FGCompose.Tests.PopulationMiddle
open AvailableChain.SimplexFG AvailableChain.KitFG

private abbrev electorate : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private abbrev cfg : FGConfig := ⟨4⟩
private abbrev row0 : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private abbrev aBlock : FGBlock (Fin 1) := .node .genesis 2 ⟨1⟩ 0 [row0]
private abbrev row1 : Row (Fin 1) := ⟨0, .vote 2 aBlock.root false, none⟩
private abbrev bBlock : FGBlock (Fin 1) := .node aBlock 4 ⟨2⟩ 0 [row1]
private abbrev row2 : Row (Fin 1) := ⟨0, .vote 3 bBlock.root false, none⟩
private abbrev dBlock : FGBlock (Fin 1) := .node bBlock 6 ⟨3⟩ 0 [row2]
private abbrev row3 : Row (Fin 1) := ⟨0, .vote 4 dBlock.root false, none⟩
private def erase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node p s r b rows => .node (erase p) s r (encFGBody b rows)
private abbrev timing : FGTiming where
  delta := 1
  roundSlots := 2
  proposal s := 4 * s
  vote s := 4 * s + 1
  early s := 4 * s + 2
  freeze s := 4 * s + 3
  release s := 4 * s + 5
  gate s := 4 * s + 6
  action r := 4 * (r * 2 : Nat) + 6
private abbrev protocol : V2.ProtocolSpecD Unit where
  State := Time
  Label := Nat
  Duty := Time
  signLabel t := if t % 8 = 6 then 0 else t.toNat + 1
  seats _ := 1
  Payload := FGBlock (Fin 1) ⊕ Row (Fin 1)
  Durable := Time
  init := 0
  clock _ t := t
  actTime := id
  duties t := [t]
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; simp
  act _ t _ := if t = 6 then some (.inr row0) else
    if t = 14 then some (.inr row1) else if t = 22 then some (.inr row2) else
    if t = 30 then some (.inr row3) else if t = 8 then some (.inl aBlock) else
    if t = 16 then some (.inl bBlock) else if t = 24 then some (.inl dBlock) else none
  gossip _ _ := []
  process st _ := st
  selfVisible _ := true
  recordOwn st _ := st
  durable := id
  restore st _ := st
  wellFormed _ := true
  depsPresent _ _ := true
  processed _ _ := false
  excludes _ _ := false
  handles _ _ _ := False
  carries _ _ := False
private abbrev wire (row : Row (Fin 1)) : protocol.Object := ⟨.seat 0 0, .inr row⟩
private abbrev prop (X : FGBlock (Fin 1)) : protocol.Object :=
  ⟨.seat (4 * X.slot + 1) 0, .inl X⟩
private abbrev decode (o : protocol.Object) : Option (Row (Fin 1)) :=
  match o.payload with | .inl _ => none | .inr row => some row
private abbrev reads : FGSafetyReads protocol 1 protocol.Object where
  proposalErase o := match o.payload with | .inl X => some (erase X) | .inr _ => none
  proposalRows o := match o.payload with | .inl X => X.rows.map wire | .inr _ => []
  encode := id
  decode := decode
  decodeObject := decode
  fgLabel := 0
  fgSeats := Equiv.refl _
  record _ := RecordOnce.initial
  inputs _ := (none, ⟨0, genesisRoot, 0⟩)
  enabled t := decide (t % 8 = 6)
  finalizedOut _ := .genesis
private abbrev source (t : Time) : FGBlock (Fin 1) :=
  if t < 16 then aBlock else if t < 24 then bBlock else dBlock
private abbrev core : FGCoreReads protocol 1 Unit Unit protocol.Object where
  core t := ⟨(), { Store.init with
    TF := if t < 16 then {.genesis, aBlock} else if t < 24 then {.genesis, aBlock, bBlock} else
      {.genesis, aBlock, bBlock, dBlock} }, [], [wire row0, wire row1, wire row2, wire row3]⟩
  erase := erase
  source t := some (source t)
  headVote _ s := erase (if s = 2 then aBlock else if s = 4 then bBlock else dBlock)
  finalityHead _ := some dBlock
  proposalFG _ _ := none
private abbrev obs : FGObservationReads core where
  height := KitFG.Window.certificateHeight electorate cfg 2
  finality := KitFG.Window.certificateFinality electorate cfg 2
  controls _ := ⟨.genesis, 1, 0, .genesis, false⟩
  viable _ X := X
private abbrev history : FGHistoryWireReads reads where
  heightPair a := (decode a).map (·.height_pair) |>.getD .empty
  finalityPair a := (decode a).bind (·.finality_pair)
  signer a := (decode a).map (·.signer)
  decode_height a u hd := by
    change ((decode a).map (·.height_pair)).getD .empty = u.height_pair
    change decode a = some u at hd
    rw [hd]; rfl
  decode_finality a u hd := by
    change (decode a).bind (·.finality_pair) = u.finality_pair
    change decode a = some u at hd
    rw [hd]; rfl
  decode_signer a u hd := by
    change (decode a).map (·.signer) = some u.signer
    change decode a = some u at hd
    rw [hd]; rfl
private abbrev interface : V2.D.Interface protocol where
  confirmed _ := .genesis
  stable _ := .genesis
  block o := match o with | .inl X => some (erase X) | .inr _ => none
  opening _ := True
  propLabel s := 4 * s + 1
  propDuty s := 4 * s
  propDuty_label s := by
    change (if (4 * s : Int) % 8 = 6 then 0 else (4 * s : Int).toNat + 1) = 4 * s + 1
    have hn : (4 * s : Int) % 8 ≠ 6 := by omega
    rw [ite_eq_right hn]
    have ht : (4 * s : Int) = ((4 * s : Nat) : Int) := by push_cast; rfl
    rw [ht, Int.toNat_natCast]
  propLabel_single _ := rfl
  propLabel_injective := by
    intro a b h
    change 4 * a + 1 = 4 * b + 1 at h
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) (Nat.add_right_cancel h)
private abbrev env (V : Type) : Generic.Env V :=
  ⟨2, by decide, 0, by decide, fun _ _ => true⟩
private abbrev run : V2.D.Run Nat protocol where
  honest := {7, 9}
  horizon := 32
  events := [.tick 9 0, .tick 7 0, .tick 9 2, .tick 7 2, .tick 9 4, .tick 7 4, .tick 9 6,
    .tick 7 6, .tick 9 8, .tick 7 8, .tick 9 10, .tick 7 10, .tick 9 12, .tick 7 12, .tick 9 14,
    .tick 7 14, .tick 9 16, .tick 7 16, .tick 9 18, .tick 7 18, .tick 9 20, .tick 7 20,
    .tick 9 22, .tick 7 22, .tick 9 24, .tick 7 24, .tick 9 26, .tick 7 26, .tick 9 28,
    .tick 7 28, .tick 9 30, .tick 7 30, .tick 9 32, .tick 7 32]
  seatOf label _ := if label = 0 then 9 else 7
  input _ _ := ()
private abbrev frozenRun : V2.D.Run (Fin 1) protocol where
  honest := Finset.univ
  horizon := 32
  events := [.tick 0 0, .tick 0 2, .tick 0 4, .tick 0 6, .tick 0 8, .tick 0 10, .tick 0 12,
    .tick 0 14, .tick 0 16, .tick 0 18, .tick 0 20, .tick 0 22, .tick 0 24, .tick 0 26,
    .tick 0 28, .tick 0 30, .tick 0 32]
  seatOf _ _ := 0
  input _ _ := ()
private abbrev decodeProposal (o : protocol.Object) : Option (Slot × FGBlock (Fin 1)) :=
  match o.payload with | .inl X => some (X.slot, X) | .inr _ => none
private abbrev parentRead (_ : Time) (Q : Block) : Option (FGBlock (Fin 1)) :=
  if Q = erase aBlock then some aBlock else if Q = erase bBlock then some bBlock else
    if Q = erase dBlock then some dBlock else some .genesis
private abbrev parentHeight (_ : Time) (_ : Slot) (X : FGBlock (Fin 1)) : Height × BlockId :=
  ((obs.height X).h, (obs.height X).T_h.root)
private abbrev makeFG (_ : FGBlock (Fin 1)) (Q : Block) (_ : List protocol.Object) :=
  if Q = erase aBlock then aBlock else if Q = erase bBlock then bBlock else dBlock
private abbrev ac (V : Type) : FGACServiceReads V where
  honest _ := True
  proposal _ _ := True
  proposalTime := timing.proposal
  actionHeadLabel r := r * 2 + 1
  actionTime := timing.action
  proposalScope _ _ := True
  sourceScope _ _ _ := True
  actionScope _ _ := True
  actionHead _ _ := some (some (erase dBlock))
  parent _ := some (erase bBlock)
  gateFloor _ _ := some (erase bBlock)
  frame _ _ _ := True
  below := Block.Preceq
  headScope _ _ := True
  gateScope _ _ := True
  voteTime s := timing.vote s
  gateTime s := timing.gate s
  gateLabel r := r * 2
  headAtLabel _ _ := some (erase dBlock)
  gate _ _ := some (some (erase dBlock))
  source _ _ := some (some (erase dBlock))
private abbrev point : FGServicePoint := ⟨⟨0, 0, 0, 0, 0, .genesis⟩, 0, .genesis, 0⟩
private abbrev pt : KernelPt := ⟨1⟩
private abbrev middleType {V : Type} [DecidableEq V] (rho : V2.D.Run V protocol) :=
  KernelMiddleWitnessFG_W core reads obs timing (env V) rho interface history electorate
    decodeProposal erase (fun X => X.rows.map wire) (fun _ => []) parentRead parentHeight
    (fun _ _ _ _ => true) makeFG (fun _ => true) (ac V) cfg 2 2 point pt (erase aBlock)

private theorem block_premises_sat :
    (obs.height aBlock).h = 2 ∧ (obs.height bBlock).h = 3 ∧
    (obs.height bBlock).T_h = bBlock ∧ (obs.height dBlock).h = 4 ∧
    (obs.height dBlock).J = bBlock ∧ (obs.height dBlock).h_j = 3 ∧
    (SimplexFG.Window.derive electorate cfg 2 dBlock).h_F < 3 ∧
    KitFG.Window.RetainedW electorate cfg 2 dBlock 3 bBlock := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, ⟨⟨3, bBlock, ∅⟩, ?_, rfl, rfl⟩⟩
  decide +kernel

#print axioms block_premises_sat

private theorem exact_rows (j x q : Nat) (a : protocol.Object)
    (ha : HonestRowAt reads (env Nat) run timing j x q a) :
    (j = 6 ∧ x = 9 ∧ q = 0 ∧ a = wire row0) ∨
    (j = 14 ∧ x = 9 ∧ q = 1 ∧ a = wire row1) ∨
    (j = 22 ∧ x = 9 ∧ q = 2 ∧ a = wire row2) ∨
    (j = 30 ∧ x = 9 ∧ q = 3 ∧ a = wire row3) := by
  obtain ⟨_, hj, hw⟩ := ha
  have hlen : j < 34 := (List.getElem?_eq_some_iff.mp hj).1
  interval_cases j
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : 9 = x ∧ (6 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (6 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    have hq : q = 0 := by omega
    obtain rfl := he.1.symm
    subst q
    change a ∈ [wire row0] at hw
    have hw' := List.mem_singleton.mp hw
    exact Or.inl (⟨rfl, rfl, rfl, hw'⟩)
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : 7 = x ∧ (8 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (8 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    omega
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : 9 = x ∧ (14 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (14 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    have hq : q = 1 := by omega
    obtain rfl := he.1.symm
    subst q
    change a ∈ [wire row1] at hw
    have hw' := List.mem_singleton.mp hw
    exact Or.inr (Or.inl (⟨rfl, rfl, rfl, hw'⟩))
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : 7 = x ∧ (16 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (16 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    omega
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : 9 = x ∧ (22 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (22 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    have hq : q = 2 := by omega
    obtain rfl := he.1.symm
    subst q
    change a ∈ [wire row2] at hw
    have hw' := List.mem_singleton.mp hw
    exact Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl, hw'⟩)))
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : 7 = x ∧ (24 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (24 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    omega
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : 9 = x ∧ (30 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (30 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    have hq : q = 3 := by omega
    obtain rfl := he.1.symm
    subst q
    change a ∈ [wire row3] at hw
    have hw' := List.mem_singleton.mp hw
    exact Or.inr (Or.inr (Or.inr (⟨rfl, rfl, rfl, hw'⟩)))
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw

#print axioms exact_rows

private theorem schedule_premises_sat : V2.D.ScheduleWellFormed (env Nat) run := by
  constructor
  · decide
  · decide +kernel
  · decide +kernel
  · intro ev hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with
      rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl
    all_goals decide
  · intro ev hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with
      rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl
    all_goals decide
  · intro x t hm
    simp only [List.mem_cons, List.mem_nil_iff, V2.Event.tick.injEq,
      or_false] at hm
    rcases hm with
      ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩
    · exact ⟨7, rfl⟩
    · exact ⟨8, rfl⟩
    · exact ⟨8, rfl⟩
    · exact ⟨9, rfl⟩
    · exact ⟨9, rfl⟩
    · exact ⟨10, rfl⟩
    · exact ⟨10, rfl⟩
    · exact ⟨11, rfl⟩
    · exact ⟨11, rfl⟩
    · exact ⟨12, rfl⟩
    · exact ⟨12, rfl⟩
    · exact ⟨13, rfl⟩
    · exact ⟨13, rfl⟩
    · exact ⟨14, rfl⟩
    · exact ⟨14, rfl⟩
    · exact ⟨15, rfl⟩
    · exact ⟨15, rfl⟩
    · exact ⟨16, rfl⟩
    · exact ⟨16, rfl⟩
  · intro x hx t ht _ hhor _
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    obtain ⟨k, hk⟩ := ht
    change t = (k : Time) * 2 at hk
    change t ≤ 32 at hhor
    rw [hk] at hhor
    have hb : k * 2 ≤ 32 := by exact_mod_cast hhor
    have hbound : k ≤ 16 := by omega
    subst t
    rcases hx' with rfl | rfl <;> interval_cases k <;> simp

#print axioms schedule_premises_sat

private abbrev batchType {V : Type} [DecidableEq V] (rho : V2.D.Run V protocol)
    (q y : Nat) (U X : FGBlock (Fin 1)) :=
  BatchPrem core reads obs timing (env V) rho interface history electorate decodeProposal
    erase (fun X => X.rows.map wire) (fun _ => []) parentRead parentHeight
    (fun _ _ _ _ => true) 2 .target q y U X

private theorem batch_premises_sat :
    batchType run 1 2 aBlock bBlock ∧ batchType run 2 3 bBlock dBlock := by
  have hweight : electorate.weightOf (historyFaulty reads run) < electorate.q := by
    change (0 : Nat) < 1
    decide
  have receipt : TRowsReceipt core reads (env Nat) run timing (fun _ => []) 2 := by
    intro j x q a ha _ z _
    rcases exact_rows j x q a ha with h | h | h | h
    all_goals
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Or.inl (by
        change wire _ ∈ [wire row0, wire row1, wire row2, wire row3]
        decide +kernel)
  have height := KitFG.Window.windowHeightLaws electorate cfg 2 (by decide)
  constructor
  · refine kmid_batchPrem_holder core reads obs timing (env Nat) run interface history
      electorate cfg 2 height rfl decodeProposal erase (fun X => X.rows.map wire)
      (fun _ => []) parentRead parentHeight (fun _ _ _ _ => true) (fun _ => true) 2
      schedule_premises_sat hweight ?_ {0} ?_ (by change (1 : Nat) ≤ 1; decide)
      (by decide) receipt 1 2 aBlock bBlock (by decide) ?_ 16 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) ?_ ?_ ?_ rfl (by intros; rfl)
      (by decide) (by constructor <;> decide +kernel) (preceq_refl _) (by decide +kernel) ?_
    · intro i i' _; exact Subsingleton.elim _ _
    · intro i _; change (9 : Nat) ∈ ({7, 9} : Finset Nat); decide
    · refine ⟨[wire row1], ?_, rfl⟩
      refine ⟨⟨⟨by decide, by decide⟩, prop bBlock, ⟨17, rfl, by decide +kernel⟩, rfl⟩,
        prop bBlock, ⟨17, rfl, by decide +kernel⟩, bBlock, rfl, rfl, rfl⟩
    · intro W hW
      change W ∈ ({.genesis, aBlock, bBlock} : Finset (FGBlock (Fin 1))) at hW
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl <;> decide +kernel
    · have ancestors (X : FGBlock (Fin 1))
          (hX : ∃ W ∈ ({.genesis, aBlock, bBlock} : Finset (FGBlock (Fin 1))), FGBlock.Preceq X W) :
          X ∈ ({.genesis, aBlock, bBlock} : Finset (FGBlock (Fin 1))) := by
        obtain ⟨W, hW, hXW⟩ := hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hW ⊢
        rcases hW with rfl | rfl | rfl
        all_goals
          simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
            decide_eq_true_eq] at hXW
          tauto
      intro W Z hW hZ he
      have hw := ancestors W hW
      have hz := ancestors Z hZ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw hz
      rcases hw with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl <;>
        simp_all [FGBlock.root, genesisRoot]
    · intro W hW row hr
      change W ∈ ({.genesis, aBlock, bBlock} : Finset (FGBlock (Fin 1))) at hW
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl
      · cases hr
      · have he : row = row0 := List.mem_singleton.mp hr
        subst row
        decide +kernel
      · have he : row = row1 := List.mem_singleton.mp hr
        subst row
        decide +kernel
    · intro i _
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact ⟨14, 1, wire row1, le_rfl, ⟨by decide, rfl, by decide +kernel⟩,
        ⟨rfl, 0, rfl, rfl⟩, rfl⟩
  · refine kmid_batchPrem_holder core reads obs timing (env Nat) run interface history
      electorate cfg 2 height rfl decodeProposal erase (fun X => X.rows.map wire)
      (fun _ => []) parentRead parentHeight (fun _ _ _ _ => true) (fun _ => true) 2
      schedule_premises_sat hweight ?_ {0} ?_ (by change (1 : Nat) ≤ 1; decide)
      (by decide) receipt 2 3 bBlock dBlock (by decide) ?_ 24 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) ?_ ?_ ?_ rfl (by intros; rfl)
      (by decide) (by constructor <;> decide +kernel) (preceq_refl _) (by decide +kernel) ?_
    · intro i i' _; exact Subsingleton.elim _ _
    · intro i _; change (9 : Nat) ∈ ({7, 9} : Finset Nat); decide
    · refine ⟨[wire row2], ?_, rfl⟩
      refine ⟨⟨⟨by decide, by decide⟩, prop dBlock, ⟨25, rfl, by decide +kernel⟩, rfl⟩,
        prop dBlock, ⟨25, rfl, by decide +kernel⟩, dBlock, rfl, rfl, rfl⟩
    · intro W hW
      change W ∈ ({.genesis, aBlock, bBlock, dBlock} : Finset (FGBlock (Fin 1))) at hW
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl | rfl <;> decide +kernel
    · have ancestors (X : FGBlock (Fin 1))
          (hX : ∃ W ∈ ({.genesis, aBlock, bBlock, dBlock} : Finset (FGBlock (Fin 1))),
            FGBlock.Preceq X W) :
          X ∈ ({.genesis, aBlock, bBlock, dBlock} : Finset (FGBlock (Fin 1))) := by
        obtain ⟨W, hW, hXW⟩ := hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hW ⊢
        rcases hW with rfl | rfl | rfl | rfl
        all_goals
          simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
            decide_eq_true_eq] at hXW
          tauto
      intro W Z hW hZ he
      have hw := ancestors W hW
      have hz := ancestors Z hZ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw hz
      rcases hw with rfl | rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl <;>
        simp_all [FGBlock.root, genesisRoot]
    · intro W hW row hr
      change W ∈ ({.genesis, aBlock, bBlock, dBlock} : Finset (FGBlock (Fin 1))) at hW
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl | rfl
      · cases hr
      · have he : row = row0 := List.mem_singleton.mp hr
        subst row
        decide +kernel
      · have he : row = row1 := List.mem_singleton.mp hr
        subst row
        decide +kernel
      · have he : row = row2 := List.mem_singleton.mp hr
        subst row
        decide +kernel
    · intro i _
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact ⟨22, 2, wire row2, le_rfl, ⟨by decide, rfl, by decide +kernel⟩,
        ⟨rfl, 0, rfl, rfl⟩, rfl⟩

#print axioms batch_premises_sat

private theorem mixed_premises_sat : ∃ m : middleType run,
    m.A₀ = aBlock ∧ m.B = bBlock ∧ m.U = bBlock ∧ m.X_D = dBlock ∧
    m.cD = 6 ∧ m.d = 2 := by
  have first : ∀ j x q a h t, HonestRowAt reads (env Nat) run timing j x q a →
      historyRowHeight reads history a = some h → 3 ≤ h → eventTime run j = some t →
      timing.action 2 ≤ t := by
    intro j x q a h t ha hh hy ht
    rcases exact_rows j x q a ha with he | he | he | he
    all_goals
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      simp only [historyRowHeight, decode, Option.map_some,
        Option.getD_some, Option.some.injEq] at hh
      obtain rfl := hh.symm
      have htime : _ = t := Option.some.inj ht
      subst t
      first | omega | decide
  have second : ∀ j x q a h t, HonestRowAt reads (env Nat) run timing j x q a →
      historyRowHeight reads history a = some h → 4 ≤ h → eventTime run j = some t →
      timing.action 3 ≤ t := by
    intro j x q a h t ha hh hy ht
    rcases exact_rows j x q a ha with he | he | he | he
    all_goals
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      simp only [historyRowHeight, decode, Option.map_some,
        Option.getD_some, Option.some.injEq] at hh
      obtain rfl := hh.symm
      have htime : _ = t := Option.some.inj ht
      subst t
      first | omega | decide
  have noFin : ∀ j x q a h t, HonestRowAt reads (env Nat) run timing j x q a →
      historyFinHeight reads history a = some h → 3 ≤ h → eventTime run j = some t →
      timing.action 3 ≤ t := by
    intro j x q a h t ha hh _ _
    rcases exact_rows j x q a ha with he | he | he | he
    all_goals
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      cases hh
  have chains : ChainRowsBefore core (env Nat) run aBlock 14 ∧
      ChainRowsBefore core (env Nat) run bBlock 22 ∧
      ChainRowsBefore core (env Nat) run dBlock 30 := by
    refine ⟨?_, ?_, ?_⟩
    · intro W hp row hr
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hp
      rcases hp with rfl | rfl
      · exact ⟨9, 1, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · cases hr
    · intro W hp row hr
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨9, 17, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · exact ⟨9, 1, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · cases hr
    · intro W hp row hr
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨9, 25, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · exact ⟨9, 17, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · exact ⟨9, 1, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · cases hr
  have capB : ∀ i x W, i ≤ run.events.length → i ≤ afterTicksIdx run 22 →
      HeldAt core (env Nat) run i x W → (obs.height W).h ≤ 3 := by
    intro i x W _ hi ⟨hx, hW⟩
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    have hib : i ≤ 24 := hi
    have ht : V2.D.Run.stateBefore (env Nat) run i x < 24 := by
      rcases hx' with rfl | rfl <;> interval_cases i <;> decide +kernel
    change W ∈ (if V2.D.Run.stateBefore (env Nat) run i x < 16 then
      ({FGBlock.genesis, aBlock} :
        Finset (FGBlock (Fin 1))) else if V2.D.Run.stateBefore (env Nat) run i x < 24 then
      ({FGBlock.genesis, aBlock, bBlock} :
        Finset (FGBlock (Fin 1))) else ({FGBlock.genesis, aBlock, bBlock, dBlock} :
        Finset (FGBlock (Fin 1)))) at hW
    rw [ite_eq_left ht] at hW
    split_ifs at hW
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl <;> decide +kernel
  have capFinal : ∀ i x W, HeldAt core (env Nat) run i x W →
      (obs.height W).h ≤ 4 ∧ (obs.finality W).h_F < 3 := by
    intro i x W ⟨_, hW⟩
    change W ∈ (if V2.D.Run.stateBefore (env Nat) run i x < 16 then
      ({FGBlock.genesis, aBlock} :
        Finset (FGBlock (Fin 1))) else if V2.D.Run.stateBefore (env Nat) run i x < 24 then
      ({FGBlock.genesis, aBlock, bBlock} :
        Finset (FGBlock (Fin 1))) else ({FGBlock.genesis, aBlock, bBlock, dBlock} :
        Finset (FGBlock (Fin 1)))) at hW
    split_ifs at hW
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl | rfl <;> constructor <;> decide +kernel
  let m : middleType run := {
    A₀ := aBlock
    B := bBlock
    U := bBlock
    X_D := dBlock
    cD := 6
    d := 2
    opening := ⟨⟨by decide, by decide⟩, prop aBlock, ⟨9, rfl, by decide +kernel⟩, rfl⟩
    eraseA := rfl
    carrierA := ⟨prop aBlock, aBlock, 8, .genesis,
      ⟨9, rfl, by decide +kernel⟩, rfl, rfl, by decide +kernel, by decide +kernel, rfl⟩
    carrierB := ⟨prop bBlock, bBlock, 16, aBlock,
      ⟨17, rfl, by decide +kernel⟩, rfl, rfl, by decide +kernel, by decide +kernel, by decide⟩
    carrierD := ⟨prop dBlock, dBlock, 24, bBlock,
      ⟨25, rfl, by decide +kernel⟩, rfl, rfl, by decide +kernel, by decide +kernel, by decide⟩
    honestB := ⟨⟨by decide, by decide⟩, prop bBlock, ⟨17, rfl, by decide +kernel⟩, rfl⟩
    honestD := ⟨⟨by decide, by decide⟩, prop dBlock, ⟨25, rfl, by decide +kernel⟩, rfl⟩
    slotA := rfl
    slotB := rfl
    slotD := rfl
    earlySlot := ⟨by decide, by decide⟩
    heightA := block_premises_sat.1
    highA := by decide
    heightB := block_premises_sat.2.1
    entryB := block_premises_sat.2.2.1
    freshEntry := ⟨by decide +kernel, by decide +kernel⟩
    strictAU := ⟨by decide, by decide⟩
    pathUB := preceq_refl _
    freshSlot := ⟨by decide, by decide⟩
    parentAB := preceq_refl _
    parentBD := preceq_refl _
    sourceA := by
      intro x hx
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx' with rfl | rfl <;> decide +kernel
    sourceB := by
      intro x hx
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx' with rfl | rfl <;> decide +kernel
    serviceD := ⟨fun _ x _ _ => rfl, fun _ x _ _ => ⟨rfl, fun _ _ => rfl⟩⟩
    heightD := by decide +kernel
    justifiedD := by decide +kernel
    justifiedHeightD := by decide +kernel
    pendingD := by decide +kernel
    retainedD := block_premises_sat.2.2.2.2.2.2.2
    noFirstHeight := first
    noSecondHeight := second
    noEarlyFinality := noFin
    chainA := chains.1
    chainB := chains.2.1
    chainD := chains.2.2
    freshD := ⟨schedule_premises_sat, by change (0 : Nat) < 1; decide,
      30, le_rfl, chains.2.2, second, noFin⟩
    noMixedD := by
      intro W hp
      change FGBlock.Preceq W bBlock at hp
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hp
      rcases hp with rfl | rfl | rfl <;> unfold MixedCross <;> decide +kernel
    batchB := fun _ => batch_premises_sat.1
    batchD := fun _ => batch_premises_sat.2
    targetsB := by
      intro i _
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact ⟨22, wire row2, ⟨by decide, rfl, by decide +kernel⟩,
        ⟨rfl, 0, rfl, rfl⟩, rfl⟩
    actionsInRun := by decide
    capThroughBAction := capB
    capThroughFinalAction := fun i x W _ _ h => (capFinal i x W h).1
    finalityThroughFinalAction := fun i x W _ _ h => (capFinal i x W h).2
    heldDAtFinalAction := by
      intro x hx
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx' with rfl | rfl <;> decide +kernel
    heldAAtEnd := by
      intro x hx
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx' with rfl | rfl <;> decide +kernel
  }
  exact ⟨m, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms mixed_premises_sat

private theorem action_premises_sat : ∃ m : middleType run,
    (m.A₀ = aBlock ∧ m.B = bBlock ∧ m.U = bBlock ∧ m.X_D = dBlock ∧
      m.cD = 6 ∧ m.d = 2) ∧
    KernelActionSupplyFG_W core reads obs timing (env Nat) run interface history electorate m := by
  obtain ⟨m, hA, hB, hU, hD, hc, hd⟩ := mixed_premises_sat
  have honestRead (x : Nat) (nd : Time) (hnd : postClock (env Nat) run x 30 = some nd) :
      x = 7 ∨ x = 9 := by
    unfold postClock preTick at hnd
    cases hi : V2.D.Run.tickIdx? run x 30 with
    | none => simp only [hi, Option.map_none] at hnd; contradiction
    | some j =>
      have he := V2.D.Run.tickIdx?_spec hi
      have hm := List.mem_of_getElem? he
      have hx := schedule_premises_sat.honest_only _ hm
      change x ∈ run.honest at hx
      simpa using hx
  refine ⟨m, ⟨hA, hB, hU, hD, hc, hd⟩, ?_⟩
  constructor
  · intro x nd hnd
    change postClock (env Nat) run x 30 = some nd at hnd
    have hx := honestRead x nd hnd
    rcases hx with rfl | rfl
    all_goals
      change some 30 = some nd at hnd
      obtain rfl := Option.some.inj hnd
      decide +kernel
  · intro x hx
    rw [hc, hD]
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl
    all_goals
      constructor
      · intro _; exact ⟨30, by decide +kernel, rfl⟩
      · intro h; change (6 : Nat) < 6 at h; omega
  · intro x nd hx hnd
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl
    all_goals
      change some 30 = some nd at hnd
      obtain rfl := Option.some.inj hnd
      exact ⟨dBlock, rfl, by decide⟩
  · intro x nd _ _ H hH
    have he : dBlock = H := Option.some.inj hH
    subst H
    rw [hD]
    decide

#print axioms action_premises_sat

private theorem mixed_inspected : ∃ m : middleType run,
    m.X_D = dBlock ∧ m.U = bBlock ∧
    (FGBlock.Preceq aBlock bBlock ∧ aBlock ≠ bBlock ∧
      (obs.height bBlock).h = (obs.height aBlock).h + 1) ∧
    ((obs.height dBlock).J = bBlock ∧ (obs.height dBlock).h_j = 3) ∧
    HonestRowAt reads (env Nat) run timing 22 9 2 (wire row2) ∧
    RowComplete reads run history.signer (fun _ => true) 9 (wire row2) ∧
    (∀ x ∈ run.honest,
      actionSourceFG core (env Nat) run timing x 1 = some (some aBlock) ∧
      actionSourceFG core (env Nat) run timing x 2 = some (some bBlock) ∧
      dBlock ∈ (core.core (V2.D.Run.stateBefore (env Nat) run (afterTicksIdx run 30) x)).fg.TF ∧
      FGSourceService core (env Nat) run x 30 6 6 dBlock ∧
      ∃ H, core.finalityHead 30 = some H ∧ H ∈ (core.core 30).fg.TF ∧
        Block.Preceq (erase dBlock) (erase H)) ∧
    electorate.IsQuorum ({0} : Finset (Fin 1)) ∧
    (FGHonestSeats reads run).card = 1 ∧ run.honest.card = 2 := by
  obtain ⟨m, ⟨hA, hB, hU, hD, hc, hd⟩, act⟩ := action_premises_sat
  have fresh := kernel_middle_fresh_U_holder (m := m)
  have early := kernel_middle_early_justification_holder (m := m)
  have hfresh : FGBlock.Preceq aBlock bBlock ∧ aBlock ≠ bBlock ∧
      (obs.height bBlock).h = (obs.height aBlock).h + 1 := by
    rw [hA, hU] at fresh
    exact ⟨fresh.1, fresh.2.1, fresh.2.2.1⟩
  have hearly : (obs.height dBlock).J = bBlock ∧ (obs.height dBlock).h_j = 3 := by
    rw [hD, hU, hd] at early
    exact ⟨early.2.1, early.2.2.1⟩
  refine ⟨m, hD, hU, hfresh, hearly, ⟨by decide, rfl, by decide +kernel⟩,
    ⟨rfl, 0, rfl, rfl⟩, ?_, by change (1 : Nat) ≤ 1; decide, ?_, by decide⟩
  · intro x hx
    have ha := m.sourceA x hx
    have hb := m.sourceB x hx
    have hh := m.heldDAtFinalAction x hx
    have service := act.service x hx
    rw [hA] at ha
    rw [hB] at hb
    rw [hD] at hh
    rw [hc, hD] at service
    have hnd : postClock (env Nat) run x 30 = some 30 := by
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx' with rfl | rfl <;> decide +kernel
    obtain ⟨H, hH, hheld⟩ := act.head x 30 hx hnd
    exact ⟨ha, hb, hh, service, H, hH, hheld, by
      simpa only [hD] using act.walk x 30 hx hnd H hH⟩
  · change (Finset.univ.filter (fun _ : Fin 1 => (9 : Nat) ∈ ({7, 9} : Finset Nat))).card = 1
    decide

#print axioms mixed_inspected

-- The only obstruction is signer ownership, independent of every selected field.
private theorem old_middle_impossible (config : FGConfig) (capacity : Nat) (delay : Time)
    (sp : FGServicePoint) (p : KernelPt) (A : Block) :
    ¬ Nonempty (KernelMiddleWitness_W core reads obs timing (env Nat) run interface
      history electorate decodeProposal erase (fun X => X.rows.map wire) (fun _ => [])
      parentRead parentHeight (fun _ _ _ _ => true) makeFG (fun _ => true) (ac Nat)
      config capacity delay sp p A) := by
  rintro ⟨m⟩
  obtain ⟨_, _, _, complete, _⟩ := m.targetsB 7 (by decide)
  obtain ⟨i, _, hi⟩ := complete.2
  change (9 : Nat) = 7 at hi
  omega

#print axioms old_middle_impossible

private theorem frozen_rows (j : Nat) (x : Fin 1) (q : Nat) (a : protocol.Object)
    (ha : HonestRowAt reads (env (Fin 1)) frozenRun timing j x q a) :
    (j = 3 ∧ x = 0 ∧ q = 0 ∧ a = wire row0) ∨
    (j = 7 ∧ x = 0 ∧ q = 1 ∧ a = wire row1) ∨
    (j = 11 ∧ x = 0 ∧ q = 2 ∧ a = wire row2) ∨
    (j = 15 ∧ x = 0 ∧ q = 3 ∧ a = wire row3) := by
  obtain ⟨_, hj, hw⟩ := ha
  have hlen : j < 17 := (List.getElem?_eq_some_iff.mp hj).1
  interval_cases j
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : (0 : Fin 1) = x ∧ (6 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (6 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    have hq : q = 0 := by omega
    obtain rfl := he.1.symm
    subst q
    change a ∈ [wire row0] at hw
    have hw' := List.mem_singleton.mp hw
    exact Or.inl (⟨rfl, rfl, rfl, hw'⟩)
  · have he : (0 : Fin 1) = x ∧ (8 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (8 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    omega
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : (0 : Fin 1) = x ∧ (14 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (14 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    have hq : q = 1 := by omega
    obtain rfl := he.1.symm
    subst q
    change a ∈ [wire row1] at hw
    have hw' := List.mem_singleton.mp hw
    exact Or.inr (Or.inl (⟨rfl, rfl, rfl, hw'⟩))
  · have he : (0 : Fin 1) = x ∧ (16 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (16 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    omega
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : (0 : Fin 1) = x ∧ (22 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (22 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    have hq : q = 2 := by omega
    obtain rfl := he.1.symm
    subst q
    change a ∈ [wire row2] at hw
    have hw' := List.mem_singleton.mp hw
    exact Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl, hw'⟩)))
  · have he : (0 : Fin 1) = x ∧ (24 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (24 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    omega
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : (0 : Fin 1) = x ∧ (30 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (30 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    have hq : q = 3 := by omega
    obtain rfl := he.1.symm
    subst q
    change a ∈ [wire row3] at hw
    have hw' := List.mem_singleton.mp hw
    exact Or.inr (Or.inr (Or.inr (⟨rfl, rfl, rfl, hw'⟩)))
  · change a ∈ [] at hw; cases hw

#print axioms frozen_rows

private theorem frozen_schedule_premises_sat :
    V2.D.ScheduleWellFormed (env (Fin 1)) frozenRun := by
  constructor
  · decide
  · decide +kernel
  · decide +kernel
  · intro ev hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with
      rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · intro ev hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with
      rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · intro x t hm
    simp only [List.mem_cons, List.mem_nil_iff, V2.Event.tick.injEq,
      or_false] at hm
    rcases hm with
      ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩
    · exact ⟨8, rfl⟩
    · exact ⟨9, rfl⟩
    · exact ⟨10, rfl⟩
    · exact ⟨11, rfl⟩
    · exact ⟨12, rfl⟩
    · exact ⟨13, rfl⟩
    · exact ⟨14, rfl⟩
    · exact ⟨15, rfl⟩
    · exact ⟨16, rfl⟩
  · intro x _ t ht _ hhor _
    obtain rfl : x = 0 := Subsingleton.elim _ _
    obtain ⟨k, hk⟩ := ht
    change t = (k : Time) * 2 at hk
    change t ≤ 32 at hhor
    rw [hk] at hhor
    have hb : k * 2 ≤ 32 := by exact_mod_cast hhor
    have hbound : k ≤ 16 := by omega
    subst t
    interval_cases k <;> simp

#print axioms frozen_schedule_premises_sat

private theorem frozen_batch_premises_sat :
    batchType frozenRun 1 2 aBlock bBlock ∧ batchType frozenRun 2 3 bBlock dBlock := by
  have hweight : electorate.weightOf (historyFaulty reads frozenRun) < electorate.q := by
    change (0 : Nat) < 1
    decide
  have receipt : TRowsReceipt core reads (env (Fin 1)) frozenRun timing (fun _ => []) 2 := by
    intro j x q a ha _ z _
    rcases frozen_rows j x q a ha with h | h | h | h
    all_goals
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Or.inl (by
        change wire _ ∈ [wire row0, wire row1, wire row2, wire row3]
        decide +kernel)
  have height := KitFG.Window.windowHeightLaws electorate cfg 2 (by decide)
  constructor
  · refine kmid_batchPrem_holder core reads obs timing (env (Fin 1)) frozenRun interface history
      electorate cfg 2 height rfl decodeProposal erase (fun X => X.rows.map wire)
      (fun _ => []) parentRead parentHeight (fun _ _ _ _ => true) (fun _ => true) 2
      frozen_schedule_premises_sat hweight ?_ {0} ?_ (by change (1 : Nat) ≤ 1; decide)
      (by decide) receipt 1 2 aBlock bBlock (by decide) ?_ 16 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) ?_ ?_ ?_ rfl (by intros; rfl)
      (by decide) (by constructor <;> decide +kernel) (preceq_refl _) (by decide +kernel) ?_
    · intro i i' _; exact Subsingleton.elim _ _
    · intro i _; change (0 : Fin 1) ∈ (Finset.univ : Finset (Fin 1)); decide
    · refine ⟨[wire row1], ?_, rfl⟩
      refine ⟨⟨⟨by decide, by decide⟩, prop bBlock, ⟨8, rfl, by decide +kernel⟩, rfl⟩,
        prop bBlock, ⟨8, rfl, by decide +kernel⟩, bBlock, rfl, rfl, rfl⟩
    · intro W hW
      change W ∈ ({.genesis, aBlock, bBlock} : Finset (FGBlock (Fin 1))) at hW
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl <;> decide +kernel
    · have ancestors (X : FGBlock (Fin 1))
          (hX : ∃ W ∈ ({.genesis, aBlock, bBlock} : Finset (FGBlock (Fin 1))), FGBlock.Preceq X W) :
          X ∈ ({.genesis, aBlock, bBlock} : Finset (FGBlock (Fin 1))) := by
        obtain ⟨W, hW, hXW⟩ := hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hW ⊢
        rcases hW with rfl | rfl | rfl
        all_goals
          simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
            decide_eq_true_eq] at hXW
          tauto
      intro W Z hW hZ he
      have hw := ancestors W hW
      have hz := ancestors Z hZ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw hz
      rcases hw with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl <;>
        simp_all [FGBlock.root, genesisRoot]
    · intro W hW row hr
      change W ∈ ({.genesis, aBlock, bBlock} : Finset (FGBlock (Fin 1))) at hW
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl
      · cases hr
      · have he : row = row0 := List.mem_singleton.mp hr
        subst row
        decide +kernel
      · have he : row = row1 := List.mem_singleton.mp hr
        subst row
        decide +kernel
    · intro i _
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact ⟨7, 1, wire row1, le_rfl, ⟨by decide, rfl, by decide +kernel⟩,
        ⟨rfl, 0, rfl, rfl⟩, rfl⟩
  · refine kmid_batchPrem_holder core reads obs timing (env (Fin 1)) frozenRun interface history
      electorate cfg 2 height rfl decodeProposal erase (fun X => X.rows.map wire)
      (fun _ => []) parentRead parentHeight (fun _ _ _ _ => true) (fun _ => true) 2
      frozen_schedule_premises_sat hweight ?_ {0} ?_ (by change (1 : Nat) ≤ 1; decide)
      (by decide) receipt 2 3 bBlock dBlock (by decide) ?_ 24 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) ?_ ?_ ?_ rfl (by intros; rfl)
      (by decide) (by constructor <;> decide +kernel) (preceq_refl _) (by decide +kernel) ?_
    · intro i i' _; exact Subsingleton.elim _ _
    · intro i _; change (0 : Fin 1) ∈ (Finset.univ : Finset (Fin 1)); decide
    · refine ⟨[wire row2], ?_, rfl⟩
      refine ⟨⟨⟨by decide, by decide⟩, prop dBlock, ⟨12, rfl, by decide +kernel⟩, rfl⟩,
        prop dBlock, ⟨12, rfl, by decide +kernel⟩, dBlock, rfl, rfl, rfl⟩
    · intro W hW
      change W ∈ ({.genesis, aBlock, bBlock, dBlock} : Finset (FGBlock (Fin 1))) at hW
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl | rfl <;> decide +kernel
    · have ancestors (X : FGBlock (Fin 1))
          (hX : ∃ W ∈ ({.genesis, aBlock, bBlock, dBlock} : Finset (FGBlock (Fin 1))),
            FGBlock.Preceq X W) :
          X ∈ ({.genesis, aBlock, bBlock, dBlock} : Finset (FGBlock (Fin 1))) := by
        obtain ⟨W, hW, hXW⟩ := hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hW ⊢
        rcases hW with rfl | rfl | rfl | rfl
        all_goals
          simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
            decide_eq_true_eq] at hXW
          tauto
      intro W Z hW hZ he
      have hw := ancestors W hW
      have hz := ancestors Z hZ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw hz
      rcases hw with rfl | rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl <;>
        simp_all [FGBlock.root, genesisRoot]
    · intro W hW row hr
      change W ∈ ({.genesis, aBlock, bBlock, dBlock} : Finset (FGBlock (Fin 1))) at hW
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl | rfl
      · cases hr
      · have he : row = row0 := List.mem_singleton.mp hr
        subst row
        decide +kernel
      · have he : row = row1 := List.mem_singleton.mp hr
        subst row
        decide +kernel
      · have he : row = row2 := List.mem_singleton.mp hr
        subst row
        decide +kernel
    · intro i _
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact ⟨11, 2, wire row2, le_rfl, ⟨by decide, rfl, by decide +kernel⟩,
        ⟨rfl, 0, rfl, rfl⟩, rfl⟩

#print axioms frozen_batch_premises_sat

private theorem frozen_premises_sat : ∃ m : middleType frozenRun,
    m.A₀ = aBlock ∧ m.B = bBlock ∧ m.U = bBlock ∧ m.X_D = dBlock ∧
    m.cD = 6 ∧ m.d = 2 := by
  have first : ∀ j x q a h t, HonestRowAt reads (env (Fin 1)) frozenRun timing j x q a →
      historyRowHeight reads history a = some h → 3 ≤ h → eventTime frozenRun j = some t →
      timing.action 2 ≤ t := by
    intro j x q a h t ha hh hy ht
    rcases frozen_rows j x q a ha with he | he | he | he
    all_goals
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      simp only [historyRowHeight, decode, Option.map_some,
        Option.getD_some, Option.some.injEq] at hh
      obtain rfl := hh.symm
      have htime : _ = t := Option.some.inj ht
      subst t
      first | omega | decide
  have second : ∀ j x q a h t, HonestRowAt reads (env (Fin 1)) frozenRun timing j x q a →
      historyRowHeight reads history a = some h → 4 ≤ h → eventTime frozenRun j = some t →
      timing.action 3 ≤ t := by
    intro j x q a h t ha hh hy ht
    rcases frozen_rows j x q a ha with he | he | he | he
    all_goals
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      simp only [historyRowHeight, decode, Option.map_some,
        Option.getD_some, Option.some.injEq] at hh
      obtain rfl := hh.symm
      have htime : _ = t := Option.some.inj ht
      subst t
      first | omega | decide
  have noFin : ∀ j x q a h t, HonestRowAt reads (env (Fin 1)) frozenRun timing j x q a →
      historyFinHeight reads history a = some h → 3 ≤ h → eventTime frozenRun j = some t →
      timing.action 3 ≤ t := by
    intro j x q a h t ha hh _ _
    rcases frozen_rows j x q a ha with he | he | he | he
    all_goals
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      cases hh
  have chains : ChainRowsBefore core (env (Fin 1)) frozenRun aBlock 14 ∧
      ChainRowsBefore core (env (Fin 1)) frozenRun bBlock 22 ∧
      ChainRowsBefore core (env (Fin 1)) frozenRun dBlock 30 := by
    refine ⟨?_, ?_, ?_⟩
    · intro W hp row hr
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hp
      rcases hp with rfl | rfl
      · exact ⟨0, 1, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · cases hr
    · intro W hp row hr
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, 17, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · exact ⟨0, 1, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · cases hr
    · intro W hp row hr
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨0, 25, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · exact ⟨0, 17, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · exact ⟨0, 1, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · cases hr
  have capB : ∀ i x W, i ≤ frozenRun.events.length → i ≤ afterTicksIdx frozenRun 22 →
      HeldAt core (env (Fin 1)) frozenRun i x W → (obs.height W).h ≤ 3 := by
    intro i x W _ hi ⟨hx, hW⟩
    have hx' : x = (0 : Fin 1) := Subsingleton.elim _ _
    have hib : i ≤ 12 := hi
    have ht : V2.D.Run.stateBefore (env (Fin 1)) frozenRun i x < 24 := by
      rcases hx' with rfl
      interval_cases i <;> decide +kernel
    change W ∈ (if V2.D.Run.stateBefore (env (Fin 1)) frozenRun i x < 16 then
      ({FGBlock.genesis, aBlock} :
        Finset (FGBlock (Fin 1))) else if V2.D.Run.stateBefore (env (Fin 1)) frozenRun i x < 24 then
      ({FGBlock.genesis, aBlock, bBlock} :
        Finset (FGBlock (Fin 1))) else ({FGBlock.genesis, aBlock, bBlock, dBlock} :
        Finset (FGBlock (Fin 1)))) at hW
    rw [ite_eq_left ht] at hW
    split_ifs at hW
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl <;> decide +kernel
  have capFinal : ∀ i x W, HeldAt core (env (Fin 1)) frozenRun i x W →
      (obs.height W).h ≤ 4 ∧ (obs.finality W).h_F < 3 := by
    intro i x W ⟨_, hW⟩
    change W ∈ (if V2.D.Run.stateBefore (env (Fin 1)) frozenRun i x < 16 then
      ({FGBlock.genesis, aBlock} :
        Finset (FGBlock (Fin 1))) else if V2.D.Run.stateBefore (env (Fin 1)) frozenRun i x < 24 then
      ({FGBlock.genesis, aBlock, bBlock} :
        Finset (FGBlock (Fin 1))) else ({FGBlock.genesis, aBlock, bBlock, dBlock} :
        Finset (FGBlock (Fin 1)))) at hW
    split_ifs at hW
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl | rfl <;> constructor <;> decide +kernel
  let m : middleType frozenRun := {
    A₀ := aBlock
    B := bBlock
    U := bBlock
    X_D := dBlock
    cD := 6
    d := 2
    opening := ⟨⟨by decide, by decide⟩, prop aBlock, ⟨4, rfl, by decide +kernel⟩, rfl⟩
    eraseA := rfl
    carrierA := ⟨prop aBlock, aBlock, 8, .genesis,
      ⟨4, rfl, by decide +kernel⟩, rfl, rfl, by decide +kernel, by decide +kernel, rfl⟩
    carrierB := ⟨prop bBlock, bBlock, 16, aBlock,
      ⟨8, rfl, by decide +kernel⟩, rfl, rfl, by decide +kernel, by decide +kernel, by decide⟩
    carrierD := ⟨prop dBlock, dBlock, 24, bBlock,
      ⟨12, rfl, by decide +kernel⟩, rfl, rfl, by decide +kernel, by decide +kernel, by decide⟩
    honestB := ⟨⟨by decide, by decide⟩, prop bBlock, ⟨8, rfl, by decide +kernel⟩, rfl⟩
    honestD := ⟨⟨by decide, by decide⟩, prop dBlock, ⟨12, rfl, by decide +kernel⟩, rfl⟩
    slotA := rfl
    slotB := rfl
    slotD := rfl
    earlySlot := ⟨by decide, by decide⟩
    heightA := block_premises_sat.1
    highA := by decide
    heightB := block_premises_sat.2.1
    entryB := block_premises_sat.2.2.1
    freshEntry := ⟨by decide +kernel, by decide +kernel⟩
    strictAU := ⟨by decide, by decide⟩
    pathUB := preceq_refl _
    freshSlot := ⟨by decide, by decide⟩
    parentAB := preceq_refl _
    parentBD := preceq_refl _
    sourceA := by
      intro x hx
      have hx' : x = (0 : Fin 1) := Subsingleton.elim _ _
      rcases hx' with rfl
      decide +kernel
    sourceB := by
      intro x hx
      have hx' : x = (0 : Fin 1) := Subsingleton.elim _ _
      rcases hx' with rfl
      decide +kernel
    serviceD := ⟨fun _ x _ _ => rfl, fun _ x _ _ => ⟨rfl, fun _ _ => rfl⟩⟩
    heightD := by decide +kernel
    justifiedD := by decide +kernel
    justifiedHeightD := by decide +kernel
    pendingD := by decide +kernel
    retainedD := block_premises_sat.2.2.2.2.2.2.2
    noFirstHeight := first
    noSecondHeight := second
    noEarlyFinality := noFin
    chainA := chains.1
    chainB := chains.2.1
    chainD := chains.2.2
    freshD := ⟨frozen_schedule_premises_sat, by change (0 : Nat) < 1; decide,
      30, le_rfl, chains.2.2, second, noFin⟩
    noMixedD := by
      intro W hp
      change FGBlock.Preceq W bBlock at hp
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hp
      rcases hp with rfl | rfl | rfl <;> unfold MixedCross <;> decide +kernel
    batchB := fun _ => frozen_batch_premises_sat.1
    batchD := fun _ => frozen_batch_premises_sat.2
    targetsB := by
      intro i _
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact ⟨11, wire row2, ⟨by decide, rfl, by decide +kernel⟩,
        ⟨rfl, 0, rfl, rfl⟩, rfl⟩
    actionsInRun := by decide
    capThroughBAction := capB
    capThroughFinalAction := fun i x W _ _ h => (capFinal i x W h).1
    finalityThroughFinalAction := fun i x W _ _ h => (capFinal i x W h).2
    heldDAtFinalAction := by
      intro x hx
      have hx' : x = (0 : Fin 1) := Subsingleton.elim _ _
      rcases hx' with rfl
      decide +kernel
    heldAAtEnd := by
      intro x hx
      have hx' : x = (0 : Fin 1) := Subsingleton.elim _ _
      rcases hx' with rfl
      decide +kernel
  }
  exact ⟨m, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms frozen_premises_sat

private theorem frozen_action_premises_sat : ∃ m : middleType frozenRun,
    (m.A₀ = aBlock ∧ m.B = bBlock ∧ m.U = bBlock ∧ m.X_D = dBlock ∧
      m.cD = 6 ∧ m.d = 2) ∧
    KernelActionSupplyFG_W core reads obs timing (env (Fin 1)) frozenRun interface
      history electorate m := by
  obtain ⟨m, hA, hB, hU, hD, hc, hd⟩ := frozen_premises_sat
  refine ⟨m, ⟨hA, hB, hU, hD, hc, hd⟩, ?_⟩
  constructor
  · intro x nd hnd
    obtain rfl : x = 0 := Subsingleton.elim _ _
    change some 30 = some nd at hnd
    obtain rfl := Option.some.inj hnd
    decide +kernel
  · intro x _
    obtain rfl : x = 0 := Subsingleton.elim _ _
    rw [hc, hD]
    constructor
    · intro _; exact ⟨30, by decide +kernel, rfl⟩
    · intro h; change (6 : Nat) < 6 at h; omega
  · intro x nd _ hnd
    obtain rfl : x = 0 := Subsingleton.elim _ _
    change some 30 = some nd at hnd
    obtain rfl := Option.some.inj hnd
    exact ⟨dBlock, rfl, by decide⟩
  · intro x nd _ _ H hH
    have he : dBlock = H := Option.some.inj hH
    subst H
    rw [hD]
    decide

#print axioms frozen_action_premises_sat

private abbrev frozenOldType :=
  KernelMiddleWitness_W core reads obs timing (env (Fin 1)) frozenRun interface history
    electorate decodeProposal erase (fun X => X.rows.map wire) (fun _ => []) parentRead
    parentHeight (fun _ _ _ _ => true) makeFG (fun _ => true) (ac (Fin 1)) cfg 2 2 point pt
    (erase aBlock)

private theorem frozen_bridge :
    (Nonempty frozenOldType ↔ Nonempty (middleType frozenRun)) ∧
    ∃ m : frozenOldType, ∃ h : middleType frozenRun,
      (m.A₀ = h.A₀ ∧ m.B = h.B ∧ m.U = h.U ∧ m.X_D = h.X_D ∧
        m.cD = h.cD ∧ m.d = h.d) ∧
      (m.X_D = dBlock ∧ m.cD = 6 ∧ h.X_D = dBlock ∧ h.cD = 6) ∧
      KernelActionSupply_W core reads obs timing (env (Fin 1)) frozenRun interface
        history electorate m ∧
      KernelActionSupplyFG_W core reads obs timing (env (Fin 1)) frozenRun interface
        history electorate h := by
  have bridge := kernel_middle_holder_frozen_iff core reads obs timing (env (Fin 1))
    frozenRun interface history electorate decodeProposal erase (fun X => X.rows.map wire)
    (fun _ => []) parentRead parentHeight (fun _ _ _ _ => true) makeFG (fun _ => true)
    (ac (Fin 1)) cfg 2 2 point pt (erase aBlock) (Equiv.refl (Fin 1))
    (fun _ => Subsingleton.elim _ _)
  obtain ⟨h₀, ⟨_, _, _, hD, hc, _⟩, act₀⟩ := frozen_action_premises_sat
  obtain ⟨m, paired₀⟩ := bridge.2.2 h₀
  have oldAct := (kernel_action_holder_frozen_iff
    (m := m) (h := h₀) (selected := paired₀)).mpr act₀
  obtain ⟨h, paired⟩ := bridge.2.1 m
  have newAct := (kernel_action_holder_frozen_iff
    (m := m) (h := h) (selected := paired)).mp oldAct
  have hmD : m.X_D = dBlock := paired₀.2.2.2.1.trans hD
  have hmc : m.cD = 6 := paired₀.2.2.2.2.1.trans hc
  exact ⟨bridge.1, m, h, paired,
    ⟨hmD, hmc, paired.2.2.2.1.symm.trans hmD, paired.2.2.2.2.1.symm.trans hmc⟩,
    oldAct, newAct⟩

#print axioms frozen_bridge

private abbrev twoProtocol : V2.ProtocolSpecD Unit where
  State := Time
  Label := Nat
  Duty := Time
  signLabel t := if t % 8 = 6 then 0 else t.toNat + 1
  seats _ := 2
  Payload := FGBlock (Fin 1) ⊕ Row (Fin 1)
  Durable := Time
  init := 0
  clock _ t := t
  actTime := id
  duties t := [t]
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; simp
  act _ t _ := if t = 6 then some (.inr row0) else
    if t = 14 then some (.inr row1) else if t = 22 then some (.inr row2) else
    if t = 30 then some (.inr row3) else if t = 8 then some (.inl aBlock) else
    if t = 16 then some (.inl bBlock) else if t = 24 then some (.inl dBlock) else none
  gossip _ _ := []
  process st _ := st
  selfVisible _ := true
  recordOwn st _ := st
  durable := id
  restore st _ := st
  wellFormed _ := true
  depsPresent _ _ := true
  processed _ _ := false
  excludes _ _ := false
  handles _ _ _ := False
  carries _ _ := False
-- Pure-data signer control: both seats have distinct owners; the second wire is valid.
private abbrev twoReads : FGSafetyReads twoProtocol 2 (Fin 2) where
  proposalErase _ := none
  proposalRows _ := []
  encode i := ⟨.seat 0 i, .inr row0⟩
  decode i := some ⟨i, .vote 1 genesisRoot false, none⟩
  decodeObject o := match o.auth with
    | .none => none
    | .seat _ i => some ⟨i, .vote 1 genesisRoot false, none⟩
  fgLabel := 0
  fgSeats := Equiv.refl _
  record _ := RecordOnce.initial
  inputs _ := (none, ⟨0, genesisRoot, 0⟩)
  enabled _ := true
  finalizedOut _ := .genesis
private abbrev twoRun : V2.D.Run Nat twoProtocol where
  honest := {7, 9}
  horizon := 32
  events := []
  seatOf _ i := if i = 0 then 9 else 11
  input _ _ := ()
private abbrev twoSigner (i : Fin 2) : Option (Fin 2) := some i

private theorem two_seat_premises_sat :
    Function.Injective (safetyHolder twoReads twoRun) ∧
    safetyHolder twoReads twoRun 0 = 9 ∧ safetyHolder twoReads twoRun 1 = 11 ∧
    RowComplete twoReads twoRun twoSigner (fun _ => true) 9 0 ∧
    (fun _ : Fin 2 => true) 1 = true ∧ twoSigner 1 = some 1 ∧
    twoReads.decode 1 = some ⟨1, .vote 1 genesisRoot false, none⟩ := by
  refine ⟨?_, rfl, rfl, ⟨rfl, 0, rfl, rfl⟩, rfl, rfl, rfl⟩
  intro i j hi
  fin_cases i <;> fin_cases j <;> simp_all [safetyHolder, twoReads]

#print axioms two_seat_premises_sat

private theorem two_seat_mismatched_signer :
    ¬ RowComplete twoReads twoRun twoSigner (fun _ => true) 9 1 := by
  intro h
  obtain ⟨i, hi, holder⟩ := h.2
  have he : (1 : Fin 2) = i := Option.some.inj hi
  subst i
  change (11 : Nat) = 9 at holder
  omega

#print axioms two_seat_mismatched_signer

end AvailableChain.FGCompose.Tests.PopulationMiddle
end
