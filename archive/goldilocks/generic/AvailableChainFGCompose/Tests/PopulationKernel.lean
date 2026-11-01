module
public import AvailableChainFGCompose.Proofs.Finality.RowsPrem
public import AvailableChainFGCompose.Proofs.Population.Kernel
public import AvailableChainFGCompose.Proofs.Population.KernelBridges

set_option linter.privateModule false
noncomputable section
public section

/-! Generic ordinary event-fold controls for the full selected middle and action records.
The mixed run has both honest receivers; FG label 0 belongs only to holder 9. -/
namespace AvailableChain.FGCompose.Tests.PopulationKernel
open AvailableChain.SimplexFG AvailableChain.KitFG

private abbrev electorate : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private abbrev cfg : FGConfig := ⟨4⟩
private abbrev row0 : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private abbrev aBlock : FGBlock (Fin 1) := .node .genesis 2 ⟨1⟩ 0 [row0]
private abbrev row1 : Row (Fin 1) := ⟨0, .vote 2 aBlock.root false, none⟩
private abbrev bBlock : FGBlock (Fin 1) := .node aBlock 4 ⟨2⟩ 0 [row1]
private abbrev row2 : Row (Fin 1) := ⟨0, .vote 3 bBlock.root false, none⟩
private abbrev dBlock : FGBlock (Fin 1) := .node bBlock 6 ⟨3⟩ 0 [row2]
private abbrev row3 : Row (Fin 1) := ⟨0, .vote 4 dBlock.root false, some ⟨3, bBlock.root⟩⟩
private abbrev xBlock : FGBlock (Fin 1) := .node dBlock 8 ⟨4⟩ 0 [row3]
private abbrev storeA := SimplexFG.Window.on_block electorate cfg 2 Store.init aBlock
private abbrev storeB := SimplexFG.Window.on_block electorate cfg 2 storeA bBlock
private abbrev storeD := SimplexFG.Window.on_block electorate cfg 2 storeB dBlock
private abbrev storeX := SimplexFG.Window.on_block electorate cfg 2 storeD xBlock
private abbrev staged (t : Time) : Store (Fin 1) :=
  { (if t < 16 then storeA else if t < 24 then storeB else if t < 32 then storeD else storeX)
    with TF := if t < 16 then {.genesis, aBlock} else
      if t < 24 then {.genesis, aBlock, bBlock} else
      if t < 32 then {.genesis, aBlock, bBlock, dBlock} else
      {.genesis, aBlock, bBlock, dBlock, xBlock} }
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
  clock st t := max st t
  actTime := id
  duties t := [t]
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; simp
  act _ t _ := if t = 6 then some (.inr row0) else
    if t = 14 then some (.inr row1) else if t = 22 then some (.inr row2) else
    if t = 30 then some (.inr row3) else if t = 8 then some (.inl aBlock) else
    if t = 16 then some (.inl bBlock) else if t = 24 then some (.inl dBlock) else
    if t = 32 then some (.inl xBlock) else none
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
  inputs t := (some (if t < 8 then .genesis else if t < 16 then aBlock else
      if t < 24 then bBlock else dBlock),
    ⟨3, bBlock.root, 0⟩)
  enabled t := decide (t % 8 = 6)
  finalizedOut _ := .genesis
private abbrev source (t : Time) : FGBlock (Fin 1) :=
  if t < 8 then .genesis else if t < 16 then aBlock else
    if t < 24 then bBlock else dBlock
private abbrev core : FGCoreReads protocol 1 Unit Unit protocol.Object where
  core t := ⟨(), staged t, [], [wire row0, wire row1, wire row2, wire row3]⟩
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
  horizon := 33
  events := [.tick 9 0, .tick 7 0, .tick 9 2, .tick 7 2, .tick 9 4, .tick 7 4, .tick 9 6,
    .tick 7 6, .tick 9 8, .tick 7 8, .tick 9 10, .tick 7 10, .tick 9 12, .tick 7 12, .tick 9 14,
    .tick 7 14, .tick 9 16, .tick 7 16, .tick 9 18, .tick 7 18, .tick 9 20, .tick 7 20,
    .tick 9 22, .tick 7 22, .tick 9 24, .tick 7 24, .tick 9 26, .tick 7 26, .tick 9 28,
    .tick 7 28, .tick 9 30, .tick 7 30, .tick 9 32, .tick 7 32]
  seatOf label _ := if label = 0 then 9 else 7
  input _ _ := ()
private abbrev frozenRun : V2.D.Run (Fin 1) protocol where
  honest := Finset.univ
  horizon := 33
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
  if Q = erase aBlock then aBlock else if Q = erase bBlock then bBlock else
    if Q = erase dBlock then dBlock else xBlock
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
  · have he : 7 = x ∧ (32 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (32 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    omega

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
    change t ≤ 33 at hhor
    rw [hk] at hhor
    have hb : k * 2 ≤ 32 := by
      have : (k : Int) * 2 ≤ 33 := by simpa using hhor
      omega
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
    intro j x q a h t ha hh _ ht
    rcases exact_rows j x q a ha with he | he | he | he
    all_goals
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      cases hh
      all_goals exact le_of_eq (Option.some.inj ht)
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
        Finset (FGBlock (Fin 1))) else if V2.D.Run.stateBefore (env Nat) run i x < 32 then
      ({FGBlock.genesis, aBlock, bBlock, dBlock} :
        Finset (FGBlock (Fin 1))) else ({FGBlock.genesis, aBlock, bBlock, dBlock, xBlock} :
        Finset (FGBlock (Fin 1)))) at hW
    rw [ite_eq_left ht] at hW
    split_ifs at hW
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl <;> decide +kernel
  have capFinal : ∀ i x W, i ≤ afterTicksIdx run 30 → HeldAt core (env Nat) run i x W →
      (obs.height W).h ≤ 4 ∧ (obs.finality W).h_F < 3 := by
    intro i x W hi ⟨hx, hW⟩
    have ht : V2.D.Run.stateBefore (env Nat) run i x < 32 := by
      have hib : i ≤ 32 := hi
      have hx : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx with rfl | rfl <;> interval_cases i <;> decide +kernel
    change W ∈ (if V2.D.Run.stateBefore (env Nat) run i x < 16 then
      ({FGBlock.genesis, aBlock} :
        Finset (FGBlock (Fin 1))) else if V2.D.Run.stateBefore (env Nat) run i x < 24 then
      ({FGBlock.genesis, aBlock, bBlock} :
        Finset (FGBlock (Fin 1))) else if V2.D.Run.stateBefore (env Nat) run i x < 32 then
      ({FGBlock.genesis, aBlock, bBlock, dBlock} :
        Finset (FGBlock (Fin 1))) else ({FGBlock.genesis, aBlock, bBlock, dBlock, xBlock} :
        Finset (FGBlock (Fin 1)))) at hW
    rw [ite_eq_left ht] at hW
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
    capThroughFinalAction := fun i x W _ hi h => (capFinal i x W hi h).1
    finalityThroughFinalAction := fun i x W _ hi h => (capFinal i x W hi h).2
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

set_option maxRecDepth 2048 in
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

private abbrev blocks : Finset (FGBlock (Fin 1)) := {.genesis, aBlock, bBlock, dBlock, xBlock}

private theorem store_premises_sat : ∀ t,
    FGStoreInvariant obs.height obs.finality (staged t) := by
  have closed : ∀ B ∈ blocks, B.parent ∈ blocks := by decide
  have roots (st : Store (Fin 1)) (B : FGBlock (Fin 1))
      (hst : st.TF ⊆ blocks) (hB : B ∈ blocks) : StoreStepRoots st B := by
    have sub : insert B st.TF ⊆ blocks := Finset.insert_subset hB hst
    intro X Y ⟨W, hW, hX⟩ ⟨Z, hZ, hY⟩ hr
    have hx := KitFG.ancestor_closed_of_parent_closed blocks closed W (sub hW) X hX
    have hy := KitFG.ancestor_closed_of_parent_closed blocks closed Z (sub hZ) Y hY
    exact (by decide : ∀ X ∈ blocks, ∀ Y ∈ blocks, X.root = Y.root → X = Y) X hx Y hy hr
  have invA : FGStoreInvariant obs.height obs.finality storeA :=
    KitFG.Window.windowStoreInvariant_on_block electorate cfg 2
      (by change ¬ (1 ≤ 0); decide) (by decide) _ _
      (KitFG.Window.windowStoreInvariant_init electorate cfg 2)
      (roots _ _ (by decide) (by decide))
  have invB : FGStoreInvariant obs.height obs.finality storeB :=
    KitFG.Window.windowStoreInvariant_on_block electorate cfg 2
      (by change ¬ (1 ≤ 0); decide) (by decide) _ _ invA
      (roots _ _ (by decide +kernel) (by decide))
  have invD : FGStoreInvariant obs.height obs.finality storeD :=
    KitFG.Window.windowStoreInvariant_on_block electorate cfg 2
      (by change ¬ (1 ≤ 0); decide) (by decide) _ _ invB
      (roots _ _ (by decide +kernel) (by decide))
  have invX : FGStoreInvariant obs.height obs.finality storeX :=
    KitFG.Window.windowStoreInvariant_on_block electorate cfg 2
      (by change ¬ (1 ≤ 0); decide) (by decide) _ _ invD
      (roots _ _ (by decide +kernel) (by decide))
  intro t
  unfold staged
  split_ifs
  · have he : { storeA with TF := {.genesis, aBlock} } = storeA := by
      have ht : {.genesis, aBlock} = storeA.TF := by decide +kernel
      rw [ht]
    rw [he]; exact invA
  · have he : { storeB with TF := {.genesis, aBlock, bBlock} } = storeB := by
      have ht : {.genesis, aBlock, bBlock} = storeB.TF := by decide +kernel
      rw [ht]
    rw [he]; exact invB
  · have he : { storeD with TF := {.genesis, aBlock, bBlock, dBlock} } = storeD := by
      have ht : {.genesis, aBlock, bBlock, dBlock} = storeD.TF := by decide +kernel
      rw [ht]
    rw [he]; exact invD
  · have he : { storeX with TF := {.genesis, aBlock, bBlock, dBlock, xBlock} } = storeX := by
      have ht : {.genesis, aBlock, bBlock, dBlock, xBlock} = storeX.TF := by decide +kernel
      rw [ht]
    rw [he]; exact invX

#print axioms store_premises_sat

private theorem durable_premises_sat : FGFinalityDurableLaws core := by
  have fin (t : Time) : (staged t).F = if t < 32 then .genesis else bBlock := by
    unfold staged
    split_ifs <;> first | rfl | decide +kernel | linarith
  have mono (s t : Time) (h : s ≤ t) : FGBlock.Preceq (staged s).F (staged t).F := by
    rw [fin s, fin t]
    split_ifs <;> first | exact preceq_refl _ | exact genesis_preceq _ | linarith
  refine ⟨fun X => ⟨?_, fun _ _ h => h, fun _ _ h => h⟩, fun _ _ => rfl⟩
  intro st t h
  exact KitFG.preceq_trans h (mono st (max st t) (le_max_left _ _))

#print axioms durable_premises_sat

private abbrev ready (i : Nat) (x : Nat) (W : FGBlock (Fin 1)) (t : Time) : Prop :=
  ((i = 32 ∧ x = 9) ∨ (i = 33 ∧ x = 7)) ∧ W = xBlock ∧ t = 32

-- Both actual terminal ticks run exactly the window insertion/update required by the owner.
set_option maxRecDepth 2048 in
private theorem acceptance_effect_premises_sat :
    AcceptStep_W core (env Nat) run electorate cfg 2 ready ∧
    ready 32 9 xBlock 32 ∧ ready 33 7 xBlock 32 ∧
    (SimplexFG.Window.derive electorate cfg 2 xBlock).F = bBlock := by
  refine ⟨?_, by decide, by decide, by decide +kernel⟩
  rintro i x W t _ ⟨h, rfl, rfl⟩
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    constructor
    · change Store.mk _ _ _ _ _ = Store.mk _ _ _ _ _
      simp only [Store.mk.injEq]
      refine ⟨?_, rfl, rfl, rfl, rfl⟩
      decide +kernel
    · decide +kernel

#print axioms acceptance_effect_premises_sat

private def selectedDelivery : BlockDelivery_W core (env Nat) run ready xBlock bBlock 32
    (kernelDeadlineW timing 2 3) where
  selected x _ := if x = 9 then ⟨32, 32⟩ else ⟨33, 32⟩
  witness x hx := by
    have hx : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx with rfl | rfl
    all_goals
      refine ⟨rfl, by decide, Or.inr ⟨le_rfl, ?_⟩⟩
      decide

set_option maxRecDepth 2048 in
private theorem receipt_premises_sat :
    Nonempty (AcceptPrem_W core (env Nat) run electorate cfg 2 ready xBlock bBlock 32
      (kernelDeadlineW timing 2 3)) := by
  refine ⟨⟨schedule_premises_sat, ?_, selectedDelivery, ?_, by decide⟩⟩
  · rw [acceptance_effect_premises_sat.2.2.2]
    exact preceq_refl _
  · constructor
    · intro x hx
      dsimp only
      intro _
      have hx : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx with rfl | rfl
      all_goals
        change FGBlock.Preceq .genesis bBlock ∨ FGBlock.Preceq bBlock .genesis
        exact Or.inl (genesis_preceq _)
    · intro x hx
      dsimp only
      intro _ _
      have hx : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx with rfl | rfl
      all_goals
        change FGBlock.Preceq bBlock xBlock ∨ (3 : Nat) < (obs.height xBlock).h_j
        exact Or.inl (by decide)
    · intro x hx
      dsimp only
      intro _ _
      have hx : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx with rfl | rfl <;> dsimp only [selectedDelivery] <;> decide +kernel

#print axioms receipt_premises_sat

private theorem target_supplier_premises_sat :
    ∀ i : Fin 1, safetyHolder reads run i ∈ run.honest → ∀ r C,
      actionSourceFG core (env Nat) run timing (safetyHolder reads run i) r = some (some C) →
      point.reset.M + 1 ≤ (obs.height C).h →
      (env Nat).awake (safetyHolder reads run i) (timing.action r) = true →
      ∃ j rSent a, rSent ≤ r ∧
        HonestRowAt reads (env Nat) run timing j (safetyHolder reads run i) rSent a ∧
        RowComplete reads run history.signer (fun _ => true) (safetyHolder reads run i) a ∧
        history.heightPair a = .vote (obs.height C).h (obs.height C).T_h.root false := by
  intro i _ r C hs _ _
  obtain rfl : i = 0 := Subsingleton.elim _ _
  change actionSourceFG core (env Nat) run timing 9 r = some (some C) at hs
  have bound : r ≤ 3 := by
    unfold actionSourceFG postClock preTick at hs
    cases hi : V2.D.Run.tickIdx? run 9 (timing.action r) with
    | none => simp only [hi, Option.map_none] at hs; contradiction
    | some j =>
      have he := V2.D.Run.tickIdx?_spec hi
      have ht := (schedule_premises_sat.in_horizon _ (List.mem_of_getElem? he)).2
      change 4 * (r * 2 : Nat) + 6 ≤ (33 : Int) at ht
      omega
  interval_cases r
  all_goals
    have hc : _ = C := Option.some.inj (Option.some.inj hs)
    subst C
  · exact ⟨6, 0, wire row0, le_rfl, ⟨by decide, rfl, by decide +kernel⟩,
      ⟨rfl, 0, rfl, rfl⟩, by decide +kernel⟩
  · exact ⟨14, 1, wire row1, le_rfl, ⟨by decide, rfl, by decide +kernel⟩,
      ⟨rfl, 0, rfl, rfl⟩, by decide +kernel⟩
  · exact ⟨22, 2, wire row2, le_rfl, ⟨by decide, rfl, by decide +kernel⟩,
      ⟨rfl, 0, rfl, rfl⟩, by decide +kernel⟩
  · exact ⟨30, 3, wire row3, le_rfl, ⟨by decide, rfl, by decide +kernel⟩,
      ⟨rfl, 0, rfl, rfl⟩, by decide +kernel⟩

#print axioms target_supplier_premises_sat

private theorem opening_premises_sat :
    HonestProposal (env Nat) run interface 2 (erase aBlock) ∧
    ∀ A, HonestProposal (env Nat) run interface 2 A → A = erase aBlock := by
  refine ⟨⟨⟨by decide, by decide⟩, prop aBlock, ⟨9, rfl, by decide +kernel⟩, rfl⟩, ?_⟩
  intro A ⟨_, o, ⟨j, hj, ho⟩, hb⟩
  have he : run.events[j]? = some (.tick 7 8) := hj
  have idx : j = 9 := by
    have hjlt : j < 34 := (List.getElem?_eq_some_iff.mp he).1
    have unique : ∀ k : Fin 34, run.events[k.val]? = some (.tick 7 8) → k.val = 9 := by
      decide +kernel
    exact unique ⟨j, hjlt⟩ he
  subst j
  change o ∈ [prop aBlock] at ho
  obtain rfl := List.mem_singleton.mp ho
  exact (Option.some.inj hb).symm

#print axioms opening_premises_sat

-- Isolated old supplier failure: its source antecedent is active at honest nonholder 7.
private theorem old_target_supplier_impossible :
    ¬ (∀ x ∈ run.honest, ∀ r C,
      actionSourceFG core (env Nat) run timing x r = some (some C) →
      point.reset.M + 1 ≤ (obs.height C).h → (env Nat).awake x (timing.action r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt reads (env Nat) run timing j x rSent a ∧
        RowComplete reads run history.signer (fun _ => true) x a ∧
        history.heightPair a = .vote (obs.height C).h (obs.height C).T_h.root false) := by
  intro old
  obtain ⟨_, _, _, _, _, complete, _⟩ := old 7 (by decide) 1 aBlock
    (by decide +kernel) (by decide +kernel) rfl
  obtain ⟨i, _, hi⟩ := complete.2
  change (9 : Nat) = 7 at hi
  omega

#print axioms old_target_supplier_impossible

private abbrev honestSlot (s : Slot) : Prop := s = 2 ∨ s = 4 ∨ s = 6 ∨ s = 8

private theorem kernel_population_premises_sat :
    KernelPrem_W timing 2 run.horizon point pt honestSlot electorate.q
      (electorate.weightOf (Finset.univ \ historyFaulty reads run)) cfg.timeoutDelay 2 ∧
    KernelRunFacts reads (env Nat) run electorate 2 ∧
    ∃ m : middleType run,
      KernelActionSupplyFG_W core reads obs timing (env Nat) run interface history
        electorate m := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · exact ⟨by decide⟩
    · rw [Gen.Pure.FGoodE_W_def]
      exact ⟨by decide, by decide, ⟨6, by decide, by decide, by decide⟩, by decide⟩
    · decide
    · decide
    · decide
    · rfl
    · decide
  · constructor
    · exact schedule_premises_sat
    · decide
    · exact le_rfl
    · intro i j _; exact Subsingleton.elim _ _
    · intro x hx t ht hhor; rfl
  · obtain ⟨m, _, act⟩ := action_premises_sat
    exact ⟨m, act⟩

#print axioms kernel_population_premises_sat

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
  · have he : (0 : Fin 1) = x ∧ (32 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (32 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    omega

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
    change t ≤ 33 at hhor
    rw [hk] at hhor
    have hb : k * 2 ≤ 32 := by
      have : (k : Int) * 2 ≤ 33 := by simpa using hhor
      omega
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
    intro j x q a h t ha hh _ ht
    rcases frozen_rows j x q a ha with he | he | he | he
    all_goals
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      cases hh
      all_goals exact le_of_eq (Option.some.inj ht)
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
        Finset (FGBlock (Fin 1))) else if V2.D.Run.stateBefore (env (Fin 1)) frozenRun i x < 32 then
      ({FGBlock.genesis, aBlock, bBlock, dBlock} :
        Finset (FGBlock (Fin 1))) else ({FGBlock.genesis, aBlock, bBlock, dBlock, xBlock} :
        Finset (FGBlock (Fin 1)))) at hW
    rw [ite_eq_left ht] at hW
    split_ifs at hW
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl <;> decide +kernel
  have capFinal : ∀ i x W, i ≤ afterTicksIdx frozenRun 30 →
      HeldAt core (env (Fin 1)) frozenRun i x W →
      (obs.height W).h ≤ 4 ∧ (obs.finality W).h_F < 3 := by
    intro i x W hi ⟨hx, hW⟩
    have ht : V2.D.Run.stateBefore (env (Fin 1)) frozenRun i x < 32 := by
      have hib : i ≤ 16 := hi
      obtain rfl : x = (0 : Fin 1) := Subsingleton.elim _ _
      interval_cases i <;> decide +kernel
    change W ∈ (if V2.D.Run.stateBefore (env (Fin 1)) frozenRun i x < 16 then
      ({FGBlock.genesis, aBlock} :
        Finset (FGBlock (Fin 1))) else if V2.D.Run.stateBefore (env (Fin 1)) frozenRun i x < 24 then
      ({FGBlock.genesis, aBlock, bBlock} :
        Finset (FGBlock (Fin 1))) else if V2.D.Run.stateBefore (env (Fin 1)) frozenRun i x < 32 then
      ({FGBlock.genesis, aBlock, bBlock, dBlock} :
        Finset (FGBlock (Fin 1))) else ({FGBlock.genesis, aBlock, bBlock, dBlock, xBlock} :
        Finset (FGBlock (Fin 1)))) at hW
    rw [ite_eq_left ht] at hW
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
    capThroughFinalAction := fun i x W _ hi h => (capFinal i x W hi h).1
    finalityThroughFinalAction := fun i x W _ hi h => (capFinal i x W hi h).2
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

set_option maxRecDepth 2048 in
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

private theorem reflection_premises_sat (A B : FGBlock (Fin 1))
    (h : Block.Preceq (erase A) (erase B)) : FGBlock.Preceq A B := by
  have inj : Function.Injective erase := by
    intro X
    induction X with
    | genesis => intro Y he; cases Y <;> simp_all [erase]
    | node p s r x rs ih =>
      intro Y he
      cases Y with
      | genesis => simp [erase] at he
      | node q t u y ts =>
        simp only [erase, Block.node.injEq] at he
        obtain ⟨hp, hs, hr, hb⟩ := he
        obtain ⟨hx, hrows⟩ := encFGBody_inj hb
        cases ih hp
        cases hs
        cases hr
        cases hx
        cases hrows
        rfl
  induction B with
  | genesis =>
    have he : erase A = erase .genesis := of_decide_eq_true h
    exact inj he ▸ preceq_refl _
  | node P slot root app rows ih =>
    change (decide (erase A = erase (.node P slot root app rows)) ||
      Block.preceq (erase A) (erase P)) = true at h
    rw [Bool.or_eq_true] at h
    rcases h with he | hp
    · exact inj (of_decide_eq_true he) ▸ preceq_refl _
    · exact preceq_node_of_preceq slot root app rows (ih hp)

#print axioms reflection_premises_sat

private theorem old_middle_impossible (m : KernelMiddleWitness_W core reads obs timing
    (env Nat) run interface history electorate decodeProposal erase (fun X => X.rows.map wire)
    (fun _ => []) parentRead parentHeight (fun _ _ _ _ => true) makeFG (fun _ => true)
    (ac Nat) cfg 2 2 point pt (erase aBlock)) : False := by
  obtain ⟨_, _, _, complete, _⟩ := m.targetsB 7 (by decide)
  obtain ⟨i, _, hi⟩ := complete.2
  change (9 : Nat) = 7 at hi
  omega

#print axioms old_middle_impossible

private abbrev frozenOldType :=
  KernelMiddleWitness_W core reads obs timing (env (Fin 1)) frozenRun interface history
    electorate decodeProposal erase (fun X => X.rows.map wire) (fun _ => []) parentRead
    parentHeight (fun _ _ _ _ => true) makeFG (fun _ => true) (ac (Fin 1))
    cfg 2 2 point pt (erase aBlock)


set_option maxRecDepth 2048 in
private theorem frozen_bridge_premises_sat :
    (Nonempty frozenOldType ↔ Nonempty (middleType frozenRun)) ∧
    ∃ m : frozenOldType, ∃ h : middleType frozenRun,
      (m.A₀ = h.A₀ ∧ m.B = h.B ∧ m.U = h.U ∧
        m.X_D = h.X_D ∧ m.cD = h.cD ∧ m.d = h.d) ∧
      KernelActionSupply_W core reads obs timing (env (Fin 1)) frozenRun interface
        history electorate m ∧
      KernelActionSupplyFG_W core reads obs timing (env (Fin 1)) frozenRun interface
        history electorate h ∧
      (∀ x ∈ frozenRun.honest, ∃ H, core.finalityHead 30 = some H ∧
        FGBlock.Preceq m.X_D H ∧ (obs.height H).h = m.d + 2 ∧
        (obs.height H).J = m.U ∧ (obs.height H).h_j = m.d + 1) ∧
      (∀ x ∈ frozenRun.honest, ∃ H, core.finalityHead 30 = some H ∧
        FGBlock.Preceq h.X_D H ∧ (obs.height H).h = h.d + 2 ∧
        (obs.height H).J = h.U ∧ (obs.height H).h_j = h.d + 1) := by
  have bridge := kernel_middle_holder_frozen_iff core reads obs timing (env (Fin 1))
    frozenRun interface history electorate decodeProposal erase (fun X => X.rows.map wire)
    (fun _ => []) parentRead parentHeight (fun _ _ _ _ => true) makeFG (fun _ => true)
    (ac (Fin 1)) cfg 2 2 point pt (erase aBlock) (Equiv.refl _) (by
      intro i; exact Subsingleton.elim _ _)
  obtain ⟨h, _, act⟩ := frozen_action_premises_sat
  obtain ⟨m, selected⟩ := bridge.2.2 h
  have oldAct := (kernel_action_holder_frozen_iff
    (m := m) (h := h) (selected := selected)).mpr act
  have newHead := rowsPrem_pending_head_holder h
    (KitFG.Window.windowHeightLaws electorate cfg 2 (by decide))
    (KitFG.Window.windowHeightBridge electorate cfg 2 (by decide))
    act.read act.head act.walk (fun _ A B _ _ hp => reflection_premises_sat A B hp)
  have oldHead := rowsPrem_pending_head m
    (KitFG.Window.windowHeightLaws electorate cfg 2 (by decide))
    (KitFG.Window.windowHeightBridge electorate cfg 2 (by decide))
    oldAct.read oldAct.head oldAct.walk
    (fun _ A B _ _ hp => reflection_premises_sat A B hp)
  refine ⟨bridge.1, m, h, selected, oldAct, act, ?_, ?_⟩
  · intro x hx
    obtain rfl : x = 0 := Subsingleton.elim _ _
    obtain ⟨H, hH, hp, hh, hJ, hj, _⟩ := oldHead 0 30 hx (by decide +kernel)
    exact ⟨H, hH, hp, hh, hJ, hj⟩
  · intro x hx
    obtain rfl : x = 0 := Subsingleton.elim _ _
    obtain ⟨H, hH, hp, hh, hJ, hj, _⟩ := newHead 0 30 hx (by decide +kernel)
    exact ⟨H, hH, hp, hh, hJ, hj⟩

#print axioms frozen_bridge_premises_sat

private theorem timing_premises_sat : FGTimingLaws timing := by
  constructor <;> intros <;> simp


#print axioms timing_premises_sat

-- Logical frozen specialization: reuse every old leaf and the paired record bridges.
-- This implication is separate from the exact-data bounded controls above.
namespace FrozenOwner

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (O : FGObservationReads R) (T : FGTiming) (L : FGTimingLaws T)
variable (E : Generic.Env V) (rho : V2.D.Run V P) (I : V2.D.Interface P)
variable (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))

variable (decodeProposal : P.Object → Option (Slot × Body))
variable (bodyErase : Body → Block) (bodyRows : Body → List Wire)
variable (blockWireRows : P.State → List Wire)
variable (chainWireRows : P.State → Block → List Wire)
variable (parentFG : P.State → Block → Option (FGBlock (Fin n)))
variable (parentHeight : P.State → Slot → FGBlock (Fin n) → Height × BlockId)
variable (validFor : P.State → Slot → FGBlock (Fin n) → Wire → Bool)
variable (makeFG : FGBlock (Fin n) → Block → List Wire → FGBlock (Fin n))
variable (valid : Wire → Bool) (ac : FGACServiceReads V)
variable (cfg : FGConfig) (K : Nat) (ΔF : Time) (sp : FGServicePoint) (pt : KernelPt)
variable {Jst : Time}

include L in
private theorem frozen_owner_specialization
    (e : Fin n ≃ V) (he : ∀ i, safetyHolder S rho i = e i)
    (CL : FGCoreLaws R) (HL : FGHeadLaws R E rho)
    (keep : FGTreeKeepLaws R) (restore : FGTreeRestoreLaws R)
    (hc : FGCertificateLaws Ef O.height O.finality)
    (heightBridge : HeightBridge Ef cfg O.height)
    (height_eq : O.height = KitFG.Window.certificateHeight Ef cfg K)
    (finality_eq : O.finality = KitFG.Window.certificateFinality Ef cfg K)
    (hne : ¬ Ef.IsQuorum ∅)
    (target : TargetJustification Ef O.height)
    (foldTarget : ∀ y U X, X ≠ .genesis → EntryAt O.height U y →
      FGBlock.Preceq U X.parent →
      ((O.height X.parent).h = y → TargetCoveredByChild Ef O.height X U y) →
      y + 1 ≤ (O.height X).h)
    (noMixed : ∀ y U X, SlotChain X → EntryAt O.height U y →
      FGBlock.Preceq U X.parent → X.slot < U.slot + cfg.timeoutDelay + 1 →
      NoMixedOnPath O.height X y)
    (honestSlot : Slot → Prop)
    (hK : KernelPrem_W T ΔF rho.horizon sp pt honestSlot Ef.q
      (Ef.weightOf (Finset.univ \ historyFaulty S rho)) cfg.timeoutDelay K)
    (run : KernelRunFacts S E rho Ef ΔF)
    (hreset : T.proposal (sp.reset.sStar + 2) ≤ sp.serviceStart)
    (hGSTstart : E.t_GST ≤ sp.serviceStart)
    (reset : H0Reset R S E rho O T (fun a => namedEntry (D.heightPair a)) Jst sp.reset)
    (history : FGHistoricalHighTransfer R O T E rho I sp rho.horizon)
    (chain : ∀ horizon, FGHistoricalHighChain R O T E rho sp horizon)
    (reflect : ∀ A B, Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B)
    (parent : ∀ B, R.erase B.parent = (R.erase B).parent)
    (hOrigin : RawHistoryOrigin R S E rho T D)
    (emission : HighRecordEmission S T E rho Ef cfg)
    (decoded : ∀ j x r a, HonestRowAt S E rho T j x r a → ∃ u, S.decode a = some u)
    (receipt : TRowsReceipt R S E rho T blockWireRows ΔF)
    (honest_slot : ∀ s, honestSlot s → ∃ x, x ∈ rho.honest)
    (proposal : ∀ s, honestSlot s → pt.r * T.roundSlots ≤ s →
      s ≤ (pt.r + 2) * T.roundSlots → ∃ Q, HonestProposal E rho I s Q)
    (terminalProposal : honestSlot ((pt.r + 2) * T.roundSlots + kappaF T ΔF) →
      ∃ Q, HonestProposal E rho I ((pt.r + 2) * T.roundSlots + kappaF T ΔF) Q)
    (carrier : ∀ s Q, HonestProposal E rho I s Q →
      ∃ X : FGBlock (Fin n), R.erase X = Q ∧
        OpeningCarrier_W decodeProposal bodyErase bodyRows (fun nd Q => parentFG nd Q.parent)
          makeFG E rho I s Q X ∧ X.slot = s ∧
        (∃ rows, HonestCarrier E rho I (kernelCarrier decodeProposal bodyErase bodyRows)
          s Q rows ∧ X.rows = rows.filterMap S.decode) ∧
        ∃ nd, proposalStateAt E rho I s = some nd ∧
          parentFG nd Q.parent = some X.parent ∧ X.parent ∈ (R.core nd).fg.TF)
    (exactService : ∀ s Q, HonestProposal E rho I s Q → pt.r * T.roundSlots ≤ s →
      KernelExactService ac rho.horizon s Q)
    (source_read : ∀ s Q r x, KernelExactService ac rho.horizon s Q →
      T.gate s ≤ rho.horizon → s = r * T.roundSlots → x ∈ rho.honest →
      pt.r * T.roundSlots ≤ s → ac.source x r = some (some Q))
    (source_eq : ∀ x r, ac.source x r =
      (actionSourceFG R E rho T x r).map (Option.map R.erase))
    (head_read : ∀ s Q x, KernelExactService ac rho.horizon s Q →
      pt.r * T.roundSlots ≤ s → s ≤ (pt.r + 2) * T.roundSlots → x ∈ rho.honest →
      headAtLabel R E rho T x s = some Q)
    (head_held : ∀ s X x, headAtLabel R E rho T x s = some (R.erase X) →
      ∃ i, rho.events[i]? = some (.tick x (T.vote s)) ∧
        X ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF)
    (slot_chain : ∀ i x X, X ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF → SlotChain X)
    (closed : ∀ s nd, proposalStateAt E rho I s = some nd →
      ∀ X ∈ (R.core nd).fg.TF, X.parent ∈ (R.core nd).fg.TF)
    (roots : ∀ s nd, proposalStateAt E rho I s = some nd → ViewRootInj (R.core nd).fg.TF)
    (validRows : ∀ s nd, proposalStateAt E rho I s = some nd →
      ∀ X ∈ (R.core nd).fg.TF, ∀ row ∈ X.rows,
        SimplexFG.Window.r6w (SimplexFG.Window.derive Ef cfg K X.parent) row = true)
    (parentEq : ∀ nd s X, parentHeight nd s X = ((O.height X).h, (O.height X).T_h.root))
    (matchValid : ∀ nd s X a, valid a = true →
      namedEntry (D.heightPair a) = some (parentHeight nd s X) → validFor nd s X a = true)
    (hBatch : ∀ q y U X,
      BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
        parentFG parentHeight validFor ΔF .target q y U X →
      (O.height X.parent).h = y → TargetCoveredByChild Ef O.height X U y)
    (hSOCOVTarget : ∀ x ∈ rho.honest, ∀ r C,
      actionSourceFG R E rho T x r = some (some C) → sp.reset.M + 1 ≤ (O.height C).h →
      E.awake x (T.action r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt S E rho T j x rSent a ∧
        RowComplete S rho D.signer valid x a ∧
        D.heightPair a = .vote (O.height C).h (O.height C).T_h.root false)
    (action : ∀ A (m : KernelMiddleWitness_W R S O T E rho I D Ef decodeProposal bodyErase
      bodyRows blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A),
      KernelActionSupply_W R S O T E rho I D Ef m)
    (makeWire : Row (Fin n) → Wire)
    (wireDecode : ∀ row, S.decode (makeWire row) = some row)
    (wireValid : ∀ i y U B,
      valid (makeWire ⟨i, .vote (y + 1) B false, some ⟨y, U⟩⟩) = true)
    (client : ∀ nd, (S.inputs nd).1 = R.source nd)
    (release : ∀ i q nd row,
      postClock E rho (safetyHolder S rho i) (T.action q) = some nd →
      E.awake (safetyHolder S rho i) (T.action q) = true →
      (createRowOnce Ef cfg (S.record nd) i (S.inputs nd).1 (S.inputs nd).2).1 = some row →
      ∃ j, rho.events[j]? = some (.tick (safetyHolder S rho i) (T.action q)) ∧
        S.encode (makeWire row) ∈ V2.D.Run.emitsAt E rho j)
    (fields : ∀ nd H, R.finalityHead nd = some H →
      (S.inputs nd).2 = certificateHeadFields O.height O.finality H)
    {storedCarrier : P.State → FGBlock (Fin n) → Wire → Prop}
    {SourceService : V → Nat → FGBlock (Fin n) → Prop}
    (hQC : RQCOrigin R S E rho O T storedCarrier SourceService Ef)
    (recordHead : HighRecordHead R S O E rho) (clientLaws : FGSafetyClientLaws S Ef cfg)
    (own : HighRecordOwnOrigin S T E rho)
    (hsel : TRowsSelect R S E rho T I (kernelCarrier decodeProposal bodyErase bodyRows)
      chainWireRows blockWireRows parentFG validFor)
    (decode : ∀ a i, D.signer a = some i → ∃ u, S.decode a = some u)
    (occurrence : ∀ s (Q : Block) H nd a u,
      proposalStateAt E rho I s = some nd → parentFG nd Q.parent = some H →
      a ∈ chainWireRows nd Q.parent → S.decode a = some u →
      ∃ W, FGBlock.Preceq W H ∧ u ∈ W.rows)
    (validFor_eq : ∀ nd s B a, validFor nd s B a =
      ((S.decode a).isSome && ((S.decode a).map
        (SimplexFG.Window.r6w (KitFG.Window.parentState Ef cfg K B s))).getD false))
    (pathValid : ∀ s nd, proposalStateAt E rho I s = some nd → ∀ H ∈ (R.core nd).fg.TF,
      ∀ B s' root body rs, FGBlock.Preceq (.node B s' root body rs) H → ∀ a ∈ rs,
      (match a.height_pair with
        | .empty => false
        | .vote h _ _ => decide (1 ≤ h) &&
            (a.finality_pair.map (fun fp => decide (fp.height < h))).getD true) = true ∧
        SimplexFG.Window.r6w (SimplexFG.Window.derive Ef cfg K B) a = true)
    (dutyTime : ∀ s, T.proposal s = V2.D.proposalTime I s)
    (rowDurable : ∀ i j x a, i ≤ j →
      rowHeld R blockWireRows (V2.D.Run.stateBefore E rho i x) a →
      rowHeld R blockWireRows (V2.D.Run.stateBefore E rho j x) a)
    (rowClock : ∀ nd t a, rowHeld R blockWireRows nd a →
      rowHeld R blockWireRows (P.clock nd t) a)
    (ready : Nat → V → FGBlock (Fin n) → Time → Prop)
    (step : AcceptStep_W R E rho Ef cfg K ready) (durable : FGFinalityDurableLaws R)
    (inv : ∀ i x, x ∈ rho.honest → KitFG.FGStoreInvariant O.height O.finality
      (R.core (V2.D.Run.stateBefore E rho i x)).fg)
    (finBlock : FGBlock (Fin n) → Prop)
    (hI3 : ∀ C W, finBlock C → finBlock W →
      FGBlock.compatible (O.finality C).F (O.finality W).F = true)
    (readyBlock : ∀ i x X t, ready i x X t → finBlock X)
    (stored : ∀ i x, ∀ C ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF,
      C ≠ .genesis → finBlock C)
    (rootScope : ∀ i x, x ∈ rho.honest → ∀ C k u r a B,
      C ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF →
      HonestRowAt S E rho T k u r a → actionSourceFG R E rho T u r = some (some B) →
      (O.height C).J.root = (O.height B).T_h.root → (O.height C).J = (O.height B).T_h)
    (hStrat : ∀ j z W, z ∈ rho.honest →
      W ∈ (R.core (V2.D.Run.stateBefore E rho j z)).fg.TF →
      ∀ J ∈ certified R O W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore S E rho T j u r a ∧
        namedEntry (D.heightPair a) = some ((O.height J).h, J.root))
    (hEmittedSource : ∀ j z r a e, HonestRowAt S E rho T j z r a →
      namedEntry (D.heightPair a) = some e → ∃ C,
        actionSourceFG R E rho T z r = some (some C) ∧
        e = ((O.height C).h, (O.height C).T_h.root) ∧
        FGBlock.Preceq (O.height C).T_h C)
    (hcapBefore : ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt R E rho j z W →
      (∀ k u r a row h B timeout, HonestRowAt S E rho T k u r a →
        S.decode a = some row → row.height_pair = .vote h B timeout →
        T.action r < cut → h < b + 1) → (O.height W).h < b + 2)
    (delivery : ∀ (X U : FGBlock (Fin n)) rows,
      HonestCarrier E rho I (kernelCarrier decodeProposal bodyErase bodyRows)
        X.slot (R.erase X) rows →
      E.t_GST ≤ T.proposal X.slot → T.proposal X.slot + T.delta ≤ rho.horizon →
      FGBlock.Preceq U (SimplexFG.Window.derive Ef cfg K X).F →
      Nonempty (BlockDelivery_W R E rho ready X U (T.proposal X.slot)
        (T.proposal X.slot + T.delta))) :
    KernelConclusion_W R E rho O T I decodeProposal bodyErase bodyRows
      (fun nd Q => parentFG nd Q.parent) makeFG ΔF pt.r := by
  have holderAction : ∀ A (h : KernelMiddleWitnessFG_W R S O T E rho I D Ef decodeProposal
      bodyErase bodyRows blockWireRows parentFG parentHeight validFor makeFG valid ac
      cfg K ΔF sp pt A), KernelActionSupplyFG_W R S O T E rho I D Ef h := by
    intro A h
    obtain ⟨m, selected⟩ := (kernel_middle_holder_frozen_iff R S O T E rho I D Ef
      decodeProposal bodyErase bodyRows blockWireRows parentFG parentHeight validFor makeFG
      valid ac cfg K ΔF sp pt A e he).2.2 h
    exact (kernel_action_holder_frozen_iff (m := m) (h := h) (selected := selected)).mp
      (action A m)
  exact finality_kernel_W_of_holder R S O T L E rho I D Ef decodeProposal bodyErase bodyRows
    blockWireRows chainWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt
    CL HL keep restore hc heightBridge height_eq finality_eq hne target foldTarget noMixed
    honestSlot hK run hreset hGSTstart reset history chain reflect parent hOrigin emission
    decoded receipt honest_slot proposal terminalProposal carrier exactService source_read
    source_eq head_read head_held slot_chain closed roots validRows parentEq matchValid hBatch
    (fun i hi r C hs hh ha => hSOCOVTarget _ hi r C hs hh ha) holderAction
    makeWire wireDecode wireValid client release fields hQC recordHead clientLaws own hsel
    decode occurrence validFor_eq pathValid dutyTime rowDurable rowClock ready step durable
    inv finBlock hI3 readyBlock stored rootScope hStrat hEmittedSource hcapBefore delivery

#print axioms frozen_owner_specialization

end FrozenOwner

-- The full owner run starts at genesis, retains its core on clocks, and updates stores
-- at actual deliveries. Its reset precedes the active kernel window.
namespace Owner

set_option maxRecDepth 8192
private abbrev env (V : Type) : Generic.Env V :=
  ⟨1, by decide, 0, by decide, fun _ _ => true⟩

private def block : Nat → FGBlock (Fin 1)
  | 0 => .genesis
  | k + 1 => .node (block k) (2 * (k + 1)) ⟨k + 1⟩ 0
      [⟨0, .vote (k + 1) (block k).root false,
        if k = 0 then none else some ⟨k, (block (k - 1)).root⟩⟩]
private abbrev row (k : Nat) : Row (Fin 1) :=
  ⟨0, .vote (k + 1) (block k).root false,
    if k = 0 then none else some ⟨k, (block (k - 1)).root⟩⟩
private def store : Nat → Store (Fin 1)
  | 0 => Store.init
  | k + 1 => SimplexFG.Window.on_block electorate cfg 2 (store k) (block (k + 1))
private abbrev head (k : Nat) : HeadFields :=
  certificateHeadFields (KitFG.Window.certificateHeight electorate cfg 2)
    (KitFG.Window.certificateFinality electorate cfg 2) (block k)
private abbrev objType := V2.Signed Nat (fun _ => 1) (FGBlock (Fin 1) ⊕ Row (Fin 1))
private abbrev protocol : V2.ProtocolSpecD Unit where
  State := Fin 8 × RecordOnce
  Label := Nat
  Duty := Time
  signLabel t := if t % 8 = 6 then 0 else t.toNat + 1
  seats _ := 1
  Payload := FGBlock (Fin 1) ⊕ Row (Fin 1)
  Durable := Fin 8 × RecordOnce
  init := (0, RecordOnce.initial)
  clock st _ := st
  actTime := id
  duties t := [t]
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; simp
  act st t _ := if t % 8 = 6 then
    ((createRowOnce electorate cfg st.2 0 (some (block st.1)) (head st.1)).1.map Sum.inr)
    else if 0 < t ∧ t ≤ 56 ∧ t % 8 = 0 then
      some (.inl (block (t.toNat / 8))) else none
  gossip _ _ := []
  process st o := (match o.payload with
    | .inl X => max st.1 ⟨min 7 (X.slot / 2), by omega⟩
    | .inr _ => st.1, st.2)
  selfVisible _ := true
  recordOwn st o := (st.1, if o.auth = .seat 0 0 then
    match o.payload with | .inr u => record_row_once st.2 u | .inl _ => st.2
    else st.2)
  durable := id
  restore st _ := st
  wellFormed _ := true
  depsPresent _ _ := true
  processed _ _ := false
  excludes _ _ := false
  handles _ _ _ := False
  carries _ _ := False
private abbrev wire (u : Row (Fin 1)) : protocol.Object := ⟨.seat 0 0, .inr u⟩
private abbrev prop (k : Nat) : protocol.Object :=
  ⟨.seat (8 * k + 1) 0, .inl (block k)⟩
private abbrev decode (o : protocol.Object) : Option (Row (Fin 1)) :=
  if o.auth = .seat 0 0 then
    match o.payload with | .inr u => some u | .inl _ => none
  else none
private abbrev reads : FGSafetyReads protocol 1 protocol.Object where
  proposalErase o := match o.payload with | .inl X => some (erase X) | .inr _ => none
  proposalRows o := match o.payload with | .inl X => X.rows.map wire | .inr _ => []
  encode := id
  decode := decode
  decodeObject := decode
  fgLabel := 0
  fgSeats := Equiv.refl _
  record := Prod.snd
  inputs st := (some (block st.1), head st.1)
  enabled t := decide (t % 8 = 6)
  finalizedOut st := erase (store st.1).F
private abbrev core : FGCoreReads protocol 1 Unit Unit protocol.Object where
  core st := ⟨(), store st.1, [], (List.range 7).map (fun k => wire (row k))⟩
  erase := erase
  source st := some (block st.1)
  headVote st _ := erase (block st.1)
  finalityHead st := some (block st.1)
  proposalFG _ _ := none
private abbrev obs : FGObservationReads core where
  height := KitFG.Window.certificateHeight electorate cfg 2
  finality := KitFG.Window.certificateFinality electorate cfg 2
  controls _ := ⟨.genesis, 1, 0, .genesis, false⟩
  viable _ X := X
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
private abbrev run : V2.D.Run Nat protocol where
  honest := {7, 9}
  horizon := 57
  events := (List.range 58).flatMap fun t =>
    [.tick 9 t, .tick 7 t] ++
    (if t % 8 = 7 then [.deliver 7 (wire (row (t / 8))) t,
        .deliver 9 (wire (row (t / 8))) t] else []) ++
    (if 0 < t ∧ t % 8 = 0 then [.deliver 7 (prop (t / 8)) t,
        .deliver 9 (prop (t / 8)) t] else [])
  seatOf label _ := if label = 0 then 9 else 7
  input _ _ := ()
private abbrev point : FGServicePoint :=
  ⟨⟨0, 22, 3, 3, 6, erase (block 3)⟩, 8, erase (block 4), 32⟩
private abbrev pt : KernelPt := ⟨4⟩

private theorem erase_injective_premises_sat : Function.Injective erase := by
  intro X
  induction X with
  | genesis => intro Y he; cases Y <;> simp_all [erase]
  | node p s r x rs ih =>
    intro Y he
    cases Y with
    | genesis => simp [erase] at he
    | node q t u y ts =>
      simp only [erase, Block.node.injEq] at he
      obtain ⟨hp, hs, hr, hb⟩ := he
      obtain ⟨hx, hrows⟩ := encFGBody_inj hb
      cases ih hp
      cases hs
      cases hr
      cases hx
      cases hrows
      rfl

private theorem core_premises_sat : FGCoreLaws core := by
  have mono : ∀ i j : Fin 8, i ≤ j → (store i).TF ⊆ (store j).TF := by decide +kernel
  have mem : ∀ i : Fin 8, block i ∈ (store i).TF := by decide +kernel
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ?_,
    fun _ _ => List.prefix_rfl, fun _ _ => List.prefix_rfl, fun _ _ => rfl,
    ?_, erase_injective_premises_sat⟩
  · intro nd o
    cases hp : o.payload with
    | inl X =>
      simpa only [core, protocol, hp] using
        (mono nd.1 (max nd.1 ⟨min 7 (X.slot / 2), by omega⟩) (le_max_left _ _))
    | inr u => simpa only [core, protocol, hp] using Finset.Subset.refl (store nd.1).TF
  · intro nd C h
    obtain rfl := Option.some.inj h
    exact mem nd.1

#print axioms core_premises_sat

private theorem client_premises_sat : FGSafetyClientLaws reads electorate cfg where
  initial_record := rfl
  clock_record _ _ := rfl
  process_record _ _ := rfl
  restart_record _ _ := rfl
  own_record nd o := by
    cases o with
    | mk auth payload =>
      cases auth with
      | none => cases payload <;> rfl
      | seat label i =>
        obtain rfl : i = 0 := Subsingleton.elim _ _
        cases label <;> cases payload <;> rfl
  tick_rows E rho e he nd x t := by
    have hx : e 0 = x := by
      rw [← e.apply_symm_apply x]
      congr 1
      exact Subsingleton.elim _ _
    have hs : e.symm x = 0 := Subsingleton.elim _ _
    have hseat : rho.seatOf 0 0 = x := (he 0).trans hx
    change ((V2.D.tick E rho nd x t).2.filter protocol.objSelfVisible).filterMap decode =
      if E.awake x t = true ∧ decide (t % 8 = 6) = true then
        (createRowOnce electorate cfg nd.2 (e.symm x) (some (block nd.1)) (head nd.1)).1.toList
      else []
    cases ha : E.awake x t <;> by_cases ht : t % 8 = 6
    · simp [V2.D.tick, ha]
    · simp [V2.D.tick, ha]
    · cases hr : (createRowOnce electorate cfg nd.2 0 (some (block nd.1)) (head nd.1)).1 <;>
        simp [V2.D.tick, V2.D.Run.ownSeats, List.finRange_succ,
          ha, ht, hr, hs, decode]
      all_goals
        have hf : List.filter (fun i : Fin 1 =>
            decide (rho.seatOf (if t % 8 = 6 then 0 else t.toNat + 1) i = x)) [0] = [0] := by
          rw [ite_eq_left ht]
          simp [hseat]
        rw [hf]
        rfl
    · by_cases hp : 0 < t ∧ t ≤ 56 ∧ t % 8 = 0
      · by_cases hb : rho.seatOf (protocol.signLabel t) 0 = x <;>
          simp [V2.D.tick, V2.D.Run.ownSeats, List.finRange_succ, ha, ht, hb,
            V2.ProtocolSpecD.objSelfVisible, decode]
        all_goals aesop
      · simp [V2.D.tick, ha, ht]
        aesop

#print axioms client_premises_sat

private theorem schedule_premises_sat : V2.D.ScheduleWellFormed (env Nat) run := by
  have info : ∀ j : Fin 144,
      0 ≤ run.events[j.val].time ∧ run.events[j.val].time ≤ 57 ∧
        run.events[j.val].node ∈ run.honest := by decide +kernel
  constructor
  · decide
  · decide +kernel
  · decide +kernel
  · intro e he
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    exact ⟨(info ⟨j, hj⟩).1, (info ⟨j, hj⟩).2.1⟩
  · intro e he
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    exact (info ⟨j, hj⟩).2.2
  · intro x t ht
    obtain ⟨j, hj, h⟩ := List.getElem_of_mem ht
    have htime : run.events[j].time = t := congrArg V2.Event.time h
    have hn : 0 ≤ t := by rw [← htime]; exact (info ⟨j, hj⟩).1
    exact ⟨t.toNat, by simpa using (Int.toNat_of_nonneg hn).symm⟩
  · intro x hx t ht hn hh _
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    obtain ⟨k, rfl⟩ := ht
    change 0 ≤ (k : Int) * 1 at hn
    change (k : Int) * 1 ≤ 57 at hh
    have hk : k ≤ 57 := by omega
    rcases hx' with rfl | rfl <;> interval_cases k <;> decide +kernel

#print axioms schedule_premises_sat

private abbrev node (x : Fin 2) : Nat := if x = 0 then 7 else 9
private abbrev stage (i : Nat) (x : Fin 2) : Nat :=
  min 7 ((i - if x = 0 then 1 else 2) / 20)

private theorem trace_premises_sat :
    (∀ i : Fin 145, ∀ x : Fin 2,
      (V2.D.Run.stateBefore (env Nat) run i (node x)).1.val = stage i x) ∧
    (∀ j : Fin 144, V2.D.Run.emitsAt (env Nat) run j =
      if j.val % 20 = 12 then [wire (row (j.val / 20))] else
      if j.val % 20 = 19 ∧ j.val < 140 then [prop (j.val / 20 + 1)] else []) ∧
    (∀ k : Fin 7,
      run.events[20 * k.val + 12]? = some (.tick 9 (timing.action k)) ∧
      run.events[20 * k.val + 19]? = some (.tick 7 (timing.proposal (2 * (k.val + 1)))) ∧
      run.events[20 * k.val + 20]? =
        some (.deliver 7 (prop (k.val + 1)) (timing.proposal (2 * (k.val + 1)))) ∧
      run.events[20 * k.val + 21]? =
        some (.deliver 9 (prop (k.val + 1)) (timing.proposal (2 * (k.val + 1))))) ∧
    (∀ k : Fin 7, ∀ x : Fin 2,
      actionSourceFG core (env Nat) run timing (node x) k = some (some (block k))) := by
  exact ⟨by decide +kernel, by decide +kernel, by
    intro k
    fin_cases k <;> exact ⟨rfl, rfl, rfl, rfl⟩, by decide +kernel⟩

#print axioms trace_premises_sat

private theorem certificate_premises_sat :
    TargetJustification electorate obs.height ∧
    (∀ y U X, X ≠ .genesis → EntryAt obs.height U y →
      FGBlock.Preceq U X.parent →
      ((obs.height X.parent).h = y → TargetCoveredByChild electorate obs.height X U y) →
      y + 1 ≤ (obs.height X).h) ∧
    (∀ y U X, SlotChain X → EntryAt obs.height U y → FGBlock.Preceq U X.parent →
      X.slot < U.slot + cfg.timeoutDelay + 1 → NoMixedOnPath obs.height X y) := by
  let hb : HeightBridge electorate cfg obs.height :=
    KitFG.Window.windowHeightBridge electorate cfg 2 (by decide)
  let laws : FGHeightLaws electorate obs.height :=
    KitFG.Window.windowHeightLaws electorate cfg 2 (by decide)
  have advance (σ : ChainState (Fin 1)) (B : FGBlock (Fin 1))
      (rs : List (Row (Fin 1))) (Q : Finset (Fin 1)) (hQ : electorate.IsQuorum Q)
      (cover : ∀ i ∈ Q, i ∈ σ.target_participation ∨ ∃ a ∈ rs,
        a.signer = i ∧ a.height_pair = .vote σ.h σ.T_h.root false) :
      (process_height_events electorate cfg (foldRows σ B rs)).h = σ.h + 1 ∧
        (process_height_events electorate cfg (foldRows σ B rs)).J = σ.T_h ∧
        (process_height_events electorate cfg (foldRows σ B rs)).h_j = σ.h := by
    have fold (rows : List (Row (Fin 1))) (σ : ChainState (Fin 1)) (i : Fin 1)
        (hi : i ∈ σ.target_participation ∨ ∃ a ∈ rows,
          a.signer = i ∧ a.height_pair = .vote σ.h σ.T_h.root false) :
        i ∈ (rows.foldl process_row σ).target_participation := by
      induction rows generalizing σ with
      | nil => simpa using hi
      | cons a rows ih =>
        apply ih
        rw [(process_row_fields σ a).2.2.1, (process_row_fields σ a).2.2.2.1]
        rcases hi with hi | ⟨b, hb, hbi, hm⟩
        · left
          rw [process_row_target]
          split_ifs
          · exact Finset.mem_insert_of_mem hi
          · exact hi
        · rcases List.mem_cons.mp hb with rfl | hb
          · left
            rw [process_row_target, ite_eq_left hm]
            exact Finset.mem_insert.mpr (Or.inl hbi.symm)
          · exact Or.inr ⟨b, hb, hbi, hm⟩
    have hq : electorate.IsQuorum (foldRows σ B rs).target_participation :=
      isQuorum_of_subset electorate hQ
        (fun i hi => fold rs { σ with s := B.slot } i (cover i hi))
    have ht : (afterFin electorate (foldRows σ B rs)).targetQuorum electorate = true := by
      change decide (electorate.q ≤ electorate.weightOf
        (afterFin electorate (foldRows σ B rs)).target_participation) = true
      rw [decide_eq_true_eq, afterFin_target_participation]
      exact hq
    rw [process_height_events_eq, ite_eq_left ht]
    have hh := (afterFin_h electorate (foldRows σ B rs)).trans (foldRows_fields σ B rs).2.1
    have he := (afterFin_T_h electorate (foldRows σ B rs)).trans
      (foldRows_fields σ B rs).2.2.1
    exact ⟨congrArg (· + 1) hh, he, hh⟩
  have parentPath (X : FGBlock (Fin 1)) : FGBlock.Preceq X.parent X := by
    cases X with
    | genesis => exact preceq_refl _
    | node P s r x rs => exact preceq_parent_node P s r x rs
  have target {U X : FGBlock (Fin 1)} {y : Nat} (hX : X ≠ .genesis)
      (hU : EntryAt obs.height U y) (hUX : FGBlock.Preceq U X.parent)
      (hP : (obs.height X.parent).h = y)
      (hc : TargetCoveredByChild electorate obs.height X U y) :
      JustifiedCross obs.height X U y := by
    have hT := (laws.entry_plateau hUX (hU.1.trans hP.symm)).symm.trans hU.2
    obtain ⟨Q, hQ, hc⟩ := hc
    cases X with
    | genesis => exact (hX rfl).elim
    | node P s r x rs =>
      have covered : ∀ i ∈ Q, i ∈ (obs.height P).target_participation ∨
          ∃ a ∈ rs, a.signer = i ∧ a.height_pair =
            .vote (obs.height P).h (obs.height P).T_h.root false := by
        intro i hi
        rcases hc i hi with hb | ⟨a, ha, hs, hp⟩
        · exact Or.inl hb
        · refine Or.inr ⟨a, ha, hs, ?_⟩
          change (obs.height P).h = y at hP
          change (obs.height P).T_h = U at hT
          rw [hP, hT]
          exact hp
      have heq : ∀ B, KitFG.Window.certificateHeight electorate cfg 2 B =
          heightOf (SimplexFG.derive electorate cfg B) := hb
      have result := advance (SimplexFG.derive electorate cfg P) (.node P s r x rs) rs Q hQ
        (by simpa only [heq, heightOf_def] using covered)
      have lifted : (obs.height (.node P s r x rs)).h = (obs.height P).h + 1 ∧
          (obs.height (.node P s r x rs)).J = (obs.height P).T_h ∧
          (obs.height (.node P s r x rs)).h_j = (obs.height P).h := by
        simpa only [heq, heightOf_def, derive_node] using result
      obtain ⟨hh, hJ, hj⟩ := lifted
      exact ⟨hP, hh.trans (congrArg (· + 1) hP), hJ.trans hT, hj.trans hP⟩
  have fold (y : Nat) (U X : FGBlock (Fin 1)) (hX : X ≠ .genesis)
      (hU : EntryAt obs.height U y) (hUX : FGBlock.Preceq U X.parent)
      (hc : (obs.height X.parent).h = y →
        TargetCoveredByChild electorate obs.height X U y) :
      y + 1 ≤ (obs.height X).h ∧
        ((∃ C, FGBlock.Preceq C X ∧ JustifiedCross obs.height C U y) ∨
          ∃ W, FGBlock.Preceq W X.parent ∧ MixedCross obs.height W y) := by
    have hlow := laws.h_mono hUX
    rw [hU.1] at hlow
    by_cases hP : (obs.height X.parent).h = y
    · have hj := target hX hU hUX hP (hc hP)
      exact ⟨by rw [hj.2.1], Or.inl ⟨X, preceq_refl _, hj⟩⟩
    · have hhigh : y < (obs.height X.parent).h := by simp only [Height] at *; omega
      obtain ⟨W, _, hUW, hWP, hp, hw⟩ :=
        first_height_crossing_edge_of_bridge electorate cfg obs.height hb y hUX hU.1 hhigh
      have hmono := laws.h_mono (parentPath X)
      refine ⟨by simp only [Height] at *; omega, ?_⟩
      rcases cross_cases_of_laws laws (FGJustificationLaws.of_bridge hb) hU hUW hp hw with
        hj | hm
      · exact Or.inl ⟨W, preceq_trans hWP (parentPath X), hj⟩
      · exact Or.inr ⟨W, hWP, hm⟩
  refine ⟨?_, fun y U X hX hU hUX hc => (fold y U X hX hU hUX hc).1, ?_⟩
  · intro y U X hX hU hUX hc hn
    rcases (fold y U X hX hU hUX hc).2 with hj | ⟨W, hWP, hm⟩
    · exact hj
    · exact (hn W hWP hm).elim
  · intro y U X hs hU hUX hearly W hWP hm
    have slot_le : ∀ Z A : FGBlock (Fin 1), SlotChain Z →
        FGBlock.Preceq A Z → A.slot ≤ Z.slot := by
      intro Z
      induction Z with
      | genesis => intro A _ h; obtain rfl := preceq_genesis.mp h; exact le_rfl
      | node P s r x rs ih =>
        intro A hz hA
        by_cases heq : A = .node P s r x rs
        · subst A; exact le_rfl
        · exact le_trans (ih A (fun B hB hn =>
            hz B (preceq_node_of_preceq s r x rs hB) hn)
            (preceq_parent_of_preceq_node hA heq))
            (Nat.le_of_lt (hz _ (preceq_refl _) (by simp)))
    obtain ⟨hP, hW, hj⟩ := hm
    have hne : W ≠ .genesis := by
      intro heq
      subst W
      change (obs.height .genesis).h = y at hP
      rw [hP] at hW
      simp only [Height, Slot] at *
      omega
    have hUW : FGBlock.Preceq U W := by
      rcases preceq_total_of_common hUX hWP with h | h
      · exact h
      · have hh := laws.h_mono h
        rw [hU.1, hW] at hh
        simp only [Height, Slot] at *
        omega
    have hUWp : FGBlock.Preceq U W.parent := by
      cases W with
      | genesis => exact (hne rfl).elim
      | node P s r x rs =>
        apply preceq_parent_of_preceq_node hUW
        intro heq
        rw [← heq, hU.1] at hW
        simp only [Height, Slot] at *
        omega
    have hXne : X ≠ .genesis := by
      intro heq
      subst X
      obtain rfl := preceq_genesis.mp hWP
      exact hne rfl
    have hPX := hs X (preceq_refl _) hXne
    have hslots := slot_le X.parent W
      (fun A hA hn => hs A (preceq_trans hA (parentPath X)) hn) hWP
    have hwEarly : W.slot < U.slot + cfg.timeoutDelay := by
      change X.slot < U.slot + cfg.timeoutDelay + 1 at hearly
      simp only [Slot] at *
      omega
    have hjust := no_mixed_cross_before_maturity_of_bridge electorate cfg obs.height hb
      y hne hUWp hU.1 hU.2 hP hwEarly hW
    rw [hjust.2] at hj
    exact (Nat.lt_irrefl y hj)

#print axioms certificate_premises_sat

private theorem data_premises_sat :
    (∀ k : Fin 8,
      (obs.height (block k)).h = k.val + 1 ∧ (obs.height (block k)).T_h = block k ∧
      (obs.height (block k)).J = block (k.val - 1) ∧ (obs.height (block k)).h_j = k.val ∧
      (obs.finality (block k)).F = block (k.val - 2) ∧
      (obs.finality (block k)).h_F = k.val - 1 ∧
      (store k).TF = (Finset.range (k.val + 1)).image block ∧
      (store k).h_max = k.val + 1 ∧ (store k).F = block (k.val - 2)) ∧
    (∀ i j : Fin 8, FGBlock.Preceq (block i) (block j) ↔ i ≤ j) ∧
    (∀ i j : Fin 8, (block i).root = (block j).root → i = j) := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms data_premises_sat

private theorem owner_exact_rows (j x r : Nat) (a : protocol.Object)
    (ha : HonestRowAt reads (env Nat) run timing j x r a) :
    ∃ k : Fin 7, j = 20 * k.val + 12 ∧ x = 9 ∧ r = k.val ∧ a = wire (row k) := by
  have hj : j < 144 := (List.getElem?_eq_some_iff.mp ha.2.1).1
  have hw := ha.2.2
  change a ∈ V2.D.Run.emitsAt (env Nat) run j at hw
  rw [trace_premises_sat.2.1 ⟨j, hj⟩] at hw
  dsimp only [Fin.val_mk] at hw
  split_ifs at hw with hr hp
  · have hk : j / 20 < 7 := by omega
    let k : Fin 7 := ⟨j / 20, hk⟩
    have he : j = 20 * k.val + 12 := by dsimp only [k]; omega
    have ht := (trace_premises_sat.2.2.1 k).1
    rw [← he] at ht
    have htick := V2.Event.tick.inj (Option.some.inj (ht.symm.trans ha.2.1))
    have ht' : 4 * (k.val * 2) + 6 = 4 * (r * 2) + 6 := by
      have h := htick.2
      change (4 : Int) * (k.val * 2 : Nat) + 6 = (4 : Int) * (r * 2 : Nat) + 6 at h
      exact_mod_cast h
    exact ⟨k, he, htick.1.symm, by omega, List.mem_singleton.mp hw⟩
  · have hk : j / 20 < 7 := by omega
    let k : Fin 7 := ⟨j / 20, hk⟩
    have he : j = 20 * k.val + 19 := by dsimp only [k]; omega
    have ht := (trace_premises_sat.2.2.1 k).2.1
    rw [← he] at ht
    have htick := V2.Event.tick.inj (Option.some.inj (ht.symm.trans ha.2.1))
    have ht' : 4 * (2 * (k.val + 1)) = 4 * (r * 2) + 6 := by
      have h := htick.2
      change (4 : Int) * (2 * (k.val + 1) : Nat) = (4 : Int) * (r * 2 : Nat) + 6 at h
      exact_mod_cast h
    omega
  · contradiction

#print axioms owner_exact_rows

private theorem source_cases (x r : Nat) (C : FGBlock (Fin 1))
    (hs : actionSourceFG core (env Nat) run timing x r = some (some C)) :
    x ∈ run.honest ∧ r < 7 ∧ C = block r := by
  have hs' := hs
  unfold actionSourceFG postClock preTick at hs'
  cases hi : V2.D.Run.tickIdx? run x (timing.action r) with
  | none => simp only [hi, Option.map_none] at hs'; contradiction
  | some j =>
    have he := V2.D.Run.tickIdx?_spec hi
    have hm := List.mem_of_getElem? he
    have hx := schedule_premises_sat.honest_only _ hm
    have htime := (schedule_premises_sat.in_horizon _ hm).2
    change 4 * (r * 2 : Nat) + 6 ≤ (57 : Int) at htime
    have hr : r < 7 := by omega
    change x ∈ run.honest at hx
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    have hsrc : actionSourceFG core (env Nat) run timing x r = some (some (block r)) := by
      rcases hx' with rfl | rfl
      · exact trace_premises_sat.2.2.2 ⟨r, hr⟩ 0
      · exact trace_premises_sat.2.2.2 ⟨r, hr⟩ 1
    rw [hsrc] at hs
    exact ⟨hx, hr, (Option.some.inj (Option.some.inj hs)).symm⟩

#print axioms source_cases

private theorem stage_before_premises_sat (i : Nat) (x : Fin 2) :
    (V2.D.Run.stateBefore (env Nat) run i (node x)).1.val = stage i x := by
  by_cases hi : i < 145
  · exact trace_premises_sat.1 ⟨i, hi⟩ x
  · have hlen : run.events.length = 144 := by decide
    have hge : run.events.length ≤ i := by omega
    have he : V2.D.Run.stateBefore (env Nat) run i =
        V2.D.Run.stateBefore (env Nat) run 144 := by
      unfold V2.D.Run.stateBefore
      rw [List.take_of_length_le hge, List.take_of_length_le (by omega :
        run.events.length ≤ 144)]
    rw [he, trace_premises_sat.1 ⟨144, by decide⟩ x]
    fin_cases x
    · change 7 = min 7 ((i - 1) / 20)
      omega
    · change 7 = min 7 ((i - 2) / 20)
      omega

#print axioms stage_before_premises_sat

private abbrev blocks : Finset (FGBlock (Fin 1)) := (Finset.range 8).image block

private theorem store_invariant_premises_sat : ∀ nd : protocol.State,
    FGStoreInvariant obs.height obs.finality (core.core nd).fg := by
  have closed : ∀ B ∈ blocks, B.parent ∈ blocks := by decide +kernel
  have subset : ∀ k : Fin 8, (store k).TF ⊆ blocks := by decide +kernel
  have roots (st : Store (Fin 1)) (B : FGBlock (Fin 1))
      (hst : st.TF ⊆ blocks) (hB : B ∈ blocks) : StoreStepRoots st B := by
    have sub : insert B st.TF ⊆ blocks := Finset.insert_subset hB hst
    intro X Y ⟨W, hW, hX⟩ ⟨Z, hZ, hY⟩ hr
    have hx := KitFG.ancestor_closed_of_parent_closed blocks closed W (sub hW) X hX
    have hy := KitFG.ancestor_closed_of_parent_closed blocks closed Z (sub hZ) Y hY
    exact (by decide +kernel : ∀ X ∈ blocks, ∀ Y ∈ blocks, X.root = Y.root → X = Y)
      X hx Y hy hr
  have inv0 : FGStoreInvariant obs.height obs.finality (store 0) := by
    rw [store]
    exact KitFG.Window.windowStoreInvariant_init electorate cfg 2
  have inv1 : FGStoreInvariant obs.height obs.finality (store 1) := by
    rw [store]
    exact KitFG.Window.windowStoreInvariant_on_block electorate cfg 2
      (by change ¬ (1 ≤ 0); decide) (by decide) _ _ inv0
      (roots _ _ (subset 0) (by decide +kernel))
  have inv2 : FGStoreInvariant obs.height obs.finality (store 2) := by
    rw [store]
    exact KitFG.Window.windowStoreInvariant_on_block electorate cfg 2
      (by change ¬ (1 ≤ 0); decide) (by decide) _ _ inv1
      (roots _ _ (subset 1) (by decide +kernel))
  have inv3 : FGStoreInvariant obs.height obs.finality (store 3) := by
    rw [store]
    exact KitFG.Window.windowStoreInvariant_on_block electorate cfg 2
      (by change ¬ (1 ≤ 0); decide) (by decide) _ _ inv2
      (roots _ _ (subset 2) (by decide +kernel))
  have inv4 : FGStoreInvariant obs.height obs.finality (store 4) := by
    rw [store]
    exact KitFG.Window.windowStoreInvariant_on_block electorate cfg 2
      (by change ¬ (1 ≤ 0); decide) (by decide) _ _ inv3
      (roots _ _ (subset 3) (by decide +kernel))
  have inv5 : FGStoreInvariant obs.height obs.finality (store 5) := by
    rw [store]
    exact KitFG.Window.windowStoreInvariant_on_block electorate cfg 2
      (by change ¬ (1 ≤ 0); decide) (by decide) _ _ inv4
      (roots _ _ (subset 4) (by decide +kernel))
  have inv6 : FGStoreInvariant obs.height obs.finality (store 6) := by
    rw [store]
    exact KitFG.Window.windowStoreInvariant_on_block electorate cfg 2
      (by change ¬ (1 ≤ 0); decide) (by decide) _ _ inv5
      (roots _ _ (subset 5) (by decide +kernel))
  have inv7 : FGStoreInvariant obs.height obs.finality (store 7) := by
    rw [store]
    exact KitFG.Window.windowStoreInvariant_on_block electorate cfg 2
      (by change ¬ (1 ≤ 0); decide) (by decide) _ _ inv6
      (roots _ _ (subset 6) (by decide +kernel))
  have inv : ∀ k : Fin 8, FGStoreInvariant obs.height obs.finality (store k) := by
    intro k
    fin_cases k
    · exact inv0
    · exact inv1
    · exact inv2
    · exact inv3
    · exact inv4
    · exact inv5
    · exact inv6
    · exact inv7
  intro nd
  exact inv nd.1

#print axioms store_invariant_premises_sat

private theorem tree_cases :
    (∀ k W, FGBlock.Preceq W (block k) → ∃ l ≤ k, W = block l) ∧
    (∀ (nd : protocol.State) W, W ∈ (core.core nd).fg.TF →
      ∃ k : Fin 8, k ≤ nd.1 ∧ W = block k) := by
  constructor
  · intro k
    induction k with
    | zero =>
      intro W h
      rw [block] at h
      obtain rfl := preceq_genesis.mp h
      exact ⟨0, le_rfl, by rw [block]⟩
    | succ k ih =>
      intro W h
      by_cases he : W = block (k + 1)
      · exact ⟨k + 1, le_rfl, he⟩
      · rw [block] at h
        rw [block] at he
        obtain ⟨l, hl, hw⟩ := ih W (preceq_parent_of_preceq_node h he)
        exact ⟨l, by omega, hw⟩
  · intro nd W hW
    obtain ⟨_, _, _, _, _, _, htf, _, _⟩ := data_premises_sat.1 nd.1
    change W ∈ (store nd.1).TF at hW
    rw [htf] at hW
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hW
    have hk' := Finset.mem_range.mp hk
    have hn := nd.1.isLt
    exact ⟨⟨k, by omega⟩, by exact Nat.le_of_lt_succ hk', rfl⟩

#print axioms tree_cases

private abbrev history : FGHistoryWireReads reads where
  heightPair a := ((decode a).map (·.height_pair)).getD .empty
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
private abbrev lookup (Q : Block) : Option (FGBlock (Fin 1)) :=
  ((List.range 8).map block).find? (fun X => decide (X.root = Q.root))
private abbrev parentRead (_ : protocol.State) (Q : Block) := lookup Q
private abbrev parentHeight (_ : protocol.State) (_ : Slot) (X : FGBlock (Fin 1)) :
    Height × BlockId := ((obs.height X).h, (obs.height X).T_h.root)
private abbrev makeFG (_ : FGBlock (Fin 1)) (Q : Block) (_ : List protocol.Object) :=
  (lookup Q).getD .genesis
private abbrev valid (a : protocol.Object) : Bool := (decode a).isSome
private abbrev validFor (_ : protocol.State) (s : Slot) (B : FGBlock (Fin 1))
    (a : protocol.Object) : Bool :=
  (decode a).isSome && ((decode a).map
    (SimplexFG.Window.r6w (KitFG.Window.parentState electorate cfg 2 B s))).getD false
private abbrev chainRowsRead (_ : protocol.State) (Q : Block) : List protocol.Object :=
  ((lookup Q).map (fun X => (List.range (X.slot / 2)).map (fun k => wire (row k)))).getD []
private abbrev service : FGACServiceReads Nat where
  honest x := x ∈ run.honest
  proposal s Q := HonestProposal (env Nat) run interface s Q
  proposalTime := timing.proposal
  actionHeadLabel r := r * 2 + 1
  actionTime := timing.action
  proposalScope _ _ := True
  sourceScope _ _ _ := True
  actionScope _ _ := True
  actionHead x r := (actionHead core (env Nat) run timing x r).map (Option.map erase)
  parent _ := some .genesis
  gateFloor _ _ := some .genesis
  frame _ _ _ := True
  below := Block.Preceq
  headScope _ _ := True
  gateScope _ _ := True
  voteTime := timing.vote
  gateTime := timing.gate
  gateLabel r := r * 2
  headAtLabel := headAtLabel core (env Nat) run timing
  gate x s := (actionSourceFG core (env Nat) run timing x (s / 2)).map (Option.map erase)
  source x r := (actionSourceFG core (env Nat) run timing x r).map (Option.map erase)
private abbrev honestSlot (s : Slot) : Prop := s = 8 ∨ s = 10 ∨ s = 12 ∨ s = 14
private abbrev storedCarrier (_ : protocol.State) (X : FGBlock (Fin 1)) (a : protocol.Object) :=
  a ∈ X.rows.map wire
private abbrev sourceService (x r : Nat) (C : FGBlock (Fin 1)) :=
  actionSourceFG core (env Nat) run timing x r = some (some C)
private abbrev finBlock (X : FGBlock (Fin 1)) : Prop := ∃ k : Fin 8, X = block k
private abbrev ready (i x : Nat) (X : FGBlock (Fin 1)) (t : Time) : Prop :=
  ∃ k : Fin 7, X = block (k.val + 1) ∧
    run.events[i]? = some (.deliver x (prop (k.val + 1)) t)
private abbrev decodeProposal (o : protocol.Object) : Option (Slot × FGBlock (Fin 1)) :=
  match o.payload with | .inl X => some (X.slot, X) | .inr _ => none
private abbrev middleType (A : Block) :=
  KernelMiddleWitnessFG_W core reads obs timing (env Nat) run interface history electorate
    decodeProposal erase (fun X => X.rows.map wire) (fun _ => []) parentRead parentHeight
    validFor makeFG valid service cfg 2 2 point pt A

private theorem raw_origin_premises_sat :
    RawHistoryOrigin core reads (env Nat) run timing history := by
  have rows : ∀ k : Fin 8, ∀ u ∈ chainRows (block k),
      ∃ l : Fin 7, l.val < k.val ∧ u = row l := by decide +kernel
  have events : ∀ l : Fin 7,
      run.events[20 * l.val + 16]? =
        some (.deliver 7 (wire (row l)) (8 * l.val + 7)) ∧
      run.events[20 * l.val + 17]? =
        some (.deliver 9 (wire (row l)) (8 * l.val + 7)) := by
    intro l
    fin_cases l <;> exact ⟨rfl, rfl⟩
  have release : ∀ l : Fin 7,
      HonestRowAt reads (env Nat) run timing (20 * l.val + 12) 9 l (wire (row l)) := by
    intro l
    fin_cases l <;> exact ⟨by decide, rfl, by decide +kernel⟩
  intro i x B hheld u hu
  obtain ⟨k, hk, rfl⟩ := tree_cases.2 _ B hheld.2
  obtain ⟨l, hl, rfl⟩ := rows k u hu
  have hx : x = 7 ∨ x = 9 := by simpa using hheld.1
  rcases hx with rfl | rfl
  · change k.val ≤ (V2.D.Run.stateBefore (env Nat) run i 7).1.val at hk
    have hi := stage_before_premises_sat i 0
    change (V2.D.Run.stateBefore (env Nat) run i 7).1.val = _ at hi
    rw [hi] at hk
    change k.val ≤ min 7 ((i - 1) / 20) at hk
    refine ⟨wire (row l), l, rfl, rfl, 20 * l.val + 16, wire (row l),
      8 * l.val + 7, by omega, (events l).1, ?_⟩
    intro z hz _
    obtain ⟨seat, _, hseat⟩ := hz
    change 9 = z at hseat
    subst z
    exact ⟨⟨20 * l.val + 12, by omega, release l⟩, by change
      (4 : Int) * (l.val * 2 : Nat) + 6 ≤ 8 * l.val + 7; omega⟩
  · change k.val ≤ (V2.D.Run.stateBefore (env Nat) run i 9).1.val at hk
    have hi := stage_before_premises_sat i 1
    change (V2.D.Run.stateBefore (env Nat) run i 9).1.val = _ at hi
    rw [hi] at hk
    change k.val ≤ min 7 ((i - 2) / 20) at hk
    refine ⟨wire (row l), l, rfl, rfl, 20 * l.val + 17, wire (row l),
      8 * l.val + 7, by omega, (events l).2, ?_⟩
    intro z hz _
    obtain ⟨seat, _, hseat⟩ := hz
    change 9 = z at hseat
    subst z
    exact ⟨⟨20 * l.val + 12, by omega, release l⟩, by change
      (4 : Int) * (l.val * 2 : Nat) + 6 ≤ 8 * l.val + 7; omega⟩

#print axioms raw_origin_premises_sat

private theorem proposal_cases (s : Slot) (Q : Block)
    (h : HonestProposal (env Nat) run interface s Q) :
    ∃ k : Fin 7, s = 2 * (k.val + 1) ∧ Q = erase (block (k.val + 1)) := by
  obtain ⟨_, o, ⟨j, hj, hw⟩, hQ⟩ := h
  have hlen : j < 144 := (List.getElem?_eq_some_iff.mp hj).1
  rw [trace_premises_sat.2.1 ⟨j, hlen⟩] at hw
  dsimp only [Fin.val_mk] at hw
  split_ifs at hw with hr hp
  · obtain rfl := List.mem_singleton.mp hw
    change none = some Q at hQ
    cases hQ
  · have hk : j / 20 < 7 := by omega
    let k : Fin 7 := ⟨j / 20, hk⟩
    have he : j = 20 * k.val + 19 := by dsimp only [k]; omega
    obtain rfl := List.mem_singleton.mp hw
    have ht := (trace_premises_sat.2.2.1 k).2.1
    rw [← he] at ht
    have htick := V2.Event.tick.inj (Option.some.inj (ht.symm.trans hj))
    have ht' : 4 * (2 * (k.val + 1)) = 4 * s := by
      have htime := htick.2
      change (4 : Int) * (2 * (k.val + 1) : Nat) = (4 : Int) * (s : Nat) at htime
      exact_mod_cast htime
    change some (erase (block (j / 20 + 1))) = some Q at hQ
    exact ⟨k, by simp only [Slot] at *; omega, (Option.some.inj hQ).symm⟩
  · contradiction

#print axioms proposal_cases

private theorem reset_premises_sat :
    H0Reset core reads (env Nat) run obs timing
      (fun a => namedEntry (history.heightPair a)) 0 point.reset ∧
    timing.proposal (point.reset.sStar + 2) ≤ point.serviceStart ∧
    (env Nat).t_GST ≤ point.serviceStart ∧
    KernelPrem_W timing 2 run.horizon point pt honestSlot electorate.q
      (electorate.weightOf (Finset.univ \ historyFaulty reads run)) cfg.timeoutDelay 2 ∧
    KernelRunFacts reads (env Nat) run electorate 2 := by
  have old : oldRowHeights reads (env Nat) run timing
      (fun a => namedEntry (history.heightPair a)) 0 = ∅ := by
    ext h
    constructor
    · rintro ⟨j, y, r, a, e, _, _, ht⟩
      change (4 : Int) * (r * 2 : Nat) + 1 < 0 at ht
      omega
    · intro h
      cases h
  have mu : muOf reads (env Nat) run timing
      (fun a => namedEntry (history.heightPair a)) 0 = 1 := by
    unfold muOf
    rw [old]
    simp
  have release : ∀ l : Fin 7,
      HonestRowAt reads (env Nat) run timing (20 * l.val + 12) 9 l (wire (row l)) := by
    intro l
    fin_cases l <;> exact ⟨by decide, rfl, by decide +kernel⟩
  refine ⟨?_, by decide, by decide, ?_, ?_⟩
  · constructor
    · decide
    · intro r _; exact Nat.zero_le r
    · decide
    · decide +kernel
    · intro j y r a h e t ha he ht hn
      obtain ⟨k, rfl, rfl, rfl, rfl⟩ := owner_exact_rows j y r a ha
      have htime := V2.Event.tick.inj
        (Option.some.inj ((trace_premises_sat.2.2.1 k).1.symm.trans he))
      have hp : (k.val + 1, (block k).root) = (h, e) := Option.some.inj hn
      have hh : k.val + 1 = h := congrArg Prod.fst hp
      rw [← hh]
      change k.val + 1 ≤ 3
      rw [← htime.2] at ht
      change (4 : Int) * (k.val * 2 : Nat) + 6 ≤ 22 at ht
      omega
    · rw [mu]; decide
    · decide
    · decide
    · exact ⟨72, 9, wire (row 3), (block 3).root, release 3, rfl⟩
    · intro r h
      obtain ⟨j, y, a, e, ha, hn⟩ := h
      obtain ⟨k, rfl, rfl, rfl, rfl⟩ := owner_exact_rows j y r a ha
      have hp : (k.val + 1, (block k).root) = (4, e) := Option.some.inj hn
      have hh : k.val + 1 = 4 := congrArg Prod.fst hp
      change 3 ≤ k.val
      omega
    · rfl
    · refine ⟨72, 9, wire (row 3), block 3, release 3, ?_, ?_, rfl, ?_⟩
      · decide +kernel
      · exact trace_premises_sat.2.2.2 3 1
      · decide +kernel
    · decide
  · constructor
    · exact ⟨by decide⟩
    · rw [Gen.Pure.FGoodE_W_def]
      exact ⟨by decide, by decide, ⟨12, by decide, by decide, by decide⟩, by decide⟩
    · decide
    · decide
    · decide
    · rfl
    · decide
  · constructor
    · exact schedule_premises_sat
    · decide
    · decide
    · intro i j _; exact Subsingleton.elim _ _
    · intro x hx t ht hhor; rfl

#print axioms reset_premises_sat

private theorem universal_action_premises_sat : ∀ A (m : middleType A),
    KernelActionSupplyFG_W core reads obs timing (env Nat) run interface history
      electorate m := by
  have readStage : ∀ x : Fin 2,
      (postClock (env Nat) run (node x) 54).map (fun st : protocol.State => st.1.val) =
        some 6 := by decide +kernel
  have endStage : ∀ x : Fin 2,
      (V2.D.Run.stateBefore (env Nat) run (afterTicksIdx run 54) (node x)).1.val = 6 := by
    decide +kernel
  have honestRead (x : Nat) (nd : protocol.State)
      (hnd : postClock (env Nat) run x 54 = some nd) : x = 7 ∨ x = 9 := by
    unfold postClock preTick at hnd
    cases hi : V2.D.Run.tickIdx? run x 54 with
    | none => simp only [hi, Option.map_none] at hnd; contradiction
    | some j =>
      have he := V2.D.Run.tickIdx?_spec hi
      have hx := schedule_premises_sat.honest_only _ (List.mem_of_getElem? he)
      change x ∈ run.honest at hx
      simpa using hx
  have stageRead (x : Nat) (nd : protocol.State)
      (hnd : postClock (env Nat) run x 54 = some nd) : nd.1.val = 6 := by
    have h := congrArg (Option.map (fun st : protocol.State => st.1.val)) hnd
    rcases honestRead x nd hnd with rfl | rfl
    · have hr := readStage 0
      change (postClock (env Nat) run 7 54).map _ = some 6 at hr
      rw [hr] at h
      exact (Option.some.inj h).symm
    · have hr := readStage 1
      change (postClock (env Nat) run 9 54).map _ = some 6 at hr
      rw [hr] at h
      exact (Option.some.inj h).symm
  intro A m
  have hc : m.cD = 12 := by
    have h := m.earlySlot
    have hk : kappaF timing 2 = 2 := by decide
    change 10 + kappaF timing 2 ≤ m.cD ∧ m.cD ≤ 12 at h
    rw [hk] at h
    simp only [Slot] at *
    omega
  obtain ⟨k, hs, hQ⟩ := proposal_cases m.cD (erase m.X_D) m.honestD
  rw [hc] at hs
  have hk : k = 5 := Fin.ext (by simp only [Slot] at *; omega)
  subst k
  have hD : m.X_D = block 6 := erase_injective_premises_sat hQ
  constructor
  · intro x nd hnd
    change postClock (env Nat) run x 54 = some nd at hnd
    have hv := stageRead x nd hnd
    change store (V2.D.Run.stateBefore (env Nat) run (afterTicksIdx run 54) x).1.val =
      store nd.1.val
    rw [hv]
    rcases honestRead x nd hnd with rfl | rfl
    · have he := endStage 0
      change (V2.D.Run.stateBefore (env Nat) run (afterTicksIdx run 54) 7).1.val = 6 at he
      rw [he]
    · have he := endStage 1
      change (V2.D.Run.stateBefore (env Nat) run (afterTicksIdx run 54) 9).1.val = 6 at he
      rw [he]
  · intro x hx
    rw [hc, hD]
    constructor
    · intro _
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      have hs : actionSourceFG core (env Nat) run timing x 6 = some (some (block 6)) := by
        rcases hx' with rfl | rfl
        · exact trace_premises_sat.2.2.2 6 0
        · exact trace_premises_sat.2.2.2 6 1
      change (postClock (env Nat) run x 54).map core.source = _ at hs
      cases hst : postClock (env Nat) run x 54 with
      | none => simp only [hst, Option.map_none] at hs; contradiction
      | some st =>
        rw [hst] at hs
        exact ⟨st, hst, Option.some.inj hs⟩
    · intro h
      change (12 : Nat) < 12 at h
      omega
  · intro x nd _ _
    exact ⟨block nd.1, rfl, core_premises_sat.source_mem nd _ rfl⟩
  · intro x nd _ hnd H hH
    change postClock (env Nat) run x 54 = some nd at hnd
    have hv := stageRead x nd hnd
    have he : block nd.1 = H := Option.some.inj hH
    subst H
    change Block.Preceq (erase m.X_D) (erase (block nd.1.val))
    rw [hD, hv]
    decide +kernel

#print axioms universal_action_premises_sat

private theorem acceptance_effect_premises_sat :
    AcceptStep_W core (env Nat) run electorate cfg 2 ready ∧
    FGFinalityDurableLaws core ∧ ready 140 7 (block 7) 56 ∧ ready 141 9 (block 7) 56 := by
  let arrivalPred (i : Nat) (e : V2.Event Nat protocol.Object) : Prop :=
    match e with
    | .deliver x o t => ∀ k : Fin 7, o = prop (k.val + 1) →
        t = timing.proposal (2 * (k.val + 1)) ∧
        ((x = 7 ∧ i = 20 * k.val + 20) ∨ (x = 9 ∧ i = 20 * k.val + 21))
    | _ => True
  let arrivalDec (i : Nat) (e : V2.Event Nat protocol.Object) : Decidable (arrivalPred i e) := by
    cases e <;> dsimp only [arrivalPred] <;> infer_instance
  have arrivals : ∀ i : Fin 144,
      ((run.events[i.val]?).map (fun e => @decide (arrivalPred i e) (arrivalDec i e))).getD
        true = true := by decide +kernel
  have updates : ∀ k : Fin 7, ∀ x : Fin 2,
      let i := 20 * k.val + if x = 0 then 20 else 21
      let W := block (k.val + 1)
      (core.core (V2.D.Run.stateBefore (env Nat) run (i + 1) (node x))).fg =
        SimplexFG.Window.update_finality electorate cfg 2
          { (core.core (V2.D.Run.stateBefore (env Nat) run i (node x))).fg with
            TF := insert W (core.core (V2.D.Run.stateBefore (env Nat) run i (node x))).fg.TF } W ∧
      (SimplexFG.Window.derive electorate cfg 2 W).F ∈
        insert W (core.core (V2.D.Run.stateBefore (env Nat) run i (node x))).fg.TF := by
    decide +kernel
  refine ⟨?_, ?_, ⟨6, rfl, rfl⟩, ⟨6, rfl, rfl⟩⟩
  · rintro i x W t _ ⟨k, rfl, he⟩
    have hi : i < 144 := (List.getElem?_eq_some_iff.mp he).1
    have h := arrivals ⟨i, hi⟩
    rw [he] at h
    have hp : arrivalPred i (.deliver x (prop (k.val + 1)) t) := of_decide_eq_true h
    obtain ⟨rfl, hpos⟩ := hp k rfl
    rcases hpos with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact updates k 0
    · exact updates k 1
  · have mono : ∀ i j : Fin 8, i ≤ j → FGBlock.Preceq (store i).F (store j).F := by
      decide +kernel
    refine ⟨fun X => ⟨fun _ _ h => h, ?_, fun _ _ h => h⟩, fun _ _ => rfl⟩
    intro st o h
    have hl : st.1 ≤ (protocol.process st o).1 := by
      cases hp : o.payload with
      | inl X =>
        simpa only [protocol, hp] using
          (le_max_left st.1 (⟨min 7 (X.slot / 2), by omega⟩ : Fin 8))
      | inr u => simpa only [protocol, hp] using (le_refl st.1)
    exact KitFG.preceq_trans h (mono st.1 (protocol.process st o).1 hl)

#print axioms acceptance_effect_premises_sat

private theorem proposal_read_premises_sat (k : Fin 7) :
    ∃ nd : protocol.State,
      proposalStateAt (env Nat) run interface (2 * (k.val + 1)) = some nd ∧
      nd.1.val = k.val := by
  have proposer : ∀ s, V2.D.proposerOf run interface s = 7 := by
    intro s
    change (if 4 * s + 1 = 0 then 9 else 7) = 7
    exact ite_eq_right (Nat.succ_ne_zero _)
  have getter : ∀ k : Fin 7, V2.D.Run.tickIdx? run 7
      (V2.D.proposalTime interface (2 * (k.val + 1))) = some (20 * k.val + 19) := by
    decide +kernel
  refine ⟨V2.D.Run.stateBefore (env Nat) run (20 * k.val + 19) 7, ?_, ?_⟩
  · unfold proposalStateAt postClock preTick
    simp only [proposer, getter, Option.map_some]
  · have h := stage_before_premises_sat (20 * k.val + 19) 0
    change (V2.D.Run.stateBefore (env Nat) run (20 * k.val + 19) 7).1.val = _ at h
    rw [h]
    change min 7 ((20 * k.val + 19 - 1) / 20) = k.val
    omega

#print axioms proposal_read_premises_sat

private theorem proposal_data_premises_sat (k : Fin 7) :
    HonestProposal (env Nat) run interface (2 * (k.val + 1)) (erase (block (k.val + 1))) ∧
    OpeningCarrier_W (P := protocol) (n := 1) decodeProposal erase (fun X => X.rows.map wire)
      (fun nd Q => parentRead nd Q.parent) makeFG (env Nat) run interface
      (2 * (k.val + 1)) (erase (block (k.val + 1))) (block (k.val + 1)) ∧
    (∃ rows, HonestCarrier (env Nat) run interface
      (kernelCarrier (P := protocol) decodeProposal erase (fun X => X.rows.map wire))
      (2 * (k.val + 1)) (erase (block (k.val + 1))) rows ∧
      (block (k.val + 1)).rows = rows.filterMap reads.decode) ∧
    (∃ nd, proposalStateAt (env Nat) run interface (2 * (k.val + 1)) = some nd ∧
      parentRead nd (erase (block (k.val + 1))).parent = some (block k) ∧
      block k ∈ (core.core nd).fg.TF) ∧
    KernelExactService service run.horizon (2 * (k.val + 1)) (erase (block (k.val + 1))) := by
  have proposer : ∀ s, V2.D.proposerOf run interface s = 7 := by
    intro s
    change (if 4 * s + 1 = 0 then 9 else 7) = 7
    exact ite_eq_right (Nat.succ_ne_zero _)
  have emits : ∀ k : Fin 7,
      prop (k.val + 1) ∈ V2.D.Run.emitsAt (env Nat) run (20 * k.val + 19) := by
    decide +kernel
  have look : ∀ k : Fin 8, lookup (erase (block k)) = some (block k) := by decide +kernel
  have slot : ∀ k : Fin 8, (block k).slot = 2 * k.val := by decide +kernel
  have par : ∀ k : Fin 7, (erase (block (k.val + 1))).parent = erase (block k) := by
    intro k
    rw [block, erase]
    rfl
  have voteStage : ∀ k : Fin 7, ∀ x : Fin 2,
      (postClock (env Nat) run (node x) (timing.vote (2 * (k.val + 1)))).map
        (fun st : protocol.State => st.1.val) = some (k.val + 1) := by decide +kernel
  have heads : ∀ k : Fin 7, ∀ x : Fin 2,
      headAtLabel core (env Nat) run timing (node x) (2 * (k.val + 1)) =
        some (erase (block (k.val + 1))) := by
    intro k x
    have hv := voteStage k x
    cases hs : postClock (env Nat) run (node x) (timing.vote (2 * (k.val + 1))) with
    | none => rw [hs] at hv; cases hv
    | some st =>
      rw [hs] at hv
      have hv' : st.1.val = k.val + 1 := Option.some.inj hv
      unfold headAtLabel
      rw [hs]
      change some (erase (block st.1.val)) = _
      rw [hv']
  obtain ⟨nd, hnd, hv⟩ := proposal_read_premises_sat k
  have hem : V2.D.Run.emits (env Nat) run 7 (prop (k.val + 1))
      (V2.D.proposalTime interface (2 * (k.val + 1))) :=
    ⟨20 * k.val + 19, (trace_premises_sat.2.2.1 k).2.1, emits k⟩
  have hp : HonestProposal (env Nat) run interface (2 * (k.val + 1))
      (erase (block (k.val + 1))) := by
    refine ⟨⟨by simp only [Slot]; omega, ?_⟩, prop (k.val + 1), ?_, rfl⟩
    · rw [proposer]; decide
    · rw [proposer]; exact hem
  have hd : decodeProposal (prop (k.val + 1)) =
      some (2 * (k.val + 1), block (k.val + 1)) := by
    change some ((block (k.val + 1)).slot, block (k.val + 1)) = _
    rw [slot ⟨k.val + 1, by omega⟩]
  have hpar : parentRead nd (erase (block (k.val + 1))).parent = some (block k) := by
    change lookup _ = _
    rw [par k, look ⟨k.val, by omega⟩]
  have hmake : makeFG (block k) (erase (block (k.val + 1)))
      ((block (k.val + 1)).rows.map wire) = block (k.val + 1) := by
    change (lookup _).getD .genesis = _
    rw [look ⟨k.val + 1, by omega⟩]
    rfl
  have held := core_premises_sat.source_mem nd (block nd.1) rfl
  change block nd.1 ∈ (core.core nd).fg.TF at held
  rw [hv] at held
  have rowsDecode : ∀ rs : List (Row (Fin 1)), (rs.map wire).filterMap reads.decode = rs := by
    intro rs
    induction rs with
    | nil => rfl
    | cons a rs ih =>
      change a :: (rs.map wire).filterMap reads.decode = a :: rs
      rw [ih]
  refine ⟨hp, ⟨prop (k.val + 1), block (k.val + 1), nd, block k, ?_, rfl, hd,
    hnd, hpar, hmake⟩, ?_, ⟨nd, hnd, hpar, held⟩, ?_⟩
  · rw [proposer]; exact hem
  · refine ⟨(block (k.val + 1)).rows.map wire, ⟨hp, prop (k.val + 1), ?_,
      block (k.val + 1), hd, rfl, rfl⟩, (rowsDecode _).symm⟩
    rw [proposer]; exact hem
  · constructor
    · intro _ x hx _
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx' with rfl | rfl
      · exact heads k 0
      · exact heads k 1
    · intro hg x hx _
      change (4 : Int) * (2 * (k.val + 1) : Nat) + 6 ≤ 57 at hg
      have hr : k.val + 1 < 7 := by omega
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      have hs : actionSourceFG core (env Nat) run timing x (k.val + 1) =
          some (some (block (k.val + 1))) := by
        rcases hx' with rfl | rfl
        · exact trace_premises_sat.2.2.2 ⟨k.val + 1, hr⟩ 0
        · exact trace_premises_sat.2.2.2 ⟨k.val + 1, hr⟩ 1
      constructor
      · change (actionSourceFG core (env Nat) run timing x (2 * (k.val + 1) / 2)).map _ = _
        rw [show 2 * (k.val + 1) / 2 = k.val + 1 by omega, hs]
        rfl
      · intro r he
        change 2 * (k.val + 1) = r * 2 at he
        have he' : r = k.val + 1 := by omega
        subst r
        change (actionSourceFG core (env Nat) run timing x (k.val + 1)).map _ = _
        rw [hs]
        rfl

#print axioms proposal_data_premises_sat

-- Every owner proof argument on these exact data; action supplies every dependent witness.
private structure OwnerPremises : Prop where
  CL : FGCoreLaws core
  HL : FGHeadLaws core (env Nat) run
  keep : FGTreeKeepLaws core
  restore : FGTreeRestoreLaws core
  hc : FGCertificateLaws electorate obs.height obs.finality
  heightBridge : HeightBridge electorate cfg obs.height
  height_eq : obs.height = KitFG.Window.certificateHeight electorate cfg 2
  finality_eq : obs.finality = KitFG.Window.certificateFinality electorate cfg 2
  hne : ¬ electorate.IsQuorum ∅
  target : TargetJustification electorate obs.height
  foldTarget : ∀ y U X, X ≠ .genesis → EntryAt obs.height U y →
      FGBlock.Preceq U X.parent →
      ((obs.height X.parent).h = y → TargetCoveredByChild electorate obs.height X U y) →
      y + 1 ≤ (obs.height X).h
  noMixed : ∀ y U X, SlotChain X → EntryAt obs.height U y →
      FGBlock.Preceq U X.parent → X.slot < U.slot + cfg.timeoutDelay + 1 →
      NoMixedOnPath obs.height X y
  hK : KernelPrem_W timing 2 run.horizon point pt honestSlot electorate.q
      (electorate.weightOf (Finset.univ \ historyFaulty reads run)) cfg.timeoutDelay 2
  runFacts : KernelRunFacts reads (env Nat) run electorate 2
  hreset : timing.proposal (point.reset.sStar + 2) ≤ point.serviceStart
  hGSTstart : (env Nat).t_GST ≤ point.serviceStart
  reset : H0Reset core reads (env Nat) run obs timing (fun a => namedEntry (history.heightPair a)) 0
    point.reset
  historyTransfer : FGHistoricalHighTransfer core obs timing (env Nat) run interface point
    run.horizon
  chain : ∀ horizon, FGHistoricalHighChain core obs timing (env Nat) run point horizon
  reflect : ∀ A B, Block.Preceq (core.erase A) (core.erase B) → FGBlock.Preceq A B
  parent : ∀ B, core.erase B.parent = (core.erase B).parent
  hOrigin : RawHistoryOrigin core reads (env Nat) run timing history
  emission : HighRecordEmission reads timing (env Nat) run electorate cfg
  decoded : ∀ j x r a, HonestRowAt reads (env Nat) run timing j x r a → ∃ u, reads.decode a = some u
  receipt : TRowsReceipt core reads (env Nat) run timing (fun _ => []) 2
  honest_slot : ∀ s, honestSlot s → ∃ x, x ∈ run.honest
  proposal : ∀ s, honestSlot s → pt.r * timing.roundSlots ≤ s →
      s ≤ (pt.r + 2) * timing.roundSlots → ∃ Q, HonestProposal (env Nat) run interface s Q
  terminalProposal : honestSlot ((pt.r + 2) * timing.roundSlots + kappaF timing 2) →
      ∃ Q, HonestProposal (env Nat) run interface ((pt.r + 2) * timing.roundSlots + kappaF timing 2)
        Q
  carrier : ∀ s Q, HonestProposal (env Nat) run interface s Q →
      ∃ X : FGBlock (Fin 1), core.erase X = Q ∧
        OpeningCarrier_W decodeProposal erase (fun X => X.rows.map wire) (fun nd Q => parentRead nd
          Q.parent)
          makeFG (env Nat) run interface s Q X ∧ X.slot = s ∧
        (∃ rows, HonestCarrier (env Nat) run interface (kernelCarrier decodeProposal erase (fun X =>
          X.rows.map wire))
          s Q rows ∧ X.rows = rows.filterMap reads.decode) ∧
        ∃ nd, proposalStateAt (env Nat) run interface s = some nd ∧
          parentRead nd Q.parent = some X.parent ∧ X.parent ∈ (core.core nd).fg.TF
  exactService : ∀ s Q, HonestProposal (env Nat) run interface s Q → pt.r * timing.roundSlots ≤ s →
      KernelExactService service run.horizon s Q
  source_read : ∀ s Q r x, KernelExactService service run.horizon s Q →
      timing.gate s ≤ run.horizon → s = r * timing.roundSlots → x ∈ run.honest →
      pt.r * timing.roundSlots ≤ s → service.source x r = some (some Q)
  source_eq : ∀ x r, service.source x r =
      (actionSourceFG core (env Nat) run timing x r).map (Option.map core.erase)
  head_read : ∀ s Q x, KernelExactService service run.horizon s Q →
      pt.r * timing.roundSlots ≤ s → s ≤ (pt.r + 2) * timing.roundSlots → x ∈ run.honest →
      headAtLabel core (env Nat) run timing x s = some Q
  head_held : ∀ s X x, headAtLabel core (env Nat) run timing x s = some (core.erase X) →
      ∃ i, run.events[i]? = some (.tick x (timing.vote s)) ∧
        X ∈ (core.core (V2.D.Run.stateBefore (env Nat) run i x)).fg.TF
  slot_chain : ∀ i x X, X ∈ (core.core (V2.D.Run.stateBefore (env Nat) run i x)).fg.TF → SlotChain X
  closed : ∀ s nd, proposalStateAt (env Nat) run interface s = some nd →
      ∀ X ∈ (core.core nd).fg.TF, X.parent ∈ (core.core nd).fg.TF
  roots : ∀ s nd, proposalStateAt (env Nat) run interface s = some nd → ViewRootInj (core.core
    nd).fg.TF
  validRows : ∀ s nd, proposalStateAt (env Nat) run interface s = some nd →
      ∀ X ∈ (core.core nd).fg.TF, ∀ row ∈ X.rows,
        SimplexFG.Window.r6w (SimplexFG.Window.derive electorate cfg 2 X.parent) row = true
  parentEq : ∀ nd s X, parentHeight nd s X = ((obs.height X).h, (obs.height X).T_h.root)
  matchValid : ∀ nd s X a, valid a = true →
      namedEntry (history.heightPair a) = some (parentHeight nd s X) → validFor nd s X a = true
  hBatch : ∀ q y U X,
      BatchPrem core reads obs timing (env Nat) run interface history electorate decodeProposal
        erase (fun X => X.rows.map wire) (fun _ => [])
        parentRead parentHeight validFor 2 .target q y U X →
      (obs.height X.parent).h = y → TargetCoveredByChild electorate obs.height X U y
  hSOCOVTarget : ∀ i : Fin 1, safetyHolder reads run i ∈ run.honest → ∀ r C,
      actionSourceFG core (env Nat) run timing (safetyHolder reads run i) r = some (some C) →
      point.reset.M + 1 ≤ (obs.height C).h →
      (env Nat).awake (safetyHolder reads run i) (timing.action r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt reads (env Nat) run timing j (safetyHolder reads run i)
        rSent a ∧
        RowComplete reads run history.signer valid (safetyHolder reads run i) a ∧
        history.heightPair a = .vote (obs.height C).h (obs.height C).T_h.root false
  action : ∀ A (m : KernelMiddleWitnessFG_W core reads obs timing (env Nat) run interface history
    electorate decodeProposal erase
      (fun X => X.rows.map wire) (fun _ => []) parentRead parentHeight validFor makeFG valid service
        cfg 2 2 point pt A),
      KernelActionSupplyFG_W core reads obs timing (env Nat) run interface history electorate m
  wireDecode : ∀ row, reads.decode (wire row) = some row
  wireValid : ∀ i y U B,
      valid (wire ⟨i, .vote (y + 1) B false, some ⟨y, U⟩⟩) = true
  client : ∀ nd, (reads.inputs nd).1 = core.source nd
  release : ∀ i q nd row,
      postClock (env Nat) run (safetyHolder reads run i) (timing.action q) = some nd →
      (env Nat).awake (safetyHolder reads run i) (timing.action q) = true →
      (createRowOnce electorate cfg (reads.record nd) i (reads.inputs nd).1 (reads.inputs nd).2).1 =
        some row →
      ∃ j, run.events[j]? = some (.tick (safetyHolder reads run i) (timing.action q)) ∧
        reads.encode (wire row) ∈ V2.D.Run.emitsAt (env Nat) run j
  fields : ∀ nd H, core.finalityHead nd = some H →
      (reads.inputs nd).2 = certificateHeadFields obs.height obs.finality H
  hQC : RQCOrigin core reads (env Nat) run obs timing storedCarrier sourceService electorate
  recordHead : HighRecordHead core reads obs (env Nat) run
  clientLaws : FGSafetyClientLaws reads electorate cfg
  own : HighRecordOwnOrigin reads timing (env Nat) run
  hsel : TRowsSelect core reads (env Nat) run timing interface (kernelCarrier decodeProposal erase
    (fun X => X.rows.map wire))
      chainRowsRead (fun _ => []) parentRead validFor
  decode : ∀ a i, history.signer a = some i → ∃ u, reads.decode a = some u
  occurrence : ∀ s (Q : Block) H nd a u,
      proposalStateAt (env Nat) run interface s = some nd → parentRead nd Q.parent = some H →
      a ∈ chainRowsRead nd Q.parent → reads.decode a = some u →
      ∃ W, FGBlock.Preceq W H ∧ u ∈ W.rows
  validFor_eq : ∀ nd s B a, validFor nd s B a =
      ((reads.decode a).isSome && ((reads.decode a).map
        (SimplexFG.Window.r6w (KitFG.Window.parentState electorate cfg 2 B s))).getD false)
  pathValid : ∀ s nd, proposalStateAt (env Nat) run interface s = some nd → ∀ H ∈ (core.core
    nd).fg.TF,
      ∀ B s' root body rs, FGBlock.Preceq (.node B s' root body rs) H → ∀ a ∈ rs,
      (match a.height_pair with
        | .empty => false
        | .vote h _ _ => decide (1 ≤ h) &&
            (a.finality_pair.map (fun fp => decide (fp.height < h))).getD true) = true ∧
        SimplexFG.Window.r6w (SimplexFG.Window.derive electorate cfg 2 B) a = true
  dutyTime : ∀ s, timing.proposal s = V2.D.proposalTime interface s
  rowDurable : ∀ i j x a, i ≤ j →
      rowHeld core (fun _ => []) (V2.D.Run.stateBefore (env Nat) run i x) a →
      rowHeld core (fun _ => []) (V2.D.Run.stateBefore (env Nat) run j x) a
  rowClock : ∀ nd t a, rowHeld core (fun _ => []) nd a →
      rowHeld core (fun _ => []) (protocol.clock nd t) a
  step : AcceptStep_W core (env Nat) run electorate cfg 2 ready
  durable : FGFinalityDurableLaws core
  inv : ∀ i x, x ∈ run.honest → KitFG.FGStoreInvariant obs.height obs.finality
      (core.core (V2.D.Run.stateBefore (env Nat) run i x)).fg
  hI3 : ∀ C W, finBlock C → finBlock W →
      FGBlock.compatible (obs.finality C).F (obs.finality W).F = true
  readyBlock : ∀ i x X t, ready i x X t → finBlock X
  stored : ∀ i x, ∀ C ∈ (core.core (V2.D.Run.stateBefore (env Nat) run i x)).fg.TF,
      C ≠ .genesis → finBlock C
  rootScope : ∀ i x, x ∈ run.honest → ∀ C k u r a B,
      C ∈ (core.core (V2.D.Run.stateBefore (env Nat) run i x)).fg.TF →
      HonestRowAt reads (env Nat) run timing k u r a → actionSourceFG core (env Nat) run timing u r
        = some (some B) →
      (obs.height C).J.root = (obs.height B).T_h.root → (obs.height C).J = (obs.height B).T_h
  hStrat : ∀ j z W, z ∈ run.honest →
      W ∈ (core.core (V2.D.Run.stateBefore (env Nat) run j z)).fg.TF →
      ∀ J ∈ certified core obs W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore reads (env Nat) run timing j u r a ∧
        namedEntry (history.heightPair a) = some ((obs.height J).h, J.root)
  hEmittedSource : ∀ j z r a e, HonestRowAt reads (env Nat) run timing j z r a →
      namedEntry (history.heightPair a) = some e → ∃ C,
        actionSourceFG core (env Nat) run timing z r = some (some C) ∧
        e = ((obs.height C).h, (obs.height C).T_h.root) ∧
        FGBlock.Preceq (obs.height C).T_h C
  hcapBefore : ∀ (cut : Time) (b j : Nat) (z : Nat) (W : FGBlock (Fin 1)),
      j ≤ V2.D.Run.idxBefore run cut → HeldAt core (env Nat) run j z W →
      (∀ k u r a row h B timeout, HonestRowAt reads (env Nat) run timing k u r a →
        reads.decode a = some row → row.height_pair = .vote h B timeout →
        timing.action r < cut → h < b + 1) → (obs.height W).h < b + 2
  delivery : ∀ (X U : FGBlock (Fin 1)) rows,
      HonestCarrier (env Nat) run interface (kernelCarrier decodeProposal erase (fun X => X.rows.map
        wire))
        X.slot (core.erase X) rows →
      (env Nat).t_GST ≤ timing.proposal X.slot → timing.proposal X.slot + timing.delta ≤ run.horizon
        →
      FGBlock.Preceq U (SimplexFG.Window.derive electorate cfg 2 X).F →
      Nonempty (BlockDelivery_W core (env Nat) run ready X U (timing.proposal X.slot)
        (timing.proposal X.slot + timing.delta))

set_option maxHeartbeats 8000000 in
-- Discharge all 71 owner leaves over the full mixed-run fold and certificate views.
private theorem owner_premises_sat : OwnerPremises := by
  let hc : FGCertificateLaws electorate obs.height obs.finality :=
    KitFG.Window.windowCertificateLaws electorate cfg 2 (by change ¬ (1 ≤ 0); decide)
      (by decide)
  let height := hc.height
  have baseRefl (B : Block) : Block.Preceq B B := by
    cases B with
    | genesis => rfl
    | node P sl root body =>
      change (decide (Block.node P sl root body = .node P sl root body) ||
        Block.preceq (.node P sl root body) P) = true
      simp only [decide_true, Bool.true_or]
  have forward : ∀ A B : FGBlock (Fin 1), FGBlock.Preceq A B →
      Block.Preceq (erase A) (erase B) := by
    intro A B h
    induction B with
    | genesis =>
      obtain rfl := preceq_genesis.mp h
      exact baseRefl _
    | node P sl root body rs ih =>
      change (decide (A = .node P sl root body rs) || FGBlock.preceq A P) = true at h
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with rfl | hp
      · exact baseRefl _
      · rw [erase]
        exact Bool.or_eq_true_iff.mpr (Or.inr (ih hp))
  have compatible (i j : Fin 8) : Block.Compatible (erase (block i)) (erase (block j)) := by
    apply Bool.or_eq_true_iff.mpr
    rcases le_total i j with hij | hji
    · exact Or.inl (forward _ _ ((data_premises_sat.2.1 i j).mpr hij))
    · exact Or.inr (forward _ _ ((data_premises_sat.2.1 j i).mpr hji))
  have releaseRow : ∀ l : Fin 7,
      HonestRowAt reads (env Nat) run timing (20 * l.val + 12) 9 l (wire (row l)) := by
    intro l
    fin_cases l <;> exact ⟨by decide, rfl, by decide +kernel⟩
  have closed : ∀ nd : protocol.State, ∀ X ∈ (core.core nd).fg.TF,
      X.parent ∈ (core.core nd).fg.TF := by
    have h : ∀ k : Fin 8, ∀ X ∈ (store k).TF, X.parent ∈ (store k).TF := by decide +kernel
    intro nd
    exact h nd.1
  have slot : ∀ k : Fin 8, (block k).slot = 2 * k.val := by decide +kernel
  have par : ∀ k : Fin 7, (block (k.val + 1)).parent = block k := by decide +kernel
  have erasePar : ∀ k : Fin 7, (erase (block (k.val + 1))).parent = erase (block k) := by
    intro k
    rw [block, erase]
    rfl
  have look : ∀ k : Fin 8, lookup (erase (block k)) = some (block k) := by decide +kernel
  have validRows : ∀ k : Fin 8, ∀ a ∈ (block k).rows,
      (match a.height_pair with
        | .empty => false
        | .vote h _ _ => decide (1 ≤ h) &&
            (a.finality_pair.map (fun fp => decide (fp.height < h))).getD true) = true ∧
      SimplexFG.Window.r6w (SimplexFG.Window.derive electorate cfg 2 (block k).parent) a =
        true := by decide +kernel
  have rootScope : ∀ c : Fin 8, ∀ k : Fin 7,
      (obs.height (block c)).J.root = (obs.height (block k)).T_h.root →
      (obs.height (block c)).J = (obs.height (block k)).T_h := by decide +kernel
  have emittedSource : ∀ j z r a e, HonestRowAt reads (env Nat) run timing j z r a →
      namedEntry (history.heightPair a) = some e → ∃ C,
        actionSourceFG core (env Nat) run timing z r = some (some C) ∧
        e = ((obs.height C).h, (obs.height C).T_h.root) ∧
        FGBlock.Preceq (obs.height C).T_h C := by
    intro j z r a e ha he
    obtain ⟨k, rfl, rfl, rfl, rfl⟩ := owner_exact_rows j z r a ha
    have hn : (k.val + 1, (block k).root) = e := Option.some.inj he
    refine ⟨block k, trace_premises_sat.2.2.2 k 1, ?_, ?_⟩
    · rw [← hn, (data_premises_sat.1 ⟨k.val, by omega⟩).1,
        (data_premises_sat.1 ⟨k.val, by omega⟩).2.1]
    · rw [(data_premises_sat.1 ⟨k.val, by omega⟩).2.1]
      exact preceq_refl _
  refine {
    CL := core_premises_sat
    HL := ⟨?_, ?_⟩
    keep := ⟨fun _ _ => Finset.Subset.refl _⟩
    restore := ⟨fun _ _ => rfl⟩
    hc := hc
    heightBridge := KitFG.Window.windowHeightBridge electorate cfg 2 (by decide)
    height_eq := rfl
    finality_eq := rfl
    hne := by change ¬ (1 ≤ 0); decide
    target := certificate_premises_sat.1
    foldTarget := certificate_premises_sat.2.1
    noMixed := certificate_premises_sat.2.2
    hK := reset_premises_sat.2.2.2.1
    runFacts := reset_premises_sat.2.2.2.2
    hreset := reset_premises_sat.2.1
    hGSTstart := reset_premises_sat.2.2.1
    reset := reset_premises_sat.1
    historyTransfer := ?_
    chain := ?_
    reflect := reflection_premises_sat
    parent := ?_
    hOrigin := raw_origin_premises_sat
    emission := ?_
    decoded := ?_
    receipt := ?_
    honest_slot := fun _ _ => ⟨7, by decide⟩
    proposal := ?_
    terminalProposal := ?_
    carrier := ?_
    exactService := ?_
    source_read := ?_
    source_eq := fun _ _ => rfl
    head_read := ?_
    head_held := ?_
    slot_chain := ?_
    closed := fun _ nd _ => closed nd
    roots := ?_
    validRows := ?_
    parentEq := fun _ _ _ => rfl
    matchValid := ?_
    hBatch := ?_
    hSOCOVTarget := ?_
    action := universal_action_premises_sat
    wireDecode := fun _ => rfl
    wireValid := fun _ _ _ _ => rfl
    client := fun _ => rfl
    release := ?_
    fields := ?_
    hQC := ?_
    recordHead := ?_
    clientLaws := client_premises_sat
    own := ?_
    hsel := ?_
    decode := ?_
    occurrence := ?_
    validFor_eq := fun _ _ _ _ => rfl
    pathValid := ?_
    dutyTime := fun _ => rfl
    rowDurable := fun _ _ _ _ _ h => h
    rowClock := fun _ _ _ h => h
    step := acceptance_effect_premises_sat.1
    durable := acceptance_effect_premises_sat.2.1
    inv := fun _ _ _ => store_invariant_premises_sat _
    hI3 := ?_
    readyBlock := ?_
    stored := ?_
    rootScope := ?_
    hStrat := ?_
    hEmittedSource := emittedSource
    hcapBefore := ?_
    delivery := ?_ }
  · intro i x t s
    exact ⟨block (V2.D.Run.stateBefore (env Nat) run i x).1,
      core_premises_sat.source_mem _ _ rfl, rfl⟩
  · intro i x X hX
    exact closed _ X hX
  · intro x r C _ hs _ _ s Q hp _ hafter
    obtain ⟨_, hr, rfl⟩ := source_cases x r C hs
    obtain ⟨k, rfl, rfl⟩ := proposal_cases s Q hp
    have hle : r ≤ k.val := by change r * 2 + 2 ≤ 2 * (k.val + 1) at hafter; omega
    rw [erasePar k]
    exact forward _ _ ((data_premises_sat.2.1 ⟨r, by omega⟩ ⟨k.val, by omega⟩).mpr hle)
  · intro horizon x y r r' C D _ _ hs hs' _ _ _ _
    obtain ⟨_, hr, rfl⟩ := source_cases x r C hs
    obtain ⟨_, hr', rfl⟩ := source_cases y r' D hs'
    exact ⟨compatible ⟨r, by omega⟩ ⟨r', by omega⟩, compatible ⟨r, by omega⟩ 3⟩
  · intro B
    cases B <;> simp [erase, FGBlock.parent, Block.parent]
  · intro j x r a u ha hu
    obtain ⟨k, rfl, rfl, rfl, rfl⟩ := owner_exact_rows j x r a ha
    have he : row k = u := Option.some.inj hu
    subst u
    fin_cases k <;> decide +kernel
  · intro j x r a ha
    obtain ⟨k, _, _, _, rfl⟩ := owner_exact_rows j x r a ha
    exact ⟨row k, rfl⟩
  · intro j y r a ha _ x _
    obtain ⟨k, _, _, _, rfl⟩ := owner_exact_rows j y r a ha
    apply Or.inl
    exact List.mem_map.mpr ⟨k.val, List.mem_range.mpr k.isLt, rfl⟩
  · intro s hs _ _
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨_, (proposal_data_premises_sat 3).1⟩
    · exact ⟨_, (proposal_data_premises_sat 4).1⟩
    · exact ⟨_, (proposal_data_premises_sat 5).1⟩
    · exact ⟨_, (proposal_data_premises_sat 6).1⟩
  · intro _
    exact ⟨_, (proposal_data_premises_sat 6).1⟩
  · intro s Q hp
    obtain ⟨k, rfl, rfl⟩ := proposal_cases s Q hp
    obtain ⟨_, hcar, hrows, hnd, _⟩ := proposal_data_premises_sat k
    refine ⟨block (k.val + 1), rfl, hcar, slot ⟨k.val + 1, by omega⟩, hrows, ?_⟩
    rw [par k]
    exact hnd
  · intro s Q hp _
    obtain ⟨k, rfl, rfl⟩ := proposal_cases s Q hp
    exact (proposal_data_premises_sat k).2.2.2.2
  · intro s Q r x hs hg he hx _
    exact (hs.2 hg x hx trivial).2 r he
  · intro s Q x hs _ hhi hx
    apply hs.1 _ x hx trivial
    change (4 : Int) * (s : Nat) + 1 ≤ 57
    change s ≤ 12 at hhi
    simp only [Slot] at *
    omega
  · intro s X x hh
    unfold headAtLabel postClock preTick at hh
    cases hi : V2.D.Run.tickIdx? run x (timing.vote s) with
    | none => simp only [hi, Option.map_none] at hh; contradiction
    | some j =>
      simp only [hi, Option.map_some, Option.some.injEq] at hh
      have hx : block (V2.D.Run.stateBefore (env Nat) run j x).1 = X :=
        erase_injective_premises_sat hh
      refine ⟨j, V2.D.Run.tickIdx?_spec hi, ?_⟩
      rw [← hx]
      exact core_premises_sat.source_mem _ _ rfl
  · intro i x X hX W hW hn
    obtain ⟨k, _, rfl⟩ := tree_cases.2 _ X hX
    obtain ⟨l, hl, rfl⟩ := tree_cases.1 k W hW
    exact (by decide +kernel : ∀ l : Fin 8, block l ≠ .genesis →
      (block l).parent.slot < (block l).slot) ⟨l, by omega⟩ hn
  · intro s nd _ X Y ⟨W, hW, hX⟩ ⟨Z, hZ, hY⟩ hr
    have hx := KitFG.ancestor_closed_of_parent_closed _ (closed nd) W hW X hX
    have hy := KitFG.ancestor_closed_of_parent_closed _ (closed nd) Z hZ Y hY
    obtain ⟨k, _, rfl⟩ := tree_cases.2 nd X hx
    obtain ⟨l, _, rfl⟩ := tree_cases.2 nd Y hy
    have he := data_premises_sat.2.2 k l hr
    cases he
    rfl
  · intro s nd _ X hX a ha
    obtain ⟨k, _, rfl⟩ := tree_cases.2 nd X hX
    exact (validRows k a ha).2
  · intro nd s X a hv hn
    cases hd : decode a with
    | none => change (decode a).isSome = true at hv; rw [hd] at hv; cases hv
    | some u =>
      have hm : u.height_pair.matchesEntry (obs.height X).h (obs.height X).T_h.root =
          true := by
        rw [history.decode_height a u hd] at hn
        cases hp : u.height_pair with
        | empty => rw [hp] at hn; cases hn
        | vote h b timeout =>
          rw [hp] at hn
          have he : (h, b) = ((obs.height X).h, (obs.height X).T_h.root) :=
            Option.some.inj hn
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
          simp [NamedHeightPair.matchesEntry]
      change ((decode a).isSome && ((decode a).map _).getD false) = true
      rw [hd]
      change SimplexFG.Window.r6w _ u = true
      rw [SimplexFG.Window.r6w_def]
      apply Bool.or_eq_true_iff.mpr
      exact Or.inl hm
  · intro q y U X h hp
    obtain ⟨rows, hcar, _⟩ := h.carrier
    obtain ⟨k, hs, hX⟩ := proposal_cases X.slot (erase X) hcar.1
    have he : X = block (k.val + 1) := erase_injective_premises_sat hX
    subst X
    have hpath := h.path
    rw [par k] at hp hpath
    have hT := (height.entry_plateau hpath (h.entry.1.trans hp.symm)).symm.trans h.entry.2
    have cover : ∀ k : Fin 7, TargetCoveredByChild electorate obs.height
        (block (k.val + 1)) (obs.height (block k)).T_h (obs.height (block k)).h := by
      intro k
      refine ⟨{0}, by decide, ?_⟩
      intro i hi
      have hi' : i = 0 := Subsingleton.elim _ _
      subst i
      right
      refine ⟨row k, ?_, rfl, ?_⟩
      · exact (by decide +kernel : ∀ k : Fin 7, row k ∈ (block (k.val + 1)).rows) k
      · rw [(data_premises_sat.1 ⟨k.val, by omega⟩).1,
          (data_premises_sat.1 ⟨k.val, by omega⟩).2.1]
    rw [← hp, ← hT]
    exact cover k
  · intro i _ r C hs _ _
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain ⟨_, hr, rfl⟩ := source_cases 9 r C hs
    let k : Fin 7 := ⟨r, hr⟩
    refine ⟨20 * r + 12, r, wire (row r), le_rfl, releaseRow k, ⟨rfl, 0, rfl, rfl⟩, ?_⟩
    rw [(data_premises_sat.1 ⟨r, by omega⟩).1,
      (data_premises_sat.1 ⟨r, by omega⟩).2.1]
    rfl
  · intro i q nd u hnd _ hu
    obtain rfl : i = 0 := Subsingleton.elim _ _
    change postClock (env Nat) run 9 (timing.action q) = some nd at hnd
    unfold postClock preTick at hnd
    cases hi : V2.D.Run.tickIdx? run 9 (timing.action q) with
    | none => simp only [hi, Option.map_none] at hnd; contradiction
    | some j =>
      simp only [hi, Option.map_some, Option.some.injEq] at hnd
      subst nd
      have he := V2.D.Run.tickIdx?_spec hi
      have ht : timing.action q % 8 = 6 := by
        change ((4 : Int) * (q * 2 : Nat) + 6) % 8 = 6
        omega
      have hl : protocol.signLabel (timing.action q) = 0 := ite_eq_left ht
      have hf : run.ownSeats (protocol.signLabel (timing.action q)) 9 = [0] := by
        rw [hl]
        rfl
      have hu' : (createRowOnce electorate cfg
          (V2.D.Run.stateBefore (env Nat) run j 9).2 0
          (some (block (V2.D.Run.stateBefore (env Nat) run j 9).1))
          (head (V2.D.Run.stateBefore (env Nat) run j 9).1)).1 = some u := hu
      have ha : protocol.act (V2.D.Run.stateBefore (env Nat) run j 9) (timing.action q) () =
          some (.inr u) := by
        change (if timing.action q % 8 = 6 then _ else _) = _
        rw [ite_eq_left ht, hu']
        rfl
      refine ⟨j, he, ?_⟩
      rw [V2.D.Run.emitsAt, he]
      have ht' := ht
      change ((4 : Int) * (q * 2 : Nat) + 6) % 8 = 6 at ht'
      push_cast at ht'
      simp [V2.D.tick, V2.D.Run.ownSeats, List.finRange_succ, ht', hu']
  · intro nd H hH
    have he : block nd.1 = H := Option.some.inj hH
    subst H
    rfl
  · intro i x W hx hW
    let origin := fun C (u : Row (Fin 1)) =>
      ∃ y r a, HonestRowBefore reads (env Nat) run timing i y r a ∧ reads.decode a = some u ∧
        storedCarrier (V2.D.Run.stateBefore (env Nat) run i x) C a ∧ ∃ B,
          actionSourceFG core (env Nat) run timing y r = some (some B) ∧
          namedEntry u.height_pair = some ((obs.height B).h, (obs.height B).T_h.root) ∧
          FGBlock.Preceq (obs.height B).T_h B ∧ sourceService y r B
    have origins : ∀ C u, FGBlock.Preceq C W → u ∈ C.rows → origin C u := by
      intro C u hCW hu
      obtain ⟨a, r, ha, hs, j, o, t, hji, he, hold⟩ := raw_origin_premises_sat i x W
        ⟨hx, hW⟩ u (KitFG.mem_chainRows_of_carrier hCW hu)
      obtain ⟨⟨l, hli, hl⟩, _⟩ := hold 9 ⟨u.signer, hs, rfl⟩ (by decide)
      obtain ⟨k, _, _, hr, hw⟩ := owner_exact_rows l 9 r a hl
      subst r
      subst a
      have heq : row k = u := Option.some.inj ha
      subst u
      have hsrc := trace_premises_sat.2.2.2 k 1
      refine ⟨9, k, wire (row k), ⟨l, hli, hl⟩, rfl,
        List.mem_map.mpr ⟨row k, hu, rfl⟩, block k, hsrc, ?_, ?_, hsrc⟩
      · rw [(data_premises_sat.1 ⟨k.val, by omega⟩).1,
          (data_premises_sat.1 ⟨k.val, by omega⟩).2.1]
        rfl
      · rw [(data_premises_sat.1 ⟨k.val, by omega⟩).2.1]
        exact preceq_refl _
    refine ⟨?_, ?_, ?_⟩
    · intro m X Q rows _ _ _ _ hQ hrows
      obtain ⟨j, hj, _⟩ := KitFG.honest_in_quorum electorate ∅ hQ (by change 0 < 1; decide)
      exact ⟨j, hj, origins _ _ (hrows j hj).1 (hrows j hj).2.1⟩
    · intro Q rows _ hQ hrows
      obtain ⟨j, hj, _⟩ := KitFG.honest_in_quorum electorate ∅ hQ (by change 0 < 1; decide)
      exact ⟨j, hj, origins _ _ (hrows j hj).1 (hrows j hj).2.1⟩
    · intro hfin
      obtain ⟨k, _, rfl⟩ := tree_cases.2 _ W hW
      have facts : ∀ k : Fin 8, (obs.finality (block k)).F ≠ .genesis →
          FGBlock.Preceq (block (k.val - 1)) (block k) ∧
          (obs.height (block (k.val - 1))).J = (obs.finality (block k)).F ∧
          (obs.height (block (k.val - 1))).h_j = (obs.finality (block k)).h_F ∧
          (∀ j : Fin 1, FGBlock.Preceq (block (k.val - 1)) (block (k.val - 1)) ∧
            row (k.val - 2) ∈ (block (k.val - 1)).rows ∧ (row (k.val - 2)).signer = j ∧
            (row (k.val - 2)).height_pair = .vote
              (obs.height (block (k.val - 1))).h_j
              (obs.height (block (k.val - 1))).J.root false) := by decide +kernel
      obtain ⟨hp, hJ, hh, hrs⟩ := facts k hfin
      refine ⟨block (k.val - 1), hp, hJ, hh, Finset.univ,
        (fun _ => (block (k.val - 1), row (k.val - 2))), (by change (1 : Nat) ≤ 1; decide),
        fun j _ => hrs j, 0, by decide, origins _ _ hp (hrs 0).2.1⟩
  · intro i x t _
    right
    exact ⟨block (V2.D.Run.stateBefore (env Nat) run i x).1,
      core_premises_sat.source_mem _ _ rfl, rfl⟩
  · intro j x o u hx ho hd
    split_ifs at ho with hnode
    · have hi : j < 144 := by
        by_contra hn
        have he : run.events[j]? = none := List.getElem?_eq_none_iff.mpr (by change 144 ≤ j; omega)
        unfold V2.D.Run.emitsAt at ho
        rw [he] at ho
        contradiction
      rw [trace_premises_sat.2.1 ⟨j, hi⟩] at ho
      dsimp only [Fin.val_mk] at ho
      split_ifs at ho with hr hp
      · obtain rfl := List.mem_singleton.mp ho
        let k : Fin 7 := ⟨j / 20, by omega⟩
        have hj : j = 20 * k.val + 12 := by dsimp only [k]; omega
        have he := (trace_premises_sat.2.2.1 k).1
        rw [← hj] at he
        rw [he] at hnode
        have hx' : x = 9 := (Option.some.inj hnode).symm
        subst x
        refine ⟨k, wire (row k), ?_, hd⟩
        rw [hj]
        exact releaseRow k
      · obtain rfl := List.mem_singleton.mp ho
        change none = some u at hd
        cases hd
      · contradiction
    · contradiction
  · intro s Q rows j y r a hcar ha hv _
    obtain ⟨k, rfl, rfl⟩ := proposal_cases s Q hcar.1
    obtain ⟨o, _, N, hd, he, hr⟩ := hcar.2
    have hN : N = block (k.val + 1) := erase_injective_premises_sat he
    subst N
    obtain ⟨l, _, _, _, rfl⟩ := owner_exact_rows j y r a ha
    obtain ⟨nd, H, _, hp, hvalid⟩ := hv
    change lookup (erase (block (k.val + 1))).parent = some H at hp
    rw [erasePar k, look ⟨k.val, by omega⟩] at hp
    have hH : block k = H := Option.some.inj hp
    subst H
    have valid_le : ∀ k l : Fin 7,
        validFor protocol.init (2 * (k.val + 1)) (block k) (wire (row l)) = true →
        l.val ≤ k.val := by decide +kernel
    have hle := valid_le k l hvalid
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · left
      have he' : l = k := Fin.ext heq
      subst l
      rw [← hr]
      exact List.mem_map.mpr ⟨row k,
        (by decide +kernel : ∀ k : Fin 7, row k ∈ (block (k.val + 1)).rows) k, rfl⟩
    · right
      obtain ⟨nd, hnd, _, _⟩ := (proposal_data_premises_sat k).2.2.2.1
      refine ⟨nd, hnd, ?_⟩
      change wire (row l) ∈ ((lookup _).map _).getD []
      rw [erasePar k, look ⟨k.val, by omega⟩]
      change wire (row l) ∈ (List.range ((block k).slot / 2)).map _
      rw [slot ⟨k.val, by omega⟩]
      change wire (row l) ∈ (List.range (2 * k.val / 2)).map _
      apply List.mem_map.mpr
      exact ⟨l.val, List.mem_range.mpr (by omega), rfl⟩
  · intro a i hs
    cases hd : decode a with
    | none => change (decode a).map _ = some i at hs; rw [hd] at hs; cases hs
    | some u => exact ⟨u, hd⟩
  · intro s Q H nd a u _ hp ha hd
    change lookup Q.parent = some H at hp
    have hm := List.mem_of_find?_eq_some hp
    obtain ⟨k, hk, hH⟩ := List.mem_map.mp hm
    have hk' : k < 8 := List.mem_range.mp hk
    subst H
    change a ∈ ((lookup Q.parent).map _).getD [] at ha
    rw [hp] at ha
    change a ∈ (List.range ((block k).slot / 2)).map _ at ha
    rw [slot ⟨k, hk'⟩] at ha
    change a ∈ (List.range (2 * k / 2)).map _ at ha
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
    have hl' : l < k := by have := List.mem_range.mp hl; omega
    have hu : row l = u := Option.some.inj hd
    subst u
    refine ⟨block (l + 1), ?_, ?_⟩
    · exact (data_premises_sat.2.1 ⟨l + 1, by omega⟩ ⟨k, hk'⟩).mpr (show l + 1 ≤ k by omega)
    · exact (by decide +kernel : ∀ l : Fin 7, row l ∈ (block (l.val + 1)).rows) ⟨l, by omega⟩
  · intro s nd _ H hH B s' root body rs hp a ha
    have hm := KitFG.ancestor_closed_of_parent_closed _ (closed nd) H hH _ hp
    obtain ⟨k, _, he⟩ := tree_cases.2 nd (.node B s' root body rs) hm
    have hB : B = (block k).parent := congrArg FGBlock.parent he
    have hrs : rs = (block k).rows := congrArg FGBlock.rows he
    have ha' : a ∈ (block k).rows := hrs ▸ ha
    rw [hB]
    exact validRows k a ha'
  · intro C W hC hW
    obtain ⟨k, hk⟩ := hC
    obtain ⟨l, hl⟩ := hW
    rw [hk, hl]
    exact (by decide +kernel : ∀ k l : Fin 8,
      FGBlock.compatible (obs.finality (block k)).F (obs.finality (block l)).F = true) k l
  · rintro i x X t ⟨k, rfl, _⟩
    exact ⟨⟨k.val + 1, by omega⟩, rfl⟩
  · intro i x C hC _
    obtain ⟨k, _, he⟩ := tree_cases.2 _ C hC
    exact ⟨k, he⟩
  · intro i x _ C j u r a B hC ha hs hr
    obtain ⟨c, _, rfl⟩ := tree_cases.2 _ C hC
    obtain ⟨k, _, rfl, rfl, _⟩ := owner_exact_rows j u r a ha
    obtain ⟨_, _, rfl⟩ := source_cases 9 k B hs
    exact rootScope c k hr
  · intro i x W hx hW J hJ hn
    obtain ⟨k, hk, rfl⟩ := tree_cases.2 _ W hW
    obtain ⟨B, hB, hJ⟩ := hJ
    obtain ⟨m, hm, rfl⟩ := tree_cases.1 k B hB
    let mi : Fin 8 := ⟨m, by omega⟩
    have entries : ∀ k m : Fin 8, m ≤ k →
        ((obs.height (block m)).J ≠ .genesis → ∃ l : Fin 7,
          l.val < k.val ∧ (obs.height (block m)).J = block l) ∧
        ((obs.finality (block m)).F ≠ .genesis → ∃ l : Fin 7,
          l.val < k.val ∧ (obs.finality (block m)).F = block l) ∧
        ((obs.height (block m)).h < (obs.height (block k)).h →
          (obs.height (block m)).T_h ≠ .genesis → ∃ l : Fin 7,
            l.val < k.val ∧ (obs.height (block m)).T_h = block l) := by decide +kernel
    have earlier : ∃ l : Fin 7, l.val < k.val ∧ J = block l := by
      rcases hJ with rfl | rfl | ⟨rfl, hh⟩
      · exact (entries k mi hm).1 hn
      · exact (entries k mi hm).2.1 hn
      · exact (entries k mi hm).2.2 hh hn
    obtain ⟨l, hl, rfl⟩ := earlier
    refine ⟨9, l, wire (row l), ⟨20 * l.val + 12, ?_, releaseRow l⟩, ?_⟩
    · have hx' : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx' with rfl | rfl
      · have hs := stage_before_premises_sat i 0
        change (V2.D.Run.stateBefore (env Nat) run i 7).1.val = _ at hs
        change k.val ≤ (V2.D.Run.stateBefore (env Nat) run i 7).1.val at hk
        rw [hs] at hk
        change k.val ≤ min 7 ((i - 1) / 20) at hk
        omega
      · have hs := stage_before_premises_sat i 1
        change (V2.D.Run.stateBefore (env Nat) run i 9).1.val = _ at hs
        change k.val ≤ (V2.D.Run.stateBefore (env Nat) run i 9).1.val at hk
        rw [hs] at hk
        change k.val ≤ min 7 ((i - 2) / 20) at hk
        omega
    · rw [(data_premises_sat.1 ⟨l.val, by omega⟩).1]
      rfl
  · intro cut b j z W hj hW hrows
    have cap := raw_causal_cap_before (R := core) (S := reads) (E := env Nat) (rho := run)
      (T := timing) (D := history) (Ef := electorate) (H := obs.height) (f := obs.finality)
      (hc := hc) (horigin := raw_origin_premises_sat) schedule_premises_sat
      (by decide) b cut (by
        intro k u r a h t ha hh he ht
        obtain ⟨l, rfl, rfl, rfl, rfl⟩ := owner_exact_rows k u r a ha
        change some (l.val + 1) = some h at hh
        have hh' : l.val + 1 = h := Option.some.inj hh
        subst h
        change run.events[20 * l.val + 12]?.map V2.Event.time = some t at he
        rw [(trace_premises_sat.2.2.1 l).1] at he
        have htime : timing.action l = t := Option.some.inj he
        have hbound := hrows (20 * l.val + 12) 9 l (wire (row l)) (row l)
          (l.val + 1) (block l).root false (releaseRow l) rfl rfl (htime ▸ ht)
        change l.val + 1 < b + 1 at hbound
        change l.val + 1 ≤ b
        exact Nat.le_of_lt_succ hbound) j z W hj hW
    change (obs.height W).h ≤ b + 1 at cap
    simp only [Height] at *
    omega
  · intro X U rows hcar _ _ _
    obtain ⟨k, hs, hX⟩ := proposal_cases X.slot (erase X) hcar.1
    have he : X = block (k.val + 1) := erase_injective_premises_sat hX
    subst X
    rw [slot ⟨k.val + 1, by omega⟩]
    refine ⟨{
      selected := fun x _ => if x = 7 then
      ⟨20 * k.val + 20, timing.proposal (2 * (k.val + 1))⟩ else
      ⟨20 * k.val + 21, timing.proposal (2 * (k.val + 1))⟩
      witness := ?_ }⟩
    intro x hx
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl
    · change run.events[20 * k.val + 20]?.map V2.Event.time = some _ ∧ _ ∧ _
      refine ⟨?_, ?_, Or.inr ⟨le_rfl, k, rfl, ?_⟩⟩
      · rw [(trace_premises_sat.2.2.1 k).2.2.1]; rfl
      · change (4 : Int) * (2 * (k.val + 1) : Nat) <
          (4 : Int) * (2 * (k.val + 1) : Nat) + 1
        omega
      · exact (trace_premises_sat.2.2.1 k).2.2.1
    · change run.events[20 * k.val + 21]?.map V2.Event.time = some _ ∧ _ ∧ _
      refine ⟨?_, ?_, Or.inr ⟨le_rfl, k, rfl, ?_⟩⟩
      · rw [(trace_premises_sat.2.2.1 k).2.2.2]; rfl
      · change (4 : Int) * (2 * (k.val + 1) : Nat) <
          (4 : Int) * (2 * (k.val + 1) : Nat) + 1
        omega
      · exact (trace_premises_sat.2.2.1 k).2.2.2

#print axioms owner_premises_sat

-- Apply the owner with every premise discharged, then trigger its actual opening.
private theorem kernel_conclusion_premises_sat :
    KernelConclusion_W core (env Nat) run obs timing interface decodeProposal erase
      (fun X => X.rows.map wire) (fun nd Q => parentRead nd Q.parent) makeFG 2 pt.r ∧
    ∃ Afg U : FGBlock (Fin 1), core.erase Afg = erase (block 4) ∧
      FGBlock.Preceq Afg U ∧ Afg ≠ U ∧ (obs.height U).h = (obs.height Afg).h + 1 ∧
      AcceptsFinalBefore core (env Nat) run 7 U (kernelDeadlineW timing 2 (pt.r + 2)) ∧
      AcceptsFinalBefore core (env Nat) run 9 U (kernelDeadlineW timing 2 (pt.r + 2)) := by
  let p := owner_premises_sat
  have kernel := finality_kernel_W_of_holder core reads obs timing
    (by constructor <;> intros <;> simp) (env Nat) run interface history electorate
    decodeProposal erase (fun X => X.rows.map wire) (fun _ => []) chainRowsRead parentRead
    parentHeight validFor makeFG valid service cfg 2 2 point pt (Jst := 0)
    (storedCarrier := storedCarrier) (SourceService := sourceService)
    p.CL p.HL p.keep p.restore p.hc p.heightBridge p.height_eq p.finality_eq p.hne p.target
    p.foldTarget p.noMixed honestSlot p.hK p.runFacts p.hreset p.hGSTstart p.reset
    p.historyTransfer p.chain p.reflect p.parent p.hOrigin p.emission p.decoded p.receipt
    p.honest_slot p.proposal p.terminalProposal p.carrier p.exactService p.source_read
    p.source_eq p.head_read p.head_held p.slot_chain p.closed p.roots p.validRows p.parentEq
    p.matchValid p.hBatch p.hSOCOVTarget p.action wire p.wireDecode p.wireValid p.client
    p.release p.fields p.hQC p.recordHead p.clientLaws p.own p.hsel p.decode p.occurrence
    p.validFor_eq p.pathValid p.dutyTime p.rowDurable p.rowClock ready p.step p.durable p.inv
    finBlock p.hI3 p.readyBlock p.stored p.rootScope p.hStrat p.hEmittedSource p.hcapBefore
    p.delivery
  obtain ⟨Afg, hA, _, _, U, hpath, hne, hh, ha⟩ := kernel _
    (proposal_data_premises_sat 3).1
  exact ⟨kernel, Afg, U, hA, hpath, hne, hh, ha 7 (by decide), ha 9 (by decide)⟩

#print axioms kernel_conclusion_premises_sat

-- The old all-node target supplier fails only at honest nonholder 7, on an active source.
private theorem old_target_supplier_impossible :
    ¬ (∀ x ∈ run.honest, ∀ r C,
      actionSourceFG core (env Nat) run timing x r = some (some C) →
      point.reset.M + 1 ≤ (obs.height C).h → (env Nat).awake x (timing.action r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt reads (env Nat) run timing j x rSent a ∧
        RowComplete reads run history.signer valid x a ∧
        history.heightPair a = .vote (obs.height C).h (obs.height C).T_h.root false) := by
  intro old
  obtain ⟨j, rSent, a, _, _, complete, _⟩ := old 7 (by decide) 4 (block 4)
    (trace_premises_sat.2.2.2 4 0) (by decide +kernel) rfl
  obtain ⟨i, _, hi⟩ := complete.2
  change 9 = 7 at hi
  contradiction

#print axioms old_target_supplier_impossible

end Owner

end AvailableChain.FGCompose.Tests.PopulationKernel
end
