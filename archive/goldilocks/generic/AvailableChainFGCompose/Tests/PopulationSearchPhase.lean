module
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchRepair
public import AvailableChainFGCompose.Proofs.Finality.History -- shake: keep (window views)
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchGap

set_option linter.privateModule false

noncomputable section
namespace AvailableChain.FGCompose.Tests.PopulationSearchPhase
open AvailableChain.SimplexFG AvailableChain.KitFG

-- Private fixture support copied from the accepted P0d5c controls.
namespace Fixture

private def d5cTiming : FGTiming where
  delta := 1
  roundSlots := 2
  proposal s := 4 * (s : Time)
  vote s := 4 * (s : Time) + 1
  early s := 4 * (s : Time) + 2
  freeze s := 4 * (s : Time) + 3
  release s := 4 * (s : Time) + 5
  gate s := 4 * (s : Time) + 6
  action r := 8 * (r : Time) + 6

private theorem d5cTimingLaws : FGTimingLaws d5cTiming where
  delta_pos := by decide
  rounds := by decide
  proposal_eq s := by simp [d5cTiming]
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq r := by simp [d5cTiming]; ring

#print axioms d5cTimingLaws

private def c5r (h : Nat) (e : BlockId) : Row (Fin 1) := ⟨0, .vote h e false, none⟩

private def c5x1 : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 [c5r 1 genesisRoot]

private def c5erase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node p s r x rs => .node (c5erase p) s r (encFGBody x rs)

private theorem c5erase_inj : Function.Injective c5erase := by
  intro A
  induction A with
  | genesis => intro B h; cases B <;> simp_all [c5erase]
  | node p s r x rs ih =>
    intro B h
    cases B with
    | genesis => simp [c5erase] at h
    | node q t u y ts =>
      simp only [c5erase, Block.node.injEq] at h
      obtain ⟨hp, hs, hr, hb⟩ := h
      obtain ⟨hx, hrows⟩ := encFGBody_inj hb
      cases ih hp
      cases hs
      cases hr
      cases hx
      cases hrows
      rfl

#print axioms c5erase_inj

private theorem c5erase_mono {A B : FGBlock (Fin 1)} (h : FGBlock.Preceq A B) :
    Block.Preceq (c5erase A) (c5erase B) := by
  induction B with
  | genesis =>
    rw [(preceq_genesis).mp h]
    rfl
  | node P s r x rs ih =>
    change (decide (A = .node P s r x rs) || FGBlock.preceq A P) = true at h
    change (decide (c5erase A = c5erase (.node P s r x rs)) ||
      Block.preceq (c5erase A) (c5erase P)) = true
    rw [Bool.or_eq_true] at h ⊢
    rcases h with he | hp
    · exact Or.inl (decide_eq_true (congrArg c5erase (of_decide_eq_true he)))
    · exact Or.inr (ih hp)

#print axioms c5erase_mono

private def c5E : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩

private def c5cfg : FGConfig := ⟨4⟩

private abbrev c5H := KitFG.Window.certificateHeight c5E c5cfg 2

private abbrev c5F := KitFG.Window.certificateFinality c5E c5cfg 2

private theorem c5cert : FGCertificateLaws c5E c5H c5F :=
  KitFG.Window.windowCertificateLaws c5E c5cfg 2
    (by unfold Electorate.IsQuorum; decide +kernel) (by decide)

#print axioms c5cert

private theorem m9erase_reflect (A B : FGBlock (Fin 1))
    (h : Block.Preceq (c5erase A) (c5erase B)) : FGBlock.Preceq A B := by
  induction B with
  | genesis =>
    have he : c5erase A = c5erase .genesis := of_decide_eq_true h
    exact c5erase_inj he ▸ preceq_refl _
  | node P slot root app rows ih =>
    change (decide (c5erase A = c5erase (.node P slot root app rows)) ||
      Block.preceq (c5erase A) (c5erase P)) = true at h
    rw [Bool.or_eq_true] at h
    rcases h with he | hp
    · exact c5erase_inj (of_decide_eq_true he) ▸ preceq_refl _
    · exact preceq_node_of_preceq slot root app rows (ih hp)

#print axioms m9erase_reflect

private def m9slotsOK : FGBlock (Fin 1) → Bool
  | .genesis => true
  | .node P s _ _ _ => decide (P.slot ≤ s) && m9slotsOK P

private theorem m9anc_slot {A K : FGBlock (Fin 1)} (hK : m9slotsOK K = true)
    (h : FGBlock.Preceq A K) : A.slot ≤ K.slot := by
  induction K with
  | genesis => rw [(preceq_genesis).mp h]
  | node P s r x rs ih =>
    change (decide (P.slot ≤ s) && m9slotsOK P) = true at hK
    rw [Bool.and_eq_true] at hK
    change (decide (A = .node P s r x rs) || FGBlock.preceq A P) = true at h
    rw [Bool.or_eq_true] at h
    rcases h with he | hp
    · rw [of_decide_eq_true he]
    · exact (ih hK.2 hp).trans (of_decide_eq_true hK.1)

#print axioms m9anc_slot

private theorem m9transition_progress (σ : ChainState (Fin 1)) (B : FGBlock (Fin 1))
    (rs : List (Row (Fin 1))) (S : Finset (Fin 1)) (hS : c5E.IsQuorum S)
    (hcover : ∀ i ∈ S, i ∈ σ.progress ∨
      ∃ a ∈ rs, a.signer = i ∧ a.height_pair.matchesEntry σ.h σ.T_h.root = true)
    (hmature : σ.T_h.slot + c5cfg.timeoutDelay ≤ B.slot) :
    (transition c5E c5cfg σ B rs).h = σ.h + 1 := by
  have hfold (rows : List (Row (Fin 1))) (σ : ChainState (Fin 1)) (i : Fin 1)
      (hi : i ∈ σ.progress ∨
        ∃ a ∈ rows, a.signer = i ∧ a.height_pair.matchesEntry σ.h σ.T_h.root = true) :
      i ∈ (rows.foldl process_row σ).progress := by
    induction rows generalizing σ with
    | nil => simpa using hi
    | cons a rows ih =>
        apply ih
        rw [(process_row_fields σ a).2.2.1, (process_row_fields σ a).2.2.2.1]
        rcases hi with hi | ⟨b, hb, hbi, hm⟩
        · left
          rw [process_row_progress]
          split_ifs
          · exact Finset.mem_insert_of_mem hi
          · exact hi
        · rcases List.mem_cons.mp hb with rfl | hb
          · left
            rw [process_row_progress, ite_eq_left hm]
            exact Finset.mem_insert.mpr (Or.inl hbi.symm)
          · exact Or.inr ⟨b, hb, hbi, hm⟩
  have hq : c5E.IsQuorum (foldRows σ B rs).progress :=
    isQuorum_of_subset c5E hS (fun i hi => hfold rs { σ with s := B.slot } i (hcover i hi))
  have hp : progReady c5E c5cfg (afterFin c5E (foldRows σ B rs)) = true := by
    simp only [progReady, Bool.or_eq_true, Bool.and_eq_true]
    right
    constructor
    · simpa only [afterFin_T_h, afterFin_s, (foldRows_fields σ B rs).2.2.1,
        foldRows_s, decide_eq_true_eq] using hmature
    · change decide (c5E.q ≤ c5E.weightOf (afterFin c5E (foldRows σ B rs)).progress) = true
      rw [decide_eq_true_eq, afterFin_progress]
      exact hq
  change (process_height_events c5E c5cfg (foldRows σ B rs)).h = σ.h + 1
  rw [process_height_events_eq]
  have hh := (afterFin_h c5E (foldRows σ B rs)).trans (foldRows_fields σ B rs).2.1
  split_ifs with ht
  · exact congrArg (· + 1) hh
  · exact congrArg (· + 1) hh

#print axioms m9transition_progress

private theorem m9progress_of_cover (hb : HeightBridge c5E c5cfg c5H)
    (p : FGBlock (Fin 1)) (s : Slot) (r_s : BlockId) (x : Nat)
    (rs : List (Row (Fin 1))) (S : Finset (Fin 1)) (hS : c5E.IsQuorum S)
    (hcover : ∀ i ∈ S, i ∈ (c5H p).progress ∨
      ∃ a ∈ rs, a.signer = i ∧
        a.height_pair.matchesEntry (c5H p).h (c5H p).T_h.root = true)
    (hmature : (c5H p).T_h.slot + c5cfg.timeoutDelay ≤ s) :
    (c5H (.node p s r_s x rs)).h = (c5H p).h + 1 := by
  have heq : ∀ B, c5H B = heightOf (derive c5E c5cfg B) := hb
  simp only [heq, heightOf_def] at hcover hmature ⊢
  exact m9transition_progress (derive c5E c5cfg p) (.node p s r_s x rs) rs S hS hcover hmature

#print axioms m9progress_of_cover

private theorem m9foldAdvance : ProgressFoldAdvance c5E c5H 4 := by
  intro y U X hX hU hUX hc hm
  have hb := KitFG.Window.windowHeightBridge c5E c5cfg 2 (by decide)
  have laws := heightLaws_of_bridge c5E c5cfg _ hb
  have hlow := laws.h_mono hUX
  change (c5H U).h ≤ (c5H X.parent).h at hlow
  rw [hU.1] at hlow
  cases X with
  | genesis => exact (hX rfl).elim
  | node P s root x rs =>
    change y ≤ (c5H P).h at hlow
    by_cases hP : (c5H P).h = y
    · have hT : (c5H P).T_h = U :=
        (laws.entry_plateau hUX (hU.1.trans hP.symm)).symm.trans hU.2
      obtain ⟨S, hS, hcov⟩ := hc hP
      have hh := m9progress_of_cover hb P s root x rs S hS (by
          intro i hi
          rcases hcov i hi with hbit | ⟨a, ha, hs, timeout, hp⟩
          · exact Or.inl hbit
          · refine Or.inr ⟨a, ha, hs, ?_⟩
            rw [hp]
            change decide (y = (c5H P).h ∧ U.root = (c5H P).T_h.root) = true
            simp only [hP, hT, and_self, decide_true]) (by
          change (c5H P).T_h.slot + 4 ≤ s
          rw [hT]
          exact hm)
      change (c5H (.node P s root x rs)).h = (c5H P).h + 1 at hh
      rw [hh, hP]
    · have hPX := laws.h_mono (preceq_parent_node P s root x rs)
      change (c5H P).h ≤ (c5H (.node P s root x rs)).h at hPX
      simp only [Height] at *
      omega

#print axioms m9foldAdvance

private theorem gidxBefore_le_timeIdx {V : Type} {P : V2.ProtocolSpecD Unit}
    (rho : V2.D.Run V P) (a : Time) : V2.D.Run.idxBefore rho a ≤ timeIdx rho a := by
  change (rho.events.filter (fun e => decide (e.time < a))).length ≤
    (rho.events.filter (fun e => decide (e.time ≤ a))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left fun e _ he => decide_eq_true (of_decide_eq_true he).le

#print axioms gidxBefore_le_timeIdx

private theorem c5H_pos (B : FGBlock (Fin 1)) : 1 ≤ (c5H B).h := by
  have laws := heightLaws_of_bridge c5E c5cfg _
    (KitFG.Window.windowHeightBridge c5E c5cfg 2 (by decide))
  have h := laws.h_mono (genesis_preceq B)
  have h0 : (c5H .genesis).h = 1 := by decide
  change (c5H .genesis).h ≤ (c5H B).h at h
  rw [h0] at h
  exact h

#print axioms c5H_pos

end Fixture

open Fixture

/-! Generic ordinary-event-fold fixture. Both honest runtime nodes tick at every time
0..46. The FG seat belongs to 9; proposals at slots 2, 5 and 7 belong to 7. The low
seed has height 1; its first opening uses 9's original action-0 row. The actual
slot-5 carrier raises the proposal to height 2 at the original gate time 26. -/

private abbrev firstRow : Row (Fin 1) := ⟨0, .vote 1 genesisRoot true, none⟩
private abbrev low : FGBlock (Fin 1) := .node .genesis 2 ⟨101⟩ 0 [firstRow]
private abbrev middle : FGBlock (Fin 1) := .node low 5 ⟨105⟩ 0 [firstRow]
private abbrev late : FGBlock (Fin 1) := .node middle 7 ⟨107⟩ 0 []
private abbrev nextRow : Row (Fin 1) := ⟨0, .vote 2 middle.root true, none⟩
private abbrev chainAt (s : Nat) : FGBlock (Fin 1) :=
  if s ≤ 2 then low else if s ≤ 5 then middle else late
private abbrev sourceAt (t : Time) : FGBlock (Fin 1) :=
  if t < 14 then .genesis else if t < 30 then low else if t < 38 then middle else late
private abbrev protocol : V2.ProtocolSpecD Unit where
  State := Time
  Label := Time
  Duty := Time
  signLabel t := if t = 6 ∨ t = 30 then 6 else t
  seats _ := 1
  Payload := Row (Fin 1) ⊕ FGBlock (Fin 1)
  Durable := Time
  init := 0
  clock _ t := t
  actTime := id
  duties t := [t]
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; simp
  act _ t _ := if t = 6 then some (.inl firstRow)
    else if t = 30 then some (.inl nextRow)
    else if t = 8 then some (.inr low)
    else if t = 20 then some (.inr middle)
    else if t = 28 then some (.inr late) else none
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
private abbrev env : Generic.Env Nat := ⟨1, by decide, 0, by decide, fun _ _ => true⟩
private abbrev run : V2.D.Run Nat protocol where
  honest := {7, 9}
  horizon := 46
  events := (List.range 47).flatMap fun (t : Nat) => [.tick 7 (t : Time), .tick 9 (t : Time)]
  seatOf l _ := if l = 6 then 9 else if l = 8 ∨ l = 20 ∨ l = 28 then 7 else 0
  input _ _ := ()
private abbrev reads : FGSafetyReads protocol 1 (Row (Fin 1)) where
  proposalErase _ := none
  proposalRows _ := []
  encode a := ⟨.seat 6 0, .inl a⟩
  decode := some
  decodeObject o := match o.auth with
    | .seat l _ => if l = 6 then o.payload.getLeft? else none
    | .none => none
  fgLabel := 6
  fgSeats := Equiv.refl _
  record _ := RecordOnce.initial
  inputs t := (some (sourceAt t), ⟨0, genesisRoot, 0⟩)
  enabled _ := true
  finalizedOut _ := .genesis
private abbrev stored (top : Bool) : Finset (FGBlock (Fin 1)) :=
  if top then {.genesis, low, middle, late, c5x1} else {.genesis, low, middle, late}
private abbrev core (top : Bool) : FGCoreReads protocol 1 Unit Unit (Row (Fin 1)) where
  core _ := ⟨(), ⟨stored top, .genesis, .genesis, if top then 1 else 0, 2⟩, [],
    [firstRow, nextRow]⟩
  erase := c5erase
  source t := some (sourceAt t)
  headVote _ s := c5erase (chainAt s)
  finalityHead _ := some .genesis
  proposalFG _ _ := none
private abbrev obs (top : Bool) : FGObservationReads (core top) where
  height := c5H
  finality := c5F
  controls st := treeStoreControlsView c5H ((core top).core st).fg
  viable st X := treeStoreFrameView c5H ((core top).core st).fg X
private abbrev iface : V2.D.Interface protocol where
  confirmed _ := .genesis
  stable _ := c5erase late
  block p := match p with | .inr X => some (c5erase X) | .inl _ => none
  opening _ := True
  propLabel s := 4 * (s : Time)
  propDuty s := 4 * (s : Time)
  propDuty_label s := by
    change (if 4 * (s : Int) = 6 ∨ 4 * (s : Int) = 30 then 6 else 4 * (s : Int)) = _
    rw [ite_eq_right (by omega)]
  propLabel_single _ := rfl
  propLabel_injective := by
    intro a b h
    change 4 * (a : Int) = 4 * (b : Int) at h
    exact Int.ofNat_inj.mp (by omega)
private abbrev wire : FGHistoryWireReads reads where
  heightPair := Row.height_pair
  finalityPair := Row.finality_pair
  signer a := some a.signer
  decode_height _ _ h := by cases h; rfl
  decode_finality _ _ h := by cases h; rfl
  decode_signer _ _ h := by cases h; rfl
private abbrev decodeProposal (o : protocol.Object) : Option (Slot × FGBlock (Fin 1)) :=
  match o.payload with | .inr X => some (X.slot, X) | .inl _ => none
private abbrev parentFG (t : Time) (_ : Block) : Option (FGBlock (Fin 1)) :=
  if t = 8 then some .genesis else if t = 20 then some low else some middle
private abbrev fold (_ : Time) (_ : Slot) (P : FGBlock (Fin 1)) := Window.derive c5E c5cfg 2 P
private abbrev parentHeight (t : Time) (s : Slot) (P : FGBlock (Fin 1)) : Height × BlockId :=
  ((fold t s P).h, (fold t s P).T_h.root)
private abbrev validFor (t : Time) (s : Slot) (P : FGBlock (Fin 1)) (a : Row (Fin 1)) :=
  Window.r6w (fold t s P) a

private theorem geometry_premises_sat (top : Bool) :
    FGCertificateLaws c5E (obs top).height (obs top).finality ∧
    FGObservationLaws (core top) (obs top) ∧
    (∀ i x, FGStoreInvariant (obs top).height (obs top).finality
      ((core top).core (run.stateBefore env i x)).fg) ∧
    (c5H low).h = 1 ∧ (c5H middle).h = 2 ∧ (c5H late).h = 2 ∧
    (c5H low).T_h = .genesis ∧ (c5H middle).T_h = middle ∧ (c5H late).T_h = middle ∧
    PhaseInterval (core top) env run (obs top) 0 46 2
      (if top then some .genesis else none) false := by
  refine ⟨c5cert, ⟨fun _ => rfl, fun _ _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i x
    cases top <;> constructor <;> dsimp [obs, core] <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · refine ⟨by decide, le_rfl, by decide, ?_⟩
    intro i x _ _ _
    cases top <;> dsimp [obs, core] <;> decide +kernel

#print axioms geometry_premises_sat

private theorem execution_premises_sat :
    V2.D.ScheduleWellFormed env run ∧ FGHonestSeats reads run = {0} ∧
    c5E.weightOf (historyFaulty reads run) < c5E.q ∧
    HonestRowAt reads env run d5cTiming 13 9 0 firstRow ∧
    HonestRowAt reads env run d5cTiming 61 9 3 nextRow ∧
    protocol.objSelfVisible (reads.encode firstRow) = true ∧
    reads.decodeObject (reads.encode firstRow) = some firstRow ∧
    (∀ x ∈ run.honest, ∀ r ≤ 5,
      postClock env run x (d5cTiming.action r) = some (d5cTiming.action r)) ∧
    (∀ x ∈ run.honest, ∀ s ≤ 10,
      postClock env run x (d5cTiming.vote s) = some (d5cTiming.vote s)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
    · intro x t ht
      dsimp only [run] at ht
      obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp ht
      have hk' : (x = 7 ∧ t = (k : Time)) ∨ (x = 9 ∧ t = (k : Time)) := by
        simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
          V2.Event.tick.injEq] using hk
      rcases hk' with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact ⟨k, by simp⟩
    · intro x hx t ht _ hh _
      obtain ⟨k, rfl⟩ := ht
      have hk : k < 47 := by change (k : Int) * 1 ≤ 46 at hh; omega
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      dsimp only [run, env]
      apply List.mem_flatMap.mpr
      refine ⟨k, List.mem_range.mpr hk, ?_⟩
      rcases hx' with rfl | rfl <;> simp
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    decide
  · decide
  · unfold HonestRowAt
    decide +kernel
  · unfold HonestRowAt
    decide +kernel
  · intro x hx r hr
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl <;> interval_cases r <;> decide +kernel
  · intro x hx s hs
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl <;> interval_cases s <;> decide +kernel

#print axioms execution_premises_sat

private theorem proposal_premises_sat :
    (∀ s, Gen.V2.Duty.HonestSlot run iface s → s = 2 ∨ s = 5 ∨ s = 7) ∧
    (∀ s, s = 2 ∨ s = 5 ∨ s = 7 →
      HonestCarrier env run iface (kernelCarrier decodeProposal c5erase FGBlock.rows)
        s (c5erase (chainAt s)) (chainAt s).rows) := by
  constructor
  · intro s hs
    have hp := hs.2
    change (if 4 * (s : Int) = 6 then 9 else
      if 4 * (s : Int) = 8 ∨ 4 * (s : Int) = 20 ∨ 4 * (s : Int) = 28
      then 7 else 0) ∈ ({7, 9} : Finset Nat) at hp
    split_ifs at hp with h6 hslot
    · omega
    · rcases hslot with h | h | h
      · exact Or.inl (Int.ofNat.inj (show (s : Int) = 2 by omega))
      · exact Or.inr (Or.inl (Int.ofNat.inj (show (s : Int) = 5 by omega)))
      · exact Or.inr (Or.inr (Int.ofNat.inj (show (s : Int) = 7 by omega)))
    · simp at hp
  · intro s hs
    rcases hs with rfl | rfl | rfl
    · refine ⟨?_, ⟨.seat 8 0, .inr low⟩,
        ⟨16, by decide +kernel, by decide +kernel⟩, low, rfl, rfl, rfl⟩
      refine ⟨⟨by decide, by decide⟩, ⟨.seat 8 0, .inr low⟩,
        ⟨16, by decide +kernel, by decide +kernel⟩, rfl⟩
    · refine ⟨?_, ⟨.seat 20 0, .inr middle⟩,
        ⟨40, by decide +kernel, by decide +kernel⟩, middle, rfl, rfl, rfl⟩
      refine ⟨⟨by decide, by decide⟩, ⟨.seat 20 0, .inr middle⟩,
        ⟨40, by decide +kernel, by decide +kernel⟩, rfl⟩
    · refine ⟨?_, ⟨.seat 28 0, .inr late⟩,
        ⟨56, by decide +kernel, by decide +kernel⟩, late, rfl, rfl, rfl⟩
      refine ⟨⟨by decide, by decide⟩, ⟨.seat 28 0, .inr late⟩,
        ⟨56, by decide +kernel, by decide +kernel⟩, rfl⟩

#print axioms proposal_premises_sat

private theorem proposal_unique {s : Slot} {Q : Block}
    (hp : HonestProposal env run iface s Q) :
    (s = 2 ∨ s = 5 ∨ s = 7) ∧ Q = c5erase (chainAt s) := by
  have hs := proposal_premises_sat.1 s hp.1
  refine ⟨hs, ?_⟩
  obtain ⟨_, o, ⟨j, hj, ho⟩, hb⟩ := hp
  have hjlt : j < 94 := (List.getElem?_eq_some_iff.mp hj).1
  rcases hs with rfl | rfl | rfl
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 7 8) → k.val = 16 := by
      decide +kernel
    have hj' : j = 16 := hu ⟨j, hjlt⟩ hj
    subst j
    change o ∈ [⟨.seat 8 0, .inr low⟩] at ho
    have ho' := List.mem_singleton.mp ho
    subst o
    exact (Option.some.inj hb).symm
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 7 20) → k.val = 40 := by
      decide +kernel
    have hj' : j = 40 := hu ⟨j, hjlt⟩ hj
    subst j
    change o ∈ [⟨.seat 20 0, .inr middle⟩] at ho
    have ho' := List.mem_singleton.mp ho
    subst o
    exact (Option.some.inj hb).symm
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 7 28) → k.val = 56 := by
      decide +kernel
    have hj' : j = 56 := hu ⟨j, hjlt⟩ hj
    subst j
    change o ∈ [⟨.seat 28 0, .inr late⟩] at ho
    have ho' := List.mem_singleton.mp ho
    subst o
    exact (Option.some.inj hb).symm

#print axioms proposal_unique

private theorem row_identity {j r x : Nat} {a : Row (Fin 1)}
    (h : HonestRowAt reads env run d5cTiming j x r a) :
    (j = 13 ∧ x = 9 ∧ r = 0 ∧ a = firstRow) ∨
      (j = 61 ∧ x = 9 ∧ r = 3 ∧ a = nextRow) := by
  have ht := (execution_premises_sat.1.in_horizon _ (List.mem_of_getElem? h.2.1)).2
  have hr : r ≤ 5 := by change 8 * (r : Int) + 6 ≤ 46 at ht; omega
  have hx : x = 7 ∨ x = 9 := by simpa using h.1
  obtain ⟨_, hj, ha⟩ := h
  have hjlt : j < 94 := (List.getElem?_eq_some_iff.mp hj).1
  rcases hx with rfl | rfl <;> interval_cases r
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 7 6) → k.val = 12 := by
      decide +kernel
    have hj' : j = 12 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [] at ha
    cases ha
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 7 14) → k.val = 28 := by
      decide +kernel
    have hj' : j = 28 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [] at ha
    cases ha
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 7 22) → k.val = 44 := by
      decide +kernel
    have hj' : j = 44 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [] at ha
    cases ha
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 7 30) → k.val = 60 := by
      decide +kernel
    have hj' : j = 60 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [] at ha
    cases ha
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 7 38) → k.val = 76 := by
      decide +kernel
    have hj' : j = 76 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [] at ha
    cases ha
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 7 46) → k.val = 92 := by
      decide +kernel
    have hj' : j = 92 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [] at ha
    cases ha
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 9 6) → k.val = 13 := by
      decide +kernel
    have hj' : j = 13 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [reads.encode firstRow] at ha
    have he := congrArg V2.Signed.payload (List.mem_singleton.mp ha)
    exact Or.inl ⟨rfl, rfl, rfl, Sum.inl.inj he⟩
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 9 14) → k.val = 29 := by
      decide +kernel
    have hj' : j = 29 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [] at ha
    cases ha
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 9 22) → k.val = 45 := by
      decide +kernel
    have hj' : j = 45 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [] at ha
    cases ha
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 9 30) → k.val = 61 := by
      decide +kernel
    have hj' : j = 61 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [reads.encode nextRow] at ha
    have he := congrArg V2.Signed.payload (List.mem_singleton.mp ha)
    exact Or.inr ⟨rfl, rfl, rfl, Sum.inl.inj he⟩
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 9 38) → k.val = 77 := by
      decide +kernel
    have hj' : j = 77 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [] at ha
    cases ha
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 9 46) → k.val = 93 := by
      decide +kernel
    have hj' : j = 93 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [] at ha
    cases ha

#print axioms row_identity

private theorem source_premises_sat (top : Bool) :
    (∀ r x K, actionSourceFG (core top) env run d5cTiming x r = some (some K) →
      K = sourceAt (d5cTiming.action r)) ∧
    (∀ r x K, x ∈ run.honest →
      actionSourceFG (core top) env run d5cTiming x r = some (some K) → K.slot ≤ r * 2) ∧
    (∀ r x K A, x ∈ run.honest →
      actionSourceFG (core top) env run d5cTiming x r = some (some K) → FGBlock.Preceq A K →
      A.slot ≤ K.slot) ∧
    (∀ r x y K L, x ∈ run.honest → y ∈ run.honest →
      actionSourceFG (core top) env run d5cTiming x r = some (some K) →
      actionSourceFG (core top) env run d5cTiming y r = some (some L) →
      (c5H K).T_h.root = (c5H L).T_h.root → (c5H K).T_h = (c5H L).T_h) ∧
    (∀ x ∈ run.honest,
      actionSourceFG (core top) env run d5cTiming x 1 = some (some low)) ∧
    (∀ x ∈ run.honest,
      actionSourceFG (core top) env run d5cTiming x 3 = some (some middle)) := by
  have src (r x K) (h : actionSourceFG (core top) env run d5cTiming x r = some (some K)) :
      K = sourceAt (d5cTiming.action r) := by
    delta actionSourceFG postClock at h
    rw [Option.map_map] at h
    obtain ⟨nd, _, he⟩ := Option.map_eq_some_iff.mp h
    exact (Option.some.inj he).symm
  refine ⟨src, ?_, ?_, ?_, ?_, ?_⟩
  · intro r x K _ hk
    rw [src r x K hk]
    by_cases hr : r < 4
    · interval_cases r <;> decide
    · have h14 : ¬ d5cTiming.action r < 14 := by change ¬ 8 * (r : Int) + 6 < 14; omega
      have h30 : ¬ d5cTiming.action r < 30 := by change ¬ 8 * (r : Int) + 6 < 30; omega
      have h38 : ¬ d5cTiming.action r < 38 := by change ¬ 8 * (r : Int) + 6 < 38; omega
      simp only [sourceAt, h14, h30, h38, ite_false]
      change 7 ≤ r * 2
      omega
  · intro r x K A _ hk ha
    have hs : m9slotsOK K = true := by
      rw [src r x K hk]
      unfold sourceAt
      split_ifs <;> decide +kernel
    exact m9anc_slot hs ha
  · intro r x y K L _ _ hk hl _
    rw [src r x K hk, src r y L hl]
  · intro x hx
    rw [actionSourceFG, execution_premises_sat.2.2.2.2.2.2.2.1 x hx 1 (by decide)]
    rfl
  · intro x hx
    rw [actionSourceFG, execution_premises_sat.2.2.2.2.2.2.2.1 x hx 3 (by decide)]
    rfl

#print axioms source_premises_sat

private theorem opening_premises_sat (top : Bool) (r : Nat) (hr : 1 ≤ r) (hr5 : r ≤ 5) :
    OpeningEntry (core top) env run c5H d5cTiming r
      (c5H (sourceAt (d5cTiming.action r))).h ∧
    ∀ Q, FGBlock.Preceq Q (sourceAt (d5cTiming.action r)) →
      OpeningCoveredFG (core top) reads env run c5H d5cTiming wire.heightPair
        (FGHonestSeats reads run) r (c5erase Q) := by
  constructor
  · refine ⟨(c5H (sourceAt (d5cTiming.action r))).T_h.root, ?_⟩
    intro x K _ hk
    rw [(source_premises_sat top).1 r x K hk]
    exact ⟨rfl, rfl⟩
  · intro Q hQ i _
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hpost := execution_premises_sat.2.2.2.2.2.2.2.1 9 (by decide) r hr5
    have hsource : actionSourceFG (core top) env run d5cTiming 9 r =
        some (some (sourceAt (d5cTiming.action r))) := by
      rw [actionSourceFG, hpost]
      rfl
    interval_cases r
    · refine ⟨sourceAt (d5cTiming.action 1), d5cTiming.action 1, 13, 0, firstRow,
        hpost, hsource, ?_, c5erase_mono hQ, by decide,
        execution_premises_sat.2.2.2.1, ?_⟩
      · cases top <;> decide +kernel
      · decide +kernel
    · refine ⟨sourceAt (d5cTiming.action 2), d5cTiming.action 2, 13, 0, firstRow,
        hpost, hsource, ?_, c5erase_mono hQ, by decide,
        execution_premises_sat.2.2.2.1, ?_⟩
      · cases top <;> decide +kernel
      · decide +kernel
    · refine ⟨sourceAt (d5cTiming.action 3), d5cTiming.action 3, 61, 3, nextRow,
        hpost, hsource, ?_, c5erase_mono hQ, by decide,
        execution_premises_sat.2.2.2.2.1, ?_⟩
      · cases top <;> decide +kernel
      · decide +kernel
    · refine ⟨sourceAt (d5cTiming.action 4), d5cTiming.action 4, 61, 3, nextRow,
        hpost, hsource, ?_, c5erase_mono hQ, by decide,
        execution_premises_sat.2.2.2.2.1, ?_⟩
      · cases top <;> decide +kernel
      · decide +kernel
    · refine ⟨sourceAt (d5cTiming.action 5), d5cTiming.action 5, 61, 3, nextRow,
        hpost, hsource, ?_, c5erase_mono hQ, by decide,
        execution_premises_sat.2.2.2.2.1, ?_⟩
      · cases top <;> decide +kernel
      · decide +kernel

#print axioms opening_premises_sat

private theorem transport_premises_sat (top : Bool) :
    (∀ t, env.t_GST ≤ t → t + 20 ≤ run.horizon →
      ∃ s, t < d5cTiming.proposal s ∧ d5cTiming.proposal s ≤ t + 20 ∧
        Gen.V2.Duty.HonestSlot run iface s) ∧
    PromotionSlotProposal (core top) env run d5cTiming iface ∧
    PromotionProposalRead (core top) reads env run (obs top) iface decodeProposal c5erase
      FGBlock.rows parentFG parentHeight validFor fold ∧
    PromotionSourceParent (core top) env run (obs top) d5cTiming iface 0 ∧
    PromotionRowSigner reads env run d5cTiming wire ∧
    TRowsReceipt (core top) reads env run d5cTiming (fun _ => [firstRow, nextRow]) 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht hh
    change 0 ≤ t at ht
    change t + 20 ≤ 46 at hh
    by_cases h20 : t < 20
    · refine ⟨5, h20, ?_, (proposal_premises_sat.2 5 (Or.inr (Or.inl rfl))).1.1⟩
      change 20 ≤ t + 20
      linarith
    · refine ⟨7, ?_, ?_, (proposal_premises_sat.2 7 (Or.inr (Or.inr rfl))).1.1⟩
      · change t < 28
        linarith
      · change 28 ≤ t + 20
        linarith
  · intro s hs _ _
    have hslots := proposal_premises_sat.1 s hs
    refine ⟨chainAt s, (proposal_premises_sat.2 s hslots).1, ?_⟩
    rcases hslots with rfl | rfl | rfl <;> rfl
  · intro s X hp _
    obtain ⟨hs, he⟩ := proposal_unique hp
    have hX : X = chainAt s := c5erase_inj he
    subst X
    rcases hs with rfl | rfl | rfl
    · exact ⟨⟨(chainAt 2).rows, proposal_premises_sat.2 2 (Or.inl rfl), rfl⟩,
        8, by decide +kernel, rfl, rfl, rfl, rfl, fun _ => rfl⟩
    · exact ⟨⟨(chainAt 5).rows, proposal_premises_sat.2 5 (Or.inr (Or.inl rfl)), rfl⟩,
        20, by decide +kernel, rfl, rfl, rfl, rfl, fun _ => rfl⟩
    · exact ⟨⟨(chainAt 7).rows, proposal_premises_sat.2 7 (Or.inr (Or.inr rfl)), rfl⟩,
        28, by decide +kernel, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  · intro u m J c r s X x K _ _ _ _ hafter hp _ hk
    obtain ⟨hs, he⟩ := proposal_unique hp
    have hX : X = chainAt s := c5erase_inj he
    subst X
    rw [(source_premises_sat top).1 r x K hk]
    change @LE.le Nat _ (r * 2 + 2) s at hafter
    rcases hs with rfl | rfl | rfl
    · have hr : @Eq Nat r 0 := by omega
      subst r
      decide +kernel
    · have hr : @LE.le Nat _ r 1 := by omega
      interval_cases r <;> decide +kernel
    · have hr : @LE.le Nat _ r 2 := by omega
      interval_cases r <;> decide +kernel
  · refine ⟨fun _ _ _ a _ => ⟨a, rfl⟩, ?_⟩
    intro i j r a _
    exact congrArg some (Subsingleton.elim a.signer i)
  · intro j x r a hrow _ y _
    rcases row_identity hrow with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)

#print axioms transport_premises_sat

private theorem progress_premises_sat (top : Bool) :
    PromotionRowOrder (core top) env run (obs top) iface ∧
    (∀ r h U X, BatchPrem (core top) reads (obs top) d5cTiming env run iface wire c5E
      decodeProposal c5erase FGBlock.rows (fun _ => [firstRow, nextRow]) parentFG parentHeight
      validFor 1 .progress r h U X → (c5H X.parent).h = h →
      ProgressCoveredByChild c5E c5H X U h) ∧
    ProgressFoldAdvance c5E c5H 4 := by
  refine ⟨?_, ?_, m9foldAdvance⟩
  · intro s X h U hp _ hh hUP i W hw hn
    change (c5H X.parent).h = h at hh
    obtain ⟨hs, he⟩ := proposal_unique hp
    have hX : X = chainAt s := c5erase_inj he
    subst X
    rcases hs with rfl | rfl | rfl
    · have hW : W = .genesis := preceq_genesis.mp hw
      subst W
      obtain ⟨a, ha, _⟩ := hn
      cases ha
    · rw [show chainAt 5 = middle by decide +kernel] at hw hUP
      change FGBlock.Preceq W low at hw
      change FGBlock.Preceq U low at hUP
      have hW : W = low ∨ W = .genesis := by
        simpa only [low, FGBlock.Preceq, FGBlock.preceq,
          Bool.or_eq_true, decide_eq_true_eq] using hw
      rcases hW with rfl | rfl
      · have hU : U = low ∨ U = .genesis := by
          simpa only [low, FGBlock.Preceq, FGBlock.preceq,
            Bool.or_eq_true, decide_eq_true_eq] using hUP
        rcases hU with rfl | rfl
        · obtain ⟨a, ha, _, timeout, hn⟩ := hn
          have ha' : a = firstRow := List.mem_singleton.mp ha
          subst a
          cases hn
        · exact genesis_preceq _
      · obtain ⟨a, ha, _⟩ := hn
        cases ha
    · rw [show chainAt 7 = late by decide +kernel] at hw hh
      change FGBlock.Preceq W middle at hw
      have hh2 : h = 2 := hh.symm.trans (by decide +kernel)
      subst h
      have hW : W = middle ∨ W = low ∨ W = .genesis := by
        simpa only [middle, low, FGBlock.Preceq, FGBlock.preceq,
          Bool.or_eq_true, decide_eq_true_eq] using hw
      rcases hW with rfl | rfl | rfl
      · obtain ⟨a, ha, _, timeout, hn⟩ := hn
        have ha' : a = firstRow := List.mem_singleton.mp ha
        subst a
        cases hn
      · obtain ⟨a, ha, _, timeout, hn⟩ := hn
        have ha' : a = firstRow := List.mem_singleton.mp ha
        subst a
        cases hn
      · obtain ⟨a, ha, _⟩ := hn
        cases ha
  · intro r h U X hb hh
    obtain ⟨_, hcar, _⟩ := hb.carrier
    obtain ⟨hs, he⟩ := proposal_unique hcar.1
    have hX : X = chainAt X.slot := c5erase_inj he
    have hu : U = (c5H X.parent).T_h :=
      hb.entry.2.symm.trans (c5cert.height.entry_plateau hb.path (hb.entry.1.trans hh.symm))
    have hafter : @LE.le Nat _ (r * 2 + 2) X.slot := hb.after
    rcases hs with hs | hs | hs
    · have hx : X = low := by
        simpa only [hs, show chainAt 2 = low by decide +kernel] using hX
      subst X
      have hu0 : U = .genesis := hu.trans (by decide +kernel)
      have hh1 : h = 1 := hh.symm.trans (by decide +kernel)
      subst U h
      refine ⟨{0}, by decide, ?_⟩
      intro i hi
      have hi' := Finset.mem_singleton.mp hi
      subst i
      exact Or.inr ⟨firstRow, by decide, rfl, true, rfl⟩
    · have hx : X = middle := by
        simpa only [hs, show chainAt 5 = middle by decide +kernel] using hX
      subst X
      have hu0 : U = .genesis := hu.trans (by decide +kernel)
      have hh1 : h = 1 := hh.symm.trans (by decide +kernel)
      subst U h
      refine ⟨{0}, by decide, ?_⟩
      intro i hi
      have hi' := Finset.mem_singleton.mp hi
      subst i
      exact Or.inr ⟨firstRow, by decide, rfl, true, rfl⟩
    · have hx : X = late := by
        simpa only [hs, show chainAt 7 = late by decide +kernel] using hX
      subst X
      have hh2 : h = 2 := hh.symm.trans (by decide +kernel)
      subst h
      obtain ⟨Q, _, hq, hall⟩ := hb.valid
      rcases Finset.eq_empty_or_nonempty Q with hQ | ⟨i, hi⟩
      · rw [hQ] at hq
        exact absurd hq (by decide)
      obtain ⟨j, rSent, a, t, hr, hrow, _, hn, _⟩ := hall i hi
      rcases row_identity hrow with ⟨_, _, _, ha⟩ | ⟨_, _, hSent, ha⟩
      · subst a
        obtain ⟨timeout, hn⟩ := hn
        cases hn
      · subst rSent
        change r * 2 + 2 ≤ 7 at hafter
        omega

#print axioms progress_premises_sat

private theorem proposal_service_premises_sat (top : Bool) :
    ∀ q Q, HonestProposal env run iface q Q →
      FrontierProposalService (core top) env run d5cTiming q Q := by
  intro q Q hp _ x hx _
  obtain ⟨hq, he⟩ := proposal_unique hp
  have h10 : @LE.le Nat _ q 10 := by rcases hq with rfl | rfl | rfl <;> decide
  rw [headAtLabel, execution_premises_sat.2.2.2.2.2.2.2.2 x hx q h10]
  exact congrArg some he.symm

#print axioms proposal_service_premises_sat

private theorem local_service_premises_sat (top : Bool) (q : Nat) (hq : q = 5 ∨ q = 7)
    (v : Time) (hhor : v ≤ 46) :
    FrontierLocalServiceFG (core top) reads env run (obs top) d5cTiming iface wire.heightPair
      q (c5erase (chainAt q)) (chainAt q) 2 v := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x s H _ hqs _ hhead
    change @LE.le Nat _ (q + 1) s at hqs
    have hs : @LE.le Nat _ 6 s := by rcases hq with rfl | rfl <;> omega
    have h1 : ¬ s ≤ 2 := Nat.not_le.mpr (by omega)
    have h5 : ¬ s ≤ 5 := Nat.not_le.mpr (by omega)
    have hl : chainAt s = late := by simp only [chainAt, h1, h5, ite_false]
    delta headAtLabel at hhead
    obtain ⟨nd, _, he⟩ := Option.map_eq_some_iff.mp hhead
    change c5erase (chainAt s) = H at he
    rw [← he, hl]
    rcases hq with rfl | rfl <;> decide +kernel
  · intro s B hqs _ hp
    change @LE.le Nat _ (q + 2) s at hqs
    obtain ⟨hs, he⟩ := proposal_unique hp
    subst B
    rcases hq with rfl | rfl <;> rcases hs with rfl | rfl | rfl
    all_goals first | omega | decide +kernel
  · intro i x _ _ _ _
    change Block.Preceq (c5erase (chainAt q)) (c5erase late)
    rcases hq with rfl | rfl <;> decide +kernel
  · intro s B _ _ hp
    exact proposal_service_premises_sat top s B hp
  · intro r hqr ht
    change @LE.le Nat _ q (r * 2) at hqr
    have ht46 := ht.trans hhor
    change 8 * (r : Int) + 6 ≤ 46 at ht46
    have hr5 : @LE.le Nat _ r 5 := by omega
    have hr3 : @LE.le Nat _ 3 r := by rcases hq with rfl | rfl <;> omega
    have hopen := opening_premises_sat top r (by omega) hr5
    have hh : (c5H (sourceAt (d5cTiming.action r))).h = 2 := by
      interval_cases r <;> decide +kernel
    have he : (c5H (sourceAt (d5cTiming.action r))).T_h = (c5H (chainAt q)).T_h := by
      rcases hq with rfl | rfl <;> interval_cases r <;> decide +kernel
    have hpath : FGBlock.Preceq (chainAt q) (sourceAt (d5cTiming.action r)) := by
      rcases hq with rfl | rfl <;> interval_cases r
      all_goals first | omega | decide +kernel
    refine ⟨hopen.2 _ hpath, ?_, ?_, ?_⟩
    · simpa only [hh] using hopen.1
    · intro x K _ hk
      rw [(source_premises_sat top).1 r x K hk]
      exact he
    · intro hfirst
      rcases hq with rfl | rfl
      · have hr : @LE.le Nat _ r 3 := hfirst 3 (by decide)
        have hr' : @Eq Nat r 3 := by omega
        subst r
        decide
      · have hr : @LE.le Nat _ r 4 := hfirst 4 (by decide)
        have hr' : @Eq Nat r 4 := by omega
        subst r
        decide

#print axioms local_service_premises_sat

private theorem repair_premises_sat (top : Bool) :
    AttemptProposalFloor (core top) env run (obs top) d5cTiming iface 0 ∧
    (∀ u v m J c q Q, (0 : Time) ≤ u → PhaseInterval (core top) env run (obs top) u v m J c →
      FrontierSeedQualification d5cTiming 1 env.t_GST u q → d5cTiming.gate q ≤ v →
      HonestProposal env run iface q Q → ∃ i x Qfg, run.idxBefore u ≤ i ∧ i ≤ timeIdx run v ∧
        x ∈ run.honest ∧ Qfg ∈ ((core top).core (run.stateBefore env i x)).fg.TF ∧
        c5erase Qfg = Q) ∧
    FrontierRepairAllowance (core top) env run (obs top) d5cTiming iface 0 1 20 14 0 ∧
    (∀ i x A K, K ∈ ((core top).core (run.stateBefore env i x)).fg.TF →
      FGBlock.Preceq A K → A.slot ≤ K.slot) ∧
    (∀ q Q K, HonestProposal env run iface q Q → c5erase K = Q → K.slot = q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u v m J c q Q Qfg _ hp _ _ _ _
    have hcut : run.idxBefore u ≤ timeIdx run v :=
      (gidxBefore_le_timeIdx run u).trans (frontierSearch_timeIdx_mono run hp.1)
    have hf := hp.2.2.2 _ 7 le_rfl hcut (by decide)
    have hm : m = 2 := hf.1.symm
    have hc : ((obs top).controls 0).contest = c := hf.2.1
    have hc0 : ((obs top).controls 0).contest = false := by cases top <;> decide +kernel
    have hc' : c = false := hc.symm.trans hc0
    rw [hm, hc']
    exact c5H_pos _
  · intro u v m J c q Q _ hp _ _ hQ
    obtain ⟨hq, he⟩ := proposal_unique hQ
    refine ⟨run.idxBefore u, 7, chainAt q, le_rfl, ?_, by decide, ?_, he.symm⟩
    · exact (gidxBefore_le_timeIdx run u).trans (frontierSearch_timeIdx_mono run hp.1)
    · change chainAt q ∈ stored top
      rcases hq with rfl | rfl | rfl <;> cases top <;> decide +kernel
  · refine ⟨by decide, 0 + 1,
      .one 0 (by decide) (fun _ _ => Nat.zero_le _) (by decide) (by decide), ?_⟩
    intro _ v m J c _ _
    refine ⟨fun s Q _ _ hp => proposal_service_premises_sat top s Q hp, fun _ => ?_⟩
    have hp := (proposal_premises_sat.2 2 (Or.inl rfl)).1
    exact ⟨2, c5erase low, by decide, by decide, hp,
      proposal_service_premises_sat top 2 _ hp⟩
  · intro i x A K hk ha
    have hslots : m9slotsOK K = true := by
      change K ∈ stored top at hk
      cases top
      · simp only [stored, Bool.false_eq_true, ite_false, Finset.mem_insert,
          Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> decide +kernel
      · simp only [stored, ite_true, Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    exact m9anc_slot hslots ha
  · intro q Q K hp he
    obtain ⟨hq, hQ⟩ := proposal_unique hp
    have hK : K = chainAt q := c5erase_inj (he.trans hQ)
    rw [hK]
    rcases hq with rfl | rfl | rfl <;> decide +kernel

#print axioms repair_premises_sat

private theorem branch_premises_sat (top : Bool) :
    (∀ u v m J contested q Q Qfg, (0 : Time) ≤ u → HonestProposal env run iface q Q → (core
      top).erase Qfg = Q → ((obs top).height Qfg).h = m → FrontierProposalService (core top)
      env run d5cTiming q Q → FrontierSeedQualification d5cTiming 1 env.t_GST u q → u ≤
      d5cTiming.proposal q → PhaseInterval (core top) env run (obs top) u (d5cTiming.gate q) m
      J contested → d5cTiming.gate q ≤ v → v ≤ run.horizon → (∀ i x, timeIdx run u ≤ i → i ≤
      timeIdx run v → x ∈ run.honest → ((core top).core (run.stateBefore env i x)).fg.h_max ≤
      m) → FrontierLocalServiceFG (core top) reads env run (obs top) d5cTiming iface
      wire.heightPair q Q Qfg m v) ∧
    (∀ u m J contested q Q Qfg r, (0 : Time) ≤ u → HonestProposal env run iface q Q → (core
      top).erase Qfg = Q → FrontierProposalService (core top) env run d5cTiming q Q →
      FrontierSeedQualification d5cTiming 1 env.t_GST u q → u ≤ d5cTiming.proposal q → q ≤ r *
      d5cTiming.roundSlots → (∀ r', q ≤ r' * d5cTiming.roundSlots → r ≤ r') → PhaseInterval
      (core top) env run (obs top) u (d5cTiming.action r) m J contested → OpeningCoveredFG
      (core top) reads env run (obs top).height d5cTiming wire.heightPair (FGHonestSeats reads
      run) r Q ∧ (((obs top).height Qfg).h = m - 1 → OpeningEntry (core top) env run (obs
      top).height d5cTiming r (m - 1) ∨ ∃ x K, x ∈ run.honest ∧ actionSourceFG (core top) env
      run d5cTiming x r = some (some K) ∧ ((obs top).height K).h = m)) := by
  constructor
  · intro u v m J c q Q Qfg _ hp he hh _ _ _ hphase _ hhor _
    have hcut : run.idxBefore u ≤ timeIdx run (d5cTiming.gate q) :=
      (gidxBefore_le_timeIdx run u).trans (frontierSearch_timeIdx_mono run hphase.1)
    have hm : m = 2 := (hphase.2.2.2 _ 7 le_rfl hcut (by decide)).1.symm
    obtain ⟨hq, hQ⟩ := proposal_unique hp
    have hB : Qfg = chainAt q := c5erase_inj (he.trans hQ)
    rw [hB, hm] at hh
    rw [hB, hQ, hm]
    apply local_service_premises_sat top q _ v hhor
    rcases hq with rfl | rfl | rfl
    · change (c5H (chainAt 2)).h = 2 at hh
      exact absurd hh (by decide +kernel)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro u m J c q Q Qfg r _ hp he _ _ _ hqr hfirst hphase
    have hcut : run.idxBefore u ≤ timeIdx run (d5cTiming.action r) :=
      (gidxBefore_le_timeIdx run u).trans (frontierSearch_timeIdx_mono run hphase.1)
    have hm : m = 2 := (hphase.2.2.2 _ 7 le_rfl hcut (by decide)).1.symm
    obtain ⟨hq, hQ⟩ := proposal_unique hp
    have hB : Qfg = chainAt q := c5erase_inj (he.trans hQ)
    rw [hB, hQ, hm]
    change @LE.le Nat _ q (r * 2) at hqr
    rcases hq with rfl | rfl | rfl
    · have hr : @LE.le Nat _ r 1 := hfirst 1 (by decide)
      have hr' : @Eq Nat r 1 := by omega
      subst r
      have ho := opening_premises_sat top 1 (by decide) (by decide)
      refine ⟨ho.2 (chainAt 2) (by decide +kernel), ?_⟩
      intro _
      left
      simpa only [show (c5H (sourceAt (d5cTiming.action 1))).h = 1 by decide +kernel]
        using ho.1
    · have hr : @LE.le Nat _ r 3 := hfirst 3 (by decide)
      have hr' : @Eq Nat r 3 := by omega
      subst r
      have ho := opening_premises_sat top 3 (by decide) (by decide)
      refine ⟨ho.2 (chainAt 5) (by decide +kernel), ?_⟩
      intro hh
      change (c5H (chainAt 5)).h = 1 at hh
      exact absurd hh (by decide +kernel)
    · have hr : @LE.le Nat _ r 4 := hfirst 4 (by decide)
      have hr' : @Eq Nat r 4 := by omega
      subst r
      have ho := opening_premises_sat top 4 (by decide) (by decide)
      refine ⟨ho.2 (chainAt 7) (by decide +kernel), ?_⟩
      intro hh
      change (c5H (chainAt 7)).h = 1 at hh
      exact absurd hh (by decide +kernel)

#print axioms branch_premises_sat

private theorem mixed_gap_low :
    (∀ q Q, HonestProposal env run iface q Q → d5cTiming.gate q ≤ 14 →
      q = 2 ∧ Q = c5erase low) ∧
    ∃ t, (0 : Time) ≤ t ∧ t ≤ 46 ∧
      StrongServedFG (core false) reads env run (obs false) d5cTiming iface wire.heightPair
        0 1 2 t ∧ 26 ≤ t ∧ V2.D.proposerOf run iface 2 = 7 ∧
      HonestRowAt reads env run d5cTiming 13 9 0 firstRow := by
  constructor
  · intro q Q hp hg
    obtain ⟨hq, he⟩ := proposal_unique hp
    rcases hq with rfl | rfl | rfl
    · exact ⟨rfl, he⟩
    · exact absurd hg (by decide)
    · exact absurd hg (by decide)
  · obtain ⟨cert, obsLaws, inv, _, _, _, _, _, _, phase⟩ := geometry_premises_sat false
    obtain ⟨gap, slotProposal, read, sourceParent, signer, rowsReceipt⟩ :=
      transport_premises_sat false
    obtain ⟨order, coverage, hfold⟩ := progress_premises_sat false
    obtain ⟨floor, copy, allowance, heldSlot, proposalSlot⟩ := repair_premises_sat false
    obtain ⟨service, common⟩ := branch_premises_sat false
    obtain ⟨_, sourceSlot, ancestorSlot, entryAgreement, _, _⟩ := source_premises_sat false
    obtain ⟨t, ht0, ht46, hs⟩ := frontierSearch_gap_phase_holder
      (R := core false) (S := reads) (O := obs false) (T := d5cTiming)
      (E := env) (rho := run) (I := iface) (D := wire) (Ef := c5E)
      (decodeProposal := decodeProposal) (bodyErase := c5erase) (bodyRows := FGBlock.rows)
      (blockWireRows := fun _ => [firstRow, nextRow]) (parentFG := parentFG)
      (parentHeight := parentHeight) (validFor := validFor) (fold := fold) (Jst := 0)
      (leaseSlots := 1) (obs := obsLaws) (cert := cert) (inv := inv)
      (hT := d5cTimingLaws) (hk := le_rfl) (schedule := execution_premises_sat.1)
      (faultWeight := execution_premises_sat.2.2.1) (G := 20) (ΔF := 1)
      (ρbar := 14) (u := 0) (Dl := 46) (deltaF := le_rfl) (hdelta := rfl)
      (gap := gap) (hJst := le_rfl) (hG := by decide) (slotProposal := slotProposal)
      (read := read) (order := order) (signer := signer) (sourceParent := sourceParent)
      (deltaT := 4) (hδ := rfl) (hbound := ⟨by decide⟩) (rowsReceipt := rowsReceipt)
      (progressCoverage := coverage) (hfold := hfold)
      (honestQuorum := ⟨{0}, fun _ _ => by change (9 : Nat) ∈ {7, 9}; decide, by decide⟩)
      (entryAgreement := entryAgreement) (sourceSlot := sourceSlot) (ancestorSlot := ancestorSlot)
      (eraseInj := c5erase_inj) (eraseReflect := m9erase_reflect) (floor := floor)
      (gateCopy := copy) (service := service) (common := common) (heldSlot := heldSlot)
      (proposalSlot := proposalSlot) (m := 2) (hready := le_rfl) (hp := phase)
      (allowance := allowance) (hbudget := by decide)
    refine ⟨t, ht0, ht46, hs, ?_, by decide, execution_premises_sat.2.2.2.1⟩
    obtain ⟨u, J, c, q, Q, Qfg, _, hp, he, hh, _, _, _, _, hg, _⟩ := hs
    obtain ⟨hq, hQ⟩ := proposal_unique hp
    have hB : Qfg = chainAt q := c5erase_inj (he.trans hQ)
    rw [hB] at hh
    change (c5H (chainAt q)).h = 2 at hh
    rcases hq with rfl | rfl | rfl
    · exact absurd hh (by decide +kernel)
    · exact hg
    · exact (by decide : (26 : Time) ≤ d5cTiming.gate 7).trans hg

#print axioms mixed_gap_low

private theorem nonholder_no_encoded (j : Nat) (t : Time)
    (hj : run.events[j]? = some (.tick 7 t)) (a : Row (Fin 1)) :
    reads.encode a ∉ V2.D.Run.emitsAt env run j := by
  have table : ∀ k : Fin 94, run.events[k.val]?.map V2.Event.node = some 7 →
      (V2.D.Run.emitsAt env run k.val).all (fun o => decide (o.auth ≠ .seat 6 0)) = true := by
    decide +kernel
  have hlen : j < 94 := (List.getElem?_eq_some_iff.mp hj).1
  have hnode : run.events[j]?.map V2.Event.node = some 7 := by rw [hj]; rfl
  have hsafe := table ⟨j, hlen⟩ hnode
  intro ha
  have hn := of_decide_eq_true ((List.all_eq_true.mp hsafe) (reads.encode a) ha)
  exact hn rfl

#print axioms nonholder_no_encoded

/-- Both old suppliers fail solely on row 7; all their other fields are supplied by
opening_premises_sat, local_service_premises_sat, and branch_premises_sat on this run. -/
private theorem old_common_service_rejected :
    (¬ OpeningCovered (core false) reads env run c5H d5cTiming wire.heightPair
      1 (c5erase low)) ∧
    ¬ FrontierLocalService (core false) reads env run (obs false) d5cTiming iface
      wire.heightPair 5 (c5erase middle) middle 2 46 := by
  constructor
  · intro hc
    obtain ⟨K, nd, j, rSent, a, _, _, _, _, _, hrow, _⟩ := hc 7 (by decide)
    exact nonholder_no_encoded j _ hrow.2.1 a hrow.2.2
  · intro hs
    obtain ⟨hc, _⟩ := hs.2.2.2.2 3 (by decide) (by decide)
    obtain ⟨K, nd, j, rSent, a, _, _, _, _, _, hrow, _⟩ := hc 7 (by decide)
    exact nonholder_no_encoded j _ hrow.2.1 a hrow.2.2

#print axioms old_common_service_rejected

/-! High branch on the same mixed event schedule. Node 7 records its proposal at time 8,
so its source at the low seed's first opening is raised (height 2). Holder 9 still
reads low and supplies its original event-13/round-0 row. Both later sources agree. -/
namespace High

private abbrev firstRow : Row (Fin 1) := ⟨0, .vote 1 genesisRoot true, none⟩
private abbrev low : FGBlock (Fin 1) := .node .genesis 2 ⟨101⟩ 0 [firstRow]
private abbrev raised : FGBlock (Fin 1) :=
  .node low 2 ⟨102⟩ 0 [c5r 1 genesisRoot]
private abbrev middle : FGBlock (Fin 1) := .node raised 5 ⟨105⟩ 0 [firstRow]
private abbrev late : FGBlock (Fin 1) := .node middle 7 ⟨107⟩ 0 []
private abbrev nextRow : Row (Fin 1) := ⟨0, .vote 2 raised.root true, none⟩
private abbrev chainAt (s : Nat) : FGBlock (Fin 1) :=
  if s ≤ 2 then low else if s ≤ 5 then middle else late
private abbrev sourceAt (t : Time) : FGBlock (Fin 1) :=
  if t < 14 then .genesis else if t < 30 then low else if t < 38 then middle else late
private abbrev protocol : V2.ProtocolSpecD Unit where
  State := Time × Bool
  Label := Time
  Duty := Time
  signLabel t := if t = 6 ∨ t = 30 then 6 else t
  seats _ := 1
  Payload := Row (Fin 1) ⊕ FGBlock (Fin 1)
  Durable := Time × Bool
  init := (0, false)
  clock st t := (t, st.2)
  actTime := id
  duties t := [t]
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; simp
  act _ t _ := if t = 6 then some (.inl firstRow)
    else if t = 30 then some (.inl nextRow)
    else if t = 8 then some (.inr low)
    else if t = 20 then some (.inr middle)
    else if t = 28 then some (.inr late) else none
  gossip _ _ := []
  process st _ := st
  selfVisible _ := true
  recordOwn st o := (st.1, st.2 || o.payload.isRight)
  durable := id
  restore st _ := st
  wellFormed _ := true
  depsPresent _ _ := true
  processed _ _ := false
  excludes _ _ := false
  handles _ _ _ := False
  carries _ _ := False
private abbrev env : Generic.Env Nat := ⟨1, by decide, 0, by decide, fun _ _ => true⟩
private abbrev run : V2.D.Run Nat protocol where
  honest := {7, 9}
  horizon := 46
  events := (List.range 47).flatMap fun (t : Nat) => [.tick 7 (t : Time), .tick 9 (t : Time)]
  seatOf l _ := if l = 6 then 9 else if l = 8 ∨ l = 20 ∨ l = 28 then 7 else 0
  input _ _ := ()
private abbrev reads : FGSafetyReads protocol 1 (Row (Fin 1)) where
  proposalErase _ := none
  proposalRows _ := []
  encode a := ⟨.seat 6 0, .inl a⟩
  decode := some
  decodeObject o := match o.auth with
    | .seat l _ => if l = 6 then o.payload.getLeft? else none
    | .none => none
  fgLabel := 6
  fgSeats := Equiv.refl _
  record _ := RecordOnce.initial
  inputs st := (some (sourceAt st.1), ⟨0, genesisRoot, 0⟩)
  enabled _ := true
  finalizedOut _ := .genesis
private abbrev stored (top : Bool) : Finset (FGBlock (Fin 1)) :=
  if top then {.genesis, low, raised, middle, late, c5x1} else {.genesis, low, raised, middle, late}
private abbrev core (top : Bool) : FGCoreReads protocol 1 Unit Unit (Row (Fin 1)) where
  core _ := ⟨(), ⟨stored top, .genesis, .genesis, 1, 2⟩, [],
    [firstRow, nextRow]⟩
  erase := c5erase
  source st :=
    some (if st.2 ∧ 14 ≤ st.1 ∧ st.1 < 30 then raised else sourceAt st.1)
  headVote _ s := c5erase (chainAt s)
  finalityHead _ := some .genesis
  proposalFG _ _ := none
private abbrev obs (top : Bool) : FGObservationReads (core top) where
  height := c5H
  finality := c5F
  controls st := treeStoreControlsView c5H ((core top).core st).fg
  viable st X := treeStoreFrameView c5H ((core top).core st).fg X
private abbrev iface : V2.D.Interface protocol where
  confirmed _ := .genesis
  stable _ := c5erase late
  block p := match p with | .inr X => some (c5erase X) | .inl _ => none
  opening _ := True
  propLabel s := 4 * (s : Time)
  propDuty s := 4 * (s : Time)
  propDuty_label s := by
    change (if 4 * (s : Int) = 6 ∨ 4 * (s : Int) = 30 then 6 else 4 * (s : Int)) = _
    rw [ite_eq_right (by omega)]
  propLabel_single _ := rfl
  propLabel_injective := by
    intro a b h
    change 4 * (a : Int) = 4 * (b : Int) at h
    exact Int.ofNat_inj.mp (by omega)
private abbrev wire : FGHistoryWireReads reads where
  heightPair := Row.height_pair
  finalityPair := Row.finality_pair
  signer a := some a.signer
  decode_height _ _ h := by cases h; rfl
  decode_finality _ _ h := by cases h; rfl
  decode_signer _ _ h := by cases h; rfl
private abbrev decodeProposal (o : protocol.Object) : Option (Slot × FGBlock (Fin 1)) :=
  match o.payload with | .inr X => some (X.slot, X) | .inl _ => none
private abbrev parentFG (st : Time × Bool) (_ : Block) : Option (FGBlock (Fin 1)) :=
  if st.1 = 8 then some .genesis
  else if st.1 = 20 then some raised else some middle
private abbrev fold (_ : Time × Bool) (_ : Slot) (P : FGBlock (Fin 1)) :=
  Window.derive c5E c5cfg 2 P
private abbrev parentHeight (t : Time × Bool) (s : Slot) (P : FGBlock (Fin 1)) : Height × BlockId :=
  ((fold t s P).h, (fold t s P).T_h.root)
private abbrev validFor (t : Time × Bool) (s : Slot) (P : FGBlock (Fin 1)) (a : Row (Fin 1)) :=
  Window.r6w (fold t s P) a

private theorem geometry_premises_sat (top : Bool) :
    FGCertificateLaws c5E (obs top).height (obs top).finality ∧
    FGObservationLaws (core top) (obs top) ∧
    (∀ i x, FGStoreInvariant (obs top).height (obs top).finality
      ((core top).core (run.stateBefore env i x)).fg) ∧
    (c5H low).h = 1 ∧ (c5H middle).h = 2 ∧ (c5H late).h = 2 ∧
    (c5H low).T_h = .genesis ∧ (c5H middle).T_h = raised ∧ (c5H late).T_h = raised ∧
    PhaseInterval (core top) env run (obs top) 0 46 2
      (some .genesis) false := by
  refine ⟨c5cert, ⟨fun _ => rfl, fun _ _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i x
    cases top <;> constructor <;> dsimp [obs, core] <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · refine ⟨by decide, le_rfl, by decide, ?_⟩
    intro i x _ _ _
    cases top <;> dsimp [obs, core] <;> decide +kernel

#print axioms geometry_premises_sat

private theorem execution_premises_sat :
    V2.D.ScheduleWellFormed env run ∧ FGHonestSeats reads run = {0} ∧
    c5E.weightOf (historyFaulty reads run) < c5E.q ∧
    HonestRowAt reads env run d5cTiming 13 9 0 firstRow ∧
    HonestRowAt reads env run d5cTiming 61 9 3 nextRow ∧
    protocol.objSelfVisible (reads.encode firstRow) = true ∧
    reads.decodeObject (reads.encode firstRow) = some firstRow ∧
    (∀ x ∈ run.honest, ∀ r ≤ 5,
      postClock env run x (d5cTiming.action r) =
        some (d5cTiming.action r, decide (x = 7 ∧ 0 < r))) ∧
    (∀ x ∈ run.honest, ∀ s ≤ 10,
      postClock env run x (d5cTiming.vote s) =
        some (d5cTiming.vote s, decide (x = 7 ∧ 2 ≤ s))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
    · intro x t ht
      dsimp only [run] at ht
      obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp ht
      have hk' : (x = 7 ∧ t = (k : Time)) ∨ (x = 9 ∧ t = (k : Time)) := by
        simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
          V2.Event.tick.injEq] using hk
      rcases hk' with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact ⟨k, by simp⟩
    · intro x hx t ht _ hh _
      obtain ⟨k, rfl⟩ := ht
      have hk : k < 47 := by change (k : Int) * 1 ≤ 46 at hh; omega
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      dsimp only [run, env]
      apply List.mem_flatMap.mpr
      refine ⟨k, List.mem_range.mpr hk, ?_⟩
      rcases hx' with rfl | rfl <;> simp
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    decide
  · decide
  · unfold HonestRowAt
    decide +kernel
  · unfold HonestRowAt
    decide +kernel
  · intro x hx r hr
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl <;> interval_cases r <;> decide +kernel
  · intro x hx s hs
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl <;> interval_cases s <;> decide +kernel

#print axioms execution_premises_sat

private theorem proposal_premises_sat :
    (∀ s, Gen.V2.Duty.HonestSlot run iface s → s = 2 ∨ s = 5 ∨ s = 7) ∧
    (∀ s, s = 2 ∨ s = 5 ∨ s = 7 →
      HonestCarrier env run iface (kernelCarrier decodeProposal c5erase FGBlock.rows)
        s (c5erase (chainAt s)) (chainAt s).rows) := by
  constructor
  · intro s hs
    have hp := hs.2
    change (if 4 * (s : Int) = 6 then 9 else
      if 4 * (s : Int) = 8 ∨ 4 * (s : Int) = 20 ∨ 4 * (s : Int) = 28
      then 7 else 0) ∈ ({7, 9} : Finset Nat) at hp
    split_ifs at hp with h6 hslot
    · omega
    · rcases hslot with h | h | h
      · exact Or.inl (Int.ofNat.inj (show (s : Int) = 2 by omega))
      · exact Or.inr (Or.inl (Int.ofNat.inj (show (s : Int) = 5 by omega)))
      · exact Or.inr (Or.inr (Int.ofNat.inj (show (s : Int) = 7 by omega)))
    · simp at hp
  · intro s hs
    rcases hs with rfl | rfl | rfl
    · refine ⟨?_, ⟨.seat 8 0, .inr low⟩,
        ⟨16, by decide +kernel, by decide +kernel⟩, low, rfl, rfl, rfl⟩
      refine ⟨⟨by decide, by decide⟩, ⟨.seat 8 0, .inr low⟩,
        ⟨16, by decide +kernel, by decide +kernel⟩, rfl⟩
    · refine ⟨?_, ⟨.seat 20 0, .inr middle⟩,
        ⟨40, by decide +kernel, by decide +kernel⟩, middle, rfl, rfl, rfl⟩
      refine ⟨⟨by decide, by decide⟩, ⟨.seat 20 0, .inr middle⟩,
        ⟨40, by decide +kernel, by decide +kernel⟩, rfl⟩
    · refine ⟨?_, ⟨.seat 28 0, .inr late⟩,
        ⟨56, by decide +kernel, by decide +kernel⟩, late, rfl, rfl, rfl⟩
      refine ⟨⟨by decide, by decide⟩, ⟨.seat 28 0, .inr late⟩,
        ⟨56, by decide +kernel, by decide +kernel⟩, rfl⟩

#print axioms proposal_premises_sat

private theorem proposal_unique {s : Slot} {Q : Block}
    (hp : HonestProposal env run iface s Q) :
    (s = 2 ∨ s = 5 ∨ s = 7) ∧ Q = c5erase (chainAt s) := by
  have hs := proposal_premises_sat.1 s hp.1
  refine ⟨hs, ?_⟩
  obtain ⟨_, o, ⟨j, hj, ho⟩, hb⟩ := hp
  have hjlt : j < 94 := (List.getElem?_eq_some_iff.mp hj).1
  rcases hs with rfl | rfl | rfl
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 7 8) → k.val = 16 := by
      decide +kernel
    have hj' : j = 16 := hu ⟨j, hjlt⟩ hj
    subst j
    change o ∈ [⟨.seat 8 0, .inr low⟩] at ho
    have ho' := List.mem_singleton.mp ho
    subst o
    exact (Option.some.inj hb).symm
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 7 20) → k.val = 40 := by
      decide +kernel
    have hj' : j = 40 := hu ⟨j, hjlt⟩ hj
    subst j
    change o ∈ [⟨.seat 20 0, .inr middle⟩] at ho
    have ho' := List.mem_singleton.mp ho
    subst o
    exact (Option.some.inj hb).symm
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 7 28) → k.val = 56 := by
      decide +kernel
    have hj' : j = 56 := hu ⟨j, hjlt⟩ hj
    subst j
    change o ∈ [⟨.seat 28 0, .inr late⟩] at ho
    have ho' := List.mem_singleton.mp ho
    subst o
    exact (Option.some.inj hb).symm

#print axioms proposal_unique

private theorem row_identity {j r x : Nat} {a : Row (Fin 1)}
    (h : HonestRowAt reads env run d5cTiming j x r a) :
    (j = 13 ∧ x = 9 ∧ r = 0 ∧ a = firstRow) ∨
      (j = 61 ∧ x = 9 ∧ r = 3 ∧ a = nextRow) := by
  have ht := (execution_premises_sat.1.in_horizon _ (List.mem_of_getElem? h.2.1)).2
  have hr : r ≤ 5 := by change 8 * (r : Int) + 6 ≤ 46 at ht; omega
  have hx : x = 7 ∨ x = 9 := by simpa using h.1
  obtain ⟨_, hj, ha⟩ := h
  have hjlt : j < 94 := (List.getElem?_eq_some_iff.mp hj).1
  rcases hx with rfl | rfl <;> interval_cases r
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 7 6) → k.val = 12 := by
      decide +kernel
    have hj' : j = 12 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [] at ha
    cases ha
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 7 14) → k.val = 28 := by
      decide +kernel
    have hj' : j = 28 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [] at ha
    cases ha
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 7 22) → k.val = 44 := by
      decide +kernel
    have hj' : j = 44 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [] at ha
    cases ha
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 7 30) → k.val = 60 := by
      decide +kernel
    have hj' : j = 60 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [] at ha
    cases ha
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 7 38) → k.val = 76 := by
      decide +kernel
    have hj' : j = 76 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [] at ha
    cases ha
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 7 46) → k.val = 92 := by
      decide +kernel
    have hj' : j = 92 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [] at ha
    cases ha
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 9 6) → k.val = 13 := by
      decide +kernel
    have hj' : j = 13 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [reads.encode firstRow] at ha
    have he := congrArg V2.Signed.payload (List.mem_singleton.mp ha)
    exact Or.inl ⟨rfl, rfl, rfl, Sum.inl.inj he⟩
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 9 14) → k.val = 29 := by
      decide +kernel
    have hj' : j = 29 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [] at ha
    cases ha
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 9 22) → k.val = 45 := by
      decide +kernel
    have hj' : j = 45 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [] at ha
    cases ha
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 9 30) → k.val = 61 := by
      decide +kernel
    have hj' : j = 61 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [reads.encode nextRow] at ha
    have he := congrArg V2.Signed.payload (List.mem_singleton.mp ha)
    exact Or.inr ⟨rfl, rfl, rfl, Sum.inl.inj he⟩
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 9 38) → k.val = 77 := by
      decide +kernel
    have hj' : j = 77 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [] at ha
    cases ha
  · have hu : ∀ k : Fin 94, run.events[k.val]? = some (.tick 9 46) → k.val = 93 := by
      decide +kernel
    have hj' : j = 93 := hu ⟨j, hjlt⟩ hj
    subst j
    change reads.encode a ∈ [] at ha
    cases ha

#print axioms row_identity

private theorem source_premises_sat (top : Bool) :
    (∀ r x K, actionSourceFG (core top) env run d5cTiming x r = some (some K) →
      (K = raised ∧ 1 ≤ r ∧ r ≤ 2) ∨ K = sourceAt (d5cTiming.action r)) ∧
    (∀ r x K, x ∈ run.honest →
      actionSourceFG (core top) env run d5cTiming x r = some (some K) → K.slot ≤ r * 2) ∧
    (∀ r x K A, x ∈ run.honest →
      actionSourceFG (core top) env run d5cTiming x r = some (some K) → FGBlock.Preceq A K →
      A.slot ≤ K.slot) ∧
    (∀ r x y K L, x ∈ run.honest → y ∈ run.honest →
      actionSourceFG (core top) env run d5cTiming x r = some (some K) →
      actionSourceFG (core top) env run d5cTiming y r = some (some L) →
      (c5H K).T_h.root = (c5H L).T_h.root → (c5H K).T_h = (c5H L).T_h) ∧
    actionSourceFG (core top) env run d5cTiming 7 1 = some (some raised) ∧
    (∀ x ∈ run.honest,
      actionSourceFG (core top) env run d5cTiming x 3 = some (some middle)) := by
  have src (r x K) (h : actionSourceFG (core top) env run d5cTiming x r = some (some K)) :
      (K = raised ∧ 1 ≤ r ∧ r ≤ 2) ∨ K = sourceAt (d5cTiming.action r) := by
    delta actionSourceFG postClock at h
    rw [Option.map_map] at h
    obtain ⟨nd, _, he⟩ := Option.map_eq_some_iff.mp h
    change some (if nd.2 ∧ 14 ≤ d5cTiming.action r ∧ d5cTiming.action r < 30
      then raised else sourceAt (d5cTiming.action r)) = some K at he
    split_ifs at he with hr
    · refine Or.inl ⟨(Option.some.inj he).symm, ?_, ?_⟩
      all_goals
        have hr0 := hr.2.1
        have hr1 := hr.2.2
        change 14 ≤ 8 * (r : Int) + 6 at hr0
        change 8 * (r : Int) + 6 < 30 at hr1
        omega
    · exact Or.inr (Option.some.inj he).symm
  refine ⟨src, ?_, ?_, ?_, by cases top <;> decide +kernel, ?_⟩
  · intro r x K _ hk
    rcases src r x K hk with ⟨rfl, hr, _⟩ | rfl
    · change 2 ≤ r * 2
      omega
    · by_cases hr : r < 4
      · interval_cases r <;> decide
      · have h14 : ¬ d5cTiming.action r < 14 := by change ¬ 8 * (r : Int) + 6 < 14; omega
        have h30 : ¬ d5cTiming.action r < 30 := by change ¬ 8 * (r : Int) + 6 < 30; omega
        have h38 : ¬ d5cTiming.action r < 38 := by change ¬ 8 * (r : Int) + 6 < 38; omega
        simp only [sourceAt, h14, h30, h38, ite_false]
        change 7 ≤ r * 2
        omega
  · intro r x K A _ hk ha
    have hs : m9slotsOK K = true := by
      rcases src r x K hk with ⟨rfl, _, _⟩ | rfl
      · decide +kernel
      · unfold sourceAt
        split_ifs <;> decide +kernel
    exact m9anc_slot hs ha
  · intro r x y K L _ _ hk hl he
    rcases src r x K hk with ⟨rfl, _, _⟩ | rfl <;>
      rcases src r y L hl with ⟨rfl, _, _⟩ | rfl
    · rfl
    · unfold sourceAt at he ⊢
      split_ifs at he ⊢ <;> first | rfl | exact absurd he (by decide +kernel)
    · unfold sourceAt at he ⊢
      split_ifs at he ⊢ <;> first | rfl | exact absurd he (by decide +kernel)
    · rfl
  · intro x hx
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl <;> cases top <;> decide +kernel

#print axioms source_premises_sat

private theorem opening_premises_sat (top : Bool) (r : Nat) (hr : 1 ≤ r) (hr5 : r ≤ 5) :
    (3 ≤ r → OpeningEntry (core top) env run c5H d5cTiming r
      (c5H (sourceAt (d5cTiming.action r))).h) ∧
    ∀ Q, FGBlock.Preceq Q (sourceAt (d5cTiming.action r)) →
      OpeningCoveredFG (core top) reads env run c5H d5cTiming wire.heightPair
        (FGHonestSeats reads run) r (c5erase Q) := by
  constructor
  · intro hr3
    refine ⟨(c5H (sourceAt (d5cTiming.action r))).T_h.root, ?_⟩
    intro x K _ hk
    rcases (source_premises_sat top).1 r x K hk with ⟨_, _, hr2⟩ | rfl
    · omega
    · exact ⟨rfl, rfl⟩
  · intro Q hQ i _
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hpost := execution_premises_sat.2.2.2.2.2.2.2.1 9 (by decide) r hr5
    have hsource : actionSourceFG (core top) env run d5cTiming 9 r =
        some (some (sourceAt (d5cTiming.action r))) := by
      rw [actionSourceFG, hpost]
      rfl
    interval_cases r
    · refine ⟨sourceAt (d5cTiming.action 1), (d5cTiming.action 1, false), 13, 0, firstRow,
        hpost, hsource, ?_, c5erase_mono hQ, by decide,
        execution_premises_sat.2.2.2.1, ?_⟩
      · cases top <;> decide +kernel
      · decide +kernel
    · refine ⟨sourceAt (d5cTiming.action 2), (d5cTiming.action 2, false), 13, 0, firstRow,
        hpost, hsource, ?_, c5erase_mono hQ, by decide,
        execution_premises_sat.2.2.2.1, ?_⟩
      · cases top <;> decide +kernel
      · decide +kernel
    · refine ⟨sourceAt (d5cTiming.action 3), (d5cTiming.action 3, false), 61, 3, nextRow,
        hpost, hsource, ?_, c5erase_mono hQ, by decide,
        execution_premises_sat.2.2.2.2.1, ?_⟩
      · cases top <;> decide +kernel
      · decide +kernel
    · refine ⟨sourceAt (d5cTiming.action 4), (d5cTiming.action 4, false), 61, 3, nextRow,
        hpost, hsource, ?_, c5erase_mono hQ, by decide,
        execution_premises_sat.2.2.2.2.1, ?_⟩
      · cases top <;> decide +kernel
      · decide +kernel
    · refine ⟨sourceAt (d5cTiming.action 5), (d5cTiming.action 5, false), 61, 3, nextRow,
        hpost, hsource, ?_, c5erase_mono hQ, by decide,
        execution_premises_sat.2.2.2.2.1, ?_⟩
      · cases top <;> decide +kernel
      · decide +kernel

#print axioms opening_premises_sat

private theorem transport_premises_sat (top : Bool) :
    (∀ t, env.t_GST ≤ t → t + 20 ≤ run.horizon →
      ∃ s, t < d5cTiming.proposal s ∧ d5cTiming.proposal s ≤ t + 20 ∧
        Gen.V2.Duty.HonestSlot run iface s) ∧
    PromotionSlotProposal (core top) env run d5cTiming iface ∧
    PromotionProposalRead (core top) reads env run (obs top) iface decodeProposal c5erase
      FGBlock.rows parentFG parentHeight validFor fold ∧
    PromotionSourceParent (core top) env run (obs top) d5cTiming iface 0 ∧
    PromotionRowSigner reads env run d5cTiming wire ∧
    TRowsReceipt (core top) reads env run d5cTiming (fun _ => [firstRow, nextRow]) 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht hh
    change 0 ≤ t at ht
    change t + 20 ≤ 46 at hh
    by_cases h20 : t < 20
    · refine ⟨5, h20, ?_, (proposal_premises_sat.2 5 (Or.inr (Or.inl rfl))).1.1⟩
      change 20 ≤ t + 20
      linarith
    · refine ⟨7, ?_, ?_, (proposal_premises_sat.2 7 (Or.inr (Or.inr rfl))).1.1⟩
      · change t < 28
        linarith
      · change 28 ≤ t + 20
        linarith
  · intro s hs _ _
    have hslots := proposal_premises_sat.1 s hs
    refine ⟨chainAt s, (proposal_premises_sat.2 s hslots).1, ?_⟩
    rcases hslots with rfl | rfl | rfl <;> rfl
  · intro s X hp _
    obtain ⟨hs, he⟩ := proposal_unique hp
    have hX : X = chainAt s := c5erase_inj he
    subst X
    rcases hs with rfl | rfl | rfl
    · exact ⟨⟨(chainAt 2).rows, proposal_premises_sat.2 2 (Or.inl rfl), rfl⟩,
        (8, false), by decide +kernel, rfl, rfl, rfl, rfl, fun _ => rfl⟩
    · exact ⟨⟨(chainAt 5).rows, proposal_premises_sat.2 5 (Or.inr (Or.inl rfl)), rfl⟩,
        (20, true), by decide +kernel, rfl, rfl, rfl, rfl, fun _ => rfl⟩
    · exact ⟨⟨(chainAt 7).rows, proposal_premises_sat.2 7 (Or.inr (Or.inr rfl)), rfl⟩,
        (28, true), by decide +kernel, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  · intro u m J c r s X x K _ _ _ _ hafter hp _ hk
    obtain ⟨hs, he⟩ := proposal_unique hp
    have hX : X = chainAt s := c5erase_inj he
    subst X
    change @LE.le Nat _ (r * 2 + 2) s at hafter
    rcases (source_premises_sat top).1 r x K hk with ⟨rfl, hr1, _⟩ | rfl
    · rcases hs with rfl | rfl | rfl
      · omega
      · decide +kernel
      · decide +kernel
    · rcases hs with rfl | rfl | rfl
      · have hr : @Eq Nat r 0 := by omega
        subst r
        decide +kernel
      · have hr : @LE.le Nat _ r 1 := by omega
        interval_cases r <;> decide +kernel
      · have hr : @LE.le Nat _ r 2 := by omega
        interval_cases r <;> decide +kernel
  · refine ⟨fun _ _ _ a _ => ⟨a, rfl⟩, ?_⟩
    intro i j r a _
    exact congrArg some (Subsingleton.elim a.signer i)
  · intro j x r a hrow _ y _
    rcases row_identity hrow with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)

#print axioms transport_premises_sat

private theorem progress_premises_sat (top : Bool) :
    PromotionRowOrder (core top) env run (obs top) iface ∧
    (∀ r h U X, BatchPrem (core top) reads (obs top) d5cTiming env run iface wire c5E
      decodeProposal c5erase FGBlock.rows (fun _ => [firstRow, nextRow]) parentFG parentHeight
      validFor 1 .progress r h U X → (c5H X.parent).h = h →
      ProgressCoveredByChild c5E c5H X U h) ∧
    ProgressFoldAdvance c5E c5H 4 := by
  refine ⟨?_, ?_, m9foldAdvance⟩
  · intro s X h U hp _ hh hUP i W hw hn
    change (c5H X.parent).h = h at hh
    obtain ⟨hs, he⟩ := proposal_unique hp
    have hX : X = chainAt s := c5erase_inj he
    subst X
    rcases hs with rfl | rfl | rfl
    · have hW : W = .genesis := preceq_genesis.mp hw
      subst W
      obtain ⟨a, ha, _⟩ := hn
      cases ha
    · change FGBlock.Preceq W raised at hw
      have hh2 : h = 2 := hh.symm.trans (by decide +kernel)
      subst h
      have hW : W = raised ∨ W = low ∨ W = .genesis := by
        simpa only [raised, low, FGBlock.Preceq, FGBlock.preceq,
          Bool.or_eq_true, decide_eq_true_eq] using hw
      rcases hW with rfl | rfl | rfl
      · obtain ⟨a, ha, _, timeout, hn⟩ := hn
        have ha' : a = c5r 1 genesisRoot := List.mem_singleton.mp ha
        subst a
        cases hn
      · obtain ⟨a, ha, _, timeout, hn⟩ := hn
        have ha' : a = firstRow := List.mem_singleton.mp ha
        subst a
        cases hn
      · obtain ⟨a, ha, _⟩ := hn
        cases ha
    · change FGBlock.Preceq W middle at hw
      have hh2 : h = 2 := hh.symm.trans (by decide +kernel)
      subst h
      have hW : W = middle ∨ W = raised ∨ W = low ∨ W = .genesis := by
        simpa only [middle, raised, low, FGBlock.Preceq, FGBlock.preceq,
          Bool.or_eq_true, decide_eq_true_eq] using hw
      rcases hW with rfl | rfl | rfl | rfl
      · obtain ⟨a, ha, _, timeout, hn⟩ := hn
        have ha' : a = firstRow := List.mem_singleton.mp ha
        subst a
        cases hn
      · obtain ⟨a, ha, _, timeout, hn⟩ := hn
        have ha' : a = c5r 1 genesisRoot := List.mem_singleton.mp ha
        subst a
        cases hn
      · obtain ⟨a, ha, _, timeout, hn⟩ := hn
        have ha' : a = firstRow := List.mem_singleton.mp ha
        subst a
        cases hn
      · obtain ⟨a, ha, _⟩ := hn
        cases ha
  · intro r h U X hb hh
    obtain ⟨_, hcar, _⟩ := hb.carrier
    obtain ⟨hs, he⟩ := proposal_unique hcar.1
    have hX : X = chainAt X.slot := c5erase_inj he
    have hu : U = (c5H X.parent).T_h :=
      hb.entry.2.symm.trans (c5cert.height.entry_plateau hb.path (hb.entry.1.trans hh.symm))
    have hafter : @LE.le Nat _ (r * 2 + 2) X.slot := hb.after
    rcases hs with hs | hs | hs
    · have hx : X = low := by
        simpa only [hs, show chainAt 2 = low by decide +kernel] using hX
      subst X
      have hu0 : U = .genesis := hu.trans (by decide +kernel)
      have hh1 : h = 1 := hh.symm.trans (by decide +kernel)
      subst U h
      refine ⟨{0}, by decide, ?_⟩
      intro i hi
      have hi' := Finset.mem_singleton.mp hi
      subst i
      exact Or.inr ⟨firstRow, by decide, rfl, true, rfl⟩
    · have hx : X = middle := by
        simpa only [hs, show chainAt 5 = middle by decide +kernel] using hX
      subst X
      have hh2 : h = 2 := hh.symm.trans (by decide +kernel)
      subst h
      obtain ⟨Q, _, hq, hall⟩ := hb.valid
      rcases Finset.eq_empty_or_nonempty Q with hQ | ⟨i, hi⟩
      · rw [hQ] at hq
        exact absurd hq (by decide)
      obtain ⟨j, rSent, a, t, hr, hrow, _, hn, _⟩ := hall i hi
      rcases row_identity hrow with ⟨_, _, _, ha⟩ | ⟨_, _, hSent, ha⟩
      · subst a
        obtain ⟨timeout, hn⟩ := hn
        cases hn
      · subst rSent
        change r * 2 + 2 ≤ 5 at hafter
        omega
    · have hx : X = late := by
        simpa only [hs, show chainAt 7 = late by decide +kernel] using hX
      subst X
      have hh2 : h = 2 := hh.symm.trans (by decide +kernel)
      subst h
      obtain ⟨Q, _, hq, hall⟩ := hb.valid
      rcases Finset.eq_empty_or_nonempty Q with hQ | ⟨i, hi⟩
      · rw [hQ] at hq
        exact absurd hq (by decide)
      obtain ⟨j, rSent, a, t, hr, hrow, _, hn, _⟩ := hall i hi
      rcases row_identity hrow with ⟨_, _, _, ha⟩ | ⟨_, _, hSent, ha⟩
      · subst a
        obtain ⟨timeout, hn⟩ := hn
        cases hn
      · subst rSent
        change r * 2 + 2 ≤ 7 at hafter
        omega

#print axioms progress_premises_sat

private theorem proposal_service_premises_sat (top : Bool) :
    ∀ q Q, HonestProposal env run iface q Q →
      FrontierProposalService (core top) env run d5cTiming q Q := by
  intro q Q hp _ x hx _
  obtain ⟨hq, he⟩ := proposal_unique hp
  have h10 : @LE.le Nat _ q 10 := by rcases hq with rfl | rfl | rfl <;> decide
  rw [headAtLabel, execution_premises_sat.2.2.2.2.2.2.2.2 x hx q h10]
  exact congrArg some he.symm

#print axioms proposal_service_premises_sat

private theorem local_service_premises_sat (top : Bool) (q : Nat) (hq : q = 5 ∨ q = 7)
    (v : Time) (hhor : v ≤ 46) :
    FrontierLocalServiceFG (core top) reads env run (obs top) d5cTiming iface wire.heightPair
      q (c5erase (chainAt q)) (chainAt q) 2 v := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x s H _ hqs _ hhead
    change @LE.le Nat _ (q + 1) s at hqs
    have hs : @LE.le Nat _ 6 s := by rcases hq with rfl | rfl <;> omega
    have h1 : ¬ s ≤ 2 := Nat.not_le.mpr (by omega)
    have h5 : ¬ s ≤ 5 := Nat.not_le.mpr (by omega)
    have hl : chainAt s = late := by simp only [chainAt, h1, h5, ite_false]
    delta headAtLabel at hhead
    obtain ⟨nd, _, he⟩ := Option.map_eq_some_iff.mp hhead
    change c5erase (chainAt s) = H at he
    rw [← he, hl]
    rcases hq with rfl | rfl <;> decide +kernel
  · intro s B hqs _ hp
    change @LE.le Nat _ (q + 2) s at hqs
    obtain ⟨hs, he⟩ := proposal_unique hp
    subst B
    rcases hq with rfl | rfl <;> rcases hs with rfl | rfl | rfl
    all_goals first | omega | decide +kernel
  · intro i x _ _ _ _
    change Block.Preceq (c5erase (chainAt q)) (c5erase late)
    rcases hq with rfl | rfl <;> decide +kernel
  · intro s B _ _ hp
    exact proposal_service_premises_sat top s B hp
  · intro r hqr ht
    change @LE.le Nat _ q (r * 2) at hqr
    have ht46 := ht.trans hhor
    change 8 * (r : Int) + 6 ≤ 46 at ht46
    have hr5 : @LE.le Nat _ r 5 := by omega
    have hr3 : @LE.le Nat _ 3 r := by rcases hq with rfl | rfl <;> omega
    have hopen := opening_premises_sat top r (by omega) hr5
    have hh : (c5H (sourceAt (d5cTiming.action r))).h = 2 := by
      interval_cases r <;> decide +kernel
    have he : (c5H (sourceAt (d5cTiming.action r))).T_h = (c5H (chainAt q)).T_h := by
      rcases hq with rfl | rfl <;> interval_cases r <;> decide +kernel
    have hpath : FGBlock.Preceq (chainAt q) (sourceAt (d5cTiming.action r)) := by
      rcases hq with rfl | rfl <;> interval_cases r
      all_goals first | omega | decide +kernel
    refine ⟨hopen.2 _ hpath, ?_, ?_, ?_⟩
    · simpa only [hh] using hopen.1 hr3
    · intro x K _ hk
      rcases (source_premises_sat top).1 r x K hk with ⟨_, _, hr2⟩ | rfl
      · omega
      · exact he
    · intro hfirst
      rcases hq with rfl | rfl
      · have hr : @LE.le Nat _ r 3 := hfirst 3 (by decide)
        have hr' : @Eq Nat r 3 := by omega
        subst r
        decide
      · have hr : @LE.le Nat _ r 4 := hfirst 4 (by decide)
        have hr' : @Eq Nat r 4 := by omega
        subst r
        decide

#print axioms local_service_premises_sat

private theorem repair_premises_sat (top : Bool) :
    AttemptProposalFloor (core top) env run (obs top) d5cTiming iface 0 ∧
    (∀ u v m J c q Q, (0 : Time) ≤ u → PhaseInterval (core top) env run (obs top) u v m J c →
      FrontierSeedQualification d5cTiming 1 env.t_GST u q → d5cTiming.gate q ≤ v →
      HonestProposal env run iface q Q → ∃ i x Qfg, run.idxBefore u ≤ i ∧ i ≤ timeIdx run v ∧
        x ∈ run.honest ∧ Qfg ∈ ((core top).core (run.stateBefore env i x)).fg.TF ∧
        c5erase Qfg = Q) ∧
    FrontierRepairAllowance (core top) env run (obs top) d5cTiming iface 0 1 20 14 0 ∧
    (∀ i x A K, K ∈ ((core top).core (run.stateBefore env i x)).fg.TF →
      FGBlock.Preceq A K → A.slot ≤ K.slot) ∧
    (∀ q Q K, HonestProposal env run iface q Q → c5erase K = Q → K.slot = q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u v m J c q Q Qfg _ hp _ _ _ _
    have hcut : run.idxBefore u ≤ timeIdx run v :=
      (gidxBefore_le_timeIdx run u).trans (frontierSearch_timeIdx_mono run hp.1)
    have hf := hp.2.2.2 _ 7 le_rfl hcut (by decide)
    have hm : m = 2 := hf.1.symm
    have hc : ((obs top).controls (0, false)).contest = c := hf.2.1
    have hc0 : ((obs top).controls (0, false)).contest = false := by cases top <;> decide +kernel
    have hc' : c = false := hc.symm.trans hc0
    rw [hm, hc']
    exact c5H_pos _
  · intro u v m J c q Q _ hp _ _ hQ
    obtain ⟨hq, he⟩ := proposal_unique hQ
    refine ⟨run.idxBefore u, 7, chainAt q, le_rfl, ?_, by decide, ?_, he.symm⟩
    · exact (gidxBefore_le_timeIdx run u).trans (frontierSearch_timeIdx_mono run hp.1)
    · change chainAt q ∈ stored top
      rcases hq with rfl | rfl | rfl <;> cases top <;> decide +kernel
  · refine ⟨by decide, 0 + 1,
      .one 0 (by decide) (fun _ _ => Nat.zero_le _) (by decide) (by decide), ?_⟩
    intro _ v m J c _ _
    refine ⟨fun s Q _ _ hp => proposal_service_premises_sat top s Q hp, fun _ => ?_⟩
    have hp := (proposal_premises_sat.2 2 (Or.inl rfl)).1
    exact ⟨2, c5erase low, by decide, by decide, hp,
      proposal_service_premises_sat top 2 _ hp⟩
  · intro i x A K hk ha
    have hslots : m9slotsOK K = true := by
      change K ∈ stored top at hk
      cases top
      · simp only [stored, Bool.false_eq_true, ite_false, Finset.mem_insert,
          Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
      · simp only [stored, ite_true, Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    exact m9anc_slot hslots ha
  · intro q Q K hp he
    obtain ⟨hq, hQ⟩ := proposal_unique hp
    have hK : K = chainAt q := c5erase_inj (he.trans hQ)
    rw [hK]
    rcases hq with rfl | rfl | rfl <;> decide +kernel

#print axioms repair_premises_sat

private theorem branch_premises_sat (top : Bool) :
    (∀ u v m J contested q Q Qfg, (0 : Time) ≤ u → HonestProposal env run iface q Q → (core
      top).erase Qfg = Q → ((obs top).height Qfg).h = m → FrontierProposalService (core top)
      env run d5cTiming q Q → FrontierSeedQualification d5cTiming 1 env.t_GST u q → u ≤
      d5cTiming.proposal q → PhaseInterval (core top) env run (obs top) u (d5cTiming.gate q) m
      J contested → d5cTiming.gate q ≤ v → v ≤ run.horizon → (∀ i x, timeIdx run u ≤ i → i ≤
      timeIdx run v → x ∈ run.honest → ((core top).core (run.stateBefore env i x)).fg.h_max ≤
      m) → FrontierLocalServiceFG (core top) reads env run (obs top) d5cTiming iface
      wire.heightPair q Q Qfg m v) ∧
    (∀ u m J contested q Q Qfg r, (0 : Time) ≤ u → HonestProposal env run iface q Q → (core
      top).erase Qfg = Q → FrontierProposalService (core top) env run d5cTiming q Q →
      FrontierSeedQualification d5cTiming 1 env.t_GST u q → u ≤ d5cTiming.proposal q → q ≤ r *
      d5cTiming.roundSlots → (∀ r', q ≤ r' * d5cTiming.roundSlots → r ≤ r') → PhaseInterval
      (core top) env run (obs top) u (d5cTiming.action r) m J contested → OpeningCoveredFG
      (core top) reads env run (obs top).height d5cTiming wire.heightPair (FGHonestSeats reads
      run) r Q ∧ (((obs top).height Qfg).h = m - 1 → OpeningEntry (core top) env run (obs
      top).height d5cTiming r (m - 1) ∨ ∃ x K, x ∈ run.honest ∧ actionSourceFG (core top) env
      run d5cTiming x r = some (some K) ∧ ((obs top).height K).h = m)) := by
  constructor
  · intro u v m J c q Q Qfg _ hp he hh _ _ _ hphase _ hhor _
    have hcut : run.idxBefore u ≤ timeIdx run (d5cTiming.gate q) :=
      (gidxBefore_le_timeIdx run u).trans (frontierSearch_timeIdx_mono run hphase.1)
    have hm : m = 2 := (hphase.2.2.2 _ 7 le_rfl hcut (by decide)).1.symm
    obtain ⟨hq, hQ⟩ := proposal_unique hp
    have hB : Qfg = chainAt q := c5erase_inj (he.trans hQ)
    rw [hB, hm] at hh
    rw [hB, hQ, hm]
    apply local_service_premises_sat top q _ v hhor
    rcases hq with rfl | rfl | rfl
    · change (c5H (chainAt 2)).h = 2 at hh
      exact absurd hh (by decide +kernel)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro u m J c q Q Qfg r _ hp he _ _ _ hqr hfirst hphase
    have hcut : run.idxBefore u ≤ timeIdx run (d5cTiming.action r) :=
      (gidxBefore_le_timeIdx run u).trans (frontierSearch_timeIdx_mono run hphase.1)
    have hm : m = 2 := (hphase.2.2.2 _ 7 le_rfl hcut (by decide)).1.symm
    obtain ⟨hq, hQ⟩ := proposal_unique hp
    have hB : Qfg = chainAt q := c5erase_inj (he.trans hQ)
    rw [hB, hQ, hm]
    change @LE.le Nat _ q (r * 2) at hqr
    rcases hq with rfl | rfl | rfl
    · have hr : @LE.le Nat _ r 1 := hfirst 1 (by decide)
      have hr' : @Eq Nat r 1 := by omega
      subst r
      have ho := opening_premises_sat top 1 (by decide) (by decide)
      refine ⟨ho.2 (chainAt 2) (by decide +kernel), ?_⟩
      intro _
      exact Or.inr ⟨7, raised, by decide, (source_premises_sat top).2.2.2.2.1,
        by change (c5H raised).h = 2; decide +kernel⟩
    · have hr : @LE.le Nat _ r 3 := hfirst 3 (by decide)
      have hr' : @Eq Nat r 3 := by omega
      subst r
      have ho := opening_premises_sat top 3 (by decide) (by decide)
      refine ⟨ho.2 (chainAt 5) (by decide +kernel), ?_⟩
      intro hh
      change (c5H (chainAt 5)).h = 1 at hh
      exact absurd hh (by decide +kernel)
    · have hr : @LE.le Nat _ r 4 := hfirst 4 (by decide)
      have hr' : @Eq Nat r 4 := by omega
      subst r
      have ho := opening_premises_sat top 4 (by decide) (by decide)
      refine ⟨ho.2 (chainAt 7) (by decide +kernel), ?_⟩
      intro hh
      change (c5H (chainAt 7)).h = 1 at hh
      exact absurd hh (by decide +kernel)

#print axioms branch_premises_sat

/-- Exact trigger: the only repair seed is low; its first opening has a high source
only at nonholder 7, while holder 9 supplies the original low row. -/
private theorem high_source_premises_sat :
    run.honest = {7, 9} ∧ (∀ i, safetyHolder reads run i = 9) ∧
    (∀ q Q, HonestProposal env run iface q Q → d5cTiming.gate q ≤ 14 →
      q = 2 ∧ Q = c5erase low) ∧
    (∀ r, 2 ≤ r * d5cTiming.roundSlots →
      (∀ r', 2 ≤ r' * d5cTiming.roundSlots → r ≤ r') → r = 1) ∧
    actionSourceFG (core true) env run d5cTiming 7 1 = some (some raised) ∧
    (c5H raised).h = 2 ∧
    actionSourceFG (core true) env run d5cTiming 9 1 = some (some low) ∧
    (c5H low).h = 1 ∧
    (¬ OpeningEntry (core true) env run c5H d5cTiming 1 1) ∧
    HonestRowAt reads env run d5cTiming 13 9 0 firstRow ∧
    protocol.objSelfVisible (reads.encode firstRow) = true ∧
    reads.decodeObject (reads.encode firstRow) = some firstRow ∧
    (∀ j t a, run.events[j]? = some (.tick 7 t) →
      reads.encode a ∉ V2.D.Run.emitsAt env run j) := by
  refine ⟨rfl, fun _ => rfl, ?_, ?_, (source_premises_sat true).2.2.2.2.1,
    by decide +kernel, by decide +kernel, by decide +kernel, ?_,
    execution_premises_sat.2.2.2.1, rfl, rfl, ?_⟩
  · intro q Q hp hg
    obtain ⟨hq, he⟩ := proposal_unique hp
    rcases hq with rfl | rfl | rfl
    · exact ⟨rfl, he⟩
    · exact absurd hg (by decide)
    · exact absurd hg (by decide)
  · intro r hr hf
    have h1 := hf 1 (by decide)
    change 2 ≤ r * 2 at hr
    omega
  · intro he
    have hh := (he.choose_spec 7 raised (by decide)
      (source_premises_sat true).2.2.2.2.1).1
    exact absurd hh (by decide +kernel)
  · intro j t a hj
    have table : ∀ k : Fin 94, run.events[k.val]?.map V2.Event.node = some 7 →
        (V2.D.Run.emitsAt env run k.val).all (fun o => decide (o.auth ≠ .seat 6 0)) =
          true := by decide +kernel
    have hlen : j < 94 := (List.getElem?_eq_some_iff.mp hj).1
    have hnode : run.events[j]?.map V2.Event.node = some 7 := by rw [hj]; rfl
    intro ha
    have hn := of_decide_eq_true
      ((List.all_eq_true.mp (table ⟨j, hlen⟩ hnode)) (reads.encode a) ha)
    exact hn rfl

#print axioms high_source_premises_sat

end High

end AvailableChain.FGCompose.Tests.PopulationSearchPhase
end
