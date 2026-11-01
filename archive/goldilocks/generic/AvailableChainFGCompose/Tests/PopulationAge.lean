module
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchAge
public import AvailableChainFGCompose.Proofs.Population.PromotionSourceBridges
public import AvailableChainFGCompose.Proofs.Finality.History -- shake: keep (window views)

set_option linter.privateModule false

noncomputable section
public section

/-! POP-3 generic ordinary-event-fold controls, not concrete PC execution producers.
The sole FG seat belongs to 9; honest proposer 7 carries its exact row. -/
namespace AvailableChain.FGCompose.Tests.PopulationAge
open AvailableChain.SimplexFG AvailableChain.KitFG

private abbrev ef : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private abbrev cfg : FGConfig := ⟨4⟩
private abbrev row : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private abbrev child : FGBlock (Fin 1) := .node .genesis 5 ⟨41⟩ 0 [row]
private def erase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node p s r x rs => .node (erase p) s r (encFGBody x rs)
private abbrev protocol : V2.ProtocolSpecD Unit where
  State := Unit
  Label := Time
  Duty := Time
  signLabel := id
  seats := fun _ => 1
  Payload := Row (Fin 1) ⊕ FGBlock (Fin 1)
  Durable := Unit
  init := ()
  clock := fun st _ => st
  actTime := id
  duties := fun t => [t]
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; simp
  act := fun _ t _ => if t = 6 then some (.inl row)
    else if t = 20 then some (.inr child) else none
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
private abbrev reads : FGSafetyReads protocol 1 (Row (Fin 1)) where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode := fun a => ⟨.seat 6 0, .inl a⟩
  decode := some
  decodeObject := fun o => match o.auth with
    | .seat l _ => if l = 6 then o.payload.getLeft? else none
    | .none => none
  fgLabel := 6
  fgSeats := Equiv.refl _
  record := fun _ => RecordOnce.initial
  inputs := fun _ => (some .genesis, ⟨0, genesisRoot, 0⟩)
  enabled := fun _ => true
  finalizedOut := fun _ => .genesis
private abbrev env : Generic.Env Nat :=
  ⟨1, by decide, 0, by decide, fun x t => decide (t = 6 ∨ (x = 7 ∧ t = 20))⟩
private abbrev run : V2.D.Run Nat protocol where
  honest := {7, 9}
  horizon := 38
  events := [.tick 9 6, .tick 7 6, .tick 7 20]
  seatOf := fun l _ => if l = 6 then 9 else if l = 20 then 7 else 0
  input := fun _ _ => ()
private abbrev timing : FGTiming where
  delta := 1
  roundSlots := 2
  proposal s := 4 * (s : Time)
  vote s := 4 * (s : Time) + 1
  early s := 4 * (s : Time) + 2
  freeze s := 4 * (s : Time) + 3
  release s := 4 * (s : Time) + 5
  gate s := 4 * (s : Time) + 6
  action r := 8 * (r : Time) + 6
private abbrev core : FGCoreReads protocol 1 Unit Unit (Row (Fin 1)) where
  core _ := ⟨(), ⟨{.genesis, child}, .genesis, .genesis, 0, 1⟩, [], [row]⟩
  erase := erase
  source := fun _ => some .genesis
  headVote := fun _ _ => .genesis
  finalityHead := fun _ => some .genesis
  proposalFG := fun _ _ => none
private abbrev height := Window.certificateHeight ef cfg 2
private abbrev obs : FGObservationReads core where
  height := height
  finality := Window.certificateFinality ef cfg 2
  controls nd := treeStoreControlsView height (core.core nd).fg
  viable nd X := treeStoreFrameView height (core.core nd).fg X
private abbrev iface : V2.D.Interface protocol where
  confirmed _ := .genesis
  stable _ := .genesis
  opening _ := True
  propLabel s := 4 * (s : Time)
  propDuty s := 4 * (s : Time)
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective := by
    intro a b h
    change 4 * (a : Int) = 4 * (b : Int) at h
    exact Int.ofNat_injective (mul_left_cancel₀ (by decide : (4 : Int) ≠ 0) h)
  block := fun p => match p with | .inr X => some (erase X) | .inl _ => none
private abbrev wire : FGHistoryWireReads reads where
  signer := fun a => some a.signer
  heightPair := Row.height_pair
  finalityPair := Row.finality_pair
  decode_finality := by intro a b h; cases h; rfl
  decode_signer := by intro a b h; cases h; rfl
  decode_height := by intro a b h; cases h; rfl
private abbrev decodeProposal (o : protocol.Object) : Option (Slot × FGBlock (Fin 1)) :=
  match o.payload with | .inr X => some (X.slot, X) | .inl _ => none
private abbrev parentFG (_ : Unit) (_ : Block) : Option (FGBlock (Fin 1)) := some .genesis
private abbrev fold (_ : Unit) (_ : Slot) (P : FGBlock (Fin 1)) := Window.derive ef cfg 2 P
private abbrev parentHeight (nd : Unit) (s : Slot) (P : FGBlock (Fin 1)) : Height × BlockId :=
  ((fold nd s P).h, (fold nd s P).T_h.root)
private abbrev validFor (nd : Unit) (s : Slot) (P : FGBlock (Fin 1)) (a : Row (Fin 1)) :=
  Window.r6w (fold nd s P) a

private theorem erase_injective : Function.Injective erase := by
  intro A
  induction A with
  | genesis => intro B h; cases B <;> simp_all [erase]
  | node p s r x rs ih =>
    intro B h
    cases B with
    | genesis => simp [erase] at h
    | node q t u y ts =>
      simp only [erase, Block.node.injEq] at h
      obtain ⟨hp, hs, hr, hb⟩ := h
      obtain ⟨hx, hrows⟩ := encFGBody_inj hb
      cases ih hp
      cases hs
      cases hr
      cases hx
      cases hrows
      rfl

#print axioms erase_injective

private theorem source_premises_sat :
    run.honest = {7, 9} ∧ run.horizon = 38 ∧
    run.events = [.tick 9 6, .tick 7 6, .tick 7 20] ∧
    (∀ i, safetyHolder reads run i = 9) ∧ FGHonestSeats reads run = {0} ∧
    protocol.objSelfVisible (reads.encode row) = true ∧
    reads.decodeObject (reads.encode row) = some row ∧
    HonestRowAt reads env run timing 0 9 0 row ∧
    V2.D.proposerOf run iface 5 = 7 ∧
    HonestCarrier env run iface (kernelCarrier decodeProposal erase FGBlock.rows)
      5 (erase child) [row] ∧
    (∀ x ∈ run.honest,
      actionSourceFG core env run timing x 0 = some (some .genesis)) ∧
    PromotionSourceAtFG core reads env run obs timing iface wire
      (FGHonestSeats reads run) 1 0 1 .genesis 5 child := by
  have hp : HonestProposal env run iface 5 (erase child) := by
    refine ⟨⟨by decide, by decide⟩, ⟨.seat 20 0, .inr child⟩,
      ⟨2, by decide +kernel, by decide +kernel⟩, rfl⟩
  have hr : HonestRowAt reads env run timing 0 9 0 row := by
    unfold HonestRowAt
    decide +kernel
  refine ⟨rfl, rfl, rfl, fun _ => rfl, ?_, rfl, rfl, hr, rfl, ?_, ?_, ?_⟩
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [FGHonestSeats_def, safetyHolder, reads, run]
  · exact ⟨hp, ⟨.seat 20 0, .inr child⟩,
      ⟨2, by decide +kernel, by decide +kernel⟩, child, rfl, rfl, rfl⟩
  · intro x hx
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl <;> decide +kernel
  · refine ⟨⟨rfl, rfl⟩, preceq_refl _, hp, rfl, by decide,
      by decide, by decide, by decide, ?_⟩
    intro i _
    exact ⟨0, 0, row, le_rfl, hr, false, rfl⟩

#print axioms source_premises_sat

private theorem row_identity {j r x : Nat} {a : Row (Fin 1)}
    (h : HonestRowAt reads env run timing j x r a) :
    j = 0 ∧ x = 9 ∧ r = 0 ∧ a = row := by
  obtain ⟨_, hj, ha⟩ := h
  have hjlt : j < 3 := (List.getElem?_eq_some_iff.mp hj).1
  interval_cases j
  · have hx : x = 9 := by
      have he := congrArg (fun e => e.map V2.Event.node) hj
      exact Option.some.inj he.symm
    have ht : timing.action r = 6 := by
      have he := congrArg (fun e => e.map V2.Event.time) hj
      exact Option.some.inj he.symm
    have hr : r = 0 := by change 8 * (r : Int) + 6 = 6 at ht; omega
    subst x r
    change reads.encode a ∈ [reads.encode row] at ha
    have he := congrArg V2.Signed.payload (List.mem_singleton.mp ha)
    exact ⟨rfl, rfl, rfl, Sum.inl.inj he⟩
  · change reads.encode a ∈ [] at ha
    cases ha
  · change reads.encode a ∈ [⟨.seat 20 0, .inr child⟩] at ha
    have he := congrArg V2.Signed.payload (List.mem_singleton.mp ha)
    cases he

#print axioms row_identity

/-- The sole missing old premise is a row at honest nonholder 7. -/
private theorem nonholder_source_rejected :
    (¬ PromotionSourceAt core reads env run obs timing iface wire 1 0 1 .genesis 5 child) ∧
    (∀ j r a, ¬ HonestRowAt reads env run timing j 7 r a) ∧
    (∀ j t a, run.events[j]? = some (.tick 7 t) →
      reads.encode a ∉ V2.D.Run.emitsAt env run j) := by
  have hn (j r a) (h : HonestRowAt reads env run timing j 7 r a) : False := by
    have hx := (row_identity h).2.1
    omega
  refine ⟨?_, hn, ?_⟩
  · intro h
    obtain ⟨j, r, a, _, hr, _⟩ := h.rows 7 (by decide)
    exact hn j r a hr
  · intro j t a hj ha
    have hjlt : j < 3 := (List.getElem?_eq_some_iff.mp hj).1
    interval_cases j
    · have he := congrArg (fun e => e.map V2.Event.node) hj
      have hx : (9 : Nat) = 7 := Option.some.inj he
      omega
    · change reads.encode a ∈ [] at ha
      cases ha
    · change reads.encode a ∈ [⟨.seat 20 0, .inr child⟩] at ha
      have he := congrArg V2.Signed.payload (List.mem_singleton.mp ha)
      cases he

#print axioms nonholder_source_rejected

private theorem proposal_unique {s : Slot} {X : FGBlock (Fin 1)}
    (h : HonestProposal env run iface s (erase X)) : s = 5 ∧ X = child := by
  obtain ⟨_, o, ⟨j, hj, ho⟩, hb⟩ := h
  have hjlt : j < 3 := (List.getElem?_eq_some_iff.mp hj).1
  interval_cases j
  · have ht : (6 : Int) = 4 * (s : Int) :=
      Option.some.inj (congrArg (fun e => e.map V2.Event.time) hj)
    omega
  · change o ∈ [] at ho
    cases ho
  · have ht : (20 : Int) = 4 * (s : Int) :=
      Option.some.inj (congrArg (fun e => e.map V2.Event.time) hj)
    have hs : s = 5 := by
      apply Int.ofNat_injective
      change (s : Int) = 5
      linarith only [ht]
    change o ∈ [⟨.seat 20 0, .inr child⟩] at ho
    have ho' := List.mem_singleton.mp ho
    subst o
    exact ⟨hs, erase_injective (Option.some.inj hb).symm⟩

#print axioms proposal_unique

private theorem fold_premises_sat : ProgressFoldAdvance ef height 4 := by
  have m9transition_progress (σ : ChainState (Fin 1)) (B : FGBlock (Fin 1))
      (rs : List (Row (Fin 1))) (S : Finset (Fin 1)) (hS : ef.IsQuorum S)
      (hcover : ∀ i ∈ S, i ∈ σ.progress ∨
        ∃ a ∈ rs, a.signer = i ∧ a.height_pair.matchesEntry σ.h σ.T_h.root = true)
      (hmature : σ.T_h.slot + cfg.timeoutDelay ≤ B.slot) :
      (transition ef cfg σ B rs).h = σ.h + 1 := by
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
    have hq : ef.IsQuorum (foldRows σ B rs).progress :=
      isQuorum_of_subset ef hS (fun i hi => hfold rs { σ with s := B.slot } i (hcover i hi))
    have hp : progReady ef cfg (afterFin ef (foldRows σ B rs)) = true := by
      simp only [progReady, Bool.or_eq_true, Bool.and_eq_true]
      right
      constructor
      · simpa only [afterFin_T_h, afterFin_s, (foldRows_fields σ B rs).2.2.1,
          foldRows_s, decide_eq_true_eq] using hmature
      · change decide (ef.q ≤ ef.weightOf (afterFin ef (foldRows σ B rs)).progress) = true
        rw [decide_eq_true_eq, afterFin_progress]
        exact hq
    change (process_height_events ef cfg (foldRows σ B rs)).h = σ.h + 1
    rw [process_height_events_eq]
    have hh := (afterFin_h ef (foldRows σ B rs)).trans (foldRows_fields σ B rs).2.1
    split_ifs with ht
    · exact congrArg (· + 1) hh
    · exact congrArg (· + 1) hh
  have m9progress_of_cover (hb : HeightBridge ef cfg height)
      (p : FGBlock (Fin 1)) (s : Slot) (r_s : BlockId) (x : Nat)
      (rs : List (Row (Fin 1))) (S : Finset (Fin 1)) (hS : ef.IsQuorum S)
      (hcover : ∀ i ∈ S, i ∈ (height p).progress ∨
        ∃ a ∈ rs, a.signer = i ∧
          a.height_pair.matchesEntry (height p).h (height p).T_h.root = true)
      (hmature : (height p).T_h.slot + cfg.timeoutDelay ≤ s) :
      (height (.node p s r_s x rs)).h = (height p).h + 1 := by
    have heq : ∀ B, height B = heightOf (derive ef cfg B) := hb
    simp only [heq, heightOf_def] at hcover hmature ⊢
    exact m9transition_progress (derive ef cfg p) (.node p s r_s x rs) rs S hS hcover hmature
  intro y U X hX hU hUX hc hm
  have hb := KitFG.Window.windowHeightBridge ef cfg 2 (by decide)
  have laws := heightLaws_of_bridge ef cfg _ hb
  have hlow := laws.h_mono hUX
  change (height U).h ≤ (height X.parent).h at hlow
  rw [hU.1] at hlow
  cases X with
  | genesis => exact (hX rfl).elim
  | node P s root x rs =>
    change y ≤ (height P).h at hlow
    by_cases hP : (height P).h = y
    · have hT : (height P).T_h = U :=
        (laws.entry_plateau hUX (hU.1.trans hP.symm)).symm.trans hU.2
      obtain ⟨S, hS, hcov⟩ := hc hP
      have hh := m9progress_of_cover hb P s root x rs S hS (by
          intro i hi
          rcases hcov i hi with hbit | ⟨a, ha, hs, timeout, hp⟩
          · exact Or.inl hbit
          · refine Or.inr ⟨a, ha, hs, ?_⟩
            rw [hp]
            change decide (y = (height P).h ∧ U.root = (height P).T_h.root) = true
            simp only [hP, hT, and_self, decide_true]) (by
          change (height P).T_h.slot + 4 ≤ s
          rw [hT]
          exact hm)
      change (height (.node P s root x rs)).h = (height P).h + 1 at hh
      rw [hh, hP]
    · have hPX := laws.h_mono (preceq_parent_node P s root x rs)
      change (height P).h ≤ (height (.node P s root x rs)).h at hPX
      simp only [Height] at *
      omega

#print axioms fold_premises_sat

private theorem advance_premises_sat :
    FGHeightLaws ef height ∧ FGTimingLaws timing ∧ V2.D.ScheduleWellFormed env run ∧
    ef.weightOf (historyFaulty reads run) < ef.q ∧ LivenessBoundW timing 1 ∧
    TRowsReceipt core reads env run timing (fun _ => [row]) 1 ∧
    PromotionProposalRead core reads env run obs iface decodeProposal erase FGBlock.rows
      parentFG parentHeight validFor fold ∧
    PromotionRowOrder core env run obs iface ∧ PromotionRowSigner reads env run timing wire ∧
    (∀ r h U X, BatchPrem core reads obs timing env run iface wire ef decodeProposal erase
      FGBlock.rows (fun _ => [row]) parentFG parentHeight validFor 1 .progress r h U X →
      (height X.parent).h = h → ProgressCoveredByChild ef height X U h) ∧
    ef.q ≤ ef.weightOf (FGHonestSeats reads run) := by
  refine ⟨heightLaws_of_bridge ef cfg _ (Window.windowHeightBridge ef cfg 2 (by decide)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by decide, by decide, fun _ => by simp, fun _ => rfl,
      fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
      fun _ => by simp; ring⟩
  · refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
    · intro x t ht
      have ht' : (x = 9 ∧ t = 6) ∨ (x = 7 ∧ t = 6) ∨ (x = 7 ∧ t = 20) := by
        simpa only [run, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
          V2.Event.tick.injEq] using ht
      rcases ht' with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact ⟨6, rfl⟩
      · exact ⟨6, rfl⟩
      · exact ⟨20, rfl⟩
    · intro x hx t _ _ _ ht
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      have ht' : t = 6 ∨ (x = 7 ∧ t = 20) := of_decide_eq_true ht
      rcases ht' with rfl | ⟨rfl, rfl⟩
      · rcases hx' with rfl | rfl <;> decide
      · decide
  · have hf : historyFaulty reads run = ∅ := by
      ext i
      change (i ∈ Finset.univ.filter (fun i => safetyHolder reads run i ∉ run.honest)) ↔ _
      simp [safetyHolder]
    rw [hf]
    decide
  · constructor; decide
  · intro j x r a hr _ y _
    obtain ⟨_, _, _, rfl⟩ := row_identity hr
    exact Or.inl (List.mem_singleton_self _)
  · intro s X hp _
    obtain ⟨rfl, rfl⟩ := proposal_unique hp
    refine ⟨⟨[row], ?_, rfl⟩, (), rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
    exact source_premises_sat.2.2.2.2.2.2.2.2.2.1
  · intro s X h U hp _ _ _ i W hw hn
    obtain ⟨_, rfl⟩ := proposal_unique hp
    have hg : W = .genesis := preceq_genesis.mp hw
    subst W
    obtain ⟨a, ha, _⟩ := hn
    cases ha
  · refine ⟨fun _ _ _ a _ => ⟨a, rfl⟩, ?_⟩
    intro i j r a ha
    obtain ⟨_, _, _, rfl⟩ := row_identity ha
    rw [Subsingleton.elim i 0]
  · intro r h U X hb hh
    obtain ⟨_, hc, _⟩ := hb.carrier
    obtain ⟨_, rfl⟩ := proposal_unique hc.1
    have hU : U = .genesis := preceq_genesis.mp hb.path
    subst U
    have hh' : h = 1 := hh.symm
    subst h
    refine ⟨{0}, by decide, ?_⟩
    intro i hi
    have hi' : i = 0 := Finset.mem_singleton.mp hi
    subst i
    exact Or.inr ⟨row, List.mem_singleton_self _, rfl, false, rfl⟩
  · rw [source_premises_sat.2.2.2.2.1]
    decide

#print axioms advance_premises_sat

private theorem mixed_age_advance :
    2 ≤ (height child).h ∧
    (∀ j x r a, HonestRowAt reads env run timing j x r a →
      j = 0 ∧ x = 9 ∧ r = 0 ∧ a = row) ∧
    (∃ x K, x = 7 ∧ x ∈ run.honest ∧
      actionSourceFG core env run timing x 0 = some (some K) ∧
      (height K).T_h = .genesis) := by
  obtain ⟨hl, ht, hs, hf, hb, hrec, hr, ho, hsi, hc, hq⟩ := advance_premises_sat
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hsource, src⟩ := source_premises_sat
  refine ⟨?_, fun _ _ _ _ h => row_identity h, 7, .genesis, rfl, by decide,
    hsource 7 (by decide), rfl⟩
  exact promotion_age_advance_of_source_holder core reads obs timing env run iface wire ef
    decodeProposal erase FGBlock.rows (fun _ => [row]) parentFG parentHeight validFor fold hl
    (Finset.Subset.refl _) ht hs hf (by decide) rfl src rfl hb hrec hc fold_premises_sat
    hq hr ho hsi

#print axioms mixed_age_advance

private theorem search_premises_sat :
    (∀ t, env.t_GST ≤ t → t + 20 ≤ run.horizon →
      ∃ s, t < timing.proposal s ∧ timing.proposal s ≤ t + 20 ∧
        Gen.V2.Duty.HonestSlot run iface s) ∧
    PromotionSlotProposal core env run timing iface ∧
    PromotionSourceParent core env run obs timing iface 0 ∧
    OpeningEntry core env run height timing 0 1 ∧
    OpeningCoveredFG core reads env run height timing wire.heightPair
      (FGHonestSeats reads run) 0 .genesis ∧
    (∀ x y K L, x ∈ run.honest → y ∈ run.honest →
      actionSourceFG core env run timing x 0 = some (some K) →
      actionSourceFG core env run timing y 0 = some (some L) →
      (height K).T_h.root = (height L).T_h.root → (height K).T_h = (height L).T_h) ∧
    (∀ x K, x ∈ run.honest →
      actionSourceFG core env run timing x 0 = some (some K) → K.slot ≤ 0 * timing.roundSlots) ∧
    (∀ x K A, x ∈ run.honest →
      actionSourceFG core env run timing x 0 = some (some K) → FGBlock.Preceq A K →
      A.slot ≤ K.slot) ∧
    PhaseInterval core env run obs 0 38 1 (some .genesis) false := by
  have src_eq {x r K} (h : actionSourceFG core env run timing x r = some (some K)) :
      K = .genesis := by
    unfold actionSourceFG at h
    obtain ⟨nd, _, hnd⟩ := Option.map_eq_some_iff.mp h
    exact (Option.some.inj hnd).symm
  obtain ⟨_, _, _, _, _, _, _, hr, _, hcar, hsrc, _⟩ := source_premises_sat
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht hh
    refine ⟨5, ?_, ?_, hcar.1.1⟩
    · change 0 ≤ t at ht
      change t + 20 ≤ 38 at hh
      change t < 20
      linarith only [hh]
    · change 0 ≤ t at ht
      change 20 ≤ t + 20
      linarith only [ht]
  · intro s hs _ _
    have hn : (4 : Int) * (s : Int) ≠ 6 := by omega
    have hs5 : s = 5 := by
      have hh := hs.2
      change (if 4 * (s : Int) = 6 then 9 else
        if 4 * (s : Int) = 20 then 7 else 0) ∈ ({7, 9} : Finset Nat) at hh
      rw [ite_eq_right hn] at hh
      split_ifs at hh with he
      · apply Int.ofNat_injective
        change (s : Int) = 5
        linarith only [he]
      · simp at hh
    subst s
    exact ⟨child, hcar.1, rfl⟩
  · intro u m J c r s X x K _ _ _ _ _ _ _ hk
    rw [src_eq hk]
    exact genesis_preceq _
  · refine ⟨genesisRoot, ?_⟩
    intro x K _ hk
    rw [src_eq hk]
    exact ⟨rfl, rfl⟩
  · intro i _
    refine ⟨.genesis, (), 0, 0, row, rfl, ?_, by decide, by decide, le_rfl, hr, rfl⟩
    exact hsrc 9 (by decide)
  · intro x y K L _ _ hk hl _
    rw [src_eq hk, src_eq hl]
  · intro x K _ hk
    rw [src_eq hk]
    exact le_rfl
  · intro x K A _ hk ha
    have hk' := src_eq hk
    subst K
    have ha' := preceq_genesis.mp ha
    subst A
    exact le_rfl
  · refine ⟨by decide, le_rfl, le_rfl, ?_⟩
    intro i x _ _ _
    change (obs.controls ()).H = 1 ∧ (obs.controls ()).contest = false ∧
      (obs.controls ()).rootIsJ = true ∧ (obs.controls ()).J = .genesis
    decide +kernel

#print axioms search_premises_sat

private theorem mixed_search_age :
    ∃ s X, s = 5 ∧ X = child ∧ HonestProposal env run iface s (erase X) ∧
      X.slot = s ∧ timing.action 0 < timing.proposal s ∧ timing.gate s ≤ 38 ∧
      2 ≤ (height X).h := by
  obtain ⟨hl, ht, hs, hf, hb, hrec, hr, ho, hsi, hc, hq⟩ := advance_premises_sat
  obtain ⟨gap, hslot, hparent, hentry, hcover, hagree, hsourceSlot, hancestorSlot, hp⟩ :=
    search_premises_sat
  have hne : (FGHonestSeats reads run).Nonempty := by
    rw [source_premises_sat.2.2.2.2.1]
    exact ⟨0, Finset.mem_singleton_self _⟩
  have hsource : ∃ x K, x ∈ run.honest ∧
      actionSourceFG core env run timing x 0 = some (some K) ∧
      (height K).T_h = .genesis := by
    obtain ⟨x, K, _, hx, hk, hu⟩ := mixed_age_advance.2.2
    exact ⟨x, K, hx, hk, hu⟩
  obtain ⟨s, X, hnew, hX, ha, hg, hheight⟩ :=
    frontierSearch_age_service_holder core reads obs timing env run iface wire ef
      decodeProposal erase FGBlock.rows (fun _ => [row]) parentFG parentHeight validFor fold hl
      (Finset.Subset.refl _) hne ht hs hf (by decide) rfl gap (by decide : env.t_GST ≤ 0)
      hslot hr ho hsi hparent rfl hb hrec hc fold_premises_sat hq
      hentry hcover hsource hagree hsourceSlot hancestorSlot (by decide : (0 : Time) ≤ 0)
      (by decide) (by decide) hp (by decide) (by decide)
  obtain ⟨hs, hchild⟩ := proposal_unique hnew
  exact ⟨s, X, hs, hchild, hnew, hX, ha, hg, hheight⟩

#print axioms mixed_search_age

private abbrev frozenEnv : Generic.Env (Fin 1) :=
  ⟨1, by decide, 0, by decide, fun _ t => decide (t = 6 ∨ t = 20)⟩
private abbrev frozenRun : V2.D.Run (Fin 1) protocol where
  honest := {0}
  horizon := 38
  events := [.tick 0 6, .tick 0 20]
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

private theorem frozen_source_premises_sat :
    (∀ i, safetyHolder reads frozenRun i = (Equiv.refl (Fin 1)) i) ∧
    PromotionSourceAt core reads frozenEnv frozenRun obs timing iface wire 1 0 1
      .genesis 5 child := by
  refine ⟨fun i => Subsingleton.elim _ _, ?_⟩
  have hp : HonestProposal frozenEnv frozenRun iface 5 (erase child) := by
    refine ⟨⟨by decide, by decide⟩, ⟨.seat 20 0, .inr child⟩,
      ⟨1, by decide +kernel, by decide +kernel⟩, rfl⟩
  refine ⟨⟨rfl, rfl⟩, preceq_refl _, hp, rfl, by decide,
    by decide, by decide, by decide, ?_⟩
  intro x _
  have hx : x = 0 := Subsingleton.elim _ _
  subst x
  refine ⟨0, 0, row, le_rfl, ?_, false, rfl⟩
  unfold HonestRowAt
  decide +kernel

#print axioms frozen_source_premises_sat

private theorem frozen_source_bridges :
    (PromotionSourceAtFG core reads frozenEnv frozenRun obs timing iface wire
      (FGHonestSeats reads frozenRun) 1 0 1 .genesis 5 child ↔
      PromotionSourceAt core reads frozenEnv frozenRun obs timing iface wire
        1 0 1 .genesis 5 child) ∧
    PromotionSourceAtFG core reads frozenEnv frozenRun obs timing iface wire
      (FGHonestSeats reads frozenRun) 1 0 1 .genesis 5 child ∧
    (∀ A, A ⊆ FGHonestSeats reads frozenRun →
      PromotionSourceAt core reads frozenEnv frozenRun obs timing iface wire
        1 0 1 .genesis 5 child →
      PromotionSourceAtFG core reads frozenEnv frozenRun obs timing iface wire
        A 1 0 1 .genesis 5 child) ∧
    (∅ : Finset (Fin 1)) ⊂ FGHonestSeats reads frozenRun := by
  have hb := promotionSourceAtFG_frozen_iff core reads frozenEnv frozenRun obs timing iface
    wire (Equiv.refl _) frozen_source_premises_sat.1 1 0 1 .genesis 5 child
  refine ⟨hb, hb.mpr frozen_source_premises_sat.2, ?_, ?_⟩
  · intro A hA h
    refine ⟨h.entry, h.parentPath, h.proposal, h.slot, h.sync, h.carrier, h.age, h.horizon, ?_⟩
    intro i hi
    exact h.rows _ (Finset.mem_filter.mp (hA hi)).2
  · apply Finset.empty_ssubset.mpr
    exact ⟨0, by simp [FGHonestSeats_def, safetyHolder]⟩

#print axioms frozen_source_bridges
end AvailableChain.FGCompose.Tests.PopulationAge
end
