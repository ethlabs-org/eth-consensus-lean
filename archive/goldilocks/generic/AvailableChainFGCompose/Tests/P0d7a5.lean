module
public import AvailableChainFGCompose.Proofs.Finality.Accept
public import AvailableChainFGCompose.Proofs.Finality.Receipt
public import AvailableChainFGCompose.Statements.HistoricalReads

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.P0d7a5
open AvailableChain.SimplexFG AvailableChain.KitFG

/-! Inhabited interface execution: three checked deliveries and a restart. The store is the
shared window store and every delivery runs `SimplexFG.Window.on_block`. This is an
interface model, not an ExecutionValid FG-SA or PC-SA run. -/

private abbrev aE : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private abbrev aCfg : FGConfig := ⟨4⟩
private abbrev aBoot : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private abbrev aU : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 [aBoot]
private abbrev aTarget : Row (Fin 1) := ⟨0, .vote 2 ⟨1⟩ false, none⟩
private abbrev aD : FGBlock (Fin 1) := .node aU 2 ⟨2⟩ 0 [aTarget]
private abbrev aSigned : Row (Fin 1) := ⟨0, .vote 3 ⟨2⟩ false, some ⟨2, ⟨1⟩⟩⟩
private abbrev aX : FGBlock (Fin 1) := .node aD 6 ⟨6⟩ 0 [aSigned]

private def aErase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node p s r x rs => .node (aErase p) s r (encFGBody x rs)

private abbrev aP : V2.ProtocolSpecD Unit where
  State := SimplexFG.Store (Fin 1)
  Label := Nat
  Duty := Nat
  signLabel := id
  seats _ := 1
  Payload := FGBlock (Fin 1)
  Durable := SimplexFG.Store (Fin 1)
  init := SimplexFG.Store.init
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
  gossip _ _ := []
  process st o := SimplexFG.Window.on_block aE aCfg 2 st o.payload
  selfVisible _ := true
  recordOwn st _ := st
  durable st := st
  restore st _ := st
  wellFormed _ := true
  depsPresent _ _ := true
  processed _ _ := false
  excludes _ _ := false
  handles _ _ _ := False
  carries _ _ := False

private noncomputable abbrev aObj (B : FGBlock (Fin 1)) : aP.Object := ⟨.none, B⟩
private abbrev aEnv : Generic.Env Unit := ⟨1, by decide, 0, le_rfl, fun _ _ => false⟩

/-- Ordered deliveries U, D, X, then a restart. `early` delivers X before its parent. -/
private noncomputable abbrev aRun (early : Bool) : V2.D.Run Unit aP where
  honest := {()}
  horizon := 10
  events := if early then [.deliver () (aObj aX) 1, .deliver () (aObj aU) 2,
      .deliver () (aObj aD) 3, .restart () 4]
    else [.deliver () (aObj aU) 1, .deliver () (aObj aD) 2,
      .deliver () (aObj aX) 3, .restart () 4]
  seatOf _ _ := ()
  input _ _ := ()

private noncomputable abbrev aR : FGCoreReads aP 1 Unit Unit Unit where
  core st := ⟨(), st, [], []⟩
  erase := aErase
  source _ := none
  headVote _ _ := .genesis
  finalityHead _ := none
  proposalFG _ o := some o.payload

/-- The selected receipt: the exact delivered body, admitted by every `on_block` check. -/
private def aReady (early : Bool) (i : Nat) (x : Unit) (W : FGBlock (Fin 1)) (t : Time) :
    Prop :=
  ∃ o, (aRun early).events[i]? = some (.deliver x o t) ∧ o.payload = W ∧
    ¬ (W ∈ (V2.D.Run.stateBefore aEnv (aRun early) i x).TF ∨
      W.parent ∉ (V2.D.Run.stateBefore aEnv (aRun early) i x).TF ∨
      FGBlock.preceq (V2.D.Run.stateBefore aEnv (aRun early) i x).F W = false ∨
      W.slot ≤ W.parent.slot)

private abbrev aS : Finset (FGBlock (Fin 1)) := {.genesis, aU, aD, aX}

private theorem aNonempty : ¬ aE.IsQuorum ∅ := by
  unfold Electorate.IsQuorum
  decide +kernel

private theorem aClosedS : ∀ B ∈ aS, B.parent ∈ aS := by decide

private theorem aRootsS (st : SimplexFG.Store (Fin 1)) (B : FGBlock (Fin 1))
    (hst : st.TF ⊆ aS) (hB : B ∈ aS) : StoreStepRoots st B := by
  have hsub : insert B st.TF ⊆ aS := Finset.insert_subset hB hst
  intro X Y ⟨W, hW, hXW⟩ ⟨W', hW', hYW'⟩ hr
  have hX := KitFG.ancestor_closed_of_parent_closed aS aClosedS W (hsub hW) X hXW
  have hY := KitFG.ancestor_closed_of_parent_closed aS aClosedS W' (hsub hW') Y hYW'
  exact (by decide : ∀ X ∈ aS, ∀ Y ∈ aS, X.root = Y.root → X = Y) X hX Y hY hr

private theorem aEvents (early : Bool) (i : Nat) (e : V2.Event Unit aP.Object)
    (he : (aRun early).events[i]? = some e) :
    (∃ v o t, e = .deliver v o t ∧ o.payload ∈ aS) ∨ ∃ v t, e = .restart v t := by
  have hm := List.mem_of_getElem? he
  cases early <;> simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons,
    List.not_mem_nil, or_false] at hm <;>
    rcases hm with rfl | rfl | rfl | rfl <;>
    first
    | exact Or.inr ⟨_, _, rfl⟩
    | exact Or.inl ⟨_, _, _, rfl, by decide⟩

private theorem aOnBlockTF (st : SimplexFG.Store (Fin 1)) (B : FGBlock (Fin 1)) :
    (SimplexFG.Window.on_block aE aCfg 2 st B).TF ⊆ insert B st.TF := by
  by_cases hc : B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot
  · rw [KitFG.Window.window_on_block_of_refused aE aCfg 2 st B hc]
    exact Finset.subset_insert _ _
  · rw [KitFG.Window.window_on_block_of_accepted aE aCfg 2 st B hc,
      KitFG.Window.window_update_finality_TF]

/-- Every reachable store has the window invariant and stays inside the four blocks. -/
private theorem aReach (early : Bool) (i : Nat) (x : Unit) :
    FGStoreInvariant (KitFG.Window.certificateHeight aE aCfg 2)
      (KitFG.Window.certificateFinality aE aCfg 2)
      (V2.D.Run.stateBefore aEnv (aRun early) i x) ∧
    (V2.D.Run.stateBefore aEnv (aRun early) i x).TF ⊆ aS := by
  induction i with
  | zero =>
    refine ⟨KitFG.Window.windowStoreInvariant_init aE aCfg 2, ?_⟩
    change ({.genesis} : Finset (FGBlock (Fin 1))) ⊆ aS
    decide
  | succ i ih =>
    cases he : (aRun early).events[i]? with
    | none =>
      have hlen : (aRun early).events.length ≤ i := by
        by_contra hn
        exact absurd (List.getElem?_eq_getElem (Nat.lt_of_not_ge hn)) (by rw [he]; simp)
      have hs : V2.D.Run.stateBefore aEnv (aRun early) (i + 1) =
          V2.D.Run.stateBefore aEnv (aRun early) i := by
        unfold V2.D.Run.stateBefore
        rw [List.take_of_length_le (by omega), List.take_of_length_le hlen]
      rw [hs]
      exact ih
    | some e =>
      rw [V2.D.Run.stateBefore_succ aEnv (aRun early) he]
      rcases aEvents early i e he with ⟨v, o, t, rfl, ho⟩ | ⟨v, t, rfl⟩
      · cases v
        cases x
        simp only [V2.D.World.step, Function.update_self]
        refine ⟨KitFG.Window.windowStoreInvariant_on_block aE aCfg 2 aNonempty (by decide) _ _
          ih.1 (aRootsS _ _ ih.2 ho), ?_⟩
        intro B hB
        rcases Finset.mem_insert.mp (aOnBlockTF _ _ hB) with h | h
        · exact h ▸ ho
        · exact ih.2 h
      · cases v
        cases x
        simp only [V2.D.World.step, Function.update_self]
        exact ih

private noncomputable abbrev aO : FGObservationReads aR where
  height := KitFG.Window.certificateHeight aE aCfg 2
  finality := KitFG.Window.certificateFinality aE aCfg 2
  controls _ := ⟨.genesis, 0, 0, .genesis, false⟩
  viable _ X := X

/-- The produced selected-step equation: the checked delivery runs `on_block`. -/
private theorem aStep (early : Bool) :
    AcceptStep_W aR aEnv (aRun early) aE aCfg 2 (aReady early) := by
  intro i x W t _hx ⟨o, he, ho, hc⟩
  have hreach := aReach early i x
  refine ⟨?_, ?_⟩
  · rw [V2.D.Run.stateBefore_succ aEnv (aRun early) he]
    cases x
    simp only [V2.D.World.step, Function.update_self]
    change SimplexFG.Window.on_block aE aCfg 2 _ o.payload = _
    rw [ho]
    exact KitFG.Window.window_on_block_of_accepted aE aCfg 2 _ W hc
  · have hpar : W.parent ∈ (V2.D.Run.stateBefore aEnv (aRun early) i x).TF := by
      simp only [not_or, not_not] at hc
      exact hc.2.1
    have hclosed : ∀ B ∈ insert W (V2.D.Run.stateBefore aEnv (aRun early) i x).TF,
        B.parent ∈ insert W (V2.D.Run.stateBefore aEnv (aRun early) i x).TF := by
      intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hB
      · exact Finset.mem_insert_of_mem hpar
      · exact Finset.mem_insert_of_mem (hreach.1.closed B hB)
    have L := KitFG.Window.windowCertificateLaws aE aCfg 2 aNonempty (by decide)
    have hFW : FGBlock.Preceq (SimplexFG.Window.derive aE aCfg 2 W).F W :=
      KitFG.preceq_trans (L.finalized_preceq_justified W)
        (KitFG.preceq_trans (L.height.justified_preceq_entry W) (L.height.entry_preceq W))
    exact KitFG.ancestor_closed_of_parent_closed _ hclosed W (Finset.mem_insert_self _ _) _ hFW

private theorem aDurable : FGFinalityDurableLaws aR :=
  ⟨fun _ => ⟨fun _ _ h => h, fun st o h => KitFG.preceq_trans h
    (KitFG.Window.window_on_block_F_mono aE aCfg 2 st o.payload), fun _ _ h => h⟩,
    fun _ _ => rfl⟩

private theorem aSchedule (early : Bool) : V2.D.ScheduleWellFormed aEnv (aRun early) := by
  refine ⟨by cases early <;> decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases early <;> decide
  · cases early <;> decide
  · cases early <;> decide
  · cases early <;> decide
  · intro v t h
    cases early <;> simp at h
  · intro v _ t _ _ _ ha
    cases ha

/-- The carrier's window finalizes U (the shared fold, computed). -/
private theorem aFinal : (SimplexFG.Window.derive aE aCfg 2 aX).F = aU := by decide +kernel

private theorem aReady2 : aReady false 2 () aX 3 :=
  ⟨aObj aX, rfl, rfl, by decide +kernel⟩

/-- The selected receipt at index 2 (time 3), strictly before the deadline 4. -/
private def aDelivery : BlockDelivery_W aR aEnv (aRun false) (aReady false) aX aU 0 4 where
  selected _ _ := ⟨2, 3⟩
  witness x _ := by
    cases x
    exact ⟨rfl, by decide, Or.inr ⟨by decide, aReady2⟩⟩

private theorem aStored2 : (V2.D.Run.stateBefore aEnv (aRun false) 2 ()).J = aU ∧
    (V2.D.Run.stateBefore aEnv (aRun false) 2 ()).F = .genesis := by decide +kernel

private theorem aGuards :
    AcceptGuards_W aR aEnv (aRun false) aE aCfg 2 (aReady false) aX aU 0 4 aDelivery where
  finCmp x hx := by
    cases x
    dsimp only
    intro _
    exact receipt_finCmp_of_block aR aEnv (aRun false) aE aCfg 2 aNonempty (by decide) aO rfl
      (· ∈ aS) (fun C W hC hW => (by decide +kernel : ∀ C ∈ aS, ∀ W ∈ aS,
        FGBlock.compatible (KitFG.Window.certificateFinality aE aCfg 2 C).F
          (KitFG.Window.certificateFinality aE aCfg 2 W).F = true) C hC W hW)
      2 () (aReach false 2 ()).1
      (fun C hC _ => (aReach false 2 ()).2 hC) aX aU (by rw [aFinal]; exact preceq_refl _)
      (by decide)
  jPath x hx := by
    cases x
    dsimp only
    intro _ _
    exact receipt_jPath_of_cached_anchor aR aEnv (aRun false) aE aCfg 2 2 () aX aU
      aStored2.1 (by decide)
  cap x hx := by
    cases x
    dsimp only
    intro _ _
    exact (by decide +kernel : (receiptInsert_W aR aEnv (aRun false) aE aCfg 2 2 () aX).h_max ≤
      (SimplexFG.Window.derive aE aCfg 2 aX).h + 1)

private def aPrem : AcceptPrem_W aR aEnv (aRun false) aE aCfg 2 (aReady false) aX aU 0 4 where
  schedule := aSchedule false
  finalized := by rw [aFinal]; exact preceq_refl _
  deliver := aDelivery
  guards := aGuards
  horizon := by decide

/-- POSITIVE: the selected receipt is accepted strictly before the deadline. -/
private theorem aAccepted : AcceptsFinalBefore aR aEnv (aRun false) () aU 4 :=
  acceptBefore_W aR aEnv (aRun false) aE aCfg 2 aNonempty (by decide) aDurable
    (aReady false) (aStep false) (fun i x _ => (aReach false i x).1) aX aU 0 4 aPrem ()
    (Finset.mem_singleton_self _)

/-- The returned acceptance is the actual store finality before time 4. -/
private theorem aAcceptedInspected :
    (V2.D.Run.stateBeforeTime aEnv (aRun false) 4 ()).F = aU ∧
      FGBlock.Preceq aU (V2.D.Run.stateBeforeTime aEnv (aRun false) 4 ()).F :=
  ⟨by decide +kernel, aAccepted⟩

/-- Restart keeps durable finality and the historical parent of the accepted carrier. -/
private theorem aAfterRestart :
    AcceptsFinalBefore aR aEnv (aRun false) () aU 10 ∧
      aX ∈ (V2.D.Run.stateBeforeTime aEnv (aRun false) 10 ()).TF ∧
      aX.parent ∈ (V2.D.Run.stateBeforeTime aEnv (aRun false) 10 ()).TF :=
  ⟨finality_acceptsFinalBefore_mono_deadline aR aEnv (aRun false) aDurable (aSchedule false)
    (by decide) aAccepted, by decide +kernel, by decide +kernel⟩

/-- The accepted descendant also accepts its ancestor D's parent chain (here U's parent). -/
private theorem aAncestor : AcceptsFinalBefore aR aEnv (aRun false) () .genesis 10 :=
  finality_acceptsFinalBefore_mono_ancestor aR aEnv (aRun false) aDurable (aSchedule false)
    (KitFG.genesis_preceq aU) (by decide) aAccepted

/-- Restore keeps the finalized ancestry of the accepted store. -/
private theorem aRestore :
    FGBlock.Preceq aU (aR.core (aP.restore (aP.durable
      (V2.D.Run.stateBefore aEnv (aRun false) 3 ())) 4)).fg.F :=
  finality_restore_preceq_F aR aDurable aU _ 4 (by decide +kernel)

/-- The c4 lookup domain: the accepted tree read from the actual execution. -/
private abbrev aBodies : List (FGBlock (Fin 1)) := [.genesis, aU, aD, aX]

/-- The actual cumulative domain equals the lookup list after the receipt and after restart. -/
private theorem aDomainActual :
    (V2.D.Run.stateBefore aEnv (aRun false) 3 ()).TF = aBodies.toFinset ∧
      (V2.D.Run.stateBefore aEnv (aRun false) 4 ()).TF = aBodies.toFinset := by
  decide +kernel

/-- Exact root/body association on that domain, also when an active frame drops X. -/
private theorem aHistorical :
    historicalLookup FGBlock.root aBodies aX.root = some aX ∧
      aX.rows = [aSigned] ∧ aX.slot = 6 ∧
      historicalLookup FGBlock.root aBodies aX.parent.root = some aD ∧
      aX ∉ aBodies.filter (fun B => decide (B.slot < 6)) ∧
      historicalLookup FGBlock.root aBodies ⟨99⟩ = none := by
  decide +kernel

/-- A malformed domain with distinct full content at X's root resolves nothing. -/
private abbrev aXAlias : FGBlock (Fin 1) := .node aD 6 ⟨6⟩ 0 []

private theorem aAmbiguous :
    aXAlias ≠ aX ∧ aXAlias.root = aX.root ∧
      historicalLookup FGBlock.root (aBodies ++ [aXAlias]) aX.root = none := by
  decide +kernel

/-! Receiver floor and F guard. The receiver's own clock sets the slot floor (the FG-SA
admission `slot ≤ receiver slot`); a tick is the only clock source. Both variants have the
same receiver, bodies, delivery events and times; they differ only in the earlier tick. -/

private abbrev aZ : FGBlock (Fin 1) := .node .genesis 7 ⟨7⟩ 0 []

private abbrev aQ : V2.ProtocolSpecD Unit where
  State := SimplexFG.Store (Fin 1) × Time
  Label := Nat
  Duty := Nat
  signLabel := id
  seats _ := 1
  Payload := FGBlock (Fin 1)
  Durable := SimplexFG.Store (Fin 1)
  init := (SimplexFG.Store.init, 0)
  clock st t := (st.1, t)
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
  gossip _ _ := []
  process st o := if (o.payload.slot : Time) ≤ st.2 then
      (SimplexFG.Window.on_block aE aCfg 2 st.1 o.payload, st.2) else st
  selfVisible _ := true
  recordOwn st _ := st
  durable st := st.1
  restore st t := (st, t)
  wellFormed _ := true
  depsPresent _ _ := true
  processed _ _ := false
  excludes _ _ := false
  handles _ _ _ := False
  carries _ _ := False

private noncomputable abbrev qObj (B : FGBlock (Fin 1)) : aQ.Object := ⟨.none, B⟩

/-- `late`: the receiver ticks at 10 (floor 10); otherwise at 2 (floor 2). -/
private noncomputable abbrev qRun (late : Bool) : V2.D.Run Unit aQ where
  honest := {()}
  horizon := 20
  events := [.tick () (if late then 10 else 2), .deliver () (qObj aU) 11,
    .deliver () (qObj aD) 12, .deliver () (qObj aX) 13, .deliver () (qObj aZ) 14]
  seatOf _ _ := ()
  input _ _ := ()

/-- The receipt check at the receiver: the exact delivered body, every store admission
check, and the receiver's slot floor. -/
private def qReady (late : Bool) (i : Nat) (x : Unit) (W : FGBlock (Fin 1)) (t : Time) : Prop :=
  ∃ o, (qRun late).events[i]? = some (.deliver x o t) ∧ o.payload = W ∧
    ¬ (W ∈ (V2.D.Run.stateBefore aEnv (qRun late) i x).1.TF ∨
      W.parent ∉ (V2.D.Run.stateBefore aEnv (qRun late) i x).1.TF ∨
      FGBlock.preceq (V2.D.Run.stateBefore aEnv (qRun late) i x).1.F W = false ∨
      W.slot ≤ W.parent.slot) ∧
    (W.slot : Time) ≤ (V2.D.Run.stateBefore aEnv (qRun late) i x).2

private theorem qSchedule (late : Bool) : V2.D.ScheduleWellFormed aEnv (qRun late) := by
  refine ⟨by cases late <;> decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases late <;> decide
  · cases late <;> decide
  · cases late <;> decide
  · cases late <;> decide
  · intro v t h
    cases late <;> simp at h <;> obtain ⟨_, rfl⟩ := h
    · exact ⟨2, by decide⟩
    · exact ⟨10, by decide⟩
  · intro v _ t _ _ _ ha
    cases ha

/-- POSITIVE floor: the same delivery of X (index 3, time 13) is ready and accepted. -/
private theorem qFloorAccepted : qReady true 3 () aX 13 ∧
    aX ∈ (V2.D.Run.stateBefore aEnv (qRun true) 4 ()).1.TF ∧
    (V2.D.Run.stateBefore aEnv (qRun true) 4 ()).1.F = aU :=
  ⟨⟨qObj aX, rfl, rfl, by decide +kernel, by decide +kernel⟩, by decide +kernel,
    by decide +kernel⟩

/-- NEGATIVE floor: the same event passes every store check (parent held, fresh, F below,
slot order) and fails only the receiver floor; X is not accepted and F stays genesis. -/
private theorem qFloorRefused :
    ¬ ((aX ∈ (V2.D.Run.stateBefore aEnv (qRun false) 3 ()).1.TF ∨
      aX.parent ∉ (V2.D.Run.stateBefore aEnv (qRun false) 3 ()).1.TF ∨
      FGBlock.preceq (V2.D.Run.stateBefore aEnv (qRun false) 3 ()).1.F aX = false ∨
      aX.slot ≤ aX.parent.slot)) ∧
    ¬ ((aX.slot : Time) ≤ (V2.D.Run.stateBefore aEnv (qRun false) 3 ()).2) ∧
    ¬ qReady false 3 () aX 13 ∧
    aX ∉ (V2.D.Run.stateBefore aEnv (qRun false) 4 ()).1.TF ∧
    (V2.D.Run.stateBefore aEnv (qRun false) 5 ()).1.F = .genesis := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩
  rintro ⟨o, he, ho, _, hf⟩
  cases he
  exact absurd hf (by decide +kernel)

/-- NEGATIVE F guard: after non-genesis finality U, a delivery of Z conflicting with U has
its parent held, is fresh, ordered and within the floor, and fails only `F ⪯ Z`; it is
refused and F stays U. -/
private theorem qFGuardRefused :
    (V2.D.Run.stateBefore aEnv (qRun true) 4 ()).1.F = aU ∧ aU ≠ .genesis ∧
    aZ ∉ (V2.D.Run.stateBefore aEnv (qRun true) 4 ()).1.TF ∧
    aZ.parent ∈ (V2.D.Run.stateBefore aEnv (qRun true) 4 ()).1.TF ∧
    aZ.parent.slot < aZ.slot ∧
    (aZ.slot : Time) ≤ (V2.D.Run.stateBefore aEnv (qRun true) 4 ()).2 ∧
    FGBlock.preceq (V2.D.Run.stateBefore aEnv (qRun true) 4 ()).1.F aZ = false ∧
    ¬ qReady true 4 () aZ 14 ∧
    aZ ∉ (V2.D.Run.stateBefore aEnv (qRun true) 5 ()).1.TF ∧
    (V2.D.Run.stateBefore aEnv (qRun true) 5 ()).1.F = aU := by
  refine ⟨by decide +kernel, by decide, by decide +kernel, by decide +kernel, by decide,
    by decide +kernel, by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩
  rintro ⟨o, he, ho, hc, _⟩
  cases he
  exact hc (Or.inr (Or.inr (Or.inl (by decide +kernel))))

/-- The index read used by acceptance, instantiated directly (events 0-2 before time 4). -/
private theorem aIdx : AcceptsFinalBefore aR aEnv (aRun false) () aU 4 :=
  finality_acceptsFinalBefore_of_idx aR aEnv (aRun false) aDurable (aSchedule false)
    ⟨3, by decide, by decide +kernel, by decide +kernel⟩

/-- Prior coverage: a receiver whose selected event is after acceptance (the restart). -/
private theorem aNotReady3 (W : FGBlock (Fin 1)) (t : Time) : ¬ aReady false 3 () W t := by
  rintro ⟨o, he, _⟩
  cases he

private def aCovered : BlockDelivery_W aR aEnv (aRun false) (aReady false) aX aU 0 5 where
  selected _ _ := ⟨3, 4⟩
  witness x _ := by
    cases x
    exact ⟨rfl, by decide, Or.inl (by decide +kernel)⟩

private theorem aCoveredAccepted : AcceptsFinalBefore aR aEnv (aRun false) () aU 5 :=
  acceptBefore_W aR aEnv (aRun false) aE aCfg 2 aNonempty (by decide) aDurable
    (aReady false) (aStep false) (fun i x _ => (aReach false i x).1) aX aU 0 5
    { schedule := aSchedule false
      finalized := by rw [aFinal]; exact preceq_refl _
      deliver := aCovered
      guards := { finCmp := fun x _ hr => by cases x; exact absurd hr (aNotReady3 _ _)
                  jPath := fun x _ hr => by cases x; exact absurd hr (aNotReady3 _ _)
                  cap := fun x _ hr => by cases x; exact absurd hr (aNotReady3 _ _) }
      horizon := by decide } ()
    (Finset.mem_singleton_self _)

/-- POSITIVE: the pending pair, consumed by the window fold, with the same receipt. -/
private theorem aFold : PendingFold_W aE aCfg 2 2 aU aX :=
  ⟨by decide, ⟨2, aU, ∅⟩, by decide +kernel, rfl, rfl, {0},
    by unfold Electorate.IsQuorum; decide +kernel,
    fun i _ => Or.inr ⟨aSigned, by decide, Subsingleton.elim _ _, rfl⟩⟩

private theorem aFinalized : AcceptsFinalBefore aR aEnv (aRun false) () aU 4 :=
  finalizePending_W aR aEnv (aRun false) aE aCfg 2 aNonempty (by decide) aDurable
    (aReady false) (aStep false) (fun i x _ => (aReach false i x).1) 2 aU aX 0 4
    ⟨aFold, aSchedule false, aDelivery, aGuards, by decide⟩ () (Finset.mem_singleton_self _)

/-- NEGATIVE (strict deadline): the receipt time itself is not before the receipt. -/
private theorem aStrict : ¬ AcceptsFinalBefore aR aEnv (aRun false) () aU 3 := by
  intro h
  have hF : (V2.D.Run.stateBeforeTime aEnv (aRun false) 3 ()).F = .genesis := by decide +kernel
  change FGBlock.Preceq aU (V2.D.Run.stateBeforeTime aEnv (aRun false) 3 ()).F at h
  rw [hF] at h
  exact absurd h (by decide)

/-- NEGATIVE (parent guard): a carrier delivered before its parent is not ready, and its
receiver never accepts U. -/
private theorem aEarlyRefused : ¬ aReady true 0 () aX 1 ∧
    ¬ AcceptsFinalBefore aR aEnv (aRun true) () aU 10 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨o, he, ho, hc⟩
    cases he
    exact hc (by decide +kernel)
  · intro h
    have hF : (V2.D.Run.stateBeforeTime aEnv (aRun true) 10 ()).F = .genesis := by
      decide +kernel
    change FGBlock.Preceq aU (V2.D.Run.stateBeforeTime aEnv (aRun true) 10 ()).F at h
    rw [hF] at h
    exact absurd h (by decide)

#print axioms aStep
#print axioms aReach
#print axioms aDurable
#print axioms aAccepted
#print axioms aAcceptedInspected
#print axioms aAfterRestart
#print axioms aDomainActual
#print axioms aHistorical
#print axioms aAmbiguous
#print axioms qSchedule
#print axioms qFloorAccepted
#print axioms qFloorRefused
#print axioms qFGuardRefused
#print axioms aIdx
#print axioms aAncestor
#print axioms aRestore
#print axioms aCoveredAccepted
#print axioms aFinalized
#print axioms aStrict
#print axioms aEarlyRefused

end AvailableChain.FGCompose.Tests.P0d7a5
end
