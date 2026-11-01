module
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchFull
public import AvailableChainFGCompose.Proofs.Finality.History -- shake: keep (window views)

set_option linter.privateModule false

public section
noncomputable section
namespace AvailableChain.FGCompose.Tests.P0d5db
open AvailableChain.SimplexFG AvailableChain.KitFG

/-! G0 for P0d5d-b (tasks and full search). Model level: `lad*` is a generic event-fold
interface model (not an ExecutionValid run). The `v5*`/`v9*` helpers are renamed copies
of the accepted P0d5c test helpers (private there).

Model `lad` ("ladder"): Δ = ΔF = 1, R = 2, G = 4, GST = 0, Jst = 12, one lease slot,
horizon 168. One honest node ticks at every time 0..168. It proposes the labelled
block x_s = node genesis s (no rows) for every slot s = 1..42 at time 4s; x_1, x_2 and x_3
are delivered right after their ticks. At every action r = 0..20 (time 8r + 6) it signs one row
whose entry has height r + 1. A progress-certified chain p_1..p_20 (heights 2..21, no
justification) is delivered at times 8k + 5 (k = 1..20), so the honest frontier rises once
per action period, after the honest row of the old frontier height. Every phase lasts at
most six time units: no seed is saved, each rise is the next delivery, and each first row
comes through RCap. -/

private def v5T : FGTiming where
  delta := 1
  roundSlots := 2
  proposal s := 4 * (s : Time)
  vote s := 4 * (s : Time) + 1
  early s := 4 * (s : Time) + 2
  freeze s := 4 * (s : Time) + 3
  release s := 4 * (s : Time) + 5
  gate s := 4 * (s : Time) + 6
  action r := 8 * (r : Time) + 6
private theorem v5TLaws : FGTimingLaws v5T where
  delta_pos := by decide
  rounds := by decide
  proposal_eq s := by simp [v5T]
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq r := by simp [v5T]; ring

private def v5erase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node p s r x rs => .node (v5erase p) s r (encFGBody x rs)

private theorem v5erase_inj : Function.Injective v5erase := by
  intro A
  induction A with
  | genesis => intro B h; cases B <;> simp_all [v5erase]
  | node p s r x rs ih =>
    intro B h
    cases B with
    | genesis => simp [v5erase] at h
    | node q t u y ts =>
      simp only [v5erase, Block.node.injEq] at h
      obtain ⟨hp, hs, hr, hb⟩ := h
      obtain ⟨hx, hrows⟩ := encFGBody_inj hb
      cases ih hp
      cases hs
      cases hr
      cases hx
      cases hrows
      rfl

private theorem v5erase_mono {A B : FGBlock (Fin 1)} (h : FGBlock.Preceq A B) :
    Block.Preceq (v5erase A) (v5erase B) := by
  induction B with
  | genesis =>
    rw [(preceq_genesis).mp h]
    rfl
  | node P s r x rs ih =>
    change (decide (A = .node P s r x rs) || FGBlock.preceq A P) = true at h
    change (decide (v5erase A = v5erase (.node P s r x rs)) ||
      Block.preceq (v5erase A) (v5erase P)) = true
    rw [Bool.or_eq_true] at h ⊢
    rcases h with he | hp
    · exact Or.inl (decide_eq_true (congrArg v5erase (of_decide_eq_true he)))
    · exact Or.inr (ih hp)

private def v5E : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private def v5cfg : FGConfig := ⟨4⟩
private abbrev v5H := KitFG.Window.certificateHeight v5E v5cfg 2
private abbrev v5F := KitFG.Window.certificateFinality v5E v5cfg 2


private abbrev v5env : Generic.Env Unit := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩

private theorem v5cert : FGCertificateLaws v5E v5H v5F :=
  KitFG.Window.windowCertificateLaws v5E v5cfg 2
    (by unfold Electorate.IsQuorum; decide +kernel) (by decide)

private theorem v5justif : FGJustificationLaws v5H :=
  FGJustificationLaws.of_bridge (KitFG.Window.windowHeightBridge v5E v5cfg 2 (by decide))

private theorem v9erase_reflect (A B : FGBlock (Fin 1))
    (h : Block.Preceq (v5erase A) (v5erase B)) : FGBlock.Preceq A B := by
  induction B with
  | genesis =>
    have he : v5erase A = v5erase .genesis := of_decide_eq_true h
    exact v5erase_inj he ▸ preceq_refl _
  | node P slot root app rows ih =>
    change (decide (v5erase A = v5erase (.node P slot root app rows)) ||
      Block.preceq (v5erase A) (v5erase P)) = true at h
    rw [Bool.or_eq_true] at h
    rcases h with he | hp
    · exact v5erase_inj (of_decide_eq_true he) ▸ preceq_refl _
    · exact preceq_node_of_preceq slot root app rows (ih hp)

private theorem v9erase_parent (X : FGBlock (Fin 1)) :
    (v5erase X).parent = v5erase X.parent := by
  cases X <;> rfl

/-- Slots increase along every parent edge of a block. -/
private def v9slotsOK : FGBlock (Fin 1) → Bool
  | .genesis => true
  | .node P s _ _ _ => decide (P.slot ≤ s) && v9slotsOK P

private theorem v9anc_slot {A K : FGBlock (Fin 1)} (hK : v9slotsOK K = true)
    (h : FGBlock.Preceq A K) : A.slot ≤ K.slot := by
  induction K with
  | genesis => rw [(preceq_genesis).mp h]
  | node P s r x rs ih =>
    change (decide (P.slot ≤ s) && v9slotsOK P) = true at hK
    rw [Bool.and_eq_true] at hK
    change (decide (A = .node P s r x rs) || FGBlock.preceq A P) = true at h
    rw [Bool.or_eq_true] at h
    rcases h with he | hp
    · rw [of_decide_eq_true he]
    · exact (ih hK.2 hp).trans (of_decide_eq_true hK.1)

private theorem v9transition_progress (σ : ChainState (Fin 1)) (B : FGBlock (Fin 1))
    (rs : List (Row (Fin 1))) (S : Finset (Fin 1)) (hS : v5E.IsQuorum S)
    (hcover : ∀ i ∈ S, i ∈ σ.progress ∨
      ∃ a ∈ rs, a.signer = i ∧ a.height_pair.matchesEntry σ.h σ.T_h.root = true)
    (hmature : σ.T_h.slot + v5cfg.timeoutDelay ≤ B.slot) :
    (transition v5E v5cfg σ B rs).h = σ.h + 1 := by
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
  have hq : v5E.IsQuorum (foldRows σ B rs).progress :=
    isQuorum_of_subset v5E hS (fun i hi => hfold rs { σ with s := B.slot } i (hcover i hi))
  have hp : progReady v5E v5cfg (afterFin v5E (foldRows σ B rs)) = true := by
    simp only [progReady, Bool.or_eq_true, Bool.and_eq_true]
    right
    constructor
    · simpa only [afterFin_T_h, afterFin_s, (foldRows_fields σ B rs).2.2.1,
        foldRows_s, decide_eq_true_eq] using hmature
    · change decide (v5E.q ≤ v5E.weightOf (afterFin v5E (foldRows σ B rs)).progress) = true
      rw [decide_eq_true_eq, afterFin_progress]
      exact hq
  change (process_height_events v5E v5cfg (foldRows σ B rs)).h = σ.h + 1
  rw [process_height_events_eq]
  have hh := (afterFin_h v5E (foldRows σ B rs)).trans (foldRows_fields σ B rs).2.1
  split_ifs with ht
  · exact congrArg (· + 1) hh
  · exact congrArg (· + 1) hh

/-- The bridge form of `v9transition_progress` for the window view. -/
private theorem v9progress_of_cover (hb : HeightBridge v5E v5cfg v5H)
    (p : FGBlock (Fin 1)) (s : Slot) (r_s : BlockId) (x : Nat)
    (rs : List (Row (Fin 1))) (S : Finset (Fin 1)) (hS : v5E.IsQuorum S)
    (hcover : ∀ i ∈ S, i ∈ (v5H p).progress ∨
      ∃ a ∈ rs, a.signer = i ∧
        a.height_pair.matchesEntry (v5H p).h (v5H p).T_h.root = true)
    (hmature : (v5H p).T_h.slot + v5cfg.timeoutDelay ≤ s) :
    (v5H (.node p s r_s x rs)).h = (v5H p).h + 1 := by
  have heq : ∀ B, v5H B = heightOf (derive v5E v5cfg B) := hb
  simp only [heq, heightOf_def] at hcover hmature ⊢
  exact v9transition_progress (derive v5E v5cfg p) (.node p s r_s x rs) rs S hS hcover hmature

private theorem v9foldAdvance : ProgressFoldAdvance v5E v5H 4 := by
  intro y U X hX hU hUX hc hm
  have hb := KitFG.Window.windowHeightBridge v5E v5cfg 2 (by decide)
  have laws := heightLaws_of_bridge v5E v5cfg _ hb
  have hlow := laws.h_mono hUX
  change (v5H U).h ≤ (v5H X.parent).h at hlow
  rw [hU.1] at hlow
  cases X with
  | genesis => exact (hX rfl).elim
  | node P s root x rs =>
    change y ≤ (v5H P).h at hlow
    by_cases hP : (v5H P).h = y
    · have hT : (v5H P).T_h = U :=
        (laws.entry_plateau hUX (hU.1.trans hP.symm)).symm.trans hU.2
      obtain ⟨S, hS, hcov⟩ := hc hP
      have hh := v9progress_of_cover hb P s root x rs S hS (by
          intro i hi
          rcases hcov i hi with hbit | ⟨a, ha, hs, timeout, hp⟩
          · exact Or.inl hbit
          · refine Or.inr ⟨a, ha, hs, ?_⟩
            rw [hp]
            change decide (y = (v5H P).h ∧ U.root = (v5H P).T_h.root) = true
            simp only [hP, hT, and_self, decide_true]) (by
          change (v5H P).T_h.slot + 4 ≤ s
          rw [hT]
          exact hm)
      change (v5H (.node P s root x rs)).h = (v5H P).h + 1 at hh
      rw [hh, hP]
    · have hPX := laws.h_mono (preceq_parent_node P s root x rs)
      change (v5H P).h ≤ (v5H (.node P s root x rs)).h at hPX
      simp only [Height] at *
      omega

private theorem v9idxBefore_mono {V : Type} {P : V2.ProtocolSpecD Unit} (rho : V2.D.Run V P)
    {a b : Time} (h : a ≤ b) : V2.D.Run.idxBefore rho a ≤ V2.D.Run.idxBefore rho b := by
  change (rho.events.filter (fun e => decide (e.time < a))).length ≤
    (rho.events.filter (fun e => decide (e.time < b))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left fun e _ he =>
    decide_eq_true ((of_decide_eq_true he).trans_le h)

private theorem v9idxBefore_le_timeIdx {V : Type} {P : V2.ProtocolSpecD Unit}
    (rho : V2.D.Run V P) (a : Time) : V2.D.Run.idxBefore rho a ≤ timeIdx rho a := by
  change (rho.events.filter (fun e => decide (e.time < a))).length ≤
    (rho.events.filter (fun e => decide (e.time ≤ a))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left fun e _ he => decide_eq_true (of_decide_eq_true he).le

private theorem v9timeIdx_mono {V : Type} {P : V2.ProtocolSpecD Unit} (rho : V2.D.Run V P)
    {a b : Time} (h : a ≤ b) : timeIdx rho a ≤ timeIdx rho b := by
  change (rho.events.filter (fun e => decide (e.time ≤ a))).length ≤
    (rho.events.filter (fun e => decide (e.time ≤ b))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left fun e _ he =>
    decide_eq_true ((of_decide_eq_true he).trans h)

private def ladX (s : Nat) : FGBlock (Fin 1) := .node .genesis s ⟨20 + s⟩ 0 []
private def ladtv (h : Nat) (e : BlockId) : Row (Fin 1) := ⟨0, .vote h e true, none⟩
private def ladp : Nat → FGBlock (Fin 1)
  | 0 => .genesis
  | k + 1 => .node (ladp k) (4 * (k + 1)) ⟨300 + k + 1⟩ 0 [ladtv (k + 1) (ladp k).root]
/-- The honest row of action r: height r + 1, a root that names no stored block. -/
private def ladrow (r : Nat) : Row (Fin 1) := ⟨0, .vote (r + 1) ⟨900 + r⟩ false, none⟩
private def ladrowIdx (a : Row (Fin 1)) : Nat :=
  match a.height_pair with | .vote h _ _ => h - 1 | .empty => 0
private def ladAllRows : List (Row (Fin 1)) := (List.range 21).map ladrow

/-- Delivered blocks, in delivery order. -/
private def ladblocks : List (FGBlock (Fin 1)) :=
  [ladX 1, ladX 2, ladX 3] ++ (List.range 20).map (fun k => ladp (k + 1))

private abbrev ladP : V2.ProtocolSpecD Unit where
  State := Nat
  Label := Nat
  Duty := Nat
  signLabel := id
  seats _ := 1
  Payload := Row (Fin 1) ⊕ Block
  Durable := Nat
  init := 0
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
  act _ d _ := if d % 8 = 6 ∧ d ≤ 168 then some (.inl (ladrow (d / 8)))
    else if d % 4 = 0 ∧ 4 ≤ d ∧ d ≤ 168 then some (.inr (v5erase (ladX (d / 4)))) else none
  gossip _ _ := []
  process st _ := st + 1
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

private abbrev ladTF (k : Nat) : Finset (FGBlock (Fin 1)) :=
  insert .genesis (ladblocks.take k).toFinset
private abbrev ladhmax (k : Nat) : Nat := if k ≤ 3 then 1 else min k 23 - 2
/-- A block that attains the frontier of a store count. -/
private abbrev ladtop (k : Nat) : FGBlock (Fin 1) := ladp (min k 23 - 3)

private abbrev ladR : FGCoreReads ladP 1 Unit Unit (Row (Fin 1)) where
  core st := ⟨(), ⟨ladTF st, .genesis, .genesis, 0, ladhmax st⟩, [], ladAllRows⟩
  erase := v5erase
  source _ := none
  headVote _ _ := .genesis
  finalityHead _ := none
  proposalFG _ _ := none

private abbrev ladO : FGObservationReads ladR where
  height := v5H
  finality := v5F
  controls nd := treeStoreControlsView v5H (ladR.core nd).fg
  viable nd X := treeStoreFrameView v5H (ladR.core nd).fg X

private theorem ladobs : FGObservationLaws ladR ladO := ⟨fun _ => rfl, fun _ _ => rfl⟩

private noncomputable abbrev ladS : FGSafetyReads ladP 1 (Row (Fin 1)) where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode a := ⟨.seat (8 * ladrowIdx a + 6) 0, .inl a⟩
  decode := some
  decodeObject o := match o.payload with | .inl a => some a | .inr _ => none
  fgLabel := 6
  fgSeats := Equiv.refl _
  record := fun _ => RecordOnce.initial
  inputs := fun _ => (none, ⟨0, ⟨0⟩, 0⟩)
  enabled := fun _ => false
  finalizedOut := fun _ => .genesis

private def ladD : FGHistoryWireReads ladS where
  heightPair := Row.height_pair
  finalityPair := Row.finality_pair
  signer := fun a => some a.signer
  decode_height _ _ h := by cases Option.some.inj h; rfl
  decode_finality _ _ h := by cases Option.some.inj h; rfl
  decode_signer _ _ h := by cases Option.some.inj h; rfl

private def ladI : V2.D.Interface ladP where
  confirmed _ := .genesis
  stable _ := .genesis
  block p := match p with | .inr B => some B | .inl _ => none
  opening _ := False
  propLabel s := 4 * s
  propDuty s := 4 * s
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective _ _ h := Nat.eq_of_mul_eq_mul_left (by decide) h

private def ladDel (B : FGBlock (Fin 1)) (t : Time) : V2.Event Unit ladP.Object :=
  .deliver () ⟨.none, .inr (v5erase B)⟩ t

private noncomputable abbrev ladrho : V2.D.Run Unit ladP where
  honest := {()}
  horizon := 168
  events := [
    .tick () 0, .tick () 1, .tick () 2, .tick () 3, .tick () 4, ladDel (ladX 1) 4, .tick () 5,
    .tick () 6, .tick () 7, .tick () 8, ladDel (ladX 2) 8, .tick () 9, .tick () 10, .tick () 11,
    .tick () 12, ladDel (ladX 3) 12, .tick () 13, ladDel (ladp 1) 13, .tick () 14, .tick () 15,
    .tick () 16, .tick () 17, .tick () 18, .tick () 19, .tick () 20, .tick () 21,
    ladDel (ladp 2) 21, .tick () 22, .tick () 23, .tick () 24, .tick () 25, .tick () 26,
    .tick () 27, .tick () 28, .tick () 29, ladDel (ladp 3) 29, .tick () 30, .tick () 31,
    .tick () 32, .tick () 33, .tick () 34, .tick () 35, .tick () 36, .tick () 37,
    ladDel (ladp 4) 37, .tick () 38, .tick () 39, .tick () 40, .tick () 41, .tick () 42,
    .tick () 43, .tick () 44, .tick () 45, ladDel (ladp 5) 45, .tick () 46, .tick () 47,
    .tick () 48, .tick () 49, .tick () 50, .tick () 51, .tick () 52, .tick () 53,
    ladDel (ladp 6) 53, .tick () 54, .tick () 55, .tick () 56, .tick () 57, .tick () 58,
    .tick () 59, .tick () 60, .tick () 61, ladDel (ladp 7) 61, .tick () 62, .tick () 63,
    .tick () 64, .tick () 65, .tick () 66, .tick () 67, .tick () 68, .tick () 69,
    ladDel (ladp 8) 69, .tick () 70, .tick () 71, .tick () 72, .tick () 73, .tick () 74,
    .tick () 75, .tick () 76, .tick () 77, ladDel (ladp 9) 77, .tick () 78, .tick () 79,
    .tick () 80, .tick () 81, .tick () 82, .tick () 83, .tick () 84, .tick () 85,
    ladDel (ladp 10) 85, .tick () 86, .tick () 87, .tick () 88, .tick () 89, .tick () 90,
    .tick () 91, .tick () 92, .tick () 93, ladDel (ladp 11) 93, .tick () 94, .tick () 95,
    .tick () 96, .tick () 97, .tick () 98, .tick () 99, .tick () 100, .tick () 101,
    ladDel (ladp 12) 101, .tick () 102, .tick () 103, .tick () 104, .tick () 105, .tick () 106,
    .tick () 107, .tick () 108, .tick () 109, ladDel (ladp 13) 109, .tick () 110, .tick () 111,
    .tick () 112, .tick () 113, .tick () 114, .tick () 115, .tick () 116, .tick () 117,
    ladDel (ladp 14) 117, .tick () 118, .tick () 119, .tick () 120, .tick () 121, .tick () 122,
    .tick () 123, .tick () 124, .tick () 125, ladDel (ladp 15) 125, .tick () 126, .tick () 127,
    .tick () 128, .tick () 129, .tick () 130, .tick () 131, .tick () 132, .tick () 133,
    ladDel (ladp 16) 133, .tick () 134, .tick () 135, .tick () 136, .tick () 137, .tick () 138,
    .tick () 139, .tick () 140, .tick () 141, ladDel (ladp 17) 141, .tick () 142, .tick () 143,
    .tick () 144, .tick () 145, .tick () 146, .tick () 147, .tick () 148, .tick () 149,
    ladDel (ladp 18) 149, .tick () 150, .tick () 151, .tick () 152, .tick () 153, .tick () 154,
    .tick () 155, .tick () 156, .tick () 157, ladDel (ladp 19) 157, .tick () 158, .tick () 159,
    .tick () 160, .tick () 161, .tick () 162, .tick () 163, .tick () 164, .tick () 165,
    ladDel (ladp 20) 165, .tick () 166, .tick () 167, .tick () 168]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

private theorem ladlen : ladrho.events.length = 192 := by decide +kernel

private theorem ladnonneg : ∀ e ∈ ladrho.events, 0 ≤ e.time := by decide +kernel

private theorem ladschedule : V2.D.ScheduleWellFormed v5env ladrho where
  horizon_nonneg := by decide
  sorted := by decide +kernel
  nodup := by decide +kernel
  in_horizon := by
    intro e he
    exact ⟨ladnonneg e he, by revert e; decide +kernel⟩
  honest_only := by intro e he; simp
  tick_public := by
    intro v t ht
    have h := ladnonneg _ ht
    refine ⟨t.toNat, ?_⟩
    simp only [V2.Event.time] at h
    change (t : Int) = ((t.toNat : Nat) : Int) * 1
    rw [Int.toNat_of_nonneg h, Int.mul_one]
  tick_total := by
    intro v _ t ht _ hh _
    obtain ⟨k, rfl⟩ := ht
    have hk : k ≤ 168 := by
      change ((k : Nat) : Int) * 1 ≤ 168 at hh
      omega
    cases v
    interval_cases k <;> decide +kernel

/-- Deliveries among the first `i` events. -/
private abbrev ladcnt (i : Nat) : Nat :=
  ((ladrho.events.take i).filter (fun e => match e with | .deliver .. => true | _ => false)).length

private theorem ladstate (i : Nat) : ladrho.stateBefore v5env i () = ladcnt i := by
  have hall : ∀ i < 193, ladrho.stateBefore v5env i () = ladcnt i := by decide +kernel
  rcases Nat.lt_or_ge i 193 with h | h
  · exact hall i h
  · have he : ∀ j, 192 ≤ j → ladrho.events.take j = ladrho.events := fun j hj =>
      List.take_of_length_le (by rw [ladlen]; omega)
    unfold V2.D.Run.stateBefore
    rw [he i (by omega)]
    have h39 := he 192 le_rfl
    have := hall 192 (by omega)
    unfold V2.D.Run.stateBefore at this
    rw [h39] at this
    rw [this]
    unfold ladcnt
    rw [he i (by omega), h39]

private theorem ladcnt_mono {i j : Nat} (hij : i ≤ j) : ladcnt i ≤ ladcnt j := by
  unfold ladcnt
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [List.take_add, List.filter_append, List.length_append]
  exact Nat.le_add_right _ _

private theorem ladcnt_le (i : Nat) : ladcnt i ≤ 23 := by
  have h := ladcnt_mono (i := i) (j := i + 192) (by omega)
  have h2 : ladcnt (i + 192) = 23 := by
    unfold ladcnt
    rw [List.take_of_length_le (by rw [ladlen]; omega)]
    decide +kernel
  omega

private theorem ladstore_inv (k : Nat) (hk : k ≤ 23) :
    FGStoreInvariant ladO.height ladO.finality (ladR.core k).fg := by
  interval_cases k <;> constructor <;> decide +kernel

private theorem ladinv (i : Nat) (x : Unit) : FGStoreInvariant ladO.height ladO.finality
    (ladR.core (ladrho.stateBefore v5env i x)).fg := by
  cases x
  rw [ladstate]
  exact ladstore_inv _ (ladcnt_le i)

private theorem ladTF_mono {a b : Nat} (hab : a ≤ b) : ladTF a ⊆ ladTF b := by
  intro B hB
  simp only [ladTF, Finset.mem_insert, List.mem_toFinset] at hB ⊢
  rcases hB with h | h
  · exact Or.inl h
  · exact Or.inr ((List.take_prefix_take_left (by omega) |>.subset) h)

private theorem ladkeep : ∀ i j, i ≤ j → ∀ x,
    TFAt ladR v5env ladrho i x ⊆ TFAt ladR v5env ladrho j x := by
  intro i j hij x
  cases x
  change ladTF (ladrho.stateBefore v5env i ()) ⊆ ladTF (ladrho.stateBefore v5env j ())
  rw [ladstate, ladstate]
  exact ladTF_mono (ladcnt_mono hij)

private theorem ladhmax_mono {a b : Nat} (h : a ≤ b) : ladhmax a ≤ ladhmax b := by
  unfold ladhmax
  split_ifs <;> omega

private theorem ladmono : FGRunOrderLaws v5env ladrho ladR := by
  constructor
  intro i j x _ hij
  cases x
  rw [ladstate, ladstate]
  exact ⟨preceq_refl _, le_refl _, ladhmax_mono (ladcnt_mono hij)⟩

private theorem ladcore : FGCoreLaws ladR where
  clock_fg _ _ := rfl
  clock_proposals _ _ := rfl
  clock_rowPool _ _ := rfl
  process_tf st _ := ladTF_mono (Nat.le_succ st)
  process_proposals _ _ := List.prefix_rfl
  process_rowPool _ _ := List.prefix_rfl
  own_core _ _ := rfl
  source_mem _ _ h := by cases h
  erase_inj := v5erase_inj

private theorem ladcrossing : RXing ladR v5env ladrho ladO := by
  intro i i' x y K W _ _ _ _ _ _
  exact genesis_preceq W

private theorem ladfront (k : Nat) : frontierAtIdx ladR v5env ladrho k = ladhmax (ladcnt k) := by
  unfold frontierAtIdx
  change ({()} : Finset Unit).sup _ = _
  rw [Finset.sup_singleton, ladstate]

/-- Controls of every store count: frontier, no contest, Z = genesis. -/
private theorem ladctl (k : Nat) (hk : k ≤ 23) :
    (treeStoreControlsView v5H (ladR.core k).fg).H = ladhmax k ∧
    (treeStoreControlsView v5H (ladR.core k).fg).contest = false ∧
    (treeStoreControlsView v5H (ladR.core k).fg).Z = .genesis := by
  interval_cases k <;> decide +kernel

/-- The frontier witness of every store count. -/
private theorem ladtopFacts (k : Nat) (hk : k ≤ 23) :
    ladtop k ∈ ladTF k ∧ (v5H (ladtop k)).h = ladhmax k := by
  interval_cases k <;> decide +kernel

private theorem ladgenesis : (v5H .genesis).h = 1 ∧ (v5H .genesis).h_j = 0 ∧
    (v5H .genesis).J = .genesis := by decide +kernel

/-- Released objects at a tick of time `d`. -/
private abbrev ladout (d : Nat) : List ladP.Object :=
  if d % 8 = 6 ∧ d ≤ 168 then [⟨.seat d 0, .inl (ladrow (d / 8))⟩]
  else if d % 4 = 0 ∧ 4 ≤ d ∧ d ≤ 168 then [⟨.seat d 0, .inr (v5erase (ladX (d / 4)))⟩]
  else []

private theorem ladEmits (j : Nat) : V2.D.Run.emitsAt v5env ladrho j =
    match ladrho.events[j]? with
    | some (.tick _ t) => ladout t.toNat
    | _ => [] := by
  rcases Nat.lt_or_ge j 192 with h | h
  · interval_cases j <;> decide +kernel
  · have hn : ladrho.events[j]? = none := List.getElem?_eq_none (by rw [ladlen]; omega)
    simp only [V2.D.Run.emitsAt, hn]

/-- Index of the tick of time `t`. -/
private abbrev ladti (t : Nat) : Nat :=
  t + (if 4 < t then 1 else 0) + (if 8 < t then 1 else 0) + (if 12 < t then 1 else 0) +
    min ((t - 6) / 8) 20

private theorem ladtick (t : Nat) (ht : t ≤ 168) :
    ladrho.events[ladti t]? = some (.tick () ((t : Nat) : Int)) := by
  interval_cases t <;> decide +kernel

/-- The honest proposals are exactly the labelled blocks of slots 1..42. -/
private theorem ladprop {s : Slot} {B : Block} (h : HonestProposal v5env ladrho ladI s B) :
    1 ≤ s ∧ s ≤ 42 ∧ B = v5erase (ladX s) := by
  obtain ⟨⟨hs0, _⟩, o, ⟨i, hi, ho⟩, hb⟩ := h
  rw [ladEmits, hi] at ho
  have ht := (ladschedule.in_horizon _ (List.mem_of_getElem? hi)).2
  change ((4 * s : Nat) : Int) ≤ 168 at ht
  change o ∈ ladout (((4 * s : Nat) : Int).toNat) at ho
  rw [Int.toNat_natCast] at ho
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = s := ⟨_, rfl⟩
  subst hk
  have h4 : 4 * k ≤ 168 := by exact_mod_cast ht
  have h1 : 1 ≤ k := hs0
  have hk6 : k ≤ 42 := by omega
  have hne : ¬ 4 * k % 8 = 6 := by omega
  have hc : 4 * k % 4 = 0 ∧ 4 ≤ 4 * k ∧ 4 * k ≤ 168 := ⟨by omega, by omega, by omega⟩
  simp only [ladout, hne, false_and, hc, and_self, ite_true, ite_false,
    List.mem_singleton] at ho
  subst ho
  have hdiv : 4 * k / 4 = k := by omega
  rw [hdiv] at hb
  exact ⟨h1, hk6, (Option.some.inj hb).symm⟩

private theorem ladpropOf (s : Nat) (h1 : 1 ≤ s) (h42 : s ≤ 42) :
    HonestProposal v5env ladrho ladI s (v5erase (ladX s)) := by
  refine ⟨⟨h1, Finset.mem_singleton_self _⟩, ⟨.seat (4 * s) 0, .inr (v5erase (ladX s))⟩,
    ⟨ladti (4 * s), ladtick (4 * s) (by omega), ?_⟩, rfl⟩
  rw [ladEmits, ladtick (4 * s) (by omega)]
  change _ ∈ ladout (((4 * s : Nat) : Int).toNat)
  rw [Int.toNat_natCast]
  have hne : ¬ 4 * s % 8 = 6 := by omega
  have hc : 4 * s % 4 = 0 ∧ 4 ≤ 4 * s ∧ 4 * s ≤ 168 := ⟨by omega, by omega, by omega⟩
  have hdiv : 4 * s / 4 = s := by omega
  simp only [ladout, hne, false_and, hc, and_self, ite_true, ite_false, List.mem_singleton,
    hdiv]

private theorem ladaction (r : Nat) : (v5T.action r).toNat = 8 * r + 6 := by
  change (8 * ((r : Nat) : Int) + 6).toNat = 8 * r + 6
  omega

/-- The honest rows are exactly the action rows 0..20. -/
private theorem ladrows {j : Nat} {y : Unit} {r : Nat} {a : Row (Fin 1)}
    (h : HonestRowAt ladS v5env ladrho v5T j y r a) : r ≤ 20 ∧ a = ladrow r := by
  obtain ⟨_, hj, hem⟩ := h
  rw [ladEmits, hj] at hem
  change ladS.encode a ∈ ladout (v5T.action r).toNat at hem
  rw [ladaction] at hem
  by_cases hr : r ≤ 20
  · have hc : (8 * r + 6) % 8 = 6 ∧ 8 * r + 6 ≤ 168 := ⟨by omega, by omega⟩
    have hdiv : (8 * r + 6) / 8 = r := by omega
    simp only [ladout, hc, and_self, ite_true, List.mem_singleton, hdiv] at hem
    have := congrArg V2.Signed.payload hem
    exact ⟨hr, Sum.inl.inj this⟩
  · have hne : ¬ 8 * r + 6 ≤ 168 := by omega
    simp only [ladout, hne, and_false, ite_false, List.not_mem_nil] at hem

private theorem ladrowAt (r : Nat) (hr : r ≤ 20) :
    HonestRowAt ladS v5env ladrho v5T (ladti (8 * r + 6)) () r (ladrow r) := by
  have ht : v5T.action r = ((8 * r + 6 : Nat) : Int) := by
    change 8 * ((r : Nat) : Int) + 6 = _
    push_cast
    rfl
  refine ⟨Finset.mem_singleton_self _, ?_, ?_⟩
  · rw [ht]
    exact ladtick (8 * r + 6) (by omega)
  · rw [ladEmits, ladtick (8 * r + 6) (by omega)]
    change _ ∈ ladout (((8 * r + 6 : Nat) : Int).toNat)
    rw [Int.toNat_natCast]
    have hc : (8 * r + 6) % 8 = 6 ∧ 8 * r + 6 ≤ 168 := ⟨by omega, by omega⟩
    have hdiv : (8 * r + 6) / 8 = r := by omega
    have hidx : ladrowIdx (ladrow r) = r := rfl
    simp only [ladout, hc, and_self, ite_true, List.mem_singleton, hdiv]
    change (⟨.seat (8 * ladrowIdx (ladrow r) + 6) 0, .inl (ladrow r)⟩ : ladP.Object) = _
    rw [hidx]

/-- Frame height at an event index. -/
private theorem ladH (i : Nat) :
    (ladO.controls (ladrho.stateBefore v5env i ())).H = ladhmax (ladcnt i) := by
  change (treeStoreControlsView v5H (ladR.core (ladrho.stateBefore v5env i ())).fg).H = _
  rw [ladstate]
  exact (ladctl _ (ladcnt_le i)).1

/-- Every window of seven time units after 12 contains a frontier rise. -/
private theorem ladshortTable : ∀ t < 162, 12 ≤ t →
    ladhmax (ladcnt (V2.D.Run.idxBefore ladrho ((t : Nat) : Int))) <
      ladhmax (ladcnt (timeIdx ladrho (((t + 7 : Nat) : Nat) : Int))) := by
  decide +kernel

/-- No phase holds over a proposal-to-gate interval of a slot from 3. -/
private theorem ladgateTable : ∀ q < 41, 3 ≤ q →
    ladhmax (ladcnt (V2.D.Run.idxBefore ladrho ((4 * q : Nat) : Int))) <
      ladhmax (ladcnt (timeIdx ladrho ((4 * q + 6 : Nat) : Int))) := by
  decide +kernel

private theorem ladphaseH {u v : Int} {m : Nat} {J : Option (FGBlock (Fin 1))}
    {contested : Bool} (hp : PhaseInterval ladR v5env ladrho ladO u v m J contested)
    {a b : Int} (ha : u ≤ a) (hb : b ≤ v) (hab : a ≤ b) :
    ladhmax (ladcnt (V2.D.Run.idxBefore ladrho a)) =
      ladhmax (ladcnt (timeIdx ladrho b)) := by
  have h1 := (hp.2.2.2 (V2.D.Run.idxBefore ladrho a) () (v9idxBefore_mono ladrho ha)
    (((v9idxBefore_le_timeIdx ladrho a).trans (v9timeIdx_mono ladrho hab)).trans
      (v9timeIdx_mono ladrho hb)) (Finset.mem_singleton_self _)).1
  have h2 := (hp.2.2.2 (timeIdx ladrho b) () (((v9idxBefore_mono ladrho ha).trans
    (v9idxBefore_le_timeIdx ladrho a)).trans (v9timeIdx_mono ladrho hab))
    (v9timeIdx_mono ladrho hb) (Finset.mem_singleton_self _)).1
  rw [ladH] at h1 h2
  rw [h1, h2]

/-- Every phase from the join time lasts at most six time units. -/
private theorem ladphase_short {u v : Int} {m : Nat} {J : Option (FGBlock (Fin 1))}
    {contested : Bool} (hu : 12 ≤ u)
    (hp : PhaseInterval ladR v5env ladrho ladO u v m J contested) : v ≤ u + 6 := by
  by_contra hn
  have hv : v ≤ 168 := hp.2.1
  obtain ⟨t, ht⟩ : ∃ t : Nat, u = ((t : Nat) : Int) :=
    ⟨u.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  subst ht
  have h12 : 12 ≤ t := by exact_mod_cast hu
  have hlt := ladshortTable t (by omega) h12
  have hb : ((t + 7 : Nat) : Int) ≤ v := by push_cast; omega
  have heq := ladphaseH hp (a := ((t : Nat) : Int)) (b := ((t + 7 : Nat) : Int)) le_rfl
    hb (by push_cast; omega)
  omega

/-- No phase from the join time contains the gate of a seed-qualified slot. -/
private theorem ladnoSeed {u v : Int} {m q : Nat} {J : Option (FGBlock (Fin 1))}
    {contested : Bool} (hu : 12 ≤ u)
    (hp : PhaseInterval ladR v5env ladrho ladO u v m J contested)
    (hseed : FrontierSeedQualification v5T 1 v5env.t_GST u q) (hg : v5T.gate q ≤ v) :
    False := by
  have hs : v ≤ u + 6 := ladphase_short hu hp
  have hg' : 4 * ((q : Nat) : Int) + 6 ≤ v := hg
  rcases hseed with ⟨β, hβ, _, hlt⟩ | ⟨b, hb, _, _, _, hlt⟩
  · have h1 : u < 4 * ((β : Nat) : Int) := hβ
    have h2 : 4 * (((β + 2 * 1 - 1 : Nat) : Nat) : Int) < 4 * ((q : Nat) : Int) := hlt
    have h3 : ((β + 2 * 1 - 1 : Nat) : Int) = (β : Int) + 1 := by push_cast; omega
    omega
  · have h1 : u ≤ 4 * ((b : Nat) : Int) + 1 := hb
    have h2 : 4 * (((b + 1 : Nat) : Nat) : Int) < 4 * ((q : Nat) : Int) := hlt
    push_cast at h2
    omega

private theorem ladready : ∀ t, (12 : Time) ≤ t →
    v5env.t_GST ≤ slotStartZ v5T (((slotAt v5T t : Slot) : Int) - 1) := by
  intro t ht
  have ht' : (12 : Int) ≤ t := ht
  change (0 : Int) ≤ 4 * 1 * ((((t / (4 * 1)).toNat : Nat) : Int) - 1)
  have h1 : (1 : Int) ≤ t / 4 := by omega
  have h2 : (((t / 4).toNat : Nat) : Int) = t / 4 := Int.toNat_of_nonneg (by omega)
  simp only [Int.mul_one] at *
  rw [h2]
  omega

private abbrev ladreceipt (B : Block) (d : Time) (y : Unit) : Prop :=
  ∃ W, v5erase W = B ∧ W ∈ (ladR.core (ladrho.stateBeforeTime v5env d y)).fg.TF

private theorem ladscope (W : FGBlock (Fin 1)) (d : Time)
    (hW : W ∈ (ladR.core (ladrho.stateBeforeTime v5env d ())).fg.TF) :
    WitnessReceiptScope ladR v5env ladrho (fun _ => true) ladreceipt W d :=
  ⟨fun _ y _ _ _ _ _ _ => by cases y; exact ⟨W, rfl, hW⟩⟩

private theorem ladheld (i : Nat) {W : FGBlock (Fin 1)} (hW : W ∈ ladTF (ladcnt i)) :
    W ∈ (ladR.core (ladrho.stateBefore v5env i ())).fg.TF := by
  change W ∈ ladTF (ladrho.stateBefore v5env i ())
  rw [ladstate]
  exact hW

/-- Receipt scopes at every event: the frontier witness is the chain tip; the top witness
exists only at frontier 1 and is genesis; no contest evidence exists. -/
private theorem ladservices : ∀ i (ev : V2.Event Unit ladP.Object) m,
    ladrho.events[i]? = some ev → (12 : Time) ≤ ev.time → 1 ≤ m →
    frontierAtIdx ladR v5env ladrho (i + 1) = m → ev.time + v5T.delta ≤ ladrho.horizon →
    PhaseWitnessReceiptScope ladR v5env ladrho ladO (fun _ => true) ladreceipt (i + 1) m
      (ev.time + v5T.delta) := by
  intro i ev m hi _ _ hf _
  rw [ladfront] at hf
  have hlater : ∀ W, W ∈ ladTF (ladcnt (i + 1)) →
      W ∈ (ladR.core (ladrho.stateBeforeTime v5env (ev.time + v5T.delta) ())).fg.TF := by
    intro W hW
    rw [← Gen.V2.Duty.stateBefore_idxBefore v5env ladrho _ ladschedule]
    have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff ladschedule hi
      (ev.time + v5T.delta)).mpr (by
        change ev.time < ev.time + 1
        exact lt_add_one _)
    exact ladheld _ (ladTF_mono (ladcnt_mono hlt) hW)
  obtain ⟨htop, hh⟩ := ladtopFacts _ (ladcnt_le (i + 1))
  refine ⟨⟨(), ladtop _, ⟨Finset.mem_singleton_self _, ladheld _ htop⟩, hh.trans hf,
    ladscope _ _ (hlater _ htop)⟩, ?_, ?_⟩
  · rintro ⟨x, _, htp⟩
    have hm1 : m = 1 := by
      have htp' : (0 : Nat) + 1 = m := htp
      omega
    subst hm1
    have hg : FGBlock.genesis ∈ ladTF (ladcnt (i + 1)) := Finset.mem_insert_self _ _
    exact ⟨(), .genesis, ⟨Finset.mem_singleton_self _, ladheld _ hg⟩, ladgenesis.1,
      by rw [ladgenesis.2.1], ladgenesis.2.2, ladscope _ _ (hlater _ hg)⟩
  · rintro ⟨x, _, _, hc⟩
    cases x
    change (treeStoreControlsView v5H (ladR.core
      (ladrho.stateBefore v5env (i + 1) ())).fg).contest = true at hc
    rw [ladstate, (ladctl _ (ladcnt_le _)).2.1] at hc
    cases hc

private theorem ladfault : v5E.weightOf (historyFaulty ladS ladrho) < v5E.q := by
  have h : historyFaulty ladS ladrho = ∅ := by
    unfold historyFaulty
    ext i
    simp
  rw [h]
  decide

private theorem ladgap : ∀ t, v5env.t_GST ≤ t → t + 4 ≤ ladrho.horizon →
    ∃ s, t < v5T.proposal s ∧ v5T.proposal s ≤ t + 4 ∧ Gen.V2.Duty.HonestSlot ladrho ladI s := by
  intro t ht0 hth
  obtain ⟨z, hz⟩ : ∃ z : Int, z = t := ⟨t, rfl⟩
  subst hz
  have h0 : (0 : Int) ≤ z := ht0
  have hs : (((z / 4 + 1).toNat : Nat) : Int) = z / 4 + 1 := Int.toNat_of_nonneg (by omega)
  have hlo : z < 4 * (z / 4 + 1) := by omega
  have hhi : 4 * (z / 4 + 1) ≤ z + 4 := by omega
  have hpos : 0 < (z / 4 + 1).toNat := by omega
  refine ⟨(z / 4 + 1).toNat, ?_, ?_, hpos, Finset.mem_singleton_self _⟩
  · change z < 4 * (((z / 4 + 1).toNat : Nat) : Int)
    rw [hs]
    exact hlo
  · change 4 * (((z / 4 + 1).toNat : Nat) : Int) ≤ z + 4
    rw [hs]
    exact hhi

private theorem ladslot : PromotionSlotProposal ladR v5env ladrho v5T ladI := by
  intro s hs _ hh
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = s := ⟨_, rfl⟩
  subst hk
  have h1 : 0 < k := hs.1
  have hH : 4 * ((k : Nat) : Int) ≤ 168 := hh
  exact ⟨ladX k, ladpropOf k h1 (by omega), rfl⟩

private theorem ladpstate (s : Nat) (h1 : 1 ≤ s) (h42 : s ≤ 42) :
    ∃ nd, proposalStateAt v5env ladrho ladI s = some nd := by
  interval_cases s <;> exact Option.isSome_iff_exists.mp (by decide +kernel)

private def laddecode (o : ladP.Object) : Option (Slot × Block) :=
  match o.payload with
  | .inr B => some (B.slot, B)
  | .inl _ => none
private def ladparentFG (nd : Nat) (B : Block) : Option (FGBlock (Fin 1)) :=
  (FGBlock.genesis :: ladblocks.take nd).find? (fun A => decide (v5erase A = B))
private def ladfold (_ : Nat) (_ : Slot) (P : FGBlock (Fin 1)) : Window.State (Fin 1) :=
  Window.derive v5E v5cfg 2 P
private def ladparentHeight (nd : Nat) (s : Slot) (P : FGBlock (Fin 1)) : Height × BlockId :=
  ((ladfold nd s P).h, (ladfold nd s P).T_h.root)
private def ladvalidFor (nd : Nat) (s : Slot) (P : FGBlock (Fin 1)) (a : Row (Fin 1)) : Bool :=
  Window.r6w (ladfold nd s P) a

private theorem ladcarrier {s : Slot} {X : FGBlock (Fin 1)} (hX : X.slot = s)
    (hQ : HonestProposal v5env ladrho ladI s (v5erase X)) :
    HonestCarrier v5env ladrho ladI
      (kernelCarrier laddecode id (fun _ => ([] : List (Row (Fin 1))))) s (v5erase X) [] := by
  refine ⟨hQ, ?_⟩
  obtain ⟨_, ⟨auth, payload⟩, hem, hb⟩ := hQ
  cases payload with
  | inl _ => cases hb
  | inr B =>
    cases Option.some.inj hb
    refine ⟨⟨auth, .inr (v5erase X)⟩, hem, v5erase X, ?_, rfl, rfl⟩
    have hs : (v5erase X).slot = X.slot := by cases X <;> rfl
    change some ((v5erase X).slot, v5erase X) = some (s, v5erase X)
    rw [hs, hX]

private theorem ladread : PromotionProposalRead ladR ladS v5env ladrho ladO ladI laddecode id
    (fun _ => []) ladparentFG ladparentHeight ladvalidFor ladfold := by
  intro s X hQ hXs
  obtain ⟨h1, h42, hX⟩ := ladprop hQ
  have hX' : X = ladX s := v5erase_inj hX
  subst hX'
  refine ⟨⟨[], ladcarrier hXs hQ, rfl⟩, ?_⟩
  obtain ⟨nd, hnd⟩ := ladpstate s h1 h42
  exact ⟨nd, hnd, rfl, rfl, rfl, rfl, fun _ => rfl⟩

private theorem ladorder : PromotionRowOrder ladR v5env ladrho ladO ladI := by
  intro s X height U hQ _ _ _ i W hW hrow
  obtain ⟨_, _, hX⟩ := ladprop hQ
  have hX' : X = ladX s := v5erase_inj hX
  subst hX'
  have hWg : W = .genesis := (preceq_genesis).mp hW
  subst hWg
  obtain ⟨row, hr, _⟩ := hrow
  cases hr

private theorem ladsigner : PromotionRowSigner ladS v5env ladrho v5T ladD := by
  refine ⟨fun _ _ _ a _ => ⟨a, rfl⟩, fun i j r a h => ?_⟩
  obtain ⟨_, rfl⟩ := ladrows h
  rw [Subsingleton.elim i 0]
  rfl

private theorem ladrowsReceipt :
    TRowsReceipt ladR ladS v5env ladrho v5T (fun _ => []) 1 := by
  intro j y r a h _ x _
  obtain ⟨hr, rfl⟩ := ladrows h
  exact Or.inl (List.mem_map.mpr ⟨r, List.mem_range.mpr (by omega), rfl⟩)

private theorem ladsrc {x : Unit} {r : Nat} {K : FGBlock (Fin 1)}
    (h : actionSourceFG ladR v5env ladrho v5T x r = some (some K)) : False := by
  unfold actionSourceFG at h
  obtain ⟨nd, _, hnd⟩ := Option.map_eq_some_iff.mp h
  cases hnd

/-- No batch premise holds: every honest row names a root that is not a stored block,
while every honest proposal's parent is genesis, whose read is (1, genesis). -/
private theorem ladnoBatch {r height : Nat} {U X : FGBlock (Fin 1)}
    (h : BatchPrem ladR ladS ladO v5T v5env ladrho ladI ladD v5E laddecode id (fun _ => [])
      (fun _ => []) ladparentFG ladparentHeight ladvalidFor 1 .progress r height U X) :
    False := by
  obtain ⟨rows, hcar, _⟩ := h.carrier
  obtain ⟨_, _, hX⟩ := ladprop hcar.1
  obtain ⟨Q, _, hq, hall⟩ := h.valid
  rcases Finset.eq_empty_or_nonempty Q with he | ⟨i, hi⟩
  · rw [he] at hq
    exact absurd hq (by decide)
  obtain ⟨j, r', a, t, _, hrow, _, _, _, _, _, ⟨nd, H, _, hpar, hent⟩⟩ := hall i hi
  obtain ⟨_, rfl⟩ := ladrows hrow
  rw [hX] at hpar
  have h0 : ladparentFG nd (v5erase (ladX X.slot)).parent = some .genesis := rfl
  rw [h0] at hpar
  cases Option.some.inj hpar
  have h1 : ladparentHeight nd X.slot .genesis = (1, genesisRoot) := rfl
  rw [h1] at hent
  have h2 : (r' + 1, (⟨900 + r'⟩ : BlockId)) = (1, genesisRoot) := Option.some.inj hent
  have h3 : 900 + r' = 0 := congrArg (fun e : Height × BlockId => e.2.value) h2
  omega

private theorem ladfloor : AttemptProposalFloor ladR v5env ladrho ladO v5T ladI 12 := by
  intro (u : Int) (v : Int) m J contested (q : Nat) Q Qfg hu hp huq hqv _ _
  exfalso
  have hu' : 12 ≤ u := hu
  have huq' : u ≤ 4 * ((q : Nat) : Int) := huq
  have hqv' : 4 * ((q : Nat) : Int) + 6 ≤ v := hqv
  have hv : v ≤ 168 := hp.2.1
  have hq3 : 3 ≤ q := by omega
  have hlt := ladgateTable q (by omega) hq3
  have heq := ladphaseH hp (a := ((4 * q : Nat) : Int)) (b := ((4 * q + 6 : Nat) : Int))
    (by push_cast; omega) (by push_cast; omega) (by push_cast; omega)
  omega

private theorem ladheldSlot : ∀ i x A K,
    K ∈ (ladR.core (ladrho.stateBefore v5env i x)).fg.TF →
    FGBlock.Preceq A K → A.slot ≤ K.slot := by
  intro i x A K hK hAK
  apply v9anc_slot _ hAK
  cases x
  change K ∈ ladTF (ladrho.stateBefore v5env i ()) at hK
  rw [ladstate] at hK
  have hall : ∀ B ∈ ladTF 23, v9slotsOK B = true := by decide +kernel
  exact hall K (ladTF_mono (ladcnt_le i) hK)

private theorem ladproposalSlot : ∀ q Q K, HonestProposal v5env ladrho ladI q Q →
    v5erase K = Q → K.slot = q := by
  intro q Q K hQ hK
  obtain ⟨_, _, hQ'⟩ := ladprop hQ
  have hK' : K = ladX q := v5erase_inj (hK.trans hQ')
  rw [hK']
  rfl

private theorem ladparentFrame : ∀ q Q, HonestProposal v5env ladrho ladI q Q → ∃ j,
    ladrho.events[j]? = some (.tick (V2.D.proposerOf ladrho ladI q) (v5T.proposal q)) ∧
    ∀ Qfg, v5erase Qfg = Q → FGBlock.Preceq
      (ladO.controls (ladrho.stateBefore v5env j (V2.D.proposerOf ladrho ladI q))).Z
      Qfg.parent := by
  intro (q : Nat) Q hQ
  obtain ⟨h1, h42, hQe⟩ := ladprop hQ
  have h42' : (q : Nat) ≤ 42 := h42
  have ht : v5T.proposal q = ((4 * q : Nat) : Int) := by
    change 4 * ((q : Nat) : Int) = _
    push_cast
    rfl
  refine ⟨ladti (4 * q), ?_, ?_⟩
  · rw [ht]
    exact ladtick (4 * q) (by omega)
  · intro Qfg he
    have hQfg : Qfg = ladX q := v5erase_inj (he.trans hQe)
    subst hQfg
    change FGBlock.Preceq (treeStoreControlsView v5H
      (ladR.core (ladrho.stateBefore v5env (ladti (4 * q)) ())).fg).Z FGBlock.genesis
    rw [ladstate, (ladctl _ (ladcnt_le _)).2.2]
    exact preceq_refl _

/-- After slot 3 the frontier is above 1 before the proposal receipt deadline. -/
private theorem ladcapTable : ∀ s < 43, 4 ≤ s →
    2 ≤ ladhmax (ladcnt (V2.D.Run.idxBefore ladrho ((4 * s + 1 : Nat) : Int))) := by
  decide +kernel

private theorem ladcapReceipt : PromotionCapReceipt ladR v5env ladrho ladO v5T ladI := by
  intro m s Qfg X hQ _ hpre hcap hQm _
  obtain ⟨h1, h42, hX⟩ := ladprop hQ
  have hX' : X = ladX s := v5erase_inj hX
  subst hX'
  have hQg : Qfg = .genesis := (preceq_genesis).mp hpre
  subst hQg
  have hm : m = 1 := hQm.symm.trans ladgenesis.1
  subst hm
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = s := ⟨_, rfl⟩
  subst hk
  have h42' : (k : Nat) ≤ 42 := h42
  by_cases hs : k ≤ 3
  · refine ⟨(), Finset.mem_singleton_self _, ?_⟩
    unfold Gen.V2.Duty.HoldsBefore
    interval_cases k <;> decide +kernel
  · exfalso
    have ht : v5T.proposal k + v5T.delta = ((4 * k + 1 : Nat) : Int) := by
      change 4 * ((k : Nat) : Int) + 1 = _
      push_cast
      rfl
    have h := hcap (V2.D.Run.idxBefore ladrho (v5T.proposal k + v5T.delta)) () le_rfl
      (Finset.mem_singleton_self _)
    have h' : ladhmax (ladrho.stateBefore v5env
        (V2.D.Run.idxBefore ladrho (v5T.proposal k + v5T.delta)) ()) ≤ (1 : Nat) := h
    rw [ladstate, ht] at h'
    have := ladcapTable k (by omega) (by omega)
    omega

/-- The honest row of height y + 1 is sent before any block of height y + 2 is held. -/
private theorem ladrowTable : ∀ i < 193, ∀ y < 20, y + 4 ≤ ladcnt i → ladti (8 * y + 6) < i := by
  decide +kernel

private theorem ladhmax_ge {c y : Nat} (h : y + 2 ≤ ladhmax c) : y + 4 ≤ c := by
  unfold ladhmax at h
  split_ifs at h <;> omega

private theorem ladcap : RCap ladR ladS v5env ladrho ladO v5T
    (fun a => namedEntry (ladD.heightPair a)) (fun _ _ => ladAllRows) := by
  intro (y : Nat) i x W hheld hy
  obtain ⟨_, hW⟩ := hheld
  cases x
  have hle := healing_phase_height_le (R := ladR) (E := v5env) (rho := ladrho) (O := ladO)
    (inv := ladinv) hW
  have hle' : (v5H W).h ≤ ladhmax (ladrho.stateBefore v5env i ()) := hle
  rw [ladstate] at hle'
  have hy' : (y + 2 : Nat) ≤ ladhmax (ladcnt i) := le_trans hy hle'
  have hc22 := ladcnt_le i
  have hc : y + 4 ≤ ladcnt i := ladhmax_ge hy'
  have hj : ladti (8 * y + 6) < i := by
    rcases Nat.lt_or_ge i 193 with hi | hi
    · exact ladrowTable i hi y (by omega) hc
    · have : ladti (8 * y + 6) ≤ 8 * y + 6 + 3 + 20 := by
        unfold ladti
        split_ifs <;> omega
      omega
  exact ⟨ladti (8 * y + 6), (), y, ladrow y, ⟨900 + y⟩, hj, ladrowAt y (by omega), rfl,
    List.mem_map.mpr ⟨y, List.mem_range.mpr (by omega), rfl⟩⟩

/-- Every allowance from 7 holds at every time: no phase lasts seven time units, and no
proposal after the first repair label reaches its gate inside a phase. -/
private theorem ladallow (ρ u : Int) (hρ : 7 ≤ ρ) :
    FrontierRepairAllowance ladR v5env ladrho ladO v5T ladI 12 1 4 ρ u := by
  classical
  have hex : ∃ s : Nat, u < v5T.proposal s := ⟨u.toNat + 1, by
    change u < 4 * (((u.toNat + 1 : Nat) : Nat) : Int)
    have := Int.self_le_toNat u
    push_cast
    omega⟩
  refine ⟨le_trans (by decide) hρ, Nat.find hex + 2 * 1 - 1,
    FrontierRepairStart.two (Nat.find hex) (Nat.find_spec hex)
      (fun b hb => Nat.find_min' hex hb), ?_⟩
  intro _ (v : Int) m J c hu hp
  have hs : v ≤ u + 6 := ladphase_short hu hp
  refine ⟨fun (s : Nat) Q hls hg _ => ?_, fun hb => ?_⟩
  · exfalso
    have h1 : u < 4 * ((Nat.find hex : Nat) : Int) := Nat.find_spec hex
    have h2 : 4 * (((Nat.find hex + 2 * 1 - 1 : Nat) : Nat) : Int) < 4 * ((s : Nat) : Int) :=
      hls
    have h3 : ((Nat.find hex + 2 * 1 - 1 : Nat) : Int) = (Nat.find hex : Int) + 1 := by
      push_cast
      omega
    have h4 : 4 * ((s : Nat) : Int) + 6 ≤ v := hg
    omega
  · exfalso
    have hb' : u + ρ ≤ v := hb
    omega

/-- The phase [30, 36] at frontier 4 from the cut. -/
private theorem ladphase30 : PhaseInterval ladR v5env ladrho ladO 30 36 4 none false := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro i x hi hi' _
  cases x
  have h1 : V2.D.Run.idxBefore ladrho 30 = 36 := by decide +kernel
  have h2 : timeIdx ladrho 36 = 43 := by decide +kernel
  rw [h1] at hi
  rw [h2] at hi'
  interval_cases i <;> decide +kernel

/-- An allowance below 7 fails at the cut: the phase [30, 36] has no repaired proposal. -/
private theorem ladallow30 {ρ : Int}
    (h : FrontierRepairAllowance ladR v5env ladrho ladO v5T ladI 12 1 4 ρ 30) : 7 ≤ ρ := by
  by_contra hn
  obtain ⟨_, l, hl, hrep⟩ := h
  obtain ⟨s, Q, hls, hg, _⟩ := (hrep (by decide) 36 4 none false (by decide) ladphase30).2
    (by
      change (30 : Int) + ρ ≤ 36
      omega)
  have hg' : 4 * ((s : Nat) : Int) + 6 ≤ 30 + ρ := hg
  cases hl with
  | two β after _ =>
    have h1 : (30 : Int) < 4 * ((β : Nat) : Int) := after
    have h2 : 4 * (((β + 2 * 1 - 1 : Nat) : Nat) : Int) < 4 * ((s : Nat) : Int) := hls
    have h3 : ((β + 2 * 1 - 1 : Nat) : Int) = (β : Int) + 1 := by
      push_cast
      omega
    omega
  | one b after _ _ _ =>
    have h1 : (30 : Int) ≤ 4 * ((b : Nat) : Int) + 1 := after
    have h2 : 4 * (((b + 1 : Nat) : Nat) : Int) < 4 * ((s : Nat) : Int) := hls
    push_cast at h2
    omega

private theorem ladfirst {rG : Nat} (h1 : (12 : Time) ≤ v5T.action rG)
    (h2 : ∀ r, (12 : Time) ≤ v5T.action r → rG ≤ r) : rG = 1 := by
  have ha : (12 : Int) ≤ 8 * ((rG : Nat) : Int) + 6 := h1
  have hb := h2 1 (by decide)
  omega

private theorem ladtransfer : ∀ rG ρbar, (12 : Time) ≤ v5T.action rG →
    (∀ r, (12 : Time) ≤ v5T.action r → rG ≤ r) →
    FrontierRepairAllowance ladR v5env ladrho ladO v5T ladI 12 1 4 ρbar
      (v5T.action (rG + 2)) →
    ∀ i ev m kind, FrontierSearchStart ladR v5env ladrho ladO v5T 12 i ev m kind →
      12 + 2 * FGCompose.P v5T ≤ ev.time →
      FrontierRepairAllowance ladR v5env ladrho ladO v5T ladI 12 1 4 ρbar
        (ev.time + 3 * v5T.delta) := by
  intro rG ρbar h1 h2 hal i ev m kind _ _
  have hr := ladfirst h1 h2
  subst hr
  exact ladallow ρbar _ (ladallow30 hal)

/-! Leaves of the full search on `lad` that are not named above. -/

private theorem ladawake : ∀ y ∈ ladrho.honest, ∀ t, v5env.t_GST ≤ t → t ≤ ladrho.horizon →
    v5env.awake y t = true := fun _ _ _ _ _ => rfl

private theorem ladjoinedTick : ∀ iy y t, y ∈ ladrho.honest →
    ladrho.events[iy]? = some (.tick y t) → t ≤ ladrho.horizon →
    v5env.t_GST ≤ slotStartZ v5T (((slotAt v5T t : Slot) : Int) - 1) →
    (fun _ => true) (ladP.clock (ladrho.stateBefore v5env iy y) t) = true :=
  fun _ _ _ _ _ _ _ => rfl

private theorem ladreceiptHeld : ∀ W d y, y ∈ ladrho.honest → ladreceipt (v5erase W) d y →
    W ∈ (ladR.core (ladrho.stateBeforeTime v5env d y)).fg.TF := by
  intro W d y _ h
  obtain ⟨W', he, hW'⟩ := h
  exact v5erase_inj he ▸ hW'

private theorem ladJst : v5env.t_GST ≤ (12 : Time) := by decide
private theorem ladG : 4 * v5T.delta ≤ (4 : Time) := by decide

private theorem ladsourceParent : PromotionSourceParent ladR v5env ladrho ladO v5T ladI 12 := by
  intro u m J contested r s X x K _ _ _ _ _ _ _ h
  exact (ladsrc h).elim

private theorem ladprogressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin 1)),
    BatchPrem ladR ladS ladO v5T v5env ladrho ladI ladD v5E laddecode id (fun _ => [])
      (fun _ => []) ladparentFG ladparentHeight ladvalidFor 1 .progress r height U X →
    (ladO.height X.parent).h = height → ProgressCoveredByChild v5E ladO.height X U height :=
  fun _ _ _ _ h _ => (ladnoBatch h).elim

private theorem ladquorum : ∃ Q : Finset (Fin 1),
    (∀ i ∈ Q, safetyHolder ladS ladrho i ∈ ladrho.honest) ∧ v5E.q ≤ v5E.weightOf Q :=
  ⟨{0}, fun _ _ => Finset.mem_singleton_self _, by decide⟩

private theorem ladentryAgreement : ∀ r x y K L, x ∈ ladrho.honest → y ∈ ladrho.honest →
    actionSourceFG ladR v5env ladrho v5T x r = some (some K) →
    actionSourceFG ladR v5env ladrho v5T y r = some (some L) →
    (ladO.height K).T_h.root = (ladO.height L).T_h.root →
    (ladO.height K).T_h = (ladO.height L).T_h := by
  intro r x y K L _ _ hK
  exact (ladsrc hK).elim

private theorem ladsourceSlot : ∀ r x K, x ∈ ladrho.honest →
    actionSourceFG ladR v5env ladrho v5T x r = some (some K) → K.slot ≤ r * v5T.roundSlots := by
  intro r x K _ hK
  exact (ladsrc hK).elim

private theorem ladancestorSlot : ∀ r x K A, x ∈ ladrho.honest →
    actionSourceFG ladR v5env ladrho v5T x r = some (some K) → FGBlock.Preceq A K →
    A.slot ≤ K.slot := by
  intro r x K A _ hK
  exact (ladsrc hK).elim

private theorem ladgateCopy : ∀ u v m J contested q Q, (12 : Time) ≤ u →
    PhaseInterval ladR v5env ladrho ladO u v m J contested →
    FrontierSeedQualification v5T 1 v5env.t_GST u q → v5T.gate q ≤ v →
    HonestProposal v5env ladrho ladI q Q → ∃ i x Qfg, V2.D.Run.idxBefore ladrho u ≤ i ∧
      i ≤ timeIdx ladrho v ∧ x ∈ ladrho.honest ∧
      Qfg ∈ (ladR.core (ladrho.stateBefore v5env i x)).fg.TF ∧ v5erase Qfg = Q := by
  intro u v m J c q Q hu hp hseed hg _
  exact (ladnoSeed hu hp hseed hg).elim

private theorem ladserviceLeaf : ∀ u v m J contested q Q Qfg, (12 : Time) ≤ u →
    HonestProposal v5env ladrho ladI q Q → v5erase Qfg = Q → (ladO.height Qfg).h = m →
    FrontierProposalService ladR v5env ladrho v5T q Q →
    FrontierSeedQualification v5T 1 v5env.t_GST u q → u ≤ v5T.proposal q →
    PhaseInterval ladR v5env ladrho ladO u (v5T.gate q) m J contested → v5T.gate q ≤ v →
    v ≤ ladrho.horizon →
    (∀ i x, timeIdx ladrho u ≤ i → i ≤ timeIdx ladrho v → x ∈ ladrho.honest →
      (ladR.core (ladrho.stateBefore v5env i x)).fg.h_max ≤ m) →
    FrontierLocalService ladR ladS v5env ladrho ladO v5T ladI ladD.heightPair q Q Qfg m v := by
  intro u v m J c q Q Qfg hu _ _ _ _ hseed _ hp _ _ _
  exact (ladnoSeed hu hp hseed le_rfl).elim

private theorem ladcommon : ∀ u m J contested q Q Qfg r, (12 : Time) ≤ u →
    HonestProposal v5env ladrho ladI q Q → v5erase Qfg = Q →
    FrontierProposalService ladR v5env ladrho v5T q Q →
    FrontierSeedQualification v5T 1 v5env.t_GST u q → u ≤ v5T.proposal q →
    q ≤ r * v5T.roundSlots → (∀ r', q ≤ r' * v5T.roundSlots → r ≤ r') →
    PhaseInterval ladR v5env ladrho ladO u (v5T.action r) m J contested →
    OpeningCovered ladR ladS v5env ladrho ladO.height v5T ladD.heightPair r Q ∧
    ((ladO.height Qfg).h = m - 1 → OpeningEntry ladR v5env ladrho ladO.height v5T r (m - 1) ∨
      ∃ x K, x ∈ ladrho.honest ∧ actionSourceFG ladR v5env ladrho v5T x r = some (some K) ∧
        (ladO.height K).h = m) := by
  intro u m J c (q : Nat) Q Qfg r hu _ _ _ hseed _ hqr _ hp
  have hq2 : q ≤ r * 2 := hqr
  exact (ladnoSeed hu hp hseed (by
    change 4 * ((q : Nat) : Int) + 6 ≤ 8 * ((r : Nat) : Int) + 6
    omega)).elim

private theorem ladjustified : ∀ i x, x ∈ ladrho.honest →
    (ladR.core (ladrho.stateBefore v5env i x)).fg.h_j ≠ 0 →
    ∃ j y r a K, j < i ∧ HonestRowAt ladS v5env ladrho v5T j y r a ∧
      actionSourceFG ladR v5env ladrho v5T y r = some (some K) ∧
      (ladO.height K).T_h = (ladR.core (ladrho.stateBefore v5env i x)).fg.J :=
  fun _ _ _ h => (h rfl).elim

private theorem ladne : ladrho.honest.Nonempty := ⟨(), Finset.mem_singleton_self _⟩

/-- G0 (POSITIVE, Full): the generic full search applied on `lad` with every premise proved. -/
private theorem ladFull :
    FrontierSearchStatement ladR ladS v5env ladrho ladO v5T ladI ladD.heightPair 12 1 4 4 1 :=
  frontierSearch (R := ladR) (S := ladS) (O := ladO) (T := v5T) (E := v5env) (rho := ladrho)
    (I := ladI) (D := ladD) (Ef := v5E) (decodeProposal := laddecode) (bodyErase := id)
    (bodyRows := fun _ => []) (blockWireRows := fun _ => []) (parentFG := ladparentFG)
    (parentHeight := ladparentHeight) (validFor := ladvalidFor) (fold := ladfold) (Jst := 12)
    (leaseSlots := 1) (obs := ladobs) (cert := v5cert) (inv := ladinv) (justif := v5justif)
    (keep := ladkeep) (positive := by decide) (coreLaws := ladcore)
    (erasePreceq := fun h => v5erase_mono h) (joined := fun _ => true) (receipt := ladreceipt)
    (chainRows := fun _ _ => ladAllRows) (G := 4) (ΔF := 1) (deltaT := 4)
    (hT := v5TLaws) (hk := le_rfl) (crossing := ladcrossing) (schedule := ladschedule) (mono :=
      ladmono) (awake := ladawake) (joinedTick := ladjoinedTick) (readyCut := ladready)
      (hServices := ladservices) (receiptHeld := ladreceiptHeld) (faultWeight := ladfault)
      (deltaF := le_rfl) (hdelta := rfl) (gap := ladgap) (hJst := ladJst) (hG := ladG)
      (slotProposal := ladslot) (read := ladread) (order := ladorder) (signer := ladsigner)
      (sourceParent := ladsourceParent) (rowsReceipt := ladrowsReceipt) (progressCoverage :=
      ladprogressCoverage) (hfold := v9foldAdvance) (honestQuorum := ladquorum) (entryAgreement
      := ladentryAgreement) (sourceSlot := ladsourceSlot) (ancestorSlot := ladancestorSlot)
      (eraseReflect := v9erase_reflect) (floor := ladfloor) (gateCopy := ladgateCopy) (service :=
      ladserviceLeaf) (common := ladcommon) (heldSlot := ladheldSlot) (proposalSlot :=
      ladproposalSlot) (justifiedSource := ladjustified) (parentFrame := ladparentFrame)
      (eraseParent := v9erase_parent) (capReceipt := ladcapReceipt) (cap := ladcap) (hne :=
      ladne) (transfer := ladtransfer)

/-- Every premise of `ladFull` on the exact run, in the order of the call (42 leaves; the
laws passed as section variables are `ladobs`, `v5cert`, `ladinv`, `v5justif`, `ladkeep`,
`ladcore` and `v5erase_mono`). -/
private theorem ladFull_premises_sat :
    (FGTimingLaws v5T) ∧
    (1 ≤ 1) ∧
    (RXing ladR v5env ladrho ladO) ∧
    (V2.D.ScheduleWellFormed v5env ladrho) ∧
    (FGRunOrderLaws v5env ladrho ladR) ∧
    (∀ y ∈ ladrho.honest, ∀ t, v5env.t_GST ≤ t → t ≤ ladrho.horizon → v5env.awake y t = true) ∧
    (∀ iy y t, y ∈ ladrho.honest → ladrho.events[iy]? = some (.tick y t) → t ≤ ladrho.horizon →
      v5env.t_GST ≤ slotStartZ v5T (((slotAt v5T t : Slot) : Int) - 1) → (fun _ => true)
      (ladP.clock (ladrho.stateBefore v5env iy y) t) = true) ∧
    (∀ t, 12 ≤ t → v5env.t_GST ≤ slotStartZ v5T (((slotAt v5T t : Slot) : Int) - 1)) ∧
    (∀ i (ev : V2.Event Unit ladP.Object) m, ladrho.events[i]? = some ev → 12 ≤ ev.time → 1 ≤ m →
      frontierAtIdx ladR v5env ladrho (i + 1) = m → ev.time + v5T.delta ≤ ladrho.horizon →
      PhaseWitnessReceiptScope ladR v5env ladrho ladO (fun _ => true) ladreceipt (i + 1) m
      (ev.time + v5T.delta)) ∧
    (∀ W d y, y ∈ ladrho.honest → ladreceipt (ladR.erase W) d y → W ∈ (ladR.core
      (ladrho.stateBeforeTime v5env d y)).fg.TF) ∧
    (v5E.weightOf (historyFaulty ladS ladrho) < v5E.q) ∧
    (v5env.Δ ≤ 1) ∧
    (v5env.Δ = v5T.delta) ∧
    (∀ t, v5env.t_GST ≤ t → t + 4 ≤ ladrho.horizon → ∃ s, t < v5T.proposal s ∧ v5T.proposal s ≤ t
      + 4 ∧ Gen.V2.Duty.HonestSlot ladrho ladI s) ∧
    (v5env.t_GST ≤ 12) ∧
    (4 * v5T.delta ≤ 4) ∧
    (PromotionSlotProposal ladR v5env ladrho v5T ladI) ∧
    (PromotionProposalRead ladR ladS v5env ladrho ladO ladI laddecode id (fun _ => [])
      ladparentFG ladparentHeight ladvalidFor ladfold) ∧
    (PromotionRowOrder ladR v5env ladrho ladO ladI) ∧
    (PromotionRowSigner ladS v5env ladrho v5T ladD) ∧
    (PromotionSourceParent ladR v5env ladrho ladO v5T ladI 12) ∧
    (TRowsReceipt ladR ladS v5env ladrho v5T (fun _ => []) 1) ∧
    (∀ (r height : Nat) (U X : FGBlock (Fin 1)), BatchPrem ladR ladS ladO v5T v5env ladrho ladI
      ladD v5E laddecode id (fun _ => []) (fun _ => []) ladparentFG ladparentHeight ladvalidFor 1
      .progress r height U X → (ladO.height X.parent).h = height → ProgressCoveredByChild v5E
      ladO.height X U height) ∧
    (ProgressFoldAdvance v5E ladO.height 4) ∧
    (∃ Q : Finset (Fin 1), (∀ i ∈ Q, safetyHolder ladS ladrho i ∈ ladrho.honest) ∧ v5E.q ≤
      v5E.weightOf Q) ∧
    (∀ r x y K L, x ∈ ladrho.honest → y ∈ ladrho.honest → actionSourceFG ladR v5env ladrho v5T x
      r = some (some K) → actionSourceFG ladR v5env ladrho v5T y r = some (some L) → (ladO.height
      K).T_h.root = (ladO.height L).T_h.root → (ladO.height K).T_h = (ladO.height L).T_h) ∧
    (∀ r x K, x ∈ ladrho.honest → actionSourceFG ladR v5env ladrho v5T x r = some (some K) →
      K.slot ≤ r * v5T.roundSlots) ∧
    (∀ r x K A, x ∈ ladrho.honest → actionSourceFG ladR v5env ladrho v5T x r = some (some K) →
      FGBlock.Preceq A K → A.slot ≤ K.slot) ∧
    (∀ A B : FGBlock (Fin 1), Block.Preceq (ladR.erase A) (ladR.erase B) → FGBlock.Preceq A B) ∧
    (AttemptProposalFloor ladR v5env ladrho ladO v5T ladI 12) ∧
    (∀ u v m J contested q Q, 12 ≤ u → PhaseInterval ladR v5env ladrho ladO u v m J contested →
      FrontierSeedQualification v5T 1 v5env.t_GST u q → v5T.gate q ≤ v → HonestProposal v5env
      ladrho ladI q Q → ∃ i x Qfg, V2.D.Run.idxBefore ladrho u ≤ i ∧ i ≤ timeIdx ladrho v ∧ x ∈
      ladrho.honest ∧ Qfg ∈ (ladR.core (ladrho.stateBefore v5env i x)).fg.TF ∧ ladR.erase Qfg =
      Q) ∧
    (∀ u v m J contested q Q Qfg, 12 ≤ u → HonestProposal v5env ladrho ladI q Q → ladR.erase Qfg
      = Q → (ladO.height Qfg).h = m → FrontierProposalService ladR v5env ladrho v5T q Q →
      FrontierSeedQualification v5T 1 v5env.t_GST u q → u ≤ v5T.proposal q → PhaseInterval ladR
      v5env ladrho ladO u (v5T.gate q) m J contested → v5T.gate q ≤ v → v ≤ ladrho.horizon → (∀ i
      x, timeIdx ladrho u ≤ i → i ≤ timeIdx ladrho v → x ∈ ladrho.honest → (ladR.core
      (ladrho.stateBefore v5env i x)).fg.h_max ≤ m) → FrontierLocalService ladR ladS v5env ladrho
      ladO v5T ladI ladD.heightPair q Q Qfg m v) ∧
    (∀ u m J contested q Q Qfg r, 12 ≤ u → HonestProposal v5env ladrho ladI q Q → ladR.erase Qfg
      = Q → FrontierProposalService ladR v5env ladrho v5T q Q → FrontierSeedQualification v5T 1
      v5env.t_GST u q → u ≤ v5T.proposal q → q ≤ r * v5T.roundSlots → (∀ r', q ≤ r' *
      v5T.roundSlots → r ≤ r') → PhaseInterval ladR v5env ladrho ladO u (v5T.action r) m J
      contested → OpeningCovered ladR ladS v5env ladrho ladO.height v5T ladD.heightPair r Q ∧
      ((ladO.height Qfg).h = m - 1 → OpeningEntry ladR v5env ladrho ladO.height v5T r (m - 1) ∨ ∃
      x K, x ∈ ladrho.honest ∧ actionSourceFG ladR v5env ladrho v5T x r = some (some K) ∧
      (ladO.height K).h = m)) ∧
    (∀ i x A K, K ∈ (ladR.core (ladrho.stateBefore v5env i x)).fg.TF → FGBlock.Preceq A K →
      A.slot ≤ K.slot) ∧
    (∀ q Q K, HonestProposal v5env ladrho ladI q Q → ladR.erase K = Q → K.slot = q) ∧
    (∀ i x, x ∈ ladrho.honest → (ladR.core (ladrho.stateBefore v5env i x)).fg.h_j ≠ 0 → ∃ j y r a
      K, j < i ∧ HonestRowAt ladS v5env ladrho v5T j y r a ∧ actionSourceFG ladR v5env ladrho v5T
      y r = some (some K) ∧ (ladO.height K).T_h = (ladR.core (ladrho.stateBefore v5env i
      x)).fg.J) ∧
    (∀ q Q, HonestProposal v5env ladrho ladI q Q → ∃ j, ladrho.events[j]? = some (.tick
      (V2.D.proposerOf ladrho ladI q) (v5T.proposal q)) ∧ ∀ Qfg, ladR.erase Qfg = Q →
      FGBlock.Preceq (ladO.controls (ladrho.stateBefore v5env j (V2.D.proposerOf ladrho ladI
      q))).Z Qfg.parent) ∧
    (∀ X : FGBlock (Fin 1), (ladR.erase X).parent = ladR.erase X.parent) ∧
    (PromotionCapReceipt ladR v5env ladrho ladO v5T ladI) ∧
    (RCap ladR ladS v5env ladrho ladO v5T (fun a => namedEntry (ladD.heightPair a)) (fun _ _ =>
      ladAllRows)) ∧
    (ladrho.honest.Nonempty) ∧
    (∀ rG ρbar, 12 ≤ v5T.action rG → (∀ r, 12 ≤ v5T.action r → rG ≤ r) → FrontierRepairAllowance
      ladR v5env ladrho ladO v5T ladI 12 1 4 ρbar (v5T.action (rG + 2)) → ∀ i ev m kind,
      FrontierSearchStart ladR v5env ladrho ladO v5T 12 i ev m kind → 12 + 2 * FGCompose.P v5T ≤
      ev.time → FrontierRepairAllowance ladR v5env ladrho ladO v5T ladI 12 1 4 ρbar (ev.time + 3
      * v5T.delta)) :=
  ⟨v5TLaws, le_rfl, ladcrossing, ladschedule, ladmono, ladawake, ladjoinedTick, ladready,
    ladservices, ladreceiptHeld, ladfault, le_rfl, rfl, ladgap, ladJst, ladG, ladslot, ladread,
    ladorder, ladsigner, ladsourceParent, ladrowsReceipt, ladprogressCoverage, v9foldAdvance,
    ladquorum, ladentryAgreement, ladsourceSlot, ladancestorSlot, v9erase_reflect, ladfloor,
    ladgateCopy, ladserviceLeaf, ladcommon, ladheldSlot, ladproposalSlot, ladjustified,
    ladparentFrame, v9erase_parent, ladcapReceipt, ladcap, ladne, ladtransfer⟩

private theorem ladM : (4 : Nat) = honestFrontier ladR v5env ladrho 30 := by
  rw [reset_inclusive_frontier (R := ladR) (E := v5env) (rho := ladrho) ladschedule 30,
    ladfront]
  decide +kernel

private theorem ladrowHeight {j : Nat} {y : Unit} {r : Nat} {a : Row (Fin 1)} {h : Nat}
    {e : BlockId} (hrow : HonestRowAt ladS v5env ladrho v5T j y r a)
    (hent : namedEntry (ladD.heightPair a) = some (h, e)) : r ≤ 20 ∧ h = r + 1 := by
  obtain ⟨hr, rfl⟩ := ladrows hrow
  have h2 : (r + 1, (⟨900 + r⟩ : BlockId)) = (h, e) := Option.some.inj hent
  exact ⟨hr, (congrArg Prod.fst h2).symm⟩

/-- The old-row cap of the statement at the cut: rows sent by time 30 name heights 1..4. -/
private theorem ladrowCap : ∀ j y r a h e t, HonestRowAt ladS v5env ladrho v5T j y r a →
    ladrho.events[j]? = some (.tick y t) → t ≤ (30 : Time) →
    namedEntry (ladD.heightPair a) = some (h, e) → h ≤ 4 := by
  intro j y r a (h : Nat) e (t : Int) hrow hj ht hent
  obtain ⟨_, hh⟩ := ladrowHeight hrow hent
  have hj' := hrow.2.1
  rw [hj] at hj'
  have ht' : t = 8 * ((r : Nat) : Int) + 6 := (V2.Event.tick.inj (Option.some.inj hj')).2
  have ht30 : t ≤ 30 := ht
  change (h : Nat) ≤ 4
  omega

private abbrev ladHR (r h : Nat) : Prop :=
  HeightRow ladS v5env ladrho v5T (fun a => namedEntry (ladD.heightPair a)) r h

/-- A height-5 row is exactly the row of action 4 (time 38). -/
private theorem ladrow5 (r : Nat) : ladHR r 5 ↔ r = 4 := by
  constructor
  · rintro ⟨j, y, a, e, hrow, hent⟩
    obtain ⟨_, hh⟩ := ladrowHeight hrow hent
    omega
  · rintro rfl
    exact ⟨ladti 38, (), ladrow 4, ⟨904⟩, ladrowAt 4 (by decide), rfl⟩

/-- Every first rise from the cut is the delivery of p_4 (index 44, time 37). -/
private theorem ladriseWitness {j : Nat} {ev : V2.Event Unit ladP.Object}
    (hj : timeIdx ladrho 30 ≤ j) (hev : ladrho.events[j]? = some ev)
    (hrise : 4 < frontierAtIdx ladR v5env ladrho (j + 1))
    (hcap : ∀ k, timeIdx ladrho 30 ≤ k → k ≤ j → frontierAtIdx ladR v5env ladrho k ≤ 4) :
    j = 44 ∧ ev = ladDel (ladp 4) 37 := by
  have hti : timeIdx ladrho 30 = 37 := by decide +kernel
  have h1 : ladhmax (ladcnt 44) = 4 := by decide +kernel
  have h2 : ladhmax (ladcnt (44 + 1)) = 5 := by decide +kernel
  have hjd : j = 44 := by
    by_contra hne
    rcases Nat.lt_or_ge j 44 with hlt | hge
    · rw [ladfront] at hrise
      have := ladhmax_mono (ladcnt_mono (show j + 1 ≤ 44 by omega))
      omega
    · have := hcap (44 + 1) (by omega) (by omega)
      rw [ladfront] at this
      omega
  subst hjd
  have h44 : ladrho.events[44]? = some (ladDel (ladp 4) 37) := by decide +kernel
  rw [h44] at hev
  exact ⟨rfl, (Option.some.inj hev).symm⟩

/-- Instantiation guards of the statement on `lad` (rG = 1, cut 30, M = 4): the first action
round, the cut delay, the frontier, the old-row cap, the allowances 7 and 8 at the cut (an
allowance of 6 fails there), and both complete deadlines within the horizon 168. -/
private theorem ladSearch_premises_sat :
    (12 : Time) ≤ v5T.action 1 ∧ (∀ r, (12 : Time) ≤ v5T.action r → 1 ≤ r) ∧
    (30 : Time) = v5T.action (1 + 2) ∧ (12 : Time) + 2 * FGCompose.P v5T ≤ 30 ∧
    (4 : Nat) = honestFrontier ladR v5env ladrho 30 ∧
    FrontierRepairAllowance ladR v5env ladrho ladO v5T ladI 12 1 4 7 30 ∧
    FrontierRepairAllowance ladR v5env ladrho ladO v5T ladI 12 1 4 8 30 ∧
    ¬ FrontierRepairAllowance ladR v5env ladrho ladO v5T ladI 12 1 4 6 30 ∧
    (30 : Time) + frontierSearchRiseBudget v5T 4 1 7 + frontierSearchRowBudget v5T 4 1 7 = 161 ∧
    (30 : Time) + frontierSearchRiseBudget v5T 4 1 8 + frontierSearchRowBudget v5T 4 1 8 = 167 ∧
    (167 : Time) ≤ ladrho.horizon ∧ ladrho.honest.Nonempty := by
  refine ⟨by decide, fun r hr => ?_, by decide, by decide, ladM, ladallow 7 30 (by decide),
    ladallow 8 30 (by decide), fun h => absurd (ladallow30 h) (by decide), by decide +kernel,
    by decide +kernel, by decide, ladne⟩
  have : (12 : Int) ≤ 8 * ((r : Nat) : Int) + 6 := hr
  omega

/-- G0 inspection (Full): the selected rise is the p_4 delivery (index 44, time 37); one
first row (action 4, time 38) serves both allowances 7 and 8. -/
private theorem ladFullExit :
    (∃ j ev, timeIdx ladrho 30 ≤ j ∧ ladrho.events[j]? = some ev ∧
      ev.time ≤ 30 + frontierSearchRiseBudget v5T 4 1 7 ∧
      j = 44 ∧ ev = ladDel (ladp 4) 37) ∧
    ∃ rStar, ladHR rStar 5 ∧
      (∀ r, ladHR r 5 → rStar ≤ r) ∧ rStar = 4 ∧
      ∀ ρ : Time, ρ = 7 ∨ ρ = 8 → ∃ j ev, ladrho.events[j]? = some ev ∧
        j = 44 ∧ ev.time = 37 ∧
        v5T.action rStar ≤ ev.time + frontierSearchRowBudget v5T 4 1 ρ := by
  obtain ⟨h1, h2, h3, h4, h5, ha7, ha8, _, hd7, hd8, hH, _⟩ := ladSearch_premises_sat
  obtain ⟨hrise, hrow⟩ := (FrontierSearchStatement_def ladR ladS v5env ladrho ladO v5T ladI
    ladD.heightPair 12 1 4 4 1).mp ladFull rfl ⟨by decide⟩ 1 30 4 h1 h2 h3 h4 h5 ladrowCap
  refine ⟨?_, ?_⟩
  · obtain ⟨j, ev, hj, hev, ht, hh, hcap⟩ := hrise 7 ha7 (by decide +kernel)
    obtain ⟨rfl, rfl⟩ := ladriseWitness hj hev hh hcap
    exact ⟨_, _, hj, hev, ht, rfl, rfl⟩
  · obtain ⟨rStar, hr, hfirst, hall⟩ := hrow ⟨7, ha7, by decide +kernel⟩
    have hr4 : rStar = 4 := (ladrow5 rStar).mp hr
    refine ⟨rStar, hr, hfirst, hr4, ?_⟩
    rintro ρ (rfl | rfl)
    · obtain ⟨j, ev, hj, hev, _, hh, hcap, hrowt⟩ := hall 7 ha7 (by decide +kernel)
      obtain ⟨rfl, rfl⟩ := ladriseWitness hj hev hh hcap
      exact ⟨_, _, hev, rfl, rfl, hrowt⟩
    · obtain ⟨j, ev, hj, hev, _, hh, hcap, hrowt⟩ := hall 8 ha8 (by decide +kernel)
      obtain ⟨rfl, rfl⟩ := ladriseWitness hj hev hh hcap
      exact ⟨_, _, hev, rfl, rfl, hrowt⟩

/-- G0 (complete nonempty task chain): the cut start, the rise task from it, and the row
task from the actual rise event, each generic task applied with every premise proved. -/
private theorem ladChain :
    ∃ i ev kind, FrontierSearchStart ladR v5env ladrho ladO v5T 12 i ev 4 kind ∧
      ev.time = 30 ∧ timeIdx ladrho 30 = i + 1 ∧
      FrontierRiseBy ladR v5env ladrho i 4 (30 + frontierSearchRiseBudget v5T 4 1 7) ∧
      ∃ kind', FrontierSearchStart ladR v5env ladrho ladO v5T 12 44 (ladDel (ladp 4) 37) 5
          kind' ∧
        FirstHeightRowBy ladS v5env ladrho v5T ladD.heightPair 5
          (37 + frontierSearchRowBudget v5T 4 1 7) := by
  obtain ⟨h1, h2, h3, h4, h5, _, _, _, _, _, _, _⟩ := ladSearch_premises_sat
  obtain ⟨i, ev, kind, hstart, ht, hidx⟩ := frontierSearch_cut_start (R := ladR) (O := ladO)
    (T := v5T) (E := v5env) (rho := ladrho) (Ef := v5E) (Jst := 12) (cert := v5cert)
    (inv := ladinv) v5TLaws ladschedule ladne ladawake rfl ladJst h1 h2 h3 h4 h5 (by decide)
  have hrise : FrontierRiseBy ladR v5env ladrho i 4
      (ev.time + frontierSearchRiseBudget v5T 4 1 7) :=
    frontierSearch_rise_task (R := ladR) (S := ladS) (O := ladO) (T := v5T) (E := v5env)
    (rho := ladrho)
    (I := ladI) (D := ladD) (Ef := v5E) (decodeProposal := laddecode) (bodyErase := id)
    (bodyRows := fun _ => []) (blockWireRows := fun _ => []) (parentFG := ladparentFG)
    (parentHeight := ladparentHeight) (validFor := ladvalidFor) (fold := ladfold) (Jst := 12)
    (leaseSlots := 1) (obs := ladobs) (cert := v5cert) (inv := ladinv) (justif := v5justif)
    (keep := ladkeep) (positive := by decide) (coreLaws := ladcore)
    (erasePreceq := fun h => v5erase_mono h) (joined := fun _ => true) (receipt := ladreceipt)
      (G := 4) (ΔF := 1) (ρbar := 7) (deltaT := 4)
    (hT := v5TLaws) (hk := le_rfl) (crossing := ladcrossing) (schedule := ladschedule) (mono :=
      ladmono) (awake := ladawake) (joinedTick := ladjoinedTick) (readyCut := ladready)
      (hServices := ladservices) (receiptHeld := ladreceiptHeld) (faultWeight := ladfault)
      (deltaF := le_rfl) (hdelta := rfl) (gap := ladgap) (hJst := ladJst) (hG := ladG)
      (slotProposal := ladslot) (read := ladread) (order := ladorder) (signer := ladsigner)
      (sourceParent := ladsourceParent) (hδ := rfl) (hbound := ⟨by decide⟩) (rowsReceipt :=
      ladrowsReceipt) (progressCoverage := ladprogressCoverage) (hfold := v9foldAdvance)
      (honestQuorum := ladquorum) (entryAgreement := ladentryAgreement) (sourceSlot :=
      ladsourceSlot) (ancestorSlot := ladancestorSlot) (eraseReflect := v9erase_reflect) (floor
      := ladfloor) (gateCopy := ladgateCopy) (service := ladserviceLeaf) (common := ladcommon)
      (heldSlot := ladheldSlot) (proposalSlot := ladproposalSlot) (justifiedSource :=
      ladjustified) (parentFrame := ladparentFrame) (allowance := fun _ _ _ _ _ _ => ladallow 7 _
      (by decide)) (eraseParent := v9erase_parent) (capReceipt := ladcapReceipt)
      (hstart := hstart) (hdelay := by rw [ht]; decide) (hhor := by rw [ht]; decide +kernel)
  rw [ht] at hrise
  obtain ⟨kind', hkind'⟩ := frontierSearch_phase_exists ladR ladO v5env ladrho (44 + 1) 5
  have hev : ladrho.events[44]? = some (ladDel (ladp 4) 37) := by decide +kernel
  have hstart' : FrontierSearchStart ladR v5env ladrho ladO v5T 12 44 (ladDel (ladp 4) 37) 5
      kind' :=
    (FrontierSearchStart_def ladR v5env ladrho ladO v5T 12 44 _ 5 kind').mpr
      ⟨hev, by decide, Or.inl (Or.inl (by rw [ladfront, ladfront]; decide +kernel)),
        by rw [ladfront]; decide +kernel, by decide, hkind'⟩
  exact ⟨i, ev, kind, hstart, ht, hidx, hrise, kind', hstart',
    frontierSearch_row_task (R := ladR) (S := ladS) (O := ladO) (T := v5T) (E := v5env)
    (rho := ladrho)
    (I := ladI) (D := ladD) (Ef := v5E) (decodeProposal := laddecode) (bodyErase := id)
    (bodyRows := fun _ => []) (blockWireRows := fun _ => []) (parentFG := ladparentFG)
    (parentHeight := ladparentHeight) (validFor := ladvalidFor) (fold := ladfold) (Jst := 12)
    (leaseSlots := 1) (obs := ladobs) (cert := v5cert) (inv := ladinv) (justif := v5justif)
    (keep := ladkeep) (positive := by decide) (coreLaws := ladcore)
    (erasePreceq := fun h => v5erase_mono h) (joined := fun _ => true) (receipt := ladreceipt)
      (chainRows := fun _ _ => ladAllRows) (G := 4) (ΔF := 1) (ρbar := 7) (deltaT := 4)
    (hT := v5TLaws) (hk := le_rfl) (crossing := ladcrossing) (schedule := ladschedule) (mono :=
      ladmono) (awake := ladawake) (joinedTick := ladjoinedTick) (readyCut := ladready)
      (hServices := ladservices) (receiptHeld := ladreceiptHeld) (faultWeight := ladfault)
      (deltaF := le_rfl) (hdelta := rfl) (gap := ladgap) (hJst := ladJst) (hG := ladG)
      (slotProposal := ladslot) (read := ladread) (order := ladorder) (signer := ladsigner)
      (sourceParent := ladsourceParent) (hδ := rfl) (hbound := ⟨by decide⟩) (rowsReceipt :=
      ladrowsReceipt) (progressCoverage := ladprogressCoverage) (hfold := v9foldAdvance)
      (honestQuorum := ladquorum) (entryAgreement := ladentryAgreement) (sourceSlot :=
      ladsourceSlot) (ancestorSlot := ladancestorSlot) (eraseReflect := v9erase_reflect) (floor
      := ladfloor) (gateCopy := ladgateCopy) (service := ladserviceLeaf) (common := ladcommon)
      (heldSlot := ladheldSlot) (proposalSlot := ladproposalSlot) (justifiedSource :=
      ladjustified) (parentFrame := ladparentFrame) (allowance := fun _ _ _ _ _ _ => ladallow 7 _
      (by decide)) (cap := ladcap)
      (hstart := hstart') (hdelay := by decide) (hhor := by decide +kernel)⟩

/-- Controls (separate rise and row horizon failures). No rise from the cut exists by 36;
the first height-5 row exists by 38 and not by 37, the time of the rise. With allowance 30
the rise guard holds and the row guard fails: the statement gives the rise only. With
allowance 60 the rise guard fails. All other premises are those of `ladFull`. -/
private theorem ladHorizon :
    (¬ ∃ j ev, timeIdx ladrho 30 ≤ j ∧ ladrho.events[j]? = some ev ∧ ev.time ≤ 36 ∧
      4 < frontierAtIdx ladR v5env ladrho (j + 1) ∧
      ∀ k, timeIdx ladrho 30 ≤ k → k ≤ j → frontierAtIdx ladR v5env ladrho k ≤ 4) ∧
    FirstHeightRowBy ladS v5env ladrho v5T ladD.heightPair 5 38 ∧
    ¬ FirstHeightRowBy ladS v5env ladrho v5T ladD.heightPair 5 37 ∧
    (30 : Time) + frontierSearchRiseBudget v5T 4 1 30 ≤ ladrho.horizon ∧
    ¬ (30 : Time) + frontierSearchRiseBudget v5T 4 1 30 + frontierSearchRowBudget v5T 4 1 30 ≤
      ladrho.horizon ∧
    ¬ (30 : Time) + frontierSearchRiseBudget v5T 4 1 60 ≤ ladrho.horizon ∧
    ∃ j ev, ladrho.events[j]? = some ev ∧ j = 44 ∧
      ev.time ≤ 30 + frontierSearchRiseBudget v5T 4 1 30 := by
  obtain ⟨h1, h2, h3, h4, h5, _, _, _, _, _, _, _⟩ := ladSearch_premises_sat
  obtain ⟨hrise, _⟩ := (FrontierSearchStatement_def ladR ladS v5env ladrho ladO v5T ladI
    ladD.heightPair 12 1 4 4 1).mp ladFull rfl ⟨by decide⟩ 1 30 4 h1 h2 h3 h4 h5 ladrowCap
  refine ⟨?_, ?_, ?_, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  · rintro ⟨j, ev, hj, hev, ht, hh, hcap⟩
    obtain ⟨rfl, rfl⟩ := ladriseWitness hj hev hh hcap
    exact absurd ht (by decide)
  · exact ⟨4, (ladrow5 4).mpr rfl, fun r hr => ((ladrow5 r).mp hr).ge, by decide⟩
  · rintro ⟨r, hr, _, ht⟩
    have hr4 := (ladrow5 r).mp hr
    subst hr4
    exact absurd ht (by decide)
  · obtain ⟨j, ev, hj, hev, ht, hh, hcap⟩ := hrise 30 (ladallow 30 30 (by decide))
      (by decide +kernel)
    obtain ⟨rfl, rfl⟩ := ladriseWitness hj hev hh hcap
    exact ⟨_, _, hev, rfl, ht⟩

/-! G0 for the start-family companion (`FrontierSearchFamilyStatement`) on `lad`. -/

/-- G0 (POSITIVE, companion): `frontierSearch_family` applied on `lad` for the allowance 7,
with every premise proved and no transfer. -/
private theorem ladFamily :
    FrontierSearchFamilyStatement ladR ladS v5env ladrho ladO v5T ladI ladD.heightPair 12 1 4
      4 1 7 :=
  frontierSearch_family (R := ladR) (S := ladS) (O := ladO) (T := v5T) (E := v5env) (rho := ladrho)
    (I := ladI) (D := ladD) (Ef := v5E) (decodeProposal := laddecode) (bodyErase := id)
    (bodyRows := fun _ => []) (blockWireRows := fun _ => []) (parentFG := ladparentFG)
    (parentHeight := ladparentHeight) (validFor := ladvalidFor) (fold := ladfold) (Jst := 12)
    (leaseSlots := 1) (obs := ladobs) (cert := v5cert) (inv := ladinv) (justif := v5justif)
    (keep := ladkeep) (positive := by decide) (coreLaws := ladcore)
    (erasePreceq := fun h => v5erase_mono h) (joined := fun _ => true) (receipt := ladreceipt)
    (chainRows := fun _ _ => ladAllRows) (G := 4) (ΔF := 1) (deltaT := 4)
    (hT := v5TLaws) (hk := le_rfl) (crossing := ladcrossing) (schedule := ladschedule) (mono :=
      ladmono) (awake := ladawake) (joinedTick := ladjoinedTick) (readyCut := ladready)
      (hServices := ladservices) (receiptHeld := ladreceiptHeld) (faultWeight := ladfault)
      (deltaF := le_rfl) (hdelta := rfl) (gap := ladgap) (hJst := ladJst) (hG := ladG)
      (slotProposal := ladslot) (read := ladread) (order := ladorder) (signer := ladsigner)
      (sourceParent := ladsourceParent) (rowsReceipt := ladrowsReceipt) (progressCoverage :=
      ladprogressCoverage) (hfold := v9foldAdvance) (honestQuorum := ladquorum) (entryAgreement
      := ladentryAgreement) (sourceSlot := ladsourceSlot) (ancestorSlot := ladancestorSlot)
      (eraseReflect := v9erase_reflect) (floor := ladfloor) (gateCopy := ladgateCopy) (service :=
      ladserviceLeaf) (common := ladcommon) (heldSlot := ladheldSlot) (proposalSlot :=
      ladproposalSlot) (justifiedSource := ladjustified) (parentFrame := ladparentFrame)
      (eraseParent := v9erase_parent) (capReceipt := ladcapReceipt) (cap := ladcap) (hne :=
      ladne) 7

/-- Every premise of `ladFamily` on the exact run (41 leaves, in the order of the call). -/
private theorem ladFamily_premises_sat :
    (FGTimingLaws v5T) ∧
    (1 ≤ 1) ∧
    (RXing ladR v5env ladrho ladO) ∧
    (V2.D.ScheduleWellFormed v5env ladrho) ∧
    (FGRunOrderLaws v5env ladrho ladR) ∧
    (∀ y ∈ ladrho.honest, ∀ t, v5env.t_GST ≤ t → t ≤ ladrho.horizon → v5env.awake y t = true) ∧
    (∀ iy y t, y ∈ ladrho.honest → ladrho.events[iy]? = some (.tick y t) → t ≤ ladrho.horizon →
      v5env.t_GST ≤ slotStartZ v5T (((slotAt v5T t : Slot) : Int) - 1) → (fun _ => true)
      (ladP.clock (ladrho.stateBefore v5env iy y) t) = true) ∧
    (∀ t, 12 ≤ t → v5env.t_GST ≤ slotStartZ v5T (((slotAt v5T t : Slot) : Int) - 1)) ∧
    (∀ i (ev : V2.Event Unit ladP.Object) m, ladrho.events[i]? = some ev → 12 ≤ ev.time → 1 ≤ m →
      frontierAtIdx ladR v5env ladrho (i + 1) = m → ev.time + v5T.delta ≤ ladrho.horizon →
      PhaseWitnessReceiptScope ladR v5env ladrho ladO (fun _ => true) ladreceipt (i + 1) m
      (ev.time + v5T.delta)) ∧
    (∀ W d y, y ∈ ladrho.honest → ladreceipt (ladR.erase W) d y → W ∈ (ladR.core
      (ladrho.stateBeforeTime v5env d y)).fg.TF) ∧
    (v5E.weightOf (historyFaulty ladS ladrho) < v5E.q) ∧
    (v5env.Δ ≤ 1) ∧
    (v5env.Δ = v5T.delta) ∧
    (∀ t, v5env.t_GST ≤ t → t + 4 ≤ ladrho.horizon → ∃ s, t < v5T.proposal s ∧ v5T.proposal s ≤ t
      + 4 ∧ Gen.V2.Duty.HonestSlot ladrho ladI s) ∧
    (v5env.t_GST ≤ 12) ∧
    (4 * v5T.delta ≤ 4) ∧
    (PromotionSlotProposal ladR v5env ladrho v5T ladI) ∧
    (PromotionProposalRead ladR ladS v5env ladrho ladO ladI laddecode id (fun _ => [])
      ladparentFG ladparentHeight ladvalidFor ladfold) ∧
    (PromotionRowOrder ladR v5env ladrho ladO ladI) ∧
    (PromotionRowSigner ladS v5env ladrho v5T ladD) ∧
    (PromotionSourceParent ladR v5env ladrho ladO v5T ladI 12) ∧
    (TRowsReceipt ladR ladS v5env ladrho v5T (fun _ => []) 1) ∧
    (∀ (r height : Nat) (U X : FGBlock (Fin 1)), BatchPrem ladR ladS ladO v5T v5env ladrho ladI
      ladD v5E laddecode id (fun _ => []) (fun _ => []) ladparentFG ladparentHeight ladvalidFor 1
      .progress r height U X → (ladO.height X.parent).h = height → ProgressCoveredByChild v5E
      ladO.height X U height) ∧
    (ProgressFoldAdvance v5E ladO.height 4) ∧
    (∃ Q : Finset (Fin 1), (∀ i ∈ Q, safetyHolder ladS ladrho i ∈ ladrho.honest) ∧ v5E.q ≤
      v5E.weightOf Q) ∧
    (∀ r x y K L, x ∈ ladrho.honest → y ∈ ladrho.honest → actionSourceFG ladR v5env ladrho v5T x
      r = some (some K) → actionSourceFG ladR v5env ladrho v5T y r = some (some L) → (ladO.height
      K).T_h.root = (ladO.height L).T_h.root → (ladO.height K).T_h = (ladO.height L).T_h) ∧
    (∀ r x K, x ∈ ladrho.honest → actionSourceFG ladR v5env ladrho v5T x r = some (some K) →
      K.slot ≤ r * v5T.roundSlots) ∧
    (∀ r x K A, x ∈ ladrho.honest → actionSourceFG ladR v5env ladrho v5T x r = some (some K) →
      FGBlock.Preceq A K → A.slot ≤ K.slot) ∧
    (∀ A B : FGBlock (Fin 1), Block.Preceq (ladR.erase A) (ladR.erase B) → FGBlock.Preceq A B) ∧
    (AttemptProposalFloor ladR v5env ladrho ladO v5T ladI 12) ∧
    (∀ u v m J contested q Q, 12 ≤ u → PhaseInterval ladR v5env ladrho ladO u v m J contested →
      FrontierSeedQualification v5T 1 v5env.t_GST u q → v5T.gate q ≤ v → HonestProposal v5env
      ladrho ladI q Q → ∃ i x Qfg, V2.D.Run.idxBefore ladrho u ≤ i ∧ i ≤ timeIdx ladrho v ∧ x ∈
      ladrho.honest ∧ Qfg ∈ (ladR.core (ladrho.stateBefore v5env i x)).fg.TF ∧ ladR.erase Qfg =
      Q) ∧
    (∀ u v m J contested q Q Qfg, 12 ≤ u → HonestProposal v5env ladrho ladI q Q → ladR.erase Qfg
      = Q → (ladO.height Qfg).h = m → FrontierProposalService ladR v5env ladrho v5T q Q →
      FrontierSeedQualification v5T 1 v5env.t_GST u q → u ≤ v5T.proposal q → PhaseInterval ladR
      v5env ladrho ladO u (v5T.gate q) m J contested → v5T.gate q ≤ v → v ≤ ladrho.horizon → (∀ i
      x, timeIdx ladrho u ≤ i → i ≤ timeIdx ladrho v → x ∈ ladrho.honest → (ladR.core
      (ladrho.stateBefore v5env i x)).fg.h_max ≤ m) → FrontierLocalService ladR ladS v5env ladrho
      ladO v5T ladI ladD.heightPair q Q Qfg m v) ∧
    (∀ u m J contested q Q Qfg r, 12 ≤ u → HonestProposal v5env ladrho ladI q Q → ladR.erase Qfg
      = Q → FrontierProposalService ladR v5env ladrho v5T q Q → FrontierSeedQualification v5T 1
      v5env.t_GST u q → u ≤ v5T.proposal q → q ≤ r * v5T.roundSlots → (∀ r', q ≤ r' *
      v5T.roundSlots → r ≤ r') → PhaseInterval ladR v5env ladrho ladO u (v5T.action r) m J
      contested → OpeningCovered ladR ladS v5env ladrho ladO.height v5T ladD.heightPair r Q ∧
      ((ladO.height Qfg).h = m - 1 → OpeningEntry ladR v5env ladrho ladO.height v5T r (m - 1) ∨ ∃
      x K, x ∈ ladrho.honest ∧ actionSourceFG ladR v5env ladrho v5T x r = some (some K) ∧
      (ladO.height K).h = m)) ∧
    (∀ i x A K, K ∈ (ladR.core (ladrho.stateBefore v5env i x)).fg.TF → FGBlock.Preceq A K →
      A.slot ≤ K.slot) ∧
    (∀ q Q K, HonestProposal v5env ladrho ladI q Q → ladR.erase K = Q → K.slot = q) ∧
    (∀ i x, x ∈ ladrho.honest → (ladR.core (ladrho.stateBefore v5env i x)).fg.h_j ≠ 0 → ∃ j y r a
      K, j < i ∧ HonestRowAt ladS v5env ladrho v5T j y r a ∧ actionSourceFG ladR v5env ladrho v5T
      y r = some (some K) ∧ (ladO.height K).T_h = (ladR.core (ladrho.stateBefore v5env i
      x)).fg.J) ∧
    (∀ q Q, HonestProposal v5env ladrho ladI q Q → ∃ j, ladrho.events[j]? = some (.tick
      (V2.D.proposerOf ladrho ladI q) (v5T.proposal q)) ∧ ∀ Qfg, ladR.erase Qfg = Q →
      FGBlock.Preceq (ladO.controls (ladrho.stateBefore v5env j (V2.D.proposerOf ladrho ladI
      q))).Z Qfg.parent) ∧
    (∀ X : FGBlock (Fin 1), (ladR.erase X).parent = ladR.erase X.parent) ∧
    (PromotionCapReceipt ladR v5env ladrho ladO v5T ladI) ∧
    (RCap ladR ladS v5env ladrho ladO v5T (fun a => namedEntry (ladD.heightPair a)) (fun _ _ =>
      ladAllRows)) ∧
    (ladrho.honest.Nonempty) :=
  ⟨v5TLaws, le_rfl, ladcrossing, ladschedule, ladmono, ladawake, ladjoinedTick, ladready,
    ladservices, ladreceiptHeld, ladfault, le_rfl, rfl, ladgap, ladJst, ladG, ladslot, ladread,
    ladorder, ladsigner, ladsourceParent, ladrowsReceipt, ladprogressCoverage, v9foldAdvance,
    ladquorum, ladentryAgreement, ladsourceSlot, ladancestorSlot, v9erase_reflect, ladfloor,
    ladgateCopy, ladserviceLeaf, ladcommon, ladheldSlot, ladproposalSlot, ladjustified,
    ladparentFrame, v9erase_parent, ladcapReceipt, ladcap, ladne⟩

/-- The premises of the companion statement itself on `lad` for the allowance 7: the
allowance is nonnegative and holds at `ev.time + 3Δ` for every actual start (in fact at
every time); with the cut guards of `ladSearch_premises_sat` and the deadline 161 ≤ 168. -/
private theorem ladFamilyStatement_premises_sat :
    (4 : Nat) = 2 * v5T.roundSlots ∧ LivenessBoundW v5T 1 ∧ (0 : Time) ≤ 7 ∧
    (∀ i ev m kind, FrontierSearchStart ladR v5env ladrho ladO v5T 12 i ev m kind →
      (12 : Time) + 2 * FGCompose.P v5T ≤ ev.time →
      FrontierRepairAllowance ladR v5env ladrho ladO v5T ladI 12 1 4 7
        (ev.time + 3 * v5T.delta)) ∧
    (∃ kind, FrontierSearchStart ladR v5env ladrho ladO v5T 12 44 (ladDel (ladp 4) 37) 5
      kind ∧ (12 : Time) + 2 * FGCompose.P v5T ≤ (ladDel (ladp 4) 37).time) ∧
    (30 : Time) + frontierSearchRiseBudget v5T 4 1 7 + frontierSearchRowBudget v5T 4 1 7 ≤
      ladrho.horizon := by
  obtain ⟨_, _, kind, _, _, _, _, kind', hst, _⟩ := ladChain
  exact ⟨rfl, ⟨by decide⟩, by decide, fun _ _ _ _ _ _ => ladallow 7 _ (by decide),
    ⟨kind', hst, by decide⟩, by decide +kernel⟩

/-- G0 inspection (companion): the rise is the p_4 delivery (index 44, time 37) and the
least height-5 row is the row of action 4 (time 38), inside the row deadline. -/
private theorem ladFamilyExit :
    (∃ j ev, ladrho.events[j]? = some ev ∧ j = 44 ∧ ev = ladDel (ladp 4) 37 ∧
      ev.time ≤ 30 + frontierSearchRiseBudget v5T 4 1 7) ∧
    ∃ rStar, ladHR rStar 5 ∧ (∀ r, ladHR r 5 → rStar ≤ r) ∧ rStar = 4 ∧
      ∃ j ev, ladrho.events[j]? = some ev ∧ j = 44 ∧
        v5T.action rStar ≤ ev.time + frontierSearchRowBudget v5T 4 1 7 := by
  obtain ⟨h1, h2, h3, h4, h5, _, _, _, _, _, _, _⟩ := ladSearch_premises_sat
  obtain ⟨hd, hb, hρ, hfam, _, _⟩ := ladFamilyStatement_premises_sat
  obtain ⟨hrise, hrow⟩ := (FrontierSearchFamilyStatement_def ladR ladS v5env ladrho ladO v5T
    ladI ladD.heightPair 12 1 4 4 1 7).mp ladFamily hd hb hρ hfam 1 30 4 h1 h2 h3 h4 h5
    ladrowCap
  refine ⟨?_, ?_⟩
  · obtain ⟨j, ev, hj, hev, ht, hh, hcap⟩ := hrise (by decide +kernel)
    obtain ⟨rfl, rfl⟩ := ladriseWitness hj hev hh hcap
    exact ⟨_, _, hev, rfl, rfl, ht⟩
  · obtain ⟨rStar, hr, hfirst, j, ev, hj, hev, _, hh, hcap, hrowt⟩ := hrow (by decide +kernel)
    obtain ⟨rfl, rfl⟩ := ladriseWitness hj hev hh hcap
    exact ⟨rStar, hr, hfirst, (ladrow5 rStar).mp hr, _, _, hev, rfl, hrowt⟩

/-! Negative for the family premise. Run `ladc` is `lad` with the p_3 delivery moved from 29
to 30, right after the tick of the cut. Same core, observations and timing. The phase
changes at the cut, so the allowance 0 holds there vacuously; at the actual later start
(the p_3 delivery, time 30) it fails at 33, where the phase [33, 36] has no repaired
proposal. The family premise rejects this allowance; only these facts are proved on `ladc`
(the other leaves are not re-proved on it). -/

private noncomputable abbrev ladcrho : V2.D.Run Unit ladP where
  honest := {()}
  horizon := 168
  events := [
    .tick () 0, .tick () 1, .tick () 2, .tick () 3, .tick () 4, ladDel (ladX 1) 4, .tick () 5,
    .tick () 6, .tick () 7, .tick () 8, ladDel (ladX 2) 8, .tick () 9, .tick () 10, .tick () 11,
    .tick () 12, ladDel (ladX 3) 12, .tick () 13, ladDel (ladp 1) 13, .tick () 14, .tick () 15,
    .tick () 16, .tick () 17, .tick () 18, .tick () 19, .tick () 20, .tick () 21,
    ladDel (ladp 2) 21, .tick () 22, .tick () 23, .tick () 24, .tick () 25, .tick () 26,
    .tick () 27, .tick () 28, .tick () 29, .tick () 30, ladDel (ladp 3) 30, .tick () 31,
    .tick () 32, .tick () 33, .tick () 34, .tick () 35, .tick () 36, .tick () 37,
    ladDel (ladp 4) 37, .tick () 38, .tick () 39, .tick () 40, .tick () 41, .tick () 42,
    .tick () 43, .tick () 44, .tick () 45, ladDel (ladp 5) 45, .tick () 46, .tick () 47,
    .tick () 48, .tick () 49, .tick () 50, .tick () 51, .tick () 52, .tick () 53,
    ladDel (ladp 6) 53, .tick () 54, .tick () 55, .tick () 56, .tick () 57, .tick () 58,
    .tick () 59, .tick () 60, .tick () 61, ladDel (ladp 7) 61, .tick () 62, .tick () 63,
    .tick () 64, .tick () 65, .tick () 66, .tick () 67, .tick () 68, .tick () 69,
    ladDel (ladp 8) 69, .tick () 70, .tick () 71, .tick () 72, .tick () 73, .tick () 74,
    .tick () 75, .tick () 76, .tick () 77, ladDel (ladp 9) 77, .tick () 78, .tick () 79,
    .tick () 80, .tick () 81, .tick () 82, .tick () 83, .tick () 84, .tick () 85,
    ladDel (ladp 10) 85, .tick () 86, .tick () 87, .tick () 88, .tick () 89, .tick () 90,
    .tick () 91, .tick () 92, .tick () 93, ladDel (ladp 11) 93, .tick () 94, .tick () 95,
    .tick () 96, .tick () 97, .tick () 98, .tick () 99, .tick () 100, .tick () 101,
    ladDel (ladp 12) 101, .tick () 102, .tick () 103, .tick () 104, .tick () 105, .tick () 106,
    .tick () 107, .tick () 108, .tick () 109, ladDel (ladp 13) 109, .tick () 110, .tick () 111,
    .tick () 112, .tick () 113, .tick () 114, .tick () 115, .tick () 116, .tick () 117,
    ladDel (ladp 14) 117, .tick () 118, .tick () 119, .tick () 120, .tick () 121, .tick () 122,
    .tick () 123, .tick () 124, .tick () 125, ladDel (ladp 15) 125, .tick () 126, .tick () 127,
    .tick () 128, .tick () 129, .tick () 130, .tick () 131, .tick () 132, .tick () 133,
    ladDel (ladp 16) 133, .tick () 134, .tick () 135, .tick () 136, .tick () 137, .tick () 138,
    .tick () 139, .tick () 140, .tick () 141, ladDel (ladp 17) 141, .tick () 142, .tick () 143,
    .tick () 144, .tick () 145, .tick () 146, .tick () 147, .tick () 148, .tick () 149,
    ladDel (ladp 18) 149, .tick () 150, .tick () 151, .tick () 152, .tick () 153, .tick () 154,
    .tick () 155, .tick () 156, .tick () 157, ladDel (ladp 19) 157, .tick () 158, .tick () 159,
    .tick () 160, .tick () 161, .tick () 162, .tick () 163, .tick () 164, .tick () 165,
    ladDel (ladp 20) 165, .tick () 166, .tick () 167, .tick () 168]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

private theorem ladcphase33 : PhaseInterval ladR v5env ladcrho ladO 33 36 4 none false := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro i x hi hi' _
  cases x
  have h1 : V2.D.Run.idxBefore ladcrho 33 = 39 := by decide +kernel
  have h2 : timeIdx ladcrho 36 = 43 := by decide +kernel
  rw [h1] at hi
  rw [h2] at hi'
  interval_cases i <;> decide +kernel

private theorem ladcBad :
    (30 : Time) = v5T.action (1 + 2) ∧
    FrontierRepairAllowance ladR v5env ladcrho ladO v5T ladI 12 1 4 0 30 ∧
    (∃ kind, FrontierSearchStart ladR v5env ladcrho ladO v5T 12 36 (ladDel (ladp 3) 30) 4
      kind) ∧
    (12 : Time) + 2 * FGCompose.P v5T ≤ (ladDel (ladp 3) 30).time ∧
    ¬ FrontierRepairAllowance ladR v5env ladcrho ladO v5T ladI 12 1 4 0
      ((ladDel (ladp 3) 30).time + 3 * v5T.delta) ∧
    ¬ ∀ i ev m kind, FrontierSearchStart ladR v5env ladcrho ladO v5T 12 i ev m kind →
      (12 : Time) + 2 * FGCompose.P v5T ≤ ev.time →
      FrontierRepairAllowance ladR v5env ladcrho ladO v5T ladI 12 1 4 0
        (ev.time + 3 * v5T.delta) := by
  have hallow : FrontierRepairAllowance ladR v5env ladcrho ladO v5T ladI 12 1 4 0 30 := by
    refine ⟨le_rfl, 8 + 2 * 1 - 1, FrontierRepairStart.two (u := 30) 8 (by decide)
      (fun (b : Nat) hb => ?_), ?_⟩
    · have hb' : (30 : Int) < 4 * ((b : Nat) : Int) := hb
      change (8 : Nat) ≤ b
      omega
    · intro _ (v : Int) m J c _ hp
      exfalso
      have hv : (30 : Int) ≤ v := hp.1
      have hi1 : V2.D.Run.idxBefore ladcrho 30 = 35 := by decide +kernel
      have hi2 : timeIdx ladcrho 30 = 37 := by decide +kernel
      have ht := v9timeIdx_mono ladcrho hv
      have a1 := (hp.2.2.2 35 () (by omega) (by omega) (by decide)).1
      have a2 := (hp.2.2.2 37 () (by omega) (by omega) (by decide)).1
      rw [← a1] at a2
      revert a2
      decide +kernel
  obtain ⟨kind, hkind⟩ := frontierSearch_phase_exists ladR ladO v5env ladcrho (36 + 1) 4
  have hstart : FrontierSearchStart ladR v5env ladcrho ladO v5T 12 36 (ladDel (ladp 3) 30)
      4 kind :=
    (FrontierSearchStart_def ladR v5env ladcrho ladO v5T 12 36 _ 4 kind).mpr
      ⟨by decide +kernel, by decide, Or.inl (Or.inl (by decide +kernel)), by decide +kernel,
        by decide, hkind⟩
  have hbad : ¬ FrontierRepairAllowance ladR v5env ladcrho ladO v5T ladI 12 1 4 0
      ((ladDel (ladp 3) 30).time + 3 * v5T.delta) := by
    rintro ⟨_, l, hl, hrep⟩
    obtain ⟨s, Q, hls, hg, _⟩ := (hrep (by decide) 36 4 none false (by decide) ladcphase33).2
      (by decide)
    have hg' : 4 * ((s : Nat) : Int) + 6 ≤ 33 + 0 := hg
    cases hl with
    | two β after _ =>
      have h1 : (33 : Int) < 4 * ((β : Nat) : Int) := after
      have h2 : 4 * (((β + 2 * 1 - 1 : Nat) : Nat) : Int) < 4 * ((s : Nat) : Int) := hls
      have h3 : ((β + 2 * 1 - 1 : Nat) : Int) = (β : Int) + 1 := by
        push_cast
        omega
      omega
    | one b after _ _ _ =>
      have h1 : (33 : Int) ≤ 4 * ((b : Nat) : Int) + 1 := after
      have h2 : 4 * (((b + 1 : Nat) : Nat) : Int) < 4 * ((s : Nat) : Int) := hls
      push_cast at h2
      omega
  exact ⟨by decide, hallow, ⟨kind, hstart⟩, by decide, hbad,
    fun h => hbad (h _ _ _ _ hstart (by decide))⟩


end AvailableChain.FGCompose.Tests.P0d5db
end
