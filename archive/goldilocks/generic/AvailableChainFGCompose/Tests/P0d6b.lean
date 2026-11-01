module
public import AvailableChainFGCompose.Proofs.Healing.Reset
public import AvailableChainFGCompose.Proofs.Finality.History -- shake: keep (window views)

set_option linter.privateModule false

public section
noncomputable section
namespace AvailableChain.FGCompose.Tests.P0d6b
open AvailableChain.SimplexFG AvailableChain.KitFG

/-! G0 for P0d6b (reset witness assembly). Model level: `rst*` is a generic event-fold
interface model (not an ExecutionValid run). It is the P0d5d-b ladder model with real row
sources: Δ = ΔF = 1, R = 2, G = 4, GST = 0, Jst = 12, one lease slot, horizon 168. One
honest node ticks at every time 0..168. A progress-certified chain p_1..p_20 (heights
2..21) is delivered at times 8k + 5. At every action r = 0..20 (time 8r + 6) the node signs
one row; its entry is the (height, root) entry of its action source, the frontier block p_r
(height r + 1). The `v5*`/`v9*` helpers are renamed copies of accepted test helpers.

Reset on this run: the first action round at or after Jst is 1, the cut is 30 (inclusive:
the row of action 3 is sent at 30), M = 4, and the first height-5 row is the row of action 4
(time 38). The start-family search statement for the allowance 7 is proved on the run by
inspection (`rstSearch`); the search leaves are not re-proved on this model. -/

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

private def v5E : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩

private def v5cfg : FGConfig := ⟨4⟩

private abbrev v5H := KitFG.Window.certificateHeight v5E v5cfg 2

private abbrev v5F := KitFG.Window.certificateFinality v5E v5cfg 2

private abbrev v5env : Generic.Env Unit := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩

private theorem v5cert : FGCertificateLaws v5E v5H v5F :=
  KitFG.Window.windowCertificateLaws v5E v5cfg 2
    (by unfold Electorate.IsQuorum; decide +kernel) (by decide)

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

private def rstX (s : Nat) : FGBlock (Fin 1) := .node .genesis s ⟨20 + s⟩ 0 []

private def rsttv (h : Nat) (e : BlockId) : Row (Fin 1) := ⟨0, .vote h e true, none⟩

private def rstp : Nat → FGBlock (Fin 1)
  | 0 => .genesis
  | k + 1 => .node (rstp k) (4 * (k + 1)) ⟨300 + k + 1⟩ 0 [rsttv (k + 1) (rstp k).root]

/-- The honest row of action r: the entry (height r + 1, root) of the chain block p_r. -/
private def rstrow (r : Nat) : Row (Fin 1) :=
  ⟨0, .vote (r + 1) (v5H (rstp r)).T_h.root false, none⟩
private def rstrowIdx (a : Row (Fin 1)) : Nat :=
  match a.height_pair with | .vote h _ _ => h - 1 | .empty => 0

private def rstAllRows : List (Row (Fin 1)) := (List.range 21).map rstrow

/-- Delivered blocks, in delivery order. -/
private def rstblocks : List (FGBlock (Fin 1)) :=
  [rstX 1, rstX 2, rstX 3] ++ (List.range 20).map (fun k => rstp (k + 1))

private abbrev rstP : V2.ProtocolSpecD Unit where
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
  act _ d _ := if d % 8 = 6 ∧ d ≤ 168 then some (.inl (rstrow (d / 8)))
    else if d % 4 = 0 ∧ 4 ≤ d ∧ d ≤ 168 then some (.inr (v5erase (rstX (d / 4)))) else none
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

private abbrev rstTF (k : Nat) : Finset (FGBlock (Fin 1)) :=
  insert .genesis (rstblocks.take k).toFinset

private abbrev rsthmax (k : Nat) : Nat := if k ≤ 3 then 1 else min k 23 - 2

/-- A block that attains the frontier of a store count. -/
private abbrev rsttop (k : Nat) : FGBlock (Fin 1) := rstp (min k 23 - 3)

private theorem rstTF_mono {a b : Nat} (hab : a ≤ b) : rstTF a ⊆ rstTF b := by
  intro B hB
  simp only [rstTF, Finset.mem_insert, List.mem_toFinset] at hB ⊢
  rcases hB with h | h
  · exact Or.inl h
  · exact Or.inr ((List.take_prefix_take_left (by omega) |>.subset) h)

/-- The frontier witness of every store count. -/
private theorem rsttopFacts (k : Nat) (hk : k ≤ 23) :
    rsttop k ∈ rstTF k ∧ (v5H (rsttop k)).h = rsthmax k := by
  interval_cases k <;> decide +kernel

private theorem rsttop_mem (st : Nat) : rsttop st ∈ rstTF st := by
  rcases Nat.le_total st 23 with h | h
  · exact (rsttopFacts st h).1
  · have he : rsttop st = rsttop 23 := by
      unfold rsttop
      rw [Nat.min_eq_right h]
      rfl
    rw [he]
    exact rstTF_mono h (rsttopFacts 23 le_rfl).1

private abbrev rstR : FGCoreReads rstP 1 Unit Unit (Row (Fin 1)) where
  core st := ⟨(), ⟨rstTF st, .genesis, .genesis, 0, rsthmax st⟩, [], rstAllRows⟩
  erase := v5erase
  source st := some (rsttop st)
  headVote _ _ := .genesis
  finalityHead _ := none
  proposalFG _ _ := none

private abbrev rstO : FGObservationReads rstR where
  height := v5H
  finality := v5F
  controls nd := treeStoreControlsView v5H (rstR.core nd).fg
  viable nd X := treeStoreFrameView v5H (rstR.core nd).fg X

private noncomputable abbrev rstS : FGSafetyReads rstP 1 (Row (Fin 1)) where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode a := ⟨.seat (8 * rstrowIdx a + 6) 0, .inl a⟩
  decode := some
  decodeObject o := match o.payload with | .inl a => some a | .inr _ => none
  fgLabel := 6
  fgSeats := Equiv.refl _
  record := fun _ => RecordOnce.initial
  inputs := fun _ => (none, ⟨0, ⟨0⟩, 0⟩)
  enabled := fun _ => false
  finalizedOut := fun _ => .genesis

private def rstI : V2.D.Interface rstP where
  confirmed _ := .genesis
  stable _ := .genesis
  block p := match p with | .inr B => some B | .inl _ => none
  opening _ := False
  propLabel s := 4 * s
  propDuty s := 4 * s
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective _ _ h := Nat.eq_of_mul_eq_mul_left (by decide) h

private def rstDel (B : FGBlock (Fin 1)) (t : Time) : V2.Event Unit rstP.Object :=
  .deliver () ⟨.none, .inr (v5erase B)⟩ t

private noncomputable abbrev rstrho : V2.D.Run Unit rstP where
  honest := {()}
  horizon := 168
  events := [
    .tick () 0, .tick () 1, .tick () 2, .tick () 3, .tick () 4, rstDel (rstX 1) 4, .tick () 5,
    .tick () 6, .tick () 7, .tick () 8, rstDel (rstX 2) 8, .tick () 9, .tick () 10, .tick () 11,
    .tick () 12, rstDel (rstX 3) 12, .tick () 13, rstDel (rstp 1) 13, .tick () 14, .tick () 15,
    .tick () 16, .tick () 17, .tick () 18, .tick () 19, .tick () 20, .tick () 21,
    rstDel (rstp 2) 21, .tick () 22, .tick () 23, .tick () 24, .tick () 25, .tick () 26,
    .tick () 27, .tick () 28, .tick () 29, rstDel (rstp 3) 29, .tick () 30, .tick () 31,
    .tick () 32, .tick () 33, .tick () 34, .tick () 35, .tick () 36, .tick () 37,
    rstDel (rstp 4) 37, .tick () 38, .tick () 39, .tick () 40, .tick () 41, .tick () 42,
    .tick () 43, .tick () 44, .tick () 45, rstDel (rstp 5) 45, .tick () 46, .tick () 47,
    .tick () 48, .tick () 49, .tick () 50, .tick () 51, .tick () 52, .tick () 53,
    rstDel (rstp 6) 53, .tick () 54, .tick () 55, .tick () 56, .tick () 57, .tick () 58,
    .tick () 59, .tick () 60, .tick () 61, rstDel (rstp 7) 61, .tick () 62, .tick () 63,
    .tick () 64, .tick () 65, .tick () 66, .tick () 67, .tick () 68, .tick () 69,
    rstDel (rstp 8) 69, .tick () 70, .tick () 71, .tick () 72, .tick () 73, .tick () 74,
    .tick () 75, .tick () 76, .tick () 77, rstDel (rstp 9) 77, .tick () 78, .tick () 79,
    .tick () 80, .tick () 81, .tick () 82, .tick () 83, .tick () 84, .tick () 85,
    rstDel (rstp 10) 85, .tick () 86, .tick () 87, .tick () 88, .tick () 89, .tick () 90,
    .tick () 91, .tick () 92, .tick () 93, rstDel (rstp 11) 93, .tick () 94, .tick () 95,
    .tick () 96, .tick () 97, .tick () 98, .tick () 99, .tick () 100, .tick () 101,
    rstDel (rstp 12) 101, .tick () 102, .tick () 103, .tick () 104, .tick () 105, .tick () 106,
    .tick () 107, .tick () 108, .tick () 109, rstDel (rstp 13) 109, .tick () 110, .tick () 111,
    .tick () 112, .tick () 113, .tick () 114, .tick () 115, .tick () 116, .tick () 117,
    rstDel (rstp 14) 117, .tick () 118, .tick () 119, .tick () 120, .tick () 121, .tick () 122,
    .tick () 123, .tick () 124, .tick () 125, rstDel (rstp 15) 125, .tick () 126, .tick () 127,
    .tick () 128, .tick () 129, .tick () 130, .tick () 131, .tick () 132, .tick () 133,
    rstDel (rstp 16) 133, .tick () 134, .tick () 135, .tick () 136, .tick () 137, .tick () 138,
    .tick () 139, .tick () 140, .tick () 141, rstDel (rstp 17) 141, .tick () 142, .tick () 143,
    .tick () 144, .tick () 145, .tick () 146, .tick () 147, .tick () 148, .tick () 149,
    rstDel (rstp 18) 149, .tick () 150, .tick () 151, .tick () 152, .tick () 153, .tick () 154,
    .tick () 155, .tick () 156, .tick () 157, rstDel (rstp 19) 157, .tick () 158, .tick () 159,
    .tick () 160, .tick () 161, .tick () 162, .tick () 163, .tick () 164, .tick () 165,
    rstDel (rstp 20) 165, .tick () 166, .tick () 167, .tick () 168]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

private theorem rstlen : rstrho.events.length = 192 := by decide +kernel

private theorem rstnonneg : ∀ e ∈ rstrho.events, 0 ≤ e.time := by decide +kernel

private theorem rstschedule : V2.D.ScheduleWellFormed v5env rstrho where
  horizon_nonneg := by decide
  sorted := by decide +kernel
  nodup := by decide +kernel
  in_horizon := by
    intro e he
    exact ⟨rstnonneg e he, by revert e; decide +kernel⟩
  honest_only := by intro e he; simp
  tick_public := by
    intro v t ht
    have h := rstnonneg _ ht
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
private abbrev rstcnt (i : Nat) : Nat :=
  ((rstrho.events.take i).filter (fun e => match e with | .deliver .. => true | _ => false)).length

private theorem rststate (i : Nat) : rstrho.stateBefore v5env i () = rstcnt i := by
  have hall : ∀ i < 193, rstrho.stateBefore v5env i () = rstcnt i := by decide +kernel
  rcases Nat.lt_or_ge i 193 with h | h
  · exact hall i h
  · have he : ∀ j, 192 ≤ j → rstrho.events.take j = rstrho.events := fun j hj =>
      List.take_of_length_le (by rw [rstlen]; omega)
    unfold V2.D.Run.stateBefore
    rw [he i (by omega)]
    have h39 := he 192 le_rfl
    have := hall 192 (by omega)
    unfold V2.D.Run.stateBefore at this
    rw [h39] at this
    rw [this]
    unfold rstcnt
    rw [he i (by omega), h39]

private theorem rstcnt_mono {i j : Nat} (hij : i ≤ j) : rstcnt i ≤ rstcnt j := by
  unfold rstcnt
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [List.take_add, List.filter_append, List.length_append]
  exact Nat.le_add_right _ _

private theorem rstcnt_le (i : Nat) : rstcnt i ≤ 23 := by
  have h := rstcnt_mono (i := i) (j := i + 192) (by omega)
  have h2 : rstcnt (i + 192) = 23 := by
    unfold rstcnt
    rw [List.take_of_length_le (by rw [rstlen]; omega)]
    decide +kernel
  omega

private theorem rststore_inv (k : Nat) (hk : k ≤ 23) :
    FGStoreInvariant rstO.height rstO.finality (rstR.core k).fg := by
  interval_cases k <;> constructor <;> decide +kernel

private theorem rstinv (i : Nat) (x : Unit) : FGStoreInvariant rstO.height rstO.finality
    (rstR.core (rstrho.stateBefore v5env i x)).fg := by
  cases x
  rw [rststate]
  exact rststore_inv _ (rstcnt_le i)

private theorem rsthmax_mono {a b : Nat} (h : a ≤ b) : rsthmax a ≤ rsthmax b := by
  unfold rsthmax
  split_ifs <;> omega

private theorem rstcore : FGCoreLaws rstR where
  clock_fg _ _ := rfl
  clock_proposals _ _ := rfl
  clock_rowPool _ _ := rfl
  process_tf st _ := rstTF_mono (Nat.le_succ st)
  process_proposals _ _ := List.prefix_rfl
  process_rowPool _ _ := List.prefix_rfl
  own_core _ _ := rfl
  source_mem st C h := by
    cases Option.some.inj h
    exact rsttop_mem st
  erase_inj := v5erase_inj

private theorem rstfront (k : Nat) : frontierAtIdx rstR v5env rstrho k = rsthmax (rstcnt k) := by
  unfold frontierAtIdx
  change ({()} : Finset Unit).sup _ = _
  rw [Finset.sup_singleton, rststate]

/-- Controls of every store count: frontier, no contest, Z = genesis. -/
private theorem rstctl (k : Nat) (hk : k ≤ 23) :
    (treeStoreControlsView v5H (rstR.core k).fg).H = rsthmax k ∧
    (treeStoreControlsView v5H (rstR.core k).fg).contest = false ∧
    (treeStoreControlsView v5H (rstR.core k).fg).Z = .genesis := by
  interval_cases k <;> decide +kernel

/-- Released objects at a tick of time `d`. -/
private abbrev rstout (d : Nat) : List rstP.Object :=
  if d % 8 = 6 ∧ d ≤ 168 then [⟨.seat d 0, .inl (rstrow (d / 8))⟩]
  else if d % 4 = 0 ∧ 4 ≤ d ∧ d ≤ 168 then [⟨.seat d 0, .inr (v5erase (rstX (d / 4)))⟩]
  else []

private theorem rstEmits (j : Nat) : V2.D.Run.emitsAt v5env rstrho j =
    match rstrho.events[j]? with
    | some (.tick _ t) => rstout t.toNat
    | _ => [] := by
  rcases Nat.lt_or_ge j 192 with h | h
  · interval_cases j <;> decide +kernel
  · have hn : rstrho.events[j]? = none := List.getElem?_eq_none (by rw [rstlen]; omega)
    simp only [V2.D.Run.emitsAt, hn]

/-- Index of the tick of time `t`. -/
private abbrev rstti (t : Nat) : Nat :=
  t + (if 4 < t then 1 else 0) + (if 8 < t then 1 else 0) + (if 12 < t then 1 else 0) +
    min ((t - 6) / 8) 20

private theorem rsttick (t : Nat) (ht : t ≤ 168) :
    rstrho.events[rstti t]? = some (.tick () ((t : Nat) : Int)) := by
  interval_cases t <;> decide +kernel

private theorem rstaction (r : Nat) : (v5T.action r).toNat = 8 * r + 6 := by
  change (8 * ((r : Nat) : Int) + 6).toNat = 8 * r + 6
  omega

/-- The honest rows are exactly the action rows 0..20. -/
private theorem rstrows {j : Nat} {y : Unit} {r : Nat} {a : Row (Fin 1)}
    (h : HonestRowAt rstS v5env rstrho v5T j y r a) : r ≤ 20 ∧ a = rstrow r := by
  obtain ⟨_, hj, hem⟩ := h
  rw [rstEmits, hj] at hem
  change rstS.encode a ∈ rstout (v5T.action r).toNat at hem
  rw [rstaction] at hem
  by_cases hr : r ≤ 20
  · have hc : (8 * r + 6) % 8 = 6 ∧ 8 * r + 6 ≤ 168 := ⟨by omega, by omega⟩
    have hdiv : (8 * r + 6) / 8 = r := by omega
    simp only [rstout, hc, and_self, ite_true, List.mem_singleton, hdiv] at hem
    have := congrArg V2.Signed.payload hem
    exact ⟨hr, Sum.inl.inj this⟩
  · have hne : ¬ 8 * r + 6 ≤ 168 := by omega
    simp only [rstout, hne, and_false, ite_false, List.not_mem_nil] at hem

private theorem rstrowAt (r : Nat) (hr : r ≤ 20) :
    HonestRowAt rstS v5env rstrho v5T (rstti (8 * r + 6)) () r (rstrow r) := by
  have ht : v5T.action r = ((8 * r + 6 : Nat) : Int) := by
    change 8 * ((r : Nat) : Int) + 6 = _
    push_cast
    rfl
  refine ⟨Finset.mem_singleton_self _, ?_, ?_⟩
  · rw [ht]
    exact rsttick (8 * r + 6) (by omega)
  · rw [rstEmits, rsttick (8 * r + 6) (by omega)]
    change _ ∈ rstout (((8 * r + 6 : Nat) : Int).toNat)
    rw [Int.toNat_natCast]
    have hc : (8 * r + 6) % 8 = 6 ∧ 8 * r + 6 ≤ 168 := ⟨by omega, by omega⟩
    have hdiv : (8 * r + 6) / 8 = r := by omega
    have hidx : rstrowIdx (rstrow r) = r := rfl
    simp only [rstout, hc, and_self, ite_true, List.mem_singleton, hdiv]
    change (⟨.seat (8 * rstrowIdx (rstrow r) + 6) 0, .inl (rstrow r)⟩ : rstP.Object) = _
    rw [hidx]

/-- Frame height at an event index. -/
private theorem rstH (i : Nat) :
    (rstO.controls (rstrho.stateBefore v5env i ())).H = rsthmax (rstcnt i) := by
  change (treeStoreControlsView v5H (rstR.core (rstrho.stateBefore v5env i ())).fg).H = _
  rw [rststate]
  exact (rstctl _ (rstcnt_le i)).1

/-- Every window of seven time units after 12 contains a frontier rise. -/
private theorem rstshortTable : ∀ t < 162, 12 ≤ t →
    rsthmax (rstcnt (V2.D.Run.idxBefore rstrho ((t : Nat) : Int))) <
      rsthmax (rstcnt (timeIdx rstrho (((t + 7 : Nat) : Nat) : Int))) := by
  decide +kernel

private theorem rstphaseH {u v : Int} {m : Nat} {J : Option (FGBlock (Fin 1))}
    {contested : Bool} (hp : PhaseInterval rstR v5env rstrho rstO u v m J contested)
    {a b : Int} (ha : u ≤ a) (hb : b ≤ v) (hab : a ≤ b) :
    rsthmax (rstcnt (V2.D.Run.idxBefore rstrho a)) =
      rsthmax (rstcnt (timeIdx rstrho b)) := by
  have h1 := (hp.2.2.2 (V2.D.Run.idxBefore rstrho a) () (v9idxBefore_mono rstrho ha)
    (((v9idxBefore_le_timeIdx rstrho a).trans (v9timeIdx_mono rstrho hab)).trans
      (v9timeIdx_mono rstrho hb)) (Finset.mem_singleton_self _)).1
  have h2 := (hp.2.2.2 (timeIdx rstrho b) () (((v9idxBefore_mono rstrho ha).trans
    (v9idxBefore_le_timeIdx rstrho a)).trans (v9timeIdx_mono rstrho hab))
    (v9timeIdx_mono rstrho hb) (Finset.mem_singleton_self _)).1
  rw [rstH] at h1 h2
  rw [h1, h2]

/-- Every phase from the join time lasts at most six time units. -/
private theorem rstphase_short {u v : Int} {m : Nat} {J : Option (FGBlock (Fin 1))}
    {contested : Bool} (hu : 12 ≤ u)
    (hp : PhaseInterval rstR v5env rstrho rstO u v m J contested) : v ≤ u + 6 := by
  by_contra hn
  have hv : v ≤ 168 := hp.2.1
  obtain ⟨t, ht⟩ : ∃ t : Nat, u = ((t : Nat) : Int) :=
    ⟨u.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  subst ht
  have h12 : 12 ≤ t := by exact_mod_cast hu
  have hlt := rstshortTable t (by omega) h12
  have hb : ((t + 7 : Nat) : Int) ≤ v := by push_cast; omega
  have heq := rstphaseH hp (a := ((t : Nat) : Int)) (b := ((t + 7 : Nat) : Int)) le_rfl
    hb (by push_cast; omega)
  omega

/-- Every allowance from 7 holds at every time: no phase lasts seven time units, and no
proposal after the first repair label reaches its gate inside a phase. -/
private theorem rstallow (ρ u : Int) (hρ : 7 ≤ ρ) :
    FrontierRepairAllowance rstR v5env rstrho rstO v5T rstI 12 1 4 ρ u := by
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
  have hs : v ≤ u + 6 := rstphase_short hu hp
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

private theorem rstfirst {rG : Nat} (h1 : (12 : Time) ≤ v5T.action rG)
    (h2 : ∀ r, (12 : Time) ≤ v5T.action r → rG ≤ r) : rG = 1 := by
  have ha : (12 : Int) ≤ 8 * ((rG : Nat) : Int) + 6 := h1
  have hb := h2 1 (by decide)
  omega

/-- The action source of every action 0..20 is the frontier block p_r. -/
private theorem rstsrc (r : Nat) (hr : r ≤ 20) :
    actionSourceFG rstR v5env rstrho v5T () r = some (some (rstp r)) := by
  interval_cases r <;> decide +kernel

private theorem rstheight (r : Nat) (hr : r ≤ 20) : (v5H (rstp r)).h = r + 1 := by
  interval_cases r <;> decide +kernel

/-- Source leaf: every honest row names the exact (height, root) entry of its source. -/
private theorem rstname : ∀ {j : Nat} {x : Unit} {r : Nat} {a : Row (Fin 1)}
    {e : Height × BlockId}, HonestRowAt rstS v5env rstrho v5T j x r a →
    namedEntry (Row.height_pair a) = some e →
    ∃ C, actionSourceFG rstR v5env rstrho v5T x r = some (some C) ∧
      e = ((rstO.height C).h, (rstO.height C).T_h.root) := by
  intro j x r a e ha he
  obtain ⟨hr, rfl⟩ := rstrows ha
  cases x
  refine ⟨rstp r, rstsrc r hr, ?_⟩
  have h1 : (r + 1, (v5H (rstp r)).T_h.root) = e := Option.some.inj he
  rw [← h1]
  change _ = ((v5H (rstp r)).h, (v5H (rstp r)).T_h.root)
  rw [rstheight r hr]

private theorem rsttreeKeep : FGTreeKeepLaws rstR := ⟨fun _ _ => Finset.Subset.refl _⟩

/-- Honest height rows: the row of action r has height r + 1. -/
private theorem rstrowH (r h : Nat) :
    HeightRow rstS v5env rstrho v5T (fun a => namedEntry (Row.height_pair a)) r h ↔
      r ≤ 20 ∧ h = r + 1 := by
  constructor
  · rintro ⟨j, y, a, e, hrow, hent⟩
    obtain ⟨hr, rfl⟩ := rstrows hrow
    have h2 : (r + 1, (v5H (rstp r)).T_h.root) = (h, e) := Option.some.inj hent
    exact ⟨hr, (congrArg Prod.fst h2).symm⟩
  · rintro ⟨hr, rfl⟩
    exact ⟨rstti (8 * r + 6), (), rstrow r, _, rstrowAt r hr, rfl⟩

private theorem rstfirstRound : resetFirstRound v5T v5TLaws 12 = 1 :=
  rstfirst (reset_rG_after v5T v5TLaws 12) (reset_rG_first v5T v5TLaws 12)

private theorem rstcut : resetCutTime v5T v5TLaws 12 = 30 := by
  rw [reset_cut, rstfirstRound]
  rfl

private theorem rstM : (4 : Nat) = honestFrontier rstR v5env rstrho 30 := by
  rw [reset_inclusive_frontier (R := rstR) (E := v5env) (rho := rstrho) rstschedule 30,
    rstfront]
  decide +kernel

private theorem rstfrontier : resetCutFrontier rstR v5env rstrho v5T v5TLaws 12 = 4 := by
  rw [reset_frontier, rstcut]
  exact rstM.symm

/-- The start-family search statement for the allowance 7, proved on the run by
inspection: the rise from the cut is the p_4 delivery (index 44, time 37) and the least
height-5 row is the row of action 4 (time 38). -/
private theorem rstSearch : FrontierSearchFamilyStatement rstR rstS v5env rstrho rstO v5T rstI
    Row.height_pair 12 1 4 4 1 7 := by
  apply (FrontierSearchFamilyStatement_def rstR rstS v5env rstrho rstO v5T rstI
    Row.height_pair 12 1 4 4 1 7).mpr
  intro _ _ _ _ rG u₀ M hgst hfirst hu₀ _ hM _
  have hr := rstfirst hgst hfirst
  subst hr
  have hu : u₀ = 30 := hu₀
  subst hu
  have hM4 : M = 4 := hM.trans rstM.symm
  subst hM4
  have hti : timeIdx rstrho 30 = 37 := by decide +kernel
  have hev : rstrho.events[44]? = some (rstDel (rstp 4) 37) := by decide +kernel
  have hrise : 4 < frontierAtIdx rstR v5env rstrho (44 + 1) := by
    rw [rstfront]
    decide +kernel
  have hcap : ∀ k, timeIdx rstrho 30 ≤ k → k ≤ 44 → frontierAtIdx rstR v5env rstrho k ≤ 4 := by
    intro k _ h2
    rw [rstfront]
    have h44 : rsthmax (rstcnt 44) = 4 := by decide +kernel
    exact (rsthmax_mono (rstcnt_mono h2)).trans_eq h44
  refine ⟨fun _ => ⟨44, _, by rw [hti]; decide, hev, by decide +kernel, hrise, hcap⟩,
    fun _ => ⟨4, (rstrowH 4 5).mpr ⟨by decide, rfl⟩, fun r hr => ?_, 44, _, by rw [hti]; decide,
      hev, by decide +kernel, hrise, hcap, by decide +kernel⟩⟩
  have := ((rstrowH r 5).mp hr).2
  omega

/-- The allowance 7 at every actual phase start (in fact at every time). -/
private theorem rstfamily : ∀ i ev m kind,
    FrontierSearchStart rstR v5env rstrho rstO v5T 12 i ev m kind →
    (12 : Time) + 2 * FGCompose.P v5T ≤ ev.time →
    FrontierRepairAllowance rstR v5env rstrho rstO v5T rstI 12 1 4 7
      (ev.time + 3 * v5T.delta) :=
  fun _ _ _ _ _ _ => rstallow 7 _ (by decide)

private theorem rstbudget : (155 : Time) = 3 * FGCompose.P v5T +
    (E_gF v5T 1 4 7 + E_jF v5T 1 4 7 + B_cF v5T 1 4 7) +
    (E_gF v5T 1 4 7 + E_jF v5T 1 4 7 + D_cF v5T 7) := by decide +kernel

/-- G0 (POSITIVE): the generic reset witness assembly applied on `rst`, allowance 7,
budget 155, strict deadline 12 + 155 = 167 ≤ horizon 168. -/
private theorem rstReset : ∃ w : FGResetHistory,
    H0Reset rstR rstS v5env rstrho rstO v5T (fun a => namedEntry (Row.height_pair a)) 12 w ∧
    w.rG = resetFirstRound v5T v5TLaws 12 ∧ w.u0 = resetCutTime v5T v5TLaws 12 ∧
    w.M = resetCutFrontier rstR v5env rstrho v5T v5TLaws 12 ∧
    v5T.action w.rStar < 12 + 155 :=
  healing_resetWitness (T := v5T) (L := v5TLaws) (Jst := 12) (R := rstR) (S := rstS)
    (E := v5env) (rho := rstrho) (O := rstO) (I := rstI) (pair := Row.height_pair)
    (Ef := v5E) (HL := v5cert.height) (CL := rstcore) (K := rsttreeKeep) (storeInv := rstinv)
    (emittedName := rstname) (leaseSlots := 1) (deltaT := 4) rstschedule (by decide)
    (by decide) (G := 4) (ΔF := 1) (ρbar := 7) (budget := 155) rfl ⟨by decide⟩ (by decide)
    rstfamily rstSearch rstbudget (by decide)

/-- Every premise of `rstReset` on the exact run, in the order of the call. -/
private theorem rstReset_premises_sat :
    FGHeightLaws v5E rstO.height ∧ FGCoreLaws rstR ∧ FGTreeKeepLaws rstR ∧
    (∀ i x, FGStoreInvariant rstO.height rstO.finality
      (rstR.core (rstrho.stateBefore v5env i x)).fg) ∧
    (∀ {j : Nat} {x : Unit} {r : Nat} {a : Row (Fin 1)} {e : Height × BlockId},
      HonestRowAt rstS v5env rstrho v5T j x r a → namedEntry (Row.height_pair a) = some e →
      ∃ C, actionSourceFG rstR v5env rstrho v5T x r = some (some C) ∧
        e = ((rstO.height C).h, (rstO.height C).T_h.root)) ∧
    V2.D.ScheduleWellFormed v5env rstrho ∧ (0 : Time) ≤ 12 ∧ v5env.t_GST ≤ (12 : Time) ∧
    (4 : Nat) = 2 * v5T.roundSlots ∧ LivenessBoundW v5T 1 ∧ (0 : Time) ≤ 7 ∧
    (∀ i ev m kind, FrontierSearchStart rstR v5env rstrho rstO v5T 12 i ev m kind →
      (12 : Time) + 2 * FGCompose.P v5T ≤ ev.time →
      FrontierRepairAllowance rstR v5env rstrho rstO v5T rstI 12 1 4 7
        (ev.time + 3 * v5T.delta)) ∧
    FrontierSearchFamilyStatement rstR rstS v5env rstrho rstO v5T rstI Row.height_pair 12 1 4
      4 1 7 ∧
    (155 : Time) = 3 * FGCompose.P v5T +
      (E_gF v5T 1 4 7 + E_jF v5T 1 4 7 + B_cF v5T 1 4 7) +
      (E_gF v5T 1 4 7 + E_jF v5T 1 4 7 + D_cF v5T 7) ∧
    (12 : Time) + 155 ≤ rstrho.horizon ∧ rstrho.honest.Nonempty :=
  ⟨v5cert.height, rstcore, rsttreeKeep, rstinv, rstname, rstschedule, by decide, by decide,
    rfl, ⟨by decide⟩, by decide, rstfamily, rstSearch, rstbudget, by decide,
    ⟨(), Finset.mem_singleton_self _⟩⟩

/-- G0 inspection: every coordinate of the reset history comes from the cut and the one
first row with its source: rG = 1, cut 30, M = 4, rStar = 4, sStar = 8, source = erase p_4,
and the first row (time 38) is strictly before the reset deadline 167. -/
private theorem rstResetExit : ∃ w : FGResetHistory,
    H0Reset rstR rstS v5env rstrho rstO v5T (fun a => namedEntry (Row.height_pair a)) 12 w ∧
    w.rG = 1 ∧ w.u0 = 30 ∧ w.M = 4 ∧ w.rStar = 4 ∧ w.sStar = 8 ∧
    w.source = v5erase (rstp 4) ∧ v5T.action w.rStar = 38 ∧
    v5T.action w.rStar < 12 + 155 := by
  obtain ⟨w, hw, hrG, hu0, hM, htime⟩ := rstReset
  rw [rstfirstRound] at hrG
  rw [rstcut] at hu0
  rw [rstfrontier] at hM
  have hrow := hw.reset_row
  rw [hM] at hrow
  have hr4 : w.rStar = 4 := by
    have := ((rstrowH w.rStar 5).mp hrow).2
    omega
  obtain ⟨j, y, a, C, _, _, hC, hE, _⟩ := hw.fresh
  cases y
  rw [hr4, rstsrc 4 (by decide)] at hC
  have hC4 : rstp 4 = C := Option.some.inj (Option.some.inj hC)
  refine ⟨w, hw, hrG, hu0, hM, hr4, by rw [hw.label, hr4]; rfl, by rw [← hE, ← hC4],
    by rw [hr4]; rfl, htime⟩

/-- Controls. Inclusive row cap: the row of action 3 is sent at the cut time 30 with height
4 = M, and the next row (time 38 > 30) has height 5 > M. Old source-vote cutoff: height 2 is
an old row height (its source vote 9 is before Jst = 12) and height 3 is not (vote 17).
First-row minimality: no height-5 row before action 4. Strict deadline: the cut 30 is
strictly before Jst + 3P = 36; with the allowance 8 the complete horizon guard fails
(12 + 161 > 168), so the witness is claimed for the allowance 7 only. -/
private theorem rstControls :
    (HonestRowAt rstS v5env rstrho v5T (rstti 30) () 3 (rstrow 3) ∧
      rstrho.events[rstti 30]? = some (.tick () 30) ∧
      namedEntry (Row.height_pair (rstrow 3)) = some (4, (v5H (rstp 3)).T_h.root) ∧
      resetCutTime v5T v5TLaws 12 = 30 ∧
      resetCutFrontier rstR v5env rstrho v5T v5TLaws 12 = 4 ∧
      ¬ HeightRow rstS v5env rstrho v5T (fun a => namedEntry (Row.height_pair a)) 3 5) ∧
    ((2 : Nat) ∈ oldRowHeights rstS v5env rstrho v5T
        (fun a => namedEntry (Row.height_pair a)) 12 ∧
      (3 : Nat) ∉ oldRowHeights rstS v5env rstrho v5T
        (fun a => namedEntry (Row.height_pair a)) 12) ∧
    (∀ r, HeightRow rstS v5env rstrho v5T (fun a => namedEntry (Row.height_pair a)) r 5 →
      4 ≤ r) ∧
    ((30 : Time) < 12 + 3 * FGCompose.P v5T ∧
      ¬ (12 : Time) + (3 * FGCompose.P v5T +
        (E_gF v5T 1 4 8 + E_jF v5T 1 4 8 + B_cF v5T 1 4 8) +
        (E_gF v5T 1 4 8 + E_jF v5T 1 4 8 + D_cF v5T 8)) ≤ rstrho.horizon) := by
  refine ⟨⟨rstrowAt 3 (by decide), rsttick 30 (by decide), rfl, rstcut, rstfrontier, ?_⟩,
    ⟨⟨rstti 14, (), 1, rstrow 1, _, rstrowAt 1 (by decide), rfl, by decide⟩, ?_⟩, ?_,
    by decide, by decide +kernel⟩
  · intro h
    have := ((rstrowH 3 5).mp h).2
    omega
  · rintro ⟨j, y, r, a, e, hrow, hent, hold⟩
    obtain ⟨hr, rfl⟩ := rstrows hrow
    have h2 : (r + 1, (v5H (rstp r)).T_h.root) = (3, e) := Option.some.inj hent
    have hr2 : r + 1 = 3 := congrArg Prod.fst h2
    have hv : 4 * (((r * 2 : Nat) : Nat) : Int) + 1 < 12 := hold
    push_cast at hv
    omega
  · intro r hr
    have := ((rstrowH r 5).mp hr).2
    omega

end AvailableChain.FGCompose.Tests.P0d6b
end
