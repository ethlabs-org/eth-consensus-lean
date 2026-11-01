module
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchRepair
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchCompose
public import AvailableChainFGCompose.Proofs.Finality.History -- shake: keep (window views)

set_option linter.privateModule false

public section
noncomputable section
namespace AvailableChain.FGCompose.Tests.P0d5da
open AvailableChain.SimplexFG AvailableChain.KitFG

/-! G0 for P0d5d-a (finite phase composition). Model levels: `q5*` and `mv*` are generic
event-fold interface models (not ExecutionValid runs); `pd*` are pure data.
The `q5` model is a renamed copy of the accepted P0d5c contest model (private there). -/

private def q5T : FGTiming where
  delta := 1
  roundSlots := 2
  proposal s := 4 * (s : Time)
  vote s := 4 * (s : Time) + 1
  early s := 4 * (s : Time) + 2
  freeze s := 4 * (s : Time) + 3
  release s := 4 * (s : Time) + 5
  gate s := 4 * (s : Time) + 6
  action r := 8 * (r : Time) + 6
private theorem q5TLaws : FGTimingLaws q5T where
  delta_pos := by decide
  rounds := by decide
  proposal_eq s := by simp [q5T]
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq r := by simp [q5T]; ring
private def q5r (h : Nat) (e : BlockId) : Row (Fin 1) := ⟨0, .vote h e false, none⟩
private def q5x1 : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 [q5r 1 genesisRoot]
private def q5x2 : FGBlock (Fin 1) := .node .genesis 1 ⟨2⟩ 0 [q5r 1 genesisRoot]
private def q5y1 : FGBlock (Fin 1) := .node q5x1 2 ⟨3⟩ 0 [q5r 2 ⟨1⟩]
private def q5y2 : FGBlock (Fin 1) := .node q5x2 2 ⟨4⟩ 0 [q5r 2 ⟨2⟩]
private def q5z : FGBlock (Fin 1) := .node q5y1 3 ⟨5⟩ 0 [q5r 3 ⟨3⟩]

private def q5erase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node p s r x rs => .node (q5erase p) s r (encFGBody x rs)

private theorem q5erase_inj : Function.Injective q5erase := by
  intro A
  induction A with
  | genesis => intro B h; cases B <;> simp_all [q5erase]
  | node p s r x rs ih =>
    intro B h
    cases B with
    | genesis => simp [q5erase] at h
    | node q t u y ts =>
      simp only [q5erase, Block.node.injEq] at h
      obtain ⟨hp, hs, hr, hb⟩ := h
      obtain ⟨hx, hrows⟩ := encFGBody_inj hb
      cases ih hp
      cases hs
      cases hr
      cases hx
      cases hrows
      rfl

private theorem q5erase_mono {A B : FGBlock (Fin 1)} (h : FGBlock.Preceq A B) :
    Block.Preceq (q5erase A) (q5erase B) := by
  induction B with
  | genesis =>
    rw [(preceq_genesis).mp h]
    rfl
  | node P s r x rs ih =>
    change (decide (A = .node P s r x rs) || FGBlock.preceq A P) = true at h
    change (decide (q5erase A = q5erase (.node P s r x rs)) ||
      Block.preceq (q5erase A) (q5erase P)) = true
    rw [Bool.or_eq_true] at h ⊢
    rcases h with he | hp
    · exact Or.inl (decide_eq_true (congrArg q5erase (of_decide_eq_true he)))
    · exact Or.inr (ih hp)

private abbrev q5P : V2.ProtocolSpecD Unit where
  State := Nat
  Label := Nat
  Duty := Nat
  signLabel := id
  seats _ := 1
  Payload := Row (Fin 1)
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
  act _ _ _ := none
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

private abbrev q5TF (st : Nat) : Finset (FGBlock (Fin 1)) :=
  if st = 0 then {.genesis} else if st = 1 then {.genesis, q5x1, q5x2, q5y1, q5y2}
  else {.genesis, q5x1, q5x2, q5y1, q5y2, q5z}

private abbrev q5R : FGCoreReads q5P 1 Unit Unit (Row (Fin 1)) where
  core st := ⟨(), ⟨q5TF st, .genesis,
    if st = 0 then .genesis else if st = 1 then q5x2 else q5y1,
    if st = 0 then 0 else if st = 1 then 2 else 3,
    if st = 0 then 1 else if st = 1 then 3 else 4⟩, [], []⟩
  erase := q5erase
  source := fun _ => none
  headVote := fun _ _ => .genesis
  finalityHead := fun _ => none
  proposalFG := fun _ _ => none

private def q5E : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private def q5cfg : FGConfig := ⟨4⟩
private abbrev q5H := KitFG.Window.certificateHeight q5E q5cfg 2
private abbrev q5F := KitFG.Window.certificateFinality q5E q5cfg 2

private abbrev q5O : FGObservationReads q5R where
  height := q5H
  finality := q5F
  controls nd := treeStoreControlsView q5H (q5R.core nd).fg
  viable nd X := treeStoreFrameView q5H (q5R.core nd).fg X

private theorem q5obs : FGObservationLaws q5R q5O := ⟨fun _ => rfl, fun _ _ => rfl⟩

private theorem q5TF_mono (st : Nat) : q5TF st ⊆ q5TF (st + 1) := by
  rcases Nat.lt_or_ge st 2 with h | h
  · interval_cases st <;> decide
  · have h0 : st ≠ 0 := by omega
    have h1 : st ≠ 1 := by omega
    have h2 : st + 1 ≠ 0 := by omega
    have h3 : st + 1 ≠ 1 := by omega
    simp only [q5TF, h0, h1, h2, h3, ite_false]
    exact Finset.Subset.refl _

private theorem q5core : FGCoreLaws q5R where
  clock_fg _ _ := rfl
  clock_proposals _ _ := rfl
  clock_rowPool _ _ := rfl
  process_tf st _ := q5TF_mono st
  process_proposals _ _ := List.prefix_rfl
  process_rowPool _ _ := List.prefix_rfl
  own_core _ _ := rfl
  source_mem _ _ h := by cases h
  erase_inj := q5erase_inj

private noncomputable abbrev q5S : FGSafetyReads q5P 1 (Row (Fin 1)) where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode := fun a => ⟨.none, a⟩
  decode := some
  decodeObject := fun o => some o.payload
  fgLabel := 0
  fgSeats := Equiv.refl _
  record := fun _ => RecordOnce.initial
  inputs := fun _ => (none, ⟨0, ⟨0⟩, 0⟩)
  enabled := fun _ => false
  finalizedOut := fun _ => .genesis

private def q5I : V2.D.Interface q5P where
  confirmed _ := .genesis
  stable _ := .genesis
  block _ := none
  opening _ := False
  propLabel s := s
  propDuty s := s
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective _ _ h := h

private abbrev q5env : Generic.Env Unit := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩

private noncomputable abbrev q5rho : V2.D.Run Unit q5P where
  honest := {()}
  horizon := 8
  events := [.tick () 0, .tick () 1, .tick () 2, .tick () 3, .tick () 4,
    .deliver () ⟨.none, q5r 9 ⟨9⟩⟩ 4, .tick () 5, .tick () 6, .tick () 7, .tick () 8,
    .deliver () ⟨.none, q5r 9 ⟨9⟩⟩ 8]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

private theorem q5nonneg : ∀ e ∈ q5rho.events, 0 ≤ e.time := by decide

private theorem q5schedule : V2.D.ScheduleWellFormed q5env q5rho where
  horizon_nonneg := by decide
  sorted := by decide
  nodup := by decide
  in_horizon := by
    intro e he
    exact ⟨q5nonneg e he, by revert e; decide⟩
  honest_only := by intro e he; simp
  tick_public := by
    intro v t ht
    have h := q5nonneg _ ht
    refine ⟨t.toNat, ?_⟩
    simp only [V2.Event.time] at h
    change (t : Int) = ((t.toNat : Nat) : Int) * 1
    rw [Int.toNat_of_nonneg h, Int.mul_one]
  tick_total := by
    intro v _ t ht _ hh _
    obtain ⟨k, rfl⟩ := ht
    have hk : k ≤ 8 := by
      change ((k : Nat) : Int) * 1 ≤ 8 at hh
      omega
    cases v
    interval_cases k <;> decide

private theorem q5state (i : Nat) : q5rho.stateBefore q5env i () =
    if i ≤ 5 then 0 else if i ≤ 10 then 1 else 2 := by
  rcases Nat.lt_or_ge i 12 with h | h
  · interval_cases i <;> decide +kernel
  · have he : V2.D.Run.stateBefore q5env q5rho i () =
        V2.D.Run.stateBefore q5env q5rho 11 () := by
      unfold V2.D.Run.stateBefore
      rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp)]
    rw [he]
    simp only [show ¬ i ≤ 5 by omega, show ¬ i ≤ 10 by omega, ↓reduceIte]
    decide +kernel

private theorem q5state_le (i : Nat) : q5rho.stateBefore q5env i () ≤ 2 := by
  rw [q5state]; split_ifs <;> decide

private theorem q5state_mono {i j : Nat} (hij : i ≤ j) :
    q5rho.stateBefore q5env i () ≤ q5rho.stateBefore q5env j () := by
  rw [q5state, q5state]; split_ifs <;> first | decide | omega

private theorem q5store_inv (st : Nat) (hst : st ≤ 2) :
    FGStoreInvariant q5O.height q5O.finality (q5R.core st).fg := by
  interval_cases st
  all_goals
    constructor
    · intro B hB
      change B ∈ q5TF _ at hB
      simp only [q5TF, ite_true, ite_false, Finset.mem_insert, Finset.mem_singleton,
        show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
        show (2 : Nat) ≠ 1 by decide] at hB
      rcases hB with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · constructor
      · first
        | exact ⟨.genesis, by decide +kernel, by decide +kernel, rfl, rfl⟩
        | exact ⟨q5y2, by decide +kernel, by decide +kernel, rfl, rfl⟩
        | exact ⟨q5z, by decide +kernel, by decide +kernel, rfl, rfl⟩
      · intro B hB _
        change B ∈ q5TF _ at hB
        simp only [q5TF, ite_true, ite_false, Finset.mem_insert, Finset.mem_singleton,
          show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
          show (2 : Nat) ≠ 1 by decide] at hB
        rcases hB with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    · decide +kernel
    · exact ⟨.genesis, by decide +kernel, rfl⟩

private theorem q5inv (i : Nat) (x : Unit) : FGStoreInvariant q5O.height q5O.finality
    (q5R.core (q5rho.stateBefore q5env i x)).fg := by
  cases x
  exact q5store_inv _ (q5state_le i)

private theorem q5cert : FGCertificateLaws q5E q5O.height q5O.finality :=
  KitFG.Window.windowCertificateLaws q5E q5cfg 2
    (by unfold Electorate.IsQuorum; decide +kernel) (by decide)

private theorem q5justif : FGJustificationLaws q5O.height :=
  FGJustificationLaws.of_bridge (KitFG.Window.windowHeightBridge q5E q5cfg 2 (by decide))

private theorem q5TF_le {a b : Nat} (hab : a ≤ b) (hb : b ≤ 2) : q5TF a ⊆ q5TF b := by
  interval_cases b <;> interval_cases a <;> decide

private theorem q5keep : ∀ i j, i ≤ j → ∀ x,
    TFAt q5R q5env q5rho i x ⊆ TFAt q5R q5env q5rho j x := by
  intro i j hij x
  cases x
  exact q5TF_le (q5state_mono hij) (q5state_le j)

private theorem q5mono : FGRunOrderLaws q5env q5rho q5R := by
  constructor
  intro i j x _ hij
  cases x
  have hm := q5state_mono (i := i) (j := j) hij
  have hj := q5state_le j
  generalize q5rho.stateBefore q5env i () = a at hm
  generalize q5rho.stateBefore q5env j () = b at hm hj
  interval_cases b <;> interval_cases a <;> decide

private theorem q5crossing : RXing q5R q5env q5rho q5O := by
  intro i i' x y K W _ _ _ _ _ _
  exact genesis_preceq W

private abbrev q5receipt (B : Block) (d : Time) (y : Unit) : Prop :=
  ∃ W, q5erase W = B ∧ W ∈ (q5R.core (q5rho.stateBeforeTime q5env d y)).fg.TF

private theorem q5noProposal {s : Slot} {Q : Block} (h : HonestProposal q5env q5rho q5I s Q) :
    False := by
  obtain ⟨_, _, _, hb⟩ := h
  cases hb

private theorem q5ready : ∀ t, (4 : Time) ≤ t →
    q5env.t_GST ≤ slotStartZ q5T (((slotAt q5T t : Slot) : Int) - 1) := by
  intro t ht
  have ht' : (4 : Int) ≤ t := ht
  change (0 : Int) ≤ 4 * 1 * ((((t / (4 * 1)).toNat : Nat) : Int) - 1)
  have h1 : (1 : Int) ≤ t / 4 := by omega
  have h2 : (((t / 4).toNat : Nat) : Int) = t / 4 := Int.toNat_of_nonneg (by omega)
  simp only [Int.mul_one] at *
  rw [h2]
  omega

-- Receipt scope at an event of the model: the witness is held at the read deadline.
private theorem q5scope (W : FGBlock (Fin 1)) (d : Time)
    (hW : W ∈ (q5R.core (q5rho.stateBeforeTime q5env d ())).fg.TF) :
    WitnessReceiptScope q5R q5env q5rho (fun _ => true) q5receipt W d :=
  ⟨fun _ y _ _ _ _ _ _ => by cases y; exact ⟨W, rfl, hW⟩⟩

private theorem q5services : ∀ i (ev : V2.Event Unit q5P.Object) m,
    q5rho.events[i]? = some ev → (4 : Time) ≤ ev.time → 1 ≤ m →
    frontierAtIdx q5R q5env q5rho (i + 1) = m → ev.time + q5T.delta ≤ q5rho.horizon →
    PhaseWitnessReceiptScope q5R q5env q5rho q5O (fun _ => true) q5receipt (i + 1) m
      (ev.time + q5T.delta) := by
  intro i ev m hi hJ hm hf hh
  have hlen : i < 11 := (List.getElem?_eq_some_iff.mp hi).1
  interval_cases i <;> simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq] at hi <;> subst hi <;> revert hf hJ hh
  all_goals
    first
    | (intro _ hJ _; exact absurd hJ (by decide))
    | (intro _ _ hh; exact absurd hh (by decide))
    | (intro hf _ _; subst hf; refine ⟨?_, ?_, ?_⟩)
  all_goals
    first
    | exact ⟨(), q5y1, ⟨by decide, by decide +kernel⟩, by decide +kernel,
        q5scope _ _ (by decide +kernel)⟩
    | exact ⟨(), .genesis, ⟨by decide, by decide +kernel⟩, by decide +kernel,
        q5scope _ _ (by decide +kernel)⟩
    | exact fun _ => ⟨(), q5y2, ⟨by decide, by decide +kernel⟩, by decide +kernel,
        by decide +kernel, by decide +kernel, q5scope _ _ (by decide +kernel)⟩
    | exact fun _ => ⟨(), .genesis, ⟨by decide, by decide +kernel⟩, by decide +kernel,
        by decide +kernel, by decide +kernel, q5scope _ _ (by decide +kernel)⟩
    | exact fun _ => ⟨(), q5y2, q5y1, ⟨by decide, by decide +kernel⟩,
        ⟨by decide, by decide +kernel⟩, by decide +kernel, by decide +kernel,
        by decide +kernel, by decide +kernel, q5scope _ _ (by decide +kernel),
        q5scope _ _ (by decide +kernel)⟩
    | (rintro ⟨x, _, _, hc⟩; cases x; exact absurd hc (by decide +kernel))

private theorem q5start : FrontierSearchStart q5R q5env q5rho q5O q5T 4 5
    (.deliver () ⟨.none, q5r 9 ⟨9⟩⟩ 4) 3 .contest := by
  refine ⟨rfl, by decide, Or.inl (Or.inl (by decide +kernel)), by decide +kernel, by decide,
    ?_⟩
  exact ⟨(), by decide, by decide +kernel, by decide +kernel⟩

-- The phase from 7 cannot reach 8: the delivery at 8 raises the honest frontier.
private theorem q5phase_breaks {v : Time} (hv : 8 ≤ v) {m : Nat}
    {J : Option (FGBlock (Fin 1))} {contested : Bool}
    (hp : PhaseInterval q5R q5env q5rho q5O 7 v m J contested) : False := by
  have hidx : V2.D.Run.idxBefore q5rho 7 = 8 := by decide
  have ht : 11 ≤ timeIdx q5rho v :=
    (show timeIdx q5rho 8 = 11 by decide) ▸ frontierSearch_timeIdx_mono q5rho hv
  have h8 := (hp.2.2.2 8 () (by omega) (by omega) (by decide)).1
  have h11 := (hp.2.2.2 11 () (by omega) ht (by decide)).1
  rw [h8.symm] at h11
  revert h11
  decide +kernel

private theorem q5allowance (ρbar : Time) (hρ : 1 ≤ ρbar) :
    FrontierRepairAllowance q5R q5env q5rho q5O q5T q5I 4 1 4 ρbar 7 := by
  refine ⟨by linarith, 3, FrontierRepairStart.two (u := 7) 2 (by decide) (fun b hb => ?_), ?_⟩
  · change (7 : Int) < 4 * (b : Int) at hb
    by_contra h
    have : (b : Int) ≤ 1 := by exact_mod_cast Nat.le_of_lt_succ (Nat.lt_of_not_le h)
    linarith
  · intro _ v m J contested _ hp
    refine ⟨fun s Q _ _ hQ => (q5noProposal hQ).elim, fun hb => ?_⟩
    exact (q5phase_breaks (by linarith) hp).elim

-- G0 (contest exit, event before service): the generic contest consumer applied with
-- every premise proved on the model. The repair window [7, 8] closes at the rise.
private theorem q5contest :
    FrontierHG3Result q5R q5S q5env q5rho q5O q5T q5I Row.height_pair 4 1 5 3 4
      (4 + (1 + 3 * q5T.delta)) :=
  frontier_hg3_contest q5R q5S q5env q5rho q5O q5T q5I Row.height_pair 4 1 q5E q5obs
    q5cert q5inv q5justif q5keep (by decide) q5core (fun h => q5erase_mono h)
    (fun _ => true) q5receipt q5TLaws le_rfl q5crossing q5schedule q5mono rfl
    (by decide) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl) q5ready q5services
    (fun W d y _ h => by
      obtain ⟨W', he, hW'⟩ := h
      exact q5erase_inj he ▸ hW')
    (G := 4) (by decide)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ hQ _ => (q5noProposal hQ).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ hQ => (q5noProposal hQ).elim)
    (fun _ _ _ _ _ _ _ _ _ hQ _ _ _ _ _ _ _ _ _ => (q5noProposal hQ).elim)
    q5start (q5allowance 1 le_rfl) (by decide)

-- Inspection: the selected exit is the first rise at index 10 (time 8, the closed
-- deadline); no phase stop and no saved seed exist.
private theorem q5contestExit :
    FirstRiseStopBy q5R q5env q5rho q5O 5 3 8 ∧
    ¬ FirstPhaseStopBy q5R q5env q5rho q5O 5 3 8 ∧
    ¬ (∃ t, StrongServed q5R q5S q5env q5rho q5O q5T q5I Row.height_pair 4 1 3 t) ∧
    ¬ FirstEffectiveBy q5R q5env q5rho q5O 5 7 := by
  have hnoserve : ¬ (∃ t, StrongServed q5R q5S q5env q5rho q5O q5T q5I
      Row.height_pair 4 1 3 t) := by
    rintro ⟨t, _, _, _, _, _, _, _, hQ, _⟩
    exact q5noProposal hQ
  have hnophase : ¬ FirstPhaseStopBy q5R q5env q5rho q5O 5 3 8 := by
    rintro ⟨j, ev, hj, hev, _, heff, hf, _⟩
    have hlen : j < 11 := (List.getElem?_eq_some_iff.mp hev).1
    interval_cases j <;> first
      | omega
      | (revert heff hf; unfold EffectiveEvent TopEvidence ContestEvidence; decide +kernel)
  refine ⟨?_, hnophase, hnoserve, ?_⟩
  · rcases q5contest with h | h | h
    · exact (hnophase h).elim
    · exact h
    · obtain ⟨t, _, _, hs⟩ := h
      exact (hnoserve ⟨t, hs⟩).elim
  · rintro ⟨j, ev, hj, hev, ht, heff, _⟩
    have hlen : j < 11 := (List.getElem?_eq_some_iff.mp hev).1
    interval_cases j <;> first
      | omega
      | (revert heff; unfold EffectiveEvent TopEvidence ContestEvidence; decide +kernel)
      | (simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hev; subst hev; exact absurd ht (by decide))

-- Bad trace: with the repair allowance shortened to 0 (deadline 7), the phase still holds
-- through 7 with no honest proposal, so the local repair service fails and no result of
-- the consumer holds by 7. All other premises are those proved above.
private theorem q5shortened :
    ¬ FrontierRepairAllowance q5R q5env q5rho q5O q5T q5I 4 1 4 0 7 ∧
    ¬ FrontierHG3Result q5R q5S q5env q5rho q5O q5T q5I Row.height_pair 4 1 5 3 4 7 := by
  have hp7 : PhaseInterval q5R q5env q5rho q5O 7 7 3 none true := by
    refine ⟨le_rfl, by decide, by decide, ?_⟩
    intro i x hi hi' _
    cases x
    have h1 : V2.D.Run.idxBefore q5rho 7 = 8 := by decide
    have h2 : timeIdx q5rho 7 = 9 := by decide
    rw [h1] at hi
    rw [h2] at hi'
    interval_cases i <;> decide +kernel
  refine ⟨?_, ?_⟩
  · rintro ⟨_, l, _, hrep⟩
    obtain ⟨_, hex⟩ := hrep (by decide) 7 3 none true (by decide) hp7
    obtain ⟨s, Q, _, _, hQ, _⟩ := hex (by decide)
    exact q5noProposal hQ
  · rintro (⟨j, ev, hj, hev, ht, heff, _⟩ | ⟨j, ev, hj, hev, ht, heff, _⟩ | ⟨t, _, _, hs⟩)
    rotate_left 2
    · obtain ⟨_, _, _, _, _, _, _, hQ, _⟩ := hs
      exact q5noProposal hQ
    all_goals
      have hlen : j < 11 := (List.getElem?_eq_some_iff.mp hev).1
      interval_cases j <;> first
        | omega
        | (revert heff; unfold EffectiveEvent TopEvidence ContestEvidence; decide +kernel)
        | (simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.some.injEq] at hev; subst hev; exact absurd ht (by decide))

/-! G0 P0d5d-a on `q5`: the composition core at the actual contest start (index 5, time 4,
frontier 3), allowance 1, tail 0, t0 = 4, deadline 4 + remaining = 8 = horizon (closed).
Every phase result is the generic consumer's result at that start; every other start
either is not a start or misses its own budget horizon. -/

private theorem q5budget_big (k : PhaseKind) (hk : k ≠ .contest) :
    (8 : Time) < 4 + interruptedRepairBudget q5T 4 1 1 k := by
  cases k
  · decide +kernel
  · decide +kernel
  · exact absurd rfl hk

private theorem q5step : ∀ i ev m kind,
    FrontierSearchStart q5R q5env q5rho q5O q5T 4 i ev m kind → (4 : Time) ≤ ev.time →
    ev.time + interruptedRepairBudget q5T 4 1 1 kind ≤ q5rho.horizon →
    FirstPhaseStopBy q5R q5env q5rho q5O i m (ev.time + interruptedRepairBudget q5T 4 1 1 kind) ∨
    FirstRiseStopBy q5R q5env q5rho q5O i m (ev.time + interruptedRepairBudget q5T 4 1 1 kind) ∨
    ∃ t, ev.time ≤ t ∧ t ≤ ev.time + interruptedRepairBudget q5T 4 1 1 kind ∧
      StrongServed q5R q5S q5env q5rho q5O q5T q5I Row.height_pair 4 1 m t := by
  intro i ev m kind hst hdl hph
  obtain ⟨hi, _, heff, hf, _, _⟩ :=
    (FrontierSearchStart_def q5R q5env q5rho q5O q5T 4 i ev m kind).mp hst
  cases kind with
  | gap =>
    have := q5budget_big .gap (by intro h; cases h)
    have h8 : q5rho.horizon = 8 := rfl
    linarith
  | topJ =>
    have := q5budget_big .topJ (by intro h; cases h)
    have h8 : q5rho.horizon = 8 := rfl
    linarith
  | contest =>
    have hlen : i < 11 := (List.getElem?_eq_some_iff.mp hi).1
    interval_cases i <;> simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hi <;> subst hi
    all_goals first
      | exact absurd hdl (by decide)
      | exact absurd hph (by decide)
      | skip
    · exfalso
      rcases heff with heff | ⟨rG, _, _, ht, _⟩
      · revert heff
        unfold EffectiveEvent TopEvidence ContestEvidence
        decide +kernel
      · change (4 : Int) = 8 * ((rG + 2 : Nat) : Int) + 6 at ht
        omega
    · have hm : m = 3 := by rw [← hf]; decide +kernel
      subst hm
      exact (FrontierHG3Result_def q5R q5S q5env q5rho q5O q5T q5I Row.height_pair 4 1 5 3 4
        _).mp q5contest

private theorem q5compose :
    FrontierRiseBy q5R q5env q5rho 5 3 (4 + frontierSearch_remaining q5T 4 1 1 0 .contest) ∨
    ∃ t, (4 : Time) ≤ t ∧ t + 0 ≤ 4 + frontierSearch_remaining q5T 4 1 1 0 .contest ∧
      StrongServed q5R q5S q5env q5rho q5O q5T q5I Row.height_pair 4 1 3 t :=
  frontierSearch_phase_compose (R := q5R) (O := q5O) (T := q5T) (E := q5env) (rho := q5rho)
    (Ef := q5E) (Jst := 4) (obs := q5obs) (cert := q5cert) (inv := q5inv) (justif := q5justif)
    (keep := q5keep) q5TLaws q5crossing q5schedule q5mono
    (StrongServed q5R q5S q5env q5rho q5O q5T q5I Row.height_pair 4 1) (G := 4) (ΔF := 1)
    (ρbar := 1) (t0 := 4) (tail := 0) (by decide) (by decide) le_rfl q5step q5start le_rfl
    (by decide +kernel)

-- Every premise of q5compose on the exact run, in the order of the call: observation,
-- certificate, store invariant, justification and retention laws; timing laws; crossing,
-- schedule and order; 4Δ ≤ G, allowance and tail nonnegative; the quantified per-start
-- phase result; the start, its delay guard, and the deadline within the horizon. Also the
-- nonempty honest scope and the actual repair allowance at the start.
private theorem q5compose_premises_sat :
    FGObservationLaws q5R q5O ∧ FGCertificateLaws q5E q5O.height q5O.finality ∧
    (∀ i x, FGStoreInvariant q5O.height q5O.finality
      (q5R.core (q5rho.stateBefore q5env i x)).fg) ∧
    FGJustificationLaws q5O.height ∧
    (∀ i j, i ≤ j → ∀ x, TFAt q5R q5env q5rho i x ⊆ TFAt q5R q5env q5rho j x) ∧
    FGTimingLaws q5T ∧ RXing q5R q5env q5rho q5O ∧ V2.D.ScheduleWellFormed q5env q5rho ∧
    FGRunOrderLaws q5env q5rho q5R ∧ (4 : Time) * q5T.delta ≤ 4 ∧ (0 : Time) ≤ 1 ∧
    (0 : Time) ≤ 0 ∧
    (∀ i ev m kind,
      FrontierSearchStart q5R q5env q5rho q5O q5T 4 i ev m kind → (4 : Time) ≤ ev.time →
      ev.time + interruptedRepairBudget q5T 4 1 1 kind ≤ q5rho.horizon →
      FirstPhaseStopBy q5R q5env q5rho q5O i m
        (ev.time + interruptedRepairBudget q5T 4 1 1 kind) ∨
      FirstRiseStopBy q5R q5env q5rho q5O i m
        (ev.time + interruptedRepairBudget q5T 4 1 1 kind) ∨
      ∃ t, ev.time ≤ t ∧ t ≤ ev.time + interruptedRepairBudget q5T 4 1 1 kind ∧
        StrongServed q5R q5S q5env q5rho q5O q5T q5I Row.height_pair 4 1 m t) ∧
    FrontierSearchStart q5R q5env q5rho q5O q5T 4 5 (.deliver () ⟨.none, q5r 9 ⟨9⟩⟩ 4) 3
      .contest ∧ (4 : Time) ≤ 4 ∧
    (4 : Time) + frontierSearch_remaining q5T 4 1 1 0 .contest = 8 ∧
    (4 : Time) + frontierSearch_remaining q5T 4 1 1 0 .contest ≤ q5rho.horizon ∧
    q5rho.honest.Nonempty ∧
    FrontierRepairAllowance q5R q5env q5rho q5O q5T q5I 4 1 4 1 (4 + 3 * q5T.delta) :=
  ⟨q5obs, q5cert, q5inv, q5justif, q5keep, q5TLaws, q5crossing, q5schedule, q5mono,
    by decide, by decide, le_rfl, q5step, q5start, le_rfl, by decide +kernel,
    by decide +kernel, ⟨(), by decide⟩, q5allowance 1 le_rfl⟩

-- Interruption before repair: the composed result is the rise arm (index 10, time 8),
-- the repair window [7, 8] saves no seed, and there is no rise by 7.
private theorem q5composeExit :
    FrontierRiseBy q5R q5env q5rho 5 3 8 ∧
    ¬ (∃ t, StrongServed q5R q5S q5env q5rho q5O q5T q5I Row.height_pair 4 1 3 t) ∧
    ¬ FrontierRiseBy q5R q5env q5rho 5 3 7 := by
  have hnoserve : ¬ (∃ t, StrongServed q5R q5S q5env q5rho q5O q5T q5I
      Row.height_pair 4 1 3 t) := by
    rintro ⟨t, _, _, _, _, _, _, _, hQ, _⟩
    exact q5noProposal hQ
  have h8 : (4 : Time) + frontierSearch_remaining q5T 4 1 1 0 .contest = 8 := by
    decide +kernel
  refine ⟨?_, hnoserve, ?_⟩
  · rcases q5compose with h | ⟨t, _, _, hs⟩
    · exact h8 ▸ h
    · exact (hnoserve ⟨t, hs⟩).elim
  · rintro ⟨j, ev, hj, hev, ht, hh, _⟩
    have hlen : j < 11 := (List.getElem?_eq_some_iff.mp hev).1
    interval_cases j <;> first
      | omega
      | (revert hh; decide +kernel)
      | (simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hev; subst hev; exact absurd ht (by decide))

-- The rise-stop consumer: the first rise stop of the phase is a first frontier rise.
private theorem q5riseOfStop : FrontierRiseBy q5R q5env q5rho 5 3 8 := by
  obtain ⟨h, _, _, _⟩ := q5contestExit
  exact frontierSearch_rise_of_stop q5R q5O q5env q5rho q5schedule (by decide +kernel) h

-- Every premise of q5riseOfStop on the exact run: schedule, nonempty honest scope, the
-- frontier at the start cut is 3, the actual first rise stop (index 10, time 8), and its
-- deadline 8 within the horizon 8.
private theorem q5riseOfStop_premises_sat :
    V2.D.ScheduleWellFormed q5env q5rho ∧ q5rho.honest.Nonempty ∧
    frontierAtIdx q5R q5env q5rho (5 + 1) ≤ 3 ∧
    FirstRiseStopBy q5R q5env q5rho q5O 5 3 8 ∧
    q5rho.events[10]? = some (.deliver () ⟨.none, q5r 9 ⟨9⟩⟩ 8) ∧
    (8 : Time) ≤ q5rho.horizon :=
  ⟨q5schedule, ⟨(), by decide⟩, by decide +kernel, q5contestExit.1, rfl, le_rfl⟩

-- Isolated negative (shortened allowance 0, deadline 4 + 3 = 7): all other premises are
-- those above. The phase result at the actual start fails (no repair is served), and so
-- does the composed conclusion.
private theorem q5composeShort :
    (4 : Time) + frontierSearch_remaining q5T 4 1 0 0 .contest = 7 ∧
    ¬ (FirstPhaseStopBy q5R q5env q5rho q5O 5 3 7 ∨ FirstRiseStopBy q5R q5env q5rho q5O 5 3 7 ∨
      ∃ t, (4 : Time) ≤ t ∧ t ≤ 7 ∧
        StrongServed q5R q5S q5env q5rho q5O q5T q5I Row.height_pair 4 1 3 t) ∧
    ¬ (FrontierRiseBy q5R q5env q5rho 5 3 7 ∨ ∃ t, (4 : Time) ≤ t ∧ t + 0 ≤ 7 ∧
      StrongServed q5R q5S q5env q5rho q5O q5T q5I Row.height_pair 4 1 3 t) := by
  obtain ⟨_, hbad⟩ := q5shortened
  obtain ⟨_, _, hnorise⟩ := q5composeExit
  refine ⟨by decide +kernel, fun h => hbad ((FrontierHG3Result_def q5R q5S q5env q5rho q5O
    q5T q5I Row.height_pair 4 1 5 3 4 7).mpr h), ?_⟩
  rintro (h | ⟨t, _, _, _, _, _, _, _, _, _, hQ, _⟩)
  · exact hnorise h
  · exact q5noProposal hQ

/-! G0 P0d5d-a, model `mv` (moving lower F, event fold): states 0..3 keep frontier 3, 3, 3
and then 4; the lower F root moves genesis -> mvA -> mvC inside the frontier-3 run. -/

private def mvA : FGBlock (Fin 1) :=
  .node .genesis 1 ⟨41⟩ 7 [⟨0, .vote 1 genesisRoot false, none⟩]
private def mvC : FGBlock (Fin 1) :=
  .node mvA 2 ⟨43⟩ 9 [⟨0, .vote 2 mvA.root false, none⟩]

private abbrev mvR : FGCoreReads q5P 1 Unit Unit (Row (Fin 1)) where
  core st := ⟨(), ⟨{.genesis, mvA, mvC},
    if st = 0 then .genesis else if st = 1 then mvA else mvC,
    .genesis, 0, if st ≤ 2 then 3 else 4⟩, [], []⟩
  erase := q5erase
  source := fun _ => none
  headVote := fun _ _ => .genesis
  finalityHead := fun _ => none
  proposalFG := fun _ _ => none

private noncomputable abbrev mvRho : V2.D.Run Unit q5P where
  honest := {()}
  horizon := 29
  events := [.deliver () ⟨.none, q5r 9 ⟨9⟩⟩ 2, .deliver () ⟨.none, q5r 9 ⟨9⟩⟩ 5,
    .deliver () ⟨.none, q5r 9 ⟨9⟩⟩ 29]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

private theorem mvstate (i : Nat) : mvRho.stateBefore q5env i () = min i 3 := by
  rcases Nat.lt_or_ge i 4 with h | h
  · interval_cases i <;> decide +kernel
  · have he : V2.D.Run.stateBefore q5env mvRho i () =
        V2.D.Run.stateBefore q5env mvRho 3 () := by
      unfold V2.D.Run.stateBefore
      rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp)]
    rw [he, show min i 3 = 3 by omega]
    decide +kernel

private theorem mvmono : FGRunOrderLaws q5env mvRho mvR := by
  constructor
  intro i j x _ hij
  cases x
  rw [mvstate, mvstate]
  have hm : min i 3 ≤ min j 3 := by omega
  have hj : min j 3 ≤ 3 := by omega
  generalize min i 3 = a at hm
  generalize min j 3 = b at hm hj
  interval_cases b <;> interval_cases a <;> decide +kernel

-- Positive: the rise from index 1 (at index 2, time 29) rebases to index 0 across the
-- move of the lower F between indices 1 and 2, while the frontier stays 3.
private theorem mvRise1 : FrontierRiseBy mvR q5env mvRho 1 3 29 :=
  ⟨2, _, by decide, rfl, le_rfl, by decide +kernel, fun k hk hk' => by
    have : k = 2 := by omega
    subst this
    decide +kernel⟩

private theorem mvRebase :
    (mvR.core (mvRho.stateBefore q5env 1 ())).fg.F ≠
      (mvR.core (mvRho.stateBefore q5env 2 ())).fg.F ∧
    frontierAtIdx mvR q5env mvRho 1 = 3 ∧ frontierAtIdx mvR q5env mvRho 2 = 3 ∧
    FrontierRiseBy mvR q5env mvRho 1 3 29 ∧ FrontierRiseBy mvR q5env mvRho 0 3 29 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, mvRise1,
    frontierSearch_rise_rebase mvR q5env mvRho mvmono (by decide) (by decide +kernel) mvRise1⟩

-- Every premise of mvRebase on the exact event fold (no schedule premise: rebase does not
-- read one): nonempty honest scope, order law, index order 0 ≤ 1, frontier at index 2 is at
-- most 3, the rise from index 1 with its event (index 2, delivery at 29), the frontier rise
-- 3 < 4, the cap over indices 2..2, and deadline 29 within the horizon 29.
private theorem mvRebase_premises_sat :
    mvRho.honest.Nonempty ∧ FGRunOrderLaws q5env mvRho mvR ∧ (0 : Nat) ≤ 1 ∧
    frontierAtIdx mvR q5env mvRho (1 + 1) ≤ 3 ∧ FrontierRiseBy mvR q5env mvRho 1 3 29 ∧
    mvRho.events[2]? = some (.deliver () ⟨.none, q5r 9 ⟨9⟩⟩ 29) ∧
    3 < frontierAtIdx mvR q5env mvRho (2 + 1) ∧
    (∀ k, 1 + 1 ≤ k → k ≤ 2 → frontierAtIdx mvR q5env mvRho k ≤ 3) ∧
    (29 : Time) ≤ mvRho.horizon :=
  ⟨⟨(), by decide⟩, mvmono, by decide, by decide +kernel, mvRise1, rfl, by decide +kernel,
    fun k hk hk' => by
      have : k = 2 := by omega
      subst this
      decide +kernel, le_rfl⟩

-- Isolated negative (order law dropped): the frontier dips 5 -> 3 at index 2. The rise
-- from index 1 and the frontier premise hold, but no rise from index 0 exists.
private abbrev mvBadR : FGCoreReads q5P 1 Unit Unit (Row (Fin 1)) where
  core st := ⟨(), ⟨{.genesis, mvA, mvC},
    if st = 0 then .genesis else if st = 1 then mvA else mvC,
    .genesis, 0, if st = 1 then 5 else if st ≤ 2 then 3 else 4⟩, [], []⟩
  erase := q5erase
  source := fun _ => none
  headVote := fun _ _ => .genesis
  finalityHead := fun _ => none
  proposalFG := fun _ _ => none

private theorem mvRebaseBad :
    ¬ FGRunOrderLaws q5env mvRho mvBadR ∧
    FrontierRiseBy mvBadR q5env mvRho 1 3 29 ∧ frontierAtIdx mvBadR q5env mvRho 2 ≤ 3 ∧
    ¬ FrontierRiseBy mvBadR q5env mvRho 0 3 29 := by
  refine ⟨fun h => ?_, ⟨2, _, by decide, rfl, le_rfl, by decide +kernel, fun k hk hk' => by
      have : k = 2 := by omega
      subst this
      decide +kernel⟩, by decide +kernel, ?_⟩
  · have := (h.mono 1 2 () (by decide) (by decide)).2.2
    revert this
    decide +kernel
  · rintro ⟨j, ev, hj, _, _, _, hcap⟩
    have := hcap 1 le_rfl (by omega)
    revert this
    decide +kernel

/-! G0 P0d5d-a, pure data (`pd`, q5 timing, G = 4, ΔF = 1, allowance 1): phase charges. -/

-- Omitted phases: gap -> top J -> contest charges exactly the gap remainder; skipping top J
-- (gap -> contest) costs less; each charge is nonnegative.
private theorem pdOmitted :
    E_gF q5T 1 4 1 + frontierSearch_remaining q5T 4 1 1 0 .topJ =
      frontierSearch_remaining q5T 4 1 1 0 .gap ∧
    E_jF q5T 1 4 1 + frontierSearch_remaining q5T 4 1 1 0 .contest =
      frontierSearch_remaining q5T 4 1 1 0 .topJ ∧
    E_gF q5T 1 4 1 + frontierSearch_remaining q5T 4 1 1 0 .contest <
      frontierSearch_remaining q5T 4 1 1 0 .gap ∧
    frontierSearch_remaining q5T 4 1 1 0 .gap = 40 := by
  decide +kernel

-- No second repair charge: after a seed saved at the contest deadline, only the tail
-- remains; a second repair allowance does not fit in the remaining budget.
private theorem pdNoSecondCharge (tail : Time) :
    interruptedRepairBudget q5T 4 1 1 .contest + tail =
      frontierSearch_remaining q5T 4 1 1 tail .contest ∧
    frontierSearch_remaining q5T 4 1 1 tail .contest <
      interruptedRepairBudget q5T 4 1 1 .contest + (1 + 3 * q5T.delta) + tail := by
  simp only [interruptedRepairBudget_contest_def, frontierSearch_remaining_def,
    frontierSearch_phaseRank_contest_def, Nat.reduceEqDiff, ↓reduceIte]
  change (1 : Int) + 3 * 1 + tail = 0 + 0 + (1 + 3 * 1 + tail) ∧
    (0 : Int) + 0 + (1 + 3 * 1 + tail) < 1 + 3 * 1 + (1 + 3 * 1) + tail
  omega

end AvailableChain.FGCompose.Tests.P0d5da
end
