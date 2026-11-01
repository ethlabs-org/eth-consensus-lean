module
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchRepair
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchGap
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchTail
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchRise
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchTop
public import AvailableChainFGCompose.Proofs.Finality.History -- shake: keep (window views)

set_option linter.privateModule false

public section
noncomputable section
namespace AvailableChain.FGCompose.Tests.P0d5c
open AvailableChain.SimplexFG AvailableChain.KitFG

-- These are inhabited event-fold interface tests, not ExecutionValid claims.
-- The phase store keeps H = 3, no contest and an F root while the lower F moves;
-- the last delivery raises the frontier.
private def d5cA : FGBlock (Fin 1) :=
  .node .genesis 1 ⟨41⟩ 7 [⟨0, .vote 1 genesisRoot false, none⟩]
private def d5cC : FGBlock (Fin 1) :=
  .node d5cA 2 ⟨43⟩ 9 [⟨0, .vote 2 d5cA.root false, none⟩]
private def d5cE : FGBlock (Fin 1) :=
  .node d5cC 3 ⟨45⟩ 11 [⟨0, .vote 3 d5cC.root false, none⟩]
private def d5cRow : Row (Fin 1) := ⟨0, .vote 3 d5cC.root false, some ⟨0, genesisRoot⟩⟩
private def d5cStopRow : Row (Fin 1) := ⟨0, .vote 4 d5cE.root true, some ⟨1, d5cA.root⟩⟩
private def d5cElectorate : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private def d5cHeight : FGHeightView (Fin 1) := simplexHeightView d5cElectorate ⟨0⟩
private def d5cErase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node P s root body _ => .node (d5cErase P) s root body
-- Same phase bits; the lower F root is genesis before the move and d5cA after it.
private def d5cLow : Store (Fin 1) := ⟨{.genesis, d5cA, d5cC}, .genesis, .genesis, 1, 3⟩
private def d5cMoved : Store (Fin 1) := ⟨{.genesis, d5cA, d5cC}, d5cA, .genesis, 1, 3⟩
private def d5cHigh : Store (Fin 1) :=
  ⟨{.genesis, d5cA, d5cC, d5cE}, d5cA, .genesis, 1, 4⟩

private abbrev d5cProtocol : V2.ProtocolSpecD Unit where
  State := Store (Fin 1)
  Label := Nat
  Duty := Nat
  signLabel := id
  seats _ := 1
  Payload := Row (Fin 1)
  Durable := Store (Fin 1)
  init := d5cLow
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
  gossip _ _ := [d5cRow]
  process _ o := if o.payload = d5cStopRow then d5cHigh else d5cMoved
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

private def d5cCore : FGCoreReads d5cProtocol 1 Unit Unit (Row (Fin 1)) where
  core nd := ⟨(), nd, [], []⟩
  erase := d5cErase
  source _ := some d5cC
  headVote _ _ := d5cErase d5cC
  finalityHead _ := some d5cC
  proposalFG _ _ := none
private def d5cObs : FGObservationReads d5cCore where
  height := d5cHeight
  finality _ := ⟨.genesis, 0⟩
  controls nd := treeStoreControlsView d5cHeight nd
  viable nd X := treeStoreFrameView d5cHeight nd X
private theorem d5cObsLaws : FGObservationLaws d5cCore d5cObs where
  controls_eq _ := rfl
  viable_eq _ _ := rfl
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
private abbrev d5cEnv : Generic.Env Unit := ⟨6, by decide, 0, by decide, fun _ _ => true⟩
private def d5cTrace : V2.D.Run Unit d5cProtocol where
  honest := {()}
  horizon := 29
  events := [.deliver () ⟨.none, d5cRow⟩ 2, .deliver () ⟨.none, d5cStopRow⟩ 29]
  seatOf _ _ := ()
  input _ _ := ()

-- G0 (moving lower F inside one phase): the phase interval [1, 5] holds at both indices,
-- while the honest lower F differs between them. No fixed-F interval is assumed.
private theorem d5cMovingF :
    PhaseInterval d5cCore d5cEnv d5cTrace d5cObs 1 5 3 none false ∧
    (d5cCore.core (d5cTrace.stateBefore d5cEnv 0 ())).fg.F ≠
      (d5cCore.core (d5cTrace.stateBefore d5cEnv 1 ())).fg.F ∧
    PhaseInterval d5cCore d5cEnv d5cTrace d5cObs 1 3 3 none false ∧
    (d5cCore.core (d5cTrace.stateBefore d5cEnv 1 ())).fg.h_max = 3 := by
  have hp : PhaseInterval d5cCore d5cEnv d5cTrace d5cObs 1 5 3 none false := by
    refine ⟨by decide, by decide, by decide, ?_⟩
    intro i x hui hiv hx
    have hv : timeIdx d5cTrace 5 = 1 := by decide
    rw [hv] at hiv
    cases x
    interval_cases i <;> decide +kernel
  refine ⟨hp, by decide +kernel, frontierSearch_phase_cut _ _ _ _ hp (by decide) (by decide),
    frontierSearch_phase_hmax _ _ _ _ d5cObsLaws hp (i := 1) (by decide) (by decide)
      (by decide)⟩

-- G0 (effective event before service): the frontier rise at index 1 is the first
-- effective event after the start index 0, at time 29, before a seed saved after 29
-- could serve. The rise arm of the phase result is selected, and it is first.
private theorem d5cRiseExit (pair : Row (Fin 1) → NamedHeightPair)
    (S : FGSafetyReads d5cProtocol 1 (Row (Fin 1))) (I : V2.D.Interface d5cProtocol) :
    FirstEffectiveBy d5cCore d5cEnv d5cTrace d5cObs 0 29 ∧
    FrontierHG3Result d5cCore S d5cEnv d5cTrace d5cObs d5cTiming I pair 0 1 0 3 2 29 ∧
    ¬ FirstEffectiveBy d5cCore d5cEnv d5cTrace d5cObs 0 28 := by
  have hrise : frontierAtIdx d5cCore d5cEnv d5cTrace 1 <
      frontierAtIdx d5cCore d5cEnv d5cTrace 2 := by
    decide +kernel
  refine ⟨⟨1, _, by decide, rfl, le_rfl, Or.inl hrise, fun k hk hk' => by omega⟩,
    Or.inr (Or.inl ⟨1, _, by decide, rfl, le_rfl, Or.inl hrise, by decide +kernel,
      fun k hk hk' => by omega⟩), ?_⟩
  rintro ⟨j, ev, hj, hev, ht, _, _⟩
  have hlen := (List.getElem?_eq_some_iff.mp hev).1
  have hj1 : j = 1 := by
    simp only [d5cTrace, List.length_cons, List.length_nil] at hlen
    omega
  subst hj1
  simp only [d5cTrace, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq] at hev
  subst hev
  exact absurd ht (by decide)

-- G0 (both seed arms): a two-label and a one-label seed both follow the phase start;
-- the first-label threshold itself is not a seed, so a served threshold slot is not
-- charged a second repair.
private theorem d5cSeedArms :
    5 ≤ d5cTiming.proposal 6 ∧ 5 ≤ d5cTiming.proposal 4 ∧
    ¬ FrontierSeedQualification d5cTiming 2 0 5 3 := by
  have hstart : FrontierRepairStart d5cEnv d5cTiming 2 5 (2 + 2 * 2 - 1) :=
    FrontierRepairStart.two 2 (by decide) (fun b hb => by
      change (5 : Int) < 4 * (b : Int) at hb
      by_contra h
      have h1 : (b : Int) ≤ 1 := by exact_mod_cast Nat.le_of_lt_succ (Nat.lt_of_not_le h)
      linarith)
  refine ⟨frontierSearch_seed_after d5cTiming 2 d5cTimingLaws (by decide)
      (frontierSearch_seed_of_start d5cEnv d5cTiming 2 hstart (by decide)),
    frontierSearch_seed_after d5cTiming 2 d5cTimingLaws (GST := 0) (by decide)
      (Or.inr ⟨1, by decide, fun i hi => by
        change (5 : Int) ≤ 4 * (i : Int) + 1 at hi
        by_contra h
        have h1 : (i : Int) ≤ 0 := by exact_mod_cast Nat.le_of_lt_succ (Nat.lt_of_not_le h)
        linarith, by decide, by decide, by decide⟩), ?_⟩
  rintro (⟨β, hβ, hmin, hlt⟩ | ⟨b, hb, hmin, _, _, hlt⟩)
  · have hb2 : β = 2 := by
      refine le_antisymm (hmin 2 (by decide)) ?_
      change (5 : Int) < 4 * (β : Int) at hβ
      by_contra h
      have h1 : (β : Int) ≤ 1 := by exact_mod_cast Nat.le_of_lt_succ (Nat.lt_of_not_le h)
      linarith
    subst hb2
    exact absurd hlt (by decide)
  · have hb1 : b = 1 := by
      refine le_antisymm (hmin 1 (by decide)) ?_
      change (5 : Int) ≤ 4 * (b : Int) + 1 at hb
      by_contra h
      have h1 : (b : Int) ≤ 0 := by exact_mod_cast Nat.le_of_lt_succ (Nat.lt_of_not_le h)
      linarith
    subst hb1
    exact absurd hlt (by decide)

-- G0 (tails): the opening period bound is tight at R = 2, and the row deadline P - 4Δ
-- and the rise deadline 2P + Γ - 9Δ are different deadlines.
private theorem d5cTails :
    8 * d5cTiming.delta ≤ FGCompose.P d5cTiming ∧
    FGCompose.P d5cTiming = 8 * d5cTiming.delta ∧
    FGCompose.P d5cTiming - 4 * d5cTiming.delta <
      2 * FGCompose.P d5cTiming + Γ d5cTiming 8 - 9 * d5cTiming.delta := by
  exact ⟨frontierSearch_period_bound d5cTiming d5cTimingLaws, by decide, by decide⟩

/-! G0 (review): the generic contest consumer on an inhabited event-fold model.
One honest node ticks at every public time 0..8. A delivery at 4 raises the frontier to 3
in a contested phase (two height-3 tips, stored J = x2 does not reach y1). A delivery at 8
raises it to 4. No honest proposal exists (the interface decodes no block), so every
proposal leaf holds trivially and no seed can be saved: the contest repair window
closes at the frontier rise. This is an interface model, not an ExecutionValid run. -/

private def c5r (h : Nat) (e : BlockId) : Row (Fin 1) := ⟨0, .vote h e false, none⟩
private def c5x1 : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 [c5r 1 genesisRoot]
private def c5x2 : FGBlock (Fin 1) := .node .genesis 1 ⟨2⟩ 0 [c5r 1 genesisRoot]
private def c5y1 : FGBlock (Fin 1) := .node c5x1 2 ⟨3⟩ 0 [c5r 2 ⟨1⟩]
private def c5y2 : FGBlock (Fin 1) := .node c5x2 2 ⟨4⟩ 0 [c5r 2 ⟨2⟩]
private def c5z : FGBlock (Fin 1) := .node c5y1 3 ⟨5⟩ 0 [c5r 3 ⟨3⟩]

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

private abbrev c5P : V2.ProtocolSpecD Unit where
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

private abbrev c5TF (st : Nat) : Finset (FGBlock (Fin 1)) :=
  if st = 0 then {.genesis} else if st = 1 then {.genesis, c5x1, c5x2, c5y1, c5y2}
  else {.genesis, c5x1, c5x2, c5y1, c5y2, c5z}

private abbrev c5R : FGCoreReads c5P 1 Unit Unit (Row (Fin 1)) where
  core st := ⟨(), ⟨c5TF st, .genesis,
    if st = 0 then .genesis else if st = 1 then c5x2 else c5y1,
    if st = 0 then 0 else if st = 1 then 2 else 3,
    if st = 0 then 1 else if st = 1 then 3 else 4⟩, [], []⟩
  erase := c5erase
  source := fun _ => none
  headVote := fun _ _ => .genesis
  finalityHead := fun _ => none
  proposalFG := fun _ _ => none

private def c5E : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private def c5cfg : FGConfig := ⟨4⟩
private abbrev c5H := KitFG.Window.certificateHeight c5E c5cfg 2
private abbrev c5F := KitFG.Window.certificateFinality c5E c5cfg 2

private abbrev c5O : FGObservationReads c5R where
  height := c5H
  finality := c5F
  controls nd := treeStoreControlsView c5H (c5R.core nd).fg
  viable nd X := treeStoreFrameView c5H (c5R.core nd).fg X

private theorem c5obs : FGObservationLaws c5R c5O := ⟨fun _ => rfl, fun _ _ => rfl⟩

private theorem c5TF_mono (st : Nat) : c5TF st ⊆ c5TF (st + 1) := by
  rcases Nat.lt_or_ge st 2 with h | h
  · interval_cases st <;> decide
  · have h0 : st ≠ 0 := by omega
    have h1 : st ≠ 1 := by omega
    have h2 : st + 1 ≠ 0 := by omega
    have h3 : st + 1 ≠ 1 := by omega
    simp only [c5TF, h0, h1, h2, h3, ite_false]
    exact Finset.Subset.refl _

private theorem c5core : FGCoreLaws c5R where
  clock_fg _ _ := rfl
  clock_proposals _ _ := rfl
  clock_rowPool _ _ := rfl
  process_tf st _ := c5TF_mono st
  process_proposals _ _ := List.prefix_rfl
  process_rowPool _ _ := List.prefix_rfl
  own_core _ _ := rfl
  source_mem _ _ h := by cases h
  erase_inj := c5erase_inj

private noncomputable abbrev c5S : FGSafetyReads c5P 1 (Row (Fin 1)) where
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

private def c5I : V2.D.Interface c5P where
  confirmed _ := .genesis
  stable _ := .genesis
  block _ := none
  opening _ := False
  propLabel s := s
  propDuty s := s
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective _ _ h := h

private abbrev c5env : Generic.Env Unit := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩

private noncomputable abbrev c5rho : V2.D.Run Unit c5P where
  honest := {()}
  horizon := 8
  events := [.tick () 0, .tick () 1, .tick () 2, .tick () 3, .tick () 4,
    .deliver () ⟨.none, c5r 9 ⟨9⟩⟩ 4, .tick () 5, .tick () 6, .tick () 7, .tick () 8,
    .deliver () ⟨.none, c5r 9 ⟨9⟩⟩ 8]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

private theorem c5nonneg : ∀ e ∈ c5rho.events, 0 ≤ e.time := by decide

private theorem c5schedule : V2.D.ScheduleWellFormed c5env c5rho where
  horizon_nonneg := by decide
  sorted := by decide
  nodup := by decide
  in_horizon := by
    intro e he
    exact ⟨c5nonneg e he, by revert e; decide⟩
  honest_only := by intro e he; simp
  tick_public := by
    intro v t ht
    have h := c5nonneg _ ht
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

private theorem c5state (i : Nat) : c5rho.stateBefore c5env i () =
    if i ≤ 5 then 0 else if i ≤ 10 then 1 else 2 := by
  rcases Nat.lt_or_ge i 12 with h | h
  · interval_cases i <;> decide +kernel
  · have he : V2.D.Run.stateBefore c5env c5rho i () =
        V2.D.Run.stateBefore c5env c5rho 11 () := by
      unfold V2.D.Run.stateBefore
      rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp)]
    rw [he]
    simp only [show ¬ i ≤ 5 by omega, show ¬ i ≤ 10 by omega, ↓reduceIte]
    decide +kernel

private theorem c5state_le (i : Nat) : c5rho.stateBefore c5env i () ≤ 2 := by
  rw [c5state]; split_ifs <;> decide

private theorem c5state_mono {i j : Nat} (hij : i ≤ j) :
    c5rho.stateBefore c5env i () ≤ c5rho.stateBefore c5env j () := by
  rw [c5state, c5state]; split_ifs <;> first | decide | omega

private theorem c5store_inv (st : Nat) (hst : st ≤ 2) :
    FGStoreInvariant c5O.height c5O.finality (c5R.core st).fg := by
  interval_cases st
  all_goals
    constructor
    · intro B hB
      change B ∈ c5TF _ at hB
      simp only [c5TF, ite_true, ite_false, Finset.mem_insert, Finset.mem_singleton,
        show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
        show (2 : Nat) ≠ 1 by decide] at hB
      rcases hB with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · constructor
      · first
        | exact ⟨.genesis, by decide +kernel, by decide +kernel, rfl, rfl⟩
        | exact ⟨c5y2, by decide +kernel, by decide +kernel, rfl, rfl⟩
        | exact ⟨c5z, by decide +kernel, by decide +kernel, rfl, rfl⟩
      · intro B hB _
        change B ∈ c5TF _ at hB
        simp only [c5TF, ite_true, ite_false, Finset.mem_insert, Finset.mem_singleton,
          show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
          show (2 : Nat) ≠ 1 by decide] at hB
        rcases hB with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    · decide +kernel
    · exact ⟨.genesis, by decide +kernel, rfl⟩

private theorem c5inv (i : Nat) (x : Unit) : FGStoreInvariant c5O.height c5O.finality
    (c5R.core (c5rho.stateBefore c5env i x)).fg := by
  cases x
  exact c5store_inv _ (c5state_le i)

private theorem c5cert : FGCertificateLaws c5E c5O.height c5O.finality :=
  KitFG.Window.windowCertificateLaws c5E c5cfg 2
    (by unfold Electorate.IsQuorum; decide +kernel) (by decide)

private theorem c5justif : FGJustificationLaws c5O.height :=
  FGJustificationLaws.of_bridge (KitFG.Window.windowHeightBridge c5E c5cfg 2 (by decide))

private theorem c5TF_le {a b : Nat} (hab : a ≤ b) (hb : b ≤ 2) : c5TF a ⊆ c5TF b := by
  interval_cases b <;> interval_cases a <;> decide

private theorem c5keep : ∀ i j, i ≤ j → ∀ x,
    TFAt c5R c5env c5rho i x ⊆ TFAt c5R c5env c5rho j x := by
  intro i j hij x
  cases x
  exact c5TF_le (c5state_mono hij) (c5state_le j)

private theorem c5mono : FGRunOrderLaws c5env c5rho c5R := by
  constructor
  intro i j x _ hij
  cases x
  have hm := c5state_mono (i := i) (j := j) hij
  have hj := c5state_le j
  generalize c5rho.stateBefore c5env i () = a at hm
  generalize c5rho.stateBefore c5env j () = b at hm hj
  interval_cases b <;> interval_cases a <;> decide

private theorem c5crossing : RXing c5R c5env c5rho c5O := by
  intro i i' x y K W _ _ _ _ _ _
  exact genesis_preceq W

private abbrev c5receipt (B : Block) (d : Time) (y : Unit) : Prop :=
  ∃ W, c5erase W = B ∧ W ∈ (c5R.core (c5rho.stateBeforeTime c5env d y)).fg.TF

private theorem c5noProposal {s : Slot} {Q : Block} (h : HonestProposal c5env c5rho c5I s Q) :
    False := by
  obtain ⟨_, _, _, hb⟩ := h
  cases hb

private theorem c5ready : ∀ t, (4 : Time) ≤ t →
    c5env.t_GST ≤ slotStartZ d5cTiming (((slotAt d5cTiming t : Slot) : Int) - 1) := by
  intro t ht
  have ht' : (4 : Int) ≤ t := ht
  change (0 : Int) ≤ 4 * 1 * ((((t / (4 * 1)).toNat : Nat) : Int) - 1)
  have h1 : (1 : Int) ≤ t / 4 := by omega
  have h2 : (((t / 4).toNat : Nat) : Int) = t / 4 := Int.toNat_of_nonneg (by omega)
  simp only [Int.mul_one] at *
  rw [h2]
  omega

-- Receipt scope at an event of the model: the witness is held at the read deadline.
private theorem c5scope (W : FGBlock (Fin 1)) (d : Time)
    (hW : W ∈ (c5R.core (c5rho.stateBeforeTime c5env d ())).fg.TF) :
    WitnessReceiptScope c5R c5env c5rho (fun _ => true) c5receipt W d :=
  ⟨fun _ y _ _ _ _ _ _ => by cases y; exact ⟨W, rfl, hW⟩⟩

private theorem c5services : ∀ i (ev : V2.Event Unit c5P.Object) m,
    c5rho.events[i]? = some ev → (4 : Time) ≤ ev.time → 1 ≤ m →
    frontierAtIdx c5R c5env c5rho (i + 1) = m → ev.time + d5cTiming.delta ≤ c5rho.horizon →
    PhaseWitnessReceiptScope c5R c5env c5rho c5O (fun _ => true) c5receipt (i + 1) m
      (ev.time + d5cTiming.delta) := by
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
    | exact ⟨(), c5y1, ⟨by decide, by decide +kernel⟩, by decide +kernel,
        c5scope _ _ (by decide +kernel)⟩
    | exact ⟨(), .genesis, ⟨by decide, by decide +kernel⟩, by decide +kernel,
        c5scope _ _ (by decide +kernel)⟩
    | exact fun _ => ⟨(), c5y2, ⟨by decide, by decide +kernel⟩, by decide +kernel,
        by decide +kernel, by decide +kernel, c5scope _ _ (by decide +kernel)⟩
    | exact fun _ => ⟨(), .genesis, ⟨by decide, by decide +kernel⟩, by decide +kernel,
        by decide +kernel, by decide +kernel, c5scope _ _ (by decide +kernel)⟩
    | exact fun _ => ⟨(), c5y2, c5y1, ⟨by decide, by decide +kernel⟩,
        ⟨by decide, by decide +kernel⟩, by decide +kernel, by decide +kernel,
        by decide +kernel, by decide +kernel, c5scope _ _ (by decide +kernel),
        c5scope _ _ (by decide +kernel)⟩
    | (rintro ⟨x, _, _, hc⟩; cases x; exact absurd hc (by decide +kernel))

private theorem c5start : FrontierSearchStart c5R c5env c5rho c5O d5cTiming 4 5
    (.deliver () ⟨.none, c5r 9 ⟨9⟩⟩ 4) 3 .contest := by
  refine ⟨rfl, by decide, Or.inl (Or.inl (by decide +kernel)), by decide +kernel, by decide,
    ?_⟩
  exact ⟨(), by decide, by decide +kernel, by decide +kernel⟩

-- The phase from 7 cannot reach 8: the delivery at 8 raises the honest frontier.
private theorem c5phase_breaks {v : Time} (hv : 8 ≤ v) {m : Nat}
    {J : Option (FGBlock (Fin 1))} {contested : Bool}
    (hp : PhaseInterval c5R c5env c5rho c5O 7 v m J contested) : False := by
  have hidx : V2.D.Run.idxBefore c5rho 7 = 8 := by decide
  have ht : 11 ≤ timeIdx c5rho v :=
    (show timeIdx c5rho 8 = 11 by decide) ▸ frontierSearch_timeIdx_mono c5rho hv
  have h8 := (hp.2.2.2 8 () (by omega) (by omega) (by decide)).1
  have h11 := (hp.2.2.2 11 () (by omega) ht (by decide)).1
  rw [h8.symm] at h11
  revert h11
  decide +kernel

private theorem c5allowance (ρbar : Time) (hρ : 1 ≤ ρbar) :
    FrontierRepairAllowance c5R c5env c5rho c5O d5cTiming c5I 4 1 4 ρbar 7 := by
  refine ⟨by linarith, 3, FrontierRepairStart.two (u := 7) 2 (by decide) (fun b hb => ?_), ?_⟩
  · change (7 : Int) < 4 * (b : Int) at hb
    by_contra h
    have : (b : Int) ≤ 1 := by exact_mod_cast Nat.le_of_lt_succ (Nat.lt_of_not_le h)
    linarith
  · intro _ v m J contested _ hp
    refine ⟨fun s Q _ _ hQ => (c5noProposal hQ).elim, fun hb => ?_⟩
    exact (c5phase_breaks (by linarith) hp).elim

-- G0 (contest exit, event before service): the generic contest consumer applied with
-- every premise proved on the model. The repair window [7, 8] closes at the rise.
private theorem c5contest :
    FrontierHG3Result c5R c5S c5env c5rho c5O d5cTiming c5I Row.height_pair 4 1 5 3 4
      (4 + (1 + 3 * d5cTiming.delta)) :=
  frontier_hg3_contest c5R c5S c5env c5rho c5O d5cTiming c5I Row.height_pair 4 1 c5E c5obs
    c5cert c5inv c5justif c5keep (by decide) c5core (fun h => c5erase_mono h)
    (fun _ => true) c5receipt d5cTimingLaws le_rfl c5crossing c5schedule c5mono rfl
    (by decide) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl) c5ready c5services
    (fun W d y _ h => by
      obtain ⟨W', he, hW'⟩ := h
      exact c5erase_inj he ▸ hW')
    (G := 4) (by decide)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ hQ _ => (c5noProposal hQ).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ hQ => (c5noProposal hQ).elim)
    (fun _ _ _ _ _ _ _ _ _ hQ _ _ _ _ _ _ _ _ _ => (c5noProposal hQ).elim)
    c5start (c5allowance 1 le_rfl) (by decide)

-- Inspection: the selected exit is the first rise at index 10 (time 8, the closed
-- deadline); no phase stop and no saved seed exist.
private theorem c5contestExit :
    FirstRiseStopBy c5R c5env c5rho c5O 5 3 8 ∧
    ¬ FirstPhaseStopBy c5R c5env c5rho c5O 5 3 8 ∧
    ¬ (∃ t, StrongServed c5R c5S c5env c5rho c5O d5cTiming c5I Row.height_pair 4 1 3 t) ∧
    ¬ FirstEffectiveBy c5R c5env c5rho c5O 5 7 := by
  have hnoserve : ¬ (∃ t, StrongServed c5R c5S c5env c5rho c5O d5cTiming c5I
      Row.height_pair 4 1 3 t) := by
    rintro ⟨t, _, _, _, _, _, _, _, hQ, _⟩
    exact c5noProposal hQ
  have hnophase : ¬ FirstPhaseStopBy c5R c5env c5rho c5O 5 3 8 := by
    rintro ⟨j, ev, hj, hev, _, heff, hf, _⟩
    have hlen : j < 11 := (List.getElem?_eq_some_iff.mp hev).1
    interval_cases j <;> first
      | omega
      | (revert heff hf; unfold EffectiveEvent TopEvidence ContestEvidence; decide +kernel)
  refine ⟨?_, hnophase, hnoserve, ?_⟩
  · rcases c5contest with h | h | h
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
private theorem c5shortened :
    ¬ FrontierRepairAllowance c5R c5env c5rho c5O d5cTiming c5I 4 1 4 0 7 ∧
    ¬ FrontierHG3Result c5R c5S c5env c5rho c5O d5cTiming c5I Row.height_pair 4 1 5 3 4 7 := by
  have hp7 : PhaseInterval c5R c5env c5rho c5O 7 7 3 none true := by
    refine ⟨le_rfl, by decide, by decide, ?_⟩
    intro i x hi hi' _
    cases x
    have h1 : V2.D.Run.idxBefore c5rho 7 = 8 := by decide
    have h2 : timeIdx c5rho 7 = 9 := by decide
    rw [h1] at hi
    rw [h2] at hi'
    interval_cases i <;> decide +kernel
  refine ⟨?_, ?_⟩
  · rintro ⟨_, l, _, hrep⟩
    obtain ⟨_, hex⟩ := hrep (by decide) 7 3 none true (by decide) hp7
    obtain ⟨s, Q, _, _, hQ, _⟩ := hex (by decide)
    exact c5noProposal hQ
  · rintro (⟨j, ev, hj, hev, ht, heff, _⟩ | ⟨j, ev, hj, hev, ht, heff, _⟩ | ⟨t, _, _, hs⟩)
    rotate_left 2
    · obtain ⟨_, _, _, _, _, _, _, hQ, _⟩ := hs
      exact c5noProposal hQ
    all_goals
      have hlen : j < 11 := (List.getElem?_eq_some_iff.mp hev).1
      interval_cases j <;> first
        | omega
        | (revert heff; unfold EffectiveEvent TopEvidence ContestEvidence; decide +kernel)
        | (simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.some.injEq] at hev; subst hev; exact absurd ht (by decide))

/-! G0 (review): the generic row tail on an inhabited event-fold model.
One honest node ticks at every public time 0..18. It signs an entry-1 row at action 0
(time 6), proposes erase x1 for slot 2 at time 8 and signs an entry-2 row at action 1
(time 14). Deliveries at 7 and 15 raise the frontier to 2 and to 3. The saved seed is the
slot-2 proposal in the phase [8, 14] at height 2; its continuing service is proved for
each capped endpoint. This is an interface model, not an ExecutionValid run. -/

private def r6row1 : Row (Fin 1) := c5r 1 genesisRoot
private def r6row2 : Row (Fin 1) := c5r 2 ⟨1⟩

private abbrev r6P : V2.ProtocolSpecD Unit where
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
  act _ d _ := if d = 6 then some (.inl r6row1) else if d = 14 then some (.inl r6row2)
    else if d = 8 then some (.inr (c5erase c5x1)) else none
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

private abbrev r6TF (st : Nat) : Finset (FGBlock (Fin 1)) :=
  if st = 0 then {.genesis} else if st = 1 then {.genesis, c5x1} else {.genesis, c5x1, c5y1}

private abbrev r6R : FGCoreReads r6P 1 Unit Unit (Row (Fin 1)) where
  core st := ⟨(), ⟨r6TF st, .genesis, if st ≤ 1 then .genesis else c5x1,
    if st = 0 then 0 else if st = 1 then 1 else 2,
    if st = 0 then 1 else if st = 1 then 2 else 3⟩, [], []⟩
  erase := c5erase
  source st := if st = 0 then none else some c5x1
  headVote _ _ := c5erase c5x1
  finalityHead _ := none
  proposalFG _ _ := none

private abbrev r6O : FGObservationReads r6R where
  height := c5H
  finality := c5F
  controls nd := treeStoreControlsView c5H (r6R.core nd).fg
  viable nd X := treeStoreFrameView c5H (r6R.core nd).fg X

private noncomputable abbrev r6S : FGSafetyReads r6P 1 (Row (Fin 1)) where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode a := ⟨.seat (if a = r6row1 then 6 else 14) 0, .inl a⟩
  decode := some
  decodeObject o := match o.payload with | .inl a => some a | .inr _ => none
  fgLabel := 6
  fgSeats := Equiv.refl _
  record := fun _ => RecordOnce.initial
  inputs := fun _ => (none, ⟨0, ⟨0⟩, 0⟩)
  enabled := fun _ => false
  finalizedOut := fun _ => .genesis

private def r6I : V2.D.Interface r6P where
  confirmed _ := .genesis
  stable _ := .genesis
  block p := match p with | .inr B => some B | .inl _ => none
  opening _ := False
  propLabel s := 4 * s
  propDuty s := 4 * s
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective _ _ h := Nat.eq_of_mul_eq_mul_left (by decide) h

private noncomputable abbrev r6rho : V2.D.Run Unit r6P where
  honest := {()}
  horizon := 18
  events := [.tick () 0, .tick () 1, .tick () 2, .tick () 3, .tick () 4, .tick () 5,
    .tick () 6, .tick () 7, .deliver () ⟨.none, .inl (c5r 9 ⟨9⟩)⟩ 7, .tick () 8,
    .tick () 9, .tick () 10, .tick () 11, .tick () 12, .tick () 13, .tick () 14,
    .tick () 15, .deliver () ⟨.none, .inl (c5r 9 ⟨9⟩)⟩ 15, .tick () 16, .tick () 17,
    .tick () 18]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

private theorem r6nonneg : ∀ e ∈ r6rho.events, 0 ≤ e.time := by decide

private theorem r6schedule : V2.D.ScheduleWellFormed c5env r6rho where
  horizon_nonneg := by decide
  sorted := by decide
  nodup := by decide
  in_horizon := by
    intro e he
    exact ⟨r6nonneg e he, by revert e; decide⟩
  honest_only := by intro e he; simp
  tick_public := by
    intro v t ht
    have h := r6nonneg _ ht
    refine ⟨t.toNat, ?_⟩
    simp only [V2.Event.time] at h
    change (t : Int) = ((t.toNat : Nat) : Int) * 1
    rw [Int.toNat_of_nonneg h, Int.mul_one]
  tick_total := by
    intro v _ t ht _ hh _
    obtain ⟨k, rfl⟩ := ht
    have hk : k ≤ 18 := by
      change ((k : Nat) : Int) * 1 ≤ 18 at hh
      omega
    cases v
    interval_cases k <;> decide

private theorem r6state (i : Nat) : r6rho.stateBefore c5env i () =
    if i ≤ 8 then 0 else if i ≤ 17 then 1 else 2 := by
  rcases Nat.lt_or_ge i 22 with h | h
  · interval_cases i <;> decide +kernel
  · have he : V2.D.Run.stateBefore c5env r6rho i () =
        V2.D.Run.stateBefore c5env r6rho 21 () := by
      unfold V2.D.Run.stateBefore
      rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp)]
    rw [he]
    simp only [show ¬ i ≤ 8 by omega, show ¬ i ≤ 17 by omega, ↓reduceIte]
    decide +kernel

private theorem r6state_le (i : Nat) : r6rho.stateBefore c5env i () ≤ 2 := by
  rw [r6state]; split_ifs <;> decide

private theorem r6state_mono {i j : Nat} (hij : i ≤ j) :
    r6rho.stateBefore c5env i () ≤ r6rho.stateBefore c5env j () := by
  rw [r6state, r6state]; split_ifs <;> first | decide | omega

private theorem r6store_inv (st : Nat) (hst : st ≤ 2) :
    FGStoreInvariant r6O.height r6O.finality (r6R.core st).fg := by
  interval_cases st
  all_goals
    constructor
    · intro B hB
      change B ∈ r6TF _ at hB
      simp only [r6TF, ite_true, ite_false, Finset.mem_insert, Finset.mem_singleton,
        show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
        show (2 : Nat) ≠ 1 by decide] at hB
      rcases hB with rfl | rfl | rfl <;> decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · constructor
      · first
        | exact ⟨.genesis, by decide +kernel, by decide +kernel, rfl, rfl⟩
        | exact ⟨c5x1, by decide +kernel, by decide +kernel, rfl, rfl⟩
        | exact ⟨c5y1, by decide +kernel, by decide +kernel, rfl, rfl⟩
      · intro B hB _
        change B ∈ r6TF _ at hB
        simp only [r6TF, ite_true, ite_false, Finset.mem_insert, Finset.mem_singleton,
          show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
          show (2 : Nat) ≠ 1 by decide] at hB
        rcases hB with rfl | rfl | rfl <;> decide +kernel
    · decide +kernel
    · exact ⟨.genesis, by decide +kernel, rfl⟩

private theorem r6inv (i : Nat) (x : Unit) : FGStoreInvariant r6O.height r6O.finality
    (r6R.core (r6rho.stateBefore c5env i x)).fg := by
  cases x
  exact r6store_inv _ (r6state_le i)

private theorem r6cert : FGCertificateLaws c5E r6O.height r6O.finality := c5cert

private theorem r6mono : FGRunOrderLaws c5env r6rho r6R := by
  constructor
  intro i j x _ hij
  cases x
  have hm := r6state_mono (i := i) (j := j) hij
  have hj := r6state_le j
  generalize r6rho.stateBefore c5env i () = a at hm
  generalize r6rho.stateBefore c5env j () = b at hm hj
  interval_cases b <;> interval_cases a <;> decide

private abbrev r6chain (_ : r6P.State) (_ : Block) : List (Row (Fin 1)) := [r6row1, r6row2]

private theorem r6row1At : HonestRowAt r6S c5env r6rho d5cTiming 6 () 0 r6row1 := by
  unfold HonestRowAt; decide +kernel

private theorem r6row2At : HonestRowAt r6S c5env r6rho d5cTiming 15 () 1 r6row2 := by
  unfold HonestRowAt; decide +kernel

private theorem r6cap : RCap r6R r6S c5env r6rho r6O d5cTiming
    (fun a => namedEntry (Row.height_pair a)) r6chain := by
  intro y i x W hW hy
  change y + 2 ≤ (c5H W).h at hy
  obtain ⟨hx, hW⟩ := hW
  cases x
  change W ∈ r6TF (r6rho.stateBefore c5env i ()) at hW
  rw [r6state] at hW
  split_ifs at hW with h1 h2
  · simp only [r6TF, ite_true, Finset.mem_singleton] at hW
    subst hW
    have : (c5H FGBlock.genesis).h = 1 := by decide +kernel
    simp only [Height] at *
    omega
  · simp only [r6TF, show (1 : Nat) ≠ 0 by decide, ite_true, ite_false, Finset.mem_insert,
      Finset.mem_singleton] at hW
    rcases hW with rfl | rfl
    · have : (c5H FGBlock.genesis).h = 1 := by decide +kernel
      simp only [Height] at *
      omega
    · have hy0 : y = 0 := by
        have : (c5H c5x1).h = 2 := by decide +kernel
        simp only [Height] at *
        omega
      subst hy0
      exact ⟨6, (), 0, r6row1, genesisRoot, by omega, r6row1At, rfl, by simp⟩
  · simp only [r6TF, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, ite_false,
      Finset.mem_insert, Finset.mem_singleton] at hW
    rcases hW with rfl | rfl | rfl
    · have : (c5H FGBlock.genesis).h = 1 := by decide +kernel
      simp only [Height] at *
      omega
    · have hy0 : y = 0 := by
        have : (c5H c5x1).h = 2 := by decide +kernel
        simp only [Height] at *
        omega
      subst hy0
      exact ⟨6, (), 0, r6row1, genesisRoot, by omega, r6row1At, rfl, by simp⟩
    · have hy1 : y ≤ 1 := by
        have : (c5H c5y1).h = 3 := by decide +kernel
        simp only [Height] at *
        omega
      interval_cases y
      · exact ⟨6, (), 0, r6row1, genesisRoot, by omega, r6row1At, rfl, by simp⟩
      · exact ⟨15, (), 1, r6row2, ⟨1⟩, by simp only [Height] at *; omega, r6row2At, rfl, by simp⟩

private theorem r6proposal : HonestProposal c5env r6rho r6I 2 (c5erase c5x1) := by
  refine ⟨⟨by decide, by decide⟩, ⟨.seat 8 0, .inr (c5erase c5x1)⟩, ⟨9, ?_, ?_⟩, rfl⟩
  · decide +kernel
  · decide +kernel

private theorem r6phase : PhaseInterval r6R c5env r6rho r6O 8 14 2 (some .genesis) false := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro i x hi hi' _
  cases x
  have h1 : V2.D.Run.idxBefore r6rho 8 = 9 := by decide
  have h2 : timeIdx r6rho 14 = 16 := by decide
  rw [h1] at hi
  rw [h2] at hi'
  interval_cases i <;> decide +kernel

-- Continuing service of the saved seed: the cap holds only through 14, where every
-- clause is checked on the actual reads (HEAD at label 3, opening 1 with its signed
-- entry-2 row and source x1).
private theorem r6service : ∀ v, d5cTiming.gate 2 ≤ v → v ≤ r6rho.horizon →
    (∀ i x, timeIdx r6rho 8 ≤ i → i ≤ timeIdx r6rho v → x ∈ r6rho.honest →
      (r6R.core (r6rho.stateBefore c5env i x)).fg.h_max ≤ 2) →
    FrontierLocalService r6R r6S c5env r6rho r6O d5cTiming r6I Row.height_pair 2
      (c5erase c5x1) c5x1 2 v := by
  intro v hv hvh hcap
  have hv14 : v = 14 := by
    by_contra hne
    have hv15 : (15 : Time) ≤ v := by
      have hv' : (14 : Int) ≤ v := hv
      have hne' : (v : Int) ≠ 14 := hne
      simp only [Height, Time] at *
      omega
    have ht : 18 ≤ timeIdx r6rho v :=
      (show timeIdx r6rho 15 = 18 by decide) ▸ frontierSearch_timeIdx_mono r6rho hv15
    have h := hcap 18 () (by decide) ht (by decide)
    revert h
    decide +kernel
  subst hv14
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x s H _ hs hvs hH
    have hs3 : s = 3 := by
      have hvs' : 4 * ((s : Nat) : Int) + 1 ≤ 14 := hvs
      have hs' : 3 ≤ (s : Nat) := hs
      simp only [Slot, Height, Time] at *
      omega
    subst hs3
    cases x
    have : headAtLabel r6R c5env r6rho d5cTiming () 3 = some (c5erase c5x1) := by
      decide +kernel
    rw [this] at hH
    cases hH
    decide
  · intro s B hs hps _
    have hps' : 4 * ((s : Nat) : Int) ≤ 14 := hps
    have hs' : 4 ≤ (s : Nat) := hs
    simp only [Slot, Height, Time] at *
    omega
  · intro i x _ h
    exact absurd h (by decide)
  · intro s B hlt hg _
    have hlt' : 4 * (2 : Int) < 4 * ((s : Nat) : Int) := hlt
    have hg' : 4 * ((s : Nat) : Int) + 6 ≤ 14 := hg
    simp only [Height, Time] at *
    omega
  · intro r hr hrt
    have hr1 : r = 1 := by
      have hrt' : 8 * ((r : Nat) : Int) + 6 ≤ 14 := hrt
      have hr' : 2 ≤ (r : Nat) * 2 := hr
      simp only [Slot, Height, Time] at *
      omega
    subst hr1
    have hsrc : actionSourceFG r6R c5env r6rho d5cTiming () 1 = some (some c5x1) := by
      decide +kernel
    refine ⟨?_, ⟨⟨1⟩, fun x K _ hK => ?_⟩, fun x K _ hK => ?_, fun _ => by decide⟩
    · intro x _
      cases x
      exact ⟨c5x1, 1, 15, 1, r6row2, by decide +kernel, hsrc, by decide +kernel,
        by decide, le_rfl, r6row2At, by decide +kernel⟩
    · cases x
      rw [hsrc] at hK
      cases hK
      exact ⟨by decide +kernel, by decide +kernel⟩
    · cases x
      rw [hsrc] at hK
      cases hK
      rfl

private theorem r6row :
    FirstHeightRowBy r6S c5env r6rho d5cTiming Row.height_pair 2
      (14 + (FGCompose.P d5cTiming - 4 * d5cTiming.delta)) :=
  healing_frontierTail_row r6R r6S c5env r6rho r6O d5cTiming r6I Row.height_pair r6chain c5E
    r6cert r6inv d5cTimingLaws r6schedule r6mono r6cap r6phase r6proposal le_rfl r6service
    (by decide)

private theorem r6emits (j : Nat) : V2.D.Run.emitsAt c5env r6rho j =
    if j = 6 then [r6S.encode r6row1] else if j = 15 then [r6S.encode r6row2]
    else if j = 9 then [⟨.seat 8 0, .inr (c5erase c5x1)⟩] else [] := by
  rcases Nat.lt_or_ge j 21 with h | h
  · interval_cases j <;> decide +kernel
  · have hn : r6rho.events[j]? = none := List.getElem?_eq_none (by simp; omega)
    simp only [V2.D.Run.emitsAt, hn, show j ≠ 6 by omega, show j ≠ 15 by omega,
      show j ≠ 9 by omega, ↓reduceIte]

-- Every honest row of the model is the entry-1 row at action 0 or the entry-2 row at 1.
private theorem r6rows {j : Nat} {y : Unit} {r : Nat} {a : Row (Fin 1)}
    (h : HonestRowAt r6S c5env r6rho d5cTiming j y r a) :
    (j = 6 ∧ r = 0 ∧ a = r6row1) ∨ (j = 15 ∧ r = 1 ∧ a = r6row2) := by
  obtain ⟨_, hj, hem⟩ := h
  rw [r6emits] at hem
  have hl : j < 21 := (List.getElem?_eq_some_iff.mp hj).1
  cases y
  interval_cases j <;> simp [d5cTiming] at hem hj ⊢
  · exact ⟨hj, hem⟩
  · have h' : (14 : Int) = 8 * ((r : Nat) : Int) + 6 := hj
    exact ⟨by omega, hem.2⟩

-- Inspection: the row tail selects the entry-2 row of action 1 (time 14) as the first
-- height-2 row; the row deadline 14 + (P - 4Δ) = 18 is closed. Bad trace: the shortened
-- deadline 13 has no height-2 row, with every premise of the tail retained.
private theorem r6rowExit :
    FirstHeightRowBy r6S c5env r6rho d5cTiming Row.height_pair 2 18 ∧
    (∀ r, HeightRow r6S c5env r6rho d5cTiming (fun a => namedEntry (Row.height_pair a)) r 2 →
      r = 1) ∧
    ¬ FirstHeightRowBy r6S c5env r6rho d5cTiming Row.height_pair 2 13 := by
  have honly : ∀ r, HeightRow r6S c5env r6rho d5cTiming
      (fun a => namedEntry (Row.height_pair a)) r 2 → r = 1 := by
    rintro r ⟨j, y, a, e, hrow, he⟩
    rcases r6rows hrow with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩
    · exact absurd he (by simp [r6row1, c5r, namedEntry])
    · rfl
  refine ⟨r6row, honly, ?_⟩
  rintro ⟨r, hr, _, ht⟩
  have := honly r hr
  subst this
  exact absurd ht (by decide)

/-! G0 (review 2): one bounded event-fold model for the rise tail and the gap and top-J
consumers. Interface model, not an ExecutionValid run. One honest node ticks at every public
time 0..26 (Δ = ΔF = 1, R = 2, G = 4, GST = 0, Jst = 4, one lease slot). It proposes the
labelled block x_s = node genesis s (no rows) for every slot s = 1..6 at time 4s, and the
proposal is delivered right after its tick. It signs one action row at time 6 whose entry
(7, 77) names no stored height. A progress-certified chain p1..p5 (heights 2..6, no
justification) is delivered at 5, 10, 15, 20, 25, and the justified block c5x1 (height 2,
J = genesis) at 7. Every effective event is at most five units after the previous one. -/

private def m9X (s : Nat) : FGBlock (Fin 1) := .node .genesis s ⟨20 + s⟩ 0 []
private def m9tv (h : Nat) (e : BlockId) : Row (Fin 1) := ⟨0, .vote h e true, none⟩
private def m9p1 : FGBlock (Fin 1) := .node .genesis 4 ⟨31⟩ 0 [m9tv 1 genesisRoot]
private def m9p2 : FGBlock (Fin 1) := .node m9p1 8 ⟨32⟩ 0 [m9tv 2 ⟨31⟩]
private def m9p3 : FGBlock (Fin 1) := .node m9p2 12 ⟨33⟩ 0 [m9tv 3 ⟨32⟩]
private def m9p4 : FGBlock (Fin 1) := .node m9p3 16 ⟨34⟩ 0 [m9tv 4 ⟨33⟩]
private def m9p5 : FGBlock (Fin 1) := .node m9p4 20 ⟨35⟩ 0 [m9tv 5 ⟨34⟩]
private def m9row : Row (Fin 1) := ⟨0, .vote 7 ⟨77⟩ false, none⟩

/-- Delivered blocks, in delivery order. -/
private def m9blocks : List (FGBlock (Fin 1)) :=
  [m9X 1, m9p1, c5x1, m9X 2, m9p2, m9X 3, m9p3, m9X 4, m9X 5, m9p4, m9X 6, m9p5]

private abbrev m9P : V2.ProtocolSpecD Unit where
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
  act _ d _ := if d = 6 then some (.inl m9row)
    else if d % 4 = 0 ∧ 4 ≤ d ∧ d ≤ 24 then some (.inr (c5erase (m9X (d / 4)))) else none
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

private abbrev m9TF (k : Nat) : Finset (FGBlock (Fin 1)) :=
  insert .genesis (m9blocks.take k).toFinset
private abbrev m9hmax (k : Nat) : Nat :=
  if k ≤ 1 then 1 else if k ≤ 4 then 2 else if k ≤ 6 then 3 else if k ≤ 9 then 4
  else if k ≤ 11 then 5 else 6

private abbrev m9R : FGCoreReads m9P 1 Unit Unit (Row (Fin 1)) where
  core st := ⟨(), ⟨m9TF st, .genesis, .genesis, if st ≤ 2 then 0 else 1, m9hmax st⟩, [],
    [m9row]⟩
  erase := c5erase
  source _ := some .genesis
  headVote _ _ := .genesis
  finalityHead _ := none
  proposalFG _ _ := none

private abbrev m9O : FGObservationReads m9R where
  height := c5H
  finality := c5F
  controls nd := treeStoreControlsView c5H (m9R.core nd).fg
  viable nd X := treeStoreFrameView c5H (m9R.core nd).fg X

private theorem m9obs : FGObservationLaws m9R m9O := ⟨fun _ => rfl, fun _ _ => rfl⟩

private noncomputable abbrev m9S : FGSafetyReads m9P 1 (Row (Fin 1)) where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode a := ⟨.seat 6 0, .inl a⟩
  decode := some
  decodeObject o := match o.payload with | .inl a => some a | .inr _ => none
  fgLabel := 6
  fgSeats := Equiv.refl _
  record := fun _ => RecordOnce.initial
  inputs := fun _ => (none, ⟨0, ⟨0⟩, 0⟩)
  enabled := fun _ => false
  finalizedOut := fun _ => .genesis

private def m9D : FGHistoryWireReads m9S where
  heightPair := Row.height_pair
  finalityPair := Row.finality_pair
  signer := fun a => some a.signer
  decode_height _ _ h := by cases Option.some.inj h; rfl
  decode_finality _ _ h := by cases Option.some.inj h; rfl
  decode_signer _ _ h := by cases Option.some.inj h; rfl

private def m9I : V2.D.Interface m9P where
  confirmed _ := .genesis
  stable _ := .genesis
  block p := match p with | .inr B => some B | .inl _ => none
  opening _ := False
  propLabel s := 4 * s
  propDuty s := 4 * s
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective _ _ h := Nat.eq_of_mul_eq_mul_left (by decide) h

private def m9deliver (B : FGBlock (Fin 1)) (t : Time) : V2.Event Unit m9P.Object :=
  .deliver () ⟨.none, .inr (c5erase B)⟩ t

private noncomputable abbrev m9rho : V2.D.Run Unit m9P where
  honest := {()}
  horizon := 26
  events := [.tick () 0, .tick () 1, .tick () 2, .tick () 3, .tick () 4, m9deliver (m9X 1) 4,
    .tick () 5, m9deliver m9p1 5, .tick () 6, .tick () 7, m9deliver c5x1 7,
    .tick () 8, m9deliver (m9X 2) 8, .tick () 9, .tick () 10, m9deliver m9p2 10,
    .tick () 11, .tick () 12, m9deliver (m9X 3) 12, .tick () 13, .tick () 14, .tick () 15,
    m9deliver m9p3 15, .tick () 16, m9deliver (m9X 4) 16, .tick () 17, .tick () 18,
    .tick () 19, .tick () 20, m9deliver (m9X 5) 20, m9deliver m9p4 20, .tick () 21,
    .tick () 22, .tick () 23, .tick () 24, m9deliver (m9X 6) 24, .tick () 25,
    m9deliver m9p5 25, .tick () 26]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

private theorem m9nonneg : ∀ e ∈ m9rho.events, 0 ≤ e.time := by decide

private theorem m9schedule : V2.D.ScheduleWellFormed c5env m9rho where
  horizon_nonneg := by decide
  sorted := by decide
  nodup := by decide
  in_horizon := by
    intro e he
    exact ⟨m9nonneg e he, by revert e; decide⟩
  honest_only := by intro e he; simp
  tick_public := by
    intro v t ht
    have h := m9nonneg _ ht
    refine ⟨t.toNat, ?_⟩
    simp only [V2.Event.time] at h
    change (t : Int) = ((t.toNat : Nat) : Int) * 1
    rw [Int.toNat_of_nonneg h, Int.mul_one]
  tick_total := by
    intro v _ t ht _ hh _
    obtain ⟨k, rfl⟩ := ht
    have hk : k ≤ 26 := by
      change ((k : Nat) : Int) * 1 ≤ 26 at hh
      omega
    cases v
    interval_cases k <;> decide

/-- Deliveries among the first `i` events. -/
private abbrev m9cnt (i : Nat) : Nat :=
  ((m9rho.events.take i).filter (fun e => match e with | .deliver .. => true | _ => false)).length

private theorem m9state (i : Nat) : m9rho.stateBefore c5env i () = m9cnt i := by
  rcases Nat.lt_or_ge i 40 with h | h
  · interval_cases i <;> decide +kernel
  · have he : ∀ j, 39 ≤ j → m9rho.events.take j = m9rho.events := fun j hj =>
      List.take_of_length_le (by simp; omega)
    unfold V2.D.Run.stateBefore
    rw [he i (by omega)]
    have h39 := he 39 le_rfl
    have := (show V2.D.Run.stateBefore c5env m9rho 39 () = m9cnt 39 by decide +kernel)
    unfold V2.D.Run.stateBefore at this
    rw [h39] at this
    rw [this]
    unfold m9cnt
    rw [he i (by omega), h39]

private theorem m9cnt_mono {i j : Nat} (hij : i ≤ j) : m9cnt i ≤ m9cnt j := by
  unfold m9cnt
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [List.take_add, List.filter_append, List.length_append]
  exact Nat.le_add_right _ _

private theorem m9cnt_le (i : Nat) : m9cnt i ≤ 12 := by
  have h := m9cnt_mono (i := i) (j := i + 39) (by omega)
  have h2 : m9cnt (i + 39) = 12 := by
    unfold m9cnt
    rw [List.take_of_length_le (by simp)]
    decide
  omega

private theorem m9store_inv (k : Nat) (hk : k ≤ 12) :
    FGStoreInvariant m9O.height m9O.finality (m9R.core k).fg := by
  interval_cases k <;> constructor <;> decide +kernel

private theorem m9inv (i : Nat) (x : Unit) : FGStoreInvariant m9O.height m9O.finality
    (m9R.core (m9rho.stateBefore c5env i x)).fg := by
  cases x
  rw [m9state]
  exact m9store_inv _ (m9cnt_le i)

private theorem m9TF_mono {a b : Nat} (hab : a ≤ b) : m9TF a ⊆ m9TF b := by
  intro B hB
  simp only [m9TF, Finset.mem_insert, List.mem_toFinset] at hB ⊢
  rcases hB with h | h
  · exact Or.inl h
  · exact Or.inr ((List.take_prefix_take_left (by omega) |>.subset) h)

private theorem m9keep : ∀ i j, i ≤ j → ∀ x,
    TFAt m9R c5env m9rho i x ⊆ TFAt m9R c5env m9rho j x := by
  intro i j hij x
  cases x
  change m9TF (m9rho.stateBefore c5env i ()) ⊆ m9TF (m9rho.stateBefore c5env j ())
  rw [m9state, m9state]
  exact m9TF_mono (m9cnt_mono hij)

private theorem m9mono : FGRunOrderLaws c5env m9rho m9R := by
  constructor
  intro i j x _ hij
  cases x
  rw [m9state, m9state]
  have hm := m9cnt_mono hij
  have hj := m9cnt_le j
  generalize m9cnt i = a at hm
  generalize m9cnt j = b at hm hj
  interval_cases b <;> interval_cases a <;> decide

private theorem m9core : FGCoreLaws m9R where
  clock_fg _ _ := rfl
  clock_proposals _ _ := rfl
  clock_rowPool _ _ := rfl
  process_tf st _ := m9TF_mono (Nat.le_succ st)
  process_proposals _ _ := List.prefix_rfl
  process_rowPool _ _ := List.prefix_rfl
  own_core _ _ := rfl
  source_mem st C h := by
    cases Option.some.inj h
    exact Finset.mem_insert_self _ _
  erase_inj := c5erase_inj

private theorem m9crossing : RXing m9R c5env m9rho m9O := by
  intro i i' x y K W _ _ _ _ _ _
  exact genesis_preceq W

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

private theorem m9erase_parent (X : FGBlock (Fin 1)) :
    (c5erase X).parent = c5erase X.parent := by
  cases X <;> rfl

/-- Slots increase along every parent edge of a block. -/
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

private theorem m9heldSlot : ∀ i x A K,
    K ∈ (m9R.core (m9rho.stateBefore c5env i x)).fg.TF →
    FGBlock.Preceq A K → A.slot ≤ K.slot := by
  intro i x A K hK hAK
  apply m9anc_slot _ hAK
  cases x
  change K ∈ m9TF (m9rho.stateBefore c5env i ()) at hK
  rw [m9state] at hK
  have hall : ∀ B ∈ m9TF 12, m9slotsOK B = true := by decide
  exact hall K (m9TF_mono (m9cnt_le i) hK)

/-- Released objects at a tick of time `d`. -/
private abbrev m9out (d : Nat) : List m9P.Object :=
  if d = 6 then [⟨.seat 6 0, .inl m9row⟩]
  else if d % 4 = 0 ∧ 4 ≤ d ∧ d ≤ 24 then [⟨.seat d 0, .inr (c5erase (m9X (d / 4)))⟩]
  else []

private theorem m9emits (j : Nat) : V2.D.Run.emitsAt c5env m9rho j =
    match m9rho.events[j]? with
    | some (.tick _ t) => m9out t.toNat
    | _ => [] := by
  rcases Nat.lt_or_ge j 39 with h | h
  · interval_cases j <;> decide +kernel
  · have hn : m9rho.events[j]? = none := List.getElem?_eq_none (by simp; omega)
    simp only [V2.D.Run.emitsAt, hn]

/-- The honest proposals are exactly the labelled blocks of slots 1..6. -/
private theorem m9prop {s : Slot} {B : Block} (h : HonestProposal c5env m9rho m9I s B) :
    1 ≤ s ∧ s ≤ 6 ∧ B = c5erase (m9X s) := by
  obtain ⟨⟨hs0, _⟩, o, ⟨i, hi, ho⟩, hb⟩ := h
  rw [m9emits, hi] at ho
  have ht := (m9schedule.in_horizon _ (List.mem_of_getElem? hi)).2
  change ((4 * s : Nat) : Int) ≤ 26 at ht
  change o ∈ m9out (((4 * s : Nat) : Int).toNat) at ho
  rw [Int.toNat_natCast] at ho
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = s := ⟨_, rfl⟩
  subst hk
  have h4 : 4 * k ≤ 26 := by exact_mod_cast ht
  have h1 : 1 ≤ k := hs0
  have hk6 : k ≤ 6 := by omega
  have hne : ¬ 4 * k = 6 := by omega
  have hc : 4 * k % 4 = 0 ∧ 4 ≤ 4 * k ∧ 4 * k ≤ 24 := ⟨by omega, by omega, by omega⟩
  simp only [m9out, hne, hc, and_self, ite_true, ite_false, List.mem_singleton] at ho
  subst ho
  have hdiv : 4 * k / 4 = k := by omega
  rw [hdiv] at hb
  exact ⟨h1, hk6, (Option.some.inj hb).symm⟩

/-- The only honest row is the entry-(7, 77) row of action 0 (event 8, time 6). -/
private theorem m9rows {j : Nat} {y : Unit} {r : Nat} {a : Row (Fin 1)}
    (h : HonestRowAt m9S c5env m9rho d5cTiming j y r a) : j = 8 ∧ r = 0 ∧ a = m9row := by
  obtain ⟨_, hj, hem⟩ := h
  rw [m9emits, hj] at hem
  have ht : (d5cTiming.action r).toNat = 8 * r + 6 := by
    change (8 * ((r : Nat) : Int) + 6).toNat = 8 * r + 6
    omega
  change m9S.encode a ∈ m9out (d5cTiming.action r).toNat at hem
  rw [ht] at hem
  have hm : ¬ ((8 * r + 6) % 4 = 0 ∧ 4 ≤ 8 * r + 6 ∧ 8 * r + 6 ≤ 24) := by omega
  by_cases hr : r = 0
  · subst hr
    simp only [m9out, ite_true, List.mem_singleton] at hem
    have ha : a = m9row := by
      have := congrArg V2.Signed.payload hem
      exact Sum.inl.inj this
    refine ⟨?_, rfl, ha⟩
    have hl : j < 39 := (List.getElem?_eq_some_iff.mp hj).1
    cases y
    interval_cases j <;> first | rfl | exact absurd hj (by decide)
  · have hne : ¬ 8 * r + 6 = 6 := by omega
    simp only [m9out, hne, hm, ite_false, List.not_mem_nil] at hem

private theorem m9idxBefore_mono {a b : Time} (h : a ≤ b) :
    V2.D.Run.idxBefore m9rho a ≤ V2.D.Run.idxBefore m9rho b := by
  change (m9rho.events.filter (fun e => decide (e.time < a))).length ≤
    (m9rho.events.filter (fun e => decide (e.time < b))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left fun e _ he =>
    decide_eq_true ((of_decide_eq_true he).trans_le h)

private theorem m9timeIdx_mono {a b : Time} (h : a ≤ b) : timeIdx m9rho a ≤ timeIdx m9rho b := by
  change (m9rho.events.filter (fun e => decide (e.time ≤ a))).length ≤
    (m9rho.events.filter (fun e => decide (e.time ≤ b))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left fun e _ he =>
    decide_eq_true ((of_decide_eq_true he).trans h)

private theorem m9front (k : Nat) : frontierAtIdx m9R c5env m9rho k = m9hmax (m9cnt k) := by
  unfold frontierAtIdx
  change ({()} : Finset Unit).sup _ = _
  rw [Finset.sup_singleton, m9state]

/-- The labelled proposal of each slot 1..6 is honest (tick indices 4, 11, 17, 23, 28, 34). -/
private theorem m9propOf (s : Nat) (h1 : 1 ≤ s) (h6 : s ≤ 6) :
    HonestProposal c5env m9rho m9I s (c5erase (m9X s)) := by
  interval_cases s
  · exact ⟨⟨by decide, by decide⟩, ⟨.seat 4 0, .inr (c5erase (m9X 1))⟩,
      ⟨4, by decide +kernel, by decide +kernel⟩, rfl⟩
  · exact ⟨⟨by decide, by decide⟩, ⟨.seat 8 0, .inr (c5erase (m9X 2))⟩,
      ⟨11, by decide +kernel, by decide +kernel⟩, rfl⟩
  · exact ⟨⟨by decide, by decide⟩, ⟨.seat 12 0, .inr (c5erase (m9X 3))⟩,
      ⟨17, by decide +kernel, by decide +kernel⟩, rfl⟩
  · exact ⟨⟨by decide, by decide⟩, ⟨.seat 16 0, .inr (c5erase (m9X 4))⟩,
      ⟨23, by decide +kernel, by decide +kernel⟩, rfl⟩
  · exact ⟨⟨by decide, by decide⟩, ⟨.seat 20 0, .inr (c5erase (m9X 5))⟩,
      ⟨28, by decide +kernel, by decide +kernel⟩, rfl⟩
  · exact ⟨⟨by decide, by decide⟩, ⟨.seat 24 0, .inr (c5erase (m9X 6))⟩,
      ⟨34, by decide +kernel, by decide +kernel⟩, rfl⟩

private theorem m9pstate (s : Nat) (h1 : 1 ≤ s) (h6 : s ≤ 6) :
    ∃ nd, proposalStateAt c5env m9rho m9I s = some nd := by
  interval_cases s <;> exact Option.isSome_iff_exists.mp (by decide +kernel)

/-- Proposal reads: the payload carries the erased block; the parent is looked up in the
store; the parent fold is the window derive. -/
private def m9decode (o : m9P.Object) : Option (Slot × Block) :=
  match o.payload with
  | .inr B => some (B.slot, B)
  | .inl _ => none
private def m9parentFG (nd : Nat) (B : Block) : Option (FGBlock (Fin 1)) :=
  (FGBlock.genesis :: m9blocks.take nd).find? (fun A => decide (c5erase A = B))
private def m9fold (_ : Nat) (_ : Slot) (P : FGBlock (Fin 1)) : Window.State (Fin 1) :=
  Window.derive c5E c5cfg 2 P
private def m9parentHeight (nd : Nat) (s : Slot) (P : FGBlock (Fin 1)) : Height × BlockId :=
  ((m9fold nd s P).h, (m9fold nd s P).T_h.root)
private def m9validFor (nd : Nat) (s : Slot) (P : FGBlock (Fin 1)) (a : Row (Fin 1)) : Bool :=
  Window.r6w (m9fold nd s P) a

private theorem m9carrier {s : Slot} {X : FGBlock (Fin 1)} (hX : X.slot = s)
    (hQ : HonestProposal c5env m9rho m9I s (c5erase X)) :
    HonestCarrier c5env m9rho m9I (kernelCarrier m9decode id (fun _ => ([] : List (Row (Fin 1)))))
      s (c5erase X) [] := by
  refine ⟨hQ, ?_⟩
  obtain ⟨_, ⟨auth, payload⟩, hem, hb⟩ := hQ
  cases payload with
  | inl _ => cases hb
  | inr B =>
    cases Option.some.inj hb
    refine ⟨⟨auth, .inr (c5erase X)⟩, hem, c5erase X, ?_, rfl, rfl⟩
    have hs : (c5erase X).slot = X.slot := by cases X <;> rfl
    change some ((c5erase X).slot, c5erase X) = some (s, c5erase X)
    rw [hs, hX]

private theorem m9read : PromotionProposalRead m9R m9S c5env m9rho m9O m9I m9decode id
    (fun _ => []) m9parentFG m9parentHeight m9validFor m9fold := by
  intro s X hQ hXs
  obtain ⟨h1, h6, hX⟩ := m9prop hQ
  have hX' : X = m9X s := c5erase_inj hX
  subst hX'
  refine ⟨⟨[], m9carrier hXs hQ, rfl⟩, ?_⟩
  obtain ⟨nd, hnd⟩ := m9pstate s h1 h6
  exact ⟨nd, hnd, rfl, rfl, rfl, rfl, fun _ => rfl⟩

private theorem m9order : PromotionRowOrder m9R c5env m9rho m9O m9I := by
  intro s X height U hQ _ _ _ i W hW hrow
  obtain ⟨_, _, hX⟩ := m9prop hQ
  have hX' : X = m9X s := c5erase_inj hX
  subst hX'
  have hWg : W = .genesis := (preceq_genesis).mp hW
  subst hWg
  obtain ⟨row, hr, _⟩ := hrow
  cases hr

private theorem m9signer : PromotionRowSigner m9S c5env m9rho d5cTiming m9D := by
  refine ⟨fun _ _ _ a _ => ⟨a, rfl⟩, fun i j r a h => ?_⟩
  obtain ⟨_, _, rfl⟩ := m9rows h
  rw [Subsingleton.elim i 0]
  rfl

private theorem m9capReceipt : PromotionCapReceipt m9R c5env m9rho m9O d5cTiming m9I := by
  intro m s Qfg X hQ _ _ _ _ _
  obtain ⟨h1, h6, hX⟩ := m9prop hQ
  have hX' : X = m9X s := c5erase_inj hX
  subst hX'
  refine ⟨(), Finset.mem_singleton_self _, ?_⟩
  unfold Gen.V2.Duty.HoldsBefore
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = s := ⟨_, rfl⟩
  subst hk
  interval_cases k <;> decide +kernel

private theorem m9fault : c5E.weightOf (historyFaulty m9S m9rho) < c5E.q := by
  have h : historyFaulty m9S m9rho = ∅ := by
    unfold historyFaulty
    ext i
    simp
  rw [h]
  decide

/-- Copy of KitFG `transition_progress_of_cover` (HeightConsume, outside the Compose test
import scope) at `Fin 1`: mature progress coverage advances the height. -/
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

/-- The bridge form of `m9transition_progress` for the window view. -/
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

private theorem m9src {x : Unit} {r : Nat} {K : FGBlock (Fin 1)}
    (h : actionSourceFG m9R c5env m9rho d5cTiming x r = some (some K)) : K = .genesis := by
  unfold actionSourceFG at h
  obtain ⟨nd, _, hnd⟩ := Option.map_eq_some_iff.mp h
  exact (Option.some.inj hnd).symm

/-- No batch premise holds: its quorum rows are the entry-(7, 77) row, while every honest
proposal's parent is genesis, whose read height is (1, genesis). -/
private theorem m9noBatch {r height : Nat} {U X : FGBlock (Fin 1)}
    (h : BatchPrem m9R m9S m9O d5cTiming c5env m9rho m9I m9D c5E m9decode id (fun _ => [])
      (fun _ => []) m9parentFG m9parentHeight m9validFor 1 .progress r height U X) : False := by
  obtain ⟨rows, hcar, _⟩ := h.carrier
  obtain ⟨_, _, hX⟩ := m9prop hcar.1
  obtain ⟨Q, _, hq, hall⟩ := h.valid
  rcases Finset.eq_empty_or_nonempty Q with he | ⟨i, hi⟩
  · rw [he] at hq
    exact absurd hq (by decide)
  obtain ⟨j, r', a, t, _, hrow, _, _, _, _, _, ⟨nd, H, _, hpar, hent⟩⟩ := hall i hi
  obtain ⟨_, _, rfl⟩ := m9rows hrow
  rw [hX] at hpar
  have h0 : m9parentFG nd (c5erase (m9X X.slot)).parent = some .genesis := rfl
  rw [h0] at hpar
  cases Option.some.inj hpar
  have h1 : m9parentHeight nd X.slot .genesis = (1, genesisRoot) := rfl
  rw [h1] at hent
  exact absurd hent (by decide)

-- G0 (review 2): healing_frontierTail_rise_of_seed on the m9 model. Seed: slot 1, block x_1
-- (height 1), u = Jst = 4, t = gate 1 = 10, i = 5 (the seed delivery). Deadline
-- 10 + (2P + Γ - 9Δ) = 21 ≤ horizon 26. Vacuous premises: progressCoverage (no BatchPrem)
-- and the continuing service (the cap ≤ 1 fails at index 8 for every v ≥ 10).
private theorem m9rise :
    FrontierRiseBy m9R c5env m9rho 5 1
      (10 + (2 * FGCompose.P d5cTiming + Γ d5cTiming 4 - 9 * d5cTiming.delta)) :=
  healing_frontierTail_rise_of_seed (R := m9R) (S := m9S) (O := m9O) (T := d5cTiming)
    (E := c5env) (rho := m9rho) (I := m9I) (D := m9D) (Ef := c5E) (decodeProposal := m9decode)
    (bodyErase := id) (bodyRows := fun _ => []) (blockWireRows := fun _ => [])
    (parentFG := m9parentFG) (parentHeight := m9parentHeight) (validFor := m9validFor)
    (fold := m9fold) (Jst := 4) (cert := c5cert) (inv := m9inv) (keep := m9keep)
    (hT := d5cTimingLaws) (schedule := m9schedule) (faultWeight := m9fault)
    (G := 4) (ΔF := 1) (deltaF := le_rfl) (hdelta := rfl)
    (gap := by
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
        exact hhi)
    (hJst := by decide) (mono := m9mono) (eraseParent := m9erase_parent)
    (eraseReflect := m9erase_reflect)
    (slotProposal := by
      intro s hs _ hh
      obtain ⟨k, hk⟩ : ∃ k : ℕ, k = s := ⟨_, rfl⟩
      subst hk
      have h1 : 0 < k := hs.1
      have h26 : 4 * ((k : Nat) : Int) ≤ 26 := hh
      exact ⟨m9X k, m9propOf k h1 (by omega), rfl⟩)
    (read := m9read) (order := m9order) (signer := m9signer) (capReceipt := m9capReceipt)
    (deltaT := 4) (hδ := rfl) (hbound := ⟨by decide⟩)
    (rowsReceipt := by
      intro j y r a h _ x _
      obtain ⟨_, _, rfl⟩ := m9rows h
      exact Or.inl (List.mem_singleton_self _))
    (progressCoverage := fun _ _ _ _ h _ => (m9noBatch h).elim)
    (hfold := m9foldAdvance)
    (honestQuorum := ⟨{0}, fun _ _ => Finset.mem_singleton_self _, by decide⟩)
    (entryAgreement := by
      intro r x y K L _ _ hK hL _
      rw [m9src hK, m9src hL])
    (sourceSlot := by
      intro r x K _ hK
      rw [m9src hK]
      exact Nat.zero_le _)
    (ancestorSlot := by
      intro r x K A _ hK hA
      rw [m9src hK] at hA ⊢
      rw [(preceq_genesis).mp hA])
    (heldSlot := m9heldSlot)
    (proposalSlot := by
      intro q Q K hQ hK
      obtain ⟨_, _, hQ'⟩ := m9prop hQ
      have hK' : K = m9X q := c5erase_inj (hK.trans hQ')
      rw [hK']
      rfl)
    (u := 4) (t := 10) (i := 5) (m := 1) (q := 1) (Q := c5erase (m9X 1)) (Qfg := m9X 1)
    (hready := le_rfl) (hQ := m9propOf 1 le_rfl (by decide)) (he := rfl) (hQm := by decide)
    (hu := by decide) (hqt := by decide)
    (hcopy := ⟨6, (), by decide +kernel⟩)
    (hservice := by
      intro v hv _ hcap
      exfalso
      have hv' : (10 : Int) ≤ v := hv
      have h16 : timeIdx m9rho 10 = 16 := by decide
      have hk := hcap 8 () (by decide) (by
        have := m9timeIdx_mono hv'
        omega) (Finset.mem_singleton_self _)
      revert hk
      rw [m9state]
      decide)
    (hstart := by rw [m9front]; decide)
    (hhor := by decide)

/-- Every first-rise witness after index 5 is the delivery of the height-2 block p1 at
index 7 (time 5). -/
private theorem m9riseWitness {D : Time} {j : Nat} {ev : V2.Event Unit m9P.Object}
    (hj : 5 < j) (hev : m9rho.events[j]? = some ev)
    (hrise : 1 < frontierAtIdx m9R c5env m9rho (j + 1))
    (hcap : ∀ k, 5 + 1 ≤ k → k ≤ j → frontierAtIdx m9R c5env m9rho k ≤ 1) :
    j = 7 ∧ ev = m9deliver m9p1 5 := by
  have _ := D
  by_cases h8 : 8 ≤ j
  · have := hcap 8 (by omega) h8
    rw [m9front] at this
    exact absurd this (by decide)
  · rw [m9front] at hrise
    have hj7 : j = 6 ∨ j = 7 := by omega
    rcases hj7 with rfl | rfl
    · exact absurd hrise (by decide)
    · refine ⟨rfl, ?_⟩
      have h7 : m9rho.events[7]? = some (m9deliver m9p1 5) := by decide
      rw [h7] at hev
      exact (Option.some.inj hev).symm

-- Inspection and bad trace: the consumer's selected rise is the p1 delivery at index 7,
-- time 5, inside the exact closed deadline 21; no rise exists by time 4 (premises kept).
private theorem m9riseExit :
    (10 : Time) + (2 * FGCompose.P d5cTiming + Γ d5cTiming 4 - 9 * d5cTiming.delta) = 21 ∧
    (∀ j ev, 5 < j → m9rho.events[j]? = some ev →
      ev.time ≤ 10 + (2 * FGCompose.P d5cTiming + Γ d5cTiming 4 - 9 * d5cTiming.delta) →
      1 < frontierAtIdx m9R c5env m9rho (j + 1) →
      (∀ k, 5 + 1 ≤ k → k ≤ j → frontierAtIdx m9R c5env m9rho k ≤ 1) →
      j = 7 ∧ ev.time = 5) ∧
    ¬ FrontierRiseBy m9R c5env m9rho 5 1 4 := by
  refine ⟨by decide, fun j ev hj hev _ hrise hcap => ?_, ?_⟩
  · obtain ⟨rfl, rfl⟩ := m9riseWitness (D := 0) hj hev hrise hcap
    exact ⟨rfl, rfl⟩
  · rintro ⟨j, ev, hj, hev, ht, hrise, hcap⟩
    obtain ⟨_, rfl⟩ := m9riseWitness (D := 0) hj hev hrise hcap
    exact absurd ht (by decide)

/-! G0 (review 2), model `g` for the gap-phase, HG3 gap and HG3 top-J consumers. Interface
model, not an ExecutionValid run; Δ = ΔF = 1, R = 2, G = 4, GST = 0, Jst = 4, one lease
slot, horizon 42. One honest node ticks at every time 0..42 and proposes the labelled chain
block x_s (parent x_{s-1}) for every slot s = 1..10 at time 4s; each proposal is delivered
right after its tick. A frontier block B* of height 2 is delivered at time 7: with
`top = false` it is a progress-certified fork block (no justification, gap phase); with
`top = true` it is the justified block c5x1 (h_j = 1, top-J phase). Honest action rows:
action 0 an unrelated row, action 2 a progress row for (1, genesis), actions 3 and 4 a
progress row for (2, x_6). x_6 carries the action-2 row (height 2 at slot 6), x_8 carries
the action-3 row, and x_10 (height 3, time 40) is the first rise after time 7. -/

private def gRow0 : Row (Fin 1) := ⟨0, .vote 7 ⟨77⟩ true, none⟩
private def gRow2 : Row (Fin 1) := ⟨0, .vote 1 genesisRoot true, none⟩
private def gRow3 : Row (Fin 1) := ⟨0, .vote 2 ⟨26⟩ true, none⟩
private def gRows (s : Nat) : List (Row (Fin 1)) :=
  if s = 6 then [gRow2] else if s = 8 then [gRow3] else []
private def gX : Nat → FGBlock (Fin 1)
  | 0 => .genesis
  | s + 1 => .node (gX s) (s + 1) ⟨20 + (s + 1)⟩ 0 (gRows (s + 1))
private def gF : FGBlock (Fin 1) := .node .genesis 4 ⟨31⟩ 0 [gRow2]
private def gB (top : Bool) : FGBlock (Fin 1) := if top then c5x1 else gF

/-- Delivered blocks, in delivery order. -/
private def gDel (top : Bool) : List (FGBlock (Fin 1)) :=
  [gX 1, gB top, gX 2, gX 3, gX 4, gX 5, gX 6, gX 7, gX 8, gX 9, gX 10]

private abbrev gP : V2.ProtocolSpecD Unit where
  State := Nat
  Label := Nat
  Duty := Nat
  signLabel d := if d % 8 = 6 then 6 else d
  seats _ := 1
  Payload := Row (Fin 1) ⊕ FGBlock (Fin 1)
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
  act _ d _ := if d = 6 then some (.inl gRow0) else if d = 22 then some (.inl gRow2)
    else if d = 30 ∨ d = 38 then some (.inl gRow3)
    else if d % 4 = 0 ∧ 4 ≤ d ∧ d ≤ 40 then some (.inr (gX (d / 4))) else none
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

private abbrev gTF (top : Bool) (k : Nat) : Finset (FGBlock (Fin 1)) :=
  insert .genesis ((gDel top).take k).toFinset
private abbrev gHmax (k : Nat) : Nat := if k ≤ 1 then 1 else if k ≤ 10 then 2 else 3
private abbrev gHj (top : Bool) (k : Nat) : Nat := if top && decide (2 ≤ k) then 1 else 0
/-- The newest stored chain block (the stable output) and the action source x_{2r}. -/
private abbrev gTip (k : Nat) : FGBlock (Fin 1) := gX (if k ≤ 1 then k else min (k - 1) 10)
private abbrev gSrc (k : Nat) : FGBlock (Fin 1) := gX (min (k - 2) 10)

private abbrev gR (top : Bool) : FGCoreReads gP 1 Unit Unit (Row (Fin 1)) where
  core st := ⟨(), ⟨gTF top st, .genesis, .genesis, gHj top st, gHmax st⟩, [],
    [gRow0, gRow2, gRow3]⟩
  erase := c5erase
  source st := some (gSrc st)
  headVote _ s := c5erase (gX s)
  finalityHead _ := none
  proposalFG _ _ := none

private abbrev gO (top : Bool) : FGObservationReads (gR top) where
  height := c5H
  finality := c5F
  controls nd := treeStoreControlsView c5H ((gR top).core nd).fg
  viable nd X := treeStoreFrameView c5H ((gR top).core nd).fg X

private theorem gobs (top : Bool) : FGObservationLaws (gR top) (gO top) :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

private noncomputable abbrev gS : FGSafetyReads gP 1 (Row (Fin 1)) where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode a := ⟨.seat 6 0, .inl a⟩
  decode := some
  decodeObject o := match o.payload with | .inl a => some a | .inr _ => none
  fgLabel := 6
  fgSeats := Equiv.refl _
  record := fun _ => RecordOnce.initial
  inputs := fun _ => (none, ⟨0, ⟨0⟩, 0⟩)
  enabled := fun _ => false
  finalizedOut := fun _ => .genesis

private def gWD : FGHistoryWireReads gS where
  heightPair := Row.height_pair
  finalityPair := Row.finality_pair
  signer := fun a => some a.signer
  decode_height _ _ h := by cases Option.some.inj h; rfl
  decode_finality _ _ h := by cases Option.some.inj h; rfl
  decode_signer _ _ h := by cases Option.some.inj h; rfl

private def gI : V2.D.Interface gP where
  confirmed _ := .genesis
  stable st := c5erase (gTip st)
  block p := match p with | .inr B => some (c5erase B) | .inl _ => none
  opening _ := False
  propLabel s := 4 * s
  propDuty s := 4 * s
  propDuty_label s := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k = s := ⟨_, rfl⟩
    subst hk
    change (if 4 * k % 8 = 6 then 6 else 4 * k) = 4 * k
    simp only [show ¬ (4 * k % 8 = 6) by omega, ↓reduceIte]
  propLabel_single _ := rfl
  propLabel_injective _ _ h := Nat.eq_of_mul_eq_mul_left (by decide) h

private def gdeliver (B : FGBlock (Fin 1)) (t : Time) : V2.Event Unit gP.Object :=
  .deliver () ⟨.none, .inr B⟩ t

private noncomputable abbrev grho (top : Bool) : V2.D.Run Unit gP where
  honest := {()}
  horizon := 42
  events := [
    .tick () 0, .tick () 1, .tick () 2, .tick () 3, .tick () 4, gdeliver (gX 1) 4, .tick () 5,
    .tick () 6, .tick () 7, gdeliver (gB top) 7, .tick () 8, gdeliver (gX 2) 8, .tick () 9,
    .tick () 10, .tick () 11, .tick () 12, gdeliver (gX 3) 12, .tick () 13, .tick () 14,
    .tick () 15, .tick () 16, gdeliver (gX 4) 16, .tick () 17, .tick () 18, .tick () 19,
    .tick () 20, gdeliver (gX 5) 20, .tick () 21, .tick () 22, .tick () 23, .tick () 24,
    gdeliver (gX 6) 24, .tick () 25, .tick () 26, .tick () 27, .tick () 28, gdeliver (gX 7) 28,
    .tick () 29, .tick () 30, .tick () 31, .tick () 32, gdeliver (gX 8) 32, .tick () 33,
    .tick () 34, .tick () 35, .tick () 36, gdeliver (gX 9) 36, .tick () 37, .tick () 38,
    .tick () 39, .tick () 40, gdeliver (gX 10) 40, .tick () 41, .tick () 42]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

private theorem gnonneg (top : Bool) : ∀ e ∈ (grho top).events, 0 ≤ e.time := by
  cases top <;> decide

private theorem gschedule (top : Bool) : V2.D.ScheduleWellFormed c5env (grho top) where
  horizon_nonneg := by change (0 : Int) ≤ 42; decide
  sorted := by cases top <;> decide
  nodup := by cases top <;> decide
  in_horizon := by
    intro e he
    exact ⟨gnonneg top e he, by revert e; cases top <;> decide⟩
  honest_only := by intro e he; simp
  tick_public := by
    intro v t ht
    have h := gnonneg top _ ht
    refine ⟨t.toNat, ?_⟩
    simp only [V2.Event.time] at h
    change (t : Int) = ((t.toNat : Nat) : Int) * 1
    rw [Int.toNat_of_nonneg h, Int.mul_one]
  tick_total := by
    intro v _ t ht _ hh _
    obtain ⟨k, rfl⟩ := ht
    have hk : k ≤ 42 := by
      change ((k : Nat) : Int) * 1 ≤ 42 at hh
      omega
    cases v
    cases top <;> interval_cases k <;> decide

/-- Deliveries among the first `i` events (the same for both variants). -/
private def gKinds : List Bool :=
  [false, false, false, false, false, true, false, false, false, true, false, true, false, false,
    false, false, true, false, false, false, false, true, false, false, false, false, true, false,
    false, false, false, true, false, false, false, false, true, false, false, false, false, true,
    false, false, false, false, true, false, false, false, false, true, false, false]
private abbrev gcnt (i : Nat) : Nat := ((gKinds.take i).filter id).length

private theorem gstate (top : Bool) (i : Nat) : (grho top).stateBefore c5env i () = gcnt i := by
  rcases Nat.lt_or_ge i 55 with h | h
  · cases top <;> interval_cases i <;> decide +kernel
  · have he : ∀ j, 54 ≤ j → (grho top).events.take j = (grho top).events := fun j hj =>
      List.take_of_length_le (by cases top <;> simp <;> omega)
    unfold V2.D.Run.stateBefore
    rw [he i (by omega)]
    have h54 := he 54 le_rfl
    have := (show V2.D.Run.stateBefore c5env (grho top) 54 () = gcnt 54 by
      cases top <;> decide +kernel)
    unfold V2.D.Run.stateBefore at this
    rw [h54] at this
    rw [this]
    unfold gcnt
    rw [List.take_of_length_le (by simp [gKinds]),
      List.take_of_length_le (by simp [gKinds]; omega)]

private theorem gcnt_mono {i j : Nat} (hij : i ≤ j) : gcnt i ≤ gcnt j := by
  unfold gcnt
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [List.take_add, List.filter_append, List.length_append]
  exact Nat.le_add_right _ _

private theorem gcnt_le (i : Nat) : gcnt i ≤ 11 := by
  have h := gcnt_mono (i := i) (j := i + 54) (by omega)
  have h2 : gcnt (i + 54) = 11 := by
    unfold gcnt
    rw [List.take_of_length_le (by simp [gKinds])]
    decide
  omega

private theorem gidxBefore_mono {V : Type} {P : V2.ProtocolSpecD Unit} (rho : V2.D.Run V P)
    {a b : Time} (h : a ≤ b) : V2.D.Run.idxBefore rho a ≤ V2.D.Run.idxBefore rho b := by
  change (rho.events.filter (fun e => decide (e.time < a))).length ≤
    (rho.events.filter (fun e => decide (e.time < b))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left fun e _ he =>
    decide_eq_true ((of_decide_eq_true he).trans_le h)

private theorem gidxBefore_le_timeIdx {V : Type} {P : V2.ProtocolSpecD Unit}
    (rho : V2.D.Run V P) (a : Time) : V2.D.Run.idxBefore rho a ≤ timeIdx rho a := by
  change (rho.events.filter (fun e => decide (e.time < a))).length ≤
    (rho.events.filter (fun e => decide (e.time ≤ a))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left fun e _ he => decide_eq_true (of_decide_eq_true he).le

private theorem gstore_inv (top : Bool) (k : Nat) (hk : k ≤ 11) :
    FGStoreInvariant (gO top).height (gO top).finality ((gR top).core k).fg := by
  cases top <;> interval_cases k <;> constructor <;> decide +kernel

private theorem ginv (top : Bool) (i : Nat) (x : Unit) :
    FGStoreInvariant (gO top).height (gO top).finality
      ((gR top).core ((grho top).stateBefore c5env i x)).fg := by
  cases x
  rw [gstate]
  exact gstore_inv top _ (gcnt_le i)

private theorem gTF_mono (top : Bool) {a b : Nat} (hab : a ≤ b) : gTF top a ⊆ gTF top b := by
  intro B hB
  simp only [gTF, Finset.mem_insert, List.mem_toFinset] at hB ⊢
  rcases hB with h | h
  · exact Or.inl h
  · exact Or.inr ((List.take_prefix_take_left (by omega) |>.subset) h)

private theorem gkeep (top : Bool) : ∀ i j, i ≤ j → ∀ x,
    TFAt (gR top) c5env (grho top) i x ⊆ TFAt (gR top) c5env (grho top) j x := by
  intro i j hij x
  cases x
  change gTF top ((grho top).stateBefore c5env i ()) ⊆ gTF top ((grho top).stateBefore c5env j ())
  rw [gstate, gstate]
  exact gTF_mono top (gcnt_mono hij)

private theorem gmono (top : Bool) : FGRunOrderLaws c5env (grho top) (gR top) := by
  constructor
  intro i j x _ hij
  cases x
  rw [gstate, gstate]
  have hm := gcnt_mono hij
  have hj := gcnt_le j
  generalize gcnt i = a at hm
  generalize gcnt j = b at hm hj
  cases top <;> interval_cases b <;> interval_cases a <;> decide

private theorem gsrc_mem (top : Bool) (st : Nat) : gSrc st ∈ gTF top st := by
  rcases Nat.lt_or_ge st 12 with h | h
  · cases top <;> interval_cases st <;> decide
  · have h11 : gSrc st = gX 10 := by
      unfold gSrc
      rw [Nat.min_eq_right (by omega)]
    rw [h11]
    exact gTF_mono top (show 11 ≤ st by omega) (by cases top <;> decide)

private theorem gcore (top : Bool) : FGCoreLaws (gR top) where
  clock_fg _ _ := rfl
  clock_proposals _ _ := rfl
  clock_rowPool _ _ := rfl
  process_tf st _ := gTF_mono top (Nat.le_succ st)
  process_proposals _ _ := List.prefix_rfl
  process_rowPool _ _ := List.prefix_rfl
  own_core _ _ := rfl
  source_mem st C h := by
    cases Option.some.inj h
    exact gsrc_mem top st
  erase_inj := c5erase_inj

private theorem gcrossing (top : Bool) : RXing (gR top) c5env (grho top) (gO top) := by
  intro i i' x y K W _ _ _ _ _ _
  exact genesis_preceq W

private theorem gchain_le {a b : Nat} (h : a ≤ b) : FGBlock.Preceq (gX a) (gX b) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => exact preceq_refl _
  | succ k ih =>
    exact preceq_node_of_preceq _ _ _ _ (ih (by omega))

private theorem gchain_anc {A : FGBlock (Fin 1)} {n : Nat} (h : FGBlock.Preceq A (gX n)) :
    ∃ j ≤ n, A = gX j := by
  induction n with
  | zero => exact ⟨0, le_rfl, (preceq_genesis).mp h⟩
  | succ n ih =>
    change (decide (A = gX (n + 1)) || FGBlock.preceq A (gX n)) = true at h
    rw [Bool.or_eq_true] at h
    rcases h with he | hp
    · exact ⟨n + 1, le_rfl, of_decide_eq_true he⟩
    · obtain ⟨j, hj, rfl⟩ := ih hp
      exact ⟨j, by omega, rfl⟩

private theorem gX_slot (s : Nat) : (gX s).slot = s := by cases s <;> rfl
private theorem gX_parent (s : Nat) : (gX (s + 1)).parent = gX s := rfl

private theorem gheldSlot (top : Bool) : ∀ i x A K,
    K ∈ ((gR top).core ((grho top).stateBefore c5env i x)).fg.TF →
    FGBlock.Preceq A K → A.slot ≤ K.slot := by
  intro i x A K hK hAK
  apply m9anc_slot _ hAK
  cases x
  change K ∈ gTF top ((grho top).stateBefore c5env i ()) at hK
  rw [gstate] at hK
  have hall : ∀ B ∈ gTF top 11, m9slotsOK B = true := by cases top <;> decide
  exact hall K (gTF_mono top (gcnt_le i) hK)

/-- Released objects at a tick of time `d`. -/
private abbrev gout (d : Nat) : List gP.Object :=
  if d = 6 then [⟨.seat 6 0, .inl gRow0⟩] else if d = 22 then [⟨.seat 6 0, .inl gRow2⟩]
  else if d = 30 ∨ d = 38 then [⟨.seat 6 0, .inl gRow3⟩]
  else if d % 4 = 0 ∧ 4 ≤ d ∧ d ≤ 40 then [⟨.seat d 0, .inr (gX (d / 4))⟩]
  else []

private theorem gemits (top : Bool) (j : Nat) : V2.D.Run.emitsAt c5env (grho top) j =
    match (grho top).events[j]? with
    | some (.tick _ t) => gout t.toNat
    | _ => [] := by
  rcases Nat.lt_or_ge j 54 with h | h
  · cases top <;> interval_cases j <;> decide +kernel
  · have hn : (grho top).events[j]? = none :=
      List.getElem?_eq_none (by cases top <;> simp <;> omega)
    simp only [V2.D.Run.emitsAt, hn]

/-- The honest proposals are exactly the chain blocks of slots 1..10. -/
private theorem gprop {top : Bool} {s : Slot} {B : Block}
    (h : HonestProposal c5env (grho top) gI s B) : 1 ≤ s ∧ s ≤ 10 ∧ B = c5erase (gX s) := by
  obtain ⟨⟨hs0, _⟩, o, ⟨i, hi, ho⟩, hb⟩ := h
  rw [gemits, hi] at ho
  have ht := ((gschedule top).in_horizon _ (List.mem_of_getElem? hi)).2
  change ((4 * s : Nat) : Int) ≤ 42 at ht
  change o ∈ gout (((4 * s : Nat) : Int).toNat) at ho
  rw [Int.toNat_natCast] at ho
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = s := ⟨_, rfl⟩
  subst hk
  have h4 : 4 * k ≤ 42 := by exact_mod_cast ht
  have h1 : 1 ≤ k := hs0
  have hk10 : k ≤ 10 := by omega
  have hn6 : ¬ 4 * k = 6 := by omega
  have hn22 : ¬ 4 * k = 22 := by omega
  have hn30 : ¬ (4 * k = 30 ∨ 4 * k = 38) := by omega
  have hc : 4 * k % 4 = 0 ∧ 4 ≤ 4 * k ∧ 4 * k ≤ 40 := ⟨by omega, by omega, by omega⟩
  simp only [gout, hn6, hn22, hn30, hc, and_self, ite_true, ite_false,
    List.mem_singleton] at ho
  subst ho
  have hdiv : 4 * k / 4 = k := by omega
  rw [hdiv] at hb
  exact ⟨h1, hk10, (Option.some.inj hb).symm⟩

private theorem gprop_eq {top : Bool} {s : Slot} {X : FGBlock (Fin 1)}
    (h : HonestProposal c5env (grho top) gI s (c5erase X)) : 1 ≤ s ∧ s ≤ 10 ∧ X = gX s := by
  obtain ⟨h1, h2, h3⟩ := gprop h
  exact ⟨h1, h2, c5erase_inj h3⟩

private theorem gpropOf (top : Bool) (s : Nat) (h1 : 1 ≤ s) (h10 : s ≤ 10) :
    HonestProposal c5env (grho top) gI s (c5erase (gX s)) := by
  have key : ∀ j : Nat, (grho top).events[j]? =
      some (.tick (V2.D.proposerOf (grho top) gI s) (V2.D.proposalTime gI s)) →
      (⟨.seat (4 * s) 0, .inr (gX s)⟩ : gP.Object) ∈
        V2.D.Run.emitsAt c5env (grho top) j →
      HonestProposal c5env (grho top) gI s (c5erase (gX s)) := fun j hj ho =>
    ⟨⟨h1, Finset.mem_singleton_self _⟩, _, ⟨j, hj, ho⟩, rfl⟩
  interval_cases s
  · exact key 4 (by cases top <;> decide +kernel) (by cases top <;> decide +kernel)
  · exact key 10 (by cases top <;> decide +kernel) (by cases top <;> decide +kernel)
  · exact key 15 (by cases top <;> decide +kernel) (by cases top <;> decide +kernel)
  · exact key 20 (by cases top <;> decide +kernel) (by cases top <;> decide +kernel)
  · exact key 25 (by cases top <;> decide +kernel) (by cases top <;> decide +kernel)
  · exact key 30 (by cases top <;> decide +kernel) (by cases top <;> decide +kernel)
  · exact key 35 (by cases top <;> decide +kernel) (by cases top <;> decide +kernel)
  · exact key 40 (by cases top <;> decide +kernel) (by cases top <;> decide +kernel)
  · exact key 45 (by cases top <;> decide +kernel) (by cases top <;> decide +kernel)
  · exact key 50 (by cases top <;> decide +kernel) (by cases top <;> decide +kernel)

/-- The honest rows: action 0 (event 7), action 2 (event 28), actions 3 and 4 (events 38,
48). -/
private theorem grows {top : Bool} {j : Nat} {y : Unit} {r : Nat} {a : Row (Fin 1)}
    (h : HonestRowAt gS c5env (grho top) d5cTiming j y r a) :
    (r = 0 ∧ a = gRow0 ∧ j = 7) ∨ (r = 2 ∧ a = gRow2 ∧ j = 28) ∨
      (r = 3 ∧ a = gRow3 ∧ j = 38) ∨ (r = 4 ∧ a = gRow3 ∧ j = 48) := by
  obtain ⟨_, hj, hem⟩ := h
  rw [gemits, hj] at hem
  have ht : (d5cTiming.action r).toNat = 8 * r + 6 := by
    change (8 * ((r : Nat) : Int) + 6).toNat = 8 * r + 6
    omega
  change gS.encode a ∈ gout (d5cTiming.action r).toNat at hem
  rw [ht] at hem
  have hl : j < 54 := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    cases top <;> simpa using this
  cases y
  have hm : ¬ ((8 * r + 6) % 4 = 0 ∧ 4 ≤ 8 * r + 6 ∧ 8 * r + 6 ≤ 40) := by omega
  rcases (show r = 0 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ (r = 1 ∨ 5 ≤ r) by omega) with
    rfl | rfl | rfl | rfl | hr
  · change gS.encode a ∈ [⟨.seat 6 0, .inl gRow0⟩] at hem
    have ha : a = gRow0 := Sum.inl.inj (congrArg V2.Signed.payload (List.mem_singleton.mp hem))
    refine Or.inl ⟨rfl, ha, ?_⟩
    cases top <;> interval_cases j <;> first | rfl | exact absurd hj (by decide)
  · change gS.encode a ∈ [⟨.seat 6 0, .inl gRow2⟩] at hem
    have ha : a = gRow2 := Sum.inl.inj (congrArg V2.Signed.payload (List.mem_singleton.mp hem))
    refine Or.inr (Or.inl ⟨rfl, ha, ?_⟩)
    cases top <;> interval_cases j <;> first | rfl | exact absurd hj (by decide)
  · change gS.encode a ∈ [⟨.seat 6 0, .inl gRow3⟩] at hem
    have ha : a = gRow3 := Sum.inl.inj (congrArg V2.Signed.payload (List.mem_singleton.mp hem))
    refine Or.inr (Or.inr (Or.inl ⟨rfl, ha, ?_⟩))
    cases top <;> interval_cases j <;> first | rfl | exact absurd hj (by decide)
  · change gS.encode a ∈ [⟨.seat 6 0, .inl gRow3⟩] at hem
    have ha : a = gRow3 := Sum.inl.inj (congrArg V2.Signed.payload (List.mem_singleton.mp hem))
    refine Or.inr (Or.inr (Or.inr ⟨rfl, ha, ?_⟩))
    cases top <;> interval_cases j <;> first | rfl | exact absurd hj (by decide)
  · have h6 : ¬ 8 * r + 6 = 6 := by omega
    have h22 : ¬ 8 * r + 6 = 22 := by omega
    have h30 : ¬ (8 * r + 6 = 30 ∨ 8 * r + 6 = 38) := by omega
    simp only [gout, h6, h22, h30, hm, ite_false, List.not_mem_nil] at hem

private theorem gsrcAt (top : Bool) (r : Nat) (hr : r ≤ 4) :
    actionSourceFG (gR top) c5env (grho top) d5cTiming () r = some (some (gX (2 * r))) := by
  interval_cases r <;> cases top <;> decide +kernel

private theorem gsrc {top : Bool} {x : Unit} {r : Nat} {K : FGBlock (Fin 1)}
    (h : actionSourceFG (gR top) c5env (grho top) d5cTiming x r = some (some K)) :
    r ≤ 4 ∧ K = gX (2 * r) := by
  cases x
  by_cases hr : r ≤ 4
  · rw [gsrcAt top r hr] at h
    exact ⟨hr, (Option.some.inj (Option.some.inj h)).symm⟩
  · exfalso
    have hnone : V2.D.Run.tickIdx? (grho top) () (d5cTiming.action r) = none := by
      unfold V2.D.Run.tickIdx?
      rw [List.findIdx?_eq_none_iff]
      intro e he
      have hh := ((gschedule top).in_horizon e he).2
      cases e with
      | tick v t' =>
        simp only [decide_eq_false_iff_not, not_and]
        intro _ ht'
        obtain ⟨z, hz⟩ : ∃ z : Int, z = t' := ⟨_, rfl⟩
        subst hz
        have h1 : z ≤ 42 := hh
        have h2 : z = 8 * ((r : Nat) : Int) + 6 := ht'
        omega
      | _ => rfl
    unfold actionSourceFG postClock preTick at h
    rw [hnone] at h
    cases h

private theorem gfront (top : Bool) (k : Nat) :
    frontierAtIdx (gR top) c5env (grho top) k = gHmax (gcnt k) := by
  unfold frontierAtIdx
  change ({()} : Finset Unit).sup _ = _
  rw [Finset.sup_singleton, gstate]

private theorem gcontest (top : Bool) (k : Nat) :
    (treeStoreControlsView c5H ((gR top).core k).fg).contest = false := by
  rcases Nat.lt_or_ge k 12 with h | h
  · cases top <;> interval_cases k <;> decide +kernel
  · have hk : gHmax k = 3 := by simp only [gHmax]; split_ifs <;> omega
    change (decide (gHmax k = gHj top k + 1) && _) = false
    rw [hk]
    cases top <;> simp [gHj, show 2 ≤ k by omega]

/-- The phase classification of the model (from Jst = 4 on). -/
private abbrev gJ (top : Bool) : Option (FGBlock (Fin 1)) := if top then some .genesis else none

private theorem gphase {top : Bool} {u v : Time} {m : Nat} {J : Option (FGBlock (Fin 1))}
    {c : Bool} (hp : PhaseInterval (gR top) c5env (grho top) (gO top) u v m J c)
    (hu : (4 : Time) ≤ u) :
    (m = 1 ∧ v ≤ 6) ∨ (m = 2 ∧ 8 ≤ u ∧ v ≤ 39 ∧ c = false ∧ J = gJ top) ∨
      (m = 3 ∧ 41 ≤ u) := by
  obtain ⟨huv, hvh, _, hall⟩ := hp
  have hab : V2.D.Run.idxBefore (grho top) u ≤ timeIdx (grho top) v :=
    (gidxBefore_le_timeIdx _ u).trans (frontierSearch_timeIdx_mono _ huv)
  have hA := hall _ () le_rfl hab (Finset.mem_singleton_self _)
  have hB := hall _ () hab le_rfl (Finset.mem_singleton_self _)
  simp only [gstate] at hA hB
  change gHmax (gcnt (V2.D.Run.idxBefore (grho top) u)) = m ∧ _ ∧ _ at hA
  change gHmax (gcnt (timeIdx (grho top) v)) = m ∧ _ ∧ _ at hB
  obtain ⟨zu, hzu⟩ : ∃ z : Int, z = u := ⟨_, rfl⟩
  obtain ⟨zv, hzv⟩ : ∃ z : Int, z = v := ⟨_, rfl⟩
  subst hzu hzv
  have hu' : (4 : Int) ≤ zu := hu
  have huv' : zu ≤ zv := huv
  have hA1 := hA.1
  have hB1 := hB.1
  have hIdx : ∀ a b : Int, a ≤ b → gcnt (V2.D.Run.idxBefore (grho top) a) ≤
      gcnt (V2.D.Run.idxBefore (grho top) b) := fun a b h => gcnt_mono (gidxBefore_mono _ h)
  have hTim : ∀ a b : Int, a ≤ b → gcnt (timeIdx (grho top) a) ≤
      gcnt (timeIdx (grho top) b) := fun a b h => gcnt_mono (frontierSearch_timeIdx_mono _ h)
  have hleA := gcnt_le (V2.D.Run.idxBefore (grho top) zu)
  have hleB := gcnt_le (timeIdx (grho top) zv)
  simp only [gHmax] at hA1 hB1
  by_cases h7 : zu ≤ 7
  · have hi := hIdx zu 7 h7
    have h9 : gcnt (V2.D.Run.idxBefore (grho top) 7) = 1 := by cases top <;> decide
    have hm1 : m = 1 := by split_ifs at hA1 <;> omega
    refine Or.inl ⟨hm1, ?_⟩
    by_contra hv
    have hv' : ¬ zv ≤ 6 := hv
    have hj := hTim 7 zv (by omega)
    have h10 : gcnt (timeIdx (grho top) 7) = 2 := by cases top <;> decide
    split_ifs at hB1 <;> omega
  by_cases h40 : zu ≤ 40
  · have hi := hIdx 8 zu (by omega)
    have hi' := hIdx zu 40 h40
    have h8 : gcnt (V2.D.Run.idxBefore (grho top) 8) = 2 := by cases top <;> decide
    have h40' : gcnt (V2.D.Run.idxBefore (grho top) 40) = 10 := by cases top <;> decide
    have hm2 : m = 2 := by split_ifs at hA1 <;> omega
    have hv39 : zv ≤ 39 := by
      by_contra hv
      have hj := hTim 40 zv (by omega)
      have h52 : gcnt (timeIdx (grho top) 40) = 11 := by cases top <;> decide
      split_ifs at hB1 <;> omega
    have hc : c = false := by
      rw [← hA.2.1]
      exact gcontest top _
    refine Or.inr (Or.inl ⟨hm2, (show (8 : Int) ≤ zu by omega), hv39, hc, ?_⟩)
    have hJ := hA.2.2
    have hk2 : 2 ≤ gcnt (V2.D.Run.idxBefore (grho top) zu) := by omega
    have hk10 : gcnt (V2.D.Run.idxBefore (grho top) zu) ≤ 10 := by omega
    generalize gcnt (V2.D.Run.idxBefore (grho top) zu) = k at hJ hk2 hk10
    cases J with
    | none =>
      cases top
      · rfl
      · exfalso
        interval_cases k <;> exact absurd hJ (by decide +kernel)
    | some B =>
      cases top
      · exfalso
        interval_cases k <;> exact absurd hJ.1 (by decide +kernel)
      · have hB' := hJ.2
        have hg : (treeStoreControlsView c5H ((gR true).core k).fg).J = .genesis := rfl
        rw [hg] at hB'
        rw [← hB']
        rfl
  · have hi := hIdx 41 zu (by omega)
    have h41 : gcnt (V2.D.Run.idxBefore (grho top) 41) = 11 := by cases top <;> decide
    have hm3 : m = 3 := by split_ifs at hA1 <;> omega
    exact Or.inr (Or.inr ⟨hm3, (show (41 : Int) ≤ zu by omega)⟩)

private theorem gpstate (top : Bool) (s : Nat) (h1 : 1 ≤ s) (h10 : s ≤ 10) :
    proposalStateAt c5env (grho top) gI s = some (if s = 1 then 0 else s) := by
  interval_cases s <;> cases top <;> decide +kernel

private theorem gservice_all (top : Bool) (s : Nat) (h1 : 1 ≤ s) (h10 : s ≤ 10) :
    FrontierProposalService (gR top) c5env (grho top) d5cTiming s (c5erase (gX s)) := by
  intro _ x _ _
  cases x
  interval_cases s <;> cases top <;> decide +kernel

private theorem gservice {top : Bool} {s : Slot} {B : Block}
    (h : HonestProposal c5env (grho top) gI s B) :
    FrontierProposalService (gR top) c5env (grho top) d5cTiming s B := by
  obtain ⟨h1, h10, rfl⟩ := gprop h
  exact gservice_all top s h1 h10

/-- At the actions 2, 3, 4 the source is x_{2r}, stored, and an honest row of the same
action names its entry. -/
private theorem gcovered (top : Bool) (r : Nat) (h2 : 2 ≤ r) (h4 : r ≤ 4) :
    ∃ nd j a, postClock c5env (grho top) () (d5cTiming.action r) = some nd ∧
      gX (2 * r) ∈ ((gR top).core nd).fg.TF ∧
      HonestRowAt gS c5env (grho top) d5cTiming j () r a ∧
      namedEntry (Row.height_pair a) =
        some ((c5H (gX (2 * r))).h, (c5H (gX (2 * r))).T_h.root) := by
  interval_cases r
  · exact ⟨6, 28, gRow2, by cases top <;> decide +kernel, by cases top <;> decide +kernel,
      ⟨Finset.mem_singleton_self _, by cases top <;> decide +kernel,
        by cases top <;> decide +kernel⟩, by decide +kernel⟩
  · exact ⟨8, 38, gRow3, by cases top <;> decide +kernel, by cases top <;> decide +kernel,
      ⟨Finset.mem_singleton_self _, by cases top <;> decide +kernel,
        by cases top <;> decide +kernel⟩, by decide +kernel⟩
  · exact ⟨10, 48, gRow3, by cases top <;> decide +kernel, by cases top <;> decide +kernel,
      ⟨Finset.mem_singleton_self _, by cases top <;> decide +kernel,
        by cases top <;> decide +kernel⟩, by decide +kernel⟩

private theorem gopening (top : Bool) (r q : Nat) (h2 : 2 ≤ r) (h4 : r ≤ 4) (hq : q ≤ 2 * r) :
    OpeningCovered (gR top) gS c5env (grho top) c5H d5cTiming Row.height_pair r
      (c5erase (gX q)) := by
  intro x _
  cases x
  obtain ⟨nd, j, a, hnd, hmem, hrow, hent⟩ := gcovered top r h2 h4
  exact ⟨gX (2 * r), nd, j, r, a, hnd, gsrcAt top r h4, hmem, c5erase_mono (gchain_le hq),
    le_rfl, hrow, hent⟩

/-- Proposal reads: the payload carries the labelled FG block; the parent is looked up in
the store; the parent fold is the window derive (`m9fold`). -/
private def gdecode (o : gP.Object) : Option (Slot × FGBlock (Fin 1)) :=
  match o.payload with
  | .inr B => some (B.slot, B)
  | .inl _ => none
private def gparentFG (top : Bool) (nd : Nat) (B : Block) : Option (FGBlock (Fin 1)) :=
  (FGBlock.genesis :: (gDel top).take nd).find? (fun A => decide (c5erase A = B))

private theorem gparent_read (top : Bool) (s : Nat) (h1 : 1 ≤ s) (h10 : s ≤ 10) :
    gparentFG top (if s = 1 then 0 else s) (c5erase (gX s)).parent = some (gX s).parent := by
  interval_cases s <;> cases top <;> decide

private theorem gread (top : Bool) : PromotionProposalRead (gR top) gS c5env (grho top) (gO top)
    gI gdecode c5erase FGBlock.rows (gparentFG top) m9parentHeight m9validFor m9fold := by
  intro s X hQ _
  obtain ⟨h1, h10, rfl⟩ := gprop_eq hQ
  refine ⟨⟨(gX s).rows, ⟨hQ, ?_⟩, List.filterMap_some.symm⟩, ?_⟩
  · obtain ⟨_, ⟨auth, payload⟩, hem, hb⟩ := hQ
    cases payload with
    | inl _ => cases hb
    | inr B =>
      have hB : B = gX s := c5erase_inj (Option.some.inj hb)
      subst hB
      refine ⟨⟨auth, .inr (gX s)⟩, hem, gX s, ?_, rfl, rfl⟩
      change some ((gX s).slot, gX s) = some (s, gX s)
      rw [gX_slot]
  · exact ⟨_, gpstate top s h1 h10, gparent_read top s h1 h10, rfl, rfl, rfl, fun _ => rfl⟩

/-- Rows inside chain blocks: x_6 names (1, genesis), x_8 names (2, x_6). -/
private def gNamed (row : Row (Fin 1)) (e : BlockId) : Bool :=
  match row.height_pair with
  | .vote _ e' _ => decide (e' = e)
  | .empty => false

private theorem gorder_key : ∀ j j', j ≤ 9 → j' ≤ 9 → ∀ row ∈ (gX j).rows,
    gNamed row (gX j').root = true → FGBlock.Preceq (gX j') (gX j).parent := by
  intro j j' hj hj'
  interval_cases j <;> interval_cases j' <;> decide

private theorem gorder (top : Bool) : PromotionRowOrder (gR top) c5env (grho top) (gO top) gI := by
  intro s X height U hQ _ _ hU i W hW hrow
  obtain ⟨h1, h10, rfl⟩ := gprop_eq hQ
  rcases s with _ | s'
  · exact absurd h1 (by decide)
  have hs9 : s' + 1 ≤ 10 := h10
  rw [gX_parent] at hU hW
  obtain ⟨j, hj, rfl⟩ := gchain_anc hW
  obtain ⟨j', hj', rfl⟩ := gchain_anc hU
  obtain ⟨row, hr, _, t, hp⟩ := hrow
  apply gorder_key j j' (by omega) (by omega) row hr
  unfold gNamed
  rw [hp]
  exact decide_eq_true rfl

private theorem gsigner (top : Bool) : PromotionRowSigner gS c5env (grho top) d5cTiming gWD := by
  refine ⟨fun _ _ _ a _ => ⟨a, rfl⟩, fun i j r a h => ?_⟩
  rw [Subsingleton.elim i 0]
  rcases grows h with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> rfl

private theorem gsourceParent (top : Bool) :
    PromotionSourceParent (gR top) c5env (grho top) (gO top) d5cTiming gI 4 := by
  intro u m J c r s X x K _ _ _ _ hrs hQ _ hK
  obtain ⟨_, rfl⟩ := gsrc hK
  obtain ⟨h1, _, rfl⟩ := gprop_eq hQ
  have h : @LE.le ℕ _ (r * 2 + 2) s := hrs
  obtain ⟨k', rfl⟩ : ∃ k', s = k' + 1 :=
    ⟨s - 1, (Nat.sub_add_cancel (show @LE.le ℕ _ 1 s by omega)).symm⟩
  rw [gX_parent]
  exact gchain_le (by omega)

private theorem growsReceipt (top : Bool) :
    TRowsReceipt (gR top) gS c5env (grho top) d5cTiming (fun _ => []) 1 := by
  intro j y r a h _ x _
  refine Or.inl ?_
  rcases grows h with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> simp

/-- Progress coverage: the only batches are the action-2 row over x_5 (carried by x_6) and
the action-3/4 rows over x_7, x_8, x_9 (carried by x_8, then kept as parent bits). -/
private theorem gcoverage (top : Bool) : ∀ (r height : Nat) (U X : FGBlock (Fin 1)),
    BatchPrem (gR top) gS (gO top) d5cTiming c5env (grho top) gI gWD c5E gdecode c5erase
      FGBlock.rows (fun _ => []) (gparentFG top) m9parentHeight m9validFor 1 .progress
      r height U X →
    (c5H X.parent).h = height → ProgressCoveredByChild c5E c5H X U height := by
  intro r height U X hB _
  obtain ⟨rows, hcar, _⟩ := hB.carrier
  obtain ⟨h1, h10, hX⟩ := gprop_eq hcar.1
  have hafter : r * 2 + 2 ≤ X.slot := hB.after
  obtain ⟨Q, _, hq, hall⟩ := hB.valid
  rcases Finset.eq_empty_or_nonempty Q with he | ⟨i, hi⟩
  · rw [he] at hq
    exact absurd hq (by decide)
  obtain ⟨j, r', a, t, hr', hrow, _, hNE, _, _, _, ⟨nd, H, hnd, hpar, hent⟩⟩ := hall i hi
  rw [hX] at hpar
  rw [hX]
  generalize X.slot = k at h1 h10 hafter hnd hpar hent
  have h1' : @LE.le ℕ _ 1 k := h1
  have h10' : @LE.le ℕ _ k 10 := h10
  have hafter' : @LE.le ℕ _ (r * 2 + 2) k := hafter
  rw [gpstate top k h1' h10'] at hnd
  cases Option.some.inj hnd
  rw [gparent_read top k h1' h10'] at hpar
  cases Option.some.inj hpar
  obtain ⟨tmo, hNE⟩ := hNE
  change a.height_pair = .vote height U.root tmo at hNE
  have hE : namedEntry a.height_pair =
      some ((c5H (gX k).parent).h, (c5H (gX k).parent).T_h.root) := hent
  rcases grows hrow with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
  · exfalso
    interval_cases k <;> exact absurd hE (by decide +kernel)
  · have hs6 : @LE.le ℕ _ 6 k := by omega
    interval_cases k
    · refine ⟨{0}, by decide, fun i hi => ?_⟩
      rw [Finset.mem_singleton.mp hi]
      exact Or.inr ⟨gRow2, by decide, rfl, tmo, hNE⟩
    all_goals exact absurd hE (by decide +kernel)
  all_goals
    have hs8 : @LE.le ℕ _ 8 k := by omega
    interval_cases k
    · refine ⟨{0}, by decide, fun i hi => ?_⟩
      rw [Finset.mem_singleton.mp hi]
      exact Or.inr ⟨gRow3, by decide, rfl, tmo, hNE⟩
    all_goals
      refine ⟨{0}, by decide, fun i hi => ?_⟩
      rw [Finset.mem_singleton.mp hi]
      exact Or.inl (by decide +kernel)

private theorem c5H_pos (B : FGBlock (Fin 1)) : 1 ≤ (c5H B).h := by
  have laws := heightLaws_of_bridge c5E c5cfg _
    (KitFG.Window.windowHeightBridge c5E c5cfg 2 (by decide))
  have h := laws.h_mono (genesis_preceq B)
  have h0 : (c5H .genesis).h = 1 := by decide
  change (c5H .genesis).h ≤ (c5H B).h at h
  rw [h0] at h
  exact h

private theorem gfloor (top : Bool) :
    AttemptProposalFloor (gR top) c5env (grho top) (gO top) d5cTiming gI 4 := by
  intro u v m J c q Q Qfg hJu hp huq hqv hQ he
  obtain ⟨h1, h10, rfl⟩ := gprop hQ
  have hu : (4 : Time) ≤ u := hJu
  rcases gphase hp hu with ⟨_, hv6⟩ | ⟨rfl, _, _, rfl, _⟩ | ⟨_, h41⟩
  · exfalso
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k = q := ⟨_, rfl⟩
    subst hk
    have h1' : 1 ≤ k := h1
    have h : 4 * ((k : Nat) : Int) + 6 ≤ v := hqv
    have h6 : v ≤ 6 := hv6
    obtain ⟨z, hz⟩ : ∃ z : Int, z = v := ⟨_, rfl⟩
    subst hz
    have h6' : z ≤ 6 := h6
    omega
  · exact c5H_pos _
  · exfalso
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k = q := ⟨_, rfl⟩
    subst hk
    have h10' : k ≤ 10 := h10
    obtain ⟨z, hz⟩ : ∃ z : Int, z = u := ⟨_, rfl⟩
    subst hz
    have hz1 : (41 : Int) ≤ z := h41
    have hz2 : z ≤ 4 * ((k : Nat) : Int) := huq
    omega

private theorem gcopy_at (top : Bool) (q : Nat) (h1 : 1 ≤ q) (h9 : q ≤ 9) :
    gX q ∈ gTF top (gcnt (timeIdx (grho top) (4 * (q : Int) + 6))) := by
  interval_cases q <;> cases top <;> decide

private theorem ggateCopy (top : Bool) : ∀ u v m J c q Q, (4 : Time) ≤ u →
    PhaseInterval (gR top) c5env (grho top) (gO top) u v m J c →
    FrontierSeedQualification d5cTiming 1 c5env.t_GST u q → d5cTiming.gate q ≤ v →
    HonestProposal c5env (grho top) gI q Q → ∃ i x Qfg,
      V2.D.Run.idxBefore (grho top) u ≤ i ∧ i ≤ timeIdx (grho top) v ∧ x ∈ (grho top).honest ∧
      Qfg ∈ ((gR top).core ((grho top).stateBefore c5env i x)).fg.TF ∧ c5erase Qfg = Q := by
  intro u v m J c q Q _ hp _ hqv hQ
  obtain ⟨h1, h10, rfl⟩ := gprop hQ
  refine ⟨timeIdx (grho top) v, (), gX q,
    (gidxBefore_le_timeIdx _ u).trans (frontierSearch_timeIdx_mono _ hp.1), le_rfl,
    Finset.mem_singleton_self _, ?_, rfl⟩
  change gX q ∈ gTF top ((grho top).stateBefore c5env _ ())
  rw [gstate]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = q := ⟨_, rfl⟩
  subst hk
  have hv42 : v ≤ 42 := hp.2.1
  obtain ⟨z, hz⟩ : ∃ z : Int, z = v := ⟨_, rfl⟩
  subst hz
  have hzq : 4 * ((k : Nat) : Int) + 6 ≤ z := hqv
  have hz42 : z ≤ 42 := hv42
  have hk9 : k ≤ 9 := by omega
  exact gTF_mono top (gcnt_mono (frontierSearch_timeIdx_mono _ hzq)) (gcopy_at top k h1 hk9)

private theorem gslotsOK (n : Nat) : m9slotsOK (gX n) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (decide ((gX n).slot ≤ n + 1) && m9slotsOK (gX n)) = true
    rw [gX_slot, ih]
    simp

private theorem gtip_ge {k q : Nat} (hq : q + 1 ≤ k) (hq10 : q ≤ 10) (hk2 : 2 ≤ k) :
    FGBlock.Preceq (gX q) (gTip k) := by
  unfold gTip
  simp only [show ¬ k ≤ 1 by omega, ↓reduceIte]
  exact gchain_le (Nat.le_min.mpr ⟨by omega, hq10⟩)

private theorem gceil (q : Nat) : q ≤ (q + 1) / 2 * 2 := by omega

private theorem gtiming (q r : Nat) (h : r ≤ (q + 1) / 2) :
    d5cTiming.action r - d5cTiming.gate q ≤ FGCompose.P d5cTiming - 4 * d5cTiming.delta := by
  change (8 * ((r : Nat) : Int) + 6) - (4 * ((q : Nat) : Int) + 6) ≤
    4 * ((2 : Nat) : Int) * 1 - 4 * 1
  omega

private theorem gqual (u : Int) (q : Nat) (hu : 8 ≤ u)
    (h : FrontierSeedQualification d5cTiming 1 c5env.t_GST u q) : 4 ≤ q := by
  rcases h with ⟨β, hβ, _, hlt⟩ | ⟨b, hb, _, _, _, hlt⟩
  · have h1 : u < 4 * ((β : Nat) : Int) := hβ
    have h2 : 4 * (((β + 2 * 1 - 1 : Nat) : Nat) : Int) < 4 * ((q : Nat) : Int) := hlt
    omega
  · have h1 : u ≤ 4 * ((b : Nat) : Int) + 1 := hb
    have h2 : 4 * (((b + 1 : Nat) : Nat) : Int) < 4 * ((q : Nat) : Int) := hlt
    omega

/-- Continuing local service: every height-2 seed (slots 6, 7, 8) through every capped
endpoint v ≤ 39. -/
private theorem gservice_local (top : Bool) : ∀ u v m J c q Q Qfg, (4 : Time) ≤ u →
    HonestProposal c5env (grho top) gI q Q → c5erase Qfg = Q → (c5H Qfg).h = m →
    FrontierProposalService (gR top) c5env (grho top) d5cTiming q Q →
    FrontierSeedQualification d5cTiming 1 c5env.t_GST u q → u ≤ d5cTiming.proposal q →
    PhaseInterval (gR top) c5env (grho top) (gO top) u (d5cTiming.gate q) m J c →
    d5cTiming.gate q ≤ v → v ≤ (grho top).horizon →
    (∀ i x, timeIdx (grho top) u ≤ i → i ≤ timeIdx (grho top) v → x ∈ (grho top).honest →
      ((gR top).core ((grho top).stateBefore c5env i x)).fg.h_max ≤ m) →
    FrontierLocalService (gR top) gS c5env (grho top) (gO top) d5cTiming gI gWD.heightPair
      q Q Qfg m v := by
  intro u v m J c q Q Qfg hu hQ he hm _ _ huq hp hqv _ hcap
  obtain ⟨h1, h10, rfl⟩ := gprop hQ
  have hQfg : Qfg = gX q := c5erase_inj he
  subst hQfg
  have h1' : @LE.le ℕ _ 1 q := h1
  have h10' : @LE.le ℕ _ q 10 := h10
  have huq' : @LE.le Int _ u (4 * ((q : Nat) : Int)) := huq
  have hqv' : 4 * ((q : Nat) : Int) + 6 ≤ v := hqv
  rcases gphase hp hu with ⟨_, hv6⟩ | ⟨rfl, _, _, _, _⟩ | ⟨_, h41⟩
  · exfalso
    have : 4 * ((q : Nat) : Int) + 6 ≤ 6 := hv6
    omega
  swap
  · exfalso
    have : (41 : Int) ≤ u := h41
    omega
  have hq6 : @LE.le ℕ _ 6 q := by
    by_contra hlt
    interval_cases q <;> exact absurd hm (by decide +kernel)
  have hv39 : @LE.le Int _ v 39 := by
    by_contra hv
    have hu40 : @LE.le Int _ u 40 := by omega
    have hv40 : @LE.le Int _ 40 v := by omega
    have hk := hcap (timeIdx (grho top) 40) () (frontierSearch_timeIdx_mono _ hu40)
      (frontierSearch_timeIdx_mono _ hv40) (Finset.mem_singleton_self _)
    rw [gstate, show gcnt (timeIdx (grho top) 40) = 11 by cases top <;> decide] at hk
    cases top <;> exact absurd hk (by decide)
  have hq8 : @LE.le ℕ _ q 8 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x s H _ hs _ hH
    unfold headAtLabel at hH
    obtain ⟨nd, _, hHe⟩ := Option.map_eq_some_iff.mp hH
    rw [← hHe]
    have hs' : @LE.le ℕ _ (q + 1) s := hs
    exact c5erase_mono (gchain_le (by omega))
  · intro s B hs _ hB
    obtain ⟨hs1, _, rfl⟩ := gprop hB
    have hs' : @LE.le ℕ _ (q + 2) s := hs
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 :=
      ⟨s - 1, (Nat.sub_add_cancel (show @LE.le ℕ _ 1 s by omega)).symm⟩
    exact c5erase_mono (gchain_le (by omega))
  · intro i x _ hgv hi _
    cases x
    change Block.Preceq (c5erase (gX q)) (c5erase (gTip ((grho top).stateBefore c5env i ())))
    rw [gstate]
    have hgv' : 4 * ((q : Nat) : Int) + 6 + 4 * 1 ≤ v := hgv
    have hle := gcnt_le i
    have hk := gcnt_mono hi
    interval_cases q
    · rw [show gcnt (afterTicksIdx (grho top) (d5cTiming.gate 6 + 4 * d5cTiming.delta)) = 9 by
        cases top <;> decide] at hk
      exact c5erase_mono (gtip_ge (by omega) (by omega) (by omega))
    · rw [show gcnt (afterTicksIdx (grho top) (d5cTiming.gate 7 + 4 * d5cTiming.delta)) = 10 by
        cases top <;> decide] at hk
      exact c5erase_mono (gtip_ge (by omega) (by omega) (by omega))
    · exfalso
      omega
  · intro s B _ _ hB
    exact gservice hB
  · intro r hqr hrv
    have hqr' : @LE.le ℕ _ q (r * 2) := hqr
    have hrv' : 8 * ((r : Nat) : Int) + 6 ≤ v := hrv
    have hr4 : @LE.le ℕ _ r 4 := by omega
    have hr3 : @LE.le ℕ _ 3 r := by omega
    refine ⟨gopening top r q (by omega) hr4 (by omega), ⟨⟨26⟩, ?_⟩, ?_, ?_⟩
    · intro x K _ hK
      obtain ⟨_, rfl⟩ := gsrc hK
      cases top <;> interval_cases r <;> decide +kernel
    · intro x K _ hK
      obtain ⟨_, rfl⟩ := gsrc hK
      cases top <;> interval_cases r <;> interval_cases q <;> decide +kernel
    · intro hfirst
      exact gtiming q r (hfirst ((q + 1) / 2) (gceil q))

private theorem gcommon (top : Bool) : ∀ u m J c q Q Qfg r, (4 : Time) ≤ u →
    HonestProposal c5env (grho top) gI q Q → c5erase Qfg = Q →
    FrontierProposalService (gR top) c5env (grho top) d5cTiming q Q →
    FrontierSeedQualification d5cTiming 1 c5env.t_GST u q → u ≤ d5cTiming.proposal q →
    q ≤ r * d5cTiming.roundSlots → (∀ r', q ≤ r' * d5cTiming.roundSlots → r ≤ r') →
    PhaseInterval (gR top) c5env (grho top) (gO top) u (d5cTiming.action r) m J c →
    OpeningCovered (gR top) gS c5env (grho top) c5H d5cTiming gWD.heightPair r Q ∧
      ((c5H Qfg).h = m - 1 → OpeningEntry (gR top) c5env (grho top) c5H d5cTiming r (m - 1) ∨
        ∃ x K, x ∈ (grho top).honest ∧
          actionSourceFG (gR top) c5env (grho top) d5cTiming x r = some (some K) ∧
          (c5H K).h = m) := by
  intro u m J c q Q Qfg r hu hQ he _ hqual huq hqr hfirst hp
  obtain ⟨h1, h10, rfl⟩ := gprop hQ
  have hQfg : Qfg = gX q := c5erase_inj he
  subst hQfg
  have h1' : @LE.le ℕ _ 1 q := h1
  have hqr' : @LE.le ℕ _ q (r * 2) := hqr
  have huq' : @LE.le Int _ u (4 * ((q : Nat) : Int)) := huq
  rcases gphase hp hu with ⟨_, hv6⟩ | ⟨rfl, h8u, hv39, _, _⟩ | ⟨_, h41⟩
  · exfalso
    have : 8 * ((r : Nat) : Int) + 6 ≤ 6 := hv6
    omega
  swap
  · exfalso
    have : (41 : Int) ≤ u := h41
    have h10' : @LE.le ℕ _ q 10 := h10
    omega
  have h8u' : (8 : Int) ≤ u := h8u
  have hq4 := gqual u q h8u' hqual
  have hr4 : @LE.le ℕ _ r 4 := by
    have : 8 * ((r : Nat) : Int) + 6 ≤ 39 := hv39
    omega
  refine ⟨gopening top r q (show @LE.le ℕ _ 2 r by omega) hr4
    (show @LE.le ℕ _ q (2 * r) by omega), fun hh => ?_⟩
  have hq5 : @LE.le ℕ _ q 5 := by
    by_contra hlt
    have h10' : @LE.le ℕ _ q 10 := h10
    interval_cases q <;> exact absurd hh (by decide +kernel)
  interval_cases q
  · have hr : @LE.le ℕ _ r 2 := hfirst 2 (by decide)
    have hr2 : @Eq ℕ r 2 := by omega
    subst hr2
    refine Or.inl ⟨genesisRoot, fun x K _ hK => ?_⟩
    obtain ⟨_, rfl⟩ := gsrc hK
    decide +kernel
  · have hr : @LE.le ℕ _ r 3 := hfirst 3 (by decide)
    have hr3 : @Eq ℕ r 3 := by omega
    subst hr3
    exact Or.inr ⟨(), gX 6, Finset.mem_singleton_self _, gsrcAt top 3 (by decide),
      by decide +kernel⟩

/-- The repair allowance from u = 8 (ρ = 14) and from u = 10 (ρ = 16): one-arm start with
b = 2 (resp. 3), and the served proposal of slot 4 (resp. 5) by u + ρ. -/
private theorem gallow8 (top : Bool) :
    FrontierRepairAllowance (gR top) c5env (grho top) (gO top) d5cTiming gI 4 1 4 14 8 := by
  refine ⟨by decide, 2 + 1, .one 2 (by decide) (fun i hi => ?_) (by decide) (by decide),
    fun _ v m J c _ _ => ⟨fun s Q _ _ hQ => gservice hQ, fun _ =>
      ⟨4, c5erase (gX 4), by decide, by decide, gpropOf top 4 (by decide) (by decide),
        gservice_all top 4 (by decide) (by decide)⟩⟩⟩
  have : (8 : Int) ≤ 4 * ((i : Nat) : Int) + 1 := hi
  change @LE.le ℕ _ 2 i
  omega

private theorem gallow10 (top : Bool) :
    FrontierRepairAllowance (gR top) c5env (grho top) (gO top) d5cTiming gI 4 1 4 16 10 := by
  refine ⟨by decide, 3 + 1, .one 3 (by decide) (fun i hi => ?_) (by decide) (by decide),
    fun _ v m J c _ _ => ⟨fun s Q _ _ hQ => gservice hQ, fun _ =>
      ⟨5, c5erase (gX 5), by decide, by decide, gpropOf top 5 (by decide) (by decide),
        gservice_all top 5 (by decide) (by decide)⟩⟩⟩
  have : (10 : Int) ≤ 4 * ((i : Nat) : Int) + 1 := hi
  change @LE.le ℕ _ 3 i
  omega

private theorem gfault (top : Bool) : c5E.weightOf (historyFaulty gS (grho top)) < c5E.q := by
  have h : historyFaulty gS (grho top) = ∅ := by
    unfold historyFaulty
    ext i
    simp
  rw [h]
  decide

private theorem ggap (top : Bool) : ∀ t, c5env.t_GST ≤ t → t + 4 ≤ (grho top).horizon →
    ∃ s, t < d5cTiming.proposal s ∧ d5cTiming.proposal s ≤ t + 4 ∧
      Gen.V2.Duty.HonestSlot (grho top) gI s := by
  intro t ht0 _
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

private theorem gslotProposal (top : Bool) :
    PromotionSlotProposal (gR top) c5env (grho top) d5cTiming gI := by
  intro s hs _ hh
  have h1 : @LE.le ℕ _ 1 s := hs.1
  have h42 : 4 * ((s : Nat) : Int) ≤ 42 := hh
  exact ⟨gX s, gpropOf top s h1 (by omega), gX_slot s⟩

private theorem gphaseGap : PhaseInterval (gR false) c5env (grho false) (gO false) 8 38 2 none
    false := by
  refine ⟨by decide, by decide, by decide, fun i x hi hi' _ => ?_⟩
  cases x
  have hlo := gcnt_mono hi
  have hhi := gcnt_mono hi'
  rw [show gcnt (V2.D.Run.idxBefore (grho false) 8) = 2 by decide] at hlo
  rw [show gcnt (timeIdx (grho false) 38) = 10 by decide] at hhi
  change (treeStoreControlsView c5H ((gR false).core ((grho false).stateBefore c5env i ())).fg).H
    = 2 ∧ _
  rw [gstate]
  generalize gcnt i = k at hlo hhi
  interval_cases k <;> decide +kernel

-- G0 (review 2): frontierSearch_gap_phase on model g (gap variant). Phase [8, 38] at
-- frontier 2 (no top, no contest), allowance ρ = 14 from u = 8, Dl = 8 + 14 + 16 = 38 ≤ 42.
-- Every premise is proved on the model; progress coverage, the opening rows, the HEAD
-- reads and the continuing service are exercised by actual blocks and rows.
private theorem ggapPhase : ∃ t, (8 : Time) ≤ t ∧ t ≤ 38 ∧
    StrongServed (gR false) gS c5env (grho false) (gO false) d5cTiming gI gWD.heightPair 4 1 2 t :=
  frontierSearch_gap_phase (R := gR false) (S := gS) (O := gO false) (T := d5cTiming)
    (E := c5env) (rho := grho false) (I := gI) (D := gWD) (Ef := c5E)
    (decodeProposal := gdecode) (bodyErase := c5erase) (bodyRows := FGBlock.rows)
    (blockWireRows := fun _ => []) (parentFG := gparentFG false)
    (parentHeight := m9parentHeight) (validFor := m9validFor) (fold := m9fold) (Jst := 4)
    (leaseSlots := 1) (obs := gobs false) (cert := c5cert) (inv := ginv false)
    (hT := d5cTimingLaws) (hk := le_rfl) (schedule := gschedule false)
    (faultWeight := gfault false) (G := 4) (ΔF := 1) (ρbar := 14) (u := 8) (Dl := 38)
    (deltaF := le_rfl) (hdelta := rfl) (gap := ggap false) (hJst := by decide)
    (hG := by decide) (slotProposal := gslotProposal false) (read := gread false)
    (order := gorder false) (signer := gsigner false) (sourceParent := gsourceParent false)
    (deltaT := 4) (hδ := rfl) (hbound := ⟨by decide⟩) (rowsReceipt := growsReceipt false)
    (progressCoverage := gcoverage false) (hfold := m9foldAdvance)
    (honestQuorum := ⟨{0}, fun _ _ => Finset.mem_singleton_self _, by decide⟩)
    (entryAgreement := by
      intro r x y K L _ _ hK hL _
      rw [(gsrc hK).2, (gsrc hL).2])
    (sourceSlot := by
      intro r x K _ hK
      rw [(gsrc hK).2, gX_slot, Nat.mul_comm]
      exact le_rfl)
    (ancestorSlot := by
      intro r x K A _ hK hA
      rw [(gsrc hK).2] at hA ⊢
      exact m9anc_slot (gslotsOK _) hA)
    (eraseInj := c5erase_inj) (eraseReflect := m9erase_reflect) (floor := gfloor false)
    (gateCopy := ggateCopy false) (service := gservice_local false)
    (common := gcommon false) (heldSlot := gheldSlot false)
    (proposalSlot := by
      intro q Q K hQ hK
      obtain ⟨_, _, hQ'⟩ := gprop hQ
      rw [c5erase_inj (hK.trans hQ'), gX_slot])
    (m := 2) (hready := by decide) (hp := gphaseGap) (allowance := gallow8 false)
    (hbudget := by decide)

/-- Every height-2 served seed has slot 6..9, so its gate is at least 30. -/
private theorem gservedLate (top : Bool) {t : Time}
    (h : StrongServed (gR top) gS c5env (grho top) (gO top) d5cTiming gI gWD.heightPair 4 1 2 t) :
    30 ≤ t := by
  obtain ⟨_, _, _, q, Q, Qfg, _, hQ, he, hm, _, _, _, _, hqt, _⟩ := h
  obtain ⟨h1, h10, rfl⟩ := gprop hQ
  have hQfg : Qfg = gX q := c5erase_inj he
  subst hQfg
  have h1' : @LE.le ℕ _ 1 q := h1
  have h10' : @LE.le ℕ _ q 10 := h10
  have hq6 : @LE.le ℕ _ 6 q := by
    by_contra hlt
    interval_cases q <;> cases top <;> exact absurd hm (by decide +kernel)
  have : 4 * ((q : Nat) : Int) + 6 ≤ t := hqt
  obtain ⟨z, hz⟩ : ∃ z : Int, z = t := ⟨t, rfl⟩
  subst hz
  have h' : 4 * ((q : Nat) : Int) + 6 ≤ z := this
  change (30 : Int) ≤ z
  omega

-- Inspection and bad trace: the selected served seed time lies in [30, 38] (a height-2 seed
-- of slot 6, 7 or 8 at or after its gate); no served seed exists by 29.
private theorem ggapExit :
    (∃ t, (30 : Time) ≤ t ∧ t ≤ 38 ∧ StrongServed (gR false) gS c5env (grho false) (gO false)
      d5cTiming gI gWD.heightPair 4 1 2 t) ∧
    ¬ ∃ t, t ≤ (29 : Time) ∧ StrongServed (gR false) gS c5env (grho false) (gO false)
      d5cTiming gI gWD.heightPair 4 1 2 t := by
  refine ⟨?_, ?_⟩
  · obtain ⟨t, _, ht, hs⟩ := ggapPhase
    exact ⟨t, gservedLate false hs, ht, hs⟩
  · rintro ⟨t, ht, hs⟩
    have := gservedLate false hs
    obtain ⟨z, hz⟩ : ∃ z : Int, z = t := ⟨t, rfl⟩
    subst hz
    have h1 : (30 : Int) ≤ z := this
    have h2 : z ≤ 29 := ht
    omega

private abbrev greceipt (top : Bool) (B : Block) (d : Time) (y : Unit) : Prop :=
  ∃ W, c5erase W = B ∧ W ∈ ((gR top).core ((grho top).stateBeforeTime c5env d y)).fg.TF

private theorem gscope (top : Bool) (W : FGBlock (Fin 1)) (d : Time)
    (hW : W ∈ ((gR top).core ((grho top).stateBeforeTime c5env d ())).fg.TF) :
    WitnessReceiptScope (gR top) c5env (grho top) (fun _ => true) (greceipt top) W d :=
  ⟨fun _ y _ _ _ _ _ _ => by cases y; exact ⟨W, rfl, hW⟩⟩

/-- Frontier and top witnesses of a store count. -/
private abbrev gWit (top : Bool) (k : Nat) : FGBlock (Fin 1) :=
  if k ≤ 1 then .genesis else if k ≤ 10 then gB top else gX 10
private abbrev gTopWit (top : Bool) (k : Nat) : FGBlock (Fin 1) :=
  if top && decide (2 ≤ k) then c5x1 else .genesis

private def gscopeB (top : Bool) (i : Nat) : Bool :=
  match (grho top).events[i]? with
  | some ev => decide (ev.time + 1 ≤ 42 →
      gWit top (gcnt (i + 1)) ∈
        ((gR top).core ((grho top).stateBeforeTime c5env (ev.time + 1) ())).fg.TF ∧
      gTopWit top (gcnt (i + 1)) ∈
        ((gR top).core ((grho top).stateBeforeTime c5env (ev.time + 1) ())).fg.TF)
  | none => true

private theorem gscopeTable (top : Bool) : ∀ i < 54, gscopeB top i = true := by
  cases top <;> decide +kernel

private theorem gwit_facts (top : Bool) (k : Nat) (hk : k ≤ 11) :
    gWit top k ∈ gTF top k ∧ (c5H (gWit top k)).h = gHmax k ∧
    (gHj top k + 1 = gHmax k → gTopWit top k ∈ gTF top k ∧
      (c5H (gTopWit top k)).h = gHmax k ∧ (c5H (gTopWit top k)).h_j + 1 = gHmax k ∧
      (c5H (gTopWit top k)).J = .genesis) := by
  cases top <;> interval_cases k <;> decide +kernel

private theorem gservices (top : Bool) : ∀ i (ev : V2.Event Unit gP.Object) m,
    (grho top).events[i]? = some ev → (4 : Time) ≤ ev.time → 1 ≤ m →
    frontierAtIdx (gR top) c5env (grho top) (i + 1) = m →
    ev.time + d5cTiming.delta ≤ (grho top).horizon →
    PhaseWitnessReceiptScope (gR top) c5env (grho top) (gO top) (fun _ => true) (greceipt top)
      (i + 1) m (ev.time + d5cTiming.delta) := by
  intro i ev m hi _ _ hf hh
  have hl : i < 54 := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    cases top <;> simpa using this
  have tab := gscopeTable top i hl
  unfold gscopeB at tab
  rw [hi] at tab
  obtain ⟨hW, hC⟩ := of_decide_eq_true tab hh
  rw [gfront] at hf
  subst hf
  obtain ⟨hWm, hWh, htop⟩ := gwit_facts top (gcnt (i + 1)) (gcnt_le _)
  refine ⟨⟨(), gWit top (gcnt (i + 1)), ⟨Finset.mem_singleton_self _, ?_⟩, hWh,
    gscope top _ _ hW⟩, fun ht => ?_, fun hc => ?_⟩
  · change _ ∈ gTF top ((grho top).stateBefore c5env (i + 1) ())
    rw [gstate]
    exact hWm
  · obtain ⟨x, _, hx⟩ := ht
    cases x
    change gHj top ((grho top).stateBefore c5env (i + 1) ()) + 1 = _ at hx
    rw [gstate] at hx
    obtain ⟨hCm, hCh, hCj, hCJ⟩ := htop hx
    refine ⟨(), gTopWit top (gcnt (i + 1)), ⟨Finset.mem_singleton_self _, ?_⟩, hCh, hCj, ?_,
      gscope top _ _ hC⟩
    · change _ ∈ gTF top ((grho top).stateBefore c5env (i + 1) ())
      rw [gstate]
      exact hCm
    · rw [hCJ]
  · exfalso
    obtain ⟨x, _, _, hc⟩ := hc
    cases x
    change (treeStoreControlsView c5H ((gR top).core
      ((grho top).stateBefore c5env (i + 1) ())).fg).contest = true at hc
    rw [gstate, gcontest] at hc
    cases hc

private theorem gTopIff (top : Bool) (k m : Nat) :
    TopEvidence (gR top) c5env (grho top) k m ↔ gHj top (gcnt k) + 1 = m := by
  constructor
  · rintro ⟨x, _, h⟩
    cases x
    change gHj top ((grho top).stateBefore c5env k ()) + 1 = m at h
    rwa [gstate] at h
  · intro h
    refine ⟨(), Finset.mem_singleton_self _, ?_⟩
    change gHj top ((grho top).stateBefore c5env k ()) + 1 = m
    rwa [gstate]

private theorem gNoContest (top : Bool) (k m : Nat) :
    ¬ ContestEvidence (gR top) c5env (grho top) (gO top) k m := by
  rintro ⟨x, _, _, hc⟩
  cases x
  change (treeStoreControlsView c5H ((gR top).core
    ((grho top).stateBefore c5env k ())).fg).contest = true at hc
  rw [gstate, gcontest] at hc
  cases hc

private theorem gEffIff (top : Bool) (k : Nat) :
    EffectiveEvent (gR top) c5env (grho top) (gO top) k ↔
      gHmax (gcnt k) < gHmax (gcnt (k + 1)) ∨
      (¬ gHj top (gcnt k) + 1 = gHmax (gcnt (k + 1)) ∧
        gHj top (gcnt (k + 1)) + 1 = gHmax (gcnt (k + 1))) := by
  unfold EffectiveEvent
  rw [gfront, gfront]
  dsimp only
  constructor
  · rintro (h | ⟨h1, h2⟩ | ⟨_, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨fun h => h1 ((gTopIff top k _).mpr h), (gTopIff top (k + 1) _).mp h2⟩
    · exact absurd h2 (gNoContest top (k + 1) _)
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨fun h => h1 ((gTopIff top k _).mp h),
        (gTopIff top (k + 1) _).mpr h2⟩)

/-- The only effective event after the B* delivery (index 9) is the x_10 delivery at
index 51 (time 40). -/
private theorem gOnlyEff (top : Bool) (j : Nat) (hj : 9 < j)
    (h : EffectiveEvent (gR top) c5env (grho top) (gO top) j) : j = 51 := by
  rw [gEffIff] at h
  rcases Nat.lt_or_ge j 54 with hl | hl
  · cases top <;> interval_cases j <;> first | rfl | exact absurd h (by decide)
  · have h1 : gcnt j = 11 := le_antisymm (gcnt_le j) ((show gcnt 54 = 11 by decide) ▸
      gcnt_mono hl)
    have h2 : gcnt (j + 1) = 11 := le_antisymm (gcnt_le _) ((show gcnt 54 = 11 by decide) ▸
      gcnt_mono (by omega))
    rw [h1, h2] at h
    cases top <;> exact absurd h (by decide)

private theorem gstart (top : Bool) : FrontierSearchStart (gR top) c5env (grho top) (gO top)
    d5cTiming 4 9 (gdeliver (gB top) 7) 2 (if top then .topJ else .gap) := by
  refine ⟨by cases top <;> rfl, by cases top <;> decide, Or.inl (Or.inl ?_), ?_, by decide, ?_⟩
  · rw [gfront, gfront]
    decide
  · rw [gfront]
    decide
  · cases top
    · exact ⟨fun h => absurd ((gTopIff false 10 2).mp h) (by decide), gNoContest false 10 2⟩
    · exact ⟨(gTopIff true 10 2).mpr (by decide), gNoContest true 10 2⟩

private theorem gjustified : ∀ i x, x ∈ (grho true).honest →
    ((gR true).core ((grho true).stateBefore c5env i x)).fg.h_j ≠ 0 →
    ∃ j y r a K, j < i ∧ HonestRowAt gS c5env (grho true) d5cTiming j y r a ∧
      actionSourceFG (gR true) c5env (grho true) d5cTiming y r = some (some K) ∧
      (c5H K).T_h = ((gR true).core ((grho true).stateBefore c5env i x)).fg.J := by
  intro i x _ hj
  cases x
  change gHj true ((grho true).stateBefore c5env i ()) ≠ 0 at hj
  rw [gstate] at hj
  have hi : 10 ≤ i := by
    by_contra hlt
    have := gcnt_mono (show i ≤ 9 by omega)
    rw [show gcnt 9 = 1 by decide] at this
    simp only [gHj, Bool.true_and, decide_eq_true_eq] at hj
    split_ifs at hj with h2 <;> omega
  refine ⟨7, (), 0, gRow0, .genesis, by omega,
    ⟨Finset.mem_singleton_self _, by decide, by decide +kernel⟩, gsrcAt true 0 (by decide), ?_⟩
  rfl

private theorem gparentFrame : ∀ q Q, HonestProposal c5env (grho true) gI q Q → ∃ j,
    (grho true).events[j]? =
      some (.tick (V2.D.proposerOf (grho true) gI q) (d5cTiming.proposal q)) ∧
    ∀ Qfg, c5erase Qfg = Q → FGBlock.Preceq
      ((gO true).controls ((grho true).stateBefore c5env j
        (V2.D.proposerOf (grho true) gI q))).Z Qfg.parent := by
  intro q Q hQ
  obtain ⟨_, _, ⟨j, hj, _⟩, _⟩ := hQ
  refine ⟨j, ?_, fun Qfg _ => ?_⟩
  · rw [hj]
    congr 2
  · unfold Controls.Z
    split <;> exact genesis_preceq _

-- G0 (review 2): frontier_hg3_gap on model g (gap variant). Start: the B* delivery at index
-- 9, time 7 (frontier 1 -> 2, gap kind). Allowance from 7 + 3Δ = 10 with ρ = 16;
-- deadline 7 + E_gF = 7 + 16 + Γ + (2P - Δ) = 42 = horizon.
private theorem gHG3gap :
    FrontierHG3Result (gR false) gS c5env (grho false) (gO false) d5cTiming gI gWD.heightPair
      4 1 9 2 7 (7 + E_gF d5cTiming 1 4 16) :=
  frontier_hg3_gap (R := gR false) (S := gS) (O := gO false) (T := d5cTiming)
    (E := c5env) (rho := grho false) (I := gI) (D := gWD) (Ef := c5E)
    (decodeProposal := gdecode) (bodyErase := c5erase) (bodyRows := FGBlock.rows)
    (blockWireRows := fun _ => []) (parentFG := gparentFG false)
    (parentHeight := m9parentHeight) (validFor := m9validFor) (fold := m9fold) (Jst := 4)
    (leaseSlots := 1) (obs := gobs false) (cert := c5cert) (inv := ginv false)
    (justif := c5justif) (keep := gkeep false) (positive := by decide)
    (coreLaws := gcore false) (erasePreceq := fun h => c5erase_mono h)
    (joined := fun _ => true) (receipt := greceipt false)
    (hT := d5cTimingLaws) (hk := le_rfl) (crossing := gcrossing false)
    (schedule := gschedule false) (mono := gmono false)
    (awake := fun _ _ _ _ _ => rfl) (joinedTick := fun _ _ _ _ _ _ _ => rfl)
    (readyCut := c5ready) (hServices := gservices false)
    (receiptHeld := fun W d y _ h => by
      obtain ⟨W', he, hW'⟩ := h
      exact c5erase_inj he ▸ hW')
    (faultWeight := gfault false) (G := 4) (ΔF := 1) (ρbar := 16)
    (deltaF := le_rfl) (hdelta := rfl) (gap := ggap false) (hJst := by decide)
    (hG := by decide) (slotProposal := gslotProposal false) (read := gread false)
    (order := gorder false) (signer := gsigner false) (sourceParent := gsourceParent false)
    (deltaT := 4) (hδ := rfl) (hbound := ⟨by decide⟩) (rowsReceipt := growsReceipt false)
    (progressCoverage := gcoverage false) (hfold := m9foldAdvance)
    (honestQuorum := ⟨{0}, fun _ _ => Finset.mem_singleton_self _, by decide⟩)
    (entryAgreement := by
      intro r x y K L _ _ hK hL _
      rw [(gsrc hK).2, (gsrc hL).2])
    (sourceSlot := by
      intro r x K _ hK
      rw [(gsrc hK).2, gX_slot, Nat.mul_comm]
      exact le_rfl)
    (ancestorSlot := by
      intro r x K A _ hK hA
      rw [(gsrc hK).2] at hA ⊢
      exact m9anc_slot (gslotsOK _) hA)
    (eraseReflect := m9erase_reflect) (floor := gfloor false)
    (gateCopy := ggateCopy false) (service := gservice_local false)
    (common := gcommon false) (heldSlot := gheldSlot false)
    (proposalSlot := by
      intro q Q K hQ hK
      obtain ⟨_, _, hQ'⟩ := gprop hQ
      rw [c5erase_inj (hK.trans hQ'), gX_slot])
    (i := 9) (m := 2) (ev := gdeliver (gB false) 7) (hstart := gstart false)
    (allowance := gallow10 false) (hhor := by decide)

-- G0 (review 2): frontier_hg3_topJ on model g (top variant). Start: the delivery of the
-- justified block c5x1 at index 9, time 7 (frontier 1 -> 2, h_j = 1, top-J kind).
-- Deadline 7 + E_jF = 7 + max(ρ + P + Γ + 3Δ + ε, 2P + Γ - 4Δ) = 7 + 31 = 38 ≤ 42.
private theorem gHG3top :
    FrontierHG3Result (gR true) gS c5env (grho true) (gO true) d5cTiming gI gWD.heightPair
      4 1 9 2 7 (7 + E_jF d5cTiming 1 4 16) :=
  frontier_hg3_topJ (R := gR true) (S := gS) (O := gO true) (T := d5cTiming)
    (E := c5env) (rho := grho true) (I := gI) (D := gWD) (Ef := c5E)
    (decodeProposal := gdecode) (bodyErase := c5erase) (bodyRows := FGBlock.rows)
    (blockWireRows := fun _ => []) (parentFG := gparentFG true)
    (parentHeight := m9parentHeight) (validFor := m9validFor) (fold := m9fold) (Jst := 4)
    (leaseSlots := 1) (obs := gobs true) (cert := c5cert) (inv := ginv true)
    (justif := c5justif) (keep := gkeep true) (positive := by decide)
    (coreLaws := gcore true) (erasePreceq := fun h => c5erase_mono h)
    (joined := fun _ => true) (receipt := greceipt true)
    (hT := d5cTimingLaws) (hk := le_rfl) (crossing := gcrossing true)
    (schedule := gschedule true) (mono := gmono true)
    (awake := fun _ _ _ _ _ => rfl) (joinedTick := fun _ _ _ _ _ _ _ => rfl)
    (readyCut := c5ready) (hServices := gservices true)
    (receiptHeld := fun W d y _ h => by
      obtain ⟨W', he, hW'⟩ := h
      exact c5erase_inj he ▸ hW')
    (faultWeight := gfault true) (G := 4) (ΔF := 1) (ρbar := 16)
    (deltaF := le_rfl) (hdelta := rfl) (gap := ggap true) (hJst := by decide)
    (hG := by decide) (slotProposal := gslotProposal true) (read := gread true)
    (order := gorder true) (signer := gsigner true) (sourceParent := gsourceParent true)
    (deltaT := 4) (hδ := rfl) (hbound := ⟨by decide⟩) (rowsReceipt := growsReceipt true)
    (progressCoverage := gcoverage true) (hfold := m9foldAdvance)
    (honestQuorum := ⟨{0}, fun _ _ => Finset.mem_singleton_self _, by decide⟩)
    (entryAgreement := by
      intro r x y K L _ _ hK hL _
      rw [(gsrc hK).2, (gsrc hL).2])
    (sourceSlot := by
      intro r x K _ hK
      rw [(gsrc hK).2, gX_slot, Nat.mul_comm]
      exact le_rfl)
    (ancestorSlot := by
      intro r x K A _ hK hA
      rw [(gsrc hK).2] at hA ⊢
      exact m9anc_slot (gslotsOK _) hA)
    (eraseReflect := m9erase_reflect) (floor := gfloor true)
    (gateCopy := ggateCopy true) (service := gservice_local true)
    (common := gcommon true) (justifiedSource := gjustified) (parentFrame := gparentFrame)
    (i := 9) (m := 2) (ev := gdeliver (gB true) 7) (hstart := gstart true)
    (allowance := gallow10 true) (hhor := by decide)

private theorem gev51 (top : Bool) : (grho top).events[51]? = some (gdeliver (gX 10) 40) := by
  cases top <;> rfl

/-- No first stop (phase or rise) of the phase after index 9 by any deadline before 40. -/
private theorem gnoStop (top : Bool) {D : Time} (hD : D < 40) :
    ¬ FirstPhaseStopBy (gR top) c5env (grho top) (gO top) 9 2 D ∧
    ¬ FirstRiseStopBy (gR top) c5env (grho top) (gO top) 9 2 D := by
  have key : ∀ j (ev : V2.Event Unit gP.Object), 9 < j → (grho top).events[j]? = some ev →
      ev.time ≤ D → EffectiveEvent (gR top) c5env (grho top) (gO top) j → False := by
    intro j ev hj hev ht he
    have h51 := gOnlyEff top j hj he
    subst h51
    rw [gev51] at hev
    cases Option.some.inj hev
    obtain ⟨z, hz⟩ : ∃ z : Int, z = D := ⟨D, rfl⟩
    subst hz
    have h1 : (40 : Int) ≤ z := ht
    have h2 : z < 40 := hD
    omega
  exact ⟨fun ⟨j, ev, hj, hev, ht, he, _⟩ => key j ev hj hev ht he,
    fun ⟨j, ev, hj, hev, ht, he, _⟩ => key j ev hj hev ht he⟩

-- Inspection and bad trace for the HG3 gap test: the deadline is exactly 42; the selected
-- first stop is the rise at index 51 (time 40, frontier 2 -> 3), no phase stop exists by
-- 42, and the whole result fails by 29 (no stop before 40 and no served seed before 30).
private theorem gHG3gapExit :
    (7 : Time) + E_gF d5cTiming 1 4 16 = 42 ∧
    FirstRiseStopBy (gR false) c5env (grho false) (gO false) 9 2 42 ∧
    ¬ FirstPhaseStopBy (gR false) c5env (grho false) (gO false) 9 2 42 ∧
    ¬ FrontierHG3Result (gR false) gS c5env (grho false) (gO false) d5cTiming gI gWD.heightPair
      4 1 9 2 7 29 := by
  refine ⟨by decide, ⟨51, gdeliver (gX 10) 40, by decide, gev51 false, by decide,
    (gEffIff false 51).mpr (Or.inl (by decide)), by rw [gfront]; decide,
    fun k hk hk' he => absurd (gOnlyEff false k hk he) (by omega)⟩, ?_, ?_⟩
  · rintro ⟨j, ev, hj, hev, _, he, hf, _⟩
    have h51 := gOnlyEff false j hj he
    subst h51
    rw [gfront] at hf
    exact absurd hf (by decide)
  · rintro (h | h | ⟨t, _, ht, hs⟩)
    · exact (gnoStop false (by decide)).1 h
    · exact (gnoStop false (by decide)).2 h
    · have := gservedLate false hs
      obtain ⟨z, hz⟩ : ∃ z : Int, z = t := ⟨t, rfl⟩
      subst hz
      have h1 : (30 : Int) ≤ z := this
      have h2 : z ≤ 29 := ht
      omega

-- Inspection and bad trace for the HG3 top-J test: the deadline is exactly 38 (inside the
-- horizon 42); no phase stop and no rise exist by 38, so the selected exit is a served seed
-- at a time in [30, 38]; the whole result fails by 29.
private theorem gHG3topExit :
    (7 : Time) + E_jF d5cTiming 1 4 16 = 38 ∧
    ¬ FirstPhaseStopBy (gR true) c5env (grho true) (gO true) 9 2 38 ∧
    ¬ FirstRiseStopBy (gR true) c5env (grho true) (gO true) 9 2 38 ∧
    (∃ t, (30 : Time) ≤ t ∧ t ≤ 38 ∧
      StrongServed (gR true) gS c5env (grho true) (gO true) d5cTiming gI gWD.heightPair 4 1 2 t) ∧
    ¬ FrontierHG3Result (gR true) gS c5env (grho true) (gO true) d5cTiming gI gWD.heightPair
      4 1 9 2 7 29 := by
  have hD : (7 : Time) + E_jF d5cTiming 1 4 16 = 38 := by decide
  have hns := gnoStop true (D := 38) (by decide)
  refine ⟨hD, hns.1, hns.2, ?_, ?_⟩
  · have h := gHG3top
    rw [hD] at h
    rcases h with h | h | ⟨t, _, ht, hs⟩
    · exact absurd h hns.1
    · exact absurd h hns.2
    · exact ⟨t, gservedLate true hs, ht, hs⟩
  · rintro (h | h | ⟨t, _, ht, hs⟩)
    · exact (gnoStop true (by decide)).1 h
    · exact (gnoStop true (by decide)).2 h
    · have := gservedLate true hs
      obtain ⟨z, hz⟩ : ∃ z : Int, z = t := ⟨t, rfl⟩
      subst hz
      have h1 : (30 : Int) ≤ z := this
      have h2 : z ≤ 29 := ht
      omega

#print axioms d5cMovingF
#print axioms d5cRiseExit
#print axioms d5cSeedArms
#print axioms d5cTails
#print axioms c5contest
#print axioms c5contestExit
#print axioms c5shortened
#print axioms r6row
#print axioms r6rowExit
#print axioms m9rise
#print axioms m9riseExit
#print axioms ggapPhase
#print axioms ggapExit
#print axioms gHG3gap
#print axioms gHG3gapExit
#print axioms gHG3top
#print axioms gHG3topExit
end AvailableChain.FGCompose.Tests.P0d5c
end
end
