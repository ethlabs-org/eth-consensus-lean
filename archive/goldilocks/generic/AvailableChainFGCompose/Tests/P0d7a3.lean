module
public import AvailableChainFGCompose.Proofs.Finality.Middle -- shake: keep (kernel test context)

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.P0d7a3
open AvailableChain.SimplexFG AvailableChain.KitFG

-- These are inhabited interface traces. They are not PC-SA production proofs.
private abbrev midE : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private abbrev midCfg : FGConfig := ⟨4⟩
private abbrev midBoot : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private abbrev midX : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 [midBoot]
private abbrev midA : FGBlock (Fin 1) := .node midX 8 ⟨8⟩ 0 []
private abbrev midZ : FGBlock (Fin 1) := .node .genesis 1 ⟨9⟩ 0 [midBoot]
private abbrev midBad : FGBlock (Fin 1) :=
  .node midZ 2 ⟨10⟩ 0 [⟨0, .vote 2 ⟨9⟩ false, none⟩]
private def midErase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node p s r x rs => .node (midErase p) s r (encFGBody x rs)

private theorem midEraseInj : Function.Injective midErase := by
  intro A
  induction A with
  | genesis => intro B h; cases B <;> simp_all [midErase]
  | node p s r x rs ih =>
    intro B h
    cases B with
    | genesis => simp [midErase] at h
    | node q t u y ts =>
      simp only [midErase, Block.node.injEq] at h
      obtain ⟨hp, hs, hr, hb⟩ := h
      obtain ⟨hx, hrows⟩ := encFGBody_inj hb
      cases ih hp
      cases hs
      cases hr
      cases hx
      cases hrows
      rfl

private theorem midReflect (A B : FGBlock (Fin 1))
    (h : Block.Preceq (midErase A) (midErase B)) : FGBlock.Preceq A B := by
  induction B with
  | genesis =>
    have he : midErase A = midErase .genesis := of_decide_eq_true h
    exact midEraseInj he ▸ preceq_refl _
  | node P slot root app rows ih =>
    change (decide (midErase A = midErase (.node P slot root app rows)) ||
      Block.preceq (midErase A) (midErase P)) = true at h
    rw [Bool.or_eq_true] at h
    rcases h with he | hp
    · exact midEraseInj (of_decide_eq_true he) ▸ preceq_refl _
    · exact preceq_node_of_preceq slot root app rows (ih hp)

private abbrev midT : FGTiming where
  delta := 1
  roundSlots := 2
  proposal s := 4 * s
  vote s := 4 * s + 1
  early s := 4 * s + 2
  freeze s := 4 * s + 3
  release s := 4 * s + 5
  gate s := 4 * s + 6
  action r := 4 * (r * 2 : Nat) + 6

private theorem midTiming : FGTimingLaws midT where
  delta_pos := by decide
  rounds := by decide
  proposal_eq := by intro s; simp
  vote_eq := by intro s; rfl
  early_eq := by intro s; rfl
  freeze_eq := by intro s; rfl
  release_eq := by intro s; rfl
  gate_eq := by intro s; rfl
  action_eq := by intro r; rfl

private abbrev midSource (bad t : Time) : FGBlock (Fin 1) :=
  if t = bad then midBad else if t = 6 then .genesis else midX
private abbrev midRow (sign : Bool) (bad t : Time) : Row (Fin 1) :=
  ⟨0, .vote (KitFG.Window.certificateHeight midE midCfg 2 (midSource bad t)).h
    (KitFG.Window.certificateHeight midE midCfg 2 (midSource bad t)).T_h.root sign, none⟩

private abbrev midP (sign : Bool) (bad : Time) : V2.ProtocolSpecD Unit where
  State := Time
  Label := Nat
  Duty := Nat
  signLabel := id
  seats _ := 1
  Payload := Row (Fin 1)
  Durable := Time
  init := 0
  clock _ t := t
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
  act _ s _ := some (midRow sign bad s)
  gossip _ _ := []
  process st _ := st
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

private abbrev midI (sign : Bool) (bad : Time) : V2.D.Interface (midP sign bad) where
  confirmed _ := midErase midX
  stable _ := midErase midX
  block _ := some (midErase midA)
  opening _ := True
  propLabel s := 4 * s
  propDuty s := 4 * s
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective := by
    intro a b h
    change 4 * a = 4 * b at h
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) h

private abbrev midEnv : Generic.Env Unit := ⟨1, by decide, 0, by decide, fun _ _ => true⟩
private abbrev midRun (sign : Bool) (bad : Time) : V2.D.Run Unit (midP sign bad) where
  honest := {()}
  horizon := 40
  events := [.tick () 6, .tick () 14, .tick () 22, .tick () 30, .tick () 32]
  seatOf _ _ := ()
  input _ _ := ()
private abbrev midWire (sign : Bool) (bad : Time) (t : Nat) : (midP sign bad).Object :=
  ⟨.seat t 0, midRow sign bad t⟩
private abbrev midS (sign : Bool) (bad : Time) :
    FGSafetyReads (midP sign bad) 1 (midP sign bad).Object where
  proposalErase _ := some (midErase midA)
  proposalRows _ := []
  encode := id
  decode o := some o.payload
  decodeObject o := some o.payload
  fgLabel := 0
  fgSeats := Equiv.refl _
  record _ := RecordOnce.initial
  inputs t := (some (midSource bad t), ⟨0, genesisRoot, 0⟩)
  enabled _ := true
  finalizedOut _ := .genesis
private abbrev midD (sign : Bool) (bad : Time) : FGHistoryWireReads (midS sign bad) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer a := some a.payload.signer
  decode_height _ _ h := by cases h; rfl
  decode_finality _ _ h := by cases h; rfl
  decode_signer _ _ h := by cases h; rfl
private abbrev midR (sign : Bool) (bad : Time) :
    FGCoreReads (midP sign bad) 1 Unit Unit (midP sign bad).Object where
  core _ := ⟨(), ⟨{.genesis, midX, midA, midZ, midBad}, .genesis, .genesis, 0, 3⟩, [], []⟩
  erase := midErase
  source t := some (midSource bad t)
  headVote _ _ := midErase midA
  finalityHead _ := some midA
  proposalFG _ _ := some midA
private abbrev midO (sign : Bool) (bad : Time) : FGObservationReads (midR sign bad) where
  height := KitFG.Window.certificateHeight midE midCfg 2
  finality := KitFG.Window.certificateFinality midE midCfg 2
  controls _ := ⟨.genesis, 0, 0, .genesis, false⟩
  viable _ X := X
private abbrev midPoint : FGServicePoint :=
  ⟨⟨0, 0, 1, 0, 0, midErase midX⟩, 1, midErase midX, 28⟩

private theorem midPaths : midX ≠ .genesis ∧ midA.parent = midX ∧
    FGBlock.Preceq midX midA ∧
    ((midO false (-1)).height midX).h = 2 := by decide +kernel

private theorem midOpening (sign : Bool) (bad : Time) :
    HonestProposal midEnv (midRun sign bad) (midI sign bad) 8 (midErase midA) := by
  refine ⟨⟨by decide, by simp [midRun]⟩, midWire sign bad 32, ⟨4, rfl, ?_⟩, rfl⟩
  simp [V2.D.Run.emitsAt, V2.D.tick, V2.D.Run.ownSeats, List.finRange_succ,
    midP, midWire]

private theorem midRowOrigin (sign : Bool) (bad : Time) (r : Nat) (hr : r < 4) :
    HonestRowAt (midS sign bad) midEnv (midRun sign bad) midT r () r
      (midWire sign bad (8 * r + 6)) := by
  interval_cases r <;> simp [HonestRowAt, V2.D.Run.emitsAt, V2.D.tick,
    V2.D.Run.ownSeats, List.finRange_succ, midP, midWire]

private theorem midRowCases (sign : Bool) (bad : Time) {j r : Nat}
    {a : (midP sign bad).Object}
    (ha : HonestRowAt (midS sign bad) midEnv (midRun sign bad) midT j () r a) :
    r < 4 ∧ j = r ∧ a = midWire sign bad (8 * r + 6) := by
  have hj : j < 5 := (List.getElem?_eq_some_iff.mp ha.2.1).1
  have ht : (if j = 4 then (32 : Time) else (8 * j + 6 : Nat)) = midT.action r := by
    interval_cases j <;> exact (V2.Event.tick.inj (Option.some.inj ha.2.1)).2
  have hrj : r = j ∧ r < 4 := by
    change (if j = 4 then (32 : Int) else (8 * j + 6 : Nat)) =
      4 * ((r * 2 : Nat) : Int) + 6 at ht
    split_ifs at ht <;> omega
  obtain ⟨heq, hr⟩ := hrj
  subst r
  refine ⟨hr, rfl, ?_⟩
  interval_cases j <;>
    simpa [V2.D.Run.emitsAt, V2.D.tick, V2.D.Run.ownSeats, List.finRange_succ,
      midP, midWire] using ha.2.2

private theorem midSources (sign : Bool) (bad : Time) (r : Nat) (hr : r < 4) :
    actionSourceFG (midR sign bad) midEnv (midRun sign bad) midT () r =
      some (some (midSource bad (8 * r + 6))) := by
  interval_cases r <;> rfl

private theorem midNames (sign : Bool) (bad : Time) :
    HighRecordNames (midR sign bad) (midS sign bad) (midO sign bad) midT midEnv
      (midRun sign bad) (midD sign bad) := by
  intro j x r a e ha he
  cases x
  obtain ⟨hr, hj, heq⟩ := midRowCases sign bad ha
  subst j
  subst a
  refine ⟨midSource bad (8 * r + 6), midSources sign bad r hr, ?_⟩
  exact (Option.some.inj he).symm

private theorem midHistory (sign : Bool) :
    FGHistoricalHighTransfer (midR sign (-1)) (midO sign (-1)) midT midEnv
      (midRun sign (-1)) (midI sign (-1)) midPoint 40 := by
  intro x r C _ hs hc _ s Q hp _ _
  obtain ⟨nd, hnd, he⟩ := Option.map_eq_some_iff.mp hs
  have hC : midSource (-1) nd = C := Option.some.inj he
  subst C
  obtain ⟨pre, _, ht⟩ := Option.map_eq_some_iff.mp hnd
  change midT.action r = nd at ht
  subst nd
  obtain ⟨_, o, _, hQ⟩ := hp
  have hQ' : midErase midA = Q := Option.some.inj hQ
  subst Q
  have hn : midT.action r ≠ -1 := by
    change 4 * ((r * 2 : Nat) : Int) + 6 ≠ -1
    omega
  unfold midSource
  rw [ite_eq_right hn]
  split
  · change Block.Preceq .genesis (midErase midX)
    decide +kernel
  · change Block.Preceq (midErase midX) (midErase midX)
    decide +kernel

private theorem midShield (sign : Bool) (bad : Time) (hbad : bad ≠ 6) :
    HighRecordShieldRows (midR sign bad) (midS sign bad) (midO sign bad) midT
      midEnv (midRun sign bad) (midD sign bad) midX 2 14 := by
  intro j x r a y root timeout ha ht hp
  cases x
  obtain ⟨hr, hj, heq⟩ := midRowCases sign bad ha
  subst j
  subst a
  have rzero : r = 0 := by
    change 4 * ((r * 2 : Nat) : Int) + 6 < 14 at ht
    omega
  subst r
  have hn : (6 : Time) ≠ bad := Ne.symm hbad
  change NamedHeightPair.vote
    (KitFG.Window.certificateHeight midE midCfg 2 (midSource bad 6)).h
    (KitFG.Window.certificateHeight midE midCfg 2 (midSource bad 6)).T_h.root sign = _ at hp
  rw [show midSource bad 6 = .genesis by simp only [midSource, ite_eq_right hn, ite_true]]
    at hp
  change NamedHeightPair.vote 1 genesisRoot sign = .vote y root timeout at hp
  obtain ⟨rfl, _, _⟩ := NamedHeightPair.vote.inj hp
  exact ⟨by decide, by intro h; cases h⟩

private theorem midCaps (sign : Bool) :
    midPoint.reset.M + 1 ≤ 2 ∧ 2 ≤ ((midO sign (-1)).height midA).h ∧
    ∀ j x r a h, r < 4 → HonestRowAt (midS sign (-1)) midEnv (midRun sign (-1)) midT
      j x r a → historyRowHeight (midS sign (-1)) (midD sign (-1)) a = some h →
      h ≤ ((midO sign (-1)).height midA).h := by
  exact middle_shield_rows_below_opening (midR sign (-1)) (midS sign (-1))
    (midO sign (-1)) midT midTiming midEnv (midRun sign (-1)) (midI sign (-1))
    (midD sign (-1)) midE midPoint 40 midX midA 2 14
    ⟨rfl, rfl, by decide, by decide, midShield sign (-1) (by decide)⟩
    (show Block.Preceq (midErase midX) (midErase midA).parent by decide +kernel)
    (midHistory sign)
    (midNames sign (-1)) (KitFG.Window.windowHeightLaws midE midCfg 2 (by decide))
    midReflect (by intro B; cases B <;> rfl) 4 (midOpening sign (-1))
    (by decide) (by decide)

-- Each sign uses the same point, opening, cutoff, and actual four-row prefix.
private theorem midFourCaps (sign : Bool) (r : Nat) (hr : r < 4) :
    ∃ a h, HonestRowAt (midS sign (-1)) midEnv (midRun sign (-1)) midT r () r a ∧
      historyRowHeight (midS sign (-1)) (midD sign (-1)) a = some h ∧
      h ≤ ((midO sign (-1)).height midA).h := by
  let a := midWire sign (-1) (8 * r + 6)
  let h := ((midO sign (-1)).height (midSource (-1) (8 * r + 6))).h
  have ha := midRowOrigin sign (-1) r hr
  have hh : historyRowHeight (midS sign (-1)) (midD sign (-1)) a = some h := rfl
  exact ⟨a, h, ha, hh, (midCaps sign).2.2 r () r a h hr ha hh⟩

private theorem midIntervalTimes : midT.action 0 < 14 ∧ midT.action 1 = 14 ∧
    (14 ≤ midT.action 2 ∧ midT.action 2 < midPoint.serviceStart) ∧
    midPoint.serviceStart ≤ midT.action 3 := by decide

private theorem midBadTransfer (sign : Bool) (r : Nat) (hr : r < 4) :
    ¬ FGHistoricalHighTransfer (midR sign (8 * r + 6)) (midO sign (8 * r + 6)) midT
      midEnv (midRun sign (8 * r + 6)) (midI sign (8 * r + 6)) midPoint 40 := by
  intro history
  have hs : actionSourceFG (midR sign (8 * r + 6)) midEnv (midRun sign (8 * r + 6))
      midT () r = some (some midBad) := by
    have h := midSources sign (8 * r + 6) r hr
    simpa only [midSource, ite_true] using h
  have hp := history () r midBad (by simp) hs
    (show 2 ≤ (KitFG.Window.certificateHeight midE midCfg 2 midBad).h by decide +kernel)
    (by change 4 * ((r * 2 : Nat) : Int) + 6 ≤ 40; omega)
    8 (midErase midA) (midOpening sign (8 * r + 6)) (by decide)
    (by change r * 2 + 2 ≤ 8; omega)
  exact (by decide +kernel : ¬ Block.Preceq (midErase midBad) (midErase midA).parent) hp

private theorem midBadRowCap (sign : Bool) (r : Nat) (hr : r < 4) :
    ∃ a, HonestRowAt (midS sign (8 * r + 6)) midEnv (midRun sign (8 * r + 6)) midT
      r () r a ∧ historyRowHeight (midS sign (8 * r + 6)) (midD sign (8 * r + 6)) a =
        some 3 ∧ ¬ 3 ≤ ((midO sign (8 * r + 6)).height midA).h := by
  refine ⟨midWire sign (8 * r + 6) (8 * r + 6), midRowOrigin sign _ r hr, ?_, ?_⟩
  · change some (KitFG.Window.certificateHeight midE midCfg 2
      (midSource (8 * r + 6) ((8 * r + 6 : Nat) : Time))).h = some 3
    push_cast
    rw [midSource, ite_eq_left rfl]
    rfl
  · change ¬ 3 ≤ (KitFG.Window.certificateHeight midE midCfg 2 midA).h
    decide +kernel

private theorem midOldShieldRejects (sign : Bool) :
    ¬ HighRecordShieldRows (midR sign 6) (midS sign 6) (midO sign 6) midT midEnv
      (midRun sign 6) (midD sign 6) midX 2 14 := by
  intro shield
  have h := (shield 0 () 0 (midWire sign 6 6) 3 midBad.root sign
    (midRowOrigin sign 6 0 (by decide)) (by decide) rfl).1
  exact (by decide : ¬ (3 : Nat) ≤ 2) h

private theorem midCutoffStrict (sign : Bool) :
    HighRecordShieldRows (midR sign 14) (midS sign 14) (midO sign 14) midT midEnv
      (midRun sign 14) (midD sign 14) midX 2 14 ∧
    ¬ HighRecordShieldRows (midR sign 14) (midS sign 14) (midO sign 14) midT midEnv
      (midRun sign 14) (midD sign 14) midX 2 15 := by
  refine ⟨midShield sign 14 (by decide), ?_⟩
  intro shield
  have h := (shield 1 () 1 (midWire sign 14 14) 3 midBad.root sign
    (midRowOrigin sign 14 1 (by decide)) (by decide) rfl).1
  exact (by decide : ¬ (3 : Nat) ≤ 2) h

private theorem midGapRejects (sign : Bool) :
    ¬ FGHistoricalHighTransfer (midR sign 22) (midO sign 22) midT midEnv
      (midRun sign 22) (midI sign 22) midPoint 40 := midBadTransfer sign 2 (by decide)
private theorem midSuffixRejects (sign : Bool) :
    ¬ FGHistoricalHighTransfer (midR sign 30) (midO sign 30) midT midEnv
      (midRun sign 30) (midI sign 30) midPoint 40 := midBadTransfer sign 3 (by decide)

private theorem midLaterStartRejected : ¬ KernelPrem_W midT 1 80
    { midPoint with serviceStart := 33 } ⟨4⟩
    (Gen.V2.Duty.HonestSlot (midRun false (-1)) (midI false (-1))) 1 1 4 2 := by
  intro h
  have hs : (33 : Int) ≤ 32 := h.start
  omega

private abbrev midB : FGBlock (Fin 1) :=
  .node midA 10 ⟨11⟩ 0 [⟨0, .vote 2 midX.root false, none⟩]
private abbrev midEarly : FGBlock (Fin 1) :=
  .node midB 12 ⟨12⟩ 0 [⟨0, .vote 3 midB.root false, none⟩]

-- Real target folds give a fresh non-genesis entry and one retained early carrier.
private theorem midFreshPath :
    midA ≠ .genesis ∧ midB.parent = midA ∧ midEarly.parent = midB ∧
    FGBlock.Preceq midA midB ∧ midA ≠ midB ∧
    (KitFG.Window.certificateHeight midE midCfg 2 midA).h = 2 ∧
    (KitFG.Window.certificateHeight midE midCfg 2 midB).h = 3 ∧
    (KitFG.Window.certificateHeight midE midCfg 2 midB).T_h = midB ∧
    (KitFG.Window.certificateHeight midE midCfg 2 midEarly).h = 4 ∧
    (KitFG.Window.certificateHeight midE midCfg 2 midEarly).J = midB ∧
    (SimplexFG.Window.derive midE midCfg 2 midEarly).h_F < 3 ∧
    KitFG.Window.RetainedW midE midCfg 2 midEarly 3 midB := by
  unfold KitFG.Window.RetainedW
  decide +kernel

private theorem midOneEarlyCarrier : ∀ cD, (4 + 1) * midT.roundSlots + kappaF midT 1 ≤ cD →
    cD ≤ (4 + 2) * midT.roundSlots → cD = midEarly.slot := by
  intro cD hlo hhi
  change 12 ≤ cD at hlo
  change cD ≤ 12 at hhi
  exact Nat.le_antisymm hhi hlo

#print axioms midFourCaps
#print axioms midIntervalTimes
#print axioms midBadTransfer
#print axioms midBadRowCap
#print axioms midOldShieldRejects
#print axioms midCutoffStrict
#print axioms midGapRejects
#print axioms midSuffixRejects
#print axioms midLaterStartRejected
#print axioms midFreshPath
#print axioms midOneEarlyCarrier

#print axioms midPaths
#print axioms midOpening
#print axioms midRowOrigin
#print axioms midSources
#print axioms midNames
#print axioms midShield
#print axioms midCaps
end AvailableChain.FGCompose.Tests.P0d7a3
end
