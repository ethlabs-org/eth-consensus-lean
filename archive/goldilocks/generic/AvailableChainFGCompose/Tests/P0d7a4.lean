module
public import AvailableChainFGCompose.Proofs.Finality.Carry
public import AvailableChainFGCompose.Proofs.Finality.Rows
public import AvailableChainFGCompose.Proofs.Finality.RowsRecords

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.P0d7a4
open AvailableChain.SimplexFG AvailableChain.KitFG

-- Inhabited interface execution with actual row emission and carrier contents.
private abbrev rowsE : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private abbrev rowsCfg : FGConfig := ⟨4⟩
private abbrev rowsBoot : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private abbrev rowsU : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 [rowsBoot]
private abbrev rowsTarget : Row (Fin 1) := ⟨0, .vote 2 ⟨1⟩ false, none⟩
private abbrev rowsD : FGBlock (Fin 1) := .node rowsU 2 ⟨2⟩ 0 [rowsTarget]
private abbrev rowsSigned (sign : Bool) : Row (Fin 1) :=
  ⟨0, .vote 3 ⟨2⟩ sign, some ⟨2, ⟨1⟩⟩⟩
private abbrev rowsX (sign : Bool) : FGBlock (Fin 1) :=
  .node rowsD 6 ⟨6⟩ 0 [rowsSigned sign]
private def rowsErase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node p s r x rs => .node (rowsErase p) s r (encFGBody x rs)

private theorem rowsEraseInj : Function.Injective rowsErase := by
  intro A
  induction A with
  | genesis => intro B h; cases B <;> simp_all [rowsErase]
  | node p s r x rs ih =>
    intro B h
    cases B with
    | genesis => simp [rowsErase] at h
    | node q t u y ts =>
      simp only [rowsErase, Block.node.injEq] at h
      obtain ⟨hp, hs, hr, hb⟩ := h
      obtain ⟨hx, hrows⟩ := encFGBody_inj hb
      cases ih hp
      cases hs
      cases hr
      cases hx
      cases hrows
      rfl

private theorem rowsReflect (A B : FGBlock (Fin 1))
    (h : Block.Preceq (rowsErase A) (rowsErase B)) : FGBlock.Preceq A B := by
  induction B with
  | genesis =>
    have he : rowsErase A = rowsErase .genesis := of_decide_eq_true h
    exact rowsEraseInj he ▸ preceq_refl _
  | node P slot root app rows ih =>
    change (decide (rowsErase A = rowsErase (.node P slot root app rows)) ||
      Block.preceq (rowsErase A) (rowsErase P)) = true at h
    rw [Bool.or_eq_true] at h
    rcases h with he | hp
    · exact rowsEraseInj (of_decide_eq_true he) ▸ preceq_refl _
    · exact preceq_node_of_preceq slot root app rows (ih hp)

private abbrev rowsT : FGTiming where
  delta := 1
  roundSlots := 2
  proposal s := 4 * s
  vote s := 4 * s + 1
  early s := 4 * s + 2
  freeze s := 4 * s + 3
  release s := 4 * s + 5
  gate s := 4 * s + 6
  action r := 4 * (r * 2 : Nat) + 6

private theorem rowsTiming : FGTimingLaws rowsT where
  delta_pos := by decide
  rounds := by decide
  proposal_eq := by intro s; simp
  vote_eq := by intro s; rfl
  early_eq := by intro s; rfl
  freeze_eq := by intro s; rfl
  release_eq := by intro s; rfl
  gate_eq := by intro s; rfl
  action_eq := by intro r; rfl

private abbrev rowsP (sign : Bool) : V2.ProtocolSpecD Unit where
  State := Unit
  Label := Nat
  Duty := Nat
  signLabel := id
  seats _ := 1
  Payload := Row (Fin 1)
  Durable := Unit
  init := ()
  clock _ _ := ()
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
  act _ _ _ := some (rowsSigned sign)
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


private abbrev rowsI (sign : Bool) : V2.D.Interface (rowsP sign) where
  confirmed _ := rowsErase rowsD
  stable _ := rowsErase rowsD
  block _ := some (rowsErase (rowsX sign))
  opening _ := True
  propLabel s := 4 * s
  propDuty s := 4 * s
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective := by
    intro a b h
    change 4 * a = 4 * b at h
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) h

private abbrev rowsEnv : Generic.Env Unit :=
  ⟨1, by decide, 0, by decide, fun _ t => decide (t = 6 ∨ t = 24)⟩
private abbrev rowsRun (sign : Bool) : V2.D.Run Unit (rowsP sign) where
  honest := {()}
  horizon := 30
  events := [.tick () 6, .tick () 24]
  seatOf _ _ := ()
  input _ _ := ()
private abbrev rowsObj (sign : Bool) (t : Nat) : (rowsP sign).Object :=
  ⟨.seat t 0, rowsSigned sign⟩
private abbrev rowsS (sign : Bool) : FGSafetyReads (rowsP sign) 1 (Row (Fin 1)) where
  proposalErase _ := some (rowsErase (rowsX sign))
  proposalRows o := [o.payload]
  encode a := ⟨.seat 6 0, a⟩
  decode := some
  decodeObject o := some o.payload
  fgLabel := 6
  fgSeats := Equiv.refl _
  record _ := RecordOnce.initial
  inputs _ := (some rowsD, ⟨2, ⟨1⟩, 0⟩)
  enabled _ := true
  finalizedOut _ := .genesis
private abbrev rowsWire (sign : Bool) : FGHistoryWireReads (rowsS sign) where
  heightPair := Row.height_pair
  finalityPair := Row.finality_pair
  signer a := some a.signer
  decode_height _ _ h := by cases h; rfl
  decode_finality _ _ h := by cases h; rfl
  decode_signer _ _ h := by cases h; rfl
private abbrev rowsR (sign : Bool) : FGCoreReads (rowsP sign) 1 Unit Unit (Row (Fin 1)) where
  core _ := ⟨(), ⟨{.genesis, rowsU, rowsD}, .genesis, .genesis, 0, 3⟩, [], [rowsSigned sign]⟩
  erase := rowsErase
  source _ := some rowsD
  headVote _ _ := rowsErase rowsD
  finalityHead _ := some rowsD
  proposalFG _ _ := some (rowsX sign)
private abbrev rowsO (sign : Bool) : FGObservationReads (rowsR sign) where
  height := KitFG.Window.certificateHeight rowsE rowsCfg 2
  finality := KitFG.Window.certificateFinality rowsE rowsCfg 2
  controls _ := ⟨.genesis, 0, 0, .genesis, false⟩
  viable _ X := X

private theorem rowsCore (sign : Bool) : FGCoreLaws (rowsR sign) where
  clock_fg _ _ := rfl
  clock_proposals _ _ := rfl
  clock_rowPool _ _ := rfl
  process_tf _ _ := Finset.Subset.refl _
  process_proposals _ _ := List.prefix_refl _
  process_rowPool _ _ := List.prefix_refl _
  own_core _ _ := rfl
  source_mem _ C h := by
    cases h
    change rowsD ∈ ({.genesis, rowsU, rowsD} : Finset (FGBlock (Fin 1)))
    decide +kernel
  erase_inj := rowsEraseInj

private theorem rowsRead (sign : Bool) : postClock rowsEnv (rowsRun sign) () 6 = some () := by
  cases sign <;> decide +kernel

private theorem rowsService (sign : Bool) :
    FGSourceService (rowsR sign) rowsEnv (rowsRun sign) () 6 0 0 rowsD where
  openingSource _ := ⟨(), rowsRead sign, rfl⟩
  coveredSource h := by omega

private theorem rowsSourceProduced (sign : Bool) :
    ∃ nd C, postClock rowsEnv (rowsRun sign) () 6 = some nd ∧
      (rowsR sign).source nd = some C ∧ FGBlock.Preceq rowsD C ∧
      ((rowsO sign).height C).h = 3 ∧
      ((rowsO sign).height C).T_h = ((rowsO sign).height rowsD).T_h := by
  exact finality_action_source (rowsR sign) (rowsO sign) rowsT rowsEnv (rowsRun sign)
    (rowsCore sign) rowsE (KitFG.Window.windowHeightLaws rowsE rowsCfg 2 (by decide))
    () 0 2 0 rowsD (rowsService sign) (by decide) (by cases sign <;> decide +kernel)
    (by
      intro nd _ B hB
      simp only [Finset.mem_insert, Finset.mem_singleton] at hB
      rcases hB with rfl | rfl | rfl <;> cases sign <;> decide +kernel)

private theorem rowsSourceInspected (sign : Bool) :
    ∃ C, C = rowsD ∧ C ≠ .genesis ∧ ((rowsO sign).height C).h = 3 := by
  obtain ⟨nd, C, _, hs, _, hh, _⟩ := rowsSourceProduced sign
  have he : rowsD = C := Option.some.inj hs
  exact ⟨C, he.symm, he ▸ (by decide +kernel), hh⟩

private theorem rowsEmitted (sign : Bool) :
    HonestRowAt (rowsS sign) rowsEnv (rowsRun sign) rowsT 0 () 0 (rowsSigned sign) := by
  refine ⟨by change () ∈ ({()} : Finset Unit); decide, rfl, ?_⟩
  simp [V2.D.Run.emitsAt, V2.D.tick, V2.D.Run.ownSeats, List.finRange_succ,
    rowsP]

private theorem rowsAllEmitted (sign : Bool) (j : Nat) (a : Row (Fin 1))
    (h : (rowsS sign).encode a ∈ V2.D.Run.emitsAt rowsEnv (rowsRun sign) j) :
    a = rowsSigned sign := by
  cases j with
  | zero =>
    simpa [V2.D.Run.emitsAt, V2.D.tick, V2.D.Run.ownSeats, List.finRange_succ,
      rowsP] using h
  | succ j =>
    cases j with
    | zero =>
      simp [V2.D.Run.emitsAt, V2.D.tick, V2.D.Run.ownSeats, List.finRange_succ,
        rowsP] at h
    | succ j => simp [V2.D.Run.emitsAt] at h

private abbrev rowsCarrier (sign : Bool) (o : (rowsP sign).Object)
    (s : Slot) (Q : Block) (rs : List (Row (Fin 1))) : Prop :=
  s = 6 ∧ Q = rowsErase (rowsX sign) ∧ o.payload = rowsSigned sign ∧ rs = [o.payload]
private abbrev rowsParent (_ : Unit) (_ : Block) := some rowsD
private abbrev rowsValid (_ : Unit) (s : Slot) (B : FGBlock (Fin 1)) (a : Row (Fin 1)) :=
  SimplexFG.Window.r6w (KitFG.Window.parentState rowsE rowsCfg 2 B s) a
private abbrev rowsPool (sign : Bool) (_ : Unit) := [rowsSigned sign]
private abbrev rowsChain (_ : Unit) (_ : Block) := [rowsBoot, rowsTarget]

private theorem rowsSelected (sign : Bool) :
    TRowsSelect (rowsR sign) (rowsS sign) rowsEnv (rowsRun sign) rowsT (rowsI sign)
      (rowsCarrier sign) rowsChain (rowsPool sign) rowsParent rowsValid := by
  intro s Q rs j x r a hc ha _ _
  obtain ⟨_, o, _, _, _, ho, hrs⟩ := hc
  have he := rowsAllEmitted sign j a ha.2.2
  subst a
  exact Or.inl (hrs ▸ ho ▸ List.mem_singleton_self _)

private theorem rowsParentRead (sign : Bool) :
    proposalStateAt rowsEnv (rowsRun sign) (rowsI sign) 6 = some () := by
  cases sign <;> decide +kernel

private theorem rowsCarrierProduced (sign : Bool) :
    HonestCarrier rowsEnv (rowsRun sign) (rowsI sign) (rowsCarrier sign)
      6 (rowsErase (rowsX sign)) [rowsSigned sign] := by
  have emitted : V2.D.Run.emits rowsEnv (rowsRun sign) () (rowsObj sign 24) 24 := by
    refine ⟨1, rfl, ?_⟩
    simp [V2.D.Run.emitsAt, V2.D.tick, V2.D.Run.ownSeats, List.finRange_succ,
      rowsP, rowsObj]
  refine ⟨⟨⟨by decide, by simp [rowsRun]⟩, rowsObj sign 24, emitted, rfl⟩,
    rowsObj sign 24, emitted, rfl, rfl, rfl, rfl⟩

private theorem rowsOccurrence (sign : Bool) (s : Slot) (Q : Block)
    (H : FGBlock (Fin 1)) (nd : Unit) (a u : Row (Fin 1))
    (_ : proposalStateAt rowsEnv (rowsRun sign) (rowsI sign) s = some nd)
    (hp : rowsParent nd Q.parent = some H)
    (hm : a ∈ rowsChain nd Q.parent) (hd : (rowsS sign).decode a = some u) :
    ∃ W, FGBlock.Preceq W H ∧ u ∈ W.rows := by
  have hH : rowsD = H := Option.some.inj hp
  have hu : a = u := Option.some.inj hd
  subst H u
  change a ∈ [rowsBoot, rowsTarget] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact ⟨rowsU, preceq_parent_node _ _ _ _ _, by decide +kernel⟩
  · exact ⟨rowsD, preceq_refl _, by decide +kernel⟩

private theorem rowsParentValid :
    ∀ B s root body rs, FGBlock.Preceq (.node B s root body rs) rowsD → ∀ a ∈ rs,
      (match a.height_pair with
        | .empty => false
        | .vote h _ _ => decide (1 ≤ h) &&
          (a.finality_pair.map (fun fp => decide (fp.height < h))).getD true) = true ∧
        SimplexFG.Window.r6w (SimplexFG.Window.derive rowsE rowsCfg 2 B) a = true := by
  intro B s root body rs hp a ha
  simp only [FGBlock.Preceq, FGBlock.preceq, rowsU, Bool.or_eq_true,
    decide_eq_true_eq, FGBlock.node.injEq] at hp
  rcases hp with h | h | h
  · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    have he : a = rowsTarget := List.mem_singleton.mp ha
    subst a
    decide +kernel
  · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    have he : a = rowsBoot := List.mem_singleton.mp ha
    subst a
    decide +kernel
  · cases h

private theorem rowsNonempty : ¬ rowsE.IsQuorum ∅ := by
  unfold Electorate.IsQuorum
  decide +kernel
private theorem rowsRetained : KitFG.Window.RetainedW rowsE rowsCfg 2 rowsD 2 rowsU := by
  refine ⟨⟨2, rowsU, ∅⟩, ?_, rfl, rfl⟩
  decide +kernel

private theorem rowsCarriage (sign : Bool) :
    KitFG.Window.CoveredW rowsE rowsCfg 2 (rowsX sign).parent 2 rowsU ∨
      FinalityCoveredByChild_W rowsE rowsCfg 2 (rowsX sign) rowsU 2 := by
  have result := terminalCarriage_general_W (rowsR sign) (rowsS sign) rowsT
    rowsEnv (rowsRun sign) (rowsI sign) (rowsWire sign) rowsE rowsCfg 2
    (rowsCarrier sign) rowsChain (rowsPool sign) rowsParent rowsValid
    (rowsSelected sign) rowsNonempty (by decide)
    (by intro a i _; exact ⟨a, rfl⟩) (rowsOccurrence sign)
    (rowsO sign).height (KitFG.Window.windowHeightLaws rowsE rowsCfg 2 (by decide)) rfl
    (fun _ _ B => (((rowsO sign).height B).h, ((rowsO sign).height B).T_h.root))
    (by intros; rfl) (by intros; rfl) 0 2 3 rowsD rowsU (rowsX sign) (by decide)
    ⟨[rowsSigned sign], rowsCarrierProduced sign, rfl⟩
    ⟨(), rowsParentRead sign, rfl⟩ rowsParentValid (preceq_refl _)
    (by cases sign <;> decide +kernel) (Or.inl rowsRetained) {0} (fun _ => rowsSigned sign)
    (by unfold Electorate.IsQuorum; decide +kernel)
    (by intro i _; have hi : i = 0 := Subsingleton.elim _ _; subst i
        exact ⟨0, rowsEmitted sign, rfl, rfl, rfl⟩)
    (by intro i _; rfl)
    (by intro i _; exact ⟨(), rowsParentRead sign, Or.inl (List.mem_singleton_self _)⟩)
  rcases result with hc | ⟨_, hcarry⟩
  · exact Or.inl hc
  · exact Or.inr hcarry

private theorem rowsCarriageInspected (sign : Bool) :
    ∃ row ∈ (rowsX sign).rows,
      row.signer = (0 : Fin 1) ∧ row.height_pair = .vote 3 ⟨2⟩ sign ∧
        row.finality_pair = some ⟨2, rowsU.root⟩ := by
  have hn : ¬ KitFG.Window.CoveredW rowsE rowsCfg 2 rowsD 2 rowsU := by
    rw [KitFG.Window.CoveredW_def]
    decide +kernel
  obtain h | h := rowsCarriage sign
  · exact (hn h).elim
  · obtain ⟨e, he, hy, hU, seats, hq, hs⟩ := h
    have hzero : (0 : Fin 1) ∈ seats := by
      by_contra hzero
      have hempty : seats = ∅ := by
        ext i
        have hi : i = 0 := Subsingleton.elim _ _
        simp [hi, hzero]
      exact rowsNonempty (hempty ▸ hq)
    have hnot : (0 : Fin 1) ∉ e.Q := by
      have hw : (SimplexFG.Window.derive rowsE rowsCfg 2 rowsD).W =
          [⟨1, .genesis, ∅⟩, ⟨2, rowsU, ∅⟩] := by decide +kernel
      change e ∈ (SimplexFG.Window.derive rowsE rowsCfg 2 rowsD).W at he
      rw [hw] at he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp
    obtain hb | ⟨row, hr, hi, hf⟩ := hs 0 hzero
    · exact (hnot hb).elim
    · have heq : row = rowsSigned sign := List.mem_singleton.mp hr
      exact ⟨row, hr, hi, heq ▸ rfl, hf⟩

private theorem rowsBothSigns :
    (∃ row ∈ (rowsX false).rows, row.height_pair = .vote 3 ⟨2⟩ false ∧
      row.finality_pair = some ⟨2, rowsU.root⟩) ∧
    (∃ row ∈ (rowsX true).rows, row.height_pair = .vote 3 ⟨2⟩ true ∧
      row.finality_pair = some ⟨2, rowsU.root⟩) := by
  constructor
  all_goals
    obtain ⟨row, hr, _, hp, hf⟩ := rowsCarriageInspected _
    exact ⟨row, hr, hp, hf⟩

private theorem rowsClientProduced :
    (createRowOnce rowsE rowsCfg RecordOnce.initial (0 : Fin 1)
      (some rowsD) ⟨2, ⟨1⟩, 0⟩).1 = some (rowsSigned false) := by decide +kernel

private theorem rowsFreshProduced :
    ∃ rows : Fin 1 → Row (Fin 1),
      FreshFinalityRows_W (rowsR false) (rowsS false) (rowsO false) rowsT rowsEnv
        (rowsRun false) (rowsWire false) rowsE (fun _ => true) 0 2 rowsU {0} rows ∧
      (∀ i ∈ ({0} : Finset (Fin 1)), (rows i).height_pair = .vote 3 ⟨2⟩ false) := by
  have result := fresh_unanimous_rows (rowsR false) (rowsS false) (rowsO false) rowsT
    rowsEnv (rowsRun false) (rowsWire false) rowsE rowsCfg (fun _ => true)
    (KitFG.Window.windowHeightLaws rowsE rowsCfg 2 (by decide))
    (KitFG.Window.windowHeightBridge rowsE rowsCfg 2 (by decide)) id
    (by intro row; rfl) (by intros; rfl) (by intro nd; rfl)
    (by
      intro i q nd row hn _ hr
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      have he : row = rowsSigned false := Option.some.inj (hr.symm.trans rowsClientProduced)
      subst row
      obtain ⟨j, hj, _⟩ := postClock_tick rowsEnv (rowsRun false) hn
      have hq : q = 0 := by
        cases j with
        | zero =>
          have ht : (6 : Time) = rowsT.action q := by simpa [rowsRun] using hj
          change (6 : Time) = 4 * (q * 2 : Nat) + 6 at ht
          norm_cast at ht
          omega
        | succ j =>
          cases j with
          | zero =>
            have ht : (24 : Time) = rowsT.action q := by simpa [rowsRun] using hj
            change (24 : Time) = 4 * (q * 2 : Nat) + 6 at ht
            norm_cast at ht
            omega
          | succ j => simp [rowsRun] at hj
      subst q
      exact ⟨0, rfl, (rowsEmitted false).2.2⟩)
    0 2 rowsD rowsU {0} (by intro i _; change () ∈ ({()} : Finset Unit); decide)
    (by unfold Electorate.IsQuorum; decide +kernel)
    (by decide +kernel)
    (by
      intro i _
      obtain ⟨nd, C, hn, hs, hp, hh, _⟩ := rowsSourceProduced false
      exact ⟨nd, C, hn, rfl, hs, hp, hh⟩)
    (by intro i _ nd _; exact ⟨rfl, rfl, by change 0 < (2 : Nat); decide⟩)
    (by intro i _ nd _; exact ⟨⟨Or.inl rfl, rfl, Or.inl rfl⟩,
        rfl, rfl, rfl, by simp [RecordOnce.initial]⟩)
    (by intro i _ j r a h hr; omega)
  obtain ⟨rows, fresh, _, hp⟩ := result
  exact ⟨rows, fresh, hp⟩

private theorem rowsFreshInspected :
    ∃ rows : Fin 1 → Row (Fin 1), rows 0 = rowsSigned false ∧
      HonestRowAt (rowsS false) rowsEnv (rowsRun false) rowsT 0 () 0 (rows 0) := by
  obtain ⟨rows, fresh, _⟩ := rowsFreshProduced
  obtain ⟨j, _, ha, _⟩ := fresh.2.2 0 (by decide)
  have he := rowsAllEmitted false j (rows 0) ha.2.2
  exact ⟨rows, he, he ▸ rowsEmitted false⟩

private theorem rowsFreshCarried :
    ∃ rows : Fin 1 → Row (Fin 1),
      HonestRowAt (rowsS false) rowsEnv (rowsRun false) rowsT 0 () 0 (rows 0) ∧
      rows 0 ∈ (rowsX false).rows ∧
      (rows 0).height_pair = .vote 3 ⟨2⟩ false ∧
      (rows 0).finality_pair = some ⟨2, rowsU.root⟩ := by
  obtain ⟨rows, he, ha⟩ := rowsFreshInspected
  obtain ⟨row, hr, _, hp, hf⟩ := rowsCarriageInspected false
  have hr' : row = rows 0 := (List.mem_singleton.mp hr).trans he.symm
  subst row
  exact ⟨rows, ha, hr, hp, hf⟩

private theorem rowsBitArms (sign : Bool) :
    let parent := KitFG.Window.parentState rowsE rowsCfg 2 rowsD 6
    let afterRow := SimplexFG.Window.process_row parent (rowsSigned sign)
    (0 : Fin 1) ∈ afterRow.progress ∧
    ((0 : Fin 1) ∈ afterRow.target_participation ↔ sign = false) ∧
    ∃ e ∈ afterRow.W, e.j = 2 ∧ e.X = rowsU ∧ (0 : Fin 1) ∈ e.Q := by
  cases sign <;> decide +kernel

private theorem rowsRetentionProduced (sign : Bool) :
    KitFG.Window.RetainedW rowsE rowsCfg 2 (rowsX sign) 2 rowsU ∨
      KitFG.Window.CoveredW rowsE rowsCfg 2 (rowsX sign) 2 rowsU := by
  exact actual_anchor_retained_or_covered rowsE rowsCfg 2 rowsNonempty (by decide)
    2 rowsD rowsU (rowsX sign) (preceq_parent_node _ _ _ _ _) rowsRetained
    (by cases sign <;> decide +kernel)

private theorem rowsPrunedInspected (sign : Bool) :
    KitFG.Window.CoveredW rowsE rowsCfg 2 (rowsX sign) 2 rowsU ∧
      ¬ KitFG.Window.RetainedW rowsE rowsCfg 2 (rowsX sign) 2 rowsU := by
  have hn : ¬ KitFG.Window.RetainedW rowsE rowsCfg 2 (rowsX sign) 2 rowsU := by
    have hw : (SimplexFG.Window.derive rowsE rowsCfg 2 (rowsX sign)).W =
        (if sign then [] else [⟨3, rowsD, ∅⟩]) := by cases sign <;> decide +kernel
    rw [KitFG.Window.RetainedW_def, hw]
    cases sign <;> simp
  exact ⟨(rowsRetentionProduced sign).resolve_left hn, hn⟩

private abbrev rowsNoFin : FGBlock (Fin 1) :=
  .node rowsD 6 ⟨6⟩ 0 [⟨0, .vote 3 ⟨2⟩ false, none⟩]
private theorem rowsCapacityRequired :
    ¬ KitFG.Window.RetainedW rowsE rowsCfg 1 rowsNoFin 2 rowsU ∧
    ¬ KitFG.Window.CoveredW rowsE rowsCfg 1 rowsNoFin 2 rowsU ∧
    KitFG.Window.RetainedW rowsE rowsCfg 2 rowsNoFin 2 rowsU := by
  have h1 : (SimplexFG.Window.derive rowsE rowsCfg 1 rowsNoFin).W =
      [⟨3, rowsD, ∅⟩] := by decide +kernel
  have h2 : (SimplexFG.Window.derive rowsE rowsCfg 2 rowsNoFin).W =
      [⟨2, rowsU, ∅⟩, ⟨3, rowsD, ∅⟩] := by decide +kernel
  rw [KitFG.Window.RetainedW_def, KitFG.Window.CoveredW_def,
    KitFG.Window.RetainedW_def, h1, h2]
  simp
  decide +kernel

private theorem rowsSignedIdentityRequired :
    rowsSigned false ≠ rowsSigned true ∧ rowsSigned false ∉ (rowsX true).rows := by
  decide +kernel

private theorem rowsWrongFinalityKey :
    let row : Row (Fin 1) := ⟨0, .vote 3 ⟨2⟩ false, some ⟨2, ⟨9⟩⟩⟩
    let afterRow := SimplexFG.Window.process_row
      (KitFG.Window.parentState rowsE rowsCfg 2 rowsD 6) row
    ∀ e ∈ afterRow.W, e.j = 2 → (0 : Fin 1) ∉ e.Q := by decide +kernel

private theorem rowsBudgetGuards :
    kappaF rowsT 1 = 2 ∧ kappaF rowsT 1 ≤ rowsT.roundSlots ∧
      ¬ kappaF rowsT 10 ≤ rowsT.roundSlots ∧ ¬ 2 ≤ (1 : Nat) := by decide +kernel

private theorem rowsSchedule (sign : Bool) :
    V2.D.ScheduleWellFormed rowsEnv (rowsRun sign) where
  horizon_nonneg := by cases sign <;> decide
  sorted := by cases sign <;> decide +kernel
  nodup := by cases sign <;> decide +kernel
  in_horizon := by
    intro ev hm
    change ev ∈ [.tick () 6, .tick () 24] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl <;> cases sign <;> decide
  honest_only := by
    intro ev hm
    change ev ∈ [.tick () 6, .tick () 24] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl <;> cases sign <;> decide
  tick_public := by
    intro x t hm
    change V2.Event.tick x t ∈ [.tick () 6, .tick () 24] at hm
    simp only [List.mem_cons, List.mem_nil_iff, V2.Event.tick.injEq, or_false] at hm
    rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨6, by decide⟩
    · exact ⟨24, by decide⟩
  tick_total := by
    intro x _ t _ _ _ ha
    have ht : t = 6 ∨ t = 24 := of_decide_eq_true ha
    rcases ht with rfl | rfl <;> simp

private theorem rowsFaultFree (sign : Bool) :
    rowsE.weightOf (historyFaulty (rowsS sign) (rowsRun sign)) < rowsE.q := by
  have h : historyFaulty (rowsS sign) (rowsRun sign) = ∅ := by
    ext i
    simp [historyFaulty, safetyHolder]
  rw [h]
  decide +kernel

-- The action label: the produced pending head at the exact action read.
private theorem rowsHeadProduced (sign : Bool) :
    ∃ H, (rowsR sign).finalityHead () = some H ∧ FGBlock.Preceq rowsD H ∧
      ((rowsO sign).height H).h = 3 ∧ ((rowsO sign).height H).J = rowsU ∧
      ((rowsO sign).height H).h_j = 2 ∧ ((rowsO sign).finality H).h_F < 2 ∧
      ((rowsO sign).height H).T_h = ((rowsO sign).height rowsD).T_h := by
  have hTF : ∀ B ∈ ((rowsR sign).core ()).fg.TF, B = .genesis ∨ B = rowsU ∨ B = rowsD := by
    intro B hB
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hB
  exact pending_action_head_capped (rowsR sign) (rowsO sign) rowsE rowsCfg
    (KitFG.Window.windowHeightLaws rowsE rowsCfg 2 (by decide))
    (KitFG.Window.windowHeightBridge rowsE rowsCfg 2 (by decide)) 2 rowsD rowsU ()
    ⟨rowsD, rfl, by cases sign <;> decide +kernel⟩
    (by intro H hH; cases hH; cases sign <;> decide +kernel)
    (fun A B _ _ h => rowsReflect A B h) (by cases sign <;> decide +kernel)
    (by cases sign <;> decide +kernel) (by cases sign <;> decide +kernel)
    (by cases sign <;> decide +kernel)
    (by intro B hB; rcases hTF B hB with rfl | rfl | rfl <;> cases sign <;> decide +kernel)
    (by intro B hB; rcases hTF B hB with rfl | rfl | rfl <;> cases sign <;> decide +kernel)

private theorem rowsHeadInspected (sign : Bool) :
    ∃ H, H = rowsD ∧ H ≠ .genesis ∧ (rowsR sign).finalityHead () = some H ∧
      ((rowsO sign).height H).h = 3 ∧ ((rowsO sign).height H).J = rowsU := by
  obtain ⟨H, hH, _, hh, hJ, _⟩ := rowsHeadProduced sign
  have he : rowsD = H := Option.some.inj hH
  exact ⟨H, he.symm, he ▸ (by decide +kernel), hH, hh, hJ⟩

-- Two HEAD labels: the action read at T.action 0 and the proposal read at slot 6.
private theorem rowsTwoLabels (sign : Bool) :
    ∃ H, (postClock rowsEnv (rowsRun sign) () (rowsT.action 0)).bind
        (rowsR sign).finalityHead = some H ∧ ((rowsO sign).height H).h = 3 ∧
      proposalHeadAt rowsEnv (rowsRun sign) (rowsI sign) (rowsR sign).headVote 6 =
        some (rowsErase H) ∧ rowsT.action 0 < rowsT.proposal 6 := by
  obtain ⟨H, hH, _, hh, _⟩ := rowsHeadProduced sign
  have he : rowsD = H := Option.some.inj hH
  subst H
  refine ⟨rowsD, ?_, hh, ?_, by decide⟩
  · rw [show rowsT.action 0 = 6 by decide, rowsRead sign]
    rfl
  · unfold proposalHeadAt
    rw [rowsParentRead sign]
    rfl

private theorem rowsTargetQC : TargetQCAt rowsE rowsD 2 rowsU :=
  ⟨{0}, by unfold Electorate.IsQuorum; decide +kernel, fun i _ =>
    ⟨rowsD, rowsTarget, preceq_refl _, by decide +kernel, Subsingleton.elim _ _, rfl⟩⟩

private theorem rowsBatchPrem (sign : Bool) :
    FinalityBatchPrem_W (rowsR sign) (rowsS sign) rowsT rowsEnv (rowsRun sign) (rowsI sign)
      (rowsWire sign) rowsE rowsCfg 2 (fun _ => true) (rowsCarrier sign) (rowsPool sign)
      rowsParent rowsValid SimplexFG.Window.r6w 1 0 2 rowsU (rowsX sign) where
  schedule := rowsSchedule sign
  fault_weight := rowsFaultFree sign
  deltaF := by decide
  rowsReceipt := by
    intro j y r a ha _ x _
    have he := rowsAllEmitted sign j a ha.2.2
    subst a
    exact Or.inl (List.mem_singleton_self _)
  carrier := ⟨[rowsSigned sign], rowsCarrierProduced sign, rfl⟩
  after := by cases sign <;> decide +kernel
  horizon := by cases sign <;> decide +kernel
  parent := ⟨(), rowsParentRead sign, rfl⟩
  birth := ⟨rowsD, preceq_refl _, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, rowsTargetQC⟩
  retainedOrCovered := Or.inl rowsRetained
  batch := by
    refine ⟨{0}, fun i _ => (by change () ∈ ({()} : Finset Unit); decide),
      by unfold Electorate.IsQuorum; decide +kernel, ?_⟩
    intro i _
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact ⟨0, rowsSigned sign, rowsEmitted sign, ⟨rfl, 0, rfl, rfl⟩, rfl, rfl,
      Or.inl (List.mem_singleton_self _),
      ⟨(), rowsParentRead sign, Or.inl (List.mem_singleton_self _)⟩,
      fun _ => ⟨by cases sign <;> decide +kernel,
        ⟨(), rowsD, rowsParentRead sign, rfl, by cases sign <;> decide +kernel⟩⟩⟩

private theorem rowsBatch (sign : Bool) :
    KitFG.Window.CoveredW rowsE rowsCfg 2 (rowsX sign).parent 2 rowsU ∨
      FinalityCoveredByChild_W rowsE rowsCfg 2 (rowsX sign) rowsU 2 :=
  finalityBatchCoverage_W_of_tRowsSelect (rowsR sign) (rowsS sign) rowsT rowsEnv
    (rowsRun sign) (rowsI sign) (rowsWire sign) rowsE rowsCfg 2 (rowsCarrier sign)
    rowsChain (rowsPool sign) rowsParent rowsValid (rowsSelected sign) rowsNonempty
    (by decide) (by intro a i _; exact ⟨a, rfl⟩) (rowsOccurrence sign)
    SimplexFG.Window.r6w (fun _ => true) 1 0 2 rowsU (rowsX sign) (rowsBatchPrem sign)
    rowsParentValid

private theorem rowsBatchInspected (sign : Bool) :
    ∃ row ∈ (rowsX sign).rows,
      row.signer = (0 : Fin 1) ∧ row.height_pair = .vote 3 ⟨2⟩ sign ∧
        row.finality_pair = some ⟨2, rowsU.root⟩ := by
  have hn : ¬ KitFG.Window.CoveredW rowsE rowsCfg 2 rowsD 2 rowsU := by
    rw [KitFG.Window.CoveredW_def]
    decide +kernel
  obtain h | h := rowsBatch sign
  · exact (hn h).elim
  · obtain ⟨e, he, _, _, seats, hq, hs⟩ := h
    have hzero : (0 : Fin 1) ∈ seats := by
      by_contra hzero
      have hempty : seats = ∅ := by
        ext i
        have hi : i = 0 := Subsingleton.elim _ _
        simp [hi, hzero]
      exact rowsNonempty (hempty ▸ hq)
    have hnot : (0 : Fin 1) ∉ e.Q := by
      have hw : (SimplexFG.Window.derive rowsE rowsCfg 2 rowsD).W =
          [⟨1, .genesis, ∅⟩, ⟨2, rowsU, ∅⟩] := by decide +kernel
      change e ∈ (SimplexFG.Window.derive rowsE rowsCfg 2 rowsD).W at he
      rw [hw] at he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp
    obtain hb | ⟨row, hr, hi, hf⟩ := hs 0 hzero
    · exact (hnot hb).elim
    · have heq : row = rowsSigned sign := List.mem_singleton.mp hr
      exact ⟨row, hr, hi, heq ▸ rfl, hf⟩

private theorem rowsTerminal :
    ∃ rows : Fin 1 → Row (Fin 1), rows 0 = rowsSigned false ∧
      ValidForParent rowsEnv (rowsRun false) (rowsI false) rowsParent rowsValid 6
        (rowsErase (rowsX false)) (rows 0) ∧
      FinalityCoveredByChild_W rowsE rowsCfg 2 (rowsX false) rowsU 2 := by
  obtain ⟨rows, fresh, _⟩ := rowsFreshProduced
  have h0 : rows 0 = rowsSigned false := by
    obtain ⟨j, _, ha, _⟩ := fresh.2.2 0 (by decide)
    exact rowsAllEmitted false j (rows 0) ha.2.2
  have hrows : ∀ i, rows i = rowsSigned false := fun i => Subsingleton.elim i 0 ▸ h0
  have result := terminalCarriage_W_of_tRowsSelect (rowsR false) (rowsS false) rowsT
    rowsEnv (rowsRun false) (rowsI false) (rowsWire false) rowsE rowsCfg 2
    (rowsCarrier false) rowsChain (rowsPool false) rowsParent rowsValid
    (rowsSelected false) rowsNonempty (by decide) (by intro a i _; exact ⟨a, rfl⟩)
    (rowsOccurrence false) (rowsO false)
    (KitFG.Window.windowHeightLaws rowsE rowsCfg 2 (by decide)) rfl
    (fun _ _ B => (((rowsO false).height B).h, ((rowsO false).height B).T_h.root))
    (by intros; rfl) (by intros; rfl) (fun _ => true) 1 0 2 rowsD rowsU (rowsX false)
    { schedule := rowsSchedule false
      fault_weight := rowsFaultFree false
      deltaF := by decide
      carrier := ⟨[rowsSigned false], rowsCarrierProduced false, rfl⟩
      parent := ⟨(), rowsParentRead false, rfl⟩
      path := preceq_refl _
      freshHeight := by decide +kernel
      retainedOrCovered := Or.inl rowsRetained
      horizon := by decide +kernel
      seats := {0}
      rows := rows
      fresh := fresh
      heightEntry := by intro i _; rw [hrows i]; decide +kernel
      receipt := by
        intro i _
        rw [hrows i]
        exact ⟨Or.inl (List.mem_singleton_self _),
          ⟨(), rowsParentRead false, Or.inl (List.mem_singleton_self _)⟩⟩ }
    rowsParentValid
  have hn : ¬ KitFG.Window.CoveredW rowsE rowsCfg 2 rowsD 2 rowsU := by
    rw [KitFG.Window.CoveredW_def]
    decide +kernel
  rcases result with hc | ⟨hall, hcarry⟩
  · exact (hn hc).elim
  · exact ⟨rows, h0, (hall 0 (Finset.mem_singleton_self 0)).1, hcarry⟩

-- The earlier-row cap at the next action round, applied to the emitted row.
private theorem rowsEarlierHeight (sign : Bool) :
    historyRowHeight (rowsS sign) (rowsWire sign) (rowsSigned sign) = some 3 ∧ 3 < 4 := by
  have hh : historyRowHeight (rowsS sign) (rowsWire sign) (rowsSigned sign) = some 3 := by
    cases sign <;> rfl
  have cap := rowsPrem_earlier_height (S := rowsS sign) (D := rowsWire sign)
    (E := rowsEnv) (rho := rowsRun sign) rowsTiming 1 4 (by
      intro j x r a h t ha hah hy _
      have he := rowsAllEmitted sign j a ha.2.2
      subst a
      rw [hh] at hah
      cases hah
      omega)
  exact ⟨hh, cap 0 () 0 (rowsSigned sign) 3 (by decide) (rowsEmitted sign) hh⟩

#print axioms rowsFreshInspected
#print axioms rowsFreshCarried
#print axioms rowsBitArms
#print axioms rowsPrunedInspected
#print axioms rowsCapacityRequired
#print axioms rowsSignedIdentityRequired
#print axioms rowsWrongFinalityKey
#print axioms rowsBudgetGuards
#print axioms rowsTwoLabels
#print axioms rowsHeadInspected
#print axioms rowsBatchInspected
#print axioms rowsTerminal
#print axioms rowsEarlierHeight

#print axioms rowsSourceInspected
#print axioms rowsBothSigns
end AvailableChain.FGCompose.Tests.P0d7a4
end
