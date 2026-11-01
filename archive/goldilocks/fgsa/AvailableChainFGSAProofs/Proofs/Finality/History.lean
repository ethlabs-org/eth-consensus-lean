module
public import AvailableChainFGSAProofs.Proofs.Shared.ReceiptFacts
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyClient
public import AvailableChainFGSAProofs.Proofs.Finality.Height
public import AvailableChainFGSA.Proofs.StoreLaws
public import AvailableChainFGCompose.Proofs.Finality.History

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- Assembly supplies this raw origin from execution validity (B28).
variable (horigin : ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
    HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
      ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)

omit [Fintype V] in
/-- DC: INTENTIONAL: membership uses the definition's classical decision procedure. -/
private theorem khistory_honestSeats_mem (i : Fin p.n) :
    i ∈ honestSeats p c rho ↔ rho.seatOf (.base .fg) i ∈ rho.honest := by
  rw [honestSeats_def p c rho]
  simpa only [Finset.mem_univ, true_and] using
    (@Finset.mem_filter (Fin p.n) (fun k => rho.seatOf (.base .fg) k ∈ rho.honest)
      (fun k => Classical.propDecidable (rho.seatOf (.base .fg) k ∈ rho.honest))
      Finset.univ i)

/-- FINAL 22:948–958. Linked unit-weight seats bound the faulty weight.
DC: INTENTIONAL: FG-SA uses linked seats. -/
private theorem khistory_faulty_weight (base : BaseSet p c E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) :
    p.E.weightOf (Finset.univ \ honestSeats p c rho) < p.E.q := by
  classical
  have hsub : (Finset.univ \ honestSeats p c rho).image (rho.seatOf (.base .fg)) ⊆
      Gen.V2.Duty.faulty rho := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    have hn := (Finset.mem_sdiff.mp hi).2
    exact fun hh => hn ((khistory_honestSeats_mem p c rho i).mpr hh)
  have hinj : Function.Injective (fun i : Fin p.n => rho.seatOf (.base .fg) i) :=
    (base.linked.toCStar (.base .fg) trivial).1
  have hc : (Finset.univ \ honestSeats p c rho).card ≤
      (Gen.V2.Duty.faulty rho).card :=
    (Finset.card_image_of_injective _ hinj).symm.trans_le (Finset.card_le_card hsub)
  have hw : p.E.weightOf (Finset.univ \ honestSeats p c rho) =
      (Finset.univ \ honestSeats p c rho).card := by
    change (∑ _ ∈ Finset.univ \ honestSeats p c rho, (1 : Nat)) = _
    simp
  have hq : p.E.q = Gen.Pure.qF p.n :=
    (toWeights_q p.E).symm.trans (unit_toWeights_q p.n)
  rw [hw, hq]
  exact hc.trans_lt hQ.lt

omit [Fintype V] in
/-- FINAL 22:948–958. A seat outside the faulty set is honest.
DC: INTENTIONAL: FG-SA uses linked seats. -/
private theorem khistory_honest_seat (u : Row (Fin p.n))
    (hf : u.signer ∉ Finset.univ \ honestSeats p c rho) :
    rho.seatOf (.base .fg) u.signer ∈ rho.honest := by
  classical
  have hm : u.signer ∈ honestSeats p c rho := by
    by_contra hn
    exact hf (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩)
  exact (khistory_honestSeats_mem p c rho u.signer).mp hm

/-- FINAL 22:954–956. Decode the exact signed wire payload.
DC: INTENTIONAL: FG-SA uses seat-authenticated wires. -/
private theorem khistory_decode {a : RowWire p.n} {u : Row (Fin p.n)}
    (ha : a.toRow? = some u) :
    a = ⟨.seat .fg u.signer, .vote ⟨u.height_pair, u.finality_pair⟩⟩ := by
  rcases a with ⟨auth, ⟨⟨ah, af⟩⟩⟩
  cases auth with
  | none => cases ha
  | proposer s => cases ha
  | seat label k =>
    cases label with
    | head s => cases ha
    | fg =>
      have he : (⟨k, ah, af⟩ : Row (Fin p.n)) = u := Option.some.inj ha
      subst u
      rfl

section

private abbrev d7a_Old := FGSA.Window.State
private abbrev d7a_New := SimplexFG.Window.State

private def d7a_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def d7a_toWindow {V : Type} (w : d7a_Old V) : d7a_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map d7a_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem d7a_entry_eq {V : Type} (e : FGSA.Window.Entry V) :
    d7a_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem d7a_state_eq {V : Type} (w : d7a_Old V) :
    d7a_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map d7a_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem d7a_entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (d7a_toEntry e).j = e.j ∧ (d7a_toEntry e).X = e.X ∧ (d7a_toEntry e).Q
      = e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem d7a_state_fields {V : Type} (w : d7a_Old V) :
    (d7a_toWindow w).L = w.L ∧ (d7a_toWindow w).s = w.s ∧
    (d7a_toWindow w).h = w.h ∧ (d7a_toWindow w).T_h = w.T_h ∧
    (d7a_toWindow w).target_participation = w.target_participation ∧
    (d7a_toWindow w).progress = w.progress ∧ (d7a_toWindow w).W = w.W.map
      d7a_toEntry ∧
    (d7a_toWindow w).J = w.J ∧ (d7a_toWindow w).h_j = w.h_j ∧
    (d7a_toWindow w).F = w.F ∧ (d7a_toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem d7a_initial_eq {V : Type} :
    d7a_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem d7a_foldRow_eq (w : d7a_Old V) (a : Row V) :
    d7a_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (d7a_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map d7a_toEntry =
      (w.W.map d7a_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [d7a_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, d7a_state_eq] using
        congrArg (fun es => ({ d7a_toWindow w with W := es } : d7a_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [d7a_state_eq] <;> rw [bits] <;> simp_all [d7a_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem d7a_rows_eq (rs : List (Row V)) (w : d7a_Old V) :
    d7a_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (d7a_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, d7a_foldRow_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem d7a_advance_eq (w : d7a_Old V) :
    d7a_toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (d7a_toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem d7a_greatest_eq (E : Electorate V) (w : d7a_Old V) :
    (FGSA.Window.greatestReady E w).map d7a_toEntry =
      SimplexFG.Window.greatestReady E (d7a_toWindow w) := by
  classical
  let oldStep := fun (best : Option (FGSA.Window.Entry V)) e =>
    if w.h_F < e.j ∧ E.q ≤ E.weightOf e.Q then
      best.elim (some e) (fun old => if old.j < e.j then some e else best)
    else best
  let newStep := fun (best : Option (SimplexFG.Window.Entry V)) e =>
    if w.h_F < e.j ∧ E.q ≤ E.weightOf e.Q then
      best.elim (some e) (fun old => if old.j < e.j then some e else best)
    else best
  have step (best) (e) :
      (oldStep best e).map d7a_toEntry = newStep (best.map d7a_toEntry)
      (d7a_toEntry e) := by
    dsimp [oldStep, newStep, d7a_entry_eq]
    split_ifs <;> cases best <;> simp_all [d7a_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map d7a_toEntry =
        (es.map d7a_toEntry).foldl newStep (best.map d7a_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (d7a_toWindow w) =
      (w.W.map d7a_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

omit [DecidableEq V] [RowCodec V] in
private theorem d7a_finalize_eq (E : Electorate V) (w : d7a_Old V) :
    d7a_toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (d7a_toWindow w) := by
  rw [FGSA.Window.finalizeWindow_def, SimplexFG.Window.finalizeWindow_def]
  rw [← d7a_greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [d7a_state_eq, d7a_entry_eq, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] [Fintype V] in
/-- Appending the new empty entry and dropping old entries preserve conversion. -/
private theorem d7a_append_eviction_eq (es : List (FGSA.Window.Entry V))
    (j : Height) (X : FGBlock V) (K : Nat) :
    ((es ++ [FGSA.Window.Entry.mk j X ∅]).drop
      ((es ++ [FGSA.Window.Entry.mk j X ∅]).length - K)).map d7a_toEntry =
      (es.map d7a_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).drop
        ((es.map d7a_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).length - K) := by
  simp [List.map_drop, d7a_entry_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem d7a_events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w :
      d7a_Old V) :
    d7a_toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (d7a_toWindow w) := by
  rw [FGSA.Window.process_height_events_def, SimplexFG.Window.process_height_events_def]
  rw [← d7a_finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change d7a_toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (d7a_toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height_def, SimplexFG.Window.advance_height_def,
      d7a_state_eq, d7a_entry_eq, List.map_drop]

private theorem d7a_transition_eq (p : Params) (K : Nat) (w : d7a_Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    d7a_toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (d7a_toWindow w) B rs := by
  rw [FGSA.Window.transition_def, d7a_events_eq, SimplexFG.Window.transition_def]
  have h := d7a_rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { d7a_toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B }
      = _
  rw [h]
  rfl

private theorem d7a_foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) d7a_toWindow where
  initial := d7a_initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := d7a_transition_eq p K

private theorem d7a_derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    d7a_toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (d7a_foldMap p K).fold_eq B

end

private def d7a_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private def d7a_signer (a : RowWire p.n) : Option (Fin p.n) := match a.auth with
  | .seat .fg i => some i
  | _ => none

private def d7a_wire : FGCompose.FGHistoryWireReads (fgsaSafetyReads p c) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer := d7a_signer p
  decode_height a u ha := by
    rw [fgsaSafetyReads_def] at ha
    rw [khistory_decode p ha]
    rfl
  decode_finality a u ha := by
    rw [fgsaSafetyReads_def] at ha
    rw [khistory_decode p ha]
    rfl
  decode_signer a u ha := by
    rw [fgsaSafetyReads_def] at ha
    rw [khistory_decode p ha]
    rfl

omit [Fintype V] in
private theorem d7a_row_eq (j r : Nat) (x : V) (a : RowWire p.n) :
    FGCompose.HonestRowAt (fgsaSafetyReads p c) E rho (d7a_timing p) j x r a =
      HonestRowAt p c E rho j x r a := by rw [fgsaSafetyReads_def]; rfl

omit [Fintype V] in
private theorem d7a_held_eq (i : Nat) (x : V) (B : FGBlock (Fin p.n)) :
    FGCompose.HeldAt (fgsaCoreReads p c) E rho i x B = HeldAt p c E rho i x B := by
  rw [fgsaCoreReads_def]
  rfl

private theorem d7a_chain_eq (B : FGBlock (Fin p.n)) (cut : Time) :
    FGCompose.ChainRowsBefore (fgsaCoreReads p c) E rho B cut =
      ChainRowsBefore p c E rho B cut := by rw [fgsaCoreReads_def]; rfl

omit [Fintype V] in
private theorem d7a_faulty_eq :
    FGCompose.historyFaulty (fgsaSafetyReads p c) rho =
      Finset.univ \ honestSeats p c rho := by
  classical
  rw [fgsaSafetyReads_def]
  delta FGCompose.historyFaulty FGCompose.safetyHolder
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
    khistory_honestSeats_mem]
  rfl

private theorem d7a_empty : ¬ p.E.IsQuorum ∅ := by
  have hn := p.nPos
  dsimp only [Params.E, Electorate.IsQuorum, Electorate.q, Electorate.totalWeight,
    Electorate.weightOf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Finset.card_empty]
  omega

private theorem d7a_height_eq :
    heightView p = KitFG.Window.certificateHeight p.E p.cfg p.K_W := by
  funext B
  change KitFG.Window.projectHeight (d7a_toWindow (FGSA.Window.derive p p.K_W B)) = _
  rw [d7a_derive_eq, KitFG.Window.certificateHeight_def]

private theorem d7a_finality_eq :
    finalityView p = KitFG.Window.certificateFinality p.E p.cfg p.K_W := by
  funext B
  change KitFG.Window.projectFinality (d7a_toWindow (FGSA.Window.derive p p.K_W B)) = _
  rw [d7a_derive_eq, KitFG.Window.certificateFinality_def]

private theorem d7a_retained_eq (B U : FGBlock (Fin p.n)) (y : Nat) :
    KitFG.Window.RetainedW p.E p.cfg p.K_W B y U = Window.RetainedW p B y U := by
  apply propext
  unfold KitFG.Window.RetainedW
  rw [← d7a_derive_eq p p.K_W B, Window.RetainedW_def]
  change (∃ e ∈ (Window.derive p p.K_W B).W.map d7a_toEntry, e.j = y ∧ e.X = U) ↔ _
  simp only [List.mem_map]
  constructor
  · rintro ⟨e, ⟨d, hd, rfl⟩, hey, heU⟩
    exact ⟨d, hd, hey, heU⟩
  · rintro ⟨d, hd, hdy, hdU⟩
    exact ⟨d7a_toEntry d, ⟨d, hd, rfl⟩, hdy, hdU⟩

private theorem d7a_target : FGCompose.TargetJustification p.E (heightView p) := by
  intro y U X hX hU hpath hcover hnomix
  exact fgsa_justifyAt p y U X hX hU hpath hcover hnomix

omit [Fintype V] in
include horigin in
private theorem d7a_origin : FGCompose.RawHistoryOrigin (fgsaCoreReads p c)
    (fgsaSafetyReads p c) E rho (d7a_timing p) (d7a_wire p c) := by
  intro i x B hh u hu
  rw [d7a_held_eq] at hh
  obtain ⟨a, r, ha, har, k, o, t, hki, hk, he⟩ := horigin i x B hh u hu
  refine ⟨a, r, ?_, ?_, k, o, t, hki, hk, ?_⟩
  · rw [fgsaSafetyReads_def]
    exact ha
  · change d7a_signer p a = some u.signer
    rw [khistory_decode p ha]
    rfl
  · intro z hz hhonest
    obtain ⟨seat, hseat, hholder⟩ := hz
    have hseat' : a.auth = .seat .fg seat := by
      change d7a_signer p a = some seat at hseat
      rw [khistory_decode p ha] at hseat ⊢
      have eq := Option.some.inj hseat
      rw [eq]
    have hholder' : rho.seatOf (.base .fg) seat = z := by
      change FGCompose.safetyHolder (fgsaSafetyReads p c) rho seat = z at hholder
      delta FGCompose.safetyHolder at hholder
      rw [fgsaSafetyReads_def] at hholder
      exact hholder
    obtain ⟨⟨j, hji, hj⟩, hrt⟩ := he z ⟨seat, hseat', hholder'⟩ hhonest
    exact ⟨⟨j, hji, (d7a_row_eq p c E rho j r z a).mpr hj⟩, hrt⟩

private def d7a_pre (q y : Nat) (U X : FGBlock (Fin p.n))
    (h : PreBatchPrem p c E rho q y U X) :
    FGCompose.PreBatchPrem (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho
      (d7a_timing p) (d7a_wire p c) p.E (heightView p) q y U X where
  schedule := h.base.valid.toScheduleWellFormed
  fault_weight := by rw [d7a_faulty_eq]; exact khistory_faulty_weight p c E rho h.base h.faultQ
  entry := h.entry
  path := h.path
  cut := h.cut
  early := h.early
  rows := (d7a_chain_eq p c E rho X.parent h.cut).mpr h.rows
  noRow := by
    intro j x r a H t hj ha hy ht
    exact h.noRow j x r a H t ((d7a_row_eq p c E rho j r x a).mp hj) ha hy ht

private def d7a_fresh (q y : Nat) (X : FGBlock (Fin p.n))
    (h : FreshPrem p c E rho q y X) :
    FGCompose.FreshPrem (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho
      (d7a_timing p) (d7a_wire p c) p.E q y X where
  schedule := h.base.valid.toScheduleWellFormed
  fault_weight := by rw [d7a_faulty_eq]; exact khistory_faulty_weight p c E rho h.base h.faultQ
  cut := h.cut
  early := h.early
  rows := (d7a_chain_eq p c E rho X h.cut).mpr h.rows
  noNextRow := by
    intro j x r a H t hj ha hy ht
    exact h.noNextRow j x r a H t ((d7a_row_eq p c E rho j r x a).mp hj) ha hy ht
  noFinRow := by
    intro j x r a H t hj ha hy ht
    exact h.noFinRow j x r a H t ((d7a_row_eq p c E rho j r x a).mp hj) ha hy ht

include horigin in
/-- FINAL 22:1771–1780. No honest height-y row precedes the first action.
DC: CarrierTimeoutGate.lean:121; FG-SA uses a raw parent-chain cut. -/
theorem noMixedPreBatchParent (q y : Nat) (U X : FGBlock (Fin p.n))
    (h : PreBatchPrem p c E rho q y U X) : NoMixedOnPath p X y := by
  exact FGCompose.noMixedPreBatchParent (R := fgsaCoreReads p c)
    (S := fgsaSafetyReads p c) (E := E)
    (rho := rho) (T := d7a_timing p) (D := d7a_wire p c) (Ef := p.E)
    (H := heightView p)
    (cfg := p.cfg) (hb := heightView_bridge p) (horigin := d7a_origin p c E rho horigin)
    q y U X (d7a_pre p c E rho q y U X h)

include horigin in
/-- FINAL 22:945–958,1218–1223. Fresh raw history fixes the endpoint and retains its W key.
DC: W4FKChainJustification.lean:185; FG-SA also proves the strict W finality bound. -/
theorem justifyFresh_W (q y : Nat) (U X : FGBlock (Fin p.n)) (hX : X ≠ .genesis)
    (hentry : EntryAt p U y) (hpath : FGBlock.Preceq U X.parent)
    (hcover : (heightView p X.parent).h = y → CoveredByChild p .target X U y)
    (hnomix : NoMixedOnPath p X y) (h : FreshPrem p c E rho q y X) :
    (heightView p X).h = y + 1 ∧ (heightView p X).J = U ∧
      (heightView p X).h_j = y ∧ (Window.derive p p.K_W X).h_F < y ∧
      Window.RetainedW p X y U := by
  have result := FGCompose.justifyFresh_W (R := fgsaCoreReads p c)
    (S := fgsaSafetyReads p c) (E := E)
    (rho := rho) (T := d7a_timing p) (D := d7a_wire p c) (Ef := p.E)
    (H := heightView p)
    (cfg := p.cfg) (f := finalityView p) (hb := heightView_bridge p)
    (hc := fgCertificateLaws p) (horigin := d7a_origin p c E rho horigin)
    p.K_W (d7a_empty p) p.kWLarge (d7a_height_eq p) (d7a_finality_eq p) (d7a_target p)
    q y U X hX hentry hpath hcover hnomix (d7a_fresh p c E rho q y X h)
  rw [d7a_retained_eq] at result
  exact result

include horigin in
/-- FINAL 22:923–938. Strict raw history caps a held block before the cut.
DC: INTENTIONAL: a delivery witness makes the event cut strict. -/
theorem raw_causal_cap_before (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) (m : Nat) (cut : Time)
    (hrows : ∀ j z r a h t, HonestRowAt p c E rho j z r a →
      rowHeight a = some h → eventTime rho j = some t → t < cut → h ≤ m)
    (i : Nat) (x : V) (B : FGBlock (Fin p.n))
    (hcut : i ≤ V2.D.Run.idxBefore rho cut) (hheld : HeldAt p c E rho i x B) :
    (heightView p B).h ≤ m + 1 := by
  apply FGCompose.raw_causal_cap_before (R := fgsaCoreReads p c)
    (S := fgsaSafetyReads p c) (E := E)
    (rho := rho) (T := d7a_timing p) (D := d7a_wire p c) (Ef := p.E)
    (H := heightView p)
    (f := finalityView p) (hc := fgCertificateLaws p)
    (horigin := d7a_origin p c E rho horigin) base.valid.toScheduleWellFormed
    (by rw [d7a_faulty_eq]; exact khistory_faulty_weight p c E rho base faultQ) m cut _ i x B hcut
    ((d7a_held_eq p c E rho i x B).mpr hheld)
  intro j z r a H t hj ha ht hearly
  exact hrows j z r a H t ((d7a_row_eq p c E rho j r z a).mp hj) ha ht hearly

include horigin in
/-- FINAL 22:923–938. The tick read precedes every delivery at the same time.
DC: INTENTIONAL: event phases give a strict cut across different nodes' ticks. -/
theorem raw_causal_cap_at_tick (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) (m : Nat) (cut : Time)
    (hrows : ∀ j z r a h t, HonestRowAt p c E rho j z r a →
      rowHeight a = some h → eventTime rho j = some t → t < cut → h ≤ m)
    (i : Nat) (x : V) (B : FGBlock (Fin p.n)) (v : V)
    (htick : rho.events[i]? = some (.tick v cut)) (hheld : HeldAt p c E rho i x B) :
    (heightView p B).h ≤ m + 1 := by
  apply FGCompose.raw_causal_cap_at_tick (R := fgsaCoreReads p c)
    (S := fgsaSafetyReads p c) (E := E)
    (rho := rho) (T := d7a_timing p) (D := d7a_wire p c) (Ef := p.E)
    (H := heightView p)
    (f := finalityView p) (hc := fgCertificateLaws p)
    (horigin := d7a_origin p c E rho horigin) base.valid.toScheduleWellFormed
    (by rw [d7a_faulty_eq]; exact khistory_faulty_weight p c E rho base faultQ)
    m cut _ i x B v htick
    ((d7a_held_eq p c E rho i x B).mpr hheld)
  intro j z r a H t hj ha ht hearly
  exact hrows j z r a H t ((d7a_row_eq p c E rho j r z a).mp hj) ha ht hearly

include horigin in
/-- FINAL 22:923–944,1188–1208. Include action q rows up to the strict next-action cut.
DC: INTENTIONAL: the current-action bound is explicit and has no source circularity. -/
theorem raw_causal_cap_through_action (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) (q m : Nat)
    (hpre : ∀ j z r a h t, HonestRowAt p c E rho j z r a →
      rowHeight a = some h → eventTime rho j = some t → t < p.actionTime q → h ≤ m)
    (haction : ∀ j z a h, HonestRowAt p c E rho j z q a → rowHeight a = some h → h ≤ m)
    (i : Nat) (x : V) (B : FGBlock (Fin p.n))
    (hcut : i ≤ V2.D.Run.idxBefore rho (p.actionTime (q + 1)))
    (hheld : HeldAt p c E rho i x B) : (heightView p B).h ≤ m + 1 := by
  apply FGCompose.raw_causal_cap_through_action (R := fgsaCoreReads p c)
    (S := fgsaSafetyReads p c) (E := E)
    (rho := rho) (T := d7a_timing p) (D := d7a_wire p c) (Ef := p.E)
    (H := heightView p)
    (f := finalityView p) (hc := fgCertificateLaws p)
    (horigin := d7a_origin p c E rho horigin) base.valid.toScheduleWellFormed
    (by rw [d7a_faulty_eq]; exact khistory_faulty_weight p c E rho base faultQ)
    (receipt_actionTime_strictMono p) q m _ _ i x B hcut
    ((d7a_held_eq p c E rho i x B).mpr hheld)
  · intro j z r a H t hj ha ht hearly
    exact hpre j z r a H t ((d7a_row_eq p c E rho j r z a).mp hj) ha ht hearly
  · intro j z a H hj ha
    exact haction j z a H ((d7a_row_eq p c E rho j q z a).mp hj) ha

#print axioms d7a_foldMap
#print axioms d7a_height_eq
#print axioms d7a_finality_eq
#print axioms d7a_retained_eq
#print axioms d7a_wire
#print axioms d7a_origin
#print axioms d7a_pre
#print axioms d7a_fresh
#print axioms d7a_target

end AvailableChain.FGSA.Run
end
