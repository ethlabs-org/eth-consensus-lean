module
public import AvailableChainFGSARun.Statements.Client
public import AvailableChainFGCompose.Proofs.Healing.PromotionRows
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionCarrier
public import AvailableChainFGSAProofs.Proofs.Healing.Promotion

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

private def p0d3_rows_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private def p0d3_rows_core (p : Params) {In : Type} (c : AppCodec In) :
  FGCompose.FGCoreReads (fgsa p c) p.n (GridCO.State p.n .root) (Wire p.n) (RowWire p.n) :=
  { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
    erase := eraseFG
    source := fun nd => FGSA.fgSource p nd.st
    headVote := fun nd s => FGSA.headVote p nd.st s
    finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
    proposalFG := fun nd o => match (toWire p o).decode with
      | some (.block _ N) => (parentFG nd.st N.erase).map (fun P => fgBlock P N.erase N.rows)
      | some (.vote _ _ _) => none
      | some (.row _ _) => none
      | none => none }
private def p0d3_rows_safety (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGSafetyReads (fgsa p c) p.n (RowWire p.n) where
  proposalErase := safetyProposalErase p
  proposalRows := safetyProposalRows p
  encode := ofRow p
  decode := RowWire.toRow?
  decodeObject := decodeRowObject p
  fgLabel := .base .fg
  fgSeats := Equiv.refl _
  record := Node.record
  inputs := fun nd => fgInputs p nd.st
  enabled := fun t => decide (p.actionTime ((p.slotOf t - 1) / p.R) = t)
  finalizedOut := finalizedOut

omit [Fintype V] in
private theorem p0d3_rows_frame_mem (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {x : V} {r : Nat} {K : FGBlock (Fin p.n)}
    {nd : Node p} (hnd : postClock E rho x (p.actionTime r) = some nd)
    (hK : actionSourceFG p c E rho x r = some (some K)) : K ∈ fullTree p nd.st := by
  rw [actionSourceFG_def, hnd] at hK
  have hs : fgSource p nd.st = some K := Option.some.inj hK
  exact (Finset.mem_filter.mp (pickPair_some_spec _ _ hs).1).1

omit [Fintype V] in
private theorem p0d3_rows_covered_eq (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (r : Nat) (Q : Block) :
    FGCompose.OpeningCovered (p0d3_rows_core p c) (p0d3_rows_safety p c) E rho
      (heightView p) (p0d3_rows_timing p) (fun a => a.payload.height_pair) r Q =
        OpeningCovered p c E rho r Q := by
  apply propext
  constructor
  · intro h x hx
    obtain ⟨K, nd, j, rSent, a, hnd, hK, _, hQ, hr, ha, hn⟩ := h x hx
    exact ⟨K, nd, j, rSent, a, hnd, hK, p0d3_rows_frame_mem E rho hnd hK,
      hQ, hr, ha, hn⟩
  · intro h x hx
    obtain ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ, hr, ha, hn⟩ := h x hx
    have htf : K ∈ nd.st.fg.TF := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
    exact ⟨K, nd, j, rSent, a, hnd, hK, htf, hQ, hr, ha, hn⟩

omit [Fintype V] in
private theorem p0d3_rows_stored_parent_slot (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hv : V2.D.ExecutionValid E rho)
    (i : Nat) (x : V) (W : FGBlock (Fin p.n))
    (hW : W ∈ (storeAt p c E rho i x).fg.TF) (hne : W ≠ .genesis) :
    W.parent.slot < W.slot := by
  have hm := ((cstoreInv_stateBefore E rho i x).baseTree (eraseFG W)).mpr ⟨W, hW, rfl⟩
  obtain ⟨w, hw, hb, j, o, t, _, hd, ho, _⟩ :=
    fgsa_stored_block_origin E rho i x (eraseFG W) hm (by
      intro he; exact hne (eraseFG_eq_genesis.mp he))
  obtain ⟨s, N, rfl, _, _, _⟩ :=
    (metaInv_stateBefore E rho i x).wireTree w hw
  have hQ : N.erase = eraseFG W := Option.some.inj hb
  have hf := hv.wire j x o t hd
  change FGSA.wellFormed p (toWire p o) = true at hf
  rw [ho] at hf
  have hlt : N.erase.parent.slot < N.erase.slot := of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hf).1).1).1).1).2
  rwa [hQ, eraseFG_parent, eraseFG_slot, eraseFG_slot] at hlt

omit [Fintype V] in
private theorem p0d3_rows_stored_ancestor_slot (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hv : V2.D.ExecutionValid E rho)
    (i : Nat) (x : V) {U K : FGBlock (Fin p.n)}
    (hK : K ∈ (storeAt p c E rho i x).fg.TF) (hUK : FGBlock.Preceq U K) :
    U.slot ≤ K.slot := by
  induction K with
  | genesis => obtain rfl := KitFG.preceq_genesis.mp hUK; exact le_rfl
  | node P s root body rows ih =>
      by_cases he : U = .node P s root body rows
      · subst U; exact le_rfl
      · have hUP := KitFG.preceq_parent_of_preceq_node hUK he
        have hP := (cstoreInv_stateBefore E rho i x).fg.closed _ hK
        exact (ih hP hUP).trans
          (p0d3_rows_stored_parent_slot E rho hv i x _ hK (by intro h; cases h)).le

private theorem p0d3_rows_ancestor (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {x : V} {r : Nat} {K U : FGBlock (Fin p.n)}
    (hK : actionSourceFG p c E rho x r = some (some K))
    (hUK : FGBlock.Preceq U K) : U.slot ≤ K.slot := by
  rw [actionSourceFG_def, postClock_def, preTick_def] at hK
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none, reduceCtorEq] at hK
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hK
    have hm := (Finset.mem_filter.mp (pickPair_some_spec _ _ hK).1).1
    have hs := ((KitFG.mem_filteredFromView _ _ _ _).mp hm).1
    change K ∈ (clock p (storeAt p c E rho i x) (p.actionTime r)).fg.TF at hs
    rw [clock_fg] at hs
    exact p0d3_rows_stored_ancestor_slot E rho hrec.base.valid i x hs hUK

omit [Fintype V] in
private theorem p0d3_rows_batch_eq (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (r height : Nat) (Q : Block) (U : FGBlock (Fin p.n)) :
    FGCompose.FixedRows (p0d3_rows_core p c) (p0d3_rows_safety p c) E rho
      (heightView p) (p0d3_rows_timing p) (fun a => a.payload.height_pair) r height Q U =
    (∀ x ∈ rho.honest, ∃ K nd j rSent a,
      postClock E rho x (p.actionTime r) = some nd ∧
      actionSourceFG p c E rho x r = some (some K) ∧ K ∈ fullTree p nd.st ∧
      Block.Preceq Q (eraseFG K) ∧ FGBlock.Preceq U K ∧ K.slot ≤ r * p.R ∧
      (heightView p K).h = height ∧ (heightView p K).T_h = U ∧ rSent ≤ r ∧
      HonestRowAt p c E rho j x rSent a ∧ NamesEntry p .progress a height U) := by
  apply propext
  constructor
  · intro h x hx
    obtain ⟨K, nd, j, rSent, a, hnd, hK, _, hQ, hUK, hs, hh, he, hr, ha, hn⟩ := h x hx
    exact ⟨K, nd, j, rSent, a, hnd, hK, p0d3_rows_frame_mem E rho hnd hK,
      hQ, hUK, hs, hh, he, hr, ha, hn⟩
  · intro h x hx
    obtain ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ, hUK, hs, hh, he, hr, ha, hn⟩ := h x hx
    have htf : K ∈ nd.st.fg.TF := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
    exact ⟨K, nd, j, rSent, a, hnd, hK, htf, hQ, hUK, hs, hh, he, hr, ha, hn⟩

private theorem p0d3_rows_nonempty (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) :
    rho.honest.Nonempty := by
  have hn : Fintype.card V = p.n :=
    (V2.D.CStar.seats_eq (ℓ := .base .fg) hrec.base.linked.toCStar trivial).symm
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  have hf := hrec.fault
  rw [Gen.V2.Duty.faulty_def, he, Finset.sdiff_empty, Finset.card_univ, hn] at hf
  have := p.nPos
  omega


private def p0d3_rows_parent (nd : Node p) (B : Block) := fgBlockOf nd.st B
private def p0d3_rows_height (_nd : Node p) (s : Slot) (B : FGBlock (Fin p.n)) :=
  ((parentFoldState p s B).h, (parentFoldState p s B).T_h.root)
private def p0d3_rows_valid (_nd : Node p) (s : Slot) (B : FGBlock (Fin p.n))
    (a : RowWire p.n) := Window.rowValidW (parentFoldState p s B) a
private def p0d3_rows_window (w : Window.State (Fin p.n)) :
    SimplexFG.Window.State (Fin p.n) :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map (fun e => ⟨e.j, e.X, e.Q⟩), w.J, w.h_j, w.F, w.h_F⟩
private def p0d3_rows_fold (_nd : Node p) (s : Slot) (B : FGBlock (Fin p.n)) :=
  p0d3_rows_window (parentFoldState p s B)

private theorem p0d3_rows_r6 (w : Window.State (Fin p.n)) (a : RowWire p.n) :
    Window.rowValidW w a =
      match a.toRow? with
      | none => false
      | some b => SimplexFG.Window.r6w (p0d3_rows_window w) b := by
  rw [Window.rowValidW_def]
  cases a.toRow? with
  | none => rfl
  | some b =>
    delta p0d3_rows_window
    cases hp : b.height_pair <;> cases hf : b.finality_pair <;>
      simp only [Window.r6w_def, Window.heightMatch_def, Window.staleUseful_def,
      Window.windowMatch_def, SimplexFG.Window.r6w_def, SimplexFG.Window.heightMatch_def,
      SimplexFG.Window.staleUseful_def, SimplexFG.Window.windowMatch_def,
      List.any_map, Function.comp_def, hp, hf]

omit [Fintype V] in
private theorem p0d3_rows_valid_eq (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (s : Slot) (Q : Block) (a : RowWire p.n) :
    FGCompose.ValidForParent E rho (fgsaInterface p c) p0d3_rows_parent
      p0d3_rows_valid s Q a = ValidForParent p c E rho s Q a := by
  apply propext
  constructor
  · rintro ⟨nd, H, hnd, hp, hv⟩
    exact ⟨nd.st, H, congrArg (Option.map Node.st) hnd, hp, hv⟩
  · rintro ⟨st, H, hst, hp, hv⟩
    obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hst
    exact ⟨nd, H, hnd, hp, hv⟩

omit [Fintype V] in
private theorem p0d3_rows_match_eq (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (s : Slot) (Q : Block) (a : RowWire p.n) :
    FGCompose.HeightMatch E rho (fgsaInterface p c)
      (fun a => FGCompose.namedEntry a.payload.height_pair) p0d3_rows_parent
      p0d3_rows_height s Q a = HeightMatch p c E rho s Q a := by
  apply propext
  constructor
  · rintro ⟨nd, H, hnd, hp, hv⟩
    exact ⟨nd.st, H, congrArg (Option.map Node.st) hnd, hp, hv⟩
  · rintro ⟨st, H, hst, hp, hv⟩
    obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hst
    exact ⟨nd, H, hnd, hp, hv⟩

private theorem p0d3_rows_read (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {s : Slot} {X : FGBlock (Fin p.n)}
    (hQ : HonestProposal E rho (fgsaInterface p c) s (eraseFG X)) :
    ∃ nd, FGCompose.proposalStateAt E rho (fgsaInterface p c) s = some nd ∧
      p0d3_rows_parent nd (eraseFG X).parent = some X.parent ∧
      (p0d3_rows_fold nd s X.parent).h = (heightView p X.parent).h ∧
      (p0d3_rows_fold nd s X.parent).T_h = (heightView p X.parent).T_h ∧
      p0d3_rows_height nd s X.parent =
        ((p0d3_rows_fold nd s X.parent).h, (p0d3_rows_fold nd s X.parent).T_h.root) ∧
      ∀ a, p0d3_rows_valid nd s X.parent a =
        match (p0d3_rows_safety p c).decode a with
        | none => false
        | some b => SimplexFG.Window.r6w (p0d3_rows_fold nd s X.parent) b := by
  obtain ⟨Y, he, _, _, st, hst, hlookup⟩ := healing_promotion_carrier E rho hrec hQ
  have hYX : Y = X := eraseFG_injective he
  subst Y
  obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hst
  exact ⟨nd, hnd, hlookup, rfl, rfl, rfl,
    fun a => p0d3_rows_r6 (parentFoldState p s X.parent) a⟩

private theorem promotion_honest_row_decode (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {j r : Nat} {x : V} {a : RowWire p.n} (ha : HonestRowAt p c E rho j x r a) :
    ∃ b, a.toRow? = some b ∧ b.height_pair = a.payload.height_pair := by
  have hawake : E.awake x (p.actionTime r) = true := by
    cases hw : E.awake x (p.actionTime r) with
    | true => rfl
    | false =>
      have hem := ha.2.2
      rw [(V2.D.Run.step_tick_eq E rho ha.2.1).2] at hem
      have hnil := (fgsa_tick_asleep (p := p) (c := c) E rho
        (V2.D.Run.stateBefore E rho j x) x (p.actionTime r) hw).1
      have hem : ofRow p a ∈ ([] : List (Obj p)) := hnil ▸ hem
      exact (List.not_mem_nil hem).elim
  have hv := honest_emit_wellFormed E rho hrec.base.valid.toDeliveryWellFormed
    hrec.base.valid.toScheduleWellFormed j x _ ha.2.1 ha.1 hawake (ofRow p a) ha.2.2
  cases a with
  | mk auth payload =>
    cases auth with
    | none => cases hv
    | proposer s => cases hv
    | seat label i =>
      cases label with
      | head s => cases hv
      | fg => exact ⟨_, rfl, rfl⟩

/-- Blueprint 21:1385–1410; plan §3.2 step 4, same-height branch.
DC: SAME the original progress row matches the current parent entry.
The path and equal height are local branch facts. They do not assert placement
of earlier matching rows. The row's finality pair can have any value. -/
private theorem promotion_same_row (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {s : Slot} {X U : FGBlock (Fin p.n)} {height : Nat}
    (hQ : HonestProposal E rho (fgsaInterface p c) s (eraseFG X)) (hslot : X.slot = s)
    (hentry : EntryAt p U height) (hpath : FGBlock.Preceq U X.parent)
    (hheight : (heightView p X.parent).h = height)
    {j rSent : Nat} {x : V} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j x rSent a) (hn : NamesEntry p .progress a height U) :
    ValidForParent p c E rho X.slot (eraseFG X) a ∧
      HeightMatch p c E rho X.slot (eraseFG X) a := by
  obtain ⟨nd, hread, hparent, hh, ht, hph, hv⟩ := p0d3_rows_read E rho hrec hQ
  have h := FGCompose.p0d3_same_row (p0d3_rows_core p c) (p0d3_rows_safety p c)
    E rho (heightView p) (fgsaInterface p c) (fun a => a.payload.height_pair)
    p0d3_rows_parent p0d3_rows_height p0d3_rows_valid p0d3_rows_fold
    p.E (fgCertificateLaws p).height hslot ⟨hentry.1, hentry.2⟩ hpath hheight
    hread hparent ⟨hh, ht⟩ hph (promotion_honest_row_decode E rho hrec ha) hn
    (by cases hd : (p0d3_rows_safety p c).decode a <;> simpa only [hd] using hv a)
  simp only [p0d3_rows_valid_eq, p0d3_rows_match_eq] at h
  exact h

/-- ROOT-DIGEST W2b. Blueprint 21:1385–1410; plan §3.2 step 4, same-height branch.
DC: SAME source transfer puts the common entry on the new parent path.
The original fixed rows supply both validity fields when the parent has the
starting height. No above-entry occurrence premise is required. -/
theorem healing_promotion_same_rows (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (perm : TPerm p c E rho) {u : Time} {m : Nat}
    {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {r height : Nat} {s : Slot} {Q : Block} {X : FGBlock (Fin p.n)}
    (hentry : OpeningEntry p c E rho r height) (hcovered : OpeningCovered p c E rho r Q)
    (hready : recoveryStart p E ≤ u)
    (hphase : PhaseInterval p c E rho u (SA.proposalTime p.toParams s) m J contested)
    (hu : u ≤ SA.voteTime p.toParams (r * p.R))
    (hgate : p.actionTime r ≤ SA.proposalTime p.toParams s) (hs : r * p.R + 2 ≤ s)
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X)) (hslot : X.slot = s) :
    ∃ U : FGBlock (Fin p.n), EntryAt p U height ∧ U.slot ≤ r * p.R ∧
      FGBlock.Preceq U X.parent ∧
      ∀ x ∈ rho.honest, ∃ K nd j rSent a,
        postClock E rho x (p.actionTime r) = some nd ∧
        actionSourceFG p c E rho x r = some (some K) ∧ K ∈ FGSA.fullTree p nd.st ∧
        Block.Preceq Q (eraseFG K) ∧ FGBlock.Preceq U K ∧ K.slot ≤ r * p.R ∧
        (heightView p K).h = height ∧ (heightView p K).T_h = U ∧
        rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        NamesEntry p .progress a height U ∧
        ((heightView p X.parent).h = height →
          ValidForParent p c E rho X.slot (eraseFG X) a ∧
          HeightMatch p c E rho X.slot (eraseFG X) a) := by
  have parents : ∀ x K, x ∈ rho.honest →
      actionSourceFG p c E rho x r = some (some K) → FGBlock.Preceq K X.parent := by
    intro x K hx hK
    have hp := healing_promotion_source_parent E rho perm hready hphase hu hgate hx hK hs hnew
    rw [eraseFG_parent] at hp
    exact eraseFG_preceq_iff.mp hp
  have h := FGCompose.healing_promotion_same_rows (p0d3_rows_core p c) (p0d3_rows_safety p c) E rho
    (heightView p) (p0d3_rows_timing p) (fgsaInterface p c) (fun a => a.payload.height_pair)
    p0d3_rows_parent p0d3_rows_height p0d3_rows_valid p0d3_rows_fold
    p.E (fgCertificateLaws p).height
    (p0d3_rows_nonempty E rho hrec)
    hentry ((p0d3_rows_covered_eq E rho r Q).mpr hcovered)
    (fun x y K L hx hy hK hL he =>
      rootScope_eq hrec.base.idealization
        (rootScope_entry (rootScope_source hx hK))
        (rootScope_entry (rootScope_source hy hL)) he)
    (fun x K hx hK => healing_source_slot p c E rho hx hK)
    (fun x K A _ hK hAK => p0d3_rows_ancestor E rho hrec hK hAK)
    parents hslot
    (by
      obtain ⟨nd, hread, hparent, hh, ht, hph, hv⟩ := p0d3_rows_read E rho hrec hnew
      refine ⟨nd, hread, hparent, hh, ht, hph, ?_⟩
      intro a
      cases hd : (p0d3_rows_safety p c).decode a <;> simpa only [hd] using hv a)
    (fun j x rSent a ha => promotion_honest_row_decode E rho hrec ha)
  obtain ⟨U, hU, hsU, hUP, rows⟩ := h
  refine ⟨U, hU, hsU, hUP, ?_⟩
  intro x hx
  obtain ⟨K, nd, j, rSent, a, hnd, hK, _, hQ, hUK, hsK, hhK, hKU, hr, ha, hn, hv⟩ :=
    rows x hx
  refine ⟨K, nd, j, rSent, a, hnd, hK, p0d3_rows_frame_mem E rho hnd hK,
    hQ, hUK, hsK, hhK, hKU, hr, ha, hn, ?_⟩
  simp only [p0d3_rows_valid_eq, p0d3_rows_match_eq] at hv
  exact hv

/-- The promotion consumer uses the selected sources at its actual proposal read. -/
theorem healing_promotion_same_rows_on (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
 {u : Time} {m : Nat}
    {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {r height : Nat} {s : Slot} {Q : Block} {X : FGBlock (Fin p.n)}
    (hentry : OpeningEntry p c E rho r height) (hcovered : OpeningCovered p c E rho r Q)
    (_hready : recoveryStart p E ≤ u)
    (_hphase : PhaseInterval p c E rho u (SA.proposalTime p.toParams s) m J contested)
    (_hu : u ≤ SA.voteTime p.toParams (r * p.R))
    (_hgate : p.actionTime r ≤ SA.proposalTime p.toParams s) (_hs : r * p.R + 2 ≤ s)
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X)) (hslot : X.slot = s)
    (hParents : ∀ x ∈ rho.honest, ∀ K,
      actionSourceFG p c E rho x r = some (some K) →
      Block.Preceq (eraseFG K) (eraseFG X).parent) :
    ∃ U : FGBlock (Fin p.n), EntryAt p U height ∧ U.slot ≤ r * p.R ∧
      FGBlock.Preceq U X.parent ∧
      ∀ x ∈ rho.honest, ∃ K nd j rSent a,
        postClock E rho x (p.actionTime r) = some nd ∧
        actionSourceFG p c E rho x r = some (some K) ∧ K ∈ FGSA.fullTree p nd.st ∧
        Block.Preceq Q (eraseFG K) ∧ FGBlock.Preceq U K ∧ K.slot ≤ r * p.R ∧
        (heightView p K).h = height ∧ (heightView p K).T_h = U ∧
        rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        NamesEntry p .progress a height U ∧
        ((heightView p X.parent).h = height →
          ValidForParent p c E rho X.slot (eraseFG X) a ∧
          HeightMatch p c E rho X.slot (eraseFG X) a) := by
  have parents : ∀ x K, x ∈ rho.honest →
      actionSourceFG p c E rho x r = some (some K) → FGBlock.Preceq K X.parent := by
    intro x K hx hK
    have hp := hParents x hx K hK
    rw [eraseFG_parent] at hp
    exact eraseFG_preceq_iff.mp hp
  have h := FGCompose.healing_promotion_same_rows_on
    (p0d3_rows_core p c) (p0d3_rows_safety p c) E rho
    (heightView p) (p0d3_rows_timing p) (fgsaInterface p c) (fun a => a.payload.height_pair)
    p0d3_rows_parent p0d3_rows_height p0d3_rows_valid p0d3_rows_fold
    p.E (fgCertificateLaws p).height
    (p0d3_rows_nonempty E rho hrec)
    hentry ((p0d3_rows_covered_eq E rho r Q).mpr hcovered)
    (fun x y K L hx hy hK hL he =>
      rootScope_eq hrec.base.idealization
        (rootScope_entry (rootScope_source hx hK))
        (rootScope_entry (rootScope_source hy hL)) he)
    (fun x K hx hK => healing_source_slot p c E rho hx hK)
    (fun x K A _ hK hAK => p0d3_rows_ancestor E rho hrec hK hAK)
    parents hslot
    (by
      obtain ⟨nd, hread, hparent, hh, ht, hph, hv⟩ := p0d3_rows_read E rho hrec hnew
      refine ⟨nd, hread, hparent, hh, ht, hph, ?_⟩
      intro a
      cases hd : (p0d3_rows_safety p c).decode a <;> simpa only [hd] using hv a)
    (fun j x rSent a ha => promotion_honest_row_decode E rho hrec ha)
  obtain ⟨U, hU, hUslot, hUP, rows⟩ := h
  refine ⟨U, hU, hUslot, hUP, ?_⟩
  intro x hx
  obtain ⟨K, nd, j, rSent, a, hnd, hK, _, hQ, hUK, hsK, hhK, hKU, hr, ha, hn, hv⟩ :=
    rows x hx
  refine ⟨K, nd, j, rSent, a, hnd, hK, p0d3_rows_frame_mem E rho hnd hK,
    hQ, hUK, hsK, hhK, hKU, hr, ha, hn, ?_⟩
  simp only [p0d3_rows_valid_eq, p0d3_rows_match_eq] at hv
  exact hv

end AvailableChain.FGSA.Run
end
