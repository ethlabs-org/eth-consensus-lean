module
public import AvailableChainFGSAProofs.Proofs.Shared.FGCompose
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainFGSAClaims.Statements.Phases
public import AvailableChainFGCompose.Proofs.Finality.Accept

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

section

private abbrev d7a5a_w_Old := FGSA.Window.State
private abbrev d7a5a_w_New := SimplexFG.Window.State

private def d7a5a_w_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def d7a5a_w_toWindow {V : Type} (w : d7a5a_w_Old V) : d7a5a_w_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map d7a5a_w_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem d7a5a_w_entry_eq {V : Type} (e : FGSA.Window.Entry V) :
    d7a5a_w_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem d7a5a_w_state_eq {V : Type} (w : d7a5a_w_Old V) :
    d7a5a_w_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map d7a5a_w_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem d7a5a_w_initial_eq {V : Type} :
    d7a5a_w_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem d7a5a_w_foldRow_eq (w : d7a5a_w_Old V) (a : Row V) :
    d7a5a_w_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (d7a5a_w_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map d7a5a_w_toEntry =
      (w.W.map d7a5a_w_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [d7a5a_w_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, d7a5a_w_state_eq] using
        congrArg (fun es => ({ d7a5a_w_toWindow w with W := es } : d7a5a_w_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [d7a5a_w_state_eq] <;> rw [bits] <;> simp_all [d7a5a_w_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem d7a5a_w_rows_eq (rs : List (Row V)) (w : d7a5a_w_Old V) :
    d7a5a_w_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (d7a5a_w_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, d7a5a_w_foldRow_eq]

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem d7a5a_w_greatest_eq (E : Electorate V) (w : d7a5a_w_Old V) :
    (FGSA.Window.greatestReady E w).map d7a5a_w_toEntry =
      SimplexFG.Window.greatestReady E (d7a5a_w_toWindow w) := by
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
      (oldStep best e).map d7a5a_w_toEntry = newStep (best.map d7a5a_w_toEntry)
      (d7a5a_w_toEntry e) := by
    dsimp [oldStep, newStep, d7a5a_w_entry_eq]
    split_ifs <;> cases best <;> simp_all [d7a5a_w_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map d7a5a_w_toEntry =
        (es.map d7a5a_w_toEntry).foldl newStep (best.map d7a5a_w_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (d7a5a_w_toWindow w) =
      (w.W.map d7a5a_w_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

omit [DecidableEq V] [RowCodec V] in
private theorem d7a5a_w_finalize_eq (E : Electorate V) (w : d7a5a_w_Old V) :
    d7a5a_w_toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (d7a5a_w_toWindow w) := by
  rw [FGSA.Window.finalizeWindow_def, SimplexFG.Window.finalizeWindow_def]
  rw [← d7a5a_w_greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [d7a5a_w_state_eq, d7a5a_w_entry_eq, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] in
private theorem d7a5a_w_events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w :
      d7a5a_w_Old V) :
    d7a5a_w_toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (d7a5a_w_toWindow w) := by
  rw [FGSA.Window.process_height_events_def, SimplexFG.Window.process_height_events_def]
  rw [← d7a5a_w_finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change d7a5a_w_toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (d7a5a_w_toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height_def, SimplexFG.Window.advance_height_def,
      d7a5a_w_state_eq, d7a5a_w_entry_eq, List.map_drop]

private theorem d7a5a_w_transition_eq (p : Params) (K : Nat) (w : d7a5a_w_Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    d7a5a_w_toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (d7a5a_w_toWindow w) B rs := by
  rw [FGSA.Window.transition_def, d7a5a_w_events_eq, SimplexFG.Window.transition_def]
  have h := d7a5a_w_rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { d7a5a_w_toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B }
      = _
  rw [h]
  rfl

private theorem d7a5a_w_foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) d7a5a_w_toWindow where
  initial := d7a5a_w_initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := d7a5a_w_transition_eq p K

private theorem d7a5a_w_derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    d7a5a_w_toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (d7a5a_w_foldMap p K).fold_eq B

end

variable (p : Params)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
DC: INTENTIONAL window finality projection, using the owner's equations. -/
private theorem accept_finality (W : FGBlock (Fin p.n)) :
    (finalityView p W).F = (Window.derive p p.K_W W).F := by
  simp only [finalityView_def, Window.certificateFinality_def, Window.projectFinality_def]

private theorem d7a5a_w_update_eq (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    Window.update_finality p p.K_W st B =
      SimplexFG.Window.update_finality p.E p.cfg p.K_W st B := by
  have hv : ∀ st : SimplexFG.Store (Fin p.n),
      Window.acceptViable p p.K_W st = SimplexFG.Window.acceptViable p.E p.cfg p.K_W st := by
    intro st
    simp only [Window.acceptViable_def, SimplexFG.Window.acceptViable_def, ← d7a5a_w_derive_eq,
      d7a5a_w_state_eq]
  simp only [Window.update_finality_def, SimplexFG.Window.update_finality_def,
    ← d7a5a_w_derive_eq, d7a5a_w_state_eq, hv]

private theorem d7a5a_w_height_eq :
    heightView p = KitFG.Window.certificateHeight p.E p.cfg p.K_W := by
  funext B
  change KitFG.Window.projectHeight (d7a5a_w_toWindow (FGSA.Window.derive p p.K_W B)) = _
  rw [d7a5a_w_derive_eq, KitFG.Window.certificateHeight_def]

private theorem d7a5a_w_finality_eq :
    finalityView p = KitFG.Window.certificateFinality p.E p.cfg p.K_W := by
  funext B
  change KitFG.Window.projectFinality (d7a5a_w_toWindow (FGSA.Window.derive p p.K_W B)) = _
  rw [d7a5a_w_derive_eq, KitFG.Window.certificateFinality_def]

private theorem d7a5a_w_nonempty : ¬ p.E.IsQuorum ∅ := by
  have hn := p.nPos
  dsimp only [Params.E, Electorate.IsQuorum, Electorate.q, Electorate.totalWeight,
    Electorate.weightOf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Finset.card_empty]
  omega

variable {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. DC: INTENTIONAL actual receipt and ancestor-closed inserted tree. -/
private theorem accept_ready (i : Nat) (x : V) (W : FGBlock (Fin p.n)) (t : Time)
    (hr : Ready_W p c E rho i x W t) :
    (storeAt p c E rho (i + 1) x).fg =
      Window.update_finality p p.K_W
        { (storeAt p c E rho i x).fg with TF := insert W (storeAt p c E rho i x).fg.TF } W ∧
    (Window.derive p p.K_W W).F ∈ insert W (storeAt p c E rho i x).fg.TF := by
  classical
  rw [Ready_W_def] at hr
  obtain ⟨o, s, N, P, he, heN, hd, hNamed, hp, ha, hw⟩ := hr
  let st := storeAt p c E rho i x
  have hI : CStoreInv p st := cstoreInv_stateBefore E rho i x
  have hPT := ((parentFG_spec st (eraseFG W) P).mp hp).1
  have hparent : W.parent = P := by rw [← hw, fgBlock_parent]
  have hclosed : ∀ B ∈ insert W st.fg.TF, B.parent ∈ insert W st.fg.TF := by
    intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact Finset.mem_insert_of_mem (hparent ▸ hPT)
    · exact Finset.mem_insert_of_mem (hI.fg.closed B hB)
  have hFW : FGBlock.Preceq (Window.derive p p.K_W W).F W := by
    rw [← accept_finality p W]
    exact KitFG.preceq_trans ((fgCertificateLaws p).finalized_preceq_justified W)
      (KitFG.preceq_trans ((fgCertificateLaws p).height.justified_preceq_entry W)
        ((fgCertificateLaws p).height.entry_preceq W))
  refine ⟨?_, KitFG.ancestor_closed_of_parent_closed _ hclosed W
    (Finset.mem_insert_self _ _) _ hFW⟩
  have hstep : storeAt p c E rho (i + 1) x = FGSA.process p st (toWire p o) := by
    change (V2.D.Run.stateBefore E rho (i + 1) x).st = _
    rw [V2.D.Run.stateBefore_succ E rho he]
    simp only [V2.D.World.step, Function.update_self]
    rfl
  rw [hstep]
  change (match (toWire p o).decode with
    | some (.vote r j b) => admitHead p st r j b
    | some (.row _ body) => admitRow p st ⟨(toWire p o).auth, body⟩
    | some (.block r M) => admitBlock p st r M
    | none => st).fg = _
  rw [hd]
  dsimp only
  obtain ⟨pool, hpool, _⟩ := admitBlock_accepted_eq p st s N P hNamed (heN ▸ hp) ha
  rw [hpool]
  dsimp only
  split_ifs
  · rw [fg_on_block_accepts p st s N P (heN ▸ hp) ha, hw]
  · rw [reconcile_fg, fg_on_block_accepts p st s N P (heN ▸ hp) ha, hw]

private def d7a5a_proposalFG := (fgsaCoreReads p c).proposalFG

private theorem d7a5a_reads_eq :
    fgsaCoreReads p c =
      { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
        erase := eraseFG
        source := fun nd => FGSA.fgSource p nd.st
        headVote := fun nd s => FGSA.headVote p nd.st s
        finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
        proposalFG := d7a5a_proposalFG p c } :=
  congrArg (fun reads => { reads with proposalFG := d7a5a_proposalFG p c })
    (fgsaCoreReads_def p c)

private theorem d7a5a_durable : FGCompose.FGFinalityDurableLaws (fgsaCoreReads p c) := by
  rw [d7a5a_reads_eq]
  refine ⟨fun X => fgsa_monoAlong_preceq_F p c X, fun nd t => ?_⟩
  change (acRestart p nd.st t).fg.F = nd.st.fg.F
  rw [acRestart_fg]

private theorem d7a5a_accepts_eq (x : V) (X : FGBlock (Fin p.n)) (d : Time) :
    FGCompose.AcceptsFinalBefore (fgsaCoreReads p c) E rho x X d =
      AcceptsFinalBefore p c E rho x X d := by
  rw [d7a5a_reads_eq]
  rfl

/-- The selected handler equation, in the shared window form. -/
private theorem d7a5a_step :
    FGCompose.AcceptStep_W (fgsaCoreReads p c) E rho p.E p.cfg p.K_W
      (fun i x W t => Ready_W p c E rho i x W t) := by
  rw [d7a5a_reads_eq]
  intro i x W t _hx hr
  obtain ⟨he, hm⟩ := accept_ready p c E rho i x W t hr
  refine ⟨?_, ?_⟩
  · change (storeAt p c E rho (i + 1) x).fg = _
    rw [he, d7a5a_w_update_eq]
    rfl
  · rw [← d7a5a_w_derive_eq]
    exact hm

private theorem d7a5a_inv (i : Nat) (x : V) (_hx : x ∈ rho.honest) :
    KitFG.FGStoreInvariant (KitFG.Window.certificateHeight p.E p.cfg p.K_W)
      (KitFG.Window.certificateFinality p.E p.cfg p.K_W)
      ((fgsaCoreReads p c).core (V2.D.Run.stateBefore E rho i x)).fg := by
  rw [d7a5a_reads_eq, ← d7a5a_w_height_eq, ← d7a5a_w_finality_eq]
  exact (cstoreInv_stateBefore E rho i x).fg

private def d7a5a_delivery [Fintype V] {W U : FGBlock (Fin p.n)} {a₀ d : Time}
    (h : BlockDelivery_W p c E rho W U a₀ d) :
    FGCompose.BlockDelivery_W (fgsaCoreReads p c) E rho
      (fun i x W t => Ready_W p c E rho i x W t) W U a₀ d where
  selected x hx := ⟨(h.selected x hx).index, (h.selected x hx).time⟩
  witness x hx := by
    obtain ⟨h1, h2, h3⟩ := h.witness x hx
    refine ⟨h1, h2, ?_⟩
    rw [d7a5a_reads_eq]
    exact h3

private theorem d7a5a_selected [Fintype V] {W U : FGBlock (Fin p.n)} {a₀ d : Time}
    (h : BlockDelivery_W p c E rho W U a₀ d) (x : V) (hx : x ∈ rho.honest) :
    (d7a5a_delivery p c E rho h).selected x hx =
      ⟨(h.selected x hx).index, (h.selected x hx).time⟩ := rfl

private theorem d7a5a_guards [Fintype V] {W U : FGBlock (Fin p.n)} {a₀ d : Time}
    (h : BlockDelivery_W p c E rho W U a₀ d) (g : AcceptGuards_W p c E rho W U a₀ d h) :
    FGCompose.AcceptGuards_W (fgsaCoreReads p c) E rho p.E p.cfg p.K_W
      (fun i x W t => Ready_W p c E rho i x W t) W U a₀ d (d7a5a_delivery p c E rho h) where
  finCmp x hx := by
    dsimp only
    rw [d7a5a_selected, d7a5a_reads_eq]
    exact g.finCmp x hx
  jPath x hx := by
    dsimp only
    rw [d7a5a_selected, d7a5a_reads_eq, ← d7a5a_w_derive_eq]
    exact g.jPath x hx
  cap x hx := by
    dsimp only
    rw [d7a5a_selected]
    intro hr hc
    have hcap := g.cap x hx hr (by rw [d7a5a_reads_eq] at hc; exact hc)
    rw [receiptInsert_W_def] at hcap
    change max ((fgsaCoreReads p c).core (V2.D.Run.stateBefore E rho _ x)).fg.h_max
      (SimplexFG.Window.derive p.E p.cfg p.K_W W).h ≤
        (SimplexFG.Window.derive p.E p.cfg p.K_W W).h + 1
    rw [d7a5a_reads_eq, ← d7a5a_w_derive_eq]
    exact hcap

private def d7a5a_prem [Fintype V] {W U : FGBlock (Fin p.n)} {a₀ d : Time}
    (h : AcceptPrem_W p c E rho W U a₀ d) :
    FGCompose.AcceptPrem_W (fgsaCoreReads p c) E rho p.E p.cfg p.K_W
      (fun i x W t => Ready_W p c E rho i x W t) W U a₀ d :=
  { schedule := h.base.valid.toScheduleWellFormed
    finalized := by
      rw [← d7a5a_w_derive_eq]
      exact h.finalized
    deliver := d7a5a_delivery p c E rho h.deliver
    guards := d7a5a_guards p c E rho h.deliver h.guards
    horizon := h.horizon }

private theorem d7a5a_fold (y : Nat) (U X : FGBlock (Fin p.n)) (h : PendingFold_W p y U X) :
    FGCompose.PendingFold_W p.E p.cfg p.K_W y U X := by
  obtain ⟨child, e, he, hj, hX, Q, hQ, cover⟩ := h
  refine ⟨child, d7a5a_w_toEntry e, ?_, hj, hX, Q, hQ, ?_⟩
  · rw [← d7a5a_w_derive_eq]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  · intro i hi
    rcases cover i hi with hb | ⟨row, hrow, hn⟩
    · exact Or.inl hb
    · exact Or.inr ⟨row, hrow, (FinRowNames_def p row i y U).mp hn⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
DC-CS/W4FKChainSecondCheckpoint.lean:43 (W4CommonFinalityAtConfirmationPin).
INTENTIONAL: FG-SA uses the selected W receipt and a strict supplied deadline. -/
theorem fgsa_acceptBefore_W : AcceptBefore_W p := by
  rw [AcceptBefore_W_def]
  intro V _ _ In c E rho W K a₀ d h x hx
  rw [← d7a5a_accepts_eq]
  exact FGCompose.acceptBefore_W (fgsaCoreReads p c) E rho p.E p.cfg p.K_W
    (d7a5a_w_nonempty p) p.kWLarge (d7a5a_durable p c)
    (fun i x W t => Ready_W p c E rho i x W t) (d7a5a_step p c E rho)
    (d7a5a_inv p c E rho) W K a₀ d (d7a5a_prem p c E rho h) x hx

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
DC-CS/W4FKChainFinalityWrite.lean:177 followed by acceptance at :43.
INTENTIONAL: the existing adapter uses the same selected receipt and strict deadline.
Conditional on FinalizePrem_W.deliver; not a deadline result. -/
theorem fgsa_finalizePending_W (ΔF : Time) : FinalizePending_W p ΔF := by
  rw [FinalizePending_W_def]
  intro V _ _ In c E rho q y U X _slot h x hx
  rw [← d7a5a_accepts_eq]
  exact FGCompose.finalizePending_W (fgsaCoreReads p c) E rho p.E p.cfg p.K_W
    (d7a5a_w_nonempty p) p.kWLarge (d7a5a_durable p c)
    (fun i x W t => Ready_W p c E rho i x W t) (d7a5a_step p c E rho)
    (d7a5a_inv p c E rho) y U X _ _
    { fold := d7a5a_fold p y U X h.fold
      schedule := h.base.valid.toScheduleWellFormed
      deliver := d7a5a_delivery p c E rho h.deliver
      guards := d7a5a_guards p c E rho h.deliver h.guards
      horizon := h.horizon } x hx

end AvailableChain.FGSA.Run
end
