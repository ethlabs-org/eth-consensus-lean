module
public import AvailableChainFGSAProofs.Proofs.Shared.HeldReceipt
public import AvailableChainFGSAProofs.Proofs.Shared.RowReads
public import AvailableChainFGSAProofs.Proofs.Finality.TailKernel
public import AvailableChainFGSARun.Proofs.Receipts -- shake: keep (receipt API)

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG

/-! ### Window bits along one chain -/

section Bits

variable {α : Type} [DecidableEq α] [RowCodec α]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
One row adds its signer to the entry with its exact finality pair. -/
private def ktailAddBit (a : Row α) (e : Window.Entry α) : Window.Entry α :=
  if a.finality_pair = some ⟨e.j, e.X.root⟩ then { e with Q := insert a.signer e.Q } else e

private theorem ktail_addBit_key (a : Row α) (e : Window.Entry α) :
    (ktailAddBit a e).j = e.j ∧ (ktailAddBit a e).X = e.X := by
  unfold ktailAddBit
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem ktail_addBit_bits (a : Row α) (e : Window.Entry α) (i : α) :
    i ∈ (ktailAddBit a e).Q ↔ i ∈ e.Q ∨
      (a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩) := by
  unfold ktailAddBit
  split_ifs with h <;> simp [h, eq_comm, or_comm]

private theorem ktail_row_fields (w : Window.State α) (a : Row α) :
    (Window.process_row w a).W = w.W.map (ktailAddBit a) ∧
    (Window.process_row w a).h_F = w.h_F ∧ (Window.process_row w a).F = w.F := by
  obtain ⟨i, pair, fp⟩ := a
  cases pair with
  | empty =>
      simp only [Window.process_row_def, NamedHeightPair.matchesEntry]
      exact ⟨rfl, rfl, rfl⟩
  | vote h X t =>
      cases t <;> simp only [Window.process_row_def] <;> split_ifs <;>
        exact ⟨rfl, rfl, rfl⟩

private theorem ktail_fold_fields (rs : List (Row α)) (w : Window.State α) :
    (rs.foldl Window.process_row w).W =
      w.W.map (fun e => rs.foldl (fun e a => ktailAddBit a e) e) ∧
    (rs.foldl Window.process_row w).h_F = w.h_F ∧ (rs.foldl Window.process_row w).F = w.F := by
  induction rs generalizing w with
  | nil => simp
  | cons a rs ih =>
      have h := ktail_row_fields w a
      have t := ih (Window.process_row w a)
      simpa only [List.foldl_cons, t.1, h.1, List.map_map, Function.comp_def,
        t.2.1, t.2.2, h.2.1, h.2.2] using (show True ∧ True ∧ True from by trivial)

private theorem ktail_fold_entry (rs : List (Row α)) (e : Window.Entry α) :
    let d := rs.foldl (fun e a => ktailAddBit a e) e
    d.j = e.j ∧ d.X = e.X ∧
      ∀ i, i ∈ d.Q ↔ i ∈ e.Q ∨ ∃ a ∈ rs,
        a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩ := by
  induction rs generalizing e with
  | nil => simp
  | cons a rs ih =>
      have h := ih (ktailAddBit a e)
      have k := ktail_addBit_key a e
      simp only [List.foldl_cons]
      refine ⟨h.1.trans k.1, h.2.1.trans k.2, ?_⟩
      intro i
      rw [h.2.2, ktail_addBit_bits, k.1, k.2]
      simp only [List.mem_cons, exists_eq_or_imp, or_assoc]

variable [Fintype α]

omit [DecidableEq α] [RowCodec α] in
private theorem ktail_greatest_mem (E : Electorate α) (w : Window.State α)
    (e : Window.Entry α) (he : Window.greatestReady E w = some e) :
    e ∈ w.W ∧ E.IsQuorum e.Q := by
  let step := fun (best : Option (Window.Entry α)) e =>
    if w.h_F < e.j ∧ E.q ≤ E.weightOf e.Q then
      best.elim (some e) (fun old => if old.j < e.j then some e else best)
    else best
  have go (xs : List (Window.Entry α)) (best : Option (Window.Entry α)) :
      ∀ e, xs.foldl step best = some e →
        best = some e ∨ (e ∈ xs ∧ E.IsQuorum e.Q) := by
    induction xs generalizing best with
    | nil =>
        simp only [List.foldl_nil, List.not_mem_nil, false_and, or_false]
        exact fun _ h => h
    | cons a xs ih =>
        intro e he
        rcases ih (step best a) e he with he | he
        · unfold step at he
          dsimp only [Electorate.IsQuorum] at *
          split_ifs at he with ha <;> cases best <;> simp_all
          all_goals aesop
        · exact Or.inr ⟨List.mem_cons_of_mem _ he.1, he.2⟩
  have heq : Window.greatestReady E w = w.W.foldl step none := by
    rw [Window.greatestReady_def]
    congr 1
    funext best e
    dsimp [step]
    split_ifs <;> cases best <;> rfl
  rw [heq] at he
  exact (go w.W none e he).resolve_left (by simp)

omit [DecidableEq α] [RowCodec α] in
private theorem ktail_finalize_fields (E : Electorate α) (w : Window.State α) :
    (∀ d, Window.greatestReady E w = some d →
      (Window.finalizeWindow E w).F = d.X ∧ (Window.finalizeWindow E w).h_F = d.j) ∧
    (Window.greatestReady E w = none →
      (Window.finalizeWindow E w).F = w.F ∧ (Window.finalizeWindow E w).h_F = w.h_F) := by
  refine ⟨fun d hd => ?_, fun hd => ?_⟩ <;> rw [Window.finalizeWindow_def] <;> simp [hd]

omit [DecidableEq α] [RowCodec α] in
private theorem ktail_finalize_W (E : Electorate α) (w : Window.State α) :
    ∀ d ∈ (Window.finalizeWindow E w).W, d ∈ w.W := by
  intro d hd
  rw [Window.finalizeWindow_def] at hd
  cases hg : Window.greatestReady E w <;> simp only [hg] at hd <;>
    exact (List.mem_filter.mp hd).1

omit [DecidableEq α] [RowCodec α] in
private theorem ktail_events_fields (E : Electorate α) (cfg : FGConfig) (K : Nat)
    (w : Window.State α) :
    (Window.process_height_events E cfg K w).F = (Window.finalizeWindow E w).F ∧
    (Window.process_height_events E cfg K w).h_F = (Window.finalizeWindow E w).h_F ∧
    ∀ d ∈ (Window.process_height_events E cfg K w).W, d ∈ w.W ∨ d.Q = ∅ := by
  have hfin := ktail_finalize_W E w
  rw [Window.process_height_events_def]
  dsimp only
  split_ifs
  · refine ⟨rfl, rfl, fun d hd => ?_⟩
    rw [Window.advance_height_def] at hd
    rcases List.mem_append.mp (List.mem_of_mem_drop hd) with h | h
    · exact Or.inl (hfin d h)
    · rw [List.mem_singleton] at h
      subst h
      exact Or.inr rfl
  · refine ⟨rfl, rfl, fun d hd => ?_⟩
    rw [Window.advance_height_def] at hd
    exact Or.inl (hfin d hd)
  · exact ⟨rfl, rfl, fun d hd => Or.inl (hfin d hd)⟩

end Bits

variable {p : Params}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Paper 22:1990–2009 (FT-Tail-W, the bits of one retained key). Every bit of the
key
(hK, K) at a descendant P of Q was already set at Q, or comes from an exact finality row
in a block strictly after Q and at or below P.
DC: INTENTIONAL: the W window keeps bits per retained key; DC reads one live pair. -/
theorem ktail_entry_bits (Q : FGBlock (Fin p.n)) (hK : Nat) (K : FGBlock (Fin p.n)) :
    ∀ P, FGBlock.Preceq Q P → ∀ e ∈ (Window.derive p p.K_W P).W, e.j = hK → e.X = K →
      ∀ i ∈ e.Q, (∃ eQ ∈ (Window.derive p p.K_W Q).W, eQ.j = hK ∧ eQ.X = K ∧ i ∈ eQ.Q) ∨
        ∃ Y, StrictPrefix Q Y ∧ FGBlock.Preceq Y P ∧ ∃ a ∈ Y.rows, a.signer = i ∧
          a.finality_pair = some ⟨hK, K.root⟩ := by
  intro P
  induction P with
  | genesis =>
      intro hQ e he hj hX i hi
      obtain rfl := preceq_genesis.mp hQ
      exact Or.inl ⟨e, he, hj, hX, hi⟩
  | node P s root x rs ih =>
      intro hQ e he hj hX i hi
      by_cases hQB : Q = .node P s root x rs
      · subst hQB
        exact Or.inl ⟨e, he, hj, hX, hi⟩
      have hQP := preceq_parent_of_preceq_node hQ hQB
      have hev := (ktail_events_fields p.E p.cfg p.K_W
        (Window.certificateFolded p p.K_W (.node P s root x rs))).2.2 e he
      rcases hev with he' | hempty
      · have hW := (ktail_fold_fields rs { Window.derive p p.K_W P with s := s }).1
        change e ∈ (rs.foldl Window.process_row { Window.derive p p.K_W P with s := s }).W at he'
        rw [hW] at he'
        obtain ⟨e', he'', rfl⟩ := List.mem_map.mp he'
        obtain ⟨k1, k2, kbits⟩ := ktail_fold_entry rs e'
        have hj' : e'.j = hK := k1.symm.trans hj
        have hX' : e'.X = K := k2.symm.trans hX
        rcases (kbits i).mp hi with hi' | ⟨a, ha, hsig, hfp⟩
        · rcases ih hQP e' he'' hj' hX' i hi' with h | ⟨Y, hQY, hYP, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨Y, hQY, preceq_node_of_preceq s root x rs hYP, h⟩
        · refine Or.inr ⟨.node P s root x rs, ⟨hQ, hQB⟩, preceq_refl _, a, ha, hsig, ?_⟩
          rw [hfp, hj', hX']
      · rw [hempty] at hi
        exact absurd hi (Finset.notMem_empty i)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Paper 22:1990–2009 (FT-Tail-W, an already-finalized action head). If a
descendant H
of Q finalizes the key (hK, K) that is pending at Q, then a quorum of identities have a
bit for that key at Q or an exact finality row in a block strictly after Q and at or
below H. The quorum is the bit set of the entry that H's chain selects.
DC: INTENTIONAL: DC pins one action head, so it has no mixed finality state. -/
theorem ktail_final_quorum (Q : FGBlock (Fin p.n)) (hK : Nat) (K : FGBlock (Fin p.n))
    (hQ : (Window.derive p p.K_W Q).h_F < hK) :
    ∀ H, FGBlock.Preceq Q H → (Window.derive p p.K_W H).F = K →
      (Window.derive p p.K_W H).h_F = hK →
      ∃ S : Finset (Fin p.n), p.E.IsQuorum S ∧ ∀ i ∈ S,
        (∃ eQ ∈ (Window.derive p p.K_W Q).W, eQ.j = hK ∧ eQ.X = K ∧ i ∈ eQ.Q) ∨
        ∃ Y, StrictPrefix Q Y ∧ FGBlock.Preceq Y H ∧ ∃ a ∈ Y.rows, a.signer = i ∧
          a.finality_pair = some ⟨hK, K.root⟩ := by
  intro H
  induction H with
  | genesis =>
      intro hQH _ hFh
      obtain rfl := preceq_genesis.mp hQH
      exact absurd hFh (Nat.ne_of_lt hQ)
  | node P s root x rs ih =>
      intro hQH hF hFh
      by_cases hQB : Q = .node P s root x rs
      · subst hQB
        exact absurd hFh (Nat.ne_of_lt hQ)
      have hQP := preceq_parent_of_preceq_node hQH hQB
      let w := Window.certificateFolded p p.K_W (.node P s root x rs)
      have hev := ktail_events_fields p.E p.cfg p.K_W w
      have hfold := ktail_fold_fields rs { Window.derive p p.K_W P with s := s }
      change (Window.process_height_events p.E p.cfg p.K_W w).F = K at hF
      change (Window.process_height_events p.E p.cfg p.K_W w).h_F = hK at hFh
      rw [hev.1] at hF
      rw [hev.2.1] at hFh
      cases hg : Window.greatestReady p.E w with
      | none =>
          have hfin := (ktail_finalize_fields p.E w).2 hg
          have hPF : (Window.derive p p.K_W P).F = K := by
            rw [← hF, hfin.1]
            exact hfold.2.2.symm
          have hPh : (Window.derive p p.K_W P).h_F = hK := by
            rw [← hFh, hfin.2]
            exact hfold.2.1.symm
          obtain ⟨S, hS, hcov⟩ := ih hQP hPF hPh
          refine ⟨S, hS, fun i hi => ?_⟩
          rcases hcov i hi with h | ⟨Y, h1, h2, h3⟩
          · exact Or.inl h
          · exact Or.inr ⟨Y, h1, preceq_node_of_preceq s root x rs h2, h3⟩
      | some d =>
          have hfin := (ktail_finalize_fields p.E w).1 d hg
          obtain ⟨hdW, hdQ⟩ := ktail_greatest_mem p.E w d hg
          have hdX : d.X = K := hfin.1.symm.trans hF
          have hdj : d.j = hK := hfin.2.symm.trans hFh
          change d ∈ (rs.foldl Window.process_row { Window.derive p p.K_W P with s := s }).W
            at hdW
          rw [hfold.1] at hdW
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hdW
          obtain ⟨k1, k2, kbits⟩ := ktail_fold_entry rs e
          have hj' : e.j = hK := k1.symm.trans hdj
          have hX' : e.X = K := k2.symm.trans hdX
          refine ⟨_, hdQ, fun i hi => ?_⟩
          rcases (kbits i).mp hi with hi' | ⟨a, ha, hsig, hfp⟩
          · rcases ktail_entry_bits Q hK K P hQP e he hj' hX' i hi' with h | ⟨Y, h1, h2, h3⟩
            · exact Or.inl h
            · exact Or.inr ⟨Y, h1, preceq_node_of_preceq s root x rs h2, h3⟩
          · refine Or.inr ⟨.node P s root x rs, ⟨hQH, hQB⟩, preceq_refl _, a, ha, hsig, ?_⟩
            rw [hfp, hj', hX']

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1265–1289, 2007–2009. A row that is R6W-valid at a parent below the key
height plus one stays R6W-valid at a later parent that retains the key: the stale arm
once the later parent is higher, the height arm on the same height plateau.
DC: INTENTIONAL: W stale R6W arm; DC has only the current entry. -/
theorem ktail_r6w_transfer (σY σX : Window.State (Fin p.n)) (a : Row (Fin p.n))
    (hK : Nat) (K : FGBlock (Fin p.n)) (hfp : a.finality_pair = some ⟨hK, K.root⟩)
    (hY : Window.r6w σY a = true) (hlt : hK < σY.h) (hle : σY.h ≤ σX.h)
    (hT : σY.h = σX.h → σY.T_h.root = σX.T_h.root)
    (hwin : ∃ e ∈ σX.W, e.j = hK ∧ e.X = K) : Window.r6w σX a = true := by
  have hmatch : Window.windowMatch σX a = true := by
    obtain ⟨e, he, hej, heX⟩ := hwin
    rw [Window.windowMatch_def, List.any_eq_true]
    exact ⟨e, he, by simp only [hfp, hej, heX, decide_true]⟩
  cases hp : a.height_pair with
  | empty =>
      simp [Window.r6w_def, Window.heightMatch_def, Window.staleUseful_def, hp,
        NamedHeightPair.matchesEntry] at hY
  | vote h T t =>
      have hY' : (h = σY.h ∧ T = σY.T_h.root) ∨ (hK < h ∧ h < σY.h) := by
        simp only [Window.r6w_def, Window.heightMatch_def, Window.staleUseful_def, hp, hfp,
          NamedHeightPair.matchesEntry, Bool.or_eq_true, Bool.and_eq_true,
          decide_eq_true_eq] at hY
        rcases hY with h1 | ⟨h1, -⟩
        · exact Or.inl h1
        · exact Or.inr h1
      simp only [Window.r6w_def, Window.heightMatch_def, Window.staleUseful_def, hp, hfp,
        NamedHeightPair.matchesEntry, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        hmatch, and_true]
      rcases hY' with ⟨hh, hTT⟩ | ⟨h1, h2⟩
      · by_cases heq : σY.h = σX.h
        · exact Or.inl ⟨hh.trans heq, hTT.trans (hT heq)⟩
        · exact Or.inr ⟨hh ▸ hlt, hh ▸ lt_of_le_of_ne hle heq⟩
      · exact Or.inr ⟨h1, h2.trans_le hle⟩

/-! ### Block relay and full row selection -/

section Relay

variable {In V : Type} [DecidableEq V] {c : AppCodec In} {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)}

omit [DecidableEq V] in
private theorem ktail_idx_le_afterTicks {a b : Time} (hab : a ≤ b) :
    V2.D.Run.idxBefore rho a ≤ afterTicksIdx rho b := by
  change (rho.events.filter (fun e => decide (e.time < a))).length ≤
    (rho.events.filter (cutPred b)).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro e _ he
  exact decide_eq_true (Prod.Lex.toLex_le_toLex.mpr
    (Or.inl ((of_decide_eq_true he).trans_le hab)))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 01:83–86, 145–149 (R7 over all valid full-content rows). The honest carrier
selects every held R6W-valid row that is not on its parent chain, for any signer.
DC: INTENTIONAL exact FG-SA row selector; no honest-signer filter. -/
private theorem ktail_select_any (hs : V2.D.ScheduleWellFormed E rho) {s : Slot} {Q : Block}
    {rows : List (RowWire p.n)} (hc : HonestCarrier p c E rho s Q rows) {st : State p.n}
    (hst : proposalStateAt p c E rho s = some st) {P : FGBlock (Fin p.n)}
    (hP : FGSA.fgBlockOf st Q.parent = some P) {w : RowWire p.n} (hheld : rowHeld p st w)
    (hvalid : Window.rowValidW (parentFoldState p s P) w = true) :
    w ∈ rows ∨ w ∈ chainWireRows st Q.parent := by
  obtain ⟨k, -, hread, hslot, hrows⟩ := rowService_carrier_read p c E rho hs hc
  by_cases hon : w ∈ chainWireRows st Q.parent
  · exact Or.inr hon
  · left
    have he := Option.some.inj (hst.symm.trans hread)
    subst he
    rw [hrows]
    change w ∈ proposalRowsFor p _ _ Q.parent
    exact (mem_proposalRowsFor_iff p _ _ _ _).mpr ⟨P, hP, hheld, hslot.symm ▸ hvalid, hon⟩

private theorem ktail_chain_occurrence (st : State p.n) (hmeta : MetaInv p st)
    (H : FGBlock (Fin p.n)) (a : RowWire p.n) (b : Row (Fin p.n))
    (hd : a.toRow? = some b) (ha : a ∈ chainWireRows st (eraseFG H)) :
    ∃ W, FGBlock.Preceq W H ∧ b ∈ W.rows := by
  obtain ⟨rows, hrs, ha⟩ := List.mem_flatten.mp ha
  obtain ⟨o, ho, hrows⟩ := List.mem_filterMap.mp hrs
  obtain ⟨s, N, rfl, _hok, _hparent, _hdec, W, _hW, hWe, hWr⟩ :=
    hmeta.wireTree o ho
  change (if Block.preceq N.erase (eraseFG H) then some N.rows else none) = some rows at hrows
  split at hrows
  next hpath =>
    have he := Option.some.inj hrows
    subst rows
    refine ⟨W, ?_, ?_⟩
    · apply eraseFG_preceq_iff.mp
      rwa [hWe]
    · rw [hWr]
      exact List.mem_filterMap.mpr ⟨a, ha, hd⟩
  next hpath => cases hrows

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Paper 22:715–728, 1265–1289, 2007–2009. A held finality row of any signer that
is
R6W-valid at the carrier parent sets the retained bit or is carried by the carrier.
This is `finalityRow_bit_or_carried_W` without the honest-origin input.
DC: INTENTIONAL exact signed row selection and checked W history. -/
private theorem ktail_any_row_bit (hv : V2.D.ExecutionValid E rho)
    (X U : FGBlock (Fin p.n)) (y : Nat) (wireRows : List (RowWire p.n))
    (hc : HonestCarrier p c E rho X.slot (eraseFG X) wireRows)
    (hrows : X.rows = wireRows.filterMap RowWire.toRow?)
    (st : State p.n) (hst : proposalStateAt p c E rho X.slot = some st)
    (hlook : FGSA.fgBlockOf st (eraseFG X).parent = some X.parent)
    (e : Window.Entry (Fin p.n)) (he : e ∈ (Window.derive p p.K_W X.parent).W)
    (hej : e.j = y) (heX : e.X = U)
    (w : RowWire p.n) (b : Row (Fin p.n)) (hd : w.toRow? = some b)
    (hpair : b.finality_pair = some ⟨y, U.root⟩) (hheld : rowHeld p st w)
    (hvalid : Window.r6w (parentFoldState p X.slot X.parent) b = true) :
    b.signer ∈ e.Q ∨ ∃ row ∈ X.rows, FinRowNames p row b.signer y U := by
  have hvw : Window.rowValidW (parentFoldState p X.slot X.parent) w = true := by
    rw [Window.rowValidW_def, hd]
    exact hvalid
  rcases ktail_select_any hv.toScheduleWellFormed hc hst hlook hheld hvw with hcarry | hchain
  · right
    refine ⟨b, ?_, ?_⟩
    · rw [hrows]
      exact List.mem_filterMap.mpr ⟨w, hcarry, hd⟩
    · rw [FinRowNames_def]
      exact ⟨rfl, hpair⟩
  · obtain ⟨k, rfl⟩ := batch_proposal_read p c E rho X.slot st hst
    have bundle := storeBundle_postClock E rho k
      (V2.D.proposerOf rho (fgsaInterface p c) X.slot)
      (V2.D.proposalTime (fgsaInterface p c) X.slot)
    have hstored := ((fgBlockOf_spec p _ bundle.cstore _ X.parent).mp hlook).1
    change X.parent ∈ (clock p _ _).fg.TF at hstored
    rw [clock_fg] at hstored
    rw [eraseFG_parent] at hchain
    obtain ⟨W, hWP, hbW⟩ := ktail_chain_occurrence _ bundle.meta X.parent w b hd hchain
    left
    cases W with
    | genesis => exact (List.not_mem_nil hbW).elim
    | node P s root body rs =>
        exact exact_row_exclusionW E rho hv k _ X.parent hstored y U e he hej heX
          P s root body rs hWP b hbW hpair

end Relay

/-! ### The mixed arm of the Tail kernel -/

section Mixed

variable {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

omit [DecidableEq V] [Fintype V] in
private theorem ktail_mixed_F (X : FGBlock (Fin p.n)) :
    (finalityView p X).F = (Window.derive p p.K_W X).F ∧
      (finalityView p X).h_F = (Window.derive p p.K_W X).h_F := by
  simp only [finalityView_def, Window.certificateFinality_def, Window.projectFinality_def,
    and_self]

omit [DecidableEq V] [Fintype V] in
private theorem ktail_mixed_height (X : FGBlock (Fin p.n)) :
    (Window.derive p p.K_W X).h = (heightView p X).h ∧
      (Window.derive p p.K_W X).T_h = (heightView p X).T_h := by
  rw [heightView_def, Window.projectHeight_def]
  exact ⟨rfl, rfl⟩

/-- Exact retained-head service for the Tail terminal proposer.
Safe history and acceptance remain supplier obligations at the same receiver and deadline. -/
structure TailHeadReceipts (ΔF : Time) (pt : TailKernelPt p) : Prop where
  service : ∀ x nd H, x ∈ rho.honest →
    postClock E rho x (p.actionTime (pt.r + 1)) = some nd → H ∈ nd.st.fg.TF →
    ∀ y, y = V2.D.proposerOf rho (fgsaInterface p c)
      ((pt.r + 1) * p.R + kappaF p ΔF) → y ∈ rho.honest →
    FGBlock.Preceq (storeAt p c E rho
      (V2.D.Run.idxBefore rho (p.actionTime (pt.r + 1) + p.Δ)) y).fg.F H →
    TargetReceiptService E rho (eraseFG H) (p.actionTime (pt.r + 1) + p.Δ) y

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Paper 01:106–126 (acceptance relay), 22:2007–2009. The action head H of an
honest node
at action r+1 is held by the terminal proposer at its read. The block relay needs the
receiver's store finality below H: its carrier has finality below e+1 = ht(H) before the
next action, so R-XING puts the store finality below H.
DC: INTENTIONAL: DC pins one action head; W relays the head to the terminal proposer.
Assembly supplies RMono (Proofs/Foundations/Store fgsa_rMono) and RXing
(Proofs/Foundations/Crossing fgsa_rXing). -/
theorem ktail_head_delivered {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt)
    (hReceipts : TailHeadReceipts (p := p) (c := c) (E := E) (rho := rho) ΔF pt)
    (ow : TailOpeningWitness_W p c E rho ΔF pt)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hOrigin : ∀ (i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      HeldAt p c E rho i x W → ∀ u ∈ chainRows W,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (_hmono : RMono p c E rho) (hXing : RXing p c E rho)
    {x : V} (hx : x ∈ rho.honest) {nd : Node p}
    (hnd : postClock E rho x (p.actionTime (pt.r + 1)) = some nd)
    {H : FGBlock (Fin p.n)} (hH : H ∈ nd.st.fg.TF) (hHh : (heightView p H).h = ow.e + 1)
    {s : Slot} (hslot : s = (pt.r + 1) * p.R + kappaF p ΔF)
    (hprop : V2.D.proposerOf rho (fgsaInterface p c) s ∈ rho.honest)
    {st : State p.n} (hst : proposalStateAt p c E rho s = some st) : H ∈ st.fg.TF := by
  have hs := hT.set.base.valid.toScheduleWellFormed
  have hGSTq : E.t_GST ≤ p.actionTime (pt.r + 1) :=
    (ktail_slot_gst hT (s := pt.r * p.R) le_rfl).trans
      ((kmid_proposal_le_action p le_rfl).trans
        (le_of_lt (kmid_action_strictMono p (Nat.lt_succ_self pt.r))))
  have hwin := ktail_batch_horizon hT hGSTq (s := s) hslot.ge hslot.le
  rw [max_eq_left hGSTq] at hwin
  have hΔ : p.Δ ≤ ΔF := hT.set.base.delta ▸ hT.set.deltaF
  have hread : p.actionTime (pt.r + 1) + p.Δ ≤ SA.proposalTime p.toParams s :=
    (Int.add_le_add_left hΔ _).trans hwin.1
  have hhor : p.actionTime (pt.r + 1) + p.Δ ≤ rho.horizon := hread.trans hwin.2
  have hnext : p.actionTime (pt.r + 1) + p.Δ ≤ p.actionTime (pt.r + 1 + 1) := by
    rw [kmid_actionTime_eq, kmid_actionTime_eq]
    have hR : 1 ≤ p.R := by have h := p.RLarge; omega
    have hle : (pt.r + 1) * p.R + 1 ≤ (pt.r + 1 + 1) * p.R := by
      rw [Nat.succ_mul (pt.r + 1)]
      omega
    have h1 := kmid_slot_scale_le p hle
    have hd := p.deltaPos
    push_cast at h1 ⊢
    nlinarith
  obtain ⟨k, hk, hclock, -⟩ := ktail_action_store p c E rho x _ nd hnd
  have hHk : H ∈ (storeAt p c E rho k x).fg.TF := by
    rw [← hclock] at hH
    change H ∈ (FGSA.clock p (V2.D.Run.stateBefore E rho k x).st _).fg.TF at hH
    rw [clock_fg] at hH
    exact hH
  have hkj : k < V2.D.Run.idxBefore rho (p.actionTime (pt.r + 1) + p.Δ) :=
    (Gen.V2.Duty.index_lt_idxBefore_iff hs hk _).mpr (lt_add_of_pos_right _ p.deltaPos)
  obtain ⟨D, hD, hDF⟩ := (storeBundle_stateBefore E rho
    (V2.D.Run.idxBefore rho (p.actionTime (pt.r + 1) + p.Δ))
    (V2.D.proposerOf rho (fgsaInterface p c) s)).cstore.fg.Fcar
  change (finalityView p D).F = (storeAt p c E rho _ _).fg.F at hDF
  have hrowsFin := (kmid_fin_cut p c E rho (ow.e + 1) (pt.r + 1)
    (fun j x r a h hr ha hh => ktail_rows_through_next hT ow hnames j x r a h hr ha hh)).2
  have hDh : (finalityView p D).h_F < ow.e + 1 :=
    kmid_held_finality_afterTicks p c E rho hOrigin hT.set.base hT.set.faultQ (ow.e + 1)
      (p.actionTime (pt.r + 1 + 1)) (Nat.succ_pos _) hrowsFin _ _ D
      (ktail_idx_le_afterTicks hnext) ⟨hprop, hD⟩
  have hHj : HeldAt p c E rho (V2.D.Run.idxBefore rho (p.actionTime (pt.r + 1) + p.Δ)) x H :=
    ⟨hx, (fgsa_store_durable p c E rho hkj.le x).1 hHk⟩
  have hguard := hXing _ _ _ x D H hprop le_rfl hD hDF hHj (hHh ▸ hDh)
  have hrec := healing_held_block_receipt_on (p := p) (c := c) E rho
    hT.set.base.valid hT.set.base.receiptIdealization H
    (p.actionTime (pt.r + 1) + p.Δ) _ hprop
    (hReceipts.service x nd H hx hnd hH _ (by rw [hslot]) hprop hguard)
  change (postClock E rho (V2.D.proposerOf rho (fgsaInterface p c) s)
    (V2.D.proposalTime (fgsaInterface p c) s)).map (·.st) = some st at hst
  rw [postClock_def, preTick_def] at hst
  cases hj : V2.D.Run.tickIdx? rho (V2.D.proposerOf rho (fgsaInterface p c) s)
      (V2.D.proposalTime (fgsaInterface p c) s) with
  | none => rw [hj] at hst; cases hst
  | some k' =>
    rw [hj] at hst
    have hk' := V2.D.Run.tickIdx?_spec hj
    have hst' : ((fgsa p c).clock (V2.D.Run.stateBefore E rho k'
        (V2.D.proposerOf rho (fgsaInterface p c) s))
        (V2.D.proposalTime (fgsaInterface p c) s)).st = st := Option.some.inj hst
    have hik : V2.D.Run.idxBefore rho (p.actionTime (pt.r + 1) + p.Δ) ≤ k' := by
      by_contra hn
      have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hs hk' _).mp (Nat.lt_of_not_ge hn)
      exact (not_lt.mpr hread) ht
    change H ∈ (V2.D.Run.stateBeforeTime E rho _ _).st.fg.TF at hrec
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hrec
    have hcum := (fgsa_store_durable p c E rho hik _).1 hrec
    rw [← hst']
    change H ∈ (FGSA.clock p _ _).fg.TF
    rw [clock_fg]
    exact hcum

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Paper 22:1993–2009 (FT-Tail-W: "an already-finalized covering entry … the chain
retains and exposes the covering finalization"). The mixed arm: some honest action head H
of round r+1 has finalized the witness key K = J(Q) at h_K = h_j(Q). The certificate of
H's chain is replayed at the terminal carrier X: each quorum bit is already in X's parent
entry, or its exact row is relayed to X's proposer with H and selected by X.
DC: INTENTIONAL: DC pins one action head (W4FKChainSecondCheckpoint.lean:34), so it has
no mixed arm; W replays the historical certificate. Assembly supplies RMono and RXing. -/
theorem ktail_mixed_final {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt)
    (hReceipts : TailHeadReceipts (p := p) (c := c) (E := E) (rho := rho) ΔF pt)
    (ow : TailOpeningWitness_W p c E rho ΔF pt)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hOrigin : ∀ (i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      HeldAt p c E rho i x W → ∀ u ∈ chainRows W,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hmono : RMono p c E rho) (hXing : RXing p c E rho)
    (hbatch : ∀ x ∈ rho.honest, ∀ nd,
      postClock E rho x (p.actionTime (pt.r + 1)) = some nd →
      ∃ raw support seats m,
        FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support ∧
        Gen.Pure.Batch (Finset.card seats) m ∧
        WalkBatch p c rho nd.st ((pt.r + 1) * p.R + 1) raw support (eraseFG ow.Q) seats m)
    (hnotF : ¬ FGBlock.Preceq pt.U (finalityView p ow.Q).F)
    (X : FGBlock (Fin p.n))
    (hX : HonestProposal E rho (fgsaInterface p c)
      ((pt.r + 1) * p.R + kappaF p ΔF) (eraseFG X))
    (hslot : X.slot = (pt.r + 1) * p.R + kappaF p ΔF)
    (hcarrier : ∃ wireRows, HonestCarrier p c E rho X.slot (eraseFG X) wireRows ∧
      X.rows = wireRows.filterMap RowWire.toRow?)
    (st : State p.n) (hst : proposalStateAt p c E rho X.slot = some st)
    (hlook : FGSA.fgBlockOf st (eraseFG X).parent = some X.parent)
    (hrc : Window.RetainedW p X.parent (heightView p ow.Q).h_j (heightView p ow.Q).J ∨
      Window.CoveredW p X.parent (heightView p ow.Q).h_j (heightView p ow.Q).J)
    (hmix : ∃ x ∈ rho.honest, ∃ nd H,
      postClock E rho x (p.actionTime (pt.r + 1)) = some nd ∧
      FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st) = some H ∧
      FGBlock.Preceq ow.Q H ∧ (heightView p ow.Q).h_j < ow.e ∧
      (finalityView p H).h_F = (heightView p ow.Q).h_j ∧
      (finalityView p H).F = (heightView p ow.Q).J) :
    FGBlock.Preceq (heightView p ow.Q).J (Window.derive p p.K_W X).F := by
  classical
  have laws := (fgCertificateLaws p).height
  have hXne : X ≠ .genesis := by
    intro hg
    rw [hg] at hslot
    obtain ⟨-, hκ2, -, -, -, -, -⟩ := ktail_bounds hT
    have h0 : (0 : Nat) = (pt.r + 1) * p.R + kappaF p ΔF := hslot
    omega
  rcases hrc with hret | hcov
  swap
  · exact ((Window.CoveredW_def p X _ _).mp (covered_parent_W p _ _ X hcov)).2
  obtain ⟨eX, heX, heXj, heXX⟩ := (Window.RetainedW_def p X.parent _ _).mp hret
  obtain ⟨wireRows, hc, hrows⟩ := hcarrier
  obtain ⟨x, hx, nd, H, hnd, hdec, hQH, hlt, hFh, hFF⟩ := hmix
  obtain ⟨raw, support, seats, m, hhead, hcount, hwb⟩ := hbatch x hx nd hnd
  obtain ⟨H', hdec', hH, -, hHh, -, -, -, -, -⟩ :=
    ktail_action_head_split hT ow hx nd hnd raw support seats m hhead hcount hwb
  obtain rfl : H' = H := Option.some.inj (hdec'.symm.trans hdec)
  have hprop : V2.D.proposerOf rho (fgsaInterface p c) X.slot ∈ rho.honest := by
    rw [hslot]
    exact hX.1.2
  have hHst : H' ∈ st.fg.TF :=
    ktail_head_delivered hT hReceipts ow hnames hOrigin hmono hXing hx hnd hH hHh hslot hprop hst
  obtain ⟨-, -, hpend, -⟩ := (ktail_witness_split p ow.Q pt.U ow.coverQ).resolve_left hnotF
  have hQpend : (Window.derive p p.K_W ow.Q).h_F < (heightView p ow.Q).h_j :=
    (ktail_mixed_F ow.Q).2 ▸ hpend
  obtain ⟨S, hS, hcov⟩ := ktail_final_quorum ow.Q _ _ hQpend H' hQH
    ((ktail_mixed_F H').1 ▸ hFF) ((ktail_mixed_F H').2 ▸ hFh)
  have hQXp : FGBlock.Preceq ow.Q X.parent := ktail_terminal_path hT ow X hX
  have hXh : ow.e + 1 ≤ (heightView p X.parent).h := ow.heightQ ▸ laws.h_mono hQXp
  obtain ⟨k', hk'⟩ := batch_proposal_read p c E rho X.slot st hst
  have bundle := storeBundle_postClock E rho k'
    (V2.D.proposerOf rho (fgsaInterface p c) X.slot)
    (V2.D.proposalTime (fgsaInterface p c) X.slot)
  rw [← hk'] at bundle
  obtain ⟨k, -, -, hstore⟩ := ktail_action_store p c E rho x _ nd hnd
  have hHk : H' ∈ (storeAt p c E rho (k + 1) x).fg.TF := by
    rw [hstore]
    exact hH
  have hcover : FinalityCoveredByChild_W p X (heightView p ow.Q).J (heightView p ow.Q).h_j := by
    rw [FinalityCoveredByChild_W_def]
    refine ⟨eX, heX, heXj, heXX, S, hS, fun i hi => ?_⟩
    rcases hcov i hi with ⟨eQ, heQ, heQj, heQX, hiQ⟩ | ⟨Y, hQY, hYH, a, ha, hsig, hfp⟩
    · exact Or.inl (Window.window_bit_retained p p.K_W p.kWLarge ow.Q X.parent hQXp eQ eX heQ heX
        (heQj.trans heXj.symm) (heQX.trans heXX.symm) hiQ)
    · subst hsig
      cases Y with
      | genesis =>
          exact absurd (preceq_genesis.mp hQY.1) hQY.2
      | node P s' root bx rs =>
          have hQP : FGBlock.Preceq ow.Q P := preceq_parent_of_preceq_node hQY.1 hQY.2
          have hPH : FGBlock.Preceq P H' := preceq_trans (preceq_parent_node P s' root bx rs) hYH
          have hPh : (heightView p P).h = ow.e + 1 :=
            le_antisymm (hHh ▸ laws.h_mono hPH) (ow.heightQ ▸ laws.h_mono hQP)
          have hPT : (heightView p ow.Q).T_h = (heightView p P).T_h :=
            laws.entry_plateau hQP (ow.heightQ.trans hPh.symm)
          have hval := (stored_chain_rowsValidW E rho hT.set.base.valid.toDeliveryWellFormed
            (k + 1) x H' hHk P s' root bx rs hYH a ha).2
          have hvalX : Window.r6w (parentFoldState p X.slot X.parent) a = true := by
            refine ktail_r6w_transfer (Window.derive p p.K_W P) _ a _ _ hfp hval ?_ ?_ ?_
              ⟨eX, heX, heXj, heXX⟩
            · rw [(ktail_mixed_height P).1, hPh]
              exact hlt.trans (Nat.lt_succ_self _)
            · change (Window.derive p p.K_W P).h ≤ (Window.derive p p.K_W X.parent).h
              rw [(ktail_mixed_height P).1, (ktail_mixed_height X.parent).1, hPh]
              exact hXh
            · intro heq
              change (Window.derive p p.K_W P).h = (Window.derive p p.K_W X.parent).h at heq
              change (Window.derive p p.K_W P).T_h.root =
                (Window.derive p p.K_W X.parent).T_h.root
              rw [(ktail_mixed_height P).1, (ktail_mixed_height X.parent).1] at heq
              rw [(ktail_mixed_height P).2, (ktail_mixed_height X.parent).2, ← hPT,
                laws.entry_plateau hQXp (ow.heightQ.trans (hPh.symm.trans heq))]
          have hYst : FGBlock.node P s' root bx rs ∈ st.fg.TF :=
            KitFG.ancestor_closed_of_parent_closed _ bundle.cstore.fg.closed H' hHst _ hYH
          obtain ⟨s0, N, hmem, _, hYrows⟩ :=
            stored_wire_of_block p st bundle.cstore bundle.meta hYst (by intro h; cases h)
          obtain ⟨w, hw, hd⟩ := List.mem_filterMap.mp (hYrows ▸ ha)
          have hheld : rowHeld p st w :=
            Or.inr ((mem_allBlockRows_iff st w).mpr
              ⟨_, hmem, s0, N, decode_eq_block.mpr rfl, hw⟩)
          exact ktail_any_row_bit hT.set.base.valid X _ _ wireRows hc hrows st hst hlook
            eX heX heXj heXX w a hd hfp hheld hvalX
  exact (pendingFold_consume_W p _ _ X ⟨hXne, hcover⟩).1

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1985–2009 (FT-Tail-W). The `hmixed` input of `tail_kernel_W_of`, proved.
The finalized arm of the witness propagates F(Q); in the pending arm the witness key is
retained or covered at the terminal parent, and the mixed certificate is replayed.
DC: INTENTIONAL: DC has no mixed arm (one pinned action head). -/
theorem ktail_hmixed_of_relay {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt)
    (hReceipts : TailHeadReceipts (p := p) (c := c) (E := E) (rho := rho) ΔF pt)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hOrigin : ∀ (i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      HeldAt p c E rho i x W → ∀ u ∈ chainRows W,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hmono : RMono p c E rho) (hXing : RXing p c E rho)
    (hbatch : ∀ ow : TailOpeningWitness_W p c E rho ΔF pt, ∀ x ∈ rho.honest, ∀ nd,
      postClock E rho x (p.actionTime (pt.r + 1)) = some nd →
      ∃ raw support seats m,
        FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support ∧
        Gen.Pure.Batch (Finset.card seats) m ∧
        WalkBatch p c rho nd.st ((pt.r + 1) * p.R + 1) raw support (eraseFG ow.Q) seats m) :
    ∀ ow : TailOpeningWitness_W p c E rho ΔF pt, ∀ X : FGBlock (Fin p.n),
      HonestProposal E rho (fgsaInterface p c)
        ((pt.r + 1) * p.R + kappaF p ΔF) (eraseFG X) →
      (∃ x ∈ rho.honest, ∃ nd H,
        postClock E rho x (p.actionTime (pt.r + 1)) = some nd ∧
        FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st) = some H ∧
        FGBlock.Preceq ow.Q H ∧ (heightView p ow.Q).h_j < ow.e ∧
        (finalityView p H).h_F = (heightView p ow.Q).h_j ∧
        (finalityView p H).F = (heightView p ow.Q).J) →
      FGBlock.Preceq pt.U (Window.derive p p.K_W X).F := by
  intro ow X hX hmix
  have hs := hT.set.base.valid.toScheduleWellFormed
  have hQX : FGBlock.Preceq ow.Q X :=
    preceq_trans (ktail_terminal_path hT ow X hX) (kmid_parent_preceq p X)
  by_cases hF : FGBlock.Preceq pt.U (finalityView p ow.Q).F
  · rw [← (ktail_mixed_F X).1]
    exact ktail_finalized_propagates p ow.Q X pt.U hQX hF
  · obtain ⟨-, -, -, hUJ, hrc, -⟩ := ktail_terminal_key hT ow hnames hOrigin hF X hX
    obtain ⟨Xb, heX, -, hXslot, hcarrier, st, hst, hlook, -⟩ :=
      kmid_opening_carrier p c E rho hs hX
    obtain rfl := kmid_eraseFG_inj p heX
    exact preceq_trans hUJ (ktail_mixed_final hT hReceipts ow hnames hOrigin hmono hXing
      (hbatch ow) hF
      Xb hX hXslot (hXslot ▸ hcarrier) st (hXslot ▸ hst) hlook hrc hmix)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1985–2009 (FT-Tail-W). `tail_kernel_W_of` with the mixed arm proved: the only
open input is `hbatch` (K-ROWS). New named inputs: RMono (Proofs/Foundations/Store
fgsa_rMono) and RXing (Proofs/Foundations/Crossing fgsa_rXing); all other inputs are those of
`tail_kernel_W_of`.
DC: INTENTIONAL: W Tail kernel; Assembly supplies the named inputs. -/
theorem tail_kernel_W_of_relay (G ΔF : Time) (pt : TailKernelPt p)
    (hT : TailKernelPrem_W p c G ΔF E rho pt)
    (hReceipts : TailHeadReceipts (p := p) (c := c) (E := E) (rho := rho) ΔF pt)
    (hOrigin : ∀ (i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      HeldAt p c E rho i x W → ∀ u ∈ chainRows W,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : BatchCoverage p ΔF .target)
    (hSOCOVTarget : ∀ x ∈ rho.honest, ∀ (r : Nat) (C : FGBlock (Fin p.n)),
      actionSourceFG p c E rho x r = some (some C) → high p pt.w C →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        RowComplete p c rho x a ∧
        a.payload.height_pair = .vote (heightView p C).h (heightView p C).T_h.root false)
    (hqc : RQCOrigin p c E rho)
    (hI3 : FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2)
    (hbatch : ∀ ow : TailOpeningWitness_W p c E rho ΔF pt, ∀ x ∈ rho.honest, ∀ nd,
      postClock E rho x (p.actionTime (pt.r + 1)) = some nd →
      ∃ raw support seats m,
        FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support ∧
        Gen.Pure.Batch (Finset.card seats) m ∧
        WalkBatch p c rho nd.st ((pt.r + 1) * p.R + 1) raw support (eraseFG ow.Q) seats m)
    (hmono : RMono p c E rho) (hXing : RXing p c E rho) :
    ∀ x ∈ rho.honest,
      AcceptsFinalBefore p c E rho x pt.U (kernelDeadlineW p ΔF (pt.r + 1)) :=
  tail_kernel_W_of G ΔF pt hT hOrigin hBatch hSOCOVTarget hqc hI3 hStrat hEmittedSource
    hcapBefore hbatch (ktail_hmixed_of_relay hT hReceipts
      (fun j x r a e ha he => by
        obtain ⟨C, h1, h2, -⟩ := hEmittedSource j x r a e ha he
        exact ⟨C, h1, h2⟩)
      hOrigin hmono hXing hbatch)

end Mixed

end AvailableChain.FGSA.Run
end
