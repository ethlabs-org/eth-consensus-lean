module
public import AvailableChainFGCompose.Statements.FinalityRows
public import AvailableChainFGCompose.Proofs.SourceHead
public import AvailableChainKitFG.HeightHistoryTransfer
public import AvailableChainKitFG.WindowTerminal

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (O : FGObservationReads R) (T : FGTiming)
variable (E : Generic.Env V) (rho : V2.D.Run V P)

/-- Exact action-walk coverage and held caps determine the pending head fields. -/
theorem pending_action_head_capped (Ef : Electorate (Fin n)) (cfg : FGConfig)
    (height : FGHeightLaws Ef O.height) (bridge : HeightBridge Ef cfg O.height)
    (y : Nat) (D U : FGBlock (Fin n)) (nd : P.State)
    (head : ∃ H, R.finalityHead nd = some H ∧ H ∈ (R.core nd).fg.TF)
    (walk : ∀ H, R.finalityHead nd = some H → Block.Preceq (R.erase D) (R.erase H))
    (reflect : ∀ A B, A ∈ (R.core nd).fg.TF → B ∈ (R.core nd).fg.TF →
      Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B)
    (hD : D ∈ (R.core nd).fg.TF)
    (hDh : (O.height D).h = y + 1) (hDJ : (O.height D).J = U)
    (hDj : (O.height D).h_j = y)
    (hcap : ∀ B ∈ (R.core nd).fg.TF, (O.height B).h ≤ y + 1)
    (hfin : ∀ B ∈ (R.core nd).fg.TF, (O.finality B).h_F < y) :
    ∃ H, R.finalityHead nd = some H ∧ FGBlock.Preceq D H ∧
      (O.height H).h = y + 1 ∧ (O.height H).J = U ∧ (O.height H).h_j = y ∧
      (O.finality H).h_F < y ∧ (O.height H).T_h = (O.height D).T_h := by
  obtain ⟨H, hH, hm⟩ := head
  have hDH := reflect D H hD hm (walk H hH)
  have hh : (O.height H).h = y + 1 :=
    Nat.le_antisymm (hcap H hm) (hDh ▸ height.h_mono hDH)
  have hj := justification_eq_on_plateau_of_bridge Ef cfg O.height bridge
    hDH (hDh.trans hh.symm)
  exact ⟨H, hH, hDH, hh, hj.1.trans hDJ, hj.2.trans hDj, hfin H hm,
    (height.entry_plateau hDH (hDh.trans hh.symm)).symm⟩

/-- The strict causal cap applies to the same held domain at the action read. -/
theorem pending_action_domain_cap (before : Nat) (x : V) (q y : Nat) (nd : P.State)
    (hx : x ∈ rho.honest)
    (hread : (R.core nd).fg.TF ⊆
      (R.core (V2.D.Run.stateBefore E rho before x)).fg.TF)
    (hbefore : before ≤ V2.D.Run.idxBefore rho (T.action q))
    (hcapBefore : ∀ (cut : Time) (b i : Nat) (x : V) (W : FGBlock (Fin n)),
      i ≤ V2.D.Run.idxBefore rho cut → HeldAt R E rho i x W →
      (∀ j z r a u h B timeout, HonestRowAt S E rho T j z r a →
        S.decode a = some u → u.height_pair = .vote h B timeout →
        T.action r < cut → h < b + 1) → (O.height W).h < b + 2)
    (hrows : ∀ j z r a u h B timeout, HonestRowAt S E rho T j z r a →
      S.decode a = some u → u.height_pair = .vote h B timeout →
      T.action r < T.action q → h < y + 1) :
    ∀ B ∈ (R.core nd).fg.TF, (O.height B).h ≤ y + 1 := by
  intro B hB
  exact Nat.le_of_lt_succ
    (hcapBefore (T.action q) y before x B hbefore ⟨hx, hread hB⟩ hrows)

/-- The action head uses the selected walk and exact read, with both causal caps. -/
theorem pending_action_head (Ef : Electorate (Fin n)) (cfg : FGConfig)
    (height : FGHeightLaws Ef O.height) (bridge : HeightBridge Ef cfg O.height)
    (before : Nat) (x : V) (q y : Nat) (D U : FGBlock (Fin n)) (nd : P.State)
    (hx : x ∈ rho.honest)
    (hread : (R.core nd).fg.TF ⊆
      (R.core (V2.D.Run.stateBefore E rho before x)).fg.TF)
    (hbefore : before ≤ V2.D.Run.idxBefore rho (T.action q)) (hq : 0 < q)
    (head : ∃ H, R.finalityHead nd = some H ∧ H ∈ (R.core nd).fg.TF)
    (walk : ∀ H, R.finalityHead nd = some H → Block.Preceq (R.erase D) (R.erase H))
    (reflect : ∀ A B, A ∈ (R.core nd).fg.TF → B ∈ (R.core nd).fg.TF →
      Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B)
    (hD : D ∈ (R.core nd).fg.TF)
    (hDh : (O.height D).h = y + 1) (hDJ : (O.height D).J = U)
    (hDj : (O.height D).h_j = y) (hDfin : (O.finality D).h_F < y)
    (hcapBefore : ∀ (cut : Time) (b i : Nat) (x : V) (W : FGBlock (Fin n)),
      i ≤ V2.D.Run.idxBefore rho cut → HeldAt R E rho i x W →
      (∀ j z r a u h B timeout, HonestRowAt S E rho T j z r a →
        S.decode a = some u → u.height_pair = .vote h B timeout →
        T.action r < cut → h < b + 1) → (O.height W).h < b + 2)
    (hfinalityLag : ∀ (r y i : Nat) (x : V) (W : FGBlock (Fin n)),
      0 < y → i ≤ V2.D.Run.idxBefore rho (T.action (r + 1)) →
      HeldAt R E rho i x W →
      (∀ j z s a u B timeout, HonestRowAt S E rho T j z s a →
        S.decode a = some u → u.height_pair = .vote y B timeout →
        ¬ T.action s < T.action r) → (O.finality W).h_F < y)
    (hrows : ∀ j z r a u h B timeout, HonestRowAt S E rho T j z r a →
      S.decode a = some u → u.height_pair = .vote h B timeout →
      T.action r < T.action q → h < y + 1)
    (hnoRow : ∀ j z r a u B timeout, HonestRowAt S E rho T j z r a →
      S.decode a = some u → u.height_pair = .vote y B timeout →
      ¬ T.action r < T.action (q - 1)) :
    ∃ H, R.finalityHead nd = some H ∧ FGBlock.Preceq D H ∧
      (O.height H).h = y + 1 ∧ (O.height H).J = U ∧ (O.height H).h_j = y ∧
      (O.finality H).h_F < y ∧ (O.height H).T_h = (O.height D).T_h := by
  apply pending_action_head_capped R O Ef cfg height bridge y D U nd head walk reflect
    hD hDh hDJ hDj
  · exact pending_action_domain_cap R S O T E rho before x q y nd
      hx hread hbefore hcapBefore hrows
  · intro B hB
    exact hfinalityLag (q - 1) y before x B ((Nat.zero_le _).trans_lt hDfin)
      (by simpa only [Nat.sub_add_cancel (Nat.one_le_of_lt hq)] using hbefore)
      ⟨hx, hread hB⟩ hnoRow

/-- Consume the produced opening or covered source at this same action read. -/
theorem finality_action_source (L : FGCoreLaws R) (Ef : Electorate (Fin n))
    (height : FGHeightLaws Ef O.height) (x : V) (q y opening : Nat)
    (D : FGBlock (Fin n))
    (service : FGSourceService R E rho x (T.action q) opening (q * T.roundSlots) D)
    (hbefore : opening ≤ q * T.roundSlots) (hDh : (O.height D).h = y + 1)
    (hcap : ∀ nd, postClock E rho x (T.action q) = some nd →
      ∀ B ∈ (R.core nd).fg.TF, (O.height B).h ≤ y + 1) :
    ∃ nd C, postClock E rho x (T.action q) = some nd ∧ R.source nd = some C ∧
      FGBlock.Preceq D C ∧ (O.height C).h = y + 1 ∧
      (O.height C).T_h = (O.height D).T_h :=
  action_source_capped R E rho L Ef O.height height x (T.action q) opening
    (q * T.roundSlots) y D service hbefore hDh hcap

/-- The exact earlier signed rows bound every held block at the next cut. -/
theorem actual_anchor_cap (q y : Nat)
    (hcapBefore : ∀ (cut : Time) (b i : Nat) (x : V) (W : FGBlock (Fin n)),
      i ≤ V2.D.Run.idxBefore rho cut → HeldAt R E rho i x W →
      (∀ j z r a u h B timeout, HonestRowAt S E rho T j z r a →
        S.decode a = some u → u.height_pair = .vote h B timeout →
        T.action r < cut → h < b + 1) → (O.height W).h < b + 2)
    (hrows : ∀ j x r a u h B timeout, HonestRowAt S E rho T j x r a →
      S.decode a = some u → u.height_pair = .vote h B timeout →
      T.action r < T.action (q + 1) → h ≤ y + 1) :
    ∀ i x W, i ≤ V2.D.Run.idxBefore rho (T.action (q + 1)) →
      HeldAt R E rho i x W → (O.height W).h ≤ y + 2 := by
  intro i x W hi hW
  have bound := hcapBefore (T.action (q + 1)) (y + 1) i x W hi hW
    (fun j z r a u h B timeout ha hu hp ht =>
      Nat.lt_succ_of_le (hrows j z r a u h B timeout ha hu hp ht))
  exact Nat.le_of_lt_succ (by simpa only [Nat.add_assoc, Nat.add_comm 1 2] using bound)

/-- Capacity at least two and the proved height cap exclude eviction. -/
theorem actual_anchor_retained_or_covered (Ef : Electorate (Fin n)) (cfg : FGConfig)
    (K : Nat) (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K)
    (y : Nat) (D U A : FGBlock (Fin n)) (hDA : FGBlock.Preceq D A)
    (hret : KitFG.Window.RetainedW Ef cfg K D y U)
    (hcap : (KitFG.Window.heightView Ef cfg K A).h ≤ y + 2) :
    KitFG.Window.RetainedW Ef cfg K A y U ∨ KitFG.Window.CoveredW Ef cfg K A y U := by
  have hj := (KitFG.Window.windowHeightLaws Ef cfg K hK).justified_below_height A
  apply KitFG.Window.terminal_retained_or_coveredW Ef cfg K hne hK D A hDA y U hret
  change (KitFG.Window.certificateHeight Ef cfg K A).h ≤ y + 2 at hcap
  exact (hj.trans_le hcap).trans_le (Nat.add_le_add_left hK y)


private theorem d7a4_release (Ef : Electorate (Fin n)) (cfg : FGConfig)
    (Λ : RecordOnce) (i : Fin n) (C U : FGBlock (Fin n)) (hd : HeadFields) (y : Nat)
    (hC : (derive Ef cfg C).h = y + 1)
    (hfields : hd.h_j = y ∧ hd.J = U.root ∧ hd.h_F < y)
    (hrecord : HighRecordGuard_W Λ y U ∧ HighRecordFresh (y + 1) Λ) :
    (createRowOnce Ef cfg Λ i (some C) hd).1 =
      some ⟨i, .vote (y + 1) (derive Ef cfg C).T_h.root false, some ⟨y, U.root⟩⟩ := by
  obtain ⟨⟨ht, hto, hl⟩, htn, hton, hln, hsent⟩ := hrecord
  have hfp : finality_pair Λ.toRecord hd = some ⟨y, U.root⟩ := by
    delta finality_pair
    simp only [hfields.1, hfields.2.1, hfields.2.2, ht, hto, hl, and_self, ↓reduceIte]
  have hhp : height_pair Λ.toRecord
      (some ((derive Ef cfg C).h, (derive Ef cfg C).T_h.root))
      (some ⟨y, U.root⟩) = .vote (y + 1) (derive Ef cfg C).T_h.root false := by
    have ho : own_lock Λ.toRecord (y + 1) (some ⟨y, U.root⟩) = none := by
      change (if y = y + 1 then some U.root else Λ.lock (y + 1)) = none
      simp only [show y ≠ y + 1 from Nat.ne_of_lt (Nat.lt_succ_self y), ↓reduceIte, hln]
    rw [hC]
    change (if Λ.timeout (y + 1) = true then _ else _) = _
    rw [hton, ho, htn]
    rfl
  have hsame : sameHeightOnce Λ (y + 1) (derive Ef cfg C).T_h.root false = false := by
    delta sameHeightOnce
    rw [List.any_eq_false]
    intro b hb
    cases hh : b.1 with
    | empty => simp only [Bool.false_eq_true, not_false_eq_true]
    | vote h B timeout =>
      have hne : h ≠ y + 1 := by
        intro he
        exact hsent b hb B timeout
          (hh.trans (congrArg (fun k => NamedHeightPair.vote k B timeout) he))
      simp only [hne, decide_false, Bool.false_and, Bool.false_eq_true, not_false_eq_true]
  have hkey : (NamedHeightPair.vote (y + 1) (derive Ef cfg C).T_h.root false,
      some (FinalityPair.mk y U.root)) ∉ Λ.sent := by
    intro hm
    exact hsent _ hm _ false rfl
  rw [createRowOnce_def, hfp]
  dsimp only [Option.map_some]
  rw [hhp]
  delta Row.onceKey
  simp only [hsame, Bool.false_eq_true, ↓reduceIte,
    Option.filter_some, Nat.lt_succ_self, decide_true, hkey]

/-- The computed client release produces one fixed signed row for each selected seat. -/
theorem fresh_unanimous_rows (D : FGHistoryWireReads S)
    (Ef : Electorate (Fin n)) (cfg : FGConfig) (valid : Wire → Bool)
    (height : FGHeightLaws Ef O.height) (bridge : HeightBridge Ef cfg O.height)
    (makeWire : Row (Fin n) → Wire)
    (wireDecode : ∀ row, S.decode (makeWire row) = some row)
    (wireValid : ∀ i y U B,
      valid (makeWire ⟨i, .vote (y + 1) B false, some ⟨y, U⟩⟩) = true)
    (client : ∀ nd, (S.inputs nd).1 = R.source nd)
    (release : ∀ i q nd row,
      postClock E rho (safetyHolder S rho i) (T.action q) = some nd →
      E.awake (safetyHolder S rho i) (T.action q) = true →
      (createRowOnce Ef cfg (S.record nd) i (S.inputs nd).1 (S.inputs nd).2).1 = some row →
      ∃ j, rho.events[j]? = some (.tick (safetyHolder S rho i) (T.action q)) ∧
        S.encode (makeWire row) ∈ V2.D.Run.emitsAt E rho j)
    (q y : Nat) (B U : FGBlock (Fin n)) (seats : Finset (Fin n))
    (hS : ∀ i ∈ seats, safetyHolder S rho i ∈ rho.honest) (hQ : Ef.IsQuorum seats)
    (hBh : (O.height B).h = y + 1)
    (hreads : ∀ i ∈ seats, ∃ nd C,
      postClock E rho (safetyHolder S rho i) (T.action q) = some nd ∧
      E.awake (safetyHolder S rho i) (T.action q) = true ∧ R.source nd = some C ∧
      FGBlock.Preceq B C ∧ (O.height C).h = y + 1)
    (hfields : ∀ i ∈ seats, ∀ nd,
      postClock E rho (safetyHolder S rho i) (T.action q) = some nd →
      (S.inputs nd).2.h_j = y ∧ (S.inputs nd).2.J = U.root ∧ (S.inputs nd).2.h_F < y)
    (hrecord : ∀ i ∈ seats, ∀ nd,
      postClock E rho (safetyHolder S rho i) (T.action q) = some nd →
      HighRecordGuard_W (S.record nd) y U ∧ HighRecordFresh (y + 1) (S.record nd))
    (hearlier : ∀ i ∈ seats, ∀ j r a h, r < q →
      HonestRowAt S E rho T j (safetyHolder S rho i) r a →
      historyRowHeight S D a = some h → h < y + 1) :
    ∃ rows : Fin n → Wire,
      FreshFinalityRows_W R S O T E rho D Ef valid q y U seats rows ∧
      (∀ i ∈ seats, namedEntry (D.heightPair (rows i)) = some (y + 1, (O.height B).T_h.root)) ∧
      (∀ i ∈ seats, D.heightPair (rows i) = .vote (y + 1) (O.height B).T_h.root false) := by
  let row : Fin n → Row (Fin n) := fun i =>
    ⟨i, .vote (y + 1) (O.height B).T_h.root false, some ⟨y, U.root⟩⟩
  let rows := fun i => makeWire (row i)
  have hp (i : Fin n) : D.heightPair (rows i) =
      .vote (y + 1) (O.height B).T_h.root false := D.decode_height _ _ (wireDecode _)
  have hf (i : Fin n) : D.finalityPair (rows i) = some ⟨y, U.root⟩ :=
    D.decode_finality _ _ (wireDecode _)
  have hs (i : Fin n) : D.signer (rows i) = some i := D.decode_signer _ _ (wireDecode _)
  refine ⟨rows, ⟨hS, hQ, ?_⟩, ?_, fun i _ => hp i⟩
  · intro i hi
    obtain ⟨nd, C, hnd, awake, src, path, hh⟩ := hreads i hi
    have entry := height.entry_plateau path (hBh.trans hh.symm)
    have ch : (derive Ef cfg C).h = y + 1 := by
      rw [bridge C] at hh
      exact hh
    have ce : (derive Ef cfg C).T_h = (O.height B).T_h := by
      rw [bridge C] at entry
      exact entry.symm
    have emitted := d7a4_release Ef cfg (S.record nd) i C U (S.inputs nd).2 y
      ch (hfields i hi nd hnd) (hrecord i hi nd hnd)
    rw [ce] at emitted
    have rel : (createRowOnce Ef cfg (S.record nd) i (S.inputs nd).1
        (S.inputs nd).2).1 = some (row i) := by
      rw [client, src]
      exact emitted
    obtain ⟨j, hj, he⟩ := release i q nd (row i) hnd awake rel
    refine ⟨j, C, ⟨hS i hi, hj, he⟩, ⟨wireValid _ _ _ _, i, hs i, rfl⟩,
      hs i, ?_, hf i, ?_, hh, hearlier i hi⟩
    · delta historyRowHeight
      rw [hp]
    · delta actionSourceFG
      simp only [hnd, Option.map_some, src]
  · intro i _
    rw [hp]; rfl

end AvailableChain.FGCompose
end
