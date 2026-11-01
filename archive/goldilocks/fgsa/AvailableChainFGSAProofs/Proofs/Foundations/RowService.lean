module
public import AvailableChainFGSAProofs.Proofs.Shared.RowReads
public import AvailableChainFGSAProofs.Proofs.Foundations.Carrier -- shake: keep (carrier API)
public import AvailableChainFGSAProofs.Proofs.Shared.Channels
public import AvailableChainFGSAProofs.Proofs.Shared.StoreRun -- shake: keep (store API)
public import AvailableChainFGSARun.Proofs.Receipts -- shake: keep (receipt API)
public import AvailableChainFGSA.Model.RowValidity -- shake: keep (R6 data)
public import AvailableChainFGSAClaims.Statements.Fold

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. BP01:109–114: a height row in an actual held carrier sets its matching bit,
which persists forward while the key stays fixed. DC: ChainState/
MatchingProgress.lean:147 gives the converse witness.
INTENTIONAL: this FG-SA adapter uses the forward KitFG
laws and an explicit occurrence; a parent-chain row alone is insufficient.
The held premise records the occurrence in the run; the fold law is pure. -/
theorem fgsa_rowBitPersist (target : Bool) (i : Nat) (x : V)
    (parent B W : FGBlock (Fin p.n)) (s : Slot) (root : BlockId) (body : Nat)
    (rows : List (Row (Fin p.n))) (a : Row (Fin p.n))
    (_held : HeldAt p c E rho i x (.node parent s root body rows))
    (ha : a ∈ rows) (hCB : FGBlock.Preceq (.node parent s root body rows) B)
    (hm : if target then a.height_pair = .vote (heightView p parent).h
      (heightView p parent).T_h.root false else
      a.height_pair.matchesEntry (heightView p parent).h (heightView p parent).T_h.root = true)
    (hPB : (heightView p parent).h = (heightView p B).h ∧
      (heightView p parent).T_h.root = (heightView p B).T_h.root)
    (hBW : FGBlock.Preceq B W)
    (hstate : (heightView p B).h = (heightView p W).h ∧
      (heightView p B).T_h.root = (heightView p W).T_h.root) :
    a.signer ∈ (if target then (heightView p W).target_participation
      else (heightView p W).progress) :=
  row_bit_persist p target parent W s root body rows a ha (KitFG.preceq_trans hCB hBW) hm
    ⟨hPB.1.trans hstate.1, hPB.2.trans hstate.2⟩

private theorem rowService_receipt_on (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hExecution : V2.D.ExecutionValid E rho)
    (dl : Time → Time) (cut : Time) (i : Fin p.n) (body : RowPayload)
    (send a : Time) (w : V)
    (hD : Gen.V2.Duty.DeliveryWithinOn E rho isRowObject dl cut)
    (hT : Gen.V2.Duty.Trigger E rho (ofRow p ⟨.seat .fg i, body⟩) send)
    (hw : w ∈ rho.honest) (hsa : send ≤ a) (ha : 0 ≤ a)
    (hcut : dl a ≤ cut) (hlt : a < dl a) (hhor : dl a ≤ rho.horizon)
    (hAwake : V2.D.AwakeOn E w a (dl a))
    (hRF : V2.D.restartFree rho w (V2.D.Run.actionCut rho a)
      (V2.D.Run.idxBefore rho (dl a))) :
    (⟨.seat .fg i, body⟩ : RowWire p.n) ∈
      (V2.D.Run.stateBeforeTime E rho (dl a) w).st.rowPool := by
  let o := ofRow p (⟨.seat .fg i, body⟩ : RowWire p.n)
  have hS := hExecution.toScheduleWellFormed
  have hReady : Gen.V2.Duty.ReadyTrigger E rho o send w a (dl a) := by
    rcases hT with ⟨v, hv, he⟩ | ⟨v, hv, k, he⟩
    · exact ⟨v, hv, Or.inl he, hAwake⟩
    · exact ⟨v, hv, Or.inr ⟨k, he⟩, hAwake⟩
  have hHistory : Gen.V2.Duty.HistorySafeAt E rho w o a := by
    apply Gen.V2.Duty.historySafeAt_of_processed_mono (E := E) (rho := rho)
    intro k l hkl _ hp
    exact decide_eq_true ((fgsa_store_durable p c E rho hkl w).2.2.2.subset
      (of_decide_eq_true hp))
  have hprocessed := Gen.V2.Duty.accepted_by_deadline_on E rho (fgsaTimely p)
    (fgsaAcceptanceInv p) isRowObject dl cut o send a w (by trivial) hD hReady hw hsa ha
    hlt hcut hhor hHistory hS hRF (fgsaHooks p c) (fgsaAcceptance p c) ?_ rfl
  · exact of_decide_eq_true hprocessed
  intro j t' hat htd hh
  have hidx : j < V2.D.Run.idxBefore rho (dl a) := by
    obtain ⟨parent, he, _⟩ := hh
    exact (Gen.V2.Duty.index_lt_idxBefore_iff hS he _).mpr htd
  have hdeps := fgsa_hReady_of_not_block (by intro s N h; cases h)
    (fgsa_hWF_of_delivery hExecution.wire) j t' hidx hh
  refine ⟨cstoreInv_stateBefore E rho j w, hdeps.1, hdeps.2, ?_⟩
  have hz : (fgsaClock p c).now (V2.D.Run.stateBefore E rho 0 w) = 0 :=
    (fgsaClock p c).init
  have hm := V2.D.Engine.stateBefore_now_mono_atRestart (fgsaClock p c)
    (fgsaRestoreTimeLaw p c) E rho hS (Nat.zero_le j) w
  rw [hz, fgsa_clock_now p c (V2.D.Run.stateBefore E rho j w)] at hm
  exact hm

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Strict receipt for every emitted row and every receiver awake from GST.
DC: SAME max deadline and horizon; INTENTIONAL FG adapter with bound ΔF. -/
theorem fgsa_rowService_receipt_sleep (ΔF : Time) (_hΔ : E.Δ = p.Δ)
    (hv : V2.D.ExecutionValid E rho)
    (hEpoch : ∀ x ∈ rho.honest, V2.D.NoRestartOn rho x E.t_GST (rho.horizon + 1))
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hΔF : E.Δ ≤ ΔF)
    (hAwake : ∀ x ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake x t = true)
    {j : Nat} {y : V} {r : Nat} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j y r a)
    (hhor : max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon)
    (x : V) (hx : x ∈ rho.honest) :
    HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF) := by
  obtain ⟨i, hi⟩ := honestRow_auth p c rho E hv ha
  obtain ⟨auth, body⟩ := a
  dsimp only at hi
  subst auth
  have hD := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hsync
    isRowObject ΔF (by
      intro o ho
      cases o with
      | mk auth m => cases m <;> first | rfl | exact ho.elim)
  let a := max (p.actionTime r) E.t_GST
  have ha0 : 0 ≤ a := (le_of_lt (by
    change (0 : Int) < 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    have := p.deltaPos
    positivity)).trans (le_max_left _ _)
  have hmax : max a E.t_GST = a := max_eq_left (le_max_right _ _)
  have hRF : V2.D.restartFree rho x (V2.D.Run.actionCut rho a)
      (V2.D.Run.idxBefore rho (max a E.t_GST + ΔF)) := by
    intro k w hka hkd he
    have hwa : a < w := by
      have hn := (V2.D.Engine.index_lt_actionCut_iff hv.toScheduleWellFormed he a).not.mp
        (Nat.not_lt.mpr hka)
      change ¬ (w < a ∨ (w = a ∧ (0 : Nat) = 0)) at hn
      rcases lt_trichotomy w a with hlt | heq | hgt
      · exact (hn (Or.inl hlt)).elim
      · exact (hn (Or.inr ⟨heq, rfl⟩)).elim
      · exact hgt
    have hwd := (Gen.V2.Duty.index_lt_idxBefore_iff hv.toScheduleWellFormed he _).mp hkd
    exact hEpoch x hx k w he ((le_max_right _ _).trans_lt hwa)
      ((hwd.le.trans (by simpa only [hmax] using hhor)).trans_lt
        (lt_add_of_pos_right _ (by decide)))
  have hheld := rowService_receipt_on p c E rho hv _ rho.horizon i body
    (p.actionTime r) a x hD (Or.inl ⟨y, ha.1, j, ha.2⟩) hx (le_max_left _ _) ha0
    (by simpa only [hmax] using hhor)
    (by simpa only [hmax] using lt_add_of_pos_right a (E.Δ_pos.trans_le hΔF))
    (by simpa only [hmax] using hhor) (by
      intro u hau hud
      exact hAwake x hx u ((le_max_right _ _).trans hau)
        (hud.le.trans (by simpa only [hmax] using hhor))) hRF
  exact Or.inl (by simpa only [hmax] using hheld)

/-- The approved base interface keeps NoRestart and the awake suffix. -/
theorem fgsa_rowService_receipt (ΔF : Time) (hΔ : E.Δ = p.Δ)
    (hv : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hΔF : E.Δ ≤ ΔF)
    (hAwake : ∀ x ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake x t = true)
    {j : Nat} {y : V} {r : Nat} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j y r a)
    (hhor : max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon)
    (x : V) (hx : x ∈ rho.honest) :
    HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF) :=
  fgsa_rowService_receipt_sleep p c E rho ΔF hΔ hv
    (fun x _ k w he _ _ => hnr k x w he) hsync hΔF hAwake ha hhor x hx

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
R6W and a row height at least the parent height imply current-height matching.
The stale arm contradicts the height bound. -/
theorem validForParent_currentHeightMatch {s : Slot} {Q : Block} {a : RowWire p.n}
    (st : State p.n) (H : FGBlock (Fin p.n))
    (hs : proposalStateAt p c E rho s = some st)
    (hH : fgBlockOf st Q.parent = some H)
    (hv : Window.rowValidW (parentFoldState p s H) a = true)
    (h : Nat) (T : BlockId) (hn : namedEntry a.payload.height_pair = some (h, T))
    (hh : (parentFoldState p s H).h ≤ h) : HeightMatch p c E rho s Q a := by
  obtain ⟨b, hb, hm⟩ := (Window.rowValidW_iff _ a).mp hv
  have he : b.height_pair = a.payload.height_pair := by
    cases a with
    | mk auth body =>
      cases auth with
      | none => cases hb
      | proposer s => cases hb
      | seat l i => cases l with
        | head s => cases hb
        | fg => cases hb; rfl
  refine ⟨st, H, hs, hH, ?_⟩
  rw [← he] at hn ⊢
  cases hp : b.height_pair with
  | empty => rw [hp] at hn; cases hn
  | vote k U timeout =>
      rw [hp] at hn
      have hname : k = h ∧ U = T := Prod.mk.inj (Option.some.inj hn)
      rcases hm with hm | hm
      · have keys : k = (parentFoldState p s H).h ∧
            U = (parentFoldState p s H).T_h.root := by
          simpa [Window.heightMatch_def, hp, NamedHeightPair.matchesEntry] using hm
        exact congrArg some (Prod.ext keys.1 keys.2)
      · cases hf : b.finality_pair with
        | none => simp [Window.staleUseful_def, hp, hf] at hm
        | some fp =>
            have hlt : k < (parentFoldState p s H).h := by
              have hbounds : (fp.height < k ∧ k < (parentFoldState p s H).h) ∧
                  Window.windowMatch (parentFoldState p s H) b = true := by
                simpa only [Window.staleUseful_def, hp, hf, Bool.and_eq_true,
                  decide_eq_true_eq] using hm
              exact hbounds.1.2
            exact (Nat.not_lt_of_ge hh (hname.1 ▸ hlt)).elim

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Exact signed-row selection from the pool or stored blocks, with R6.
DC: INTENTIONAL FG-SA transport adapter; no quorum or row-count premise. -/
theorem fgsa_tRowsSelect (hv : V2.D.ExecutionValid E rho) : TRowsSelect p c E rho := by
  intro s Q rows j y r a hc _ha hvalid hheld
  obtain ⟨k, hk, hread, hslot, hrows⟩ := rowService_carrier_read p c E rho
    hv.toScheduleWellFormed hc
  obtain ⟨st, hs, hh⟩ := hheld
  have he := Option.some.inj (hs.symm.trans hread)
  subst st
  obtain ⟨st', H, hs', hH, hvalid⟩ := hvalid
  have he := Option.some.inj (hs'.symm.trans hread)
  subst st'
  let st := ((fgsa p c).clock
    (V2.D.Run.stateBefore E rho k (V2.D.proposerOf rho (fgsaInterface p c) s))
    (SA.proposalTime p.toParams s)).st
  by_cases hon : a ∈ chainWireRows st Q.parent
  · exact Or.inr ⟨_, hread, hon⟩
  · left
    rw [hrows]
    change a ∈ proposalRowsFor p _ _ Q.parent
    apply (mem_proposalRowsFor_iff p _ _ _ _).mpr
    exact ⟨H, hH, hh, hslot.symm ▸ hvalid, hon⟩

private theorem heldBefore_at_proposal_durable (hs : V2.D.ScheduleWellFormed E rho)
    {s : Slot} {a : RowWire p.n} {d : Time} {st : State p.n}
    (hst : proposalStateAt p c E rho s = some st)
    (hheld : HeldBefore p c E rho (V2.D.proposerOf rho (fgsaInterface p c) s) a d)
    (hd : d ≤ SA.proposalTime p.toParams s) : heldAtProposal p c E rho s a := by
  refine ⟨st, hst, ?_⟩
  change (postClock E rho (V2.D.proposerOf rho (fgsaInterface p c) s)
    (V2.D.proposalTime (fgsaInterface p c) s)).map (·.st) = some st at hst
  rw [postClock_def, preTick_def] at hst
  cases hj : V2.D.Run.tickIdx? rho (V2.D.proposerOf rho (fgsaInterface p c) s)
      (V2.D.proposalTime (fgsaInterface p c) s) with
  | none => rw [hj] at hst; cases hst
  | some k =>
    rw [hj] at hst
    have hk := V2.D.Run.tickIdx?_spec hj
    have hst' : ((fgsa p c).clock (V2.D.Run.stateBefore E rho k
        (V2.D.proposerOf rho (fgsaInterface p c) s))
        (V2.D.proposalTime (fgsaInterface p c) s)).st = st := Option.some.inj hst
    have hik : V2.D.Run.idxBefore rho d ≤ k := by
      by_contra hn
      have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hs hk d).mp (Nat.lt_of_not_ge hn)
      exact (not_lt.mpr hd) ht
    change rowHeld p (V2.D.Run.stateBeforeTime E rho d
      (V2.D.proposerOf rho (fgsaInterface p c) s)).st a at hheld
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hs] at hheld
    have hcumul := fgsa_store_durable p c E rho hik
      (V2.D.proposerOf rho (fgsaInterface p c) s)
    rw [← hst']
    rcases hheld with hp | hb
    · left
      change a ∈ (FGSA.clock p (V2.D.Run.stateBefore E rho k _).st _).rowPool
      rw [clock_rowPool]
      exact hcumul.2.2.2.subset hp
    · right
      change a ∈ allBlockRows _ at hb
      change a ∈ allBlockRows (FGSA.clock p (V2.D.Run.stateBefore E rho k _).st _)
      unfold allBlockRows at hb ⊢
      rw [clock_proposals]
      obtain ⟨xs, hxs, ha⟩ := List.mem_flatten.mp hb
      obtain ⟨w, hw, hdec⟩ := List.mem_filterMap.mp hxs
      exact List.mem_flatten.mpr ⟨xs,
        List.mem_filterMap.mpr ⟨w, hcumul.2.2.1.subset hw, hdec⟩, ha⟩


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Receipt transport to a later proposal uses no second delivery delay.
DC: SAME no-restart storage transport; INTENTIONAL exact FG wire selector. -/
theorem fgsa_rowsReceipt_carriage (hv : V2.D.ExecutionValid E rho)
    {s : Slot} {Q : Block} {rows : List (RowWire p.n)}
    {j : Nat} {y : V} {r : Nat} {a : RowWire p.n} {d : Time}
    (hc : HonestCarrier p c E rho s Q rows) (ha : HonestRowAt p c E rho j y r a)
    (hvalid : ValidForParent p c E rho s Q a)
    (hheld : HeldBefore p c E rho (V2.D.proposerOf rho (fgsaInterface p c) s) a d)
    (hd : d ≤ SA.proposalTime p.toParams s) :
    a ∈ rows ∨ onParentChain p c E rho s Q a := by
  obtain ⟨k, hk, hread, _hslot, _hrows⟩ := rowService_carrier_read p c E rho
    hv.toScheduleWellFormed hc
  apply fgsa_tRowsSelect p c E rho hv s Q rows j y r a hc ha hvalid
  exact heldBefore_at_proposal_durable p c E rho hv.toScheduleWellFormed hread hheld hd

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
T-ROWS receipt under the bound row family, including pre-GST sends.
DC: SAME strict max deadline and finite horizon; INTENTIONAL row family. -/
theorem fgsa_tRowsReceipt (ΔF : Time) (hΔ : E.Δ = p.Δ)
    (hv : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hΔF : E.Δ ≤ ΔF)
    (hAwake : ∀ x ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake x t = true) : TRowsReceipt p c E rho ΔF := by
  intro j y r a ha hhor x hx
  exact fgsa_rowService_receipt p c E rho ΔF hΔ hv hnr hsync hΔF hAwake ha hhor x hx

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Post-GST receipt and carriage at one row delay.
DC: SAME strict receipt; INTENTIONAL R6 selector and independent row delay. -/
theorem fgsa_tRowsSync (ΔF : Time) (hΔ : E.Δ = p.Δ)
    (hv : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hΔF : E.Δ ≤ ΔF)
    (hAwake : ∀ x ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake x t = true) : TRowsSync p c E rho ΔF := by
  intro j y r a ha hg
  have receipt := fgsa_tRowsReceipt p c E rho ΔF hΔ hv hnr hsync hΔF hAwake j y r a ha
  rw [max_eq_left hg] at receipt
  refine ⟨receipt, ?_⟩
  intro s Q rows hc hvalid htime
  obtain ⟨k, hk, _⟩ := rowService_carrier_read p c E rho hv.toScheduleWellFormed hc
  have hhor := htime.trans (hv.toScheduleWellFormed.in_horizon _ (List.mem_of_getElem? hk)).2
  exact fgsa_rowsReceipt_carriage p c E rho hv hc ha hvalid
    (receipt hhor _ hc.1.1.2) htime

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The three T-ROWS clauses share one bound row family.
DC: INTENTIONAL FG transport adapter; SAME receipt and storage premises. -/
theorem fgsa_tRows (ΔF : Time) (hΔ : E.Δ = p.Δ)
    (hv : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hΔF : E.Δ ≤ ΔF)
    (hAwake : ∀ x ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake x t = true) : TRows p c E rho ΔF :=
  ⟨fgsa_tRowsSelect p c E rho hv, fgsa_tRowsSync p c E rho ΔF hΔ hv hnr hsync hΔF hAwake,
    fgsa_tRowsReceipt p c E rho ΔF hΔ hv hnr hsync hΔF hAwake⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
T-ROWS receipt under the bound row family, including pre-GST sends.
DC: SAME strict max deadline and finite horizon; INTENTIONAL row family. -/
theorem fgsa_tRowsReceipt_sleep (ΔF : Time) (hΔ : E.Δ = p.Δ)
    (hv : V2.D.ExecutionValid E rho)
    (hEpoch : ∀ x ∈ rho.honest, V2.D.NoRestartOn rho x E.t_GST (rho.horizon + 1))
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hΔF : E.Δ ≤ ΔF)
    (hAwake : ∀ x ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake x t = true) : TRowsReceipt p c E rho ΔF := by
  intro j y r a ha hhor x hx
  exact fgsa_rowService_receipt_sleep p c E rho ΔF hΔ hv hEpoch hsync hΔF hAwake ha hhor x hx

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Post-GST receipt and carriage at one row delay.
DC: SAME strict receipt; INTENTIONAL R6 selector and independent row delay. -/
theorem fgsa_tRowsSync_sleep (ΔF : Time) (hΔ : E.Δ = p.Δ)
    (hv : V2.D.ExecutionValid E rho)
    (hEpoch : ∀ x ∈ rho.honest, V2.D.NoRestartOn rho x E.t_GST (rho.horizon + 1))
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hΔF : E.Δ ≤ ΔF)
    (hAwake : ∀ x ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake x t = true) : TRowsSync p c E rho ΔF := by
  intro j y r a ha hg
  have receipt := fgsa_tRowsReceipt_sleep p c E rho ΔF hΔ hv hEpoch hsync hΔF hAwake j y r a ha
  rw [max_eq_left hg] at receipt
  refine ⟨receipt, ?_⟩
  intro s Q rows hc hvalid htime
  obtain ⟨k, hk, _⟩ := rowService_carrier_read p c E rho hv.toScheduleWellFormed hc
  have hhor := htime.trans (hv.toScheduleWellFormed.in_horizon _ (List.mem_of_getElem? hk)).2
  exact fgsa_rowsReceipt_carriage p c E rho hv hc ha hvalid
    (receipt hhor _ hc.1.1.2) htime

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The three T-ROWS clauses share one bound row family.
DC: INTENTIONAL FG transport adapter; SAME receipt and storage premises. -/
theorem fgsa_tRows_sleep (ΔF : Time) (hΔ : E.Δ = p.Δ)
    (hv : V2.D.ExecutionValid E rho)
    (hEpoch : ∀ x ∈ rho.honest, V2.D.NoRestartOn rho x E.t_GST (rho.horizon + 1))
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hΔF : E.Δ ≤ ΔF)
    (hAwake : ∀ x ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake x t = true) : TRows p c E rho ΔF :=
  ⟨fgsa_tRowsSelect p c E rho hv, fgsa_tRowsSync_sleep p c E rho ΔF hΔ hv hEpoch hsync hΔF hAwake,
    fgsa_tRowsReceipt_sleep p c E rho ΔF hΔ hv hEpoch hsync hΔF hAwake⟩

/-- The awake recovery suffix excludes a later wake restart at each honest receiver. -/
theorem rowService_epoch_of_recovery [Fintype V] {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) :
    ∀ x ∈ rho.honest, V2.D.NoRestartOn rho x E.t_GST (rho.horizon + 1) := by
  intro x hx k w he hgw _
  have hh := (h.base.valid.in_horizon _ (List.mem_of_getElem? he)).2
  change w ≤ rho.horizon at hh
  have hw := (h.base.restartsAtWakes x w (List.mem_of_getElem? he)).2.2
  have ha := h.awake x hx (w - 1) (by dsimp [Time] at *; omega) (by dsimp [Time] at *; omega)
  exact Bool.noConfusion (ha.symm.trans hw)

/-- Recovery supplies the service, awake suffix, and local epoch for all three row clauses. -/
theorem fgsa_tRows_recovery [Fintype V] {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) : TRows p c E rho ΔF :=
  fgsa_tRows_sleep p c E rho ΔF h.base.delta h.base.valid
    (rowService_epoch_of_recovery p c E rho h) h.sync h.deltaF h.awake

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The R6 invariant is available at the exact carrier read.
DC: INTENTIONAL immutable-parent validity of every stored proposal. -/
theorem fgsa_rowsValidStored_atProposal (hv : V2.D.ExecutionValid E rho)
    {s : Slot} {Q : Block} {rows : List (RowWire p.n)} {st : State p.n}
    (hc : HonestCarrier p c E rho s Q rows)
    (hs : proposalStateAt p c E rho s = some st) : RowsValidStored p st := by
  obtain ⟨i, _hi, hread, _⟩ := rowService_carrier_read p c E rho hv.toScheduleWellFormed hc
  have he := Option.some.inj (hs.symm.trans hread)
  subst st
  exact rowsValidStored_reachable p (reachable_postClock E rho i _ _)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The complete valid witnesses imply the raw batch witnesses. -/
theorem BatchPrem.batch_of_valid {p : Params} {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {ΔF : Time} {k : RowKind} {q y : Nat} {U X : FGBlock (Fin p.n)}
    (h : BatchPrem p c E rho ΔF k q y U X) :
    ∃ S : Finset (Fin p.n), S ⊆ honestSeats p c rho ∧ p.E.q ≤ p.E.weightOf S ∧
      ∀ i ∈ S, ∃ j r a t, r ≤ q ∧
        HonestRowAt p c E rho j (rho.seatOf (.base .fg) i) r a ∧
        a.auth = .seat .fg i ∧ NamesEntry p k a y U ∧
        eventTime rho j = some t ∧ t = p.actionTime r := by
  rcases h.valid with ⟨S, hs, hq, hv⟩; exact ⟨S, hs, hq, by grind⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. SO-COV chooses the same complete witness for validity, match, and receipt.
DC: SAME height coverage; INTENTIONAL cutoff q and pre-GST row transport. -/
theorem fgsa_batchCoverage (ΔF : Time) (kind : RowKind) : BatchCoverage p ΔF kind := by
  intro V _ _ In c E rho q y U X hb hheight
  rw [← KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)] at hheight
  dsimp only [hOf] at hheight
  obtain ⟨rows, hc, hXrows⟩ := hb.carrier
  obtain ⟨S, hS, hquorum, hvalid⟩ := hb.valid
  refine ⟨S, hquorum, ?_⟩
  intro i hi
  obtain ⟨j, r, a, t, hr, ha, hauth, hname, _ht, _htime, hvalid, hmatch⟩ := hvalid i hi
  have htime : p.actionTime r ≤ p.actionTime q := by
    change 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ ≤
      4 * p.Δ * ((q * p.R : Nat) : Int) + 6 * p.Δ
    have hR : (r * p.R : Nat) ≤ q * p.R := Nat.mul_le_mul_right p.R hr
    have hc : ((r * p.R : Nat) : Int) ≤ (q * p.R : Nat) := by exact_mod_cast hR
    have hΔ := p.deltaPos
    nlinarith
  have hdeadline : max (p.actionTime r) E.t_GST + ΔF ≤
      SA.proposalTime p.toParams X.slot := by
    have hmax := max_le_max_right E.t_GST htime
    exact (Int.add_le_add_right hmax ΔF).trans hb.horizon.1
  have hreceipt := hb.rowsReceipt j _ r a ha (hdeadline.trans hb.horizon.2)
    _ hc.1.1.2
  have hcarry := fgsa_rowsReceipt_carriage p c E rho hb.base.valid
    hc ha hvalid hreceipt hdeadline
  let b : Row (Fin p.n) := a.payload.toRow i
  have hdecode : a.toRow? = some b := by
    obtain ⟨auth, body⟩ := a
    dsimp only at hauth
    subst auth
    rfl
  have hrow : RowNames p kind b i y U := ⟨rfl, hname⟩
  rcases hcarry with hcarry | hchain
  · right
    refine ⟨b, ?_, hrow⟩
    rw [hXrows]
    exact List.mem_filterMap.mpr ⟨a, hcarry, hdecode⟩
  · obtain ⟨st, hs, hchain⟩ := hchain
    obtain ⟨idx, _hidx, hread, _⟩ := rowService_carrier_read p c E rho
      hb.base.valid.toScheduleWellFormed hc
    have he := Option.some.inj (hs.symm.trans hread)
    have hmeta : MetaInv p st := he ▸ (storeBundle_postClock E rho idx _ _).meta
    rw [eraseFG_parent] at hchain
    obtain ⟨W, hWP, hbW⟩ := rowService_chain_occurrence p st hmeta X.parent a b hdecode hchain
    have hUW := hb.above i (hS hi) W hWP ⟨b, hbW, hrow⟩
    have hpar : FGBlock.Preceq W.parent X.parent := by
      cases W with
      | genesis => exact hWP
      | node P s root body rs =>
          exact KitFG.preceq_trans (KitFG.preceq_parent_node P s root body rs) hWP
    have hlow := KitFG.h_mono p.E p.cfg hUW
    have hhigh := KitFG.h_mono p.E p.cfg hpar
    have hentry : (heightView p U).h = y ∧ (heightView p U).T_h = U := hb.entry
    simp only [heightView_eq_simplex p,
      KitFG.simplexHeightView_def, KitFG.heightOf_def] at hentry
    have hh : (derive p.E p.cfg W.parent).h = y := by
      rw [hentry.1] at hlow
      rw [hheight] at hhigh
      exact Nat.le_antisymm hhigh hlow
    have hT : (derive p.E p.cfg W.parent).T_h = U :=
      (KitFG.entry_eq_on_plateau p.E p.cfg hUW (hentry.1.trans hh.symm)).symm.trans hentry.2
    have hsames : (derive p.E p.cfg W.parent).h = (derive p.E p.cfg X.parent).h ∧
        (derive p.E p.cfg W.parent).T_h.root = (derive p.E p.cfg X.parent).T_h.root :=
      ⟨hh.trans hheight.symm,
        congrArg FGBlock.root (KitFG.entry_eq_on_plateau p.E p.cfg hpar (hh.trans hheight.symm))⟩
    -- HeightMatch remains an explicit consumer input when the fold changes.
    obtain ⟨_st, _H, _hs, _hH, _hm⟩ := hmatch
    left
    cases W with
    | genesis => exact (List.not_mem_nil hbW).elim
    | node P s root body rs =>
      change (derive p.E p.cfg P).h = y at hh
      change (derive p.E p.cfg P).T_h = U at hT
      change (derive p.E p.cfg P).h = (derive p.E p.cfg X.parent).h ∧
        (derive p.E p.cfg P).T_h.root = (derive p.E p.cfg X.parent).T_h.root at hsames
      cases kind with
      | target =>
        have hm : b.height_pair = .vote (heightView p P).h (heightView p P).T_h.root false := by
          simp only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def]
          rw [hh, hT]
          exact hrow.2
        have hk : (heightView p P).h = (heightView p X.parent).h ∧
            (heightView p P).T_h.root = (heightView p X.parent).T_h.root := by
          simpa only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def]
            using hsames
        have ht := row_bit_persist p true P X.parent s root body rs b hbW hWP hm hk
        change b.signer ∈ (heightView p X.parent).target_participation at ht
        exact hrow.1 ▸ ht
      | progress =>
        have hm : b.height_pair.matchesEntry
            (heightView p P).h (heightView p P).T_h.root = true := by
          simp only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def]
          obtain ⟨timeout, hn⟩ := hrow.2
          rw [hh, hT, hn]
          cases timeout <;> simp [NamedHeightPair.matchesEntry]
        have hk : (heightView p P).h = (heightView p X.parent).h ∧
            (heightView p P).T_h.root = (heightView p X.parent).T_h.root := by
          simpa only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def]
            using hsames
        have ht := row_bit_persist p false P X.parent s root body rs b hbW hWP hm hk
        change b.signer ∈ (heightView p X.parent).progress at ht
        exact hrow.1 ▸ ht

end AvailableChain.FGSA.Run
end
