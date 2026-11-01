module
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthProposal
public import AvailableChainFGSAProofs.Proofs.Shared.ProposalRead
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionArithmetic

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. The proposal read retains the emitted wire, its rows and its exact parent. -/
theorem healing_promotion_proposal_read (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {s : Slot} {b : Block}
    (hp : HonestProposal E rho (fgsaInterface p c) s b) :
    ∃ j N, N.erase = b ∧ rho.events[j]? = some (.tick (V2.D.proposerOf rho (fgsaInterface p c) s)
        (SA.proposalTime p.toParams s)) ∧
      (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
        V2.D.Run.emitsAt E rho j ∧
      let st := ((fgsa p c).clock
        (V2.D.Run.stateBefore E rho j (V2.D.proposerOf rho (fgsaInterface p c) s))
        (SA.proposalTime p.toParams s)).st
      proposalStateAt p c E rho s = some st ∧ st.slot p = s ∧
        b = proposalBlock p (proposerHead p st s) s (c.app (rho.input
          (V2.D.proposerOf rho (fgsaInterface p c) s) (SA.proposalTime p.toParams s))) N.raw
              N.support
            (proposalRows p st (proposerHead p st s)) ∧
        N.rows = proposalRows p st (proposerHead p st s) :=
  proposal_read_named p c E rho hs hp

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:1356–1370; plan §3.2 step 2.
DC: SAME the honest proposal wire gives one FG carrier and its stored parent.
The result retains the original signed rows in their original order. -/
theorem healing_promotion_carrier [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {s : Slot} {Q : Block} (hQ : HonestProposal E rho (fgsaInterface p c) s Q) :
    ∃ X : FGBlock (Fin p.n), eraseFG X = Q ∧ X.slot = s ∧
      (∃ rows, HonestCarrier p c E rho s Q rows ∧ X.rows = rows.filterMap RowWire.toRow?) ∧
      ∃ st, proposalStateAt p c E rho s = some st ∧
        FGSA.fgBlockOf st Q.parent = some X.parent := by
  obtain ⟨j, N, heN, hj, hem, hst, _hslot, hb, hrows⟩ :=
    healing_promotion_proposal_read p c E rho hrec.base.valid.toScheduleWellFormed hQ
  let v := V2.D.proposerOf rho (fgsaInterface p c) s
  let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho j v)
    (SA.proposalTime p.toParams s)).st
  have hinv : CStoreInv p st := (storeBundle_postClock E rho j v _).cstore
  have hhead : proposerHead p st s ∈ st.base.blocks := by
    rw [proposerHead_def]
    exact getHead_stored p st hinv _ _
  obtain ⟨P, hP, hPe⟩ := (hinv.baseTree _).mp hhead
  have hpar : Q.parent = proposerHead p st s := by rw [hb]; rfl
  have hok : rowsOk Q N.rows = true := by
    rw [hb, hrows]
    exact rowsOk_node_packBody _ _ _ _ _
  have hne : Q ≠ .genesis := by rw [hb]; intro h; cases h
  have hlook : FGSA.fgBlockOf st Q.parent = some P :=
    (fgBlockOf_spec p st hinv _ P).mpr ⟨hP, hPe.trans hpar.symm⟩
  let o : Obj p := ⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩
  have hemit : V2.D.Run.emits E rho v o (V2.D.proposalTime (fgsaInterface p c) s) :=
    ⟨j, hj, hem⟩
  refine ⟨fgBlock P Q N.rows, eraseFG_fgBlock hne (hPe.trans hpar.symm) N.rows hok, ?_,
    ⟨N.rows, ⟨hQ, o, N, hemit, rfl, heN, rfl⟩, rfl⟩, st, hst, ?_⟩
  · rw [fgBlock_slot, hb]
    rfl
  · rw [fgBlock_parent]
    exact hlook

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:1356–1370; plan §3.2 step 2.
DC: SAME an honest slot after GST emits an actual proposal within the horizon.
Recovery supplies awake; the exact joined duty guard permits emission. -/
theorem healing_promotion_slot_proposal [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {s : Slot} (hslot : Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s)
    (hgst : E.t_GST ≤ SA.proposalTime p.toParams s)
    (hhor : SA.proposalTime p.toParams s ≤ rho.horizon)
    (hjoin : ∀ w, 0 ≤ w → w ≤ SA.proposalTime p.toParams s →
      V2.Event.restart (V2.D.proposerOf rho (fgsaInterface p c) s) w ∈ rho.events →
      w ≤ slotStartZ p ((s : Int) - 1)) :
    ∃ X : FGBlock (Fin p.n), HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧
      X.slot = s ∧
      ∃ rows, HonestCarrier p c E rho s (eraseFG X) rows ∧
        X.rows = rows.filterMap RowWire.toRow? := by
  obtain ⟨Q, hQ, _⟩ := fgsa_honestProposal_exists_of_awake_slot E rho
    hrec.base.valid.toScheduleWellFormed hrec.base.delta hslot
    (hrec.awake _ hslot.2 _ hgst hhor) hjoin hhor
  obtain ⟨X, he, hs, hc, _⟩ := healing_promotion_carrier E rho hrec hQ
  exact ⟨X, he ▸ hQ, hs, he ▸ hc⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1356–1370; plan §3.2 step 2.
DC: SAME the gap slot carries an actual FG proposal on the same time grid.
The full gap window and the gate deadline are retained. -/
theorem healing_promotion_gap_proposal [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (r : Nat) (hgst : E.t_GST ≤ p.actionTime r)
    (hhor : p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ ≤ rho.horizon) :
    (r : Time) * P p + 2 * P p - 4 * p.Δ + G ≤ rho.horizon ∧
    ∃ s X, HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
      (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s ≤
        p.actionTime r + 2 * P p + Γ p G - 10 * p.Δ ∧
      SA.gateTime p.toParams s ≤ p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ ∧
      ∃ rows, HonestCarrier p c E rho s (eraseFG X) rows ∧
        X.rows = rows.filterMap RowWire.toRow? := by
  obtain ⟨hwindow, s, hlo, hhi, hslot, hgate⟩ :=
    healing_promotion_gap E rho hrec.toRecovery₂ r hgst hhor
  have hbefore : SA.proposalTime p.toParams s ≤ rho.horizon := by
    change SA.proposalTime p.toParams s + 6 * p.Δ ≤ _ at hgate
    linarith [p.deltaPos]
  have hstart : E.t_GST ≤ SA.proposalTime p.toParams s := by
    have ha := actionTime_periodW p r
    have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
    have hP : 8 * p.Δ ≤ P p := by
      change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ
      nlinarith [p.deltaPos]
    linarith [p.deltaPos]
  have hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
    have ha := actionTime_periodW p r
    have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
    have hP : 8 * p.Δ ≤ P p := by
      change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ
      nlinarith [p.deltaPos]
    change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
    change (r : Time) * P p + 2 * P p ≤ 4 * p.Δ * (s : Int) at hlo
    nlinarith [p.deltaPos]
  have hjoin : ∀ w, 0 ≤ w → w ≤ SA.proposalTime p.toParams s →
      V2.Event.restart (V2.D.proposerOf rho (fgsaInterface p c) s) w ∈ rho.events →
      w ≤ slotStartZ p ((s : Int) - 1) := by
    intro w _ hws he
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
    have hwgst : w ≤ E.t_GST := by
      by_contra hn
      exact hrec.suffixNoRestart _ hslot.2 j w hj (lt_of_not_ge hn)
        ((hws.trans hbefore).trans_lt (lt_add_of_pos_right _ (by decide)))
    exact hwgst.trans hcut
  obtain ⟨X, hQ, hs, hc⟩ := healing_promotion_slot_proposal E rho hrec.toRecovery₂
    hslot hstart hbefore hjoin
  exact ⟨hwindow, s, X, hQ, hs, hlo, hhi, hgate, hc⟩

end AvailableChain.FGSA.Run
end
