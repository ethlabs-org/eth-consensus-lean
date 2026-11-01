module
public import AvailableChainFGSAClaims.Statements.ChannelProps
public import AvailableChainFGSAProofs.Proofs.Foundations.Store

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params)

private theorem fgsa_block_reconcile_edits (st : State p.n) (h : CStoreInv p st)
    (s : Slot) (N : NamedProposal p.n)
    (hF : st.fg.F ≠ (admitBlock p st s N).fg.F) :
    let st' := admitBlock p st s N
    st'.base.obligations = st.base.obligations.filter (fun row => activeCompatible st' row.1) ∧
    st'.base.genuine = st.base.genuine.map
      (fun row => (row.1, row.2.filter (activeCompatible st'))) ∧
    st'.fastWrite = st.fastWrite.map
      (fun row => (row.1, row.2.filter (activeCompatible st'))) ∧
    st'.base.stableRecord =
      (if Block.preceq (eraseFG st'.fg.F) st.base.stableRecord then st.base.stableRecord
       else eraseFG st'.fg.F) := by
  cases hn : namedParentHeld st N with
  | false =>
    rw [admitBlock_refused p st s N (Or.inl hn)] at hF
    exact (hF rfl).elim
  | true =>
    cases hP : parentFG st N.erase with
    | none =>
        rw [admitBlock_refused p st s N (Or.inr (Or.inl hP))] at hF
        exact (hF rfl).elim
    | some P =>
        cases ha : blockAccepted p st s N P with
        | false =>
            rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hP, ha⟩))] at hF
            exact (hF rfl).elim
        | true =>
            obtain ⟨pool, he, -⟩ := admitBlock_accepted_eq p st s N P hn hP ha
            obtain ⟨-, -, -, hob, hgen, hstab, -, -, -⟩ :=
              cstoreInv_accepted_pre p st h s N P hP ha
            let st1 : State p.n := { st with
              base := GridCO.admitProposal p.toParams.engine st.base (baseProposal s N.erase
                  N.raw N.support) N.erase
                (N.raw.map baseHead)
              fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
              proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
            change admitBlock p st s N =
              { (if st1.fg.F = st.fg.F then st1 else reconcile st1) with rowPool := pool } at he
            change st1.base.obligations = st.base.obligations at hob
            change st1.base.genuine = st.base.genuine at hgen
            change st1.base.stableRecord = st.base.stableRecord at hstab
            rw [he] at hF ⊢
            by_cases hc : st1.fg.F = st.fg.F
            · rw [ite_eq_left hc] at hF
              exact (hF hc.symm).elim
            · rw [ite_eq_right hc] at hF ⊢
              change (reconcile st1).base.obligations =
                  st.base.obligations.filter (fun row => activeCompatible (reconcile st1) row.1) ∧
                (reconcile st1).base.genuine = st.base.genuine.map
                  (fun row => (row.1, row.2.filter (activeCompatible (reconcile st1)))) ∧
                (reconcile st1).fastWrite = st.fastWrite.map
                  (fun row => (row.1, row.2.filter (activeCompatible (reconcile st1)))) ∧
                (reconcile st1).base.stableRecord =
                  (if Block.preceq (eraseFG (reconcile st1).fg.F) st.base.stableRecord
                   then st.base.stableRecord else eraseFG (reconcile st1).fg.F)
              have hcompat : activeCompatible (reconcile st1) = activeCompatible st1 := by
                rw [activeCompatible_eq, activeCompatible_eq, (reconcile_frame st1).1]
              rw [hcompat, reconcile_obligations, reconcile_genuine, reconcile_fastWrite,
                reconcile_stable, (reconcile_frame st1).1, hob, hgen, hstab]
              exact ⟨rfl, rfl, rfl, rfl⟩

variable {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
bp.reconcile.v1 on runs. T7.5 supplies the reachable store through Gen E-10;
F1.1 supplies CStoreInv. Admission preserves the pre-reconcile AC fields.
Gen AC.Reconcile describes the output clause; here all four edits are exact. -/
theorem fgsa_rRec : RRec p c E rho := by
  intro i x hx hmove
  obtain ⟨⟨o, t, he⟩, hF⟩ := hmove
  have hn : V2.D.Run.stateBefore E rho (i + 1) x =
      (fgsa p c).process (V2.D.Run.stateBefore E rho i x) o := by
    rw [V2.D.Run.stateBefore_succ E rho he]
    simp only [V2.D.World.step, Function.update_self]
  have hs : storeAt p c E rho (i + 1) x =
      FGSA.process p (storeAt p c E rho i x) (toWire p o) := congrArg Node.st hn
  have hr : (V2.D.Run.stateBefore E rho (i + 1) x).record =
      (V2.D.Run.stateBefore E rho i x).record := by
    rw [hn]
    rfl
  change (storeAt p c E rho i x).fg.F ≠ (storeAt p c E rho (i + 1) x).fg.F at hF
  rw [hs] at hF ⊢
  suffices hedits :
      let st := storeAt p c E rho i x
      let st' := FGSA.process p st (toWire p o)
      st'.base.obligations = st.base.obligations.filter (fun row => activeCompatible st' row.1) ∧
      st'.base.genuine = st.base.genuine.map
        (fun row => (row.1, row.2.filter (activeCompatible st'))) ∧
      st'.fastWrite = st.fastWrite.map
        (fun row => (row.1, row.2.filter (activeCompatible st'))) ∧
      st'.base.stableRecord =
        (if Block.preceq (eraseFG st'.fg.F) st.base.stableRecord then st.base.stableRecord
         else eraseFG st'.fg.F) from
    ⟨hedits.1, hedits.2.1, hedits.2.2.1, hedits.2.2.2,
      hr, fun u => reconcile_eq u⟩
  have h := (fgsa_rStore p c E rho i x hx).1
  generalize hw : toWire p o = w at hF ⊢
  obtain ⟨auth, msg⟩ := w
  cases auth with
  | none => cases msg <;> exact (hF rfl).elim
  | proposer s =>
      cases msg with
      | head b => exact (hF rfl).elim
      | row body => exact (hF rfl).elim
      | proposal N =>
          exact fgsa_block_reconcile_edits p _ h s N hF
  | seat label k =>
      cases label with
      | head s =>
          cases msg with
          | head b =>
              change (storeAt p c E rho i x).fg.F ≠ (admitHead p _ s k b).fg.F at hF
              rw [admitHead_fg] at hF
              exact (hF rfl).elim
          | proposal N => exact (hF rfl).elim
          | row body => exact (hF rfl).elim
      | fg =>
          cases msg with
          | head b => exact (hF rfl).elim
          | proposal N => exact (hF rfl).elim
          | row body =>
              change (storeAt p c E rho i x).fg.F ≠
                (admitRow p _ ⟨.seat .fg k, body⟩).fg.F at hF
              rcases admitRow_eq p (storeAt p c E rho i x) _ with he | he <;>
                rw [he] at hF <;> exact (hF rfl).elim

end AvailableChain.FGSA.Run
end
