module
public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryScope
public import AvailableChainFGSAProofs.Proofs.Shared.AnchorService

public import AvailableChainFGSAProofs.Proofs.Healing.Frame
public import AvailableChainFGSAProofs.Proofs.Shared.ProposalRead
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseRelay
public import AvailableChainFGSAProofs.Proofs.Healing.ReceiptProducers
public import AvailableChainFGSAProofs.Proofs.Healing.SupportFrame

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {G ΔF : Time}

/-- Recovery serves the jointly selected HEAD carrier and its actual direct target. -/
theorem healing_selected_carriers_recovery (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (s : Slot) (iy : Nat) (y : V) (t : Time) :
    HealingCarriersAt E rho s iy y t := by
  intro hSync hRead hDeadline hhor j z hz hj hJoin
  have hpub : V2.PublicTime E (SA.voteTime p.toParams s) := by
    refine ⟨4 * s + 1, ?_⟩
    rw [hrec.base.delta]
    change 4 * p.Δ * (s : Int) + p.Δ = ((4 * s + 1 : Nat) : Int) * p.Δ
    push_cast
    ring
  have service (W : FGBlock (Fin p.n)) (hW : W ∈ (storeAt p c E rho j z).fg.TF)
      (hCompat : Block.Compatible (eraseFG W)
        (eraseFG (rho.stateBeforeTime E (SA.voteTime p.toParams s + p.Δ) y).st.fg.F)) :
      TargetReceiptService E rho (eraseFG W) (SA.voteTime p.toParams s + p.Δ) y :=
    healing_target_service_of_tick E rho hrec hz hRead.1 hj
      (((storeBundle_stateBefore E rho j z).cstore.baseTree _).mpr ⟨W, hW, rfl⟩)
      hpub hSync (hDeadline.trans hhor) hCompat
  constructor
  · intro demand
    obtain ⟨K, hK, he, W, hW, hKW, hlo, hCompat⟩ := demand.witness
    have hW0 : W ∈ (storeAt p c E rho j z).fg.TF := by
      change W ∈ (clock p (storeAt p c E rho j z) _).fg.TF at hW
      rwa [clock_fg] at hW
    exact ⟨⟨K, hK, he, W, hW, hKW, hlo, hCompat, service W hW0 hCompat⟩⟩
  · intro K hK he hFloor
    exact service K hK (Bool.or_eq_true_iff.mpr (Or.inr hFloor))

/-- Select one source HEAD witness and serve it only under each receiver's floor. -/
theorem healing_head_witness_receipts_recovery (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho)
    {i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hSync : E.t_GST ≤ SA.voteTime p.toParams s)
    (hhor : SA.voteTime p.toParams s + p.Δ ≤ rho.horizon) :
    HeadWitnessReceiptScope E rho i x s := by
  obtain ⟨K, hK, heK, W, hW, hKW, hlo⟩ := healing_full_witness_all p c E rho
    hrec.base.valid.toScheduleWellFormed crossing hx hi
  have hW0 : W ∈ (storeAt p c E rho i x).fg.TF := by
    change W ∈ (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)).fg.TF at hW
    rwa [clock_fg] at hW
  refine ⟨K, hK, heK, W, hW0, hKW, ?_, ?_⟩
  · change (controls p (clock p (storeAt p c E rho i x)
      (SA.voteTime p.toParams s))).lo ≤ _ at hlo
    have he : controls p (clock p (storeAt p c E rho i x)
        (SA.voteTime p.toParams s)) = R_at p c E rho i x := by
      change KitFG.treeStoreControlsView (heightView p) (clock p _ _).fg = _
      rw [clock_fg]
      rfl
    exact he ▸ hlo
  · constructor
    intro iy y t hy _ _ _ hf
    have hpub : V2.PublicTime E (SA.voteTime p.toParams s) := by
      refine ⟨4 * s + 1, ?_⟩
      rw [hrec.base.delta]
      change 4 * p.Δ * (s : Int) + p.Δ = _
      push_cast; ring
    exact healing_target_service_of_tick E rho hrec hx hy hi
      (((storeBundle_stateBefore E rho i x).cstore.baseTree _).mpr ⟨W, hW0, rfl⟩)
      hpub hSync hhor (block_compatible_of_common (block_preceq_refl _) hf)

/-- The joined recurrence supplies the proposal gap on the healing start domain. -/
theorem healing_proposal_gap (hrec : RecoverySleep₂ p c E rho G ΔF) :
    ProposalGap p c E rho G := by
  intro t hready hhor
  obtain ⟨s, hlo, hhi, hs, _⟩ := hrec.joinedGap t hready hhor
  exact ⟨s, hlo, hhi, hs⟩

/-- An original proposal acceptance gives receiver service in the recovery epoch.
The acceptance keeps its source index and time. The local anchor can be later.
Proposal history is durable; the receiver epoch extends through its freeze. -/
theorem healing_accepted_proposal_service (hrec : RecoverySleep₂ p c E rho G ΔF)
    {k : Nat} {v x : V} {s : Slot} {N : NamedProposal p.n} {send a freeze : Time}
    (hv : v ∈ rho.honest) (hx : x ∈ rho.honest)
    (hacc : V2.D.Run.acceptsAt E rho k v (ofWire p ⟨.proposer s, .proposal N⟩) send)
    (hsa : send ≤ a) (ha : 0 ≤ a) (hpub : V2.PublicTime E a)
    (hgst : E.t_GST ≤ a) (haf : a + p.Δ ≤ freeze) (hfh : freeze ≤ rho.horizon)
    (hexclude : (fgsa p c).excludes (rho.stateBeforeTime E (a + p.Δ) x)
      (ofWire p ⟨.proposer s, .proposal N⟩) = false) :
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩) send freeze x) := by
  have hd : (toWire p (ofWire p ⟨.proposer s, .proposal N⟩)).decode = some (.block s N) := by
    rw [toWire_ofWire]
    rfl
  have had : a < a + p.Δ := lt_add_of_pos_right a p.deltaPos
  have hh : a + p.Δ ≤ rho.horizon := haf.trans hfh
  have handlers := fgsa_proposal_handlers_at_anchor hrec.base.valid hrec.base.delta hx
    hd hacc hsa ha hpub (hrec.awake x hx a hgst (had.le.trans hh)) had hh
    (healing_recovery_action_epoch hrec hx hgst _)
  exact healing_recovery_receiverService E rho hrec _ send a freeze x hx hgst ha hsa haf hfh
    (Or.inr ⟨v, hv, k, hacc⟩) (fgsa_historySafeAt_of_proposal x _ a hd) handlers hexclude

/-- Accepted proposal service supplies the exact target, with its original acceptance. -/
theorem healing_accepted_target_service (hrec : RecoverySleep₂ p c E rho G ΔF)
    {k : Nat} {v x : V} {s : Slot} {N : NamedProposal p.n} {send a freeze : Time}
    (hv : v ∈ rho.honest) (hx : x ∈ rho.honest)
    (hacc : V2.D.Run.acceptsAt E rho k v (ofWire p ⟨.proposer s, .proposal N⟩) send)
    (hsa : send ≤ a) (ha : 0 ≤ a) (hpub : V2.PublicTime E a)
    (hgst : E.t_GST ≤ a) (haf : a + p.Δ ≤ freeze) (hfh : freeze ≤ rho.horizon)
    (hexclude : (fgsa p c).excludes (rho.stateBeforeTime E (a + p.Δ) x)
      (ofWire p ⟨.proposer s, .proposal N⟩) = false) :
    TargetReceiptService E rho N.erase freeze x :=
  fgsa_target_service_of_proposal E rho s N send freeze x
    (healing_accepted_proposal_service hrec hv hx hacc hsa ha hpub hgst haf hfh hexclude)

/-- Original emission supplies proposal transport without an acceptance-time rewrite.
The caller keeps the exact handler window and the receiver's finality exclusion. -/
theorem healing_emitted_proposal_service (hrec : RecoverySleep₂ p c E rho G ΔF)
    {i : Nat} {v x : V} {s : Slot} {N : NamedProposal p.n} {freeze : Time}
    (hv : v ∈ rho.honest) (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick v (SA.proposalTime p.toParams s)))
    (hem : ofWire p ⟨.proposer s, .proposal N⟩ ∈ rho.emitsAt E i)
    (hgst : E.t_GST ≤ SA.proposalTime p.toParams s)
    (haf : SA.proposalTime p.toParams s + p.Δ ≤ freeze) (hfh : freeze ≤ rho.horizon)
    (hhandlers : ∀ j t, SA.proposalTime p.toParams s ≤ t →
      t < SA.proposalTime p.toParams s + p.Δ →
      rho.handlesAt E j x (ofWire p ⟨.proposer s, .proposal N⟩) t →
      (fgsa p c).wellFormed (ofWire p ⟨.proposer s, .proposal N⟩) = true ∧
      (fgsa p c).depsPresent (rho.stateBefore E j x)
        (ofWire p ⟨.proposer s, .proposal N⟩) = true ∧
      fgsaTimely p (rho.stateBefore E j x) (ofWire p ⟨.proposer s, .proposal N⟩))
    (hexclude : (fgsa p c).excludes
      (rho.stateBeforeTime E (SA.proposalTime p.toParams s + p.Δ) x)
      (ofWire p ⟨.proposer s, .proposal N⟩) = false) :
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
      (SA.proposalTime p.toParams s) freeze x) := by
  have hd : (toWire p (ofWire p ⟨.proposer s, .proposal N⟩)).decode = some (.block s N) := by
    rw [toWire_ofWire]
    rfl
  exact healing_recovery_receiverService E rho hrec _ _ _ freeze x hx hgst
    (hgst.trans' E.t_GST_nonneg) le_rfl haf hfh (Or.inl ⟨v, hv, i, hi, hem⟩)
    (fgsa_historySafeAt_of_proposal x _ _ hd) hhandlers hexclude

/-- A fresh HEAD uses its original vote time and the receiver's action-cut epoch.
Its receipt proof replays HistorySafeAt from this exact emission. -/
theorem healing_emitted_head_service (hrec : RecoverySleep₂ p c E rho G ΔF)
    {i : Nat} {v x : V} {s : Slot} {q : Fin p.n} {b : BlockId} {freeze : Time}
    (hv : v ∈ rho.honest) (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick v (SA.voteTime p.toParams s)))
    (hem : ofHead p ⟨.seat (.head s) q, b⟩ ∈ rho.emitsAt E i)
    (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (haf : SA.voteTime p.toParams s + p.Δ ≤ freeze) (hfh : freeze ≤ rho.horizon)
    (hhandlers : ∀ j t, SA.voteTime p.toParams s ≤ t →
      t < SA.voteTime p.toParams s + p.Δ →
      rho.handlesAt E j x (ofHead p ⟨.seat (.head s) q, b⟩) t →
      (fgsa p c).wellFormed (ofHead p ⟨.seat (.head s) q, b⟩) = true ∧
      (fgsa p c).depsPresent (rho.stateBefore E j x)
        (ofHead p ⟨.seat (.head s) q, b⟩) = true ∧
      fgsaTimely p (rho.stateBefore E j x) (ofHead p ⟨.seat (.head s) q, b⟩))
    (hexclude : (fgsa p c).excludes
      (rho.stateBeforeTime E (SA.voteTime p.toParams s + p.Δ) x)
      (ofHead p ⟨.seat (.head s) q, b⟩) = false) :
    Nonempty (FreshHeadService E rho s q b freeze x) := by
  let dl := fun t => max t E.t_GST + p.Δ
  have hd : dl (SA.voteTime p.toParams s) = SA.voteTime p.toParams s + p.Δ :=
    congrArg (· + p.Δ) (max_eq_left hgst)
  have delay (o : Obj p) (hn : ¬ isRowObject o) : fgsaDelay E.Δ ΔF o = p.Δ := by
    rw [fgsaDelay_nonrow E.Δ ΔF o hn, hrec.base.delta]
  have within := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hrec.sync
    (fun o => ¬ isRowObject o) p.Δ delay
  have ready := healing_recovery_readyTrigger E rho hrec.toRecovery₂ _ _ _
    (SA.voteTime p.toParams s + p.Δ) x hx hgst (haf.trans hfh)
    (Or.inl ⟨v, hv, i, hi, hem⟩)
  refine ⟨⟨dl, rho.horizon, within, hd.symm ▸ ready,
    hd.symm ▸ lt_add_of_pos_right _ p.deltaPos, hd.symm ▸ haf.trans hfh,
    hd.symm ▸ haf.trans hfh, hd.symm ▸ haf,
    healing_recovery_action_epoch hrec hx hgst _, hd.symm ▸ hhandlers,
    hd.symm ▸ hexclude⟩⟩

/-- Recovery serves the actual emitted proposal at its own honest receiver. -/
theorem healing_self_proposal_service (hrec : RecoverySleep₂ p c E rho G ΔF)
    (s : Slot) (ip : Nat) (x : V) (N : NamedProposal p.n) (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hem : (ofWire p ⟨.proposer s, .proposal N⟩) ∈ rho.emitsAt E ip)
    (hSync : E.t_GST ≤ SA.proposalTime p.toParams s)
    (hhor : SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon)
    (hCompat : Block.Compatible N.erase (eraseFG (rho.stateBeforeTime E
      (SA.proposalTime p.toParams s + p.Δ) x).st.fg.F)) :
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
      (SA.proposalTime p.toParams s) (SA.proposalTime p.toParams s + p.Δ) x) := by
  have hD := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hrec.sync
    (fun o => ¬ isRowObject o) p.Δ (fun o hn => by
      rw [fgsaDelay_nonrow E.Δ ΔF o hn, hrec.base.delta])
  have he : max (SA.proposalTime p.toParams s) E.t_GST + p.Δ =
      SA.proposalTime p.toParams s + p.Δ := by rw [max_eq_left hSync]
  apply fgsa_proposal_service_of_emission hrec.base.valid hrec.base.delta
    (fun t => max t E.t_GST + p.Δ) rho.horizon hx hip hem hD
  · rw [he]; exact lt_add_of_pos_right _ p.deltaPos
  · simpa only [he] using hhor
  · simpa only [he] using hhor
  · exact he.le
  · intro t hlo hhi
    exact hrec.awake x hx t (hSync.trans hlo) (hhi.le.trans (he ▸ hhor))
  · exact healing_recovery_restartFree hrec hx hSync hhor
  · simpa only [he] using hCompat

omit [Fintype V] in
/-- A proposal parent in the fixed phase is above each receiver's current F.
The selected parent is retained at its source. RXing uses the receiver's actual
certificate; this does not assume that the parent is already held at the receiver. -/
theorem healing_proposal_phase_reader_floor (hvalid : V2.D.ExecutionValid E rho)
    (crossing : RXing p c E rho) {u v : Time} {m : Nat}
    {J : Option (FGBlock (Fin p.n))} {contested : Bool} {s : Slot} {Q : Block}
    (hp : PhaseInterval p c E rho u v m J contested)
    (hQ : HonestProposal E rho (fgsaInterface p c) s Q)
    (hu : u ≤ SA.proposalTime p.toParams s) (hv : SA.voteTime p.toParams s ≤ v)
    {y : V} (hy : y ∈ rho.honest) :
    Block.Preceq (eraseFG (rho.stateBeforeTime E (SA.voteTime p.toParams s) y).st.fg.F) Q := by
  have hs := hvalid.toScheduleWellFormed
  obtain ⟨j, N, heN, hj, hem, hst, _⟩ := proposal_read_named p c E rho hs hQ
  let x := V2.D.proposerOf rho (fgsaInterface p c) s
  let st := ((fgsa p c).clock (rho.stateBefore E j x) (SA.proposalTime p.toParams s)).st
  have hx : x ∈ rho.honest := hQ.1.2
  have ht : SA.proposalTime p.toParams s < SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) < 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  let iy := V2.D.Run.idxBefore rho (SA.voteTime p.toParams s)
  have hji : j ≤ iy :=
    ((Gen.V2.Duty.index_lt_idxBefore_iff hs hj _).mpr ht).le
  have hjv : j ≤ timeIdx rho v :=
    (healing_phase_lt_timeIdx p c E rho hs hj (ht.le.trans hv)).le
  have hjU : V2.D.Run.idxBefore rho u ≤ j :=
    by
      by_contra hn
      have hb := (Gen.V2.Duty.index_lt_idxBefore_iff hs hj u).mp (Nat.lt_of_not_ge hn)
      exact (not_lt_of_ge hu) hb
  have hiU : V2.D.Run.idxBefore rho u ≤ iy := hjU.trans hji
  have hiV : iy ≤ timeIdx rho v :=
    (fgsa_idxBefore_mono rho hv).trans (idxBefore_le_timeIdx rho v)
  have hfg : st.fg = (storeAt p c E rho j x).fg := clock_fg p _ _
  have hcontrols : controls p st = controls p (storeAt p c E rho j x) := by
    change KitFG.treeStoreControlsView (heightView p) st.fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho j x).fg
    rw [hfg]
  have hne : (fullTree p st).Nonempty := by
    change (KitFG.treeStoreFrameView (heightView p) st.fg st.fg.TF).Nonempty
    rw [hfg]
    obtain ⟨W, hW, hh⟩ := healing_phase_frontier_witness p c E rho j x
    obtain ⟨hF, hZ⟩ := healing_phase_frontier_root p c E rho crossing hx hW hh
    exact ⟨W, (KitFG.mem_filteredFromView _ _ _ _).mpr
      ⟨hW, hF, hZ, W, hW, KitFG.preceq_refl _, hh ▸ KitFG.Controls.lo_le_H _⟩⟩
  obtain ⟨B, hB, heB, hlo⟩ := healing_proposer_floor p c E rho hs s Q st hQ hst hne
  obtain ⟨hBT, _, hZB, _⟩ := (KitFG.mem_filteredFromView _ _ _ _).mp hB
  have hB0 : B ∈ (storeAt p c E rho j x).fg.TF := hfg ▸ hBT
  have hB1 : B ∈ (storeAt p c E rho iy x).fg.TF :=
    (fgsa_store_durable p c E rho hji x).1 hB0
  have hsFrame := healing_phase_frame p c E rho crossing hx hp.2.2.1
    (hp.2.2.2 j x hjU hjv hx).1 (hp.2.2.2 j x hjU hjv hx).2.1
    (hp.2.2.2 j x hjU hjv hx).2.2
  have hyFrame := healing_phase_frame p c E rho crossing hy hp.2.2.1
    (hp.2.2.2 iy y hiU hiV hy).1 (hp.2.2.2 iy y hiU hiV hy).2.1
    (hp.2.2.2 iy y hiU hiV hy).2.2
  have hF : FGBlock.Preceq (storeAt p c E rho iy y).fg.F B := by
    cases J with
    | some A =>
      obtain ⟨_, _, hZ, _, _, _⟩ := hsFrame.2.2.2.1
      obtain ⟨_, _, _, _, _, hFA⟩ := hyFrame.2.2.2.1
      have hZB0 : FGBlock.Preceq (controls p (storeAt p c E rho j x)).Z B := by
        change FGBlock.Preceq (controls p st).Z B at hZB
        rw [hcontrols] at hZB
        exact hZB
      rw [hZ] at hZB0
      exact KitFG.preceq_trans hFA hZB0
    | none =>
      obtain ⟨_, _, ⟨K, hK, hKF, hKh⟩, _⟩ := hyFrame.2.2.2.1
      have hlo0 : (if contested then m else m - 1) ≤ (heightView p B).h := by
        change (controls p st).lo ≤ _ at hlo
        have hloEq : (controls p st).lo = (if contested then m else m - 1) := by
          rw [hcontrols]
          exact hsFrame.2.2.1
        exact hloEq ▸ hlo
      rw [hyFrame.2.2.1] at hKh
      exact crossing iy iy y x K B hy le_rfl hK hKF ⟨hx, hB1⟩ (hKh.trans_le hlo0)
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
  have hF' := eraseFG_preceq hF
  rw [heB] at hF'
  apply Gen.Pure.block_preceq_trans hF'
  cases Q with
  | genesis => exact Gen.Pure.block_preceq_refl _
  | node P s root body => exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_preceq_refl P))

omit [Fintype V] in
/-- A selected high witness remains at its source while the receiver's F can move.
The receiver cap and its current certificate establish the floor before receipt. -/
theorem healing_capped_witness_reader_floor (crossing : RXing p c E rho)
    {i j : Nat} {x y : V} {W : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) (hij : i ≤ j)
    (hW : W ∈ (storeAt p c E rho i x).fg.TF)
    (hcap : (storeAt p c E rho j y).fg.h_max ≤ (heightView p W).h) :
    FGBlock.Preceq (storeAt p c E rho j y).fg.F W := by
  have hW' := (fgsa_store_durable p c E rho hij x).1 hW
  obtain ⟨K, hK, hKF⟩ := (storeBundle_stateBefore E rho j y).cstore.fg.Fcar
  have hlt := (healing_phase_finality_le p c E rho hK hKF).trans_lt
    ((healing_phase_justified_lt p c E rho j y).trans_le hcap)
  exact crossing j j y x K W hy le_rfl hK hKF ⟨hx, hW'⟩ hlt

end AvailableChain.FGSA.Run
end
