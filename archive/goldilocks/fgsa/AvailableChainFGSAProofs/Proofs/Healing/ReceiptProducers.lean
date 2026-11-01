module
public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryScope
public import AvailableChainFGSAProofs.Proofs.Healing.SupportRecovery
public import AvailableChainFGSAProofs.Proofs.Shared.AnchorService
public import AvailableChainFGSAProofs.Proofs.Shared.SameLabel

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

/-- A selected stored target is served from its original proposal acceptance.
The public post-GST anchor and the receiver floor bound the finite service. -/
theorem healing_target_service_of_stored (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {i : Nat} {v x : V} {K : Block} {a : Time}
    (hv : v ∈ rho.honest) (hx : x ∈ rho.honest)
    (hK : K ∈ (storeAt p c E rho i v).base.blocks)
    (hStamp : GridCO.stampBlock (storeAt p c E rho i v).base K < a)
    (hpub : V2.PublicTime E a) (hSync : E.t_GST ≤ a)
    (hhor : a + p.Δ ≤ rho.horizon)
    (hCompat : Block.Compatible K (eraseFG (rho.stateBeforeTime E (a + p.Δ) x).st.fg.F)) :
    TargetReceiptService E rho K (a + p.Δ) x := by
  by_cases hg : K = .genesis
  · exact hg ▸ fgsa_target_service_genesis E rho _ x
  have ha : 0 ≤ a := E.t_GST_nonneg.trans hSync
  obtain ⟨k, _, send, o, hb, hacc, hsend⟩ := fgsa_block_accepted_before E rho
    hrec.base.valid i v K a hg hpub ha hK hStamp
  dsimp only [blockOf?] at hb
  cases hd : (toWire p o).decode with
  | none => simp only [hd, reduceCtorEq] at hb
  | some m =>
    cases m with
    | vote r q b => simp only [hd, reduceCtorEq] at hb
    | row q body => simp only [hd, reduceCtorEq] at hb
    | block s N =>
      simp only [hd, Option.some.injEq] at hb
      have ho : o = ofWire p ⟨.proposer s, .proposal N⟩ := by
        apply toWire_injective
        rw [toWire_ofWire]
        exact decode_eq_block.mp hd
      have hD := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hrec.sync
        (fun o => ¬ isRowObject o) p.Δ (fun o hn => by
          rw [fgsaDelay_nonrow E.Δ ΔF o hn, hrec.base.delta])
      have he : max a E.t_GST + p.Δ = a + p.Δ := by rw [max_eq_left hSync]
      have hRF := healing_recovery_restartFree hrec hx hSync hhor
      have hs := fgsa_proposal_service_at_anchor hrec.base.valid hrec.base.delta
        (fun t => max t E.t_GST + p.Δ) rho.horizon hv hx (ho ▸ hacc) hD hsend.le ha hpub
        (he ▸ lt_add_of_pos_right a p.deltaPos) (he ▸ hhor) (he ▸ hhor) he.le
        (by intro t hat htd; exact hrec.awake x hx t (hSync.trans hat) (htd.le.trans
            (he ▸ hhor))) hRF (by simpa only [he, hb] using hCompat)
      rw [← hb]
      exact fgsa_target_service_of_proposal E rho s N send _ x hs

/-- A selected body at a source tick has its strict source stamp.
This receipt keeps pre-GST proposal history while using the recovery epoch. -/
theorem healing_target_service_of_tick (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {i : Nat} {v x : V} {K : Block} {a : Time}
    (hv : v ∈ rho.honest) (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick v a))
    (hK : K ∈ (storeAt p c E rho i v).base.blocks)
    (hpub : V2.PublicTime E a) (hSync : E.t_GST ≤ a)
    (hhor : a + p.Δ ≤ rho.horizon)
    (hCompat : Block.Compatible K (eraseFG (rho.stateBeforeTime E (a + p.Δ) x).st.fg.F)) :
    TargetReceiptService E rho K (a + p.Δ) x := by
  by_cases hg : K = .genesis
  · exact hg ▸ fgsa_target_service_genesis E rho _ x
  have hS := hrec.base.valid.toScheduleWellFormed
  obtain ⟨k, hki, send, o, hb, hacc⟩ := fgsa_block_accepted_origin E rho i v K hg hK
  obtain ⟨parent, hk, _⟩ := hacc.1
  obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hkey := List.pairwise_iff_getElem.mp hS.sorted k i hkl hil hki
  rw [hke, hie] at hkey
  have hsend : send < a := by
    change toLex (send, 2) ≤ toLex (a, 1) at hkey
    rcases Prod.Lex.toLex_le_toLex.mp hkey with hlt | ⟨_, hphase⟩
    · exact hlt
    · omega
  dsimp only [blockOf?] at hb
  cases hd : (toWire p o).decode with
  | none => simp only [hd, reduceCtorEq] at hb
  | some m =>
    cases m with
    | vote r q b => simp only [hd, reduceCtorEq] at hb
    | row q body => simp only [hd, reduceCtorEq] at hb
    | block s N =>
      simp only [hd, Option.some.injEq] at hb
      have ho : o = ofWire p ⟨.proposer s, .proposal N⟩ := by
        apply toWire_injective
        rw [toWire_ofWire]
        exact decode_eq_block.mp hd
      have hD := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hrec.sync
        (fun o => ¬ isRowObject o) p.Δ (fun o hn => by
          rw [fgsaDelay_nonrow E.Δ ΔF o hn, hrec.base.delta])
      have he : max a E.t_GST + p.Δ = a + p.Δ := by rw [max_eq_left hSync]
      have hs := fgsa_proposal_service_at_anchor hrec.base.valid hrec.base.delta
        (fun t => max t E.t_GST + p.Δ) rho.horizon hv hx (ho ▸ hacc) hD hsend.le
        (E.t_GST_nonneg.trans hSync) hpub (he ▸ lt_add_of_pos_right a p.deltaPos)
        (he ▸ hhor) (he ▸ hhor) he.le
        (by intro t hat htd; exact hrec.awake x hx t (hSync.trans hat) (htd.le.trans
            (he ▸ hhor)))
        (healing_recovery_restartFree hrec hx hSync hhor)
        (by simpa only [he, hb] using hCompat)
      rw [← hb]
      exact fgsa_target_service_of_proposal E rho s N send _ x hs

/-- A fresh honest HEAD has a recovery service from its actual vote time. -/
theorem healing_fresh_head_service (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot} {q : Fin p.n} {b : BlockId}
    {x : V} {freeze : Time} (hx : x ∈ rho.honest)
    (hh : rho.seatOf (.base (.head s)) q ∈ rho.honest)
    (hem : V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
      (ofHead p ⟨.seat (.head s) q, b⟩) (SA.voteTime p.toParams s))
    (hSync : E.t_GST ≤ SA.voteTime p.toParams s)
    (hef : SA.earlyTime p.toParams s ≤ freeze) (hhor : freeze ≤ rho.horizon) :
    Nonempty (FreshHeadService E rho s q b freeze x) := by
  let dl := fun t => max t E.t_GST + p.Δ
  have he : dl (SA.voteTime p.toParams s) = SA.earlyTime p.toParams s := by
    dsimp only [dl]
    rw [max_eq_left hSync]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 2 * p.Δ
    ring
  have hve : SA.voteTime p.toParams s < SA.earlyTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ < 4 * p.Δ * (s : Int) + 2 * p.Δ
    linarith [p.deltaPos]
  have hp0 : 0 ≤ SA.proposalTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int)
    have := p.deltaPos
    positivity
  have hpub : V2.PublicTime E (SA.proposalTime p.toParams s) := by
    refine ⟨4 * s, ?_⟩
    rw [hrec.base.delta]
    change 4 * p.Δ * (s : Int) = ((4 * s : Nat) : Int) * p.Δ
    push_cast
    ring
  have hD := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hrec.sync
    (fun o => ¬ isRowObject o) p.Δ (fun o hn => by
      rw [fgsaDelay_nonrow E.Δ ΔF o hn, hrec.base.delta])
  refine ⟨{
    dl := dl, cut := rho.horizon, within := hD
    ready := ⟨_, hh, Or.inl hem, ?_⟩
    later := he ▸ hve, cut_le := he ▸ hef.trans hhor
    horizon := he ▸ hef.trans hhor, freeze_le := he ▸ hef
    epoch := healing_recovery_restartFree hrec hx hSync hhor
    handlers := ?_
    not_excluded := ?_ }⟩
  · intro t hvt htd
    exact hrec.awake x hx t (hSync.trans hvt) (htd.le.trans (he ▸ hef.trans hhor))
  · intro j t hvt htd hcall
    have hhcall := hcall
    obtain ⟨parent, hj, _⟩ := hcall
    have hdeps := fgsa_hReady_of_not_block (by intro r N h; cases h)
      (fgsa_hWF_of_delivery hrec.base.valid.wire) j t
      ((Gen.V2.Duty.index_lt_idxBefore_iff hrec.base.valid.toScheduleWellFormed hj _).mpr htd)
      hhcall
    refine ⟨hdeps.1, hdeps.2, ?_⟩
    have hpt : SA.proposalTime p.toParams s ≤ t := by
      apply le_trans _ hvt
      change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
      linarith [p.deltaPos]
    have hb := V2.D.Engine.delivery_now_ge_public_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho hrec.base.valid hj hpub hp0 hpt
    change SA.proposalTime p.toParams s ≤ (rho.stateBefore E j x).st.base.now
    rw [fgsa_clock_now p c (rho.stateBefore E j x)] at hb
    exact hb
  · apply fgsa_honest_head_not_excluded E rho hrec.base.valid hh hem
    have hn := fgsa_clock_before_time_le hrec.base.valid.toScheduleWellFormed x
      (dl (SA.voteTime p.toParams s)) (by
        rw [he]
        change 0 ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
        have := p.deltaPos
        positivity)
    apply le_trans (Internal.slotOf_mono (p := p) hn)
    rw [he]
    have hs : p.slotOf (SA.earlyTime p.toParams s) = s :=
      slotOf_offset p s (2 * p.Δ) (by linarith [p.deltaPos]) (by linarith [p.deltaPos])
    rw [hs]
    exact Nat.le_succ s

omit [Fintype V] in
/-- The named monotonicity producer pulls an actual reader floor to an earlier cut. -/
theorem healing_receipt_floor_before_tick (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hS : V2.D.ScheduleWellFormed E rho)
    (mono : RMonoAll p c E rho) {i : Nat} {x : V} {t d : Time} {K : Block}
    (hx : x ∈ rho.honest) (hi : rho.events[i]? = some (.tick x t))
    (hd : d ≤ t) (hFloor : Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) K) :
    Block.Preceq (eraseFG (rho.stateBeforeTime E d x).st.fg.F) K := by
  have hid : V2.D.Run.idxBefore rho d ≤ i := by
    by_contra hn
    exact (not_lt.mpr hd) ((Gen.V2.Duty.index_lt_idxBefore_iff hS hi d).mp
      (Nat.lt_of_not_ge hn))
  have hm := eraseFG_preceq (mono _ i x hx hid).1
  change Block.Preceq (eraseFG (rho.stateBefore E (V2.D.Run.idxBefore rho d) x).st.fg.F)
    (eraseFG (storeAt p c E rho i x).fg.F) at hm
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho d hS] at hm
  exact Gen.Pure.block_preceq_trans hm hFloor

/-- An actual emitted proposal is served at the joined repair reader.
Its exact body floor is pulled back from that reader's vote cut. -/
theorem healing_retained_proposal_service (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {ip : Nat} {x y : V} {s : Slot}
    {N : NamedProposal p.n} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hem : ofWire p ⟨.proposer s, .proposal N⟩ ∈ rho.emitsAt E ip)
    (hSync : E.t_GST ≤ SA.proposalTime p.toParams s)
    (hhor : SA.voteTime p.toParams s ≤ rho.horizon)
    (hFloor : Block.Preceq (eraseFG (rho.stateBeforeTime E
      (SA.voteTime p.toParams s) y).st.fg.F) N.erase) :
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
      (SA.proposalTime p.toParams s) (SA.voteTime p.toParams s) y) := by
  let dl := fun t => max t E.t_GST + p.Δ
  have he : dl (SA.proposalTime p.toParams s) = SA.voteTime p.toParams s := by
    dsimp only [dl]
    rw [max_eq_left hSync]
    rfl
  have hD := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hrec.sync
    (fun o => ¬ isRowObject o) p.Δ (fun o hn => by
      rw [fgsaDelay_nonrow E.Δ ΔF o hn, hrec.base.delta])
  apply fgsa_proposal_service_of_emission hrec.base.valid hrec.base.delta dl rho.horizon
    hx hip hem hD
  · rw [he]
    exact lt_add_of_pos_right _ p.deltaPos
  · exact he ▸ hhor
  · exact he ▸ hhor
  · exact he.le
  · intro t hat htd
    exact hrec.awake y hy t (hSync.trans hat) (htd.le.trans (he ▸ hhor))
  · exact healing_recovery_restartFree hrec hy hSync hhor
  · rw [he]
    exact Bool.or_eq_true_iff.mpr (Or.inr hFloor)

/-- A selected stored HEAD uses its actual acceptance before a public anchor. -/
theorem healing_stored_head_service (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {i : Nat} {v x : V} {s : Slot}
    {q : Fin p.n} {b : BlockId} {a freeze : Time}
    (hv : v ∈ rho.honest) (hx : x ∈ rho.honest)
    (hm : (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∈
      (storeAt p c E rho i v).base.votes)
    (hStamp : GridCO.stampVote (storeAt p c E rho i v).base ⟨.seat s q, .head b⟩ < a)
    (hSync : E.t_GST ≤ SA.proposalTime p.toParams s)
    (hpa : SA.proposalTime p.toParams s ≤ a) (hpub : V2.PublicTime E a)
    (hdf : a + p.Δ ≤ freeze) (hhor : freeze ≤ rho.horizon)
    (hNX : (fgsa p c).excludes (rho.stateBeforeTime E (a + p.Δ) x)
      (ofHead p ⟨.seat (.head s) q, b⟩) = false) :
    ∃ send, Nonempty (ReceiverService E rho (ofHead p ⟨.seat (.head s) q, b⟩)
      send freeze x) := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hp0 : 0 ≤ SA.proposalTime p.toParams s := E.t_GST_nonneg.trans hSync
  have hpubP : V2.PublicTime E (SA.proposalTime p.toParams s) := by
    refine ⟨4 * s, ?_⟩
    rw [hrec.base.delta]
    change 4 * p.Δ * (s : Int) = ((4 * s : Nat) : Int) * p.Δ
    push_cast
    ring
  have hph : SA.proposalTime p.toParams s ≤ rho.horizon :=
    hpa.trans ((le_add_of_nonneg_right p.deltaPos.le).trans (hdf.trans hhor))
  have tick (z : V) (hz : z ∈ rho.honest) :
      ∃ j : Nat, rho.events[j]? = some (V2.Event.tick z (SA.proposalTime p.toParams s)) :=
    List.mem_iff_getElem?.mp (hrec.base.valid.tick_total z hz _ hpubP hp0 hph
      (hrec.awake z hz _ hSync hph))
  obtain ⟨iv, hiv⟩ := tick v hv
  obtain ⟨j, _, send, hacc, hsend⟩ := fgsa_vote_accepted_before_local E rho hrec.base.valid
    hrec.base.restartsAtWakes s hiv
    (fun k w _ hk => (healing_recovery_restart_bound E rho hrec hv hk).trans hSync)
    q b a hpub (hp0.trans hpa) hm hStamp
  obtain ⟨ix, hix⟩ := tick x hx
  have hist := fgsa_head_historySafeAt_of_tick E rho hrec.base.valid
    hrec.base.restartsAtWakes (a := a) hix
    (fun k w _ hk => (healing_recovery_restart_bound E rho hrec hx hk).trans hSync) q b
  let dl := fun t => max t E.t_GST + p.Δ
  have he : dl a = a + p.Δ := by dsimp only [dl]; rw [max_eq_left (hSync.trans hpa)]
  have hD := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hrec.sync
    (fun o => ¬ isRowObject o) p.Δ (fun o hn => by
      rw [fgsaDelay_nonrow E.Δ ΔF o hn, hrec.base.delta])
  refine ⟨send, fgsa_head_service_at_anchor hrec.base.valid hrec.base.delta dl rho.horizon hx
    (Or.inr ⟨v, hv, j, hacc⟩) hD hsend.le (hp0.trans hpa) hpa
    (he ▸ lt_add_of_pos_right a p.deltaPos) (he ▸ hdf.trans hhor) (he ▸ hdf.trans hhor)
    (he ▸ hdf) ?_ hist (healing_recovery_restartFree hrec hx (hSync.trans hpa) hhor)
    (he ▸ hNX)⟩
  intro t hat htd
  exact hrec.awake x hx t ((hSync.trans hpa).trans hat)
    (htd.le.trans (he ▸ hdf.trans hhor))

/-- A selected target held at an earlier actual tick uses a later recovery anchor. -/
theorem healing_target_service_of_earlier_tick (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {i : Nat} {v x : V} {K : Block} {t a : Time}
    (hv : v ∈ rho.honest) (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick v t))
    (hK : K ∈ (storeAt p c E rho i v).base.blocks) (hta : t < a)
    (hpub : V2.PublicTime E a) (hSync : E.t_GST ≤ a)
    (hhor : a + p.Δ ≤ rho.horizon)
    (hCompat : Block.Compatible K (eraseFG (rho.stateBeforeTime E (a + p.Δ) x).st.fg.F)) :
    TargetReceiptService E rho K (a + p.Δ) x := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hid := ((Gen.V2.Duty.index_lt_idxBefore_iff hS hi a).mpr hta).le
  have hm := (fgsa_store_durable p c E rho hid v).2.1.subset hK
  change K ∈ (rho.stateBefore E (V2.D.Run.idxBefore rho a) v).st.base.blocks at hm
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho a hS] at hm
  have hStamp := fgsa_block_stamp_before_read E rho hS v a
    ((hrec.base.valid.in_horizon _ (List.mem_of_getElem? hi)).1.trans_lt hta) K hm
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho a hS] at hm hStamp
  exact healing_target_service_of_stored E rho hrec hv hx hm hStamp hpub hSync hhor hCompat

end AvailableChain.FGSA.Run
end
