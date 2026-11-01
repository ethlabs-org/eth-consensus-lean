module
public import AvailableChainFGSAProofs.Proofs.Shared.StoreRun
public import AvailableChainFGSAProofs.Proofs.Shared.Channels
public import AvailableChainFGSAClaims.Statements.Channels
public import AvailableChainFGSARun.Proofs.Receipts -- shake: keep (receipt API)

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

theorem rowService_carrier_read {s : Slot} {Q : Block} {rows : List (RowWire p.n)}
    (hs : V2.D.ScheduleWellFormed E rho) (hc : HonestCarrier p c E rho s Q rows) :
    ∃ j, rho.events[j]? = some (.tick (V2.D.proposerOf rho (fgsaInterface p c) s)
        (SA.proposalTime p.toParams s)) ∧
      let st := ((fgsa p c).clock
        (V2.D.Run.stateBefore E rho j (V2.D.proposerOf rho (fgsaInterface p c) s))
        (SA.proposalTime p.toParams s)).st
      proposalStateAt p c E rho s = some st ∧ st.slot p = s ∧
        rows = proposalRows p st Q.parent := by
  obtain ⟨hp, o, N, ⟨j, hj, hem⟩, hpay, heN, hrows⟩ := hc
  subst Q rows
  have hs0 : 0 < s := hp.1.1
  change rho.events[j]? = some (.tick _ (SA.proposalTime p.toParams s)) at hj
  rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem
  obtain ⟨auth, m⟩ := o
  change m = _ at hpay
  subst m
  cases auth with
  | none =>
    change (⟨.none, _⟩ : Obj p) ∈ (if E.awake _ _ then
      (duties p _).flatMap (fun d => (rho.ownSeats (RunDuty.signLabel d) _).filterMap
        (fun i => ((fgsa p c).act ((fgsa p c).clock _ _) d (rho.input _ _)).map
          (fun m => ⟨.seat (RunDuty.signLabel d) i, m⟩))) ++ [] else []) at hem
    split at hem
    · rw [List.append_nil] at hem
      obtain ⟨d, _, hm⟩ := List.mem_flatMap.mp hem
      obtain ⟨i, _, hm⟩ := List.mem_filterMap.mp hm
      obtain ⟨m, _, he⟩ := Option.map_eq_some_iff.mp hm
      cases he
    · exact (List.not_mem_nil hem).elim
  | seat l seat =>
    obtain ⟨_, _, d, _, ht, hm⟩ :=
      (V2.D.Engine.mem_tick_seat_iff E rho _ _ _ l seat _).mp hem
    cases d with
    | headAction v =>
      change (if joinedNow p _ then some (Msg.head _) else none) = some (Msg.proposal N) at hm
      split_ifs at hm; cases hm
    | fgAction r =>
      change (attest p _ _ _).1.map Msg.row = some (.proposal N) at hm
      obtain ⟨body, _, he⟩ := Option.map_eq_some_iff.mp hm
      cases he
    | propAction s' =>
      have hss : s' = s := by
        change 4 * p.Δ * (s' : Int) = 4 * p.Δ * (s : Int) at ht
        have hΔ : (0 : Int) < p.Δ := p.deltaPos
        have he : (s' : Int) = s := by nlinarith
        exact_mod_cast he
      subst s'
      let nd := V2.D.Run.stateBefore E rho j
        (V2.D.proposerOf rho (fgsaInterface p c) s)
      let st := ((fgsa p c).clock nd (SA.proposalTime p.toParams s)).st
      have htick : V2.D.Run.tickIdx? rho (V2.D.proposerOf rho (fgsaInterface p c) s)
          (SA.proposalTime p.toParams s) = some j := by
        obtain ⟨k, hk⟩ : ∃ k, V2.D.Run.tickIdx? rho
            (V2.D.proposerOf rho (fgsaInterface p c) s)
            (SA.proposalTime p.toParams s) = some k := by
          rw [V2.D.Run.tickIdx?, ← Option.isSome_iff_exists, List.findIdx?_isSome, List.any_eq_true]
          exact ⟨_, List.mem_of_getElem? hj, by simp⟩
        exact (fgsa_tick_unique E rho hs (V2.D.Run.tickIdx?_spec hk) hj) ▸ hk
      refine ⟨j, hj, ?_, fgsa_proposal_slot nd s, ?_⟩
      · change (postClock E rho _ _).map (·.st) = some st
        rw [proposalTime_fgsa p c s, postClock_def, preTick_def]
        change (((V2.D.Run.tickIdx? rho _ (SA.proposalTime p.toParams s)).map
          (fun k => V2.D.Run.stateBefore E rho k _)).map
          (fun nd : Node p => (fgsa p c).clock nd (SA.proposalTime p.toParams s))).map
          (fun nd : Node p => nd.st) = some st
        rw [htick]
        rfl
      · change (if joinedNow p st then
          (propose p st s).map (withApp p _) else none) = some (.proposal N) at hm
        split_ifs at hm with hjoin
        rw [propose_head p st s (Nat.ne_of_gt hs0)] at hm
        simp only [Option.map_map] at hm
        obtain ⟨P, hP, he⟩ := Option.map_eq_some_iff.mp hm
        cases Msg.proposal.inj he
        have hparent := (namedByErase?_sound st (proposerHead p st s) P hP).2
        change proposalRows p st (proposerHead p st s) = proposalRows p st P.erase
        rw [hparent]

theorem rowService_chain_occurrence (st : State p.n) (hmeta : MetaInv p st)
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
    refine ⟨W, eraseFG_preceq_iff.mp ?_, ?_⟩
    · rwa [hWe]
    · rw [hWr]
      exact List.mem_filterMap.mpr ⟨a, ha, hd⟩
  next hpath => cases hrows

theorem batch_proposal_read (s : Slot) (st : State p.n)
    (hs : proposalStateAt p c E rho s = some st) :
    ∃ k, st = ((fgsa p c).clock
      (V2.D.Run.stateBefore E rho k (V2.D.proposerOf rho (fgsaInterface p c) s))
      (V2.D.proposalTime (fgsaInterface p c) s)).st := by
  change (postClock E rho _ _).map (·.st) = some st at hs
  rw [postClock_def, preTick_def] at hs
  cases hk : V2.D.Run.tickIdx? rho (V2.D.proposerOf rho (fgsaInterface p c) s)
      (V2.D.proposalTime (fgsaInterface p c) s) with
  | none => rw [hk] at hs; cases hs
  | some k =>
      rw [hk] at hs
      exact ⟨k, (Option.some.inj hs).symm⟩

theorem heldBefore_at_proposal (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) {s : Slot} {a : RowWire p.n} {d : Time} {st : State p.n}
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
    have hcumul := fgsa_store_cumulative p c E rho hnr hik
      (V2.D.proposerOf rho (fgsaInterface p c) s)
    rw [← hst']
    rcases hheld with hp | hb
    · left
      change a ∈ (FGSA.clock p (V2.D.Run.stateBefore E rho k _).st _).rowPool
      rw [clock_rowPool]
      exact hcumul.2.2.2.2.2.subset hp
    · right
      change a ∈ allBlockRows _ at hb
      change a ∈ allBlockRows (FGSA.clock p (V2.D.Run.stateBefore E rho k _).st _)
      unfold allBlockRows at hb ⊢
      rw [clock_proposals]
      obtain ⟨xs, hxs, ha⟩ := List.mem_flatten.mp hb
      obtain ⟨w, hw, hdec⟩ := List.mem_filterMap.mp hxs
      exact List.mem_flatten.mpr ⟨xs,
        List.mem_filterMap.mpr ⟨w, hcumul.2.2.2.2.1.subset hw, hdec⟩, ha⟩

end AvailableChain.FGSA.Run
end
