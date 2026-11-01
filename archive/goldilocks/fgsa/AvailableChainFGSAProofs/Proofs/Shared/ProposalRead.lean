module
public import AvailableChainFGSAProofs.Proofs.Shared.Channels
public import AvailableChainFGSARun.Proofs.Interface

public section
namespace AvailableChain.FGSA.Run

/-- [ROOT-DIGEST-2 W2; DC NamedBlocks] An honest proposal has its actual named payload
and the selected geometric parent at the exact proposal tick. -/
theorem proposal_read_named (p : Params) {In V : Type} [DecidableEq V]
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
        N.rows = proposalRows p st (proposerHead p st s) := by
  obtain ⟨hslot, o, ⟨j, hj, hem⟩, hpay⟩ := hp
  have hs0 : 0 < s := hslot.1
  change rho.events[j]? = some (.tick _ (SA.proposalTime p.toParams s)) at hj
  have hem0 := hem
  rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem
  obtain ⟨auth, m⟩ := o
  cases m with
  | head B => cases hpay
  | row body => cases hpay
  | proposal N =>
  have hb : N.erase = b := Option.some.inj hpay
  subst b
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
    obtain ⟨_, _, d, hl, ht, hm⟩ :=
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
      change RunLabel.prop s = l at hl
      subst l
      have hseat : seat = ⟨0, Nat.one_pos⟩ := by
        have h1 : (fgsa p c).seats (RunLabel.prop s) = 1 := rfl
        have hlt : seat.val < 1 := h1 ▸ seat.isLt
        exact Fin.ext (by change seat.val = 0; omega)
      subst seat
      let nd := V2.D.Run.stateBefore E rho j
        (V2.D.proposerOf rho (fgsaInterface p c) s)
      let st := ((fgsa p c).clock nd (SA.proposalTime p.toParams s)).st
      have htick : V2.D.Run.tickIdx? rho (V2.D.proposerOf rho (fgsaInterface p c) s)
          (SA.proposalTime p.toParams s) = some j := by
        obtain ⟨k, hk⟩ : ∃ k, V2.D.Run.tickIdx? rho
            (V2.D.proposerOf rho (fgsaInterface p c) s)
            (SA.proposalTime p.toParams s) = some k := by
          rw [V2.D.Run.tickIdx?, ← Option.isSome_iff_exists, List.findIdx?_isSome,
            List.any_eq_true]
          exact ⟨_, List.mem_of_getElem? hj, by simp⟩
        exact (fgsa_tick_unique E rho hs (V2.D.Run.tickIdx?_spec hk) hj) ▸ hk
      change (if joinedNow p st then
        (propose p st s).map (withApp p _) else none) = some (.proposal N) at hm
      split_ifs at hm with hjoin
      rw [propose_head p st s (Nat.ne_of_gt hs0)] at hm
      simp only [Option.map_map] at hm
      obtain ⟨P, hP, he⟩ := Option.map_eq_some_iff.mp hm
      cases Msg.proposal.inj he
      have hparent := (namedByErase?_sound st (proposerHead p st s) P hP).2
      refine ⟨j, _, rfl, hj, hem0, ?_, fgsa_proposal_slot nd s, ?_, rfl⟩
      · change (postClock E rho _ _).map (·.st) = some st
        rw [proposalTime_fgsa p c s, postClock_def, preTick_def]
        change (((V2.D.Run.tickIdx? rho _ (SA.proposalTime p.toParams s)).map
          (fun k => V2.D.Run.stateBefore E rho k _)).map
          (fun nd : Node p => (fgsa p c).clock nd (SA.proposalTime p.toParams s))).map
          (fun nd : Node p => nd.st) = some st
        rw [htick]
        rfl
      · rw [namedProposal_erase, hparent]
        rfl

end AvailableChain.FGSA.Run
end
