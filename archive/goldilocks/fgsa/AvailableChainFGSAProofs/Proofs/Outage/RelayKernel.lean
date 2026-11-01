module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Shared.AnchorService -- shake: keep
public import AvailableChainFGSAProofs.Proofs.Shared.Relay

namespace AvailableChain.FGSA.Run
private theorem inclusionRelay_slotStartZ_unfold (p : Params) (s : Int) :
    slotStartZ p s = 4 * p.Δ * s := rfl
end AvailableChain.FGSA.Run

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

-- Local HEAD history suppliers for the receiver epoch.
private theorem inclusionRelay_grid_future_absent (st : GridCO.State p.n .root)
    (r : Slot) (i : Fin p.n)
    (b : BlockId) (o : GridCO.Wire p.n .root) (hf : (st.now / (4 * p.Δ)).toNat < r)
    (hm : (⟨.seat r i, .head b⟩ : GridCO.Wire p.n .root) ∉ st.votes) :
    (⟨.seat r i, .head b⟩ : GridCO.Wire p.n .root) ∉
      (GridCO.admitVote p.toParams.engine st o).votes := by
  by_cases ho : o = ⟨.seat r i, .head b⟩
  · subst o
    unfold GridCO.admitVote
    change _ ∉ (if r < (st.now / (4 * p.Δ)).toNat - 1 ||
        (st.now / (4 * p.Δ)).toNat < r || decide (_ ∈ st.votes) ||
        GridCO.equivocates (GridCO.votesAt st r) i then st else _).votes
    simp [hf, hm]
  · obtain ⟨auth, payload⟩ := o
    cases auth <;> cases payload <;> dsimp only [GridCO.admitVote]
    all_goals first
      | exact hm
      | split_ifs
        · exact hm
        · simp only [List.mem_append, List.mem_singleton, not_or]
          exact ⟨hm, fun he => ho he.symm⟩

private theorem inclusionRelay_grid_future_fold (raw : List (GridCO.HeadWire p.n .root))
    (st : GridCO.State p.n .root) (r : Slot) (i : Fin p.n) (b : BlockId)
    (hf : (st.now / (4 * p.Δ)).toNat < r)
    (hm : (⟨.seat r i, .head b⟩ : GridCO.Wire p.n .root) ∉ st.votes) :
    (⟨.seat r i, .head b⟩ : GridCO.Wire p.n .root) ∉
      (raw.foldl (fun v h => GridCO.admitVote p.toParams.engine v
        (GridCO.fromHead h)) st).votes := by
  induction raw generalizing st with
  | nil => exact hm
  | cons h raw ih =>
    apply ih _ _ (inclusionRelay_grid_future_absent st r i b _ hf hm)
    rwa [Internal.grid_admitVote_now]

private theorem inclusionRelay_grid_future_proposal
    (st : GridCO.State p.n .root) (r : Slot) (i : Fin p.n)
    (b : BlockId) (o : GridCO.Wire p.n .root) (B : Block) (raw : List (GridCO.HeadWire p.n .root))
    (hf : (st.now / (4 * p.Δ)).toNat < r)
    (hm : (⟨.seat r i, .head b⟩ : GridCO.Wire p.n .root) ∉ st.votes) :
    (⟨.seat r i, .head b⟩ : GridCO.Wire p.n .root) ∉
      (GridCO.admitProposal p.toParams.engine st o B raw).votes := by
  unfold GridCO.admitProposal
  dsimp only
  split_ifs
  · exact hm
  · exact inclusionRelay_grid_future_fold raw _ r i b hf hm

private theorem inclusionRelay_future_head_process (st : State p.n) (r : Slot) (i : Fin p.n)
    (b : BlockId) (o : Wire p.n) (hf : st.slot p < r)
    (hm : (⟨.seat r i, .head b⟩ : GridCO.Wire p.n .root) ∉ st.base.votes) :
    (⟨.seat r i, .head b⟩ : GridCO.Wire p.n .root) ∉ (FGSA.process p st o).base.votes := by
  dsimp only [FGSA.process]
  cases hd : o.decode with
  | none => exact hm
  | some m =>
    cases m with
    | vote s j B => exact inclusionRelay_grid_future_absent st.base r i b _ hf hm
    | row j B => rwa [Internal.admitRow_base]
    | block s N =>
      dsimp only [admitBlock]
      split
      · exact hm
      · cases hP : parentFG st N.erase with
        | none => exact hm
        | some P =>
          let st1 : State p.n := { st with
            base := GridCO.admitProposal p.toParams.engine st.base (baseProposal s N.erase N.raw
                N.support) N.erase
              (N.raw.map baseHead)
            fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
            proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
          dsimp only
          split
          · rw [Internal.foldl_admitRow_base, (Internal.ite_reconcile st1 st).1]
            exact inclusionRelay_grid_future_proposal st.base r i b _ _ _ hf hm
          · exact hm

private theorem inclusionRelay_replay_head_step_origin (st : State p.n) (h : HeadWire p.n)
    (s : Slot) (i : Fin p.n) (b : BlockId)
    (hm : (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
      (FGSA.process p st ⟨h.auth, .head h.payload⟩).base.votes) :
    (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈ st.base.votes ∨
      h = ⟨.seat (.head s) i, b⟩ := by
  rcases h with ⟨auth, payload⟩
  rcases auth with ⟨(_ | _), _⟩ | _ | _ <;> try exact Or.inl hm
  rename_i j r
  change (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
    (GridCO.admitVote p.toParams.engine st.base ⟨.seat r j, .head payload⟩).votes at hm
  unfold GridCO.admitVote at hm
  dsimp only at hm
  split at hm
  · exact Or.inl hm
  · rcases List.mem_append.mp hm with hm | hm
    · exact Or.inl hm
    · have he : s = r ∧ i = j ∧ b = payload := by
        simpa only [List.mem_singleton, Signed.mk.injEq, Auth.seat.injEq,
          GridCO.Msg.head.injEq, and_assoc] using hm
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact Or.inr rfl

private theorem inclusionRelay_replay_heads_origin (raw : List (HeadWire p.n)) (st : State p.n)
    (s : Slot) (i : Fin p.n) (b : BlockId)
    (hm : (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
      (raw.foldl (fun acc h => FGSA.process p acc ⟨h.auth, .head h.payload⟩) st).base.votes) :
    (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈ st.base.votes ∨
      (⟨.seat (.head s) i, b⟩ : HeadWire p.n) ∈ raw := by
  induction raw generalizing st with
  | nil => exact Or.inl hm
  | cons h raw ih =>
    rcases ih _ hm with hh | hh
    · rcases inclusionRelay_replay_head_step_origin st h s i b hh with hh | rfl
      · exact Or.inl hh
      · exact Or.inr (List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ hh)

private theorem inclusionRelay_replay_sources_origin
    (sources : List (NamedProposal p.n)) (st : State p.n)
    (s : Slot) (i : Fin p.n) (b : BlockId)
    (hm : (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
      (sources.foldl (fun acc N => N.raw.foldl
        (fun acc h => FGSA.process p acc ⟨h.auth, .head h.payload⟩) acc) st).base.votes) :
    (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈ st.base.votes ∨
      ∃ N ∈ sources, (⟨.seat (.head s) i, b⟩ : HeadWire p.n) ∈ N.raw := by
  induction sources generalizing st with
  | nil => exact Or.inl hm
  | cons N sources ih =>
    rcases ih _ hm with hh | ⟨M, hM, hh⟩
    · rcases inclusionRelay_replay_heads_origin N.raw st s i b hh with hh | hh
      · exact Or.inl hh
      · exact Or.inr ⟨N, List.mem_cons_self .., hh⟩
    · exact Or.inr ⟨M, List.mem_cons_of_mem _ hM, hh⟩


private theorem inclusionRelay_replay_before_proposal_absent
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hV : V2.D.ExecutionValid E rho) {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hs : 0 < s) (k : Nat) (hki : k ≤ i) (w : Time) (q : Fin p.n) (b : BlockId) :
    (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∉
      (acRestart p (rho.stateBefore E k x).st w).base.votes := by
  intro hm
  rw [acRestart_replay_order] at hm
  rcases inclusionRelay_replay_sources_origin _ _ s q b hm with hm | ⟨N, hN, hh⟩
  · exact (List.not_mem_nil hm).elim
  · unfold restartSources at hN
    obtain ⟨wire, hwire, he⟩ := List.mem_filterMap.mp hN
    cases hd : wire.decode with
    | none => simp only [hd, reduceCtorEq] at he
    | some input =>
      cases input with
      | vote r j B => simp only [hd, reduceCtorEq] at he
      | row j body => simp only [hd, reduceCtorEq] at he
      | block r M =>
        simp only [hd] at he
        split at he
        · cases Option.some.inj he
          have hB : N.erase ∈ (rho.stateBefore E k x).st.base.blocks := by
            obtain ⟨r', M', hw, _, _, _, B, hB, heB, _⟩ :=
              (metaInv_stateBefore E rho k x).wireTree wire hwire
            have eqwire := decode_eq_block.mp hd
            have heq : r' = r ∧ M' = N := by simpa only [Signed.mk.injEq,
              Auth.proposer.injEq, Msg.proposal.injEq] using hw.symm.trans eqwire
            obtain ⟨rfl, rfl⟩ := heq
            exact ((cstoreInv_stateBefore E rho k x).baseTree _).mpr ⟨B, hB, heB⟩
          have hold := (fgsa_stored_block_slots E rho hV.toScheduleWellFormed hi hs).1
            N.erase ((fgsa_store_durable p c E rho hki x).2.1.subset hB)
          obtain ⟨j, o, t, _, hj, ho, _, _⟩ := stored_proposal_delivered E rho k x wire hwire
          have hf := hV.wire j x o t hj
          change FGSA.wellFormed p (toWire p o) = true at hf
          rw [ho] at hf
          unfold FGSA.wellFormed at hf
          rw [hd] at hf
          have hr := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
            (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hf).1).1).1).2
          have hl := List.all_eq_true.mp hr _ hh
          change (s + 1 == N.erase.slot) = true at hl
          have heq := beq_iff_eq.mp hl
          exact (Nat.not_le_of_lt hold) (heq ▸ Nat.le_succ s)
        · cases he

private theorem inclusionRelay_before_proposal_absent
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hV : V2.D.ExecutionValid E rho) (hR : V2.D.RestartsAtWakes E rho)
    {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.proposalTime p.toParams s)))
    (q : Fin p.n) (b : BlockId) :
    ∀ k, k ≤ i → (fgsa p c).processed (rho.stateBefore E k x)
      (ofHead p ⟨.seat (.head s) q, b⟩) = false := by
  have all : ∀ k, k ≤ i →
      (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∉
        (rho.stateBefore E k x).st.base.votes := by
    intro k hki
    refine V2.D.Engine.stateBefore_step_induction E rho
      (fun nd => (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∉ nd.st.base.votes)
      (Nat.zero_le k) x ?_ (List.not_mem_nil ·)
    intro j e _ hjk he hnode hprev
    cases e with
    | tick v t =>
      change v = x at hnode; subst v
      simp only [V2.D.World.step, Function.update_self]
      rw [tick_st (c := c) E rho (rho.stateBefore E j x) x t, (clock_vn _ _).1]
      exact hprev
    | restart v w =>
      change v = x at hnode; subst v
      simp only [V2.D.World.step, Function.update_self]
      change _ ∉ (acRestart p (rho.stateBefore E j x).st w).base.votes
      by_cases hs : 0 < s
      · exact inclusionRelay_replay_before_proposal_absent E rho hV hi hs j (by omega) w q b
      · have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
        have hw0 := (hR x w (List.mem_of_getElem? he)).1
        have hm := List.pairwise_iff_getElem.mp hV.sorted
          j i (List.getElem?_eq_some_iff.mp he).1
          (List.getElem?_eq_some_iff.mp hi).1 (by omega)
        rw [(List.getElem?_eq_some_iff.mp he).2,
          (List.getElem?_eq_some_iff.mp hi).2] at hm
        have ht := V2.D.Engine.time_le_of_key_le _ _ hm
        change w ≤ SA.proposalTime p.toParams s at ht
        change w ≤ 4 * p.Δ * (s : Int) at ht
        rw [hs0] at ht
        norm_num at ht
        exact ((not_lt.mpr ht) hw0).elim
    | deliver v o t =>
      change v = x at hnode; subst v
      have ht : t < SA.proposalTime p.toParams s := by
        by_contra hn
        have ht := V2.D.Engine.tick_index_lt_delivery E rho hV.toScheduleWellFormed
          hi he (le_of_not_gt hn)
        omega
      have hn := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
        (fgsaRestoreTimeLaw p c) E rho hV.toScheduleWellFormed he x
      have hnow : (rho.stateBefore E j x).st.base.now ≤ t :=
        (fgsa_clock_now p c (rho.stateBefore E j x)) ▸ hn
      have hslot : (rho.stateBefore E j x).st.slot p < s := by
        have hs : 0 < s := by
          have hz := (hV.in_horizon _ (List.mem_of_getElem? he)).1
          by_contra hs
          have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
          change t < 4 * p.Δ * (s : Int) at ht
          rw [hs0] at ht
          norm_num at ht
          exact (not_lt.mpr hz) ht
        apply (Int.toNat_lt' hs).mpr
        apply (Int.ediv_lt_iff_lt_mul (by linarith [p.deltaPos])).mpr
        have ht' : (rho.stateBefore E j x).st.base.now < 4 * p.Δ * (s : Int) :=
          hnow.trans_lt ht
        nlinarith
      simp only [V2.D.World.step, Function.update_self]
      exact inclusionRelay_future_head_process _ s q b (toWire p o) hslot hprev
  intro k hki
  exact decide_eq_false_iff_not.mpr (all k hki)


omit [DecidableEq V] in
/-- A receiver restart cutoff gives the epoch after its label's proposal tick. -/
theorem inclusion_relay_head_epoch (hS : V2.D.ScheduleWellFormed E rho)
    {i it : Nat} {x : V} {s : Slot}
    (hit : rho.events[it]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hBound : ∀ j w, j < i → rho.events[j]? = some (.restart x w) →
      w ≤ SA.proposalTime p.toParams s) : V2.D.restartFree rho x it i := by
  classical
  intro j w htj hji hj
  have hjt := V2.D.Engine.restart_index_lt_event hS hj hit (hBound j w hji hj)
    (show 0 < 1 from by decide)
  omega

/-- HEAD history before the label is absent; later history stays in this epoch. -/
theorem inclusion_relay_head_history (hV : V2.D.ExecutionValid E rho)
    (hR : V2.D.RestartsAtWakes E rho) {i it : Nat} {x : V} {s : Slot}
    (hit : rho.events[it]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hBound : ∀ j w, j < i → rho.events[j]? = some (.restart x w) →
      w ≤ SA.proposalTime p.toParams s)
    (q : Fin p.n) (b : BlockId) {a : Time} (_hpa : SA.proposalTime p.toParams s < a)
    (hai : V2.D.Run.actionCut rho a ≤ i) :
    Gen.V2.Duty.HistorySafeAt E rho x (ofHead p ⟨.seat (.head s) q, b⟩) a := by
  rintro ⟨k, hk, hp⟩
  by_cases hkt : k ≤ it
  · have hf := inclusionRelay_before_proposal_absent E rho hV hR hit q b k hkt
    rw [hf] at hp
    cases hp
  · exact (fgsaHooks p c).processed_stable E rho hV.toScheduleWellFormed x
      (ofHead p ⟨.seat (.head s) q, b⟩) k _ hk
      ((inclusion_relay_head_epoch hV.toScheduleWellFormed hit hBound).mono
        (Nat.le_of_lt (Nat.lt_of_not_ge hkt)) hai) hp

/-- A HEAD handler after its label start has dependencies and is timely. -/
theorem inclusion_relay_head_handlers (hV : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (q : Fin p.n) (b : BlockId) (x : V) {a d : Time}
    (hpa : SA.proposalTime p.toParams s ≤ a) :
    ∀ j u, a ≤ u → u < d →
      V2.D.Run.handlesAt E rho j x (ofHead p ⟨.seat (.head s) q, b⟩) u →
      (fgsa p c).wellFormed (ofHead p ⟨.seat (.head s) q, b⟩) = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x)
        (ofHead p ⟨.seat (.head s) q, b⟩) = true ∧
      fgsaTimely p (V2.D.Run.stateBefore E rho j x) (ofHead p ⟨.seat (.head s) q, b⟩) := by
  intro j u hau hud hh
  have hcall := hh
  obtain ⟨parent, he, _⟩ := hh
  have deps := fgsa_hReady_of_not_block
    (dl := fun _ => d) (t := a) (o := ofHead p ⟨.seat (.head s) q, b⟩) (by intro r N h; cases h)
    (fgsa_hWF_of_delivery (dl := fun _ => d) (t := a) hV.wire) j u
    ((Gen.V2.Duty.index_lt_idxBefore_iff hV.toScheduleWellFormed he d).mpr hud) hcall
  refine ⟨deps.1, deps.2, ?_⟩
  have hpub : V2.PublicTime E (SA.proposalTime p.toParams s) := by
    refine ⟨4 * s, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * (s : Int) = _
    push_cast
    ring
  have h0 : 0 ≤ SA.proposalTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int)
    have := p.deltaPos
    positivity
  have hn := V2.D.Engine.delivery_now_ge_public_atRestart (fgsaClock p c)
    (fgsaRestoreTimeLaw p c) E rho hV he hpub h0 (hpa.trans hau)
  change 4 * p.Δ * (s : Int) ≤ (rho.stateBefore E j x).st.base.now
  rw [← fgsa_clock_now p c (rho.stateBefore E j x)]
  exact hn

/-- Enabled gates bound all prior receiver restarts by the label start. -/
theorem inclusion_relay_gate_restart_bound (hS : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot} (hG : enabledGateAt p c E rho i x s) :
    ∀ j w, j < i → rho.events[j]? = some (.restart x w) →
      w ≤ SA.proposalTime p.toParams s := by
  intro j w hji hj
  obtain ⟨u, hu, hwu⟩ := fgsa_restartTime_ge E rho hS hj hji
  have hb := hG.2
  change (match (storeAt p c E rho i x).restartTime with
    | none => True | some t => t ≤ 4 * p.Δ * (s : Int)) at hb
  change (match (rho.stateBefore E i x).st.restartTime with
    | none => True | some t => t ≤ 4 * p.Δ * (s : Int)) at hb
  rw [hu] at hb
  exact hwu.trans hb

omit [DecidableEq V] in
/-- A joined next-slot voter has the same earlier-label receiver cutoff. -/
theorem inclusion_relay_vote_restart_bound (hS : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1))) :
    ∀ j w, j < i → rho.events[j]? = some (.restart x w) →
      w ≤ SA.proposalTime p.toParams s := by
  intro j w hji hj
  have hw : w ≤ SA.voteTime p.toParams (s + 1) := by
    by_contra hn
    have hij := V2.D.Engine.eventIndex_lt_of_time_lt hS hi hj (lt_of_not_ge hn)
    omega
  have hb := hJ.2.2 w (hS.in_horizon _ (List.mem_of_getElem? hj)).1 hw
    (List.mem_of_getElem? hj)
  change w ≤ 4 * p.Δ * (s : Int)
  simpa only [inclusionRelay_slotStartZ_unfold, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_right] using hb

/-- Local HEAD service keeps the original source and the receiver's exact anchor. -/
theorem inclusion_relay_head_receiver_service {ΔF : Time}
    (hV : V2.D.ExecutionValid E rho) (hR : V2.D.RestartsAtWakes E rho)
    (hDelta : E.Δ = p.Δ)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF)) {i it : Nat} {x v : V}
      {s : Slot}
    (_hx : x ∈ rho.honest) (hv : v ∈ rho.honest)
    (hit : rho.events[it]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hBound : ∀ j w, j < i → rho.events[j]? = some (.restart x w) →
      w ≤ SA.proposalTime p.toParams s)
    (q : Fin p.n) (b : BlockId) {send a D : Time}
    (hTrigger : V2.D.Run.emits E rho v (ofHead p ⟨.seat (.head s) q, b⟩) send ∨
      ∃ j, V2.D.Run.acceptsAt E rho j v (ofHead p ⟨.seat (.head s) q, b⟩) send)
    (hsa : send ≤ a) (hpa : SA.proposalTime p.toParams s < a)
    (hai : V2.D.Run.actionCut rho a ≤ i) (hdi : V2.D.Run.idxBefore rho D ≤ i)
    (had : a + p.Δ ≤ D) (hcut : D ≤ rho.horizon) (hGST : E.t_GST ≤ a)
    (hAw : ∀ u, a ≤ u → u < a + p.Δ → E.awake x u = true)
    (hNX : (fgsa p c).excludes (rho.stateBeforeTime E D x)
      (ofHead p ⟨.seat (.head s) q, b⟩) = false) :
    Nonempty (ReceiverService E rho (ofHead p ⟨.seat (.head s) q, b⟩) send D x) := by
  have hS := hV.toScheduleWellFormed
  have htcut : it ≤ V2.D.Run.actionCut rho a :=
    ((V2.D.Engine.index_lt_actionCut_iff hS hit a).mpr (Or.inl hpa)).le
  have hRF := (inclusion_relay_head_epoch hS hit hBound).mono htcut hdi
  have hnot : (fgsa p c).excludes (rho.stateBeforeTime E (a + p.Δ) x)
      (ofHead p ⟨.seat (.head s) q, b⟩) = false := by
    by_contra hn
    have hex := Bool.eq_true_of_ne_false hn
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hex hNX
    have he := (fgsaHooks p c).excludes_stable E rho hS x
      (ofHead p ⟨.seat (.head s) q, b⟩) _ _ (fgsa_idxBefore_mono rho had)
      (hRF.mono (Gen.V2.Duty.actionCut_le_idxBefore hS
        (lt_add_of_pos_right _ p.deltaPos)) le_rfl) hex
    rw [hNX] at he
    cases he
  refine ⟨{
    dl := fun t => max t E.t_GST + p.Δ, cut := rho.horizon, anchor := a
    within := ?_, ready := ⟨v, hv, hTrigger, ?_⟩, send_le := hsa
    nonneg := ?_, later := (le_max_left _ _).trans_lt (lt_add_of_pos_right _ p.deltaPos)
    cut_le := by simpa only [max_eq_left hGST] using had.trans hcut,
    horizon := by simpa only [max_eq_left hGST] using had.trans hcut
    freeze_le := by simpa only [max_eq_left hGST] using had
    history := inclusion_relay_head_history hV hR
      hit hBound q b hpa hai, epoch := hRF
    handlers := inclusion_relay_head_handlers hV hDelta s q b x hpa.le
    not_excluded := by simpa only [max_eq_left hGST] using hnot }⟩
  · simpa only [hDelta] using
      Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hSync
        (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ _)
  · intro u hau hud
    exact hAw u hau (by simpa only [max_eq_left hGST] using hud)
  · have h0 : 0 ≤ SA.proposalTime p.toParams s := by
      change 0 ≤ 4 * p.Δ * (s : Int)
      have := p.deltaPos
      positivity
    exact h0.trans hpa.le

/-- A bounded awake receiver has HEAD service and retention at its consuming tick. -/
theorem inclusion_relay_head_relay_scope {ΔF : Time}
    (hV : V2.D.ExecutionValid E rho) (hR : V2.D.RestartsAtWakes E rho)
    (hDelta : E.Δ = p.Δ)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF)) {i : Nat} {x v : V} {s
      : Slot} {T : Time}
    (hx : x ∈ rho.honest) (hv : v ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x T))
    (hBound : ∀ j w, j < i → rho.events[j]? = some (.restart x w) →
      w ≤ SA.proposalTime p.toParams s)
    (hAw : AwakeClosed E x (SA.proposalTime p.toParams s) T)
    (hslot : p.slotOf T ≤ s + 1) (q : Fin p.n) (b : BlockId) {j : Nat} {send a D : Time}
    (hacc : rho.acceptsAt E j v (ofHead p ⟨.seat (.head s) q, b⟩) send)
    (hsa : send ≤ a) (hpa : SA.proposalTime p.toParams s < a)
    (had : a + p.Δ ≤ D) (hDT : D ≤ T) (hcut : D ≤ rho.horizon) (hGST : E.t_GST ≤ a) :
    HeadRelayServiceScope E rho s q b D i x := by
  have hS := hV.toScheduleWellFormed
  have hp0 : 0 ≤ SA.proposalTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int)
    have := p.deltaPos
    positivity
  have hpt := hpa.le.trans ((le_add_of_nonneg_right p.deltaPos.le).trans (had.trans hDT))
  have hpub : V2.PublicTime E (SA.proposalTime p.toParams s) := by
    refine ⟨4 * s, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * (s : Int) = _
    push_cast
    ring
  obtain ⟨it, hit⟩ := List.mem_iff_getElem?.mp (hV.tick_total x hx _ hpub hp0
    (hpt.trans (hS.in_horizon _ (List.mem_of_getElem? hi)).2) (hAw _ hp0 le_rfl hpt))
  have hdi : V2.D.Run.idxBefore rho D ≤ i := by
    by_contra hn
    exact (not_lt_of_ge hDT) ((Gen.V2.Duty.index_lt_idxBefore_iff hS hi D).mp
      (Nat.lt_of_not_ge hn))
  have had' : a < D := (lt_add_of_pos_right _ p.deltaPos).trans_le had
  have hai := (Gen.V2.Duty.actionCut_le_idxBefore hS had').trans hdi
  have hitD : it ≤ V2.D.Run.idxBefore rho D :=
    ((Gen.V2.Duty.index_lt_idxBefore_iff hS hit D).mpr (hpa.trans had')).le
  refine ⟨hdi, (inclusion_relay_head_epoch hS hit hBound).mono hitD le_rfl, ?_, ?_⟩
  · have hm := V2.D.Engine.stateBefore_now_mono_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho hS hdi x
    rw [fgsa_clock_now p c (rho.stateBefore E _ x),
      fgsa_clock_now p c (rho.stateBefore E i x),
      Gen.V2.Duty.stateBefore_idxBefore E rho D hS] at hm
    exact (Internal.slotOf_mono (p := p)
      (hm.trans (fgsa_preTick_now_le E rho hS hi))).trans hslot
  · intro hNX
    refine ⟨send, inclusion_relay_head_receiver_service hV hR hDelta hSync hx hv hit hBound q b
      (Or.inr ⟨j, hacc⟩)
      hsa hpa hai hdi had hcut hGST ?_ hNX⟩
    intro u hau hud
    exact hAw u (hp0.trans (hpa.le.trans hau)) (hpa.le.trans hau)
      (hud.le.trans (had.trans hDT))

open Gen.AC.Root
private theorem inclusionCarried_vote_shape {n : Nat} (o : GridCO.Wire n .root)
    (s : Slot) (k : Fin n)
    (hl : GridCO.headLabel? o = some s) (hk : GridCO.headSeat? o = some k) :
    ∃ B, o = ⟨.seat s k, .head B⟩ := by
  obtain ⟨auth, payload⟩ := o
  cases auth <;> cases payload <;> try contradiction
  rename_i r j B
  have hr : r = s := Option.some.inj hl
  have hj : j = k := Option.some.inj hk
  subst r; subst j
  exact ⟨B, rfl⟩

private def WcCarried (st : State p.n) (s : Slot) : Prop :=
  ∀ w ∈ st.proposals, ∀ r N,
    w.decode = some (.block r N) → N.erase.slot = s + 1 →
    ∀ o ∈ N.raw.map baseVote, ∀ seat,
      GridCO.headLabel? o = some s → GridCO.headSeat? o = some seat →
      o ∈ GridCO.votesAt st.base s ∨
        GridCO.equivocates (GridCO.votesAt st.base s) seat = true

private theorem inclusionCarried_settled_mono {v v' : GridCO.State p.n .root} (s : Slot)
    (h : v.votes ⊆ v'.votes) (o : GridCO.Wire p.n .root) (seat : Fin p.n)
    (hr : o ∈ GridCO.votesAt v s ∨ GridCO.equivocates (GridCO.votesAt v s) seat = true) :
    o ∈ GridCO.votesAt v' s ∨ GridCO.equivocates (GridCO.votesAt v' s) seat = true := by
  have hs : GridCO.votesAt v s ⊆ GridCO.votesAt v' s := by
    intro a ha
    obtain ⟨ha, hl⟩ := List.mem_filter.mp ha
    exact List.mem_filter.mpr ⟨h ha, hl⟩
  exact hr.elim (fun hm => Or.inl (hs hm))
    (fun he => Or.inr (Gen.AC.Root.vote_pool_equivocates_mono _ _ seat hs he))

private theorem inclusionCarried_carried_mono {st st' : State p.n} (s : Slot)
    (hp : st'.proposals = st.proposals) (hv : st.base.votes ⊆ st'.base.votes)
    (h : WcCarried st s) : WcCarried st' s := by
  intro w hw r N hd hb o ho seat hl hk
  rw [hp] at hw
  exact inclusionCarried_settled_mono s hv o seat (h w hw r N hd hb o ho seat hl hk)

private theorem inclusionCarried_fold_heads (raw : List (GridCO.HeadWire p.n .root))
    (st : GridCO.State p.n .root) (s : Slot) (seat : Fin p.n) (B : BlockId)
    (hlo : (st.now / (4 * p.toParams.engine.Δ)).toNat - 1 ≤ s)
    (hhi : s ≤ (st.now / (4 * p.toParams.engine.Δ)).toNat)
    (hraw : (⟨.seat s seat, .head B⟩ : GridCO.Wire p.n .root) ∈ raw.map GridCO.fromHead) :
    let post := raw.foldl
      (fun acc row => GridCO.admitVote p.toParams.engine acc (GridCO.fromHead row)) st
    (⟨.seat s seat, .head B⟩ : GridCO.Wire p.n .root) ∈ post.votes ∨
      GridCO.equivocates (GridCO.votesAt post s) seat = true := by
  induction raw generalizing st with
  | nil => exact (List.not_mem_nil hraw).elim
  | cons row raw ih =>
    dsimp only
    have hf (v : GridCO.State p.n .root) : v.votes ⊆
        (raw.foldl (fun acc row => GridCO.admitVote p.toParams.engine acc
          (GridCO.fromHead row)) v).votes := by
      clear ih hraw
      induction raw generalizing v with
      | nil => exact List.Subset.refl _
      | cons a raw ih =>
          exact List.Subset.trans (Internal.grid_admitVote_votes_subset _ _) (ih _)
    rcases List.mem_cons.mp hraw with he | hm
    · have hh : (⟨.seat s seat, .head B⟩ : GridCO.Wire p.n .root) ∈
          (GridCO.admitVote p.toParams.engine st ⟨.seat s seat, .head B⟩).votes ∨
          GridCO.equivocates (GridCO.votesAt
            (GridCO.admitVote p.toParams.engine st ⟨.seat s seat, .head B⟩) s) seat = true := by
        by_cases hc : GridCO.equivocates (GridCO.votesAt st s) seat = true
        · right; simp only [GridCO.admitVote, hc, Bool.or_true, ite_true]
        · left
          by_cases hm : (⟨.seat s seat, .head B⟩ : GridCO.Wire p.n .root) ∈ st.votes
          · simp [GridCO.admitVote, hm]
          · simp [GridCO.admitVote, not_lt.mpr hlo, not_lt.mpr hhi, hm, hc]
      rw [he] at hh
      rcases hh with hm | hc
      · left; rw [he]; exact hf _ hm
      · exact Or.inr (vote_pool_equivocates_mono _ _ seat
          (Internal.grid_votesAt_subset _ _ s (hf _)) hc)
    · exact ih _ (by simpa only [Internal.grid_admitVote_now] using hlo)
        (by simpa only [Internal.grid_admitVote_now] using hhi) hm

private theorem inclusionCarried_carried_process (st : State p.n) (hInv : CStoreInv p st)
    (s : Slot) (hslot : st.slot p ≤ s + 1) (parent : Wire p.n)
    (h : WcCarried st s) : WcCarried (FGSA.process p st parent) s := by
  have hv := process_votes_subset st parent
  change WcCarried (match parent.decode with
    | some (.vote r i b) => admitHead p st r i b
    | some (.row _ body) => admitRow p st ⟨parent.auth, body⟩
    | some (.block r N) => admitBlock p st r N
    | none => st) s
  cases hd : parent.decode with
  | none => exact h
  | some m =>
    cases m with
    | vote r i b =>
      exact inclusionCarried_carried_mono (st := st) s rfl
        (Internal.grid_admitVote_votes_subset _ _) h
    | row i body =>
      dsimp only
      rcases admitRow_eq p st ⟨parent.auth, body⟩ with he | he <;> rw [he]
      · exact h
      · exact h
    | block r N =>
      dsimp only
      cases hn : namedParentHeld st N with
      | false =>
        rw [admitBlock_refused p st r N (Or.inl hn)]
        exact h
      | true =>
        cases hp : parentFG st N.erase with
        | none => rw [admitBlock_refused p st r N (Or.inr (Or.inl hp))]; exact h
        | some P =>
          cases ha : blockAccepted p st r N P with
          | false =>
            rw [admitBlock_refused p st r N (Or.inr (Or.inr ⟨P, hp, ha⟩))]
            exact h
          | true =>
            have hprops : (admitBlock p st r N).proposals =
                st.proposals ++ [⟨.proposer r, .proposal N⟩] := by
              obtain ⟨pool, he, -⟩ := admitBlock_accepted_eq p st r N P hn hp ha
              rw [he]
              exact (accepted_st2 p st hInv r N P hp ha).1
            have hvotes : (admitBlock p st r N).base.votes =
                ((N.raw.map baseHead).foldl
                  (fun acc row => GridCO.admitVote p.toParams.engine acc (GridCO.fromHead row))
                  { st.base with
                    blocks := st.base.blocks ++ [N.erase]
                    blockStamp := st.base.blockStamp ++ [(N.erase, st.base.now)],
                    proposals := st.base.proposals ++ [baseProposal r N.erase N.raw N.support]
                        }).votes := by
              obtain ⟨pool, he, -⟩ := admitBlock_accepted_eq p st r N P hn hp ha
              rw [he]
              dsimp only
              have hb := congrArg GridCO.State.votes
                (admitProposal_base_view p st hInv.toInv0 r N P hp ha).1
              split
              · exact hb
              · exact (reconcile_frame _).2.2.2.2.2.1.trans hb
            intro w hw r' M hd' hb o ho seat hl hk
            rw [hprops] at hw
            rcases List.mem_append.mp hw with hw | hw
            · have hv' : st.base.votes ⊆ (admitBlock p st r N).base.votes := by
                change st.base.votes ⊆ (match parent.decode with
                  | some (.vote r i root) => admitHead p st r i root
                  | some (.row _ body) => admitRow p st ⟨parent.auth, body⟩
                  | some (.block r N) => admitBlock p st r N
                  | none => st).base.votes at hv
                rw [hd] at hv
                exact hv
              exact inclusionCarried_settled_mono s hv' o seat
                (h w hw r' M hd' hb o ho seat hl hk)
            · have he := List.mem_singleton.mp hw
              subst w
              change some (Input.block r N) =
                some (Input.block r' M) at hd'
              cases hd'
              have hwindow : st.slot p = s + 1 :=
                le_antisymm hslot (hb ▸ (blockAccepted_facts ha).2.1)
              obtain ⟨B, rfl⟩ := inclusionCarried_vote_shape o s seat hl hk
              have hh := inclusionCarried_fold_heads
                (N.raw.map baseHead)
                { st.base with
                  blocks := st.base.blocks ++ [N.erase]
                  blockStamp := st.base.blockStamp ++ [(N.erase, st.base.now)],
                  proposals := st.base.proposals ++ [baseProposal r N.erase N.raw N.support] }
                s seat B (by change st.slot p - 1 ≤ s; rw [hwindow, Nat.add_sub_cancel])
                (by change s ≤ st.slot p; rw [hwindow]; exact Nat.le_succ s)
                (by rw [List.map_map]; change _ ∈ N.raw.map baseVote; exact ho)
              change _ ∈ (GridCO.votesAt _ s) ∨ _
              unfold GridCO.votesAt at hh ⊢
              rw [hvotes]
              exact hh.elim
                (fun hm => Or.inl (List.mem_filter.mpr
                  ⟨hm, by change (some s == some s) = true; exact beq_self_eq_true _⟩))
                Or.inr

private theorem inclusionCarried_carried_run (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hV : V2.D.ExecutionValid E rho)
    (k : Nat) (y : V) (s : Slot)
    (htick : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)))
    {it : Nat} (hit : rho.events[it]? = some (.tick y (SA.proposalTime p.toParams s))) :
    WcCarried (V2.D.Run.stateBefore E rho k y).st s := by
  have hS := hV.toScheduleWellFormed
  have hBound := inclusion_relay_vote_restart_bound hS htick hJ
  have hu (j : Nat) (hj : j ≤ k) : (V2.D.Run.stateBefore E rho j y).st.slot p ≤ s + 1 := by
    have hm := V2.D.Engine.stateBefore_now_mono_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho hS hj y
    have hb := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c)
      E rho hS htick y
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho j y),
      fgsa_clock_now p c (V2.D.Run.stateBefore E rho k y)] at hm
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho k y)] at hb
    have he : p.slotOf (SA.voteTime p.toParams (s + 1)) = s + 1 := by
      exact (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho k y) _).2.symm.trans
        (fgsa_vote_slot (c := c) _ (s + 1))
    exact (Internal.slotOf_mono (p := p) (hm.trans hb)).trans_eq he
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd => WcCarried nd.st s) (Nat.zero_le k) y ?_ ?_
  · intro j e hj hk he hy ih
    cases e with
    | restart v t =>
      change v = y at hy; subst v
      simp only [V2.D.World.step, Function.update_self]
      have hjk := hk
      intro w hw r N hd hb o ho seat hl hseat
      have hjt := V2.D.Engine.restart_index_lt_event hS he hit (hBound j t hjk he)
        (show 0 < 1 from by decide)
      have hprops : (acRestart p (rho.stateBefore E j y).st t).proposals =
          (rho.stateBefore E j y).st.proposals := acRestart_proposals p _ t
      change w ∈ (acRestart p (rho.stateBefore E j y).st t).proposals at hw
      rw [hprops] at hw
      obtain ⟨r', M, hew, _, _, _, B, hB, heB, _⟩ :=
        (metaInv_stateBefore E rho j y).wireTree w hw
      have hdecode : r' = r ∧ M = N := by
        have heq := decode_eq_block.mp hd
        simpa only [Signed.mk.injEq, Auth.proposer.injEq, Msg.proposal.injEq] using
          hew.symm.trans heq
      obtain ⟨hr, hM⟩ := hdecode
      subst r'
      subst M
      have hNm := ((cstoreInv_stateBefore E rho j y).baseTree N.erase).mpr ⟨B, hB, heB⟩
      have hNm' := (fgsa_store_durable p c E rho hjt.le y).2.1.subset hNm
      -- Every retained proposal before the label's start has slot at most s.
      have hn := (fgsa_stateBefore_bounds E rho hS it y).1 N.erase hNm'
      have hnow := fgsa_preTick_now_le E rho hS hit
      have hslot : p.slotOf (SA.proposalTime p.toParams s) = s := by
        change p.slotOf (4 * p.Δ * (s : Int)) = s
        simpa only [add_zero] using
          slotOf_offset p s 0 (by omega) (by have hpos := p.deltaPos; dsimp [Time] at *; omega)
      have hslt := hn.trans ((Internal.slotOf_mono (p := p) hnow).trans_eq hslot)
      change N.erase.slot = s + 1 at hb
      have hle : N.erase.slot ≤ s := hslt
      rw [hb] at hle
      exact ((Nat.not_succ_le_self s) hle).elim
    | tick v t =>
      change v = y at hy; subst v
      simp only [V2.D.World.step, Function.update_self]
      rw [tick_st E rho (V2.D.Run.stateBefore E rho j y) y t]
      exact inclusionCarried_carried_mono s (clock_proposals p _ t)
        (by rw [(clock_vn _ t).1]) ih
    | deliver v o t =>
      change v = y at hy; subst v
      simp only [V2.D.World.step, Function.update_self]
      exact inclusionCarried_carried_process _ (cstoreInv_stateBefore E rho j y) s (hu j (by omega))
        (toWire p o) ih
  · exact fun _ h => (List.not_mem_nil h).elim


theorem inclusion_relay_headVotes_provenance (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (k : Nat) (y : V) (s : Slot)
    (htick : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)))
    {it : Nat} (hit : rho.events[it]? = some (.tick y (SA.proposalTime p.toParams s))) :
    let pre := (V2.D.Run.stateBefore E rho k y).st
    let dst := ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y)
      (SA.voteTime p.toParams (s + 1))).st
    ∀ o ∈ headVotes p dst (s + 1), ∀ seat, GridCO.headSeat? o = some seat →
      o ∈ GridCO.votesAt pre.base s ∨
        GridCO.equivocates (GridCO.votesAt pre.base s) seat = true := by
  intro pre dst o ho seat hk
  change o ∈ List.eraseDups (_ ++ _) at ho
  rcases List.mem_append.mp (List.mem_eraseDups.mp ho) with ho | ho
  · left
    have hm := (List.mem_filter.mp ho).1
    change o ∈ GridCO.votesAt (clock p pre _).base (s + 1 - 1) at hm
    simpa only [GridCO.votesAt, Nat.add_sub_cancel, (clock_vn pre _).1] using hm
  · obtain ⟨ho, hl⟩ := List.mem_filter.mp ho
    have hl' : GridCO.headLabel? o = some s := by
      simpa only [Nat.add_sub_cancel, beq_iff_eq] using hl
    obtain ⟨row, hr, hm⟩ := List.mem_flatMap.mp ho
    obtain ⟨w, hw, hd⟩ := List.mem_filterMap.mp hr
    have hw' : w ∈ pre.proposals := by
      change w ∈ (clock p pre _).proposals at hw
      rwa [clock_proposals] at hw
    cases hdw : w.decode with
    | none => rw [hdw] at hd; cases hd
    | some m =>
      cases m with
      | vote r i B => rw [hdw] at hd; cases hd
      | row i body => rw [hdw] at hd; cases hd
      | block r N =>
        rw [hdw] at hd
        dsimp only at hd
        split at hd
        · rename_i hb
          cases hd
          exact inclusionCarried_carried_run E rho hE k y s htick hJ hit
            w hw' r N hdw (by simpa using hb.1) o hm seat hl' hk
        · cases hd

theorem inclusion_relay_vote_proposal_tick (hV : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    {i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1))) :
    ∃ it : Nat, rho.events[it]? = some (.tick x (SA.proposalTime p.toParams s)) := by
  have hp0 : 0 ≤ SA.proposalTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int)
    have := p.deltaPos
    positivity
  have hpT : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have hpub : V2.PublicTime E (SA.proposalTime p.toParams s) := by
    refine ⟨4 * s, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * (s : Int) = _
    push_cast
    ring
  have hAw := fgsa_awake_of_joinedAt E rho x (s + 1) _ _ hJ hp0
    (by
      change 4 * p.Δ * (((s + 1 : Nat) : Int) - 1) ≤ 4 * p.Δ * (s : Int)
      push_cast
      ring_nf
      exact le_rfl)
    hpT
  exact List.mem_iff_getElem?.mp (hV.tick_total x hx _ hpub hp0
    (hpT.trans (hV.in_horizon _ (List.mem_of_getElem? hi)).2) hAw)


end AvailableChain.FGSA.Run
end
