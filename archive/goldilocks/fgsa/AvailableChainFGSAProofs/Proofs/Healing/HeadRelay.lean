module
public import AvailableChainFGSAProofs.Proofs.Shared.Relay
public import AvailableChainFGSAProofs.Proofs.Shared.AnchorService

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

private theorem headRelay_slotStartZ_unfold (p : Params) (s : Int) :
    slotStartZ p s = 4 * p.Δ * s := rfl

omit [DecidableEq V] in
/-- A joined next-slot voter has the same earlier-label receiver cutoff. -/
theorem healing_head_vote_restart_bound (hS : V2.D.ScheduleWellFormed E rho)
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
  simpa only [headRelay_slotStartZ_unfold, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_right] using hb

open Gen.AC.Root
private theorem headCarried_vote_shape {n : Nat} (o : GridCO.Wire n .root) (s : Slot) (k : Fin n)
    (hl : GridCO.headLabel? o = some s) (hk : GridCO.headSeat? o = some k) :
    ∃ B, o = ⟨.seat s k, .head B⟩ := by
  obtain ⟨auth, payload⟩ := o
  cases auth <;> cases payload <;> try contradiction
  rename_i r j B
  have hr : r = s := Option.some.inj hl
  have hj : j = k := Option.some.inj hk
  subst r; subst j
  exact ⟨B, rfl⟩

private def HeadCarried (st : State p.n) (s : Slot) : Prop :=
  ∀ w ∈ st.proposals, ∀ r N,
    w.decode = some (.block r N) → N.erase.slot = s + 1 →
    ∀ o ∈ N.raw.map baseVote, ∀ seat,
      GridCO.headLabel? o = some s → GridCO.headSeat? o = some seat →
      o ∈ GridCO.votesAt st.base s ∨
        GridCO.equivocates (GridCO.votesAt st.base s) seat = true

private theorem headCarried_settled_mono {v v' : GridCO.State p.n .root} (s : Slot)
    (h : v.votes ⊆ v'.votes) (o : GridCO.Wire p.n .root) (seat : Fin p.n)
    (hr : o ∈ GridCO.votesAt v s ∨ GridCO.equivocates (GridCO.votesAt v s) seat = true) :
    o ∈ GridCO.votesAt v' s ∨ GridCO.equivocates (GridCO.votesAt v' s) seat = true := by
  have hs : GridCO.votesAt v s ⊆ GridCO.votesAt v' s := by
    intro a ha
    obtain ⟨ha, hl⟩ := List.mem_filter.mp ha
    exact List.mem_filter.mpr ⟨h ha, hl⟩
  exact hr.elim (fun hm => Or.inl (hs hm))
    (fun he => Or.inr (Gen.AC.Root.vote_pool_equivocates_mono _ _ seat hs he))

private theorem headCarried_carried_mono {st st' : State p.n} (s : Slot)
    (hp : st'.proposals = st.proposals) (hv : st.base.votes ⊆ st'.base.votes)
    (h : HeadCarried st s) : HeadCarried st' s := by
  intro w hw r N hd hb o ho seat hl hk
  rw [hp] at hw
  exact headCarried_settled_mono s hv o seat (h w hw r N hd hb o ho seat hl hk)

private theorem headCarried_fold_heads (raw : List (GridCO.HeadWire p.n .root))
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

private theorem headCarried_carried_process (st : State p.n) (hInv : CStoreInv p st)
    (s : Slot) (hslot : st.slot p ≤ s + 1) (parent : Wire p.n)
    (h : HeadCarried st s) : HeadCarried (FGSA.process p st parent) s := by
  have hv := process_votes_subset st parent
  change HeadCarried (match parent.decode with
    | some (.vote r i b) => admitHead p st r i b
    | some (.row _ body) => admitRow p st ⟨parent.auth, body⟩
    | some (.block r N) => admitBlock p st r N
    | none => st) s
  cases hd : parent.decode with
  | none => exact h
  | some m =>
    cases m with
    | vote r i b =>
      exact headCarried_carried_mono (st := st) s rfl (Internal.grid_admitVote_votes_subset _ _) h
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
              exact headCarried_settled_mono s hv' o seat
                (h w hw r' M hd' hb o ho seat hl hk)
            · have he := List.mem_singleton.mp hw
              subst w
              change some (Input.block r N) =
                some (Input.block r' M) at hd'
              cases hd'
              have hwindow : st.slot p = s + 1 :=
                le_antisymm hslot (hb ▸ (blockAccepted_facts ha).2.1)
              obtain ⟨B, rfl⟩ := headCarried_vote_shape o s seat hl hk
              have hh := headCarried_fold_heads
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

private theorem headCarried_carried_run (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hV : V2.D.ExecutionValid E rho)
    (k : Nat) (y : V) (s : Slot)
    (htick : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)))
    {it : Nat} (hit : rho.events[it]? = some (.tick y (SA.proposalTime p.toParams s))) :
    HeadCarried (V2.D.Run.stateBefore E rho k y).st s := by
  have hS := hV.toScheduleWellFormed
  have hBound := healing_head_vote_restart_bound hS htick hJ
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
    (fun nd => HeadCarried nd.st s) (Nat.zero_le k) y ?_ ?_
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
      exact headCarried_carried_mono s (clock_proposals p _ t)
        (by rw [(clock_vn _ t).1]) ih
    | deliver v o t =>
      change v = y at hy; subst v
      simp only [V2.D.World.step, Function.update_self]
      exact headCarried_carried_process _ (cstoreInv_stateBefore E rho j y) s (hu j (by omega))
        (toWire p o) ih
  · exact fun _ h => (List.not_mem_nil h).elim


theorem healing_head_provenance_on (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
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
          exact headCarried_carried_run E rho hE k y s htick hJ hit
            w hw' r N hdw (by simpa using hb.1) o hm seat hl' hk
        · cases hd

theorem healing_head_proposal_tick (hV : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
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


/-- Joined local provenance includes carried HEADs refused after seat equivocation.
No network acceptance is asserted for the refused HEAD. -/
theorem healing_head_read_provenance (hV : V2.D.ExecutionValid E rho)
    (hDelta : E.Δ = p.Δ) {i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1))) :
    let pre := (rho.stateBefore E i x).st
    let dst := clock p pre (SA.voteTime p.toParams (s + 1))
    ∀ o ∈ headVotes p dst (s + 1), ∀ q, GridCO.headSeat? o = some q →
      o ∈ GridCO.votesAt pre.base s ∨ GridCO.equivocates (GridCO.votesAt pre.base s) q = true := by
  obtain ⟨it, hit⟩ := healing_head_proposal_tick hV hDelta hx hi hJ
  exact healing_head_provenance_on E rho hV i x s hi hJ hit

/-- Enabled gates bound all prior receiver restarts by the label start. -/
theorem healing_head_gate_restart_bound (hS : V2.D.ScheduleWellFormed E rho)
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

/-- Source support has an original early acceptance in this label's epoch. -/
theorem healing_head_support_accepted (hV : V2.D.ExecutionValid E rho)
    (hR : V2.D.RestartsAtWakes E rho) (hDelta : E.Δ = p.Δ)
    {i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hG : enabledGateAt p c E rho i x s) (q : Fin p.n) (b : BlockId)
    (ho : baseVote (⟨.seat (.head s) q, b⟩ : HeadWire p.n) ∈
      GridCO.cleanSupport p.toParams.engine
        (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s) :
    ∃ j < i, ∃ send, rho.acceptsAt E j x (ofHead p ⟨.seat (.head s) q, b⟩) send ∧
      send < SA.earlyTime p.toParams s := by
  have hp0 : 0 ≤ SA.proposalTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int)
    have := p.deltaPos
    positivity
  have hpT : SA.proposalTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hpubP : V2.PublicTime E (SA.proposalTime p.toParams s) := by
    refine ⟨4 * s, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * (s : Int) = _
    push_cast
    ring
  obtain ⟨it, hit⟩ := List.mem_iff_getElem?.mp (hV.tick_total x hx _ hpubP hp0
    (hpT.trans (hV.in_horizon _ (List.mem_of_getElem? hG.1)).2)
    (fgsa_enabledGate_awakeClosed hV hx hG _ hp0 le_rfl hpT))
  have hc := List.mem_filter.mp ho
  have hm := (List.mem_filter.mp (List.mem_filter.mp hc.1).1).1
  change _ ∈ (clockPre p _ _).base.votes at hm
  rw [(Internal.clockPre_vn _ _).1] at hm
  have hres := (List.mem_filter.mp hc.1).2
  change GridCO.resolvedBefore _ _ _ = true at hres
  dsimp only [GridCO.resolvedBefore] at hres
  have ht : GridCO.stampVote (storeAt p c E rho i x).base
      (baseVote (⟨.seat (.head s) q, b⟩ : HeadWire p.n)) < SA.earlyTime p.toParams s := by
    cases he : GridCO.resolvedHead? _ _ with
    | none => rw [he] at hres; cases hres
    | some K =>
      rw [he] at hres
      have hstamp := of_decide_eq_true (Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp hres).1).2
      change (((clockPre p _ _).base.voteStamp.find? _).map Prod.snd).getD _ < _ at hstamp
      rw [(clockPre_stamps p _ _).2] at hstamp
      have hkeys := hm
      change _ ∈ (rho.stateBefore E i x).st.base.votes at hkeys
      rw [← fgsa_vote_stamp_keys E rho i x] at hkeys
      unfold GridCO.stampVote
      cases hf : (storeAt p c E rho i x).base.voteStamp.find?
          (fun row => row.1 == baseVote (⟨.seat (.head s) q, b⟩ : HeadWire p.n)) with
      | none =>
        obtain ⟨row, hr, heq⟩ := List.mem_map.mp hkeys
        have hn := List.find?_eq_none.mp hf row hr
        rw [heq, beq_self_eq_true] at hn
        contradiction
      | some row => simpa only [hf, Option.map_some, Option.getD_some] using hstamp
  apply fgsa_vote_accepted_before_local E rho hV hR s hit
    (healing_head_gate_restart_bound hV.toScheduleWellFormed hG) q b
    (SA.earlyTime p.toParams s) ?_ (by
      change 0 ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
      have := p.deltaPos
      positivity) hm ht
  refine ⟨4 * s + 2, ?_⟩
  rw [hDelta]
  change 4 * p.Δ * (s : Int) + 2 * p.Δ = _
  push_cast
  ring

/-- Every stored HEAD or cap witness has a strict stamp at this joined release read. -/
theorem healing_head_read_stamp (hV : V2.D.ExecutionValid E rho)
    {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1)))
    (o : GridCO.Wire p.n .root) :
    GridCO.stampVote (rho.stateBefore E i x).st.base o < SA.voteTime p.toParams (s + 1) := by
  have he : SA.voteTime p.toParams (s + 1) = SA.releaseTime p.toParams s := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ = 4 * p.Δ * (s : Int) + 5 * p.Δ
    push_cast
    ring
  rw [he]
  apply (fgsa_release_votes_stamped E rho hV.toScheduleWellFormed (he ▸ hi) ?_).1 o
  intro j w hji hj
  apply (healing_head_vote_restart_bound hV.toScheduleWellFormed hi hJ j w hji hj).trans_lt
  change 4 * p.Δ * (s : Int) < 4 * p.Δ * (s : Int) + 5 * p.Δ
  linarith [p.deltaPos]

/-- The local raw pool has read evidence even when its carried HEAD was refused. -/
theorem healing_head_local_receipt (hV : V2.D.ExecutionValid E rho)
    (hDelta : E.Δ = p.Δ) {i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1)))
    (q : Fin p.n) (b : BlockId)
    (ho : (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∈
      headVotes p (clock p (rho.stateBefore E i x).st
        (SA.voteTime p.toParams (s + 1))) (s + 1)) :
    HeadRelayReceiptScope E rho s q b (SA.voteTime p.toParams (s + 1)) i x := by
  constructor
  rcases healing_head_read_provenance hV hDelta hx hi hJ _ ho q rfl with hm | hc
  · exact Or.inl ⟨(List.mem_filter.mp hm).1, healing_head_read_stamp hV hi hJ _⟩
  · obtain ⟨u, hu, v, hv, hne, hku, hkv⟩ := (Gen.AC.Root.cap_pair _ q).mp hc
    obtain ⟨hum, hul⟩ := List.mem_filter.mp hu
    obtain ⟨hvm, hvl⟩ := List.mem_filter.mp hv
    exact Or.inr ⟨u, hum, v, hvm, hne, beq_iff_eq.mp hul, beq_iff_eq.mp hvl,
      hku, hkv, healing_head_read_stamp hV hi hJ _, healing_head_read_stamp hV hi hJ _⟩

end AvailableChain.FGSA.Run
end
