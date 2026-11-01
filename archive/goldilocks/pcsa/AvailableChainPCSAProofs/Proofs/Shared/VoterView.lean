module
public import AvailableChainPCSAProofs.Proofs.Shared.HonestProposal
public import AvailableChainPCSAProofs.Proofs.Shared.Certificates
public import AvailableChainPCSAProofs.Proofs.Shared.RelayRun
public import AvailableChainPCSAProofs.Proofs.Foundations.SnapshotRun
public import AvailableChainGeneric.Proofs.V2.Duty.Signatures
public import AvailableChainPCSAClaims.Statements.LaneReads

public section

/-! The voter view at an honest proposal slot (pcsa34-r4.3b §5.3 (F3), §5.6.1
step 1), shared by the lanes. Every stored slot-`s` proposal is the honest
one, so its PC is the only carried PC. Every frozen PC of slot `s - 1` has a
whole-PC acceptance no later than `z_{s-1}`; under the deadline
`max t z_{s-1} + Δ` its key is held at the proposer before `t_s`. The
proposer's maximum then outranks every voter source, and the voter view has
the proposer's target (`pcsa_voter_view_of_delivery`). The state and run
steps follow the Formation lane (FormationView, FormationOrigins,
FormationRelay) with the premises reduced to `Base₂`, `StageOneFrame`, the
honest proposal and the delivery premise. -/

open AvailableChain AvailableChain.SimplexFG

namespace AvailableChain.PCSA
variable {n : Nat}

private theorem voter_pcs_wellFormed (p : Params) (st : State p.n) (h : Reachable p st) :
    ∀ D ∈ st.pcs, D.wellFormed = true := by
  have hs : CertSafe (fun _ => True) st := by
    induction h with
    | init =>
      rw [CertSafe_def]
      refine ⟨fun _ _ => True.intro, ?_⟩
      intro d hd
      change d ∈ ([] : List (PC p.n)) at hd
      cases hd
    | tick t _ ih => exact clock_certSafe p _ _ t ih
    | deliver o _ ih =>
      exact process_certSafe p _ _ o ih (by intros; trivial)
        (by intros; trivial) (by intros; trivial)
  rw [CertSafe_def] at hs
  exact fun D hD => (hs.2 D hD).1

private theorem voter_freeze_row (p : Params) (st : State p.n) (s : Slot)
    (h : st.pcSnapshot.find? (fun row => row.1 == s) = none) :
    (clock p st (SA.freezeTime p.toParams s)).pcSnapshot.find?
      (fun row => row.1 == s) = some (s, st.pcs) := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have hf : ((SA.freezeTime p.toParams s - 3 * p.Δ) / (4 * p.Δ)).toNat = s := by
    change ((4 * p.Δ * (s : Int) + 3 * p.Δ - 3 * p.Δ) / (4 * p.Δ)).toNat = s
    rw [add_sub_cancel_right, Int.mul_ediv_cancel_left _ (by omega), Int.toNat_natCast]
  have hz : 0 ≤ SA.freezeTime p.toParams s - 3 * p.Δ := by
    change 0 ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ - 3 * p.Δ
    rw [add_sub_cancel_right]
    positivity
  rw [clock_freeze, clockPre_snapshot]
  simp only [hf, hz, decide_true, BEq.rfl, Bool.and_self, ite_true,
    h, Option.isSome_none, Bool.false_eq_true, ite_false,
    List.find?_append, List.find?_cons]
  rfl

private theorem voter_snapshot_label (st : State n) (s : Slot) (C : PC n)
    (hC : C ∈ pcSnapshotAt st s) : s ∈ st.pcSnapshot.map Prod.fst := by
  delta pcSnapshotAt at hC
  cases hr : st.pcSnapshot.find? (fun row => row.1 == s) with
  | none => rw [hr] at hC; exact (List.not_mem_nil hC).elim
  | some row =>
    exact List.mem_map.mpr ⟨row, List.mem_of_find?_eq_some hr,
      beq_iff_eq.mp (List.find?_some (p := fun r : Slot × List (PC n) => r.1 == s) hr)⟩

private theorem voter_snapshot_before_clock (p : Params) (st : State p.n)
    (s : Slot) (t : Time) (C : PC p.n) (ht : t ≠ SA.freezeTime p.toParams s)
    (hC : C ∈ pcSnapshotAt (clock p st t) s) : C ∈ pcSnapshotAt st s := by
  cases hr : st.pcSnapshot.find? (fun row => row.1 == s) with
  | some row =>
    have hs : (st.pcSnapshot.find? (fun row => row.1 == s)).isSome := by rw [hr]; rfl
    rw [(pcsa_clock_pcSnapshotAt p st t s hs).1] at hC
    exact hC
  | none =>
    rcases clock_snapshot_origin p st t s (voter_snapshot_label _ _ C hC) with hs | hs
    · obtain ⟨row, hrow, he⟩ := List.mem_map.mp hs
      have hh := List.find?_eq_none.mp hr row hrow
      rw [he, BEq.rfl] at hh
      exact (hh rfl).elim
    · exact (ht hs).elim

/-- Frozen key receipt at the proposer and the unique carried PC fix the
voter view target. -/
theorem pcsa_view_of_frozen_receipt (p : Params) (src dst : State p.n)
    (s : Slot) (pc : Option (PC p.n))
    (hProposer : proposerPC p src = pc)
    (hFrozenPCReceipt : ∀ C ∈ pcSnapshotAt dst (s - 1), frameActive p dst C = true →
      ∃ A ∈ src.pcs.filter (frameActive p src), A.slot = C.slot ∧ A.target = C.target)
    (hCarried : ∀ C ∈ carriedPCs dst s, pc = some C)
    (hPresent : ∀ D, pc = some D →
      D ∈ (pcSnapshotAt dst (s - 1) ++ carriedPCs dst s).filter (frameActive p dst))
    (hRoots : ∀ A ∈ src.pcs.filter (frameActive p src),
      ∀ B ∈ src.pcs.filter (frameActive p src), A.target.root = B.target.root →
      A.target = B.target) :
    (voterPC p dst s).map PC.target = pc.map PC.target := by
  let cs := (pcSnapshotAt dst (s - 1) ++ carriedPCs dst s).filter (frameActive p dst)
  have hRecv : ∀ C ∈ cs,
      ∃ A ∈ src.pcs.filter (frameActive p src), A.slot = C.slot ∧ A.target = C.target := by
    intro C hC
    obtain ⟨hm, ha⟩ := List.mem_filter.mp hC
    rcases List.mem_append.mp hm with hf | hc
    · exact hFrozenPCReceipt C hf ha
    · have he := hCarried C hc
      have hbest : proposerPC p src = some C := hProposer.trans he
      exact ⟨C, bestPC_mem _ C hbest, rfl, rfl⟩
  cases hp : pc with
  | none =>
    have hEmpty : src.pcs.filter (frameActive p src) = [] :=
      pcsa_bestPC_none _ (hProposer.trans hp)
    cases hv : voterPC p dst s with
    | none => rfl
    | some C =>
      obtain ⟨A, hA, _⟩ := hRecv C (bestPC_mem cs C hv)
      rw [hEmpty] at hA
      exact (List.not_mem_nil hA).elim
  | some D =>
    apply pcsa_view_target_of_rank cs D (hPresent D hp)
    · intro C hC
      obtain ⟨A, hA, hs, ht⟩ := hRecv C hC
      have hb := pcsa_bestPC_rank_max _ A D hA (hProposer.trans hp)
      change (decide (D.slot < A.slot) ||
        (D.slot == A.slot && (decide (D.target.depth < A.target.depth) ||
          (D.target.depth == A.target.depth &&
            decide (D.target.root < A.target.root))))) = false at hb
      change (decide (D.slot < C.slot) ||
        (D.slot == C.slot && (decide (D.target.depth < C.target.depth) ||
          (D.target.depth == C.target.depth && decide (D.target.root < C.target.root))))) = false
      rw [hs, ht] at hb
      exact hb
    · intro C hC A hA he
      obtain ⟨B, hB, _, htB⟩ := hRecv C hC
      obtain ⟨D', hD', _, htD⟩ := hRecv A hA
      exact htB.symm.trans ((hRoots B hB D' hD'
        (by rw [htB, htD]; exact he)).trans htD)

/-- A delivery keeps every stored proposal wire with property `P`, when each
admitted proposal wire has `P`. -/
private theorem voter_process_scope (p : Params) (st : State p.n) (o : Wire p.n)
    (P : Wire p.n → Prop) (h : ∀ w ∈ st.proposals, P w)
    (ho : ∀ s N, o.decode = some (.block s N) →
      N.erase.slot = s → P ⟨.proposer s, .proposal N⟩) :
    ∀ w ∈ (process p st o).proposals, P w := by
  cases hd : o.decode with
  | none => delta process; rw [hd]; exact h
  | some d =>
    cases d with
    | vote s i r => delta process; rw [hd]; exact h
    | row i body => delta process; rw [hd, pcsa_admitRow_proposals]; exact h
    | ack s i r =>
      delta process
      rw [hd]
      change ∀ w ∈ (collectPCs (poolAck p st ⟨o.auth, r⟩)).proposals, P w
      rw [pcsa_collectPCs_keeps_proposals, pcsa_poolAck_proposals]
      exact h
    | pc C =>
      delta process
      rw [hd]
      change ∀ w ∈ (admitPC st C).proposals, P w
      delta admitPC
      split
      · rw [pcsa_collectPCs_keeps_proposals, pcsa_fold_poolAckRaw_proposals]; exact h
      · exact h
    | block s N =>
      delta process
      rw [hd]
      change ∀ w ∈ (admitBlock p st s N).proposals, P w
      delta admitBlock
      split
      · exact h
      · cases parentFG st N.erase with
        | none => exact h
        | some B =>
          dsimp only
          split
          · rename_i hAcc
            have hSlot : N.erase.slot = s := by
              have hf := hAcc
              change (N.erase != .genesis && decide (N.erase.slot ≤ st.slot p) &&
                !decide (∃ Y ∈ st.fg.TF, Y.root = N.erase.root) &&
                SimplexFG.FGBlock.preceq st.fg.F (fgBlock B N.erase N.rows) &&
                decide (N.erase.parent.slot < N.erase.slot) && s == N.erase.slot &&
                rowsValidForParent p B N.erase.slot N.rows &&
                (N.pc.map PC.wellFormed).getD true && namedContentOk p N) = true at hf
              simp only [Bool.and_eq_true] at hf
              exact (beq_iff_eq.mp (by tauto)).symm
            rw [pcsa_fold_admitRow_proposals, pcsa_collectPCs_keeps_proposals,
              pcsa_fold_poolAckRaw_proposals]
            have hh : ∀ w ∈ st.proposals ++ [⟨.proposer s, .proposal N⟩], P w := by
              intro w hw
              rcases List.mem_append.mp hw with hw | hw
              · exact h w hw
              · exact List.mem_singleton.mp hw ▸ ho s N hd hSlot
            cases N.pc <;> dsimp only <;> split_ifs <;>
              first
              | exact hh
              | (rw [pcsa_reconcile_proposals]; exact hh)
          · exact h

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Each frozen key comes from a whole-PC acceptance no later than its freeze. -/
theorem pcsa_frozen_pc_origin_valid (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hBase : Base₂ p c E rho)
    (hFrame : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest)
    (K : Nat) (s : Slot) (C : PC p.n)
    (hC : C ∈ pcSnapshotAt (V2.D.Run.stateBefore E rho K x).st s) :
    ∃ j t D, t ≤ SA.freezeTime p.toParams s ∧ D.slot = C.slot ∧ D.target = C.target ∧
      D.wellFormed = true ∧
      V2.D.Run.acceptsAt E rho j x (⟨.none, .pc D⟩ : Obj p) t := by
  have hlabel := voter_snapshot_label _ s C hC
  obtain ⟨i, hiK, hi⟩ := snapshot_key_origin E rho K x s hlabel
  have hs := snapshot_absent_before_tick E rho hBase.valid.nodup i x s hi
  have hrow : ((V2.D.Run.stateBefore E rho (i + 1) x).st.pcSnapshot.find?
      (fun row => row.1 == s)).isSome := by
    rw [V2.D.Run.stateBefore_succ E rho hi]
    rw [pcsa_tick_step, voter_freeze_row p _ s hs]
    rfl
  have he := ((pcsa_stageOne_mono E rho hBase.noRestart hFrame x hx
    (Nat.succ_le_of_lt hiK)).2 s hrow).1
  rw [he, V2.D.Run.stateBefore_succ E rho hi] at hC
  change C ∈ pcSnapshotAt
    (V2.D.World.step E rho (V2.D.Run.stateBefore E rho i) (.tick x _) x).st s at hC
  rw [pcsa_tick_step, clock_freeze_snapshot p _ s hs, pcsa_clock_pcs] at hC
  obtain ⟨j, hji, D, t, hDs, hDt, hD, ha⟩ := pcsa_keyHeld_accepted E rho hBase hFrame x hx
    C.slot C.target i ((KeyHeld_def _ _ _).mpr ⟨C, hC, rfl, rfl⟩)
  obtain ⟨o, hj, _⟩ := ha.1
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have ht := (List.pairwise_iff_getElem.mp hBase.valid.sorted) j i hjl hil hji
  rw [hje, hie] at ht
  exact ⟨j, t, D, V2.D.Engine.time_le_of_key_le _ _ ht, hDs, hDt,
    voter_pcs_wellFormed p _ (pcsa_reachable_stateBefore E rho (j + 1) x) D hD, ha⟩

/-- A read away from the freeze time keeps the frozen-key origin. -/
theorem pcsa_frozen_pc_origin_read_valid (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hBase : Base₂ p c E rho)
    (hFrame : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest)
    (s : Slot) (t : Time) (nd : Node p) (C : PC p.n)
    (hr : pcsa_postClock E rho x t = some nd) (ht : t ≠ SA.freezeTime p.toParams s)
    (hC : C ∈ pcSnapshotAt nd.st s) :
    ∃ j u D, u ≤ SA.freezeTime p.toParams s ∧ D.slot = C.slot ∧ D.target = C.target ∧
      D.wellFormed = true ∧
      V2.D.Run.acceptsAt E rho j x (⟨.none, .pc D⟩ : Obj p) u := by
  rw [pcsa_postClock_def] at hr
  obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hr
  rw [pcsa_preTick_def] at hp
  obtain ⟨k, _, he⟩ := Option.map_eq_some_iff.mp hp
  subst pre
  subst nd
  exact pcsa_frozen_pc_origin_valid E rho hBase hFrame x hx k s C
    (voter_snapshot_before_clock p _ s t C ht hC)

/-- Every stored proposal wire has `P` when every admitted one has. -/
theorem pcsa_metadata_scope (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (P : Wire p.n → Prop)
    (hDeliver : ∀ (j : Nat) (x : V) (o : Obj p) (t : Time) (s : Slot)
      (N : NamedProposal p.n), rho.events[j]? = some (.deliver x o t) →
      (toWire p o).decode = some (.block s N) →
      N.erase.slot = s → P ⟨.proposer s, .proposal N⟩)
    (i : Nat) (x : V) :
    ∀ w ∈ (V2.D.Run.stateBefore E rho i x).st.proposals, P w := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => ∀ w ∈ nd.st.proposals, P w) (Nat.zero_le i) x ?_ ?_
  · intro j e _ _ he hx h
    cases e with
    | restart y t =>
      change y = x at hx
      subst y
      change ∀ w ∈ (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st.proposals, P w
      rw [Function.update_self]
      exact fun w hw => (List.not_mem_nil hw).elim
    | tick y t =>
      change y = x at hx
      subst y
      change ∀ w ∈ (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st.proposals, P w
      rw [Function.update_self]
      have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho j x) x t
      rw [ht, pcsa_clock_proposals]
      exact h
    | deliver y o t =>
      change y = x at hx
      subst y
      change ∀ w ∈ (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st.proposals, P w
      rw [Function.update_self]
      exact voter_process_scope p _ (toWire p o) P h (hDeliver j x o t · · he)
  · exact fun w hw => (List.not_mem_nil hw).elim

/-- The stored-proposal scope at a post-clock read. -/
theorem pcsa_metadata_read_scope (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (P : Wire p.n → Prop)
    (hDeliver : ∀ (j : Nat) (x : V) (o : Obj p) (t : Time) (s : Slot)
      (N : NamedProposal p.n), rho.events[j]? = some (.deliver x o t) →
      (toWire p o).decode = some (.block s N) →
      N.erase.slot = s → P ⟨.proposer s, .proposal N⟩)
    (x : V) (t : Time) (nd : Node p) (hr : pcsa_postClock E rho x t = some nd) :
    ∀ w ∈ nd.st.proposals, P w := by
  rw [pcsa_postClock_def] at hr
  obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hr
  rw [pcsa_preTick_def] at hp
  obtain ⟨k, hk, he⟩ := Option.map_eq_some_iff.mp hp
  subst pre
  subst nd
  rw [show ((pcsaWith m p c).clock (V2.D.Run.stateBefore E rho k x) t).st =
    clock p (V2.D.Run.stateBefore E rho k x).st t from rfl, pcsa_clock_proposals]
  exact pcsa_metadata_scope E rho P hDeliver k x

private theorem voter_decoded (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (hd : (toWire p o).decode = some (.block s N)) :
    o = ⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> delta toWire toAuth Wire.decode at hd <;> cases hd
  | seat l i =>
    cases l with
    | prop k =>
      have hi : i = ⟨0, Nat.one_pos⟩ := by
        apply Fin.ext
        change i.val = 0
        have hh : i.val < 1 := i.isLt
        omega
      subst i
      cases payload <;> delta toWire toAuth Wire.decode at hd
      all_goals cases hd
      rfl
    | base l =>
      cases l <;> cases payload <;>
        delta toWire toAuth Wire.decode Label.ackSlot? at hd <;> cases hd

/-- Every delivered proposal signed for slot `s` is its honest emitted proposal. -/
theorem pcsa_delivered_proposal_unique (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) (s : Slot)
    (N : NamedProposal p.n) (hN : HonestNamedProposal p c E rho s N)
    (j : Nat) (y : V) (o : Obj p) (t : Time)
    (M : NamedProposal p.n) (he : rho.events[j]? = some (.deliver y o t))
    (hd : (toWire p o).decode = some (.block s M)) : M = N := by
  obtain rfl := voter_decoded o s M hd
  have hx : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ ∈ rho.honest := hN.1
  obtain ⟨u, _, k, hk, hm⟩ := h.valid.unforgeable y _ t ⟨j, he⟩ _ hx rfl
  obtain ⟨i, hi, hn⟩ := hN.2
  have hD : Gen.V2.Duty.SingleDuty (pcsaWith m p c) (.prop s) := by
    refine ⟨.propAction s, rfl, ?_⟩
    intro d hd
    exact (pcsa_signLabel_prop d s).mp hd
  have ho := Gen.V2.Duty.emitted_unique_of_singleDuty E rho h.valid.nodup
    (.prop s) hD ⟨0, Nat.one_pos⟩ _ k i u _ _ _ hk hi hm hn rfl rfl
  exact Msg.proposal.inj (congrArg V2.Signed.payload ho.2)

/-- Stored proposal wires keep the signed slot, and the slot-`s` one is the
honest proposal. -/
theorem pcsa_metadata_unique (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) (s : Slot)
    (N : NamedProposal p.n) (hN : HonestNamedProposal p c E rho s N)
    (x : V) (t : Time) (nd : Node p) (hr : pcsa_postClock E rho x t = some nd) :
    ∀ w ∈ nd.st.proposals, ∀ k M, w.decode = some (.block k M) →
      M.erase.slot = k ∧ (k = s → M = N) := by
  apply pcsa_metadata_read_scope E rho
    (fun w => ∀ k M, w.decode = some (.block k M) →
      M.erase.slot = k ∧ (k = s → M = N)) ?_ x t nd hr
  intro j y o u k M he hd hs l D hw
  change some (Input.block k M) = some (Input.block l D) at hw
  cases Option.some.inj hw
  refine ⟨hs, ?_⟩
  intro hk
  rw [hk] at hd
  exact pcsa_delivered_proposal_unique E rho h s N hN j y o u M he hd

/-- Every PC carried by a stored slot-`s` proposal is the honest proposal's PC. -/
theorem pcsa_carried_pc_unique (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) (s : Slot)
    (N : NamedProposal p.n) (hN : HonestNamedProposal p c E rho s N)
    (x : V) (t : Time) (nd : Node p)
    (hr : pcsa_postClock E rho x t = some nd) (C : PC p.n)
    (hm : C ∈ carriedPCs nd.st s) : N.pc = some C := by
  have hmeta := pcsa_metadata_unique E rho h s N hN x t nd hr
  delta carriedPCs at hm
  obtain ⟨w, hw, hf⟩ := List.mem_filterMap.mp (List.mem_filter.mp hm).1
  cases hd : w.decode with
  | none => rw [hd] at hf; cases hf
  | some d =>
    rw [hd] at hf
    cases d with
    | vote k i r => cases hf
    | row i body => cases hf
    | ack k i r => cases hf
    | pc D => cases hf
    | block k M =>
      dsimp only at hf
      split at hf
      · rename_i hs
        have hslot : M.erase.slot = M.slot := by cases M <;> rfl
        have hinfo := hmeta w hw k M hd
        have hk : k = s := hinfo.1.symm.trans (hslot.trans hs)
        obtain rfl := hinfo.2 hk
        exact hf
      · cases hf

omit [DecidableEq V] in
/-- The events up to a delivery at `t` have times at most `t`. -/
private theorem voter_events_le (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hS : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {x : V} {o : Obj p} {t : Time} (hk : rho.events[k]? = some (.deliver x o t)) :
    ∀ k' < k + 1, ∀ e', rho.events[k']? = some e' → e'.time ≤ t := by
  intro k' hk' e' he'
  apply le_of_not_gt
  intro hlt
  have h1 := (Gen.V2.Duty.index_lt_idxBefore_iff hS hk e'.time).mpr hlt
  have h2 := (Gen.V2.Duty.index_lt_idxBefore_iff hS he' e'.time).not.mpr (lt_irrefl _)
  omega

/-- The Formation/RECOVERY deadline of a time no later than `z_{s-1}` is `t_s`. -/
private theorem voter_deadline (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (s : Slot) (hs : 0 < s) (t : Time)
    (ht : t ≤ SA.freezeTime p.toParams (s - 1)) :
    max t (SA.freezeTime p.toParams (s - 1)) + E.Δ = SA.proposalTime p.toParams s := by
  have hs1 : ((s - 1 : Nat) : Int) + 1 = (s : Int) := by
    exact_mod_cast Nat.sub_add_cancel (Nat.one_le_of_lt hs)
  rw [max_eq_right ht, h.delta]
  change (4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ) + p.Δ = 4 * p.Δ * (s : Int)
  have hs' : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by omega
  rw [hs']
  ring

/-- [pcsa34-r4.3b §5.6.1 step 1 (R4)] Under the deadline `max t z_{s-1} + Δ`, a
PC accepted by an honest node no later than `z_{s-1}` has its key held at
every honest node before `t_s`. -/
theorem pcsa_frozen_key_before_proposal (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (s : Slot) (hs : 0 < s) {cut : Time}
    (hD : Gen.V2.Duty.DeliveryWithinOn E rho IsNonRow
      (fun t => max t (SA.freezeTime p.toParams (s - 1)) + E.Δ) cut)
    (hcut : SA.proposalTime p.toParams s ≤ cut)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (j : Nat) (t : Time) (D : PC p.n) (ht : t ≤ SA.freezeTime p.toParams (s - 1))
    (hwf : D.wellFormed = true)
    (hAccept : V2.D.Run.acceptsAt E rho j x (⟨.none, .pc D⟩ : Obj p) t) :
    KeyHeld (V2.D.Run.stateBeforeTime E rho (SA.proposalTime p.toParams s) y).st
      D.slot D.target := by
  have hS := h.valid.toScheduleWellFormed
  have hdl := voter_deadline E rho h s hs t ht
  have hdlz := voter_deadline E rho h s hs _ (le_refl (SA.freezeTime p.toParams (s - 1)))
  have hz : SA.freezeTime p.toParams (s - 1) < SA.proposalTime p.toParams s := by
    rw [← hdlz, max_self]
    exact lt_add_of_pos_right _ E.Δ_pos
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
  obtain ⟨o, hj, _⟩ := hAccept.1
  have hjI : j + 1 ≤ V2.D.Run.idxBefore rho (SA.proposalTime p.toParams s) :=
    Nat.succ_le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff hS hj _).mpr (ht.trans_lt hz))
  cases hpr : (pcsaWith m p c).processed (V2.D.Run.stateBefore E rho (j + 1) y)
      (⟨.none, .pc D⟩ : Obj p) with
  | true =>
    exact pcsa_keyHeld_mono (pcsa_stageOne_mono E rho h.noRestart hF y hy hjI).1
      ((pcsa_processed_pc _ D).mp hpr)
  | false =>
    obtain ⟨t', -, ht2, k, o'', hevk, hh⟩ := hD.relay x hx j (⟨.none, .pc D⟩ : Obj p)
      True.intro t hAccept y hy hpr (by rw [hdl]; exact hcut) (pcsa_pc_not_excluded _ D)
    replace ht2 : t' < SA.proposalTime p.toParams s := by simpa only [hdl] using ht2
    have hkI : k + 1 ≤ V2.D.Run.idxBefore rho (SA.proposalTime p.toParams s) :=
      Nat.succ_le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff hS hevk _).mpr ht2)
    rcases pcsa_handles_pc_store _ o'' D hwf hh with hk | hp
    · rw [← pcsa_deliver_succ E rho hevk] at hk
      exact pcsa_keyHeld_mono (pcsa_stageOne_mono E rho h.noRestart hF y hy hkI).1 hk
    · rw [← pcsa_deliver_succ E rho hevk] at hp
      have hkx : KeyHeld (V2.D.Run.stateBefore E rho (j + 1) x).st D.slot D.target :=
        (pcsa_processed_pc _ D).mp hAccept.2.2
      obtain ⟨C, hC, -, hCt⟩ := (KeyHeld_def _ _ _).mp hkx
      have hTx : D.target ∈ (V2.D.Run.stateBefore E rho (j + 1) x).st.base.blocks := by
        rw [← hCt]
        exact (pcsa_outageStore_stateBefore E rho (j + 1) x hx).pcBlocks C hC
      have hTy := pcsa_indexed_body_within_on E rho h hF hD
        (fun o s N hdec => pcsa_block_isNonRow o s N hdec)
        (by
          intro a b hab
          dsimp only
          exact Int.add_le_add_right (max_le_max hab (le_refl _)) E.Δ)
        (fun t => lt_of_le_of_lt (le_max_left t _) (lt_add_of_pos_right _ E.Δ_pos))
        x y hx hy (j + 1) (SA.freezeTime p.toParams (s - 1))
        (fun k' hk' e' he' => (voter_events_le E rho hS hj k' hk' e' he').trans ht)
        (by show max _ _ + E.Δ ≤ cut; rw [hdlz]; exact hcut) D.target hTx
      change D.target ∈ (V2.D.Run.stateBeforeTime E rho
        (max (SA.freezeTime p.toParams (s - 1)) (SA.freezeTime p.toParams (s - 1)) + E.Δ)
        y).st.base.blocks at hTy
      rw [hdlz, ← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hTy
      have hFA := hF y hy (V2.D.Run.idxBefore rho (SA.proposalTime p.toParams s))
      exact pcsa_keyHeld_of_collectClosed _
        (pcsa_collectClosed_stateBefore E rho h y hy _) D hwf
        (fun a ha => pcsa_ackPool_mono_run E rho h.noRestart y hkI (hp a ha)) hTy
        (pcsa_activeCompatible_genesis _ ((FrameVacuous_def p _).mp hFA).1 D.target)

/-- A post-clock read of an honest node in stage 1 has a vacuous frame. -/
private theorem voter_read_frame (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hF : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest) (k : Nat) (t : Time) :
    FrameVacuous p (clock p (V2.D.Run.stateBefore E rho k x).st t) := by
  have h := hF x hx k
  rw [FrameVacuous_def, controls_def] at h ⊢
  rw [pcsa_body_clock_fg]
  exact h

/-- A held PC of an honest post-clock read is frame-active in stage 1. -/
private theorem voter_read_active (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hF : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest) (k : Nat) (t : Time)
    (A : PC p.n) (hA : A.target ∈ (clock p (V2.D.Run.stateBefore E rho k x).st t).base.blocks) :
    frameActive p (clock p (V2.D.Run.stateBefore E rho k x).st t) A = true := by
  have hO := pcsa_clock_outageStore p _ _ t (pcsa_outageStore_stateBefore E rho k x hx)
  exact (pcsa_frameActive_vacuous p _ (voter_read_frame E rho hF x hx k t) A).mpr
    (hO.lift A.target hA)

/-- [pcsa34-r4.3b §5.3 (F3), §5.6.1 step 1] The voter view at `v_s`: under the
deadline `max t z_{s-1} + Δ` up to `v_s`, every honest voter read at `v_s` has
the target of the honest slot-`s` proposal's PC. -/
theorem pcsa_voter_view_of_delivery (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (s : Slot) (hs : 0 < s) (N : NamedProposal p.n)
    (hN : HonestNamedProposal p c E rho s N) {cut : Time}
    (hD : Gen.V2.Duty.DeliveryWithinOn E rho IsNonRow
      (fun t => max t (SA.freezeTime p.toParams (s - 1)) + E.Δ) cut)
    (hcut : SA.voteTime p.toParams s ≤ cut)
    (y : V) (hy : y ∈ rho.honest) (dst : Node p)
    (hr : pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst) :
    (voterPC p dst.st s).map PC.target = N.pc.map PC.target := by
  have hS := h.valid.toScheduleWellFormed
  have hd := p.deltaPos
  have hts : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
    change SA.proposalTime p.toParams s ≤ SA.proposalTime p.toParams s + p.Δ
    linarith
  obtain ⟨src, hsrc, -, -, hpc⟩ := pcsa_honest_proposal_state E rho h s N hN
  have hsrc' := hsrc
  rw [pcsa_postClock_def, pcsa_preTick_def] at hsrc'
  obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hsrc'
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hp
  subst hc
  have hkT := V2.D.Run.tickIdx?_spec hk
  have hIk : V2.D.Run.idxBefore rho (SA.proposalTime p.toParams s) ≤ k := by
    apply Nat.le_of_not_lt
    intro hlt
    exact lt_irrefl _ ((Gen.V2.Duty.index_lt_idxBefore_iff hS hkT _).mp hlt)
  have hx := hN.1
  have hRecv := pcsa_honest_proposal_from_vote E rho h hF s hs N hN hD _ le_rfl hcut
    y hy dst hr
  apply pcsa_view_of_frozen_receipt p _ dst.st s N.pc hpc.symm
  · intro C hC _
    have hne : SA.voteTime p.toParams s ≠ SA.freezeTime p.toParams (s - 1) := by
      have hz := voter_deadline E rho h s hs _ le_rfl
      rw [max_self, h.delta] at hz
      change SA.proposalTime p.toParams s + p.Δ ≠ SA.freezeTime p.toParams (s - 1)
      intro he
      rw [← hz] at he
      linarith
    obtain ⟨j, u, D, hu, hDs, hDt, hwf, ha⟩ :=
      pcsa_frozen_pc_origin_read_valid E rho h hF y hy (s - 1) _ dst C hr hne hC
    have hkey := pcsa_frozen_key_before_proposal E rho h hF s hs hD (hts.trans hcut)
      y _ hy hx j u D hu hwf ha
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS, KeyHeld_def] at hkey
    obtain ⟨A, hA, hAs, hAt⟩ := hkey
    have hAk := (pcsa_stageOne_mono E rho h.noRestart hF _ hx hIk).1 hA
    have hAc : A ∈ (clock p (V2.D.Run.stateBefore E rho k
        (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)).st
        (SA.proposalTime p.toParams s)).pcs := by
      rw [pcsa_clock_pcs]
      exact hAk
    have hAb := (pcsa_clock_outageStore p _ _ _
      (pcsa_outageStore_stateBefore E rho k _ hx)).pcBlocks A hAc
    refine ⟨A, List.mem_filter.mpr ⟨hAc, voter_read_active E rho hF _ hx k _ A hAb⟩, ?_, ?_⟩
    · rw [hAs, hDs]
    · rw [hAt, hDt]
  · exact fun C hC => pcsa_carried_pc_unique E rho h s N hN y _ dst hr C hC
  · intro D hD
    obtain ⟨hw, hv⟩ := hRecv
    have hval := hv D hD
    refine List.mem_filter.mpr ⟨List.mem_append_right _ ?_, ?_⟩
    · delta carriedPCs
      refine List.mem_filter.mpr ⟨List.mem_filterMap.mpr ⟨_, hw, ?_⟩, hval⟩
      have hslot : N.slot = s := by
        obtain ⟨-, -, hes, -, -⟩ := pcsa_honest_proposal_state E rho h s N hN
        have he : N.erase.slot = N.slot := by cases N <;> rfl
        exact he.symm.trans hes
      change (if N.slot = s then N.pc else none) = some D
      split
      · exact hD
      · contradiction
    · have hb : D.target ∈ dst.st.base.blocks := by
        change (D.wellFormed && decide (D.target ∈ dst.st.base.blocks) &&
          activeCompatible dst.st D.target) = true at hval
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hval
        exact hval.1.2
      have hr' := hr
      rw [pcsa_postClock_def, pcsa_preTick_def] at hr'
      obtain ⟨pre', hp', hc'⟩ := Option.map_eq_some_iff.mp hr'
      obtain ⟨k', -, rfl⟩ := Option.map_eq_some_iff.mp hp'
      subst hc'
      exact voter_read_active E rho hF y hy k' _ D hb
  · intro A hA B hB he
    have hu := pcsa_rootsUnique_stateBefore E rho h k _ hx
    rw [RootsUnique_def] at hu
    have hO := pcsa_clock_outageStore p _ _ (SA.proposalTime p.toParams s)
      (pcsa_outageStore_stateBefore E rho k _ hx)
    have hAb := hO.pcBlocks A (List.mem_filter.mp hA).1
    have hBb := hO.pcBlocks B (List.mem_filter.mp hB).1
    rw [(pcsa_clock_frame p _ _).2.2.2.2] at hAb hBb
    exact hu A.target hAb B.target hBb he

/-- An honest node has a post-clock read at each public time up to the horizon. -/
theorem pcsa_postClock_exists (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) (x : V) (hx : x ∈ rho.honest)
    (t : Time) (hpub : V2.PublicTime E t) (h0 : 0 ≤ t) (hh : t ≤ rho.horizon) :
    ∃ nd, pcsa_postClock E rho x t = some nd := by
  have hm := h.valid.toScheduleWellFormed.tick_total x hx t hpub h0 hh
  rw [pcsa_postClock_def, pcsa_preTick_def]
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp
    (show (V2.D.Run.tickIdx? rho x t).isSome = true from by
      delta V2.D.Run.tickIdx?
      rw [List.findIdx?_isSome, List.any_eq_true]
      exact ⟨_, hm, decide_eq_true ⟨rfl, rfl⟩⟩)
  rw [hj]
  exact ⟨_, rfl⟩

/-- [pcsa34-r4.3b §5.3 (F3), §5.6.1 step 1] The common view field of the
Formation premise, from the deadline `max t z_{s-1} + Δ` up to `v_s`. -/
theorem pcsa_commonView_of_delivery (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (s : Slot) (hs : 0 < s) (N : NamedProposal p.n)
    (hN : HonestNamedProposal p c E rho s N) {cut : Time}
    (hD : Gen.V2.Duty.DeliveryWithinOn E rho IsNonRow
      (fun t => max t (SA.freezeTime p.toParams (s - 1)) + E.Δ) cut)
    (hcut : SA.voteTime p.toParams s ≤ cut) (hhor : SA.voteTime p.toParams s ≤ rho.horizon) :
    ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams s) = true →
      (viewAt p c E rho y s).map (Option.map PC.target) = some (N.pc.map PC.target) := by
  intro y hy _
  have hd := p.deltaPos
  have hpub : V2.PublicTime E (SA.voteTime p.toParams s) := by
    refine ⟨4 * s + 1, ?_⟩
    rw [h.delta]
    change 4 * p.Δ * (s : Int) + p.Δ = ((4 * s + 1 : Nat) : Int) * p.Δ
    push_cast
    ring
  have h0 : 0 ≤ SA.voteTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + p.Δ
    positivity
  obtain ⟨dst, hdst⟩ := pcsa_postClock_exists E rho h y hy _ hpub h0 hhor
  rw [pcsa_viewAt_def, hdst]
  change some ((voterPC p dst.st s).map PC.target) = _
  rw [pcsa_voter_view_of_delivery E rho h hF s hs N hN hD hcut y hy dst hdst]

end AvailableChain.PCSA.Run
end
