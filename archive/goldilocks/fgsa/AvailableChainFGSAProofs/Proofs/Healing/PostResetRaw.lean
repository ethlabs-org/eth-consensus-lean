module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetInvariant -- shake: keep (J5 carrier)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetCompat -- shake: keep (J5 lane input)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetKeep -- shake: keep (J5 lane input)
public import AvailableChainFGSAProofs.Proofs.Healing.ResetTransfer -- shake: keep (J5 lane input)
public import AvailableChainFGSAProofs.Proofs.Healing.SupportSlow

public section

/-! Blueprint 21 H.16:2924–2945, H5:3318–3325; post-reset plan J5 B;
B1/B13/B17/B18. DC: SAME removal of event-prefix guards from raw transfer.
The all-cut input is conditional; this file does not produce its successor. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.AC.Root

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Exact services for each active source and moving read. -/
structure RawServiceScope (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) : Prop where
  late : ∀ (s : Slot) (ix : Nat) (x : V), HealingWindow p E 1 s → x ∈ rho.honest →
    IsGateTick p c rho ix x s → enabledGateAt p c E rho ix x s →
    ProposalSupportScope E rho ix x s (SA.gateTime p.toParams s)
  first : ∀ (s : Slot) (ix iy : Nat) (x y : V), E.t_GST ≤ SA.voteTime p.toParams s →
    x ∈ rho.honest → y ∈ rho.honest → IsGateTick p c rho ix x s →
    rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
    enabledGateAt p c E rho ix x s →
    joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
    FirstTransferScope E rho ix iy x y s
  proposal : ∀ (r : Slot) (ip : Nat) (x : V), HealingWindow p E 1 r → x ∈ rho.honest →
    rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (r + 1))) →
    joinedAt p E rho x (r + 1) (SA.proposalTime p.toParams (r + 1)) →
    ProposalSupportScope E rho ip x r (SA.proposalTime p.toParams (r + 1))
  gates : ∀ s i x, E.t_GST ≤ SA.voteTime p.toParams s → x ∈ rho.honest →
    IsGateTick p c rho i x s → enabledGateAt p c E rho i x s →
    ∀ B, GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B →
    GateReceiptScope E rho i x s
  same : ∀ s, E.t_GST ≤ SA.voteTime p.toParams s →
    SameLabelServiceScope E rho s

private theorem raw_reset_vote_cutoff {w : HealingWitness} (h0r : H0Reset p c E rho w) :
    E.t_GST ≤ slotStartZ p ((w.sStar : Int) - 1) :=
  healing_ready_vote_cutoff E (healing_reset_source_ready h0r)

private theorem raw_reset_later_cutoff {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {s : Slot} (hs : w.sStar ≤ s) : E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
  have hcut := raw_reset_vote_cutoff p c E rho h0r
  have hi : (w.sStar : Int) ≤ s := by exact_mod_cast hs
  change E.t_GST ≤ 4 * p.Δ * ((w.sStar : Int) - 1) at hcut
  change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
  nlinarith [p.deltaPos]

private theorem raw_tick_read_on (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {t : Time} (hi : rho.events[i]? = some (.tick x t))
    (hEpoch : V2.D.restartFree rho x (V2.D.Run.idxBefore rho t) i) :
    rho.stateBefore E i x = rho.stateBeforeTime E t x := by
  let q := fun e : V2.Event V (fgsa p c).Object => decide (e.time < t)
  have hDown : ∀ e f : V2.Event V (fgsa p c).Object, e.key ≤ f.key → q f = true → q e = true := by
    intro e f hef hq
    have hqt : f.time < t := of_decide_eq_true hq
    change toLex (e.time, e.phase) ≤ toLex (f.time, f.phase) at hef
    rcases Prod.Lex.toLex_le_toLex.mp hef with hlt | ⟨heq, _⟩
    · exact decide_eq_true (hlt.trans hqt)
    · exact decide_eq_true (lt_of_eq_of_lt heq hqt)
  have hf := V2.D.Engine.filter_eq_take hs q hDown
  have hni : (rho.events.filter q).length ≤ i := by
    by_contra hc
    have hlt : i < (rho.events.filter q).length := by omega
    have hm : V2.Event.tick x t ∈ rho.events.filter q := by
      rw [hf]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hlt]; exact hi)
    have ht := of_decide_eq_true (List.mem_filter.mp hm).2
    exact lt_irrefl t ht
  change _ = ((rho.events.filter q).foldl (V2.D.World.step E rho) V2.D.World.init) x
  rw [hf]
  apply V2.D.Engine.stateBefore_other_node E rho hni
  intro j e hj hji hget hnode
  have hl : t ≤ e.time := by
    have hh := V2.D.Engine.filter_false_of_index_ge hs q hDown hj hget
    simpa only [q, decide_eq_false_iff_not, not_lt] using hh
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hget
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hk : e.key ≤ (V2.Event.tick x t : V2.Event V (fgsa p c).Object).key := by
    simpa only [hje, hie] using (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hji
  have ht : e.time = t := le_antisymm (V2.D.Engine.time_le_of_key_le _ _ hk) hl
  have he : e = .tick x t := by
    cases e with
    | restart y u =>
      dsimp only [V2.Event.node] at hnode
      subst y
      exact (hEpoch j u hj hji hget).elim
    | tick y u =>
      dsimp only [V2.Event.node] at hnode
      dsimp only [V2.Event.time] at ht
      rw [hnode, ht]
    | deliver y o u =>
      dsimp only [V2.Event.time] at ht
      subst u
      dsimp only [V2.Event.key, V2.Event.time, V2.Event.phase] at hk
      simp [Prod.Lex.toLex_le_toLex] at hk
  have hjEq : j = i := (List.Nodup.getElem_inj_iff hs.nodup).mp (by rw [hje, hie, he])
  omega

private theorem raw_gate_result_of_raw (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    {j : Nat} {x : V} {s : Slot} {B : Block}
    (ht : rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)))
    (hGuard : enabledGateAt p c E rho j x s)
    (hc : SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (V2.D.Run.stateBefore E rho j x).st (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (V2.D.Run.stateBefore E rho j x).st
        (SA.gateTime p.toParams s))) s = some B) :
    gateResultAt p c E rho j = some (some B) := by
  rw [gateResultAt_eq_gateResult p c E rho hs ht, gateResult_eq_saved p c E rho hs ht]
  have hsaved := fgsa_gate_saved_result E rho hs ht
    (fgsa_gate_joined_of_enabled E rho hGuard)
  rw [clockPre_fg] at hc
  exact hsaved.trans (congrArg some hc)


private theorem raw_result_tick {y : V} {j : Slot} {C : Block}
    (hC : gateResult p c E rho y j = some (some C)) :
    ∃ k, IsGateTick p c rho k y j := by
  rw [gateResult_def, gateIn_def, preTick_def] at hC
  cases hk : V2.D.Run.tickIdx? rho y (SA.gateTime p.toParams j) with
  | none => rw [hk] at hC; cases hC
  | some k => exact ⟨k, V2.D.Run.tickIdx?_spec hk⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2924–2945, H5:3318–3325; plan J5 B;
B1/B13/B17/B18. DC: SAME all-cut projection of the four H5 clauses.
Each concrete reader uses a cut past the source tick and its own read.
The input covers every Nat cut, including cuts past rho.events.length.
Only raw_transfer is needed at all cuts; no J4 or J6 field is used. -/
theorem postReset_h5RawTransfer_body {w : HealingWitness}
    (_h0r : H0Reset p c E rho w)
    (raw : ∀ i, PostResetRawTransfer p c E rho w i) :
    H5RawTransfer p c E rho w := by
  change ∀ y j C, y ∈ rho.honest → w.sStar ≤ j →
    gateResult p c E rho y j = some (some C) → _
  intro y j C hy hj hC
  obtain ⟨k, hk⟩ := raw_result_tick p c E rho hC
  have atCut (i : Nat) (hi : k < i) := by
    have h := raw i
    rw [PostResetRawTransfer_def] at h
    exact h k hi y j C hy hj hk hC
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x nd hx hnd lease hlease hlive
    let i := max (k + 1) (timeIdx rho (SA.releaseTime p.toParams j))
    have h := atCut i (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _))
    exact h.1 x nd hx (le_max_right _ _) hnd lease hlease hlive
  · intro x s H hx hs hH
    let i := max (k + 1) (timeIdx rho (SA.voteTime p.toParams s))
    have h := atCut i (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _))
    exact h.2.1 x s H hx.1 hs (le_max_right _ _) hH
  · intro v Q hv hQ
    let i := max (k + 1) (timeIdx rho (SA.proposalTime p.toParams v))
    have h := atCut i (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _))
    exact h.2.2.1 v Q hv (le_max_right _ _) hQ
  · intro a x hx hhor ha
    let i := max (k + 1) (a + 1)
    have h := atCut i (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _))
    exact h.2.2.2 a x (Nat.lt_of_lt_of_le (Nat.lt_succ_self a) (le_max_right _ _))
      hx.1.1 hhor ha

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2926–2932, H.1:673–689; plan J5A shared helper.
B1/B13/B17/B18. DC: SAME strict-majority honest supporter.
The raw result can have low support or a vetoed guard. Its supporter
HEAD is an actual earlier event; no release-threshold premise is used. -/
theorem healing_gate_result_supporter [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hServices : RawServiceScope p c E rho)
    {s : Slot} (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hJoinCut : E.t_GST ≤ slotStartZ p ((s : Int) - 1))
    {ix : Nat} {x : V} {C : Block} (hx : x ∈ rho.honest)
    (hix : IsGateTick p c rho ix x s)
    (hres : gateResultAt p c E rho ix = some (some C)) :
    ∃ k z, z ∈ rho.honest ∧
      rho.events[k]? = some (.tick z (SA.voteTime p.toParams s)) ∧
      Block.Preceq C (headAtIdx p c E rho k s) ∧ k < ix := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hres' := (gateResultAt_eq_gateResult p c E rho hS hix).symm.trans hres
  have hmaj := healing_slow_majority E rho hS hix hres' (Gen.Pure.block_preceq_refl C)
  have hhor := (hS.in_horizon _ (List.mem_of_getElem? hix)).2
  obtain ⟨seat, o, hh, ho, hs, hsup⟩ :=
    healing_slow_honest_seat E rho hrec hgst hhor hx hix
      (hServices.late s ix x (healing_window_of_cut E hJoinCut) hx hix
        (healing_gate_enabled_of_result E rho hS hix hres))
      (healing_gate_enabled_of_result E rho hS hix hres) hmaj
  obtain ⟨H, hH, hHm, _, _, hom, hol⟩ := healing_support_clean_target E rho o ho
  obtain ⟨k, hk, ht⟩ := healing_support_honest_head E rho hrec.base.valid hom hol hs hh
  refine ⟨k, _, hh, hk, ?_, ?_⟩
  · have hlookup : Gen.AC.Root.resolvedTarget?
        (actView (clockPre p (storeAt p c E rho ix x)
          (SA.gateTime p.toParams s))).blocks o = some H :=
      actView_target_of_resolvedHead p _
        (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho ix x) _) o hH
    rw [Gen.AC.Root.voteSupports_def, hlookup] at hsup
    have heq := stored_eq_headVote E rho hrec.base.idealization ix x hHm k
      (rho.seatOf (.base (.head s)) seat) (SA.voteTime p.toParams s) s
      (Option.some.inj ((resolvedHead_root _ o hH).symm.trans ht))
    rw [healing_headAtIdx_tick p c E rho hk]
    exact heq ▸ (Bool.and_eq_true_iff.mp hsup).2
  · apply healing_idx_lt_of_time_lt p c E rho hS hk hix
    change 4 * p.Δ * (s : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]

private theorem raw_process_obligations (st : State p.n) (o : Wire p.n) :
    (process p st o).base.obligations ⊆ st.base.obligations := by
  unfold process
  cases o.decode with
  | none => exact List.Subset.refl _
  | some input =>
    cases input with
    | vote s seat b => rw [admitHead_obligations]
    | row seat body => rw [Internal.admitRow_base]
    | block s N =>
      change (admitBlock p st s N).base.obligations ⊆ st.base.obligations
      unfold admitBlock
      split
      · exact List.Subset.refl _
      · cases parentFG st N.erase with
        | none => exact List.Subset.refl _
        | some P =>
          dsimp only
          split
          · rw [Internal.foldl_admitRow_base]
            split
            · intro row hm
              rwa [admitProposal_obligations_slow] at hm
            · intro row hm
              rw [reconcile_obligations] at hm
              have hold := (List.mem_filter.mp hm).1
              rwa [admitProposal_obligations_slow] at hold
          · exact List.Subset.refl _

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2933–2935; plan J5A C1, R2(c); B13/B17.
DC: INTENTIONAL; DC has no leases. Delivery adds no obligation at any
node. Reconciliation can remove rows, so the conclusion is inclusion. -/
theorem postReset_delivery_no_obligation {i : Nat} {x y : V} {o : Obj p} {t : Time}
    (he : rho.events[i]? = some (.deliver x o t)) :
    (storeAt p c E rho (i + 1) y).base.obligations ⊆
      (storeAt p c E rho i y).base.obligations := by
  change (V2.D.Run.stateBefore E rho (i + 1) y).st.base.obligations ⊆ _
  rw [V2.D.Run.stateBefore_succ E rho he]
  by_cases hxy : x = y
  · subst x
    simp only [V2.D.World.step, Function.update_self]
    exact raw_process_obligations p (storeAt p c E rho i y) (toWire p o)
  · simp only [V2.D.World.step, Function.update_of_ne (Ne.symm hxy)]
    exact List.Subset.refl _

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2933–2938; plan J5A C1, P2(a)(b); B13/B17.
DC: INTENTIONAL; DC has no leases. Expiry, release and reconciliation
only remove rows. A write can merge a deadline only at its own target.
The compatible write-target input is supplied by P1. -/
theorem postReset_resetLease_preserve (w : HealingWitness) (st : State p.n)
    (hlease : ∀ row ∈ st.base.obligations, st.base.now < row.2.2 →
      Block.Compatible row.1 w.CStar) (t : Time) (s : Slot) (B : Block) (g : Nat) (d : Time)
    (hB : Block.Compatible B w.CStar) :
    (∀ row ∈ (GridCO.expire st.base t).obligations, st.base.now < row.2.2 →
      Block.Compatible row.1 w.CStar) ∧
    (∀ row ∈ (SA.Root.release p.toParams st.base s).obligations, st.base.now < row.2.2 →
      Block.Compatible row.1 w.CStar) ∧
    (∀ row ∈ (reconcile st).base.obligations, st.base.now < row.2.2 →
      Block.Compatible row.1 w.CStar) ∧
    (∀ row ∈ (GridCO.writeObligation st.base B g d).obligations,
      st.base.now < row.2.2 → Block.Compatible row.1 w.CStar) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro row hm hlive
    exact hlease row (List.mem_filter.mp hm).1 hlive
  · intro row hm hlive
    exact hlease row (List.mem_filter.mp hm).1 hlive
  · intro row hm hlive
    rw [reconcile_obligations] at hm
    exact hlease row (List.mem_filter.mp hm).1 hlive
  · intro row hm hlive
    change row ∈ st.base.obligations.filter _ ++ [(B, g, _)] at hm
    rcases List.mem_append.mp hm with hold | hnew
    · exact hlease row (List.mem_filter.mp hold).1 hlive
    · rw [List.mem_singleton.mp hnew]
      exact hB

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2933–2938, H.12:2664–2665; plan J5A C2 base;
B1/B13/B17. DC: INTENTIONAL; DC has no leases; SA reset cut.
No stored read is both before and at or after the reset cut. The first
successor still needs the actual reset-release removal proof. -/
theorem postReset_resetLease_base {w : HealingWitness} (_h0r : H0Reset p c E rho w) :
    PostResetResetLeaseCompatible p c E rho w
      (afterTicksIdx rho (SA.releaseTime p.toParams w.sStar)) := by
  rw [PostResetResetLeaseCompatible_def]
  intro j hj x _hx hcut
  exact False.elim (Nat.not_lt_of_ge hcut hj)

private theorem raw_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.1:673–700, H.16:2938–2944; plan J5A A2;
B1/B13/B17/B18. DC: INTENTIONAL moving frame with a direct lease input.
A concrete raw result and receiver HEAD use their own frozen domain.
No HighSrcN, threshold, passed gate, or PhaseInterval is required. -/
theorem healing_first_transfer_raw_domain [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hServices : RawServiceScope p c E rho)
    {s : Slot} (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    {ix : Nat} {x : V} {C : Block} (hx : x ∈ rho.honest)
    (hix : IsGateTick p c rho ix x s)
    (hres : gateResultAt p c E rho ix = some (some C))
    {B : FGBlock (Fin p.n)} (heB : eraseFG B = C)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hJoined : joinedAtTime p (storeAt p c E rho iy y).restartTime
      (SA.releaseTime p.toParams s) = true)
    {X : Finset (FGBlock (Fin p.n))}
    (hXv : X ⊆ voterBlocks p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))) (s + 1))
    (hXc : ∀ W ∈ X, ∀ A, FGBlock.Preceq (storeAt p c E rho iy y).fg.F A →
      FGBlock.Preceq A W → A ∈ X)
    (hD : B ∈ D_at p c E rho iy y X)
    (hlease : ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))).base.obligations, Block.Compatible row.1 C) :
    Block.Preceq C (headAtIdx p c E rho iy (s + 1)) := by
  rw [← heB] at hlease ⊢
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hScope := hServices.first s ix iy x y hgst hx hy hix hiy
    (healing_gate_enabled_of_result E rho hS hix hres)
    (by have htime : SA.voteTime p.toParams (s + 1) = SA.releaseTime p.toParams s := by
          change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ = 4 * p.Δ * (s : Int) + 5 * p.Δ
          push_cast; ring
        have hread := healing_joined_tick_of_guard p c E rho hE hy hiy
          (by simpa only [htime] using hJoined)
        have hs : slotAt p (SA.voteTime p.toParams (s + 1)) = s + 1 := by
          exact (fgsa_postClock_slot (c := c) (rho.stateBefore E iy y) _).2.symm.trans
            (fgsa_vote_slot (c := c) _ (s + 1))
        simpa only [hs] using hread.2.2)
  have hhor := (hS.in_horizon _ (List.mem_of_getElem? hix)).2
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hgst hvd hhor
  let src := actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))
  let dst := FGSA.clock p (storeAt p c E rho iy y) (SA.voteTime p.toParams (s + 1))
  have hres' := (gateResultAt_eq_gateResult p c E rho hS hix).symm.trans hres
  have hprefix : Block.Preceq (eraseFG B) C := by rw [heB]; exact Gen.Pure.block_preceq_refl C
  have hmaj := healing_slow_majority E rho hS hix hres' hprefix
  -- The domain witness of B at the receiver read.
  have hinv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho iy y) _
  have hdfg : dst.fg = (storeAt p c E rho iy y).fg := clock_fg p _ _
  have hRd : FGSA.controls p dst = R_at p c E rho iy y := by
    change KitFG.treeStoreControlsView (heightView p) dst.fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho iy y).fg
    rw [hdfg]
  obtain ⟨_hBX, hFB, hZB, W, hWX, hBW, hloW⟩ :=
    (KitFG.mem_filteredFromView (heightView p) (R_at p c E rho iy y) X B).mp hD
  have hvW : W ∈ voterBlocks p dst (s + 1) := hXv hWX
  have hWdst : W ∈ dst.fg.TF :=
    Next.tree_subset_TF p dst (Finset.mem_filter.mp hvW).1
  have hFB0 : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) (eraseFG B) :=
    eraseFG_preceq hFB
  have hFB' : Block.Preceq (eraseFG dst.fg.F) (eraseFG B) := hdfg ▸ hFB0
  -- The kept path: every block between the live root and B is in the frozen domain.
  have hpath : ∀ C, Block.Prec (liveRoot p dst) C → Block.Preceq C (eraseFG B) →
      C ∈ erasedList dst (filteredFrom p.E p.cfg (FGSA.controls p dst)
        (voterBlocks p dst (s + 1))) := by
    intro C hr hCB
    have hr' : liveRoot p dst ≠ C ∧ Block.Preceq (liveRoot p dst) C := by
      change ((!decide (liveRoot p dst = C)) && Block.preceq (liveRoot p dst) C) = true at hr
      simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Block.Preceq] using hr
    obtain ⟨A, hA, heA, hAW⟩ := eraseFG_ancestor_preceq hinv.fg.closed hWdst
      (Gen.Pure.block_preceq_trans hCB (eraseFG_preceq hBW))
    have hFA : FGBlock.Preceq dst.fg.F A := raw_lift p
      (Gen.Pure.block_preceq_trans (F_preceq_liveRoot p dst hinv) (heA ▸ hr'.2))
    have hZA : FGBlock.Preceq (FGSA.controls p dst).Z A := raw_lift p
      (Gen.Pure.block_preceq_trans (fgsa_Z_preceq_liveRoot p dst) (heA ▸ hr'.2))
    apply List.mem_filter.mpr
    refine ⟨(hinv.baseTree C).mpr ⟨A, hA, heA⟩, decide_eq_true ⟨A, ?_, heA⟩⟩
    rw [KitFG.filteredFrom_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
    exact (KitFG.mem_filteredFromView (heightView p) (FGSA.controls p dst) _ A).mpr
      ⟨hXv (hXc W hWX A (hdfg ▸ hFA) hAW), hFA, hZA, W, hvW, hAW, hRd ▸ hloW⟩
  -- The live root is compatible with B: every surviving lease passed the release.
  have hrows := hlease
  have hanchor : Block.Compatible (liveRoot p dst) (eraseFG B) := by
    have hselect := Gen.Pure.foldl_select_mem (fun (best b : Block) =>
      best.depth < b.depth || (best.depth == b.depth && best.root < b.root))
      (dst.base.obligations.filterMap (fun row =>
        if dst.base.now < row.2.2 && decide (∃ X ∈ FGSA.fullTree p dst, eraseFG X = row.1)
        then some row.1 else none)) (eraseFG (FGSA.controls p dst).Z)
    change FGSA.liveRoot p dst = _ ∨ FGSA.liveRoot p dst ∈ _ at hselect
    rcases hselect with he | hm
    · rw [he, hRd]
      exact Gen.Pure.block_compatible_of_common (eraseFG_preceq hZB)
        (Gen.Pure.block_preceq_refl _)
    · obtain ⟨row, hr, hrow⟩ := List.mem_filterMap.mp hm
      split at hrow
      · rw [← Option.some.inj hrow]
        exact hrows row hr
      · contradiction
  -- Majority and rival dominance at the receiver (forward and reverse relay).
  have hforward : ∀ o ∈ GridCO.cleanSupport p.toParams.engine src s, ∀ seat,
      GridCO.headSeat? o = some seat → Gen.AC.Root.voteSupports src.blocks (eraseFG B) o = true →
      (o ∈ FGSA.headSupport p dst (s + 1) ∧
        Gen.AC.Root.voteSupports dst.base.blocks (eraseFG B) o = true) ∨
        GridCO.equivocates (FGSA.headVotes p dst (s + 1)) seat = true := by
    intro o' ho' seat hs' hsup'
    obtain ⟨K', hK', hKm', hKst', _, _, _⟩ := healing_support_clean_target E rho o' ho'
    have hBK' : Block.Preceq (eraseFG B) K' := by
      have hlookup : Gen.AC.Root.resolvedTarget? src.blocks o' = some K' :=
        actView_target_of_resolvedHead p _
          (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho ix x) _) o' hK'
      rw [Gen.AC.Root.voteSupports_def, hlookup] at hsup'
      exact (Bool.and_eq_true_iff.mp hsup').2
    obtain ⟨Kfg', hKe', hpath'⟩ := healing_support_target_path_on
      (hroots := hrec.base.receiptIdealization) E rho hS hy hiy
      (hScope.epoch.mono (fgsa_idxBefore_mono rho (by
        change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
        linarith [p.deltaPos])) le_rfl) K'
      (hScope.targets K' hKm' hKst' (Gen.Pure.block_preceq_trans hFB0 hBK'))
    exact fgsa_cleanSupport_forward_relay_on_receipt E rho hE s hx hy hix hiy o' ho'
      seat hs' (fun b he => hScope.forward seat b (he ▸ ho')) Kfg' (hKe' ▸ hK')
      (eraseFG B) (hKe' ▸ hBK') hpath' hFB'
  have htr := Gen.AC.Root.transfer src.blocks dst.base.blocks
    (GridCO.cleanSupport p.toParams.engine src s) (GridCO.lateVotes p.toParams.engine src s)
    (FGSA.headVotes p dst (s + 1)) (FGSA.headSupport p dst (s + 1)) (eraseFG B)
    (fun _ ho' => fgsa_early_subset_late p src s (List.mem_filter.mp ho').1)
    (fgsa_cleanSupport_seat_clean_late p src s) hforward
    (fgsa_headVotes_backward_relay_on_receipt E rho hE s ix iy x y hx
      (fun q b hb => hScope.backward q b (Or.inr hb)))
    (fgsa_headSupport_subset_headVotes E rho hE iy y s) hmaj
  rw [Gen.AC.Root.TransferBounds_def] at htr
  rw [healing_headAtIdx_tick p c E rho hiy]
  rw [fgsa_headVote_eq_filtered, ite_eq_right (Nat.succ_ne_zero s)]
  exact fgsa_headInTree_covers_of_transfer p dst _ _ _ (eraseFG B) hanchor hpath
    htr.2.2.2.2.2.1 htr.2.2.2.2.2.2


private theorem raw_result_sync [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (_hServices : RawServiceScope p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {ix : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hix : IsGateTick p c rho ix x s)
    (hres : gateResultAt p c E rho ix = some (some C))
    (hB : Block.Preceq w.CStar (eraseFG B)) (hBC : Block.Preceq (eraseFG B) C) :
    E.t_GST < SA.voteTime p.toParams s := by
  have hs := hrec.base.valid.toScheduleWellFormed
  let pre := clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s)
  have hinv : CStoreInv p pre := cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho ix x) _
  have hglobal := (gateResultAt_eq_gateResult p c E rho hs hix).symm.trans hres
  have hmaj := healing_slow_majority E rho hs hix hglobal (Gen.Pure.block_preceq_refl C)
  let src := actView pre
  let supp := GridCO.cleanSupport p.toParams.engine src s
  have hmaj' : GridCO.voterCount (GridCO.lateVotes p.toParams.engine src s) <
      2 * GridCO.goldfishScore src.blocks supp supp C := hmaj
  have hpos : 0 < GridCO.goldfishScore src.blocks supp supp C := by omega
  rw [Gen.AC.Root.vote_pool_score_card] at hpos
  obtain ⟨seat, hseat⟩ := Finset.card_pos.mp hpos
  have hsup := (Finset.mem_filter.mp hseat).2
  have hclean : GridCO.equivocates supp seat = false :=
    fgsa_cleanSupport_no_equivocation p src s seat
  rw [hclean, Bool.false_or] at hsup
  obtain ⟨o, ho, _, hvs⟩ := (Gen.AC.Root.vote_pool_support_witness src.blocks supp seat C).mp hsup
  obtain ⟨K, hK, hKm, _, _, _, _⟩ := healing_support_clean_target E rho o ho
  have hCK : Block.Preceq C K := by
    have hlookup : Gen.AC.Root.resolvedTarget? src.blocks o = some K :=
      actView_target_of_resolvedHead p pre hinv o hK
    rw [Gen.AC.Root.voteSupports_def, hlookup] at hvs
    exact (Bool.and_eq_true_iff.mp hvs).2
  have hKpre : K ∈ pre.base.blocks := by
    change K ∈ (clockPre p (storeAt p c E rho ix x) _).base.blocks
    rw [(clockPre_fields p _ _).2.1]
    exact hKm
  obtain ⟨W, hW, heW⟩ := (hinv.baseTree K).mp hKpre
  have hBW : Block.Preceq (eraseFG B) (eraseFG W) := by
    rw [heW]
    exact Gen.Pure.block_preceq_trans hBC hCK
  obtain ⟨A, hA, heA, _⟩ := eraseFG_ancestor_preceq hinv.fg.closed hW hBW
  have hAB : A = B := eraseFG_injective heA
  subst A
  have hheld : B ∈ (storeAt p c E rho ix x).fg.TF := by
    change B ∈ (clockPre p _ _).fg.TF at hA
    rwa [clockPre_fg] at hA
  obtain ⟨_, _, _, C0, _, _, _, he0, hh0⟩ := h0r.fresh
  have hC0B : FGBlock.Preceq C0 B := raw_lift p (by rw [he0]; exact hB)
  have hhB : w.M + 1 ≤ (heightView p B).h := by
    rw [← hh0]
    exact (fgCertificateLaws p).height.h_mono hC0B
  have hafter : w.u₀ < SA.gateTime p.toParams s := by
    by_contra hn
    have hixCut := healing_phase_lt_timeIdx p c E rho hs hix (not_lt.mp hn)
    have hheldCut := (fgsa_store_durable p c E rho hixCut.le x).1 hheld
    have hI : KitFG.FGStoreInvariant (heightView p) (finalityView p)
        (storeAt p c E rho (timeIdx rho w.u₀) x).fg :=
      (cstoreInv_stateBefore E rho (timeIdx rho w.u₀) x).fg
    have hBh : (heightView p B).h ≤ (storeAt p c E rho (timeIdx rho w.u₀) x).fg.h_max := by
      rw [hI.hmax]
      exact (Finset.le_sup (f := fun A => (heightView p A).h) hheldCut).trans (le_max_left _ _)
    have hMh : (storeAt p c E rho (timeIdx rho w.u₀) x).fg.h_max ≤ w.M := by
      rw [h0r.frontier]
      delta honestFrontier
      rw [V2.D.Engine.readAt_eq_stateBefore hs]
      exact Finset.le_sup (f := fun z => (storeAt p c E rho (timeIdx rho w.u₀) z).fg.h_max) hx
    exact Nat.not_succ_le_self w.M (hhB.trans (hBh.trans hMh))
  have hR : (2 : Int) ≤ p.R := by exact_mod_cast p.RLarge
  have hgap : 5 * p.Δ < 2 * P p := by
    change 5 * p.Δ < 2 * (4 * (p.R : Int) * p.Δ)
    nlinarith [p.deltaPos]
  have hgv : SA.gateTime p.toParams s = SA.voteTime p.toParams s + 5 * p.Δ := by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ = 4 * p.Δ * (s : Int) + p.Δ + 5 * p.Δ
    ring
  rw [hgv] at hafter
  linarith [h0r.cut_lower, healing_recoveryStart_ge p E]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15:2893–2900; plan J5A shared slow-window helper;
B1/B13/B17/B18. DC: INTENTIONAL reset frontier and SA saved results.
Each actual saved result covering a reset extension has its own
synchronous label. No earliest-window synchrony premise is required. -/
theorem postReset_slow_window_sync [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hServices : RawServiceScope p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {i : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest)
    (hsaved : GridCO.savedGenuine (storeAt p c E rho i x).base s = some (some C))
    (hB : Block.Preceq w.CStar (eraseFG B)) (hBC : Block.Preceq (eraseFG B) C) :
    E.t_GST < SA.voteTime p.toParams s := by
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨ix, _, hix, hres⟩ := healing_saved_origin_on E rho hs hsaved
  have hat := (gateResultAt_eq_gateResult p c E rho hs hix).trans hres
  exact raw_result_sync p c E rho hrec hServices h0r hx hix hat hB hBC

omit [DecidableEq V] in
private theorem raw_timeIdx_le (hs : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {ev : V2.Event V (Obj p)} (hk : rho.events[k]? = some ev)
    {t : Time} (ht : t < ev.time) : timeIdx rho t ≤ k := by
  have hcut : timeIdx rho t ≤ V2.D.Run.idxBefore rho ev.time := by
    change (rho.events.filter (fun e => decide (e.time ≤ t))).length ≤
      (rho.events.filter (fun e => decide (e.time < ev.time))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he =>
      decide_eq_true (lt_of_le_of_lt (of_decide_eq_true he) ht))
  exact hcut.trans (not_lt.mp (fun hn => lt_irrefl _
    ((Gen.V2.Duty.index_lt_idxBefore_iff hs hk _).mp hn)))

private theorem raw_head_read (hs : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {x : V} {s : Slot}
    (hk : rho.events[k]? = some (.tick x (SA.voteTime p.toParams s))) :
    headAtLabel p c E rho x s = some (headAtIdx p c E rho k s) := by
  rw [healing_headAtIdx_tick p c E rho hk]
  delta headAtLabel
  rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hk]
  rfl

section ResetCompatibility
variable [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hServices : RawServiceScope p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))

include hrec hServices emittedNonempty emittedName

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2930–2932; plan J5A A1(b) and P1;
B1/B13/B17/B18. DC: SAME compatibility in a concrete honest HEAD.
At the reset label use IF.6. At a later label use the reset result's
HEAD clause at cut i and the raw result's earlier honest supporter.
Assembly supplies sourceDiscipline_emittedNonempty and emittedName. -/
theorem postReset_raw_reset_compatible {w : HealingWitness}
    (h0r : H0Reset p c E rho w) {i : Nat} (hinv : PostResetInv p c E rho w i)
    {ix : Nat} {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hix : IsGateTick p c rho ix x s)
    (hres : gateResultAt p c E rho ix = some (some C)) (hcut : ix ≤ i) :
    Block.Compatible w.CStar C := by
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨_, y0, _, C0, ha, _, hsource, he0, _⟩ := h0r.fresh
  obtain ⟨_, G0, _, hG0, hC0G, _⟩ :=
    healing_source_decode p c E rho emittedNonempty emittedName ha hsource
  rw [← h0r.label] at hG0
  have hresetG : Block.Preceq w.CStar G0 := he0 ▸ hC0G
  have hres' := (gateResultAt_eq_gateResult p c E rho hs hix).symm.trans hres
  have hgst : E.t_GST ≤ SA.voteTime p.toParams s := by
    apply h0r.synchronous.trans
    change 4 * p.Δ * (w.sStar : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    have hlabel' : (w.sStar : Int) ≤ s := by exact_mod_cast hlabel
    nlinarith [p.deltaPos]
  rcases eq_or_lt_of_le hlabel with heq | hlt
  · subst s
    have hhor := (hs.in_horizon _ (List.mem_of_getElem? hix)).2
    have hvd : SA.voteTime p.toParams w.sStar + E.Δ ≤
        SA.gateTime p.toParams w.sStar := by
      rw [hrec.base.delta]
      change 4 * p.Δ * (w.sStar : Int) + p.Δ + p.Δ ≤
        4 * p.Δ * (w.sStar : Int) + 6 * p.Δ
      linarith [p.deltaPos]
    have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
      hrec.sync (fgsaDelay_nonrow E.Δ _) hgst hvd hhor
    exact Gen.Pure.block_compatible_of_preceq_compatible hresetG
      (fgsa_sameLabel_on p c E rho hrec.base.valid w.sStar
        (hServices.same w.sStar h0r.synchronous) hrec.base.idealization
        y0 x G0 C ha.1 hx hG0 hres')
  · obtain ⟨k0, hk0⟩ := raw_result_tick p c E rho hG0
    have ht : SA.gateTime p.toParams w.sStar < SA.gateTime p.toParams s := by
      change 4 * p.Δ * (w.sStar : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
      have hlt' : (w.sStar : Int) < s := by exact_mod_cast hlt
      nlinarith [p.deltaPos]
    have hk0i : k0 < i :=
      (healing_idx_lt_of_time_lt p c E rho hs hk0 hix ht).trans_le hcut
    obtain ⟨kh, z, hz, hkh, hCH, _⟩ :=
      healing_gate_result_supporter p c E rho hrec hServices hgst
        (raw_reset_later_cutoff p c E rho h0r hlabel) hx hix hres
    have hread : timeIdx rho (SA.voteTime p.toParams s) ≤ i := by
      apply (raw_timeIdx_le p c E rho hs hix ?_).trans hcut
      change 4 * p.Δ * (s : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
      linarith [p.deltaPos]
    have hraw := hinv.raw_transfer
    rw [PostResetRawTransfer_def] at hraw
    have hG0H := (hraw k0 hk0i y0 w.sStar G0 ha.1 le_rfl hk0 hG0).2.1
      z s (headAtIdx p c E rho kh s) hz (Nat.succ_le_of_lt hlt) hread
      (raw_head_read p c E rho hs hkh)
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_trans hresetG hG0H) hCH

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2933–2938; plan J5A P1; B1/B13/B17/B18.
DC: INTENTIONAL; DC has no leases. A post-reset passing gate can write
only targets compatible with CStar. Only raw_transfer at cut i is used.
The writing event can be i; raw_transfer at i+1 is not an input. -/
theorem postReset_noRewrite {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {ix : Nat} {x : V} {s : Slot} {C B : Block} {g : Nat} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hix : IsGateTick p c rho ix x s)
    (_hpass : gatePassedAt p c E rho ix)
    (hres : gateResultAt p c E rho ix = some (some C)) (hcut : ix ≤ i)
    (hkey : (B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s C) :
    Block.Compatible B w.CStar := by
  have hcomp := postReset_raw_reset_compatible p c E rho hrec hServices
    emittedNonempty emittedName
    h0r hinv hx hlabel hix hres hcut
  change Block.compatible w.CStar C = true at hcomp
  rw [Gen.Pure.block_compatible_comm] at hcomp
  exact Gen.Pure.block_compatible_of_preceq_compatible (healing_support_key_cases p hkey).2.2.1
    hcomp

end ResetCompatibility

omit [DecidableEq V] in
private theorem raw_tick_cut (hs : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {x : V} {t : Time} (hk : rho.events[k]? = some (.tick x t)) :
    k < afterTicksIdx rho t := by
  by_contra hn
  have hc : cutPred (P := fgsa p c) t (.tick x t) = true := by
    change decide (toLex (t, 1) ≤ toLex (t, 1)) = true
    exact decide_eq_true le_rfl
  have hf := V2.D.Engine.filter_false_of_index_ge hs (cutPred t)
    (fun e f h ef => decide_eq_true (h.trans (of_decide_eq_true ef)))
    (Nat.le_of_not_gt hn) hk
  rw [hc] at hf
  contradiction

private theorem raw_F_read (b : Nat) (y : V) :
    F_at p c E rho b y = eraseFG (storeAt p c E rho b y).fg.F := by rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.2:721–734, H.16:2940–2944; plan J5A A4;
B1/B13/B17/B18. DC: INTENTIONAL moving finality and SA leases.
For any block covered by the preceding HEAD batches, the next gate
establishes output coverage. Event induction preserves it on HealSuffix.
Assembly supplies fgsa_rMono; service and PhaseInterval are not inputs. -/
theorem healing_output_moving_suffix_at [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (hServices : RawServiceScope p c E rho)
    (mono : RMonoAll p c E rho)
    {s : Slot} {B : Block} {cut : Nat}
    (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hBatches : ∀ l, s + 1 ≤ l → timeIdx rho (SA.voteTime p.toParams l) ≤ cut →
      SA.voteTime p.toParams l ≤ rho.horizon →
      Gen.Pure.Batch (joinedHonest p E rho (SA.voteTime p.toParams l)).card
        (Gen.V2.Duty.faulty rho).card)
    (hguard : SA.gateTime p.toParams s + 4 * p.Δ ≤ rho.horizon)
    (hheads : ∀ l, s + 1 ≤ l → timeIdx rho (SA.voteTime p.toParams l) ≤ cut →
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z l = some K → Block.Preceq B K)
    (hfinality : ∀ b, b ≤ cut → ∀ y, y ∈ rho.honest →
      V2.D.Run.idxBefore rho (SA.gateTime p.toParams (s + 1)) ≤ b →
      Block.Compatible (F_at p c E rho b y) B)
    (hlease : ∀ j y, y ∈ rho.honest → IsGateTick p c rho j y (s + 1) → j ≤ cut →
      Block.Preceq (F_at p c E rho j y) B →
      ∀ row ∈ (storeAt p c E rho j y).base.obligations, Block.Compatible row.1 B) :
    ∀ a y, y ∈ rho.honest → a ≤ cut →
      HealSuffix p c rho (SA.gateTime p.toParams s + 4 * p.Δ) a →
      Block.Preceq B (S_at p c E rho a y) := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hd := p.deltaPos
  have hG : SA.gateTime p.toParams s + 4 * p.Δ = SA.gateTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ + 4 * p.Δ =
      4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    push_cast
    ring
  rw [hG] at hguard ⊢
  intro a y hy hacut hsuffix
  have hg := (isGateTime_iff p (SA.gateTime p.toParams (s + 1))).mpr ⟨s + 1, rfl⟩
  delta HealSuffix healStart at hsuffix
  rw [hg, ite_eq_left rfl] at hsuffix
  have hai := hsuffix.1
  let a0 := afterTicksIdx rho (SA.gateTime p.toParams (s + 1))
  have htime : ((4 * (s + 1) + 6 : Nat) : Time) * p.Δ =
      SA.gateTime p.toParams (s + 1) := by
    change _ = 4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨j1, hj1, _⟩ := fgsa_tick_total E rho hs hrec.base.delta y hy
    (4 * (s + 1) + 6) (htime ▸ hguard)
    (htime ▸ hrec.awake y hy _ (by
      refine hgst.trans ?_
      change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
      push_cast
      nlinarith [p.deltaPos]) hguard)
  rw [htime] at hj1
  have hj1a0 : j1 < a0 := raw_tick_cut p c E rho hs hj1
  have hcut : V2.D.Run.stateBefore E rho a0 y = V2.D.Run.stateBefore E rho (j1 + 1) y := by
    rw [← congrFun (afterTicks_eq_stateBefore E rho hs _) y, afterTicks_node E rho hs hj1,
      V2.D.Run.stateBefore_succ E rho hj1]
    simp only [V2.D.World.step, Function.update_self]
  have hidx : V2.D.Run.idxBefore rho (SA.gateTime p.toParams (s + 1)) ≤ a0 := by
    have h := (preIdx_le_afterTicksIdx E rho hs (SA.gateTime p.toParams (s + 1))).1
    rw [V2.D.Run.idxBefore_def]
    exact h
  have hj1i : V2.D.Run.idxBefore rho (SA.gateTime p.toParams (s + 1)) ≤ j1 :=
    not_lt.mp (fun hn => lt_irrefl _ ((Gen.V2.Duty.index_lt_idxBefore_iff hs hj1 _).mp hn))
  have hgst1 : E.t_GST ≤ SA.voteTime p.toParams (s + 1) := by
    apply hgst.trans
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hFc (b : Nat) (hb : V2.D.Run.idxBefore rho (SA.gateTime p.toParams (s + 1)) ≤ b)
      (hbc : b ≤ cut) :
      Block.Preceq B (eraseFG (storeAt p c E rho b y).fg.F) ∨
        Block.Preceq (eraseFG (storeAt p c E rho b y).fg.F) B := by
    have hf := hfinality b hbc y hy hb
    rw [raw_F_read p c E rho b y] at hf
    rcases Bool.or_eq_true_iff.mp hf with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hanchor (b : Nat) (h : Block.Preceq B (eraseFG (storeAt p c E rho b y).fg.F)) :
      Block.Preceq B (S_at p c E rho b y) :=
    Gen.Pure.block_preceq_trans h (fgsaAC_anchor_le_output E rho b y)
  have hFmono {b d : Nat} (hbd : b ≤ d)
      (h : Block.Preceq (eraseFG (storeAt p c E rho d y).fg.F) B) :
      Block.Preceq (eraseFG (storeAt p c E rho b y).fg.F) B :=
    Gen.Pure.block_preceq_trans (eraseFG_preceq (mono b d y hy hbd).1) h
  have hbase : Block.Preceq B (S_at p c E rho (j1 + 1) y) := by
    rcases hFc (j1 + 1) (hj1i.trans (Nat.le_succ _)) (by omega) with hBF | hFB
    · exact hanchor _ hBF
    have hFB0 := hFmono (Nat.le_succ _) hFB
    have hread : timeIdx rho (SA.voteTime p.toParams (s + 1)) ≤ cut := by
      apply (raw_timeIdx_le p c E rho hs hj1 ?_).trans (show j1 ≤ cut by omega)
      change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ <
        4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
      linarith
    exact healing_output_gate_step E rho hrec hgst1 hguard (hheads (s + 1) le_rfl hread)
      hy hj1 (healing_support_gate_scope_of_batch E rho
        (hServices.gates (s + 1) j1 y hgst1 hy hj1
          (healing_recovery_later_gate E rho hrec hgst le_rfl hy hj1) B
          (healing_support_gate_geometry E rho hs (hheads (s + 1) le_rfl hread)
            (by rw [clockPre_fg]; exact hFB0)))
        (hBatches (s + 1) le_rfl hread (by
          apply le_trans ?_ hguard
          change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ ≤
            4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
          linarith))) hFB0
      (Or.inr (hlease j1 y hy hj1 (by omega) hFB0))
  have h0 : Block.Preceq B (S_at p c E rho a0 y) := by
    rw [S_at_def]
    change Block.Preceq B (V2.D.Run.stateBefore E rho a0 y).st.base.stableRecord
    rw [hcut]
    exact hbase
  suffices hn : ∀ n, a0 + n ≤ cut → Block.Preceq B (S_at p c E rho (a0 + n) y) by
    have h := hn (a - a0) (by omega)
    rwa [Nat.add_sub_cancel' hai] at h
  intro n
  induction n with
  | zero => intro _; exact h0
  | succ n ih =>
    intro hn
    have hIH := ih (by omega)
    let b := a0 + n
    have hb : V2.D.Run.idxBefore rho (SA.gateTime p.toParams (s + 1)) ≤ b :=
      hidx.trans (Nat.le_add_right _ _)
    change Block.Preceq B (S_at p c E rho (b + 1) y)
    rcases hFc (b + 1) (hb.trans (Nat.le_succ _)) hn with hBF | hFB
    · exact hanchor _ hBF
    have hFb := hFmono (Nat.le_succ _) hFB
    rcases fgsaAC_output_step E rho b y with hsame | ⟨l, hl⟩ | hrc | ⟨t, hr, _⟩
    · rw [S_at_def]
      change Block.Preceq B ((fgsaAC E rho).output (b + 1) y)
      rw [hsame]
      exact hIH
    · have hgateLower : SA.gateTime p.toParams (s + 1) ≤ SA.gateTime p.toParams l :=
        not_lt.mp (fun h => absurd ((Gen.V2.Duty.index_lt_idxBefore_iff hs hl _).mpr h)
          (not_lt.mpr hb))
      have hlower : s + 1 ≤ l := by
        change 4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ ≤
          4 * p.Δ * (l : Int) + 6 * p.Δ at hgateLower
        have h : ((s + 1 : Nat) : Int) ≤ l := by nlinarith
        exact_mod_cast h
      have hgw : E.t_GST ≤ SA.voteTime p.toParams l := by
        apply hgst1.trans
        change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (l : Int) + p.Δ
        have h : ((s + 1 : Nat) : Int) ≤ l := by exact_mod_cast hlower
        nlinarith
      have hread : timeIdx rho (SA.voteTime p.toParams l) ≤ cut := by
        apply (raw_timeIdx_le p c E rho hs hl ?_).trans (show b ≤ cut by omega)
        change 4 * p.Δ * (l : Int) + p.Δ < 4 * p.Δ * (l : Int) + 6 * p.Δ
        linarith
      exact healing_output_gate_step E rho hrec hgw
        (hs.in_horizon _ (List.mem_of_getElem? hl)).2 (hheads l hlower hread) hy hl
        (healing_support_gate_scope_of_batch E rho
          (hServices.gates l b y hgw hy hl
            (healing_recovery_later_gate E rho hrec hgst hlower hy hl) B
            (healing_support_gate_geometry E rho hs (hheads l hlower hread)
              (by rw [clockPre_fg]; exact hFb))) (hBatches l hlower hread (by
                apply le_trans ?_ (hs.in_horizon _ (List.mem_of_getElem? hl)).2
                change 4 * p.Δ * (l : Int) + p.Δ ≤ 4 * p.Δ * (l : Int) + 6 * p.Δ
                linarith))) hFb
        (Or.inl hIH)
    · obtain ⟨_, _, _, _, _, _, hout⟩ := hrc
      rw [S_at_def]
      change Block.Preceq B ((fgsaAC E rho).output (b + 1) y)
      rw [hout, Gen.AC.normalizeOutput_def]
      have ha : Block.preceq ((fgsaAC E rho).anchor (b + 1) y)
          ((fgsaAC E rho).output b y) = true := Gen.Pure.block_preceq_trans hFB hIH
      simp only [ha]
      exact hIH
    · rw [S_at_def] at hIH ⊢
      change Block.Preceq B (rho.stateBefore E (b + 1) y).st.base.stableRecord
      rw [V2.D.Run.stateBefore_succ E rho hr]
      simp only [V2.D.World.step, Function.update_self]
      change Block.Preceq B (acRestart p (rho.stateBefore E b y).st t).base.stableRecord
      rw [acRestart_stableRecord]
      exact hIH

private theorem raw_clock_compatible (w : HealingWitness) (st : State p.n) (t : Time)
    (hold : ∀ row ∈ st.base.obligations, st.base.now < row.2.2 →
      Block.Compatible row.1 w.CStar) (hnow : st.base.now ≤ t)
    (hresult : ∀ s C, t = SA.gateTime p.toParams s →
      joinedNow p (clockPre p st t) = true →
      SA.Root.confirmationFrom p.toParams
        (eraseFG (clockPre p st t).fg.F) (actView (clockPre p st t)) s = some C →
      Block.Compatible C w.CStar) :
    ∀ row ∈ (FGSA.clock p st t).base.obligations, Block.Compatible row.1 w.CStar := by
  have hpre : ∀ row ∈ (clockPre p st t).base.obligations,
      Block.Compatible row.1 w.CStar := by
    intro row hm
    exact hold row ((clockPre_obligations_sublist p st t).subset hm)
      (hnow.trans_lt (healing_clockPre_live st t row hm))
  intro row hm
  change row ∈ (if isGateTime p t then
    gateStep p (clockPre p st t) ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
    else clockPre p st t).base.obligations at hm
  split at hm
  · rename_i hgate
    let s := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
    let pre := clockPre p st t
    have htime : t = SA.gateTime p.toParams s :=
      beq_iff_eq.mp (Bool.and_eq_true_iff.mp hgate).2
    cases hsaved : GridCO.savedGenuine pre.base s with
    | some saved =>
      rw [gateStep_saved p pre s (by rw [hsaved]; rfl), normalizeS_fields] at hm
      exact hpre row hm
    | none =>
      by_cases hJ : joinedNow p pre = true
      swap
      · rw [gateStep_unjoined_eq p pre s hsaved (Bool.eq_false_of_ne_true hJ),
          normalizeS_fields] at hm
        change row ∈ pre.base.obligations at hm
        exact hpre row hm
      have he : (gateStep p pre s).base.obligations =
          (SA.Root.gateFrom p.toParams (eraseFG pre.fg.F) (actView pre) s).obligations := by
        unfold gateStep
        rw [normalizeS_fields]
        simp only [hsaved, Option.isSome_none, Bool.false_eq_true, ite_false,
          hJ, Bool.not_true]
        rfl
      rw [he] at hm
      cases hc : SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) s with
      | none =>
        unfold SA.Root.gateFrom GridCO.gateFrom at hm
        rw [show GridCO.confirmationFrom p.toParams.engine
          (eraseFG pre.fg.F) (actView pre) s = none from hc] at hm
        exact hpre row hm
      | some C =>
        cases hg : (actView pre).obligations.any (fun r => !Block.compatible r.1 C) with
        | true =>
          unfold SA.Root.gateFrom GridCO.gateFrom at hm
          rw [show GridCO.confirmationFrom p.toParams.engine
            (eraseFG pre.fg.F) (actView pre) s = some C from hc] at hm
          dsimp only at hm
          rw [hg, ite_eq_left rfl] at hm
          exact hpre row hm
        | false =>
          rw [gateFrom_eq_writeKeys_fgsa p.toParams (eraseFG pre.fg.F) (actView pre) s C hc hg]
            at hm
          rcases writeKeys_row_cases _ _ _ row hm with hold | ⟨hkey, _⟩
          · exact hpre row hold
          · exact Gen.Pure.block_compatible_of_preceq_compatible
              (healing_support_key_cases p hkey).2.2.1 (hresult s C htime hJ hc)
  · exact hpre row hm
/-- The original H1 consumer retains its exact batch callback type. -/
theorem healing_output_moving_suffix [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (hServices : RawServiceScope p c E rho)
    (mono : RMonoAll p c E rho)
    {s : Slot} {B : Block} {cut : Nat}
    (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hBatches : ∀ l, s + 1 ≤ l → timeIdx rho (SA.voteTime p.toParams l) ≤ cut →
      Gen.Pure.Batch (joinedHonest p E rho (SA.voteTime p.toParams l)).card
        (Gen.V2.Duty.faulty rho).card)
    (hguard : SA.gateTime p.toParams s + 4 * p.Δ ≤ rho.horizon)
    (hheads : ∀ l, s + 1 ≤ l → timeIdx rho (SA.voteTime p.toParams l) ≤ cut →
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z l = some K → Block.Preceq B K)
    (hfinality : ∀ b, b ≤ cut → ∀ y, y ∈ rho.honest →
      V2.D.Run.idxBefore rho (SA.gateTime p.toParams (s + 1)) ≤ b →
      Block.Compatible (F_at p c E rho b y) B)
    (hlease : ∀ j y, y ∈ rho.honest → IsGateTick p c rho j y (s + 1) → j ≤ cut →
      Block.Preceq (F_at p c E rho j y) B →
      ∀ row ∈ (storeAt p c E rho j y).base.obligations, Block.Compatible row.1 B) :
    ∀ a y, y ∈ rho.honest → a ≤ cut →
      HealSuffix p c rho (SA.gateTime p.toParams s + 4 * p.Δ) a →
      Block.Preceq B (S_at p c E rho a y) := by
  exact healing_output_moving_suffix_at p c E rho hrec hServices mono hgst
    (fun l hsl hcut _ => hBatches l hsl hcut) hguard hheads hfinality hlease


section ResetLeaseStep
variable [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hServices : RawServiceScope p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (xing : RXing p c E rho) (cap : RCap p c E rho) (source : TSrc p c E rho)

include hrec hServices emittedNonempty emittedName xing cap source

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.12:2664–2665, H.16:2933–2935; plan J5A P0;
B1/B13/B17/B18. DC: INTENTIONAL; DC has no leases; SA fast reset release.
The reset fast support removes every conflict at each node's own tick.
Assembly supplies the source decoders, fgsa_rXing, fgsa_rCap_channel
and sourceDiscipline_tSrc. No finality-release arm is used. -/
theorem postReset_resetLease_at_reset {w : HealingWitness} (h0r : H0Reset p c E rho w) :
    ∀ x, x ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho
        (afterTicksIdx rho (SA.releaseTime p.toParams w.sStar)) x).base.obligations,
        Block.Compatible row.1 w.CStar := by
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨_, y0, _, C0, ha, _, hsource, he0, _⟩ := h0r.fresh
  obtain ⟨_, G0, _, hG0, _, pre, hpre, hτ⟩ :=
    healing_source_decode p c E rho emittedNonempty emittedName ha hsource
  rw [← h0r.label] at hG0 hpre hτ
  obtain ⟨ix, hix⟩ := raw_result_tick p c E rho hG0
  have hpreEq : pre = clockPre p (storeAt p c E rho ix y0)
      (SA.gateTime p.toParams w.sStar) :=
    Option.some.inj (hpre.symm.trans (healing_support_gate_reads p c E rho hs hix).1)
  subst pre
  rw [he0] at hτ
  have hhor := (hs.in_horizon _ (List.mem_of_getElem? hix)).2
  have hqv : SA.releaseTime p.toParams w.sStar = SA.voteTime p.toParams (w.sStar + 1) := by
    change 4 * p.Δ * (w.sStar : Int) + 5 * p.Δ =
      4 * p.Δ * ((w.sStar + 1 : Nat) : Int) + p.Δ
    push_cast
    ring
  have hqg : SA.releaseTime p.toParams w.sStar ≤ SA.gateTime p.toParams w.sStar := by
    change 4 * p.Δ * (w.sStar : Int) + 5 * p.Δ ≤ 4 * p.Δ * (w.sStar : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hvd : SA.voteTime p.toParams w.sStar + E.Δ ≤ SA.gateTime p.toParams w.sStar := by
    rw [hrec.base.delta]
    change 4 * p.Δ * (w.sStar : Int) + p.Δ + p.Δ ≤
      4 * p.Δ * (w.sStar : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) h0r.synchronous hvd hhor
  intro x hx
  have htime : ((4 * w.sStar + 5 : Nat) : Time) * p.Δ =
      SA.releaseTime p.toParams w.sStar := by
    change _ = 4 * p.Δ * (w.sStar : Int) + 5 * p.Δ
    push_cast
    ring
  obtain ⟨iy, hiy, _⟩ := fgsa_tick_total E rho hs hrec.base.delta x hx
    (4 * w.sStar + 5) (htime ▸ hqg.trans hhor)
    (htime ▸ hrec.awake x hx _ (h0r.synchronous.trans (by
      change 4 * p.Δ * (w.sStar : Int) + p.Δ ≤ 4 * p.Δ * (w.sStar : Int) + 5 * p.Δ
      linarith [p.deltaPos])) (hqg.trans hhor))
  rw [htime] at hiy
  have hF := healing_low_finality_at_reset_reset E rho hrec.toRecovery₂ xing cap source w h0r x hx
  have hEpoch : V2.D.restartFree rho x
      (V2.D.Run.idxBefore rho (SA.releaseTime p.toParams w.sStar)) iy := by
    apply healing_recovery_epoch E rho hrec hx (fgsa_idxBefore_mono rho ?_)
    have hg := h0r.synchronous
    change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hg
    change E.t_GST + 1 ≤ 4 * p.Δ * (w.sStar : Int) + 5 * p.Δ
    have hp : (1 : Int) ≤ p.Δ := by have hd : (0 : Int) < p.Δ := p.deltaPos; omega
    linarith
  rw [← raw_tick_read_on p c E rho hs hiy hEpoch] at hF
  have hJoined := healing_recovery_joined E rho hrec hx
    (s := w.sStar + 1) (t := SA.voteTime p.toParams (w.sStar + 1))
    (by simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using
      (show E.t_GST ≤ slotStartZ p (w.sStar : Int) from by
        have hcut := raw_reset_vote_cutoff p c E rho h0r
        change E.t_GST ≤ 4 * p.Δ * ((w.sStar : Int) - 1) at hcut
        change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int)
        nlinarith [p.deltaPos]))
    (h0r.synchronous.trans (by
      change 4 * p.Δ * (w.sStar : Int) + p.Δ ≤
        4 * p.Δ * ((w.sStar + 1 : Nat) : Int) + p.Δ
      push_cast; linarith [p.deltaPos])) (hqv ▸ hqg.trans hhor)
  have hRead : joinedAtTime p (storeAt p c E rho iy x).restartTime
      (SA.releaseTime p.toParams w.sStar) = true := by
    rw [hqv]
    have hj := fgsa_head_joined_of_joinedAt E rho hs (hqv ▸ hiy) hJoined
    change joinedNow p (FGSA.clock p (storeAt p c E rho iy x)
      (SA.voteTime p.toParams (w.sStar + 1))) = true at hj
    simpa only [joinedNow, fgsa_clock_restartTime, (clock_vn _ _).2] using hj
  have hrows := healing_support_release_compat (hroots := hrec.base.receiptIdealization)
    E rho hrec.base.valid hrec.base.delta w.sStar hSync ha.1 hx hix (hqv ▸ hiy)
    (hServices.first w.sStar ix iy y0 x h0r.synchronous ha.1 hx hix (hqv ▸ hiy)
      (healing_gate_enabled_of_result E rho hs hix
        ((gateResultAt_eq_gateResult p c E rho hs hix).trans hG0)) hJoined) hτ hF
  have hstore : storeAt p c E rho (afterTicksIdx rho (SA.releaseTime p.toParams w.sStar)) x =
      FGSA.clock p (storeAt p c E rho iy x) (SA.releaseTime p.toParams w.sStar) := by
    change (V2.D.Run.stateBefore E rho _ x).st = _
    rw [← congrFun (afterTicks_eq_stateBefore E rho hs _) x, afterTicks_node E rho hs hiy]
    exact tick_st (c := c) E rho (V2.D.Run.stateBefore E rho iy x) x _
  rw [hstore, hqv]
  exact hrows

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2933–2938; plan J5A C2, R3; B1/B13/B17/B18.
DC: INTENTIONAL; DC has no leases; SA event preservation.
The new stored instance j=i is proved first. It uses only cut-i raw
transfer, past reset leases, reset release and the preceding event's
effect on stateBefore i. No field at cut i+1 is used. -/
theorem postReset_resetLease_succ {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hreset : PostResetResetLeaseCompatible p c E rho w i) :
    PostResetResetLeaseCompatible p c E rho w (i + 1) := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hd := p.deltaPos
  rw [PostResetResetLeaseCompatible_def] at hreset
  let cut := afterTicksIdx rho (SA.releaseTime p.toParams w.sStar)
  have hTime : E.t_GST + 1 ≤ SA.releaseTime p.toParams w.sStar := by
    have hg := h0r.synchronous
    change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hg
    change E.t_GST + 1 ≤ 4 * p.Δ * (w.sStar : Int) + 5 * p.Δ
    have hp : (1 : Int) ≤ p.Δ := by have hd : (0 : Int) < p.Δ := p.deltaPos; omega
    linarith
  have hStart : V2.D.Run.idxBefore rho (E.t_GST + 1) ≤ cut :=
    (fgsa_idxBefore_mono rho hTime).trans (by
      have hh := (preIdx_le_afterTicksIdx E rho hs (SA.releaseTime p.toParams w.sStar)).1
      rw [V2.D.Run.idxBefore_def]
      exact hh)
  have hnew : ∀ x, x ∈ rho.honest → cut ≤ i →
      ∀ row ∈ (storeAt p c E rho i x).base.obligations,
        (storeAt p c E rho i x).base.now < row.2.2 → Block.Compatible row.1 w.CStar := by
    intro x hx hcut row hrow hlive
    by_cases hic : i = cut
    · subst i
      exact postReset_resetLease_at_reset p c E rho hrec hServices emittedNonempty emittedName
        xing cap source h0r x hx row hrow
    have hci : cut < i := Nat.lt_of_le_of_ne hcut (Ne.symm hic)
    cases i with
    | zero => exact False.elim (Nat.not_lt_zero _ hci)
    | succ m =>
      have hmc : cut ≤ m := Nat.le_of_lt_succ hci
      have hold := hreset m (Nat.lt_succ_self m) x hx hmc
      cases he : rho.events[m]? with
      | none =>
        change row ∈ (V2.D.Run.stateBefore E rho (m + 1) x).st.base.obligations at hrow
        change (V2.D.Run.stateBefore E rho (m + 1) x).st.base.now < row.2.2 at hlive
        simp only [V2.D.Run.stateBefore, List.take_add_one, he, Option.toList_none,
          List.append_nil] at hrow hlive
        exact hold row hrow hlive
      | some ev =>
        have other {z : V} (hz : z ≠ x) {ev : V2.Event V (Obj p)}
            (hev : rho.events[m]? = some ev) (hn : ev.node = z) :
            V2.D.Run.stateBefore E rho (m + 1) x = V2.D.Run.stateBefore E rho m x := by
          rw [V2.D.Run.stateBefore_succ E rho hev]
          exact V2.D.World.step_apply_of_node_ne E rho _ (hn ▸ hz)
        cases ev with
        | restart z t =>
          have hz : z ∈ rho.honest := hrec.base.valid.honest_only _ (List.mem_of_getElem? he)
          have hEpoch : V2.D.restartFree rho z cut (m + 1) :=
            healing_recovery_epoch E rho hrec hz hStart
          exact (hEpoch m t hmc (Nat.lt_succ_self m) he).elim
        | deliver z o t =>
          by_cases hz : z = x
          · subst z
            have hm := postReset_delivery_no_obligation p c E rho he hrow
            have hnow : (storeAt p c E rho (m + 1) x).base.now =
                (storeAt p c E rho m x).base.now := by
              change (V2.D.Run.stateBefore E rho (m + 1) x).st.base.now = _
              rw [V2.D.Run.stateBefore_succ E rho he]
              simp only [V2.D.World.step, Function.update_self]
              exact process_base_now (p := p) _ (toWire p o)
            exact hold row hm (hnow ▸ hlive)
          · have hEq := other hz he rfl
            change row ∈ (V2.D.Run.stateBefore E rho (m + 1) x).st.base.obligations at hrow
            change (V2.D.Run.stateBefore E rho (m + 1) x).st.base.now < row.2.2 at hlive
            rw [hEq] at hrow hlive
            exact hold row hrow hlive
        | tick z t =>
          by_cases hz : z = x
          · subst z
            have hidx : V2.D.Run.idxBefore rho (SA.releaseTime p.toParams w.sStar) ≤ cut := by
              have h := (preIdx_le_afterTicksIdx E rho hs
                (SA.releaseTime p.toParams w.sStar)).1
              rw [V2.D.Run.idxBefore_def]
              exact h
            have hqt : SA.releaseTime p.toParams w.sStar ≤ t :=
              not_lt.mp (fun ht => absurd
                ((Gen.V2.Duty.index_lt_idxBefore_iff hs he _).mpr ht)
                (not_lt.mpr (hidx.trans hmc)))
            have hqpos : 0 < SA.releaseTime p.toParams w.sStar := by
              change 0 < 4 * p.Δ * (w.sStar : Int) + 5 * p.Δ
              positivity
            have hnow := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
              (fgsaRestoreTimeLaw p c) E rho hs he x
            rw [fgsa_clock_now p c (rho.stateBefore E m x)] at hnow
            have hresult : ∀ s C, t = SA.gateTime p.toParams s →
                joinedNow p (clockPre p (storeAt p c E rho m x) t) = true →
                SA.Root.confirmationFrom p.toParams
                  (eraseFG (clockPre p (storeAt p c E rho m x) t).fg.F)
                  (actView (clockPre p (storeAt p c E rho m x) t)) s = some C →
                Block.Compatible C w.CStar := by
              intro s C ht hJ hc
              subst t
              have hlabel : w.sStar ≤ s := by
                by_contra hn
                have hlt : (s : Int) + 1 ≤ w.sStar := by
                  exact_mod_cast Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)
                change 4 * p.Δ * (w.sStar : Int) + 5 * p.Δ ≤
                  4 * p.Δ * (s : Int) + 6 * p.Δ at hqt
                nlinarith [p.deltaPos]
              have hGST : E.t_GST ≤ SA.voteTime p.toParams s := by
                have hg := h0r.synchronous
                change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hg
                change E.t_GST ≤ 4 * p.Δ * (s : Int) + p.Δ
                have hh : (w.sStar : Int) ≤ s := by exact_mod_cast hlabel
                nlinarith [p.deltaPos]
              have hres := raw_gate_result_of_raw p c E rho hs he
                (healing_gate_enabled_of_joined E rho he (by
                  rwa [clockPre_joined] at hJ)) hc
              have hcomp := postReset_raw_reset_compatible p c E rho hrec hServices
                emittedNonempty emittedName h0r hinv hx hlabel he hres (Nat.le_succ m)
              change Block.compatible w.CStar C = true at hcomp
              rw [Gen.Pure.block_compatible_comm] at hcomp
              exact hcomp
            have hm : row ∈ (FGSA.clock p (storeAt p c E rho m x) t).base.obligations := by
              change row ∈ (V2.D.Run.stateBefore E rho (m + 1) x).st.base.obligations at hrow
              rw [V2.D.Run.stateBefore_succ E rho he] at hrow
              simp only [V2.D.World.step, Function.update_self] at hrow
              exact (tick_st (c := c) E rho (V2.D.Run.stateBefore E rho m x) x t) ▸ hrow
            exact raw_clock_compatible p w _ t hold hnow hresult row hm
          · have hEq := other hz he rfl
            change row ∈ (V2.D.Run.stateBefore E rho (m + 1) x).st.base.obligations at hrow
            change (V2.D.Run.stateBefore E rho (m + 1) x).st.base.now < row.2.2 at hlive
            rw [hEq] at hrow hlive
            exact hold row hrow hlive
  rw [PostResetResetLeaseCompatible_def]
  intro j hj x hx hcut
  dsimp only
  intro row hrow hlive
  by_cases hji : j = i
  · subst j
    exact hnew x hx hcut row hrow hlive
  · exact hreset j (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) hji) x hx hcut row hrow hlive

end ResetLeaseStep

private theorem raw_postClock_store (hs : V2.D.ScheduleWellFormed E rho)
    {x : V} {t : Time} {nd : Node p} (hnd : postClock E rho x t = some nd) :
    nd.st = storeAt p c E rho (afterTicksIdx rho t) x := by
  rw [postClock_def, preTick_def] at hnd
  cases hi : V2.D.Run.tickIdx? rho x t with
  | none => rw [hi] at hnd; cases hnd
  | some iy =>
    rw [hi] at hnd
    have hiy := V2.D.Run.tickIdx?_spec hi
    have he := Option.some.inj hnd
    have hstore : storeAt p c E rho (afterTicksIdx rho t) x =
        FGSA.clock p (storeAt p c E rho iy x) t := by
      change (V2.D.Run.stateBefore E rho _ x).st = _
      rw [← congrFun (afterTicks_eq_stateBefore E rho hs _) x, afterTicks_node E rho hs hiy]
      exact tick_st (c := c) E rho (V2.D.Run.stateBefore E rho iy x) x t
    exact (congrArg Node.st he).symm.trans hstore.symm

omit [DecidableEq V] in
private theorem raw_cut_time (hs : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {ev : V2.Event V (Obj p)} {t : Time}
    (hk : rho.events[k]? = some ev) (hcut : k < afterTicksIdx rho t) : ev.time ≤ t := by
  have hm : ev ∈ rho.events.filter (cutPred t) := by
    rw [V2.D.Engine.filter_eq_take hs (cutPred t)
      (fun e f h hf => decide_eq_true (h.trans (of_decide_eq_true hf)))]
    apply List.mem_of_getElem? (i := k)
    change (rho.events.take (afterTicksIdx rho t))[k]? = some ev
    rw [List.getElem?_take_of_lt hcut]
    exact hk
  have hp := Prod.Lex.toLex_le_toLex.mp (of_decide_eq_true (List.mem_filter.mp hm).2)
  rcases hp with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

private theorem raw_key_admission {v : GridCO.State p.n .root} {s : Slot} {C B : Block} {g : Nat}
    (hkey : (B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n v
        s C) :
    g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine p.n .root v s B := by
  rw [@GridCO.gateWriteKeys_def GridCO.slowLeasePolicy] at hkey
  obtain ⟨b, _, hm⟩ := List.mem_flatMap.mp hkey
  obtain ⟨g', hg', he⟩ := List.mem_map.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact hg'

section RawRelease
variable [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hServices : RawServiceScope p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)

include hrec hServices emittedNonempty emittedName writes

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2930–2938; plan J5A A1; B1/B13/B17/B18.
DC: INTENTIONAL; DC has no leases. Classify each live release lease.
C0 at i+1 excludes reset conflicts. Prefixes of CStar use reset/raw
compatibility at i. Strict extensions use lease_safe at i+1 in the
raw result's concrete honest supporter HEAD. Assembly supplies the
source decoders and fgsa_leaseOrigins_lastWrite with its exact type. -/
theorem postReset_raw_release_compatible {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatible p c E rho w (i + 1))
    (hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    {k : Nat} {y : V} {j : Slot} {C : Block} (hy : y ∈ rho.honest)
    (hlabel : w.sStar ≤ j) (hk : IsGateTick p c rho k y j)
    (hres : gateResult p c E rho y j = some (some C)) (hki : k ≤ i)
    {x : V} {nd : Node p} (hx : x ∈ rho.honest)
    (hnd : postClock E rho x (SA.releaseTime p.toParams j) = some nd) :
    ∀ row ∈ nd.st.base.obligations, nd.st.base.now < row.2.2 → Block.Compatible row.1 C := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hresAt := (gateResultAt_eq_gateResult p c E rho hs hk).trans hres
  have hresetC := postReset_raw_reset_compatible p c E rho hrec hServices
    emittedNonempty emittedName
    h0r hinv hy hlabel hk hresAt hki
  have hgst : E.t_GST ≤ SA.voteTime p.toParams j := by
    apply h0r.synchronous.trans
    change 4 * p.Δ * (w.sStar : Int) + p.Δ ≤ 4 * p.Δ * (j : Int) + p.Δ
    have h : (w.sStar : Int) ≤ j := by exact_mod_cast hlabel
    nlinarith [p.deltaPos]
  obtain ⟨kh, z, hz, hkh, hCH, _⟩ := healing_gate_result_supporter p c E rho hrec
    hServices hgst (raw_reset_later_cutoff p c E rho h0r hlabel) hy hk hresAt
  have hndst := raw_postClock_store p c E rho hs hnd
  rw [hndst]
  let ir := afterTicksIdx rho (SA.releaseTime p.toParams j)
  have hirk : ir ≤ k := by
    apply (preIdx_le_afterTicksIdx E rho hs (SA.releaseTime p.toParams j)).2.trans
    apply raw_timeIdx_le p c E rho hs hk
    change 4 * p.Δ * (j : Int) + 5 * p.Δ < 4 * p.Δ * (j : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hir : ir < i + 1 := hirk.trans_lt (Nat.lt_succ_of_le hki)
  have hcut : afterTicksIdx rho (SA.releaseTime p.toParams w.sStar) ≤ ir := by
    change (rho.events.filter (cutPred (SA.releaseTime p.toParams w.sStar))).length ≤
      (rho.events.filter (cutPred (SA.releaseTime p.toParams j))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro ev _ he
    have he' : ev.key ≤ toLex (SA.releaseTime p.toParams w.sStar, 1) :=
      of_decide_eq_true he
    change decide (ev.key ≤ toLex (SA.releaseTime p.toParams j, 1)) = true
    apply decide_eq_true
    apply he'.trans
    apply Prod.Lex.toLex_le_toLex.mpr
    by_cases hj : w.sStar = j
    · rw [hj]; exact Or.inr ⟨rfl, le_rfl⟩
    · left
      change 4 * p.Δ * (w.sStar : Int) + 5 * p.Δ < 4 * p.Δ * (j : Int) + 5 * p.Δ
      have h : (w.sStar : Int) < j := by exact_mod_cast Nat.lt_of_le_of_ne hlabel hj
      nlinarith [p.deltaPos]
  rw [PostResetResetLeaseCompatible_def] at hresetNext
  rw [PostResetLeaseSafe_def] at hleaseNext
  intro row hrow hlive
  obtain ⟨kw, hkw, s, Gw, hwrite, hpass, hGw, _, hkey, _, _, _⟩ := writes ir x row hrow
  obtain ⟨hmem, hng, hBG, _, _⟩ := healing_support_key_cases p hkey
  have hrowReset := hresetNext ir hir x hx hcut row hrow hlive
  by_cases hbelow : Block.Preceq row.1 w.CStar
  · exact Gen.Pure.block_compatible_of_preceq_compatible hbelow hresetC
  have habove : Block.Preceq w.CStar row.1 := (Bool.or_eq_true_iff.mp hrowReset).resolve_left hbelow
  have hne : row.1 ≠ w.CStar := fun he => hbelow (he ▸ Gen.Pure.block_preceq_refl w.CStar)
  have htime := raw_cut_time p c E rho hs hwrite hkw
  have hsj : s < j := by
    by_contra hn
    have h : (j : Int) ≤ s := by exact_mod_cast Nat.le_of_not_gt hn
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ 4 * p.Δ * (j : Int) + 5 * p.Δ at htime
    nlinarith [p.deltaPos]
  have hread : timeIdx rho (SA.voteTime p.toParams j) ≤ i + 1 := by
    apply (raw_timeIdx_le p c E rho hs hk ?_).trans (Nat.le_succ_of_le hki)
    change 4 * p.Δ * (j : Int) + p.Δ < 4 * p.Δ * (j : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hBHead := (hleaseNext kw (hkw.trans hir) x s row.1 row.2.1 Gw hx hwrite hpass hGw
    habove hne hmem hng hBG (raw_key_admission p hkey)).2.1
    z j (headAtIdx p c E rho kh j) hz (Nat.succ_le_of_lt hsj) hread (raw_head_read p c E rho hs hkh)
  exact Gen.Pure.block_compatible_of_common hBHead hCH


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2933–2944, H.2:736–746; plan J5-A-3 R5;
B1/B13/B17/B18. DC: SAME lease guard for an actual raw result.
The reader is after the reset release. Strict extensions of CStar and
C share an honest HEAD in the complete preceding batch. -/
theorem postReset_raw_moving_lease_compat {w : HealingWitness}
    (h0r : H0Reset p c E rho w) {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatible p c E rho w (i + 1))
    {ix : Nat} {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some C))
    {l : Slot} (hsl : s + 1 ≤ l)
    (hbatch : ∀ z ∈ rho.honest, ∀ H, headAtLabel p c E rho z l = some H →
      Block.Preceq C H)
    {iy : Nat} {y : V} {t : Time} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y t)) (hyi : iy ≤ i)
    (hafter : SA.freezeTime p.toParams l < t)
    (hupper : t ≤ SA.voteTime p.toParams (l + 1)) :
    ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y) t).base.obligations,
      Block.Compatible row.1 C := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hrelease : SA.releaseTime p.toParams w.sStar < t := by
    have h : (w.sStar : Int) + 1 ≤ l := by exact_mod_cast ((Nat.succ_le_succ hlabel).trans hsl)
    change 4 * p.Δ * (w.sStar : Int) + 5 * p.Δ < t
    change 4 * p.Δ * (l : Int) + 3 * p.Δ < t at hafter
    nlinarith [p.deltaPos]
  have hreleaseCut : afterTicksIdx rho (SA.releaseTime p.toParams w.sStar) ≤ iy :=
    (preIdx_le_afterTicksIdx E rho hs _).2.trans (raw_timeIdx_le p c E rho hs hiy hrelease)
  have hread : timeIdx rho (SA.voteTime p.toParams l) ≤ i := by
    apply (raw_timeIdx_le p c E rho hs hiy ?_).trans hyi
    change 4 * p.Δ * (l : Int) + p.Δ < t
    change 4 * p.Δ * (l : Int) + 3 * p.Δ < t at hafter
    linarith [p.deltaPos]
  have hnongate : ∀ q : Slot, t ≠ SA.gateTime p.toParams q := by
    intro q he
    rw [he] at hafter hupper
    change 4 * p.Δ * (l : Int) + 3 * p.Δ <
      4 * p.Δ * (q : Int) + 6 * p.Δ at hafter
    change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤
      4 * p.Δ * ((l + 1 : Nat) : Int) + p.Δ at hupper
    push_cast at hupper
    have hq : (q : Int) ≤ l := by nlinarith [p.deltaPos]
    have hl : (l : Int) ≤ q := by
      by_contra hn
      have h : (q : Int) + 1 ≤ l := by omega
      nlinarith [p.deltaPos]
    nlinarith [p.deltaPos]
  have hnow : (storeAt p c E rho iy y).base.now ≤ t := by
    have h := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho hs hiy y
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho iy y)] at h
    exact h
  have hresetC := postReset_raw_reset_compatible p c E rho hrec hServices
    emittedNonempty emittedName
    h0r hinv hx hlabel hix hres hxi
  have hvote : SA.voteTime p.toParams l ≤ t := by
    change 4 * p.Δ * (l : Int) + p.Δ ≤ t
    change 4 * p.Δ * (l : Int) + 3 * p.Δ < t at hafter
    linarith [p.deltaPos]
  obtain ⟨ih, hih⟩ := healing_support_vote_tick E rho hs hrec.base.delta hy l
    (hvote.trans (hs.in_horizon _ (List.mem_of_getElem? hiy)).2)
    (hrec.awake y hy _ (by
      have hg := h0r.synchronous
      change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hg
      change E.t_GST ≤ 4 * p.Δ * (l : Int) + p.Δ
      have hh : (w.sStar : Int) ≤ l := by
        exact_mod_cast hlabel.trans ((Nat.le_succ s).trans hsl)
      nlinarith [p.deltaPos])
      (hvote.trans (hs.in_horizon _ (List.mem_of_getElem? hiy)).2))
  have hhead := raw_head_read p c E rho hs hih
  have hCH := hbatch y hy _ hhead
  rw [PostResetResetLeaseCompatible_def] at hresetNext
  have hsafe := hinv.lease_safe
  rw [PostResetLeaseSafe_def] at hsafe
  intro row hr
  have hpre : row ∈ (clockPre p (storeAt p c E rho iy y) t).base.obligations := by
    change row ∈ (if isGateTime p t then
      gateStep p (clockPre p (storeAt p c E rho iy y) t) ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
      else clockPre p (storeAt p c E rho iy y) t).base.obligations at hr
    rw [show isGateTime p t = false from Bool.eq_false_iff.mpr (fun hg => by
      obtain ⟨q, hq⟩ := (isGateTime_iff p t).mp hg
      exact hnongate q hq.symm)] at hr
    exact hr
  have hrow := (clockPre_obligations_sublist p _ t).subset hpre
  have hlive := hnow.trans_lt (healing_clockPre_live _ t row hpre)
  have hreset := hresetNext iy (Nat.lt_succ_of_le hyi) y hy hreleaseCut row hrow hlive
  by_cases hbelow : Block.Preceq row.1 w.CStar
  · exact Gen.Pure.block_compatible_of_preceq_compatible hbelow hresetC
  have habove := (Bool.or_eq_true_iff.mp hreset).resolve_left hbelow
  have hne : row.1 ≠ w.CStar := fun he => hbelow (he ▸ Gen.Pure.block_preceq_refl w.CStar)
  obtain ⟨kw, hkw, q, D, hwrite, hpass, hD, -, hkey, -, -, -⟩ := writes iy y row hrow
  obtain ⟨hmem, hng, hBD, -, -⟩ := healing_support_key_cases p hkey
  have htime := fgsa_tick_time_strict E rho hs hwrite hiy hkw
  have hql : q + 1 ≤ l := by
    have ht := htime.trans_le hupper
    change 4 * p.Δ * (q : Int) + 6 * p.Δ <
      4 * p.Δ * ((l + 1 : Nat) : Int) + p.Δ at ht
    push_cast at ht
    have h : (q : Int) < l := by nlinarith [p.deltaPos]
    exact_mod_cast h
  have hTH := (hsafe kw (hkw.trans_le hyi) y q row.1 row.2.1 D hy hwrite hpass hD
    habove hne hmem hng hBD (raw_key_admission p hkey)).2.1 y l _ hy hql hread hhead
  exact Gen.Pure.block_compatible_of_common hTH hCH

end RawRelease

omit [DecidableEq V] in
private theorem raw_idx_mono : Monotone (V2.D.Run.idxBefore rho) := by
  intro a b hab
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true
    (lt_of_lt_of_le (of_decide_eq_true he) hab))

omit [DecidableEq V] in
private theorem raw_block_decode {o : Obj p} {b : Block} (h : blockOf? p o = some b) :
    ∃ u N, o = ofWire p ⟨.proposer u, .proposal N⟩ ∧ N.erase = b := by
  unfold blockOf? at h
  cases hd : (toWire p o).decode with
  | none => simp only [hd, reduceCtorEq] at h
  | some m =>
    cases m <;> simp only [hd, reduceCtorEq, Option.some.injEq] at h
    rename_i u N
    refine ⟨u, N, ?_, h⟩
    apply toWire_injective (p := p)
    rw [toWire_ofWire]
    exact decode_eq_block.mp hd


private theorem raw_receipt_proposal (hs : V2.D.ScheduleWellFormed E rho)
    {s : Slot} {y : V} (hy : y ∈ rho.honest) (K : Block)
    (hService : TargetReceiptService E rho K (SA.freezeTime p.toParams s) y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∃ Y : FGBlock (Fin p.n), eraseFG Y = K ∧
      Y ∈ (rho.stateBeforeTime E (SA.freezeTime p.toParams s) y).st.fg.TF := by
  have hb := fgsa_target_receipt_on E rho hs hroots K (SA.freezeTime p.toParams s) y hy hService
  obtain ⟨Y, hY, he⟩ := ((storeBundle_stateBeforeTime E rho _ y).cstore.baseTree K).mp hb
  exact ⟨Y, he, hY⟩

private theorem raw_proposal_seat [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hServices : RawServiceScope p c E rho)
    (mono : RMonoAll p c E rho)
    {r : Slot} {B : Block} (hgst : E.t_GST ≤ SA.voteTime p.toParams r)
    (hJoinCut : E.t_GST ≤ slotStartZ p ((r : Int) - 1))
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K → Block.Preceq B K)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (r + 1))))
    (hFB : Block.Preceq (eraseFG (storeAt p c E rho ip x).fg.F) B)
    (k : Fin p.n) (hk : rho.seatOf (.base (.head r)) k ∈ rho.honest)
    (hJoin : joinedAt p E rho (rho.seatOf (.base (.head r)) k) r
      (SA.voteTime p.toParams r)) :
    Gen.AC.Root.poolSupports (FGSA.clock p (storeAt p c E rho ip x)
        (SA.proposalTime p.toParams (r + 1))).base.blocks
      (FGSA.proposerSupport (FGSA.clock p (storeAt p c E rho ip x)
        (SA.proposalTime p.toParams (r + 1))) (r + 1)) k B = true ∧
    GridCO.equivocates (FGSA.proposerVotes (FGSA.clock p (storeAt p c E rho ip x)
      (SA.proposalTime p.toParams (r + 1))) (r + 1)) k = false := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  let st := FGSA.clock p (storeAt p c E rho ip x) (SA.proposalTime p.toParams (r + 1))
  let z := rho.seatOf (.base (.head r)) k
  have hvp : SA.voteTime p.toParams r + p.Δ ≤ SA.proposalTime p.toParams (r + 1) := by
    change 4 * p.Δ * (r : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
    push_cast
    linarith
  have hgstr := hgst
  have hhorp := (hS.in_horizon _ (List.mem_of_getElem? hip)).2
  have hhorr : SA.voteTime p.toParams r ≤ rho.horizon :=
    ((le_add_of_nonneg_right hd.le).trans hvp).trans hhorp
  have hawake := hrec.awake z hk _ hgstr hhorr
  obtain ⟨jz, hjz⟩ := healing_support_vote_tick E rho hS hDelta hk r hhorr hawake
  have hScope := hServices.proposal r ip x (healing_window_of_cut E hJoinCut) hx hip
    (healing_recovery_joined_proposal_next E rho hrec
      (healing_window_of_cut E hJoinCut) hx hip)
  obtain ⟨hem, hhl⟩ := healing_support_honest_emits (c := c) E rho hS hjz hawake
    (fgsa_head_joined_of_joinedAt E rho hS hjz hJoin)
  let K := headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho jz z).st
    (SA.voteTime p.toParams r)) r
  have hBK : Block.Preceq B K := hcover z hk K hhl
  have hzinv := cstoreInv_clock p _ (cstoreInv_stateBefore E rho jz z)
    (SA.voteTime p.toParams r)
  have hKz : K ∈ (storeAt p c E rho jz z).base.blocks := by
    have hm := headVote_stored p _ hzinv r
    rwa [clock_base_blocks] at hm
  have hve : SA.voteTime p.toParams r + p.Δ = SA.earlyTime p.toParams r := by
    change 4 * p.Δ * (r : Int) + p.Δ + p.Δ = 4 * p.Δ * (r : Int) + 2 * p.Δ
    ring
  obtain ⟨Kfg, hKfg, hKe⟩ := ((cstoreInv_stateBefore E rho jz z).baseTree K).mp hKz
  have hFloor : Block.Preceq
      (eraseFG (rho.stateBeforeTime E (SA.voteTime p.toParams r + p.Δ) x).st.fg.F) K := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    exact Gen.Pure.block_preceq_trans
      (eraseFG_preceq (mono _ _ x hx
        (healing_support_idxBefore_le p c E rho hS hip hvp)).1)
      (Gen.Pure.block_preceq_trans hFB hBK)
  have hService := (healing_carriers_window_at p c E rho hrec
    (healing_window_of_cut E hJoinCut) hScope.carriers hx hip hvp
    jz z hk hjz).direct Kfg hKfg hKe
    (hKe ▸ hFloor)
  have hBase := fgsa_target_receipt_on E rho hS hrec.base.receiptIdealization K
    (SA.voteTime p.toParams r + p.Δ) x hx (hKe ▸ hService)
  rw [hve] at hBase
  obtain ⟨Y, hY, hYe⟩ := ((storeBundle_stateBeforeTime E rho _ x).cstore.baseTree K).mp hBase
  have hEY : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams r) ≤ ip := by
    apply healing_support_idxBefore_le p c E rho hS hip
    change 4 * p.Δ * (r : Int) + 2 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
    push_cast
    linarith
  have hKx : Y ∈ (storeAt p c E rho ip x).fg.TF := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hY
    exact (fgsa_store_durable p c E rho hEY x).1 hY
  have hKe' := hYe
  have hinv : CStoreInv p st := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have hKb : K ∈ st.base.blocks := by
    rw [← hKe']
    refine (hinv.baseTree _).mpr ⟨Y, ?_, rfl⟩
    change Y ∈ (FGSA.clock p _ _).fg.TF
    rw [clock_fg]
    exact hKx
  have hKslot : K.slot ≤ r := by
    have hb := (fgsa_stateBefore_bounds E rho hS jz z).1 K hKz
    have hn := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho hS hjz z
    rw [fgsa_clock_now p c (rho.stateBefore E jz z)] at hn
    have hsl := Internal.slotOf_mono (p := p) hn
    have he : p.slotOf (SA.voteTime p.toParams r) = r :=
      (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho jz z) _).2.symm.trans
        (fgsa_vote_slot (c := c) _ r)
    exact hb.trans (hsl.trans_eq he)
  -- Fresh HEAD service reaches earlyTime; its receiver epoch keeps the vote.
  obtain ⟨hFresh⟩ := hScope.fresh k K.root hk hem
  obtain ⟨jem, hjEm, hoEm⟩ := hem
  have hem : V2.D.Run.emits E rho z (ofHead p ⟨.seat (.head r) k, K.root⟩)
      (SA.voteTime p.toParams r) := ⟨jem, hjEm, hoEm⟩
  obtain ⟨hom, _⟩ := hFresh.receipt hE hx hjEm hoEm
  let o := baseVote (⟨.seat (.head r) k, K.root⟩ : HeadWire p.n)
  have hidx : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams r) ≤ ip := by
    apply healing_support_idxBefore_le p c E rho hS hip
    change 4 * p.Δ * (r : Int) + 2 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
    push_cast
    linarith
  have hom' : o ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho
      (SA.earlyTime p.toParams r)) x).base.votes := by
    change o ∈ (rho.stateBefore E _ x).st.base.votes
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    exact hom
  obtain ⟨hod, _⟩ := healing_support_vote_kept_on E rho hidx x
    (SA.proposalTime p.toParams (r + 1)) hScope.epoch o hom'
  have hFK : Block.Compatible K (eraseFG st.fg.F) := by
    change Block.Compatible K (eraseFG (FGSA.clock p _ _).fg.F)
    rw [clock_fg]
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K)
      (Gen.Pure.block_preceq_trans hFB hBK)
  have hol : GridCO.headLabel? o = some r := rfl
  have hok : GridCO.headSeat? o = some k := rfl
  have hoK : GridCO.headTarget? o = some K.root := rfl
  have hresolve := actView_resolve_target p st hinv
    (base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho ip x)))
    o ((actView_blocks st K).mpr ⟨hKb, hFK⟩) hoK
  have hvotes : o ∈ FGSA.proposerVotes st (r + 1) := by
    change o ∈ GridCO.votesAt st.base (r + 1 - 1)
    exact List.mem_filter.mpr ⟨hod, by
      simpa only [Nat.add_sub_cancel, hol] using beq_self_eq_true (some r)⟩
  have hsupp : o ∈ FGSA.proposerSupport st (r + 1) := by
    apply List.mem_filter.mpr
    refine ⟨hvotes, ?_⟩
    change (match GridCO.resolvedHead? (actView st) o with
      | some H => Block.preceq (eraseFG st.fg.F) H &&
        decide (H.slot ≤ r + 1 - 1) | none => false) = true
    rw [hresolve]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨?_, decide_eq_true (by simpa only [Nat.add_sub_cancel] using hKslot)⟩
    change Block.Preceq (eraseFG (FGSA.clock p _ _).fg.F) K
    rw [clock_fg]
    exact Gen.Pure.block_preceq_trans hFB hBK
  have hvs : Gen.AC.Root.voteSupports st.base.blocks B o = true := by
    exact (Gen.AC.Root.vote_support_body _ _ _).mpr
      ⟨K, resolvedTarget_of_mem _ (baseBlocks_rootInj p st hinv) o hKb hoK,
        hKb, by simpa only [hol, Option.getD_some] using hKslot, hBK⟩
  refine ⟨(Gen.AC.Root.vote_pool_support_witness _ _ k B).mpr ⟨o, hsupp, hok, hvs⟩, ?_⟩
  -- Every stored label-r vote of the honest seat is its emitted HEAD.
  have hall : ∀ w ∈ GridCO.votesAt (storeAt p c E rho ip x).base r,
      GridCO.headSeat? w = some k → w = o := by
    intro w hw hwk
    obtain ⟨hwm, hwl⟩ := List.mem_filter.mp hw
    exact fgsa_honest_head_eq_of_stored E rho hE ip x r k K.root _ hk hem w hwm
      (by simpa only [beq_iff_eq] using hwl) hwk
  have hvat : FGSA.proposerVotes st (r + 1) = GridCO.votesAt (storeAt p c E rho ip x).base r := by
    change GridCO.votesAt st.base (r + 1 - 1) = _
    rw [Nat.add_sub_cancel]
    unfold GridCO.votesAt
    rw [(clock_vn (storeAt p c E rho ip x) (SA.proposalTime p.toParams (r + 1))).1]
  rw [hvat]
  cases he : GridCO.equivocates (GridCO.votesAt (storeAt p c E rho ip x).base r) k with
  | false => rfl
  | true =>
    obtain ⟨a, ha, b, hb, hne, hka, hkb⟩ := (cap_pair _ k).mp he
    exact absurd ((hall a ha hka).trans (hall b hb hkb).symm) hne

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.2:736–745, H.16:2940–2944; plan J5A A3;
B1/B13/B17/B18. DC: INTENTIONAL moving full-tree proposal domain.
A general block in this read's domain uses the preceding honest HEAD
batch, direct lease compatibility, and per-block receipt. No fixed
phase or successor service is assumed. -/
theorem healing_proposal_moving_domain [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hServices : RawServiceScope p c E rho)
    (mono : RMonoAll p c E rho)
    {r : Slot} {B : FGBlock (Fin p.n)} (hgst : E.t_GST ≤ SA.voteTime p.toParams r)
    (hJoinCut : E.t_GST ≤ slotStartZ p ((r : Int) - 1))
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K →
      Block.Preceq (eraseFG B) K)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (r + 1))))
    {X : Finset (FGBlock (Fin p.n))} (hX : X ⊆ (storeAt p c E rho ip x).fg.TF)
    (hXc : ∀ W ∈ X, ∀ A, FGBlock.Preceq A W → A ∈ X)
    (hD : B ∈ D_at p c E rho ip x X)
    (hlease : ∀ row ∈ (FGSA.clock p (storeAt p c E rho ip x)
      (SA.proposalTime p.toParams (r + 1))).base.obligations,
      Block.Compatible row.1 (eraseFG B)) :
    Block.Preceq (eraseFG B) (proposerHead p (FGSA.clock p (storeAt p c E rho ip x)
      (SA.proposalTime p.toParams (r + 1))) (r + 1)) := by
  classical
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  let st := FGSA.clock p (storeAt p c E rho ip x) (SA.proposalTime p.toParams (r + 1))
  have hhor := (hS.in_horizon _ (List.mem_of_getElem? hip)).2
  have hvp : SA.voteTime p.toParams r + p.Δ ≤ SA.proposalTime p.toParams (r + 1) := by
    change 4 * p.Δ * (r : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
    push_cast
    linarith
  have hgstr := hgst
  have hhorr : SA.voteTime p.toParams r ≤ rho.horizon :=
    ((le_add_of_nonneg_right hd.le).trans hvp).trans hhor
  have hinv : CStoreInv p st := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have hdfg : st.fg = (storeAt p c E rho ip x).fg := clock_fg p _ _
  have hRd : FGSA.controls p st = R_at p c E rho ip x := by
    change KitFG.treeStoreControlsView (heightView p) st.fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho ip x).fg
    rw [hdfg]
  obtain ⟨_, hFB, hZB, W, hWX, hBW, hloW⟩ :=
    (KitFG.mem_filteredFromView (heightView p) (R_at p c E rho ip x) X B).mp hD
  have hWst : W ∈ st.fg.TF := hdfg ▸ hX hWX
  have hFB0 : Block.Preceq (eraseFG (storeAt p c E rho ip x).fg.F) (eraseFG B) :=
    eraseFG_preceq hFB
  have hkeep : ∀ C, Block.Prec (liveRoot p st) C → Block.Preceq C (eraseFG B) →
      C ∈ erasedList st (domainR p st st.fg.TF) := by
    intro C hr hCB
    have hr' : liveRoot p st ≠ C ∧ Block.Preceq (liveRoot p st) C := by
      change ((!decide (liveRoot p st = C)) && Block.preceq (liveRoot p st) C) = true at hr
      simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Block.Preceq] using hr
    obtain ⟨A, hA, heA, hAW⟩ := eraseFG_ancestor_preceq hinv.fg.closed hWst
      (Gen.Pure.block_preceq_trans hCB (eraseFG_preceq hBW))
    have hFA : FGBlock.Preceq st.fg.F A := raw_lift p
      (Gen.Pure.block_preceq_trans (F_preceq_liveRoot p st hinv) (heA ▸ hr'.2))
    have hZA : FGBlock.Preceq (FGSA.controls p st).Z A := raw_lift p
      (Gen.Pure.block_preceq_trans (fgsa_Z_preceq_liveRoot p st) (heA ▸ hr'.2))
    apply List.mem_filter.mpr
    refine ⟨(hinv.baseTree C).mpr ⟨A, hA, heA⟩, decide_eq_true ⟨A, ?_, heA⟩⟩
    rw [domainR_def, frameR_def]
    exact (KitFG.mem_filteredFromView (heightView p) (FGSA.controls p st) _ A).mpr
      ⟨hdfg ▸ hX (hXc W hWX A hAW), hFA, hZA, W, hWst, hAW, hRd ▸ hloW⟩
  have hanchor : Block.Compatible (liveRoot p st) (eraseFG B) := by
    have hselect := Gen.Pure.foldl_select_mem (fun (best b : Block) =>
      best.depth < b.depth || (best.depth == b.depth && best.root < b.root))
      (st.base.obligations.filterMap (fun row =>
        if st.base.now < row.2.2 && decide (∃ X ∈ FGSA.fullTree p st, eraseFG X = row.1)
        then some row.1 else none)) (eraseFG (FGSA.controls p st).Z)
    change FGSA.liveRoot p st = _ ∨ FGSA.liveRoot p st ∈ _ at hselect
    rcases hselect with he | hm
    · rw [he, hRd]
      exact Gen.Pure.block_compatible_of_common (eraseFG_preceq hZB) (Gen.Pure.block_preceq_refl _)
    · obtain ⟨row, hr, hrow⟩ := List.mem_filterMap.mp hm
      split at hrow
      · rw [← Option.some.inj hrow]
        exact hlease row hr
      · contradiction
  have hhead_eq : proposerHead p st (r + 1) = headInTree p st
      (erasedList st (domainR p st st.fg.TF)) (FGSA.proposerVotes st (r + 1))
      (FGSA.proposerSupport st (r + 1)) := by
    rw [fgsa_domainR_eq_treeStoreFrameView]
    rfl
  rw [hhead_eq]
  let Hon : Finset (Fin p.n) := healingJoinedSeats E rho r
  have hseat (k : Fin p.n) (hk : k ∈ Hon) := raw_proposal_seat p c E rho hrec hServices mono
    hgst hJoinCut hcover hx hip hFB0 k ((healingJoinedSeats_mem E rho r k).mp hk).1
    ((healingJoinedSeats_mem E rho r k).mp hk).2
  have hScope := hServices.proposal r ip x (healing_window_of_cut E hJoinCut) hx hip
    (healing_recovery_joined_proposal_next E rho hrec
      (healing_window_of_cut E hJoinCut) hx hip)
  have hb : Gen.Pure.Batch Hon.card (Gen.V2.Duty.faulty rho).card := hScope.batch
  have hother : ((GridCO.seats p.n (FGSA.proposerVotes st (r + 1))).toFinset \ Hon).card ≤
      (Gen.V2.Duty.faulty rho).card := hScope.rivals
  exact batch_head_covers p st st.fg.TF (FGSA.proposerVotes st (r + 1))
    (FGSA.proposerSupport st (r + 1)) Hon Hon.card (Gen.V2.Duty.faulty rho).card (eraseFG B)
    (fun _ ho => (List.mem_filter.mp ho).1) rfl (fun k hk => (hseat k hk).2)
    (fun k hk => (hseat k hk).1)
    hother hb hanchor hkeep

private theorem raw_proposal_read (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {s : Slot} {Q : Block}
    (hp : HonestProposal E rho (fgsaInterface p c) s Q) :
    ∃ j, rho.events[j]? = some (.tick (V2.D.proposerOf rho (fgsaInterface p c) s)
        (SA.proposalTime p.toParams s)) ∧
      Q.parent = proposerHead p (FGSA.clock p
        (storeAt p c E rho j (V2.D.proposerOf rho (fgsaInterface p c) s))
        (SA.proposalTime p.toParams s)) s := by
  obtain ⟨_, o, ⟨j, hj, hem⟩, hb⟩ := hp
  rw [proposalTime_fgsa p c s] at hj
  refine ⟨j, hj, ?_⟩
  obtain ⟨auth, m⟩ := o
  cases m with
  | head _ => cases hb
  | row _ => cases hb
  | proposal N =>
    have he : N.erase = Q := Option.some.inj hb
    subst Q
    rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem
    change (⟨auth, .proposal N⟩ : Obj p) ∈
      (if E.awake _ (SA.proposalTime p.toParams s) then
        (duties p (SA.proposalTime p.toParams s)).flatMap (fun d =>
          (rho.ownSeats (RunDuty.signLabel d) _).filterMap (fun i =>
            (act p c ((fgsa p c).clock _ _) d (rho.input _ _)).map
              (fun m => (⟨.seat (RunDuty.signLabel d) i, m⟩ : Obj p)))) ++
                ([] : List (Obj p)) else []) at hem
    split at hem
    · rw [List.append_nil] at hem
      obtain ⟨d, hd, hem⟩ := List.mem_flatMap.mp hem
      obtain ⟨i, _, hm⟩ := List.mem_filterMap.mp hem
      obtain ⟨m, hm, ho⟩ := Option.map_eq_some_iff.mp hm
      have he : m = .proposal N := congrArg V2.Signed.payload ho
      subst m
      cases d with
      | headAction _ =>
        change (if joinedNow p _ then some (Msg.head _) else none) = some (Msg.proposal N) at hm
        split at hm <;> cases hm
      | fgAction _ =>
        change (attest p _ _ _).1.map Msg.row = some (.proposal N) at hm
        obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp hm
        cases he
      | propAction s' =>
        have ht := (duties_spec p _ _).mp hd
        have hss : s' = s := by
          change 4 * p.Δ * (s' : Int) = 4 * p.Δ * (s : Int) at ht
          have hΔ := p.deltaPos
          have he : (s' : Int) = s := by nlinarith
          exact_mod_cast he
        subst s'
        change (if joinedNow p _ then
          (propose p _ s).map (withApp p _) else none) = some (.proposal N) at hm
        split at hm
        · exact (fgsa_walkRun_proposal_parent p _ s _ N hm).2.2
        · cases hm
    · exact (List.not_mem_nil hem).elim


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.2:736–745, H.16:2940–2944; plan J5A A3;
B1/B13/B17/B18. DC: INTENTIONAL moving-frame parent consumer.
A concrete honest proposal uses its own domain and live lease read,
and the preceding HEAD batch. The block can be any transferred prefix. -/
theorem healing_proposal_moving_parent [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hServices : RawServiceScope p c E rho)
    (mono : RMonoAll p c E rho)
    {r : Slot} {B : FGBlock (Fin p.n)} {Q : Block}
    (hgst : E.t_GST ≤ SA.voteTime p.toParams r)
    (hJoinCut : E.t_GST ≤ slotStartZ p ((r : Int) - 1))
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K →
      Block.Preceq (eraseFG B) K)
    (hp : HonestProposal E rho (fgsaInterface p c) (r + 1) Q)
    (hdomain : ∀ ip, rho.events[ip]? = some
      (.tick (V2.D.proposerOf rho (fgsaInterface p c) (r + 1))
        (SA.proposalTime p.toParams (r + 1))) →
      ∃ X : Finset (FGBlock (Fin p.n)),
        X ⊆ (storeAt p c E rho ip (V2.D.proposerOf rho (fgsaInterface p c) (r + 1))).fg.TF ∧
        (∀ W ∈ X, ∀ A, FGBlock.Preceq A W → A ∈ X) ∧
        B ∈ D_at p c E rho ip (V2.D.proposerOf rho (fgsaInterface p c) (r + 1)) X)
    (hlease : ∀ ip, rho.events[ip]? = some
      (.tick (V2.D.proposerOf rho (fgsaInterface p c) (r + 1))
        (SA.proposalTime p.toParams (r + 1))) →
      ∀ row ∈ (FGSA.clock p
        (storeAt p c E rho ip (V2.D.proposerOf rho (fgsaInterface p c) (r + 1)))
        (SA.proposalTime p.toParams (r + 1))).base.obligations,
        Block.Compatible row.1 (eraseFG B)) : Block.Preceq (eraseFG B) Q.parent := by
  obtain ⟨ip, hip, hparent⟩ := raw_proposal_read (p := p) (c := c) E rho hp
  rw [hparent]
  obtain ⟨X, hX, hXc, hD⟩ := hdomain ip hip
  exact healing_proposal_moving_domain p c E rho hrec hServices mono hgst hJoinCut hcover
    hp.1.2 hip hX hXc hD
    (hlease ip hip)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2933–2938; plan J5A C0; lead step-range hint,
2026-10-03 20:05. DC: INTENTIONAL; DC has no leases; empty SA prefix.
The joint induction can start at zero without an after-reset premise. -/
theorem postReset_resetLease_zero {w : HealingWitness} (_h0r : H0Reset p c E rho w) :
    PostResetResetLeaseCompatible p c E rho w 0 := by
  rw [PostResetResetLeaseCompatible_def]
  intro j hj
  exact False.elim (Nat.not_lt_zero j hj)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2926–2938; plan J5A A5 before-reset case;
lead step-range hint, 2026-10-03 20:05; B1/B17.
DC: SAME a post-reset source gate is strictly after reset release.
No concrete source gate can precede a cut at or before that release. -/
theorem postReset_rawTransfer_before_reset
    (hs : V2.D.ScheduleWellFormed E rho) {w : HealingWitness} (_h0r : H0Reset p c E rho w)
    {i : Nat} (hbefore : i ≤ afterTicksIdx rho (SA.releaseTime p.toParams w.sStar)) :
    PostResetRawTransfer p c E rho w i := by
  rw [PostResetRawTransfer_def]
  intro k hk y j C _hy hlabel hgate _hres
  have ht : SA.releaseTime p.toParams w.sStar < SA.gateTime p.toParams j := by
    change 4 * p.Δ * (w.sStar : Int) + 5 * p.Δ < 4 * p.Δ * (j : Int) + 6 * p.Δ
    have hl : (w.sStar : Int) ≤ j := by exact_mod_cast hlabel
    nlinarith [p.deltaPos]
  have hcut : afterTicksIdx rho (SA.releaseTime p.toParams w.sStar) ≤ k :=
    (preIdx_le_afterTicksIdx E rho hs _).2.trans (raw_timeIdx_le p c E rho hs hgate ht)
  exact False.elim (Nat.not_lt_of_ge (hbefore.trans hcut) hk)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2933–2938; lead joint step type, 2026-10-03 20:33.
DC: INTENTIONAL; DC has no leases; SA reset-lease step.
The third conjunct is exactly the prior opening-domain body owned by
J6-3. It is written inline because its real definition is not on this
base. This adapter closes PostResetResetLeaseStep at every Nat cut. -/
theorem postReset_resetLease_step [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hServices : RawServiceScope p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (xing : RXing p c E rho) (cap : RCap p c E rho) (source : TSrc p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w) {i : Nat}
    (hprev : PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
      (∀ k, k < i → ∀ x v Q, x ∈ rho.honest → IsGateTick p c rho k x v →
        HonestProposal E rho (fgsaInterface p c) v Q → w.sStar + 2 ≤ v →
        ∀ r, v = r * p.R →
          let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho k x) (p.actionTime r)).st
          ∃ D, eraseFG D = Q ∧ D ∈ domainR p st (treeT p st))) :
    PostResetResetLeaseCompatible p c E rho w (i + 1) :=
  postReset_resetLease_succ p c E rho hrec hServices emittedNonempty emittedName xing cap source h0r
    hprev.1 hprev.2.1

end AvailableChain.FGSA.Run
end
