module
public import AvailableChainFGSAProofs.Proofs.Finality.RecoveryScope
public import AvailableChainFGSAProofs.Proofs.Finality.CoreServices
public import AvailableChainFGSAProofs.Proofs.Shared.AnchorService
public import AvailableChainFGSAProofs.Proofs.Finality.RestoreReads
public import AvailableChainFGSAProofs.Proofs.Finality.TailMixed

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- A Recovery proposal service uses the receiver's public anchor.
Proposal history is durable; the source acceptance can precede GST. -/
theorem finality_proposal_receiver_service {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) {x v : V} {k : Nat} {s : Slot}
    {N : NamedProposal p.n} {send a : Time}
    (hx : x ∈ rho.honest) (hv : v ∈ rho.honest)
    (hacc : V2.D.Run.acceptsAt E rho k v (ofWire p ⟨.proposer s, .proposal N⟩) send)
    (hsa : send ≤ a) (ha : 0 ≤ a) (hpub : V2.PublicTime E a)
    (hGST : E.t_GST < a) (hhor : a + p.Δ ≤ rho.horizon)
    (hF : Block.Preceq (eraseFG (rho.stateBeforeTime E (a + p.Δ) x).st.fg.F) N.erase) :
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
      send (a + p.Δ) x) := by
  let o := ofWire p (⟨.proposer s, .proposal N⟩ : Wire p.n)
  have hd : (toWire p o).decode = some (.block s N) := rfl
  have hD := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho h.sync
    (fun o => ¬ isRowObject o) p.Δ (fun o ho => h.base.delta ▸ fgsaDelay_nonrow E.Δ ΔF o ho)
  have hRF : V2.D.restartFree rho x (V2.D.Run.actionCut rho a)
      (V2.D.Run.idxBefore rho (a + p.Δ)) := by
    apply Gen.V2.Duty.restartFree_actionCut_idxBefore h.base.valid.toScheduleWellFormed
      (lt_add_of_pos_right _ p.deltaPos)
    intro j t hj hat _
    exact (not_lt_of_ge (finality_recovery_restart_bound p c E rho h hx
      (List.mem_of_getElem? hj))) (hGST.trans hat)
  have hT : Gen.V2.Duty.Trigger E rho o send := Or.inr ⟨v, hv, k, hacc⟩
  have hNX : (fgsa p c).excludes (rho.stateBeforeTime E (a + p.Δ) x) o = false := by
    change excludesS p (rho.stateBeforeTime E (a + p.Δ) x).st o = false
    rw [excludesS_of_block _ hd,
      fgsa_trigger_invalid_false E rho o send s N hT hd _]
    change ((!Block.compatible N.erase (eraseFG _)) || false) = false
    rw [block_compatible_comm, block_compatible_of_preceq hF]
    rfl
  refine ⟨{ dl := fun t => max t E.t_GST + p.Δ
            cut := rho.horizon
            anchor := a
            within := hD
            ready := ?_
            send_le := hsa
            nonneg := ha
            later := ?_
            cut_le := ?_
            horizon := ?_
            freeze_le := ?_
            history := fgsa_historySafeAt_of_proposal x o a hd
            epoch := hRF
            handlers := ?_
            not_excluded := ?_ }⟩
  · refine ⟨v, hv, Or.inr ⟨k, hacc⟩, ?_⟩
    intro t hat htd
    rw [max_eq_left hGST.le] at htd
    exact h.awake x hx t (hGST.le.trans hat) (htd.le.trans hhor)
  · rw [max_eq_left hGST.le]
    exact lt_add_of_pos_right _ p.deltaPos
  · simpa only [max_eq_left hGST.le] using hhor
  · simpa only [max_eq_left hGST.le] using hhor
  · rw [max_eq_left hGST.le]
  · rw [max_eq_left hGST.le]
    exact fgsa_proposal_handlers_at_anchor h.base.valid h.base.delta hx hd hacc hsa ha
      hpub (h.awake x hx a hGST.le (le_add_of_nonneg_right p.deltaPos.le |>.trans hhor))
      (lt_add_of_pos_right _ p.deltaPos) hhor hRF
  · simpa only [max_eq_left hGST.le] using hNX

omit [Fintype V] in
/-- Every stored vote of an honest HEAD seat has its unique emitted payload.
A replayed vote uses its durable proposal's original network delivery. -/
theorem finality_honest_head_pool_unique (hV : V2.D.ExecutionValid E rho)
    {s : Slot} {q : Fin p.n} {b : BlockId} {v : V} {i : Nat}
    (hv : v ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick v (SA.voteTime p.toParams s)))
    (hem : ofHead p ⟨.seat (.head s) q, b⟩ ∈ V2.D.Run.emitsAt E rho i)
    (k : Nat) (x : V) (B : BlockId)
    (hm : baseVote (⟨.seat (.head s) q, B⟩ : HeadWire p.n) ∈
      (rho.stateBefore E k x).st.base.votes) : B = b := by
  have hemit := hem
  rw [(V2.D.Run.step_tick_eq E rho hi).2] at hemit
  have hEm := (fgsa_emits_head E rho _ v _ s q b).mp hemit
  rw [← fgsa_vote_stamp_keys E rho k x] at hm
  obtain ⟨⟨word, stamp⟩, hs, he⟩ := List.mem_map.mp hm
  dsimp only at he
  subst word
  have origin : ∃ (j : Nat) (parent : Obj p) (t : Time),
      rho.events[j]? = some (.deliver x parent t) ∧
      (parent = ofHead p ⟨.seat (.head s) q, B⟩ ∨
        (fgsa p c).carries parent (ofHead p ⟨.seat (.head s) q, B⟩)) := by
    rcases fgsa_vote_stamp_source_or_restart E rho k x s q B stamp hs with
      ⟨j, _, t, ha, _⟩ | ⟨j, _, wake, _, _, hr⟩
    · obtain ⟨parent, hd, hh⟩ := ha.1
      exact ⟨j, parent, t, hd, (fgsaHooks p c).handles_carries _ _ _ hh⟩
    · obtain ⟨l, _, parent, t, hd, hc⟩ :=
        fgsa_replayed_head_delivery_origin E rho j x wake s q B hr
      exact ⟨l, parent, t, hd, Or.inr hc⟩
  obtain ⟨j, parent, t, hd, hh⟩ := origin
  have hholder : V2.D.Run.holder rho (ofHead p ⟨.seat (.head s) q, B⟩).auth = some v :=
    congrArg some hEm.2.2.1
  have hsig : ∃ u, u ≤ t ∧ V2.D.Run.emits E rho v (ofHead p ⟨.seat (.head s) q, B⟩) u := by
    rcases hh with rfl | hc
    · exact hV.unforgeable x _ t ⟨j, hd⟩ v hv hholder
    · exact hV.carried x parent t ⟨j, hd⟩ _ hc v hv hholder
  obtain ⟨u, _, l, hl, hel⟩ := hsig
  rw [(V2.D.Run.step_tick_eq E rho hl).2] at hel
  have hEm' := (fgsa_emits_head E rho _ v u s q B).mp hel
  have ht : u = SA.voteTime p.toParams s := hEm'.2.1.symm
  subst u
  have heq : l = i := fgsa_tick_unique E rho hV.toScheduleWellFormed hl hi
  subst l
  exact hEm'.2.2.2.2.trans hEm.2.2.2.2.symm


private theorem finality_head_keys (o : GridCO.Wire p.n .root) (s : Slot) (q : Fin p.n)
    (hl : GridCO.headLabel? o = some s) (hq : GridCO.headSeat? o = some q) :
    ∃ b, o = ⟨.seat s q, .head b⟩ := by
  obtain ⟨auth, payload⟩ := o
  cases auth with
  | seat r j =>
    cases payload with
    | head B =>
      have hs : r = s := Option.some.inj hl
      have hj : j = q := Option.some.inj hq
      subst r j
      exact ⟨B, rfl⟩
    | proposal B raw sup => cases hl
  | proposer r => cases payload <;> cases hl
  | none => cases payload <;> cases hl

/-- A fresh honest HEAD has a Recovery service from its vote to the requested read.
The previous-slot cutoff excludes a receiver wake between the vote and that read. -/
theorem finality_fresh_head_service {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) {x v : V} {s : Slot} {q : Fin p.n}
    {b : BlockId} {i : Nat} {freeze : Time}
    (hx : x ∈ rho.honest) (hv : v ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick v (SA.voteTime p.toParams s)))
    (hem : ofHead p ⟨.seat (.head s) q, b⟩ ∈ V2.D.Run.emitsAt E rho i)
    (hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1))
    (hfreeze : SA.earlyTime p.toParams s ≤ freeze) (hhor : freeze ≤ rho.horizon) :
    Nonempty (FreshHeadService E rho s q b freeze x) := by
  let a := SA.voteTime p.toParams s
  let d := SA.earlyTime p.toParams s
  let o := ofHead p (⟨.seat (.head s) q, b⟩ : HeadWire p.n)
  have hGST : E.t_GST < a := by
    have hd := p.deltaPos
    change E.t_GST < 4 * p.Δ * (s : Int) + p.Δ
    change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1) at hcut
    linarith
  have had : a < d := by
    change 4 * p.Δ * _ + p.Δ < 4 * p.Δ * _ + 2 * p.Δ
    linarith [p.deltaPos]
  have hadEq : a + p.Δ = d := by
    change 4 * p.Δ * _ + p.Δ + p.Δ = 4 * p.Δ * _ + 2 * p.Δ
    ring
  have hdhor : d ≤ rho.horizon := hfreeze.trans hhor
  have hD := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho h.sync
    (fun o => ¬ isRowObject o) p.Δ (fun o ho => h.base.delta ▸ fgsaDelay_nonrow E.Δ ΔF o ho)
  have hRF : V2.D.restartFree rho x (V2.D.Run.actionCut rho a)
      (V2.D.Run.idxBefore rho freeze) := by
    apply Gen.V2.Duty.restartFree_actionCut_idxBefore h.base.valid.toScheduleWellFormed
      (had.trans_le hfreeze)
    intro j t hj hat _
    exact (not_lt_of_ge (finality_recovery_restart_bound p c E rho h hx
      (List.mem_of_getElem? hj))) (hGST.trans hat)
  have htime : ((4 * s + 2 : Nat) : Time) * p.Δ = d := by
    change ((4 * s + 2 : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int) + 2 * p.Δ
    push_cast
    ring
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho h.base.valid.toScheduleWellFormed h.base.delta
    x hx (4 * s + 2) (htime ▸ hdhor)
    (htime ▸ h.awake x hx d (hGST.le.trans had.le) hdhor)
  rw [htime] at hj
  have hid : V2.D.Run.idxBefore rho d ≤ j := by
    apply Nat.le_of_not_gt
    intro hn
    exact (lt_irrefl d) ((Gen.V2.Duty.index_lt_idxBefore_iff
      h.base.valid.toScheduleWellFormed hj d).mp hn)
  have hwindow : (rho.stateBeforeTime E d x).st.slot p ≤ s + 1 := by
    have hn := V2.D.Engine.stateBefore_now_mono_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho h.base.valid.toScheduleWellFormed hid x
    rw [fgsa_clock_now p c (rho.stateBefore E _ x),
      fgsa_clock_now p c (rho.stateBefore E j x),
      Gen.V2.Duty.stateBefore_idxBefore E rho d h.base.valid.toScheduleWellFormed] at hn
    have hb := fgsa_preTick_now_le E rho h.base.valid.toScheduleWellFormed hj
    have hs : p.slotOf d = s := slotOf_offset p s (2 * p.Δ)
      (by linarith [p.deltaPos]) (by linarith [p.deltaPos])
    exact ((Internal.slotOf_mono (p := p) (hn.trans hb)).trans_eq hs).trans (Nat.le_succ s)
  have hNX : (fgsa p c).excludes (rho.stateBeforeTime E d x) o = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    obtain ⟨u, hu, w, hw, hne, hlu, hlw, hqu, hqw, _, _⟩ :=
      fgsa_head_excluded_before E rho h.base.valid.toScheduleWellFormed x d s q b hwindow he
    obtain ⟨B, rfl⟩ := finality_head_keys u s q hlu hqu
    obtain ⟨C, rfl⟩ := finality_head_keys w s q hlw hqw
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d h.base.valid.toScheduleWellFormed] at hu hw
    have hB := finality_honest_head_pool_unique h.base.valid hv hi hem _ x B hu
    have hC := finality_honest_head_pool_unique h.base.valid hv hi hem _ x C hw
    exact hne (by rw [hB, hC])
  have htick : ((4 * s + 1 : Nat) : Time) * p.Δ = a := by
    change ((4 * s + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int) + p.Δ
    push_cast
    ring
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho h.base.valid.toScheduleWellFormed h.base.delta
    x hx (4 * s + 1) (htick ▸ (had.le.trans hdhor))
    (htick ▸ h.awake x hx a hGST.le (had.le.trans hdhor))
  rw [htick] at hk
  have hak : V2.D.Run.actionCut rho a ≤ k := by
    apply Nat.le_of_not_gt
    intro hn
    have ht := (V2.D.Engine.index_lt_actionCut_iff h.base.valid.toScheduleWellFormed hk a).mp hn
    rcases ht with ht | ⟨_, hp⟩
    · exact (lt_irrefl a ht).elim
    · change (1 : Nat) = 0 at hp
      cases hp
  refine ⟨{ dl := fun t => max t E.t_GST + p.Δ
            cut := rho.horizon
            within := hD
            ready := ⟨v, hv, Or.inl ⟨i, hi, hem⟩, ?_⟩
            later := ?_
            cut_le := ?_
            horizon := ?_
            freeze_le := ?_
            epoch := hRF
            handlers := ?_
            not_excluded := ?_ }⟩
  · intro t hat htd
    rw [max_eq_left hGST.le, hadEq] at htd
    exact h.awake x hx t (hGST.le.trans hat) (htd.le.trans hdhor)
  · change a < max a E.t_GST + p.Δ
    simpa only [max_eq_left hGST.le, hadEq] using had
  · change max a E.t_GST + p.Δ ≤ rho.horizon
    simpa only [max_eq_left hGST.le, hadEq] using hdhor
  · change max a E.t_GST + p.Δ ≤ rho.horizon
    simpa only [max_eq_left hGST.le, hadEq] using hdhor
  · change max a E.t_GST + p.Δ ≤ freeze
    simpa only [max_eq_left hGST.le, hadEq] using hfreeze
  · intro l t hat htd hh
    rw [max_eq_left hGST.le, hadEq] at htd
    obtain ⟨parent, he, hhandles⟩ := hh
    have hwf := handles_wellFormed p c _ parent o hhandles (h.base.valid.wire l x parent t he)
    refine ⟨hwf, depsS_of_not_block (rho.stateBefore E l x).st o (by intro r N hn; cases hn), ?_⟩
    apply Gen.V2.Duty.timely_of_clock E rho (fgsaTimelyClock p c)
      h.base.valid.toScheduleWellFormed x o a k l
    · rw [fgsaTimelyClock_actTime]
      change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
      linarith [p.deltaPos]
    · exact hk
    · exact V2.D.Engine.tick_index_lt_delivery E rho h.base.valid.toScheduleWellFormed hk he hat
    · exact hRF.mono hak
        ((Gen.V2.Duty.index_lt_idxBefore_iff h.base.valid.toScheduleWellFormed he freeze).mpr
          (htd.trans_le hfreeze)).le
  · change (fgsa p c).excludes (rho.stateBeforeTime E (max a E.t_GST + p.Δ) x) o = false
    simpa only [max_eq_left hGST.le, hadEq] using hNX

/-- The original proposal acceptance behind a held target, before it is wrapped. -/
private theorem d7a5s_target_core {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF)
    {i : Nat} {v x : V} {a : Time}
    {K : Block} (hv : v ∈ rho.honest) (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick v a))
    (hK : K ∈ (rho.stateBefore E i v).st.base.blocks)
    (ha : 0 ≤ a) (hpub : V2.PublicTime E a) (hGST : E.t_GST < a)
    (hhor : a + p.Δ ≤ rho.horizon)
    (hF : Block.Preceq (eraseFG (rho.stateBeforeTime E (a + p.Δ) x).st.fg.F) K) :
    K = .genesis ∨ ∃ s N send, NamedProposal.erase N = K ∧
      Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩) send (a + p.Δ)
        x) := by
  by_cases hg : K = .genesis
  · exact Or.inl hg
  right
  obtain ⟨j, hj, send, o, ho, hacc⟩ := fgsa_block_accepted_origin E rho i v K hg hK
  have hsa : send ≤ a := by
    obtain ⟨parent, he, _⟩ := hacc.1
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp he
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    have ht := List.pairwise_iff_getElem.mp h.base.valid.sorted j i hjl hil hj
    rw [hje, hie] at ht
    exact V2.D.Engine.time_le_of_key_le _ _ ht
  unfold blockOf? at ho
  cases hd : (toWire p o).decode with
  | none => simp only [hd, reduceCtorEq] at ho
  | some m =>
    cases m <;> simp only [hd, reduceCtorEq, Option.some.injEq] at ho
    rename_i s N
    have he : o = ofWire p ⟨.proposer s, .proposal N⟩ := by
      apply toWire_injective
      rw [toWire_ofWire]
      exact decode_eq_block.mp hd
    subst o
    exact ⟨s, N, send, ho,
      finality_proposal_receiver_service h hx hv hacc hsa ha hpub hGST hhor (ho ▸ hF)⟩

/-- A held target has an original proposal acceptance, including before a restart.
The finality guard is at the service deadline. -/
theorem finality_target_service_of_held {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF)
    (hGenesis : ∀ D x, TargetReceiptService E rho .genesis D x)
    {i : Nat} {v x : V} {a : Time}
    {K : Block} (hv : v ∈ rho.honest) (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick v a))
    (hK : K ∈ (rho.stateBefore E i v).st.base.blocks)
    (ha : 0 ≤ a) (hpub : V2.PublicTime E a) (hGST : E.t_GST < a)
    (hhor : a + p.Δ ≤ rho.horizon)
    (hF : Block.Preceq (eraseFG (rho.stateBeforeTime E (a + p.Δ) x).st.fg.F) K) :
    TargetReceiptService E rho K (a + p.Δ) x := by
  rcases d7a5s_target_core h hv hx hi hK ha hpub hGST hhor hF with hg | ⟨s, N, send, he, hs⟩
  · exact hg ▸ hGenesis (a + p.Δ) x
  · exact he ▸ fgsa_target_service_of_proposal E rho s N send (a + p.Δ) x hs


omit [Fintype V] in
/-- A post-clock read retains the exact tick index and clock equation. -/
theorem finality_postClock_tick {x : V} {t : Time} {nd : Node p}
    (hnd : postClock E rho x t = some nd) :
    ∃ i, rho.events[i]? = some (.tick x t) ∧
      (fgsa p c).clock (rho.stateBefore E i x) t = nd := by
  rw [postClock_def, preTick_def] at hnd
  cases hi : V2.D.Run.tickIdx? rho x t with
  | none => rw [hi] at hnd; cases hnd
  | some i =>
    rw [hi] at hnd
    exact ⟨i, V2.D.Run.tickIdx?_spec hi, Option.some.inj hnd⟩

omit [Fintype V] in
/-- Finality is durable and monotone across every receiver restart. -/
theorem finality_F_mono_idx {i j : Nat} (hij : i ≤ j) (x : V) :
    FGBlock.Preceq (storeAt p c E rho i x).fg.F (storeAt p c E rho j x).fg.F := by
  let X := (storeAt p c E rho i x).fg.F
  have hm := fgsa_monoAlong_preceq_F p c X
  rw [Gen.V2.Duty.MonoAlong_def] at hm
  exact V2.D.Engine.stateBefore_stable_restore (P := fgsa p c)
    (fun nd => FGBlock.Preceq X nd.st.fg.F) hm.1 hm.2.1 hm.2.2 E rho hij x
    (finality_restore_preceq_F p c X) (KitFG.preceq_refl X)

omit [Fintype V] in
/-- The strict deadline's finality is below finality at the actual post-clock read. -/
theorem finality_F_before_postClock (hS : V2.D.ScheduleWellFormed E rho)
    {x : V} {t : Time} {nd : Node p} (hnd : postClock E rho x t = some nd) :
    FGBlock.Preceq (rho.stateBeforeTime E t x).st.fg.F nd.st.fg.F := by
  obtain ⟨i, hi, hclock⟩ := finality_postClock_tick hnd
  have hidx : V2.D.Run.idxBefore rho t ≤ i := by
    apply Nat.le_of_not_gt
    intro hn
    exact (lt_irrefl t) ((Gen.V2.Duty.index_lt_idxBefore_iff hS hi t).mp hn)
  have hm := finality_F_mono_idx (E := E) (rho := rho) hidx x
  rw [← hclock]
  change FGBlock.Preceq _ (FGSA.clock p _ t).fg.F
  rw [clock_F_eq]
  change FGBlock.Preceq (rho.stateBefore E (V2.D.Run.idxBefore rho t) x).st.fg.F
    (rho.stateBefore E i x).st.fg.F at hm
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho t hS] at hm
  exact hm

/-- The action-receipt derivation, for any wrapping of the held target's service. -/
private theorem d7a5s_action_core {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) {TRS : Block → Time → V → Prop}
    (target : ∀ {i : Nat} {v x : V} {a : Time} {K : Block}, v ∈ rho.honest →
      x ∈ rho.honest → rho.events[i]? = some (.tick v a) →
      K ∈ (rho.stateBefore E i v).st.base.blocks → 0 ≤ a → V2.PublicTime E a →
      E.t_GST < a → a + p.Δ ≤ rho.horizon →
      Block.Preceq (eraseFG (rho.stateBeforeTime E (a + p.Δ) x).st.fg.F) K → TRS K (a + p.Δ) x)
    (r : Nat) (x : V) (hx : x ∈ rho.honest) (_hact : E.t_GST < p.actionTime r)
    (hcut : E.t_GST ≤ slotStartZ p (((r * p.R + 1 : Nat) : Int) - 1))
    (hhor : p.actionTime r ≤ rho.horizon) (nd : Node p)
    (hnd : postClock E rho x (p.actionTime r) = some nd) (q : Fin p.n) (K : Block)
    (hv : rho.seatOf (.base (.head (r * p.R + 1))) q ∈ rho.honest)
    (hhead : headAtLabel p c E rho (rho.seatOf (.base (.head (r * p.R + 1))) q)
      (r * p.R + 1) = some K)
    (hFK : Block.Preceq (eraseFG nd.st.fg.F) K) :
    Nonempty (FreshHeadService E rho (r * p.R + 1) q K.root (p.actionTime r) x) ∧
      TRS K (p.actionTime r) x := by
  let s := r * p.R + 1
  let v := rho.seatOf (.base (.head s)) q
  have hearly : SA.earlyTime p.toParams s = p.actionTime r := by
    change 4 * p.Δ * ((r * p.R + 1 : Nat) : Int) + 2 * p.Δ =
      4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    push_cast
    ring
  have hvhor : SA.voteTime p.toParams s ≤ rho.horizon := by
    have hd := p.deltaPos
    rw [← hearly] at hhor
    change 4 * p.Δ * (s : Int) + p.Δ ≤ rho.horizon
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ rho.horizon at hhor
    linarith
  have hGST : E.t_GST < SA.voteTime p.toParams s := by
    change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1) at hcut
    change E.t_GST < 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  change (postClock E rho v (SA.voteTime p.toParams s)).map
    (fun nd => FGSA.headVote p nd.st s) = some K at hhead
  obtain ⟨headNode, hh, hK⟩ := Option.map_eq_some_iff.mp hhead
  obtain ⟨i, hi, hc⟩ := finality_postClock_tick hh
  have hJ := finality_recovery_joined p c E rho h hv hcut hGST.le hvhor
  have hem : ofHead p ⟨.seat (.head s) q, K.root⟩ ∈ V2.D.Run.emitsAt E rho i := by
    rw [(V2.D.Run.step_tick_eq E rho hi).2]
    apply (fgsa_emits_head E rho _ v _ s q K.root).mpr
    refine ⟨hJ.1, rfl, rfl, fgsa_head_joined_of_joinedAt E rho
      h.base.valid.toScheduleWellFormed hi hJ, ?_⟩
    change K.root = (FGSA.headVote p
      ((fgsa p c).clock (rho.stateBefore E i v) (SA.voteTime p.toParams s)).st s).root
    rw [hc, hK]
  have hKheld : K ∈ (rho.stateBefore E i v).st.base.blocks := by
    have hm := headVote_stored p
      ((fgsa p c).clock (rho.stateBefore E i v) (SA.voteTime p.toParams s)).st
      (storeBundle_postClock E rho i v (SA.voteTime p.toParams s)).cstore s
    rw [hc, hK, ← hc] at hm
    change K ∈ (FGSA.clock p (rho.stateBefore E i v).st (SA.voteTime p.toParams s)).base.blocks
      at hm
    rwa [clock_base_blocks] at hm
  have hpub : V2.PublicTime E (SA.voteTime p.toParams s) := by
    refine ⟨4 * s + 1, ?_⟩
    rw [h.base.delta]
    change 4 * p.Δ * (s : Int) + p.Δ = ((4 * s + 1 : Nat) : Int) * p.Δ
    push_cast
    ring
  have ha : 0 ≤ SA.voteTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + p.Δ
    have hd := p.deltaPos
    positivity
  have hF := Gen.Pure.block_preceq_trans
    (eraseFG_preceq (finality_F_before_postClock h.base.valid.toScheduleWellFormed hnd)) hFK
  have he : SA.voteTime p.toParams s + p.Δ = p.actionTime r := by
    change 4 * p.Δ * ((r * p.R + 1 : Nat) : Int) + p.Δ + p.Δ =
      4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    push_cast
    ring
  have htarget := target hv hx hi hKheld ha hpub
    hGST (by simpa only [he] using hhor) (by simpa only [he] using hF)
  have hheadService := finality_fresh_head_service h hx hv hi hem hcut hearly.le hhor
  exact ⟨hheadService, by simpa only [he] using htarget⟩

/-- Recovery proves action receipts in the exact receiver and finality scope.
Only the opaque Shared genesis constructor is left as an API input. -/
theorem finality_action_receipts {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF)
    (hGenesis : ∀ D x, TargetReceiptService E rho .genesis D x) :
    FinalityActionReceipts p c E rho := by
  constructor
  intro r x hx hact hcut hhor nd hnd q K hv hhead hFK
  exact d7a5s_action_core h (fun hv hx hi hK ha hpub hGST hhor hF =>
    finality_target_service_of_held h hGenesis hv hx hi hK ha hpub hGST hhor hF)
    r x hx hact hcut hhor nd hnd q K hv hhead hFK

/-- The Tail target is relayed as a durable proposal from the actual action read. -/
theorem finality_tail_head_receipts {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt)
    (hGenesis : ∀ D x, TargetReceiptService E rho .genesis D x) :
    TailHeadReceipts (p := p) (c := c) (E := E) (rho := rho) ΔF pt := by
  constructor
  intro x nd H hx hnd hH y hy hprop hF
  obtain ⟨i, hi, hc⟩ := finality_postClock_tick hnd
  have hheld : eraseFG H ∈ (rho.stateBefore E i x).st.base.blocks := by
    have htf := hH
    rw [← hc] at htf
    have hm := ((storeBundle_postClock E rho i x _).cstore.baseTree (eraseFG H)).mpr
      ⟨H, htf, rfl⟩
    change eraseFG H ∈ (FGSA.clock p (rho.stateBefore E i x).st
      (p.actionTime (pt.r + 1))).base.blocks at hm
    rwa [clock_base_blocks] at hm
  have hGST : E.t_GST < p.actionTime (pt.r + 1) :=
    ((ktail_slot_gst hT (s := pt.r * p.R) le_rfl).trans
      (kmid_proposal_le_action p le_rfl)).trans_lt
      (kmid_action_strictMono p (Nat.lt_succ_self pt.r))
  have hwin := ktail_batch_horizon hT hGST.le le_rfl le_rfl
  have hd : p.Δ ≤ ΔF := hT.set.base.delta ▸ hT.set.deltaF
  have hhor : p.actionTime (pt.r + 1) + p.Δ ≤ rho.horizon := by
    rw [max_eq_left hGST.le] at hwin
    exact ((Int.add_le_add_left hd _).trans hwin.1).trans hwin.2
  have hpub : V2.PublicTime E (p.actionTime (pt.r + 1)) := by
    refine ⟨4 * ((pt.r + 1) * p.R) + 6, ?_⟩
    rw [hT.set.base.delta]
    change 4 * p.Δ * (((pt.r + 1) * p.R : Nat) : Int) + 6 * p.Δ =
      ((4 * ((pt.r + 1) * p.R) + 6 : Nat) : Int) * p.Δ
    push_cast
    ring
  have ha : 0 ≤ p.actionTime (pt.r + 1) := by
    change 0 ≤ 4 * p.Δ * (((pt.r + 1) * p.R : Nat) : Int) + 6 * p.Δ
    have hd := p.deltaPos
    positivity
  have hF' : Block.Preceq
      (eraseFG (rho.stateBeforeTime E (p.actionTime (pt.r + 1) + p.Δ) y).st.fg.F)
      (eraseFG H) := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hT.set.base.valid.toScheduleWellFormed]
    exact eraseFG_preceq hF
  exact finality_target_service_of_held hT.set hGenesis hx hprop hi hheld ha hpub hGST hhor hF'


/-- Recovery supplies current honest votes at every read in the exact internal scope. -/
theorem finality_scoped_vote_receipts {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) : FinalityScopedVoteReceipts E rho := by
  constructor
  intro s x t nd hx hcut hfreeze hhor hnd y a hy hem hl
  obtain ⟨q, ha⟩ := finality_emitted_head_form E rho h.base.valid y s a hy hem
  rw [ha] at hem ⊢
  obtain ⟨i, hi, ho⟩ := hem
  obtain ⟨hService⟩ := finality_fresh_head_service h hx hy hi ho hcut hfreeze hhor
  have hp := (hService.receipt h.base.valid hx hi ho).1
  obtain ⟨j, hj, hc⟩ := finality_postClock_tick hnd
  have hid : V2.D.Run.idxBefore rho t ≤ j := by
    apply Nat.le_of_not_gt
    intro hn
    exact (lt_irrefl t) ((Gen.V2.Duty.index_lt_idxBefore_iff
      h.base.valid.toScheduleWellFormed hj t).mp hn)
  have hGST : E.t_GST < t := by
    change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1) at hcut
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ t at hfreeze
    linarith [p.deltaPos]
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho t h.base.valid.toScheduleWellFormed] at hp
  have hm := fgsa_votes_cumulative_on p c E rho hid x
    (finality_recovery_readEpoch p c E rho h hx hGST j) hp
  rw [← hc]
  change baseVote _ ∈ (FGSA.clock p (rho.stateBefore E j x).st t).base.votes
  rw [(clock_vn _ _).1]
  exact hm

/-- The scoped supplier preserves FullVoteService's resolved-head support filter. -/
theorem finality_full_vote_at_scoped_read {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) {s : Slot} {x : V} {t : Time} {nd : Node p}
    (hx : x ∈ rho.honest) (hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1))
    (hfreeze : SA.earlyTime p.toParams s ≤ t) (hhor : t ≤ rho.horizon)
    (hnd : postClock E rho x t = some nd) : FullVoteService p c E rho nd.st s :=
  finality_full_vote_of_receipts E rho s nd
    ((finality_scoped_vote_receipts h).receipt s x t nd hx hcut hfreeze hhor hnd)

/-- Recovery supplies both public TVote read shapes with their GST cutoffs. -/
theorem finality_vote_receipts {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) : FinalityVoteReceipts E rho := by
  constructor
  · intro v nd hv hcut hSync hnd y a hy hem hl
    obtain ⟨dl, cut, _, _, _, _, _, _, hhor⟩ := hSync
    have hfreeze : SA.earlyTime p.toParams (v - 1) ≤ SA.proposalTime p.toParams v := by
      have hv0 : 0 < v := hv.1
      have hvcast : ((v - 1 : Nat) : Int) + 1 = (v : Int) := by
        rw [Nat.cast_sub (Nat.succ_le_of_lt hv0)]
        simp
      change 4 * p.Δ * ((v - 1 : Nat) : Int) + 2 * p.Δ ≤ 4 * p.Δ * (v : Int)
      nlinarith [p.deltaPos]
    exact (List.mem_filter.mp ((finality_full_vote_at_scoped_read h hv.2 hcut
      hfreeze hhor hnd) y a hy hem hl).1).1
  · intro r x nd hx hcut hSync hnd y a hy hem hl
    obtain ⟨dl, cut, _, _, _, _, _, _, hhor⟩ := hSync
    have hfreeze : SA.earlyTime p.toParams (r * p.R + 1) ≤ p.actionTime r := by
      change 4 * p.Δ * ((r * p.R + 1 : Nat) : Int) + 2 * p.Δ ≤
        4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
      push_cast
      ring_nf
      exact le_rfl
    exact (List.mem_filter.mp ((finality_full_vote_at_scoped_read h hx hcut
      hfreeze hhor hnd) y a hy hem hl).1).1

section
variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private def d7a5s_timing : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

/-- The actual FG-SA service reads (the receipt service reads only the HEAD label). -/
private def d7a5s_ac (w : HealingWitness) : FGCompose.FGACServiceReads V where
  honest x := x ∈ rho.honest
  proposal := HonestProposal E rho (fgsaInterface p c)
  proposalTime := SA.proposalTime p.toParams
  voteTime := SA.voteTime p.toParams
  gateTime := SA.gateTime p.toParams
  gateLabel q := q * p.R
  actionHeadLabel q := q * p.R + 1
  actionTime := p.actionTime
  proposalScope s _ := w.sStar + 2 ≤ s
  sourceScope x r B := ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
    eraseFG C = B ∧ high p w C
  headScope x s := joinedAt p E rho x s (SA.voteTime p.toParams s)
  gateScope x s := confirmedReaderAtIdx p c E rho x
    (afterTicksIdx rho (SA.gateTime p.toParams s)) (SA.gateTime p.toParams s)
  actionScope x q := ∃ nd, postClock E rho x (p.actionTime q) = some nd
  headAtLabel := headAtLabel p c E rho
  actionHead x q := (postClock E rho x (p.actionTime q)).map
    (fun nd => (fgBlockOf nd.st (fgHead p nd.st)).map eraseFG)
  gate := gateResult p c E rho
  source := actionSource p c E rho
  parent := proposalHeadAt p c E rho
  gateFloor x s := (gateIn p c E rho x s).map (fun st => eraseFG st.fg.F)
  frame x q B := ∀ nd, postClock E rho x (p.actionTime q) = some nd →
    ∃ D, eraseFG D = B ∧ D ∈ nd.st.fg.TF ∧
      FGBlock.Preceq (FGSA.controls p nd.st).F D ∧
      FGBlock.Preceq (FGSA.controls p nd.st).Z D ∧
      (FGSA.controls p nd.st).lo ≤ (heightView p D).h
  below := Block.Preceq

omit [Fintype V] in
/-- A receiver service is the generic receiver service, field by field. -/
private theorem d7a5s_receiver {o : Obj p} {send freeze : Time} {x : V}
    (h : ReceiverService E rho o send freeze x) :
    Nonempty (FGCompose.ReceiverService (fun o => ¬ isRowObject o) (fgsaTimely p) E rho o
      send freeze x) :=
  ⟨⟨h.dl, h.cut, h.anchor, h.within, h.ready, h.send_le, h.nonneg, h.later, h.cut_le,
    h.horizon, h.freeze_le, h.history, h.epoch, h.handlers, h.not_excluded⟩⟩

/-- Receipt ruling (option A): the generic target service is produced from the original
proposal acceptance, before the FG-SA wrapper hides it. -/
private theorem d7a5s_target_generic {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) {i : Nat} {v x : V} {a : Time}
    {K : Block} (hv : v ∈ rho.honest) (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick v a))
    (hK : K ∈ (rho.stateBefore E i v).st.base.blocks)
    (ha : 0 ≤ a) (hpub : V2.PublicTime E a) (hGST : E.t_GST < a)
    (hhor : a + p.Δ ≤ rho.horizon)
    (hF : Block.Preceq (eraseFG (rho.stateBeforeTime E (a + p.Δ) x).st.fg.F) K) :
    FGCompose.TargetReceiptService (fun s N => ofWire p ⟨.proposer s, .proposal N⟩)
      NamedProposal.erase (fun o => ¬ isRowObject o) (fgsaTimely p) E rho K (a + p.Δ) x := by
  rcases d7a5s_target_core h hv hx hi hK ha hpub hGST hhor hF with
    hg | ⟨s, N, send, he, ⟨hs⟩⟩
  · exact Or.inl hg
  · exact Or.inr ⟨s, N, send, he, d7a5s_receiver p c E rho hs⟩

private theorem d7a5s_core_fg (nd : (fgsa p c).State) :
    ((fgsaCoreReads p c).core nd).fg = nd.st.fg := by
  rw [fgsaCoreReads_def]

private theorem d7a5s_erase : (fgsaCoreReads p c).erase = eraseFG := by
  rw [fgsaCoreReads_def]

/-- Receipt ruling (option A): the generic action receipts, from the same original
witnesses as `finality_action_receipts`. -/
private theorem d7a5s_action_receipts {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (w : HealingWitness) :
    FGCompose.FinalityActionReceipts (d7a5s_timing p) (fgsaCoreReads p c)
      (d7a5s_ac p c E rho w) E rho (fun s a => rho.seatOf (.base (.head s)) a)
      (fun o => ¬ isRowObject o) (fgsaTimely p)
      (fun s q b => ofHead p ⟨.seat (.head s) q, b⟩)
      (fun s N => ofWire p ⟨.proposer s, .proposal N⟩) NamedProposal.erase := by
  constructor
  intro r x hx hact hcut hhor nd hnd q K hv hhead hFK
  rw [d7a5s_core_fg, d7a5s_erase] at hFK
  obtain ⟨⟨hs⟩, ht⟩ := d7a5s_action_core h (TRS := fun K D x =>
    FGCompose.TargetReceiptService (fun s N => ofWire p ⟨.proposer s, .proposal N⟩)
      NamedProposal.erase (fun o => ¬ isRowObject o) (fgsaTimely p) E rho K D x)
    (fun hv hx hi hK ha hpub hGST hhor hF =>
      d7a5s_target_generic p c E rho h hv hx hi hK ha hpub hGST hhor hF)
    r x hx hact hcut hhor nd hnd q K hv hhead hFK
  exact ⟨⟨⟨hs.dl, hs.cut, hs.within, hs.ready, hs.later, hs.cut_le, hs.horizon, hs.freeze_le,
    hs.epoch, hs.handlers, hs.not_excluded⟩⟩, ht⟩

end

end AvailableChain.FGSA.Run
end
