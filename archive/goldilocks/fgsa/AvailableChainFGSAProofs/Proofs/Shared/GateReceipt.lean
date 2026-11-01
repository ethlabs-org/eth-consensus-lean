module

public import AvailableChainFGSAProofs.Proofs.Shared.CatchUp

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 erratum 13; blueprint 21 H.22:3100–3120, 02:531–541, 03:293–312.
DC: Goldfish/Confirmation.lean:434–441, HonestSupport.vote.
INTENTIONAL: the consumer supplies two prefixes of each honest awake HEAD,
including the FG-SA active floor. Shared does not derive lane geometry. -/
structure GateReceiptGeometry (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (pre : State p.n) (s : Slot) (B : Block) : Prop where
  target_floor : ∀ q : Fin p.n, rho.seatOf (.base (.head s)) q ∈ rho.honest →
    E.awake (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s) = true →
    ∀ K, HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
      (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
      Block.Preceq (eraseFG pre.fg.F) K
  covered_prefix : ∀ q : Fin p.n, rho.seatOf (.base (.head s)) q ∈ rho.honest →
    E.awake (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s) = true →
    ∀ K, HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
      (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
      Block.Preceq B K

private theorem gateReceipt_find_kept {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List (α × Time)} (hp : xs <+: ys) (a : α)
    (hm : a ∈ xs.map Prod.fst) :
    ys.find? (fun row => row.1 == a) = xs.find? (fun row => row.1 == a) := by
  obtain ⟨tail, he⟩ := hp
  rw [← he, List.find?_append]
  cases hf : xs.find? (fun row => row.1 == a) with
  | none =>
    obtain ⟨⟨b, t⟩, ht, hb⟩ := List.mem_map.mp hm
    dsimp only at hb
    subst b
    have hn := List.find?_eq_none.mp hf (a, t) ht
    simp only [beq_self_eq_true] at hn
    exact (hn trivial).elim
  | some row => rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 02:537–539, original early stamps remain.
DC: Handlers/GoldfishVotePool.lean:810, admittedBefore_ancestor_mem_and_stamp_at.
INTENTIONAL: FG-SA keeps first-receipt lists through clockPre and actView;
this equality needs the receiver epoch, not a Clean foundation or honest reader. -/
theorem fgsa_gateReceipt_stamps_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {j i : Nat} (hji : j ≤ i) (x : V) (hRF : V2.D.restartFree rho x j i) (s : Slot)
    (o : GridCO.Wire p.n .root) (K : Block)
    (ho : o ∈ (storeAt p c E rho j x).base.votes)
    (hK : K ∈ (storeAt p c E rho j x).base.blocks) :
    let v := actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    o ∈ (storeAt p c E rho i x).base.votes ∧
      GridCO.stampVote v o = GridCO.stampVote (storeAt p c E rho j x).base o ∧
      GridCO.stampBlock v K = GridCO.stampBlock (storeAt p c E rho j x).base K := by
  intro v
  have hc := fgsa_store_cumulative_on p c E rho hji x hRF
  have hv : o ∈ (storeAt p c E rho j x).base.voteStamp.map Prod.fst := by
    change o ∈ (V2.D.Run.stateBefore E rho j x).st.base.voteStamp.map Prod.fst
    rw [fgsa_vote_stamp_keys E rho j x]
    exact ho
  have hb : K ∈ (storeAt p c E rho j x).base.blockStamp.map Prod.fst := by
    change K ∈ (V2.D.Run.stateBefore E rho j x).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho j x).«meta».stampKeys]
    exact hK
  have hev := gateReceipt_find_kept hc.2.2.2.1 o hv
  have heb := gateReceipt_find_kept hc.2.2.1 K hb
  refine ⟨?_, ?_, ?_⟩
  · change o ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes
    rw [← fgsa_vote_stamp_keys E rho i x]
    obtain ⟨row, hr, he⟩ := List.mem_map.mp hv
    exact List.mem_map.mpr ⟨row, hc.2.2.2.1.subset hr, he⟩
  · change (((clockPre p _ _).base.voteStamp.find? _).map Prod.snd).getD _ = _
    rw [(clockPre_stamps p _ _).2, hev]
    unfold GridCO.stampVote
    cases he : (storeAt p c E rho j x).base.voteStamp.find? (fun row => row.1 == o) with
    | none =>
      obtain ⟨row, hr, ho⟩ := List.mem_map.mp hv
      have hn := List.find?_eq_none.mp he row hr
      rw [ho, beq_self_eq_true] at hn
      contradiction
    | some row => rfl
  · change (((clockPre p _ _).base.blockStamp.find? _).map Prod.snd).getD _ = _
    rw [(clockPre_stamps p _ _).1, heb]
    unfold GridCO.stampBlock
    cases he : (storeAt p c E rho j x).base.blockStamp.find? (fun row => row.1 == K) with
    | none =>
      obtain ⟨row, hr, ho⟩ := List.mem_map.mp hb
      have hn := List.find?_eq_none.mp he row hr
      rw [ho, beq_self_eq_true] at hn
      contradiction
    | some row => rfl

/-- The legacy stamp API follows from the local receiver epoch API. -/
theorem fgsa_gateReceipt_stamps
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hN : V2.D.NoRestart rho)
    {j i : Nat} (hji : j ≤ i) (x : V) (s : Slot)
    (o : GridCO.Wire p.n .root) (K : Block)
    (ho : o ∈ (storeAt p c E rho j x).base.votes)
    (hK : K ∈ (storeAt p c E rho j x).base.blocks) :
    let v := actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    o ∈ (storeAt p c E rho i x).base.votes ∧
      GridCO.stampVote v o = GridCO.stampVote (storeAt p c E rho j x).base o ∧
      GridCO.stampBlock v K = GridCO.stampBlock (storeAt p c E rho j x).base K :=
  fgsa_gateReceipt_stamps_on E rho hji x (hN.restartFree x j i) s o K ho hK

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 02:537–539, strict early block stamps.
DC: Handlers/GoldfishVotePool.lean:810, admittedBefore_ancestor_mem_and_stamp_at.
INTENTIONAL: an FG-SA stamp is the original local pre-process clock;
the strict tick read bounds it, including genesis at positive times. -/
theorem fgsa_gateReceipt_block_stamp_lt_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hsch : V2.D.ScheduleWellFormed E rho)
    {j : Nat} {x : V} {t : Time} (hj : rho.events[j]? = some (.tick x t))
    (ht : 0 < t)
    (hEpoch : ∀ k w, k < j → rho.events[k]? = some (.restart x w) → w < t)
    (K : Block) (hK : K ∈ (storeAt p c E rho j x).base.blocks) :
    GridCO.stampBlock (storeAt p c E rho j x).base K < t := by
  have hm : K ∈ (V2.D.Run.stateBefore E rho j x).st.base.blockStamp.map Prod.fst := by
    rw [(storeBundle_stateBefore E rho j x).«meta».stampKeys]
    exact hK
  change (((V2.D.Run.stateBefore E rho j x).st.base.blockStamp.find? _).map Prod.snd).getD _ < t
  cases he : (V2.D.Run.stateBefore E rho j x).st.base.blockStamp.find? (fun row => row.1 == K) with
  | none =>
    obtain ⟨row, hr, hb⟩ := List.mem_map.mp hm
    have hn := List.find?_eq_none.mp he row hr
    rw [hb, beq_self_eq_true] at hn
    contradiction
  | some row =>
    change row.2 < t
    rcases fgsa_block_stamp_source_or_restart E rho j x row.1 row.2
        (List.mem_of_find?_eq_some he) with
      ⟨_, hs⟩ | ⟨l, hl, _, _, _, _, hs⟩ | ⟨l, hl, w, hr, _, _, hs⟩
    · rw [hs]
      exact ht
    · rw [hs]
      have hb := V2.D.Engine.stateBefore_now_mono_atRestart (fgsaClock p c)
        (fgsaRestoreTimeLaw p c) E rho hsch hl.le x
      rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho l x),
        fgsa_clock_now p c (V2.D.Run.stateBefore E rho j x)] at hb
      exact hb.trans_lt (fgsa_preTick_now_lt E rho hsch hj ht hEpoch)
    · rw [hs]
      exact hEpoch l w hl hr

theorem fgsa_gateReceipt_block_stamp_lt
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hsch : V2.D.ScheduleWellFormed E rho) (hN : V2.D.NoRestart rho)
    {j : Nat} {x : V} {t : Time} (hj : rho.events[j]? = some (.tick x t))
    (ht : 0 < t) (K : Block) (hK : K ∈ (storeAt p c E rho j x).base.blocks) :
    GridCO.stampBlock (storeAt p c E rho j x).base K < t :=
  fgsa_gateReceipt_block_stamp_lt_on E rho hsch hj ht
    (fun k w _ he => (hN k x w he).elim) K hK

private theorem gateReceipt_floor_mono
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hN : V2.D.NoRestart rho)
    {j i : Nat} (hji : j ≤ i) (x : V) :
    Block.Preceq (eraseFG (storeAt p c E rho j x).fg.F)
      (eraseFG (storeAt p c E rho i x).fg.F) := by
  apply eraseFG_preceq
  have h := fgsa_monoAlong_preceq_F p c (storeAt p c E rho j x).fg.F
  rw [Gen.V2.Duty.MonoAlong_def] at h
  exact V2.D.Engine.stateBefore_stable _ h.1 h.2.1 h.2.2 E rho hji x
    (hN.restartFree x j i) (KitFG.preceq_refl _)

omit [DecidableEq V] in
private theorem gateReceipt_idx_mono (rho : V2.D.Run V (fgsa p c)) :
    Monotone (V2.D.Run.idxBefore rho) := by
  intro a b hab
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true
    (lt_of_lt_of_le (of_decide_eq_true he) hab))

private theorem gateReceipt_block_decode {o : Obj p} {b : Block}
    (h : blockOf? p o = some b) :
    ∃ s N, o = ofWire p ⟨.proposer s, .proposal N⟩ ∧ N.erase = b := by
  unfold blockOf? at h
  cases hd : (toWire p o).decode with
  | none => simp only [hd, reduceCtorEq] at h
  | some m =>
    cases m <;> simp only [hd, reduceCtorEq, Option.some.injEq] at h
    rename_i s N
    refine ⟨s, N, ?_, h⟩
    apply toWire_injective
    rw [toWire_ofWire]
    exact decode_eq_block.mp hd

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 02:537–539 and 03:293–304, compatible receipt before a read.
DC: Handlers/GoldfishVotePool.lean:810, retained resolved block membership.
INTENTIONAL: the receiving FG-SA floor bounds earlier admission floors.
Only the opaque proposal row list is passed to the receipt interface.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_gateReceipt_block_to_tick
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (dl : Time → Time) (cut : Time) (hD : Gen.V2.Duty.DeliveryWithinOn E rho
      (fun o => ¬ isRowObject o) dl cut)
    (t : Time) (o : Obj p) (K : Block) (ho : blockOf? p o = some K)
    (hT : Gen.V2.Duty.Trigger E rho o t) (hlt : t < dl t) (hc : dl t ≤ cut)
    {j : Nat} {x : V} {u : Time} (hx : x ∈ rho.honest)
    (hj : rho.events[j]? = some (.tick x u)) (hd : dl t ≤ u)
    (hF : Block.Preceq (eraseFG (storeAt p c E rho j x).fg.F) K)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    K ∈ (storeAt p c E rho j x).base.blocks := by
  have hsch := hE.toScheduleWellFormed
  have hidx := gateReceipt_idx_mono rho hd
  have hfloor := gateReceipt_floor_mono E rho hN hidx x
  change Block.Preceq (eraseFG (V2.D.Run.stateBefore E rho
    (V2.D.Run.idxBefore rho (dl t)) x).st.fg.F)
    (eraseFG (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho u) x).st.fg.F) at hfloor
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hsch,
    Gen.V2.Duty.stateBefore_idxBefore E rho u hsch,
    ← fgsa_preTick_eq_timeRead E rho hsch hN hj] at hfloor
  have hcompat := Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K)
    (Gen.Pure.block_preceq_trans hfloor hF)
  obtain ⟨s, N, rfl, heN⟩ := gateReceipt_block_decode ho
  obtain ⟨Y, hY, he⟩ := fgsa_proposal_receipt (hRoots := hroots) E rho hDelta hE hN dl cut
    s N t x hD hT hx hc hlt (by simpa only [heN] using hcompat)
    (hd.trans (hE.in_horizon _ (List.mem_of_getElem? hj)).2)
    (fgsa_awakeOn_before_tick_noRestart E rho hE hN hj hx
      (fgsa_trigger_nonneg E rho hsch hT) hd)
  have hkeep := (fgsa_store_cumulative p c E rho hN hidx x).1
  change (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho (dl t)) x).st.fg.TF ⊆
    (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho u) x).st.fg.TF at hkeep
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hsch,
    Gen.V2.Duty.stateBefore_idxBefore E rho u hsch,
    ← fgsa_preTick_eq_timeRead E rho hsch hN hj] at hkeep
  exact ((cstoreInv_stateBefore E rho j x).baseTree K).mpr ⟨Y, hkeep hY, he.trans heN⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 erratum 13; blueprint 02:531–541 and 21 H.22:3100–3120.
DC: Goldfish/Confirmation.lean:434–441, HonestSupport.vote.
INTENTIONAL: produce resolved honest HEAD receipts in the F-anchored gate view,
with strict original early stamps and two consumer-supplied prefix bounds.
The only timing pair is (voteTime s, gateTime s).
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_gateReceipt
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams s) (SA.gateTime p.toParams s))
    {i : Nat} {x : V} (ht : IsGateTick p c rho i x s) (B : Block)
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head s)) q ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s) = true →
      ∃ K t,
        rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
          (ofHead p ⟨.seat (.head s) q, K.root⟩) t ∧
        baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n) ∈
          (storeAt p c E rho i x).base.votes ∧
        K ∈ (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))).blocks ∧
        K.slot ≤ s ∧
        GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)))
          (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) <
            GridCO.earlyTime p.toParams.engine s ∧
        GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))) K < GridCO.earlyTime p.toParams.engine s ∧
        Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)).fg.F) K ∧ Block.Preceq B K := by
  intro q hy hawake
  let y := rho.seatOf (.base (.head s)) q
  have hsch := hE.toScheduleWellFormed
  have hx := hsch.honest_only _ (List.mem_of_getElem? ht)
  have hd : (0 : Int) < p.Δ := p.deltaPos
  have htimes : SA.voteTime p.toParams s + p.Δ = SA.earlyTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 2 * p.Δ
    ring
  have hearly : SA.earlyTime p.toParams s < SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hvote : SA.voteTime p.toParams s < SA.earlyTime p.toParams s := by
    rw [← htimes]
    exact lt_add_of_pos_right _ hd
  have hvt : ((4 * s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams s := by
    change ((4 * s + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int) + p.Δ
    push_cast
    ring
  have het : ((4 * s + 2 : Nat) : Time) * p.Δ = SA.earlyTime p.toParams s := by
    change ((4 * s + 2 : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int) + 2 * p.Δ
    push_cast
    ring
  rw [Gen.V2.Duty.LabelSyncOn_def] at hSync
  obtain ⟨dl, cut, hD, _, hlt, hbound, _, hcut, hhorizon⟩ := hSync
  have hxearly : E.awake x (SA.earlyTime p.toParams s) = true := by
    exact fgsa_awake_before_noRestart E rho hE hN x hx (SA.gateTime p.toParams s)
      (hsch.in_horizon _ (List.mem_of_getElem? ht)).2
      (hE.tick_awake x _ (List.mem_of_getElem? ht)) _
      (by change 0 ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ; positivity) hearly.le
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hsch hDelta y hy (4 * s + 1)
    (hvt ▸ (hvote.le.trans (hearly.le.trans hhorizon)))
    (by simpa only [hvt] using hawake)
  rw [hvt] at hk
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hsch hDelta x hx (4 * s + 2)
    (het ▸ (hearly.le.trans hhorizon)) (by simpa only [het] using hxearly)
  rw [het] at hj
  have hji := (V2.D.Engine.eventIndex_lt_of_time_lt hsch hj ht hearly).le
  let K := headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y)
    (SA.voteTime p.toParams s)).st s
  have hKsource : K ∈ (storeAt p c E rho k y).base.blocks := by
    have hm := headVote_stored p _ (storeBundle_postClock E rho k y
      (SA.voteTime p.toParams s)).cstore s
    change K ∈ (clock p (storeAt p c E rho k y) _).base.blocks at hm
    rwa [(clock_cumulative p _ _).2.1] at hm
  have hem : V2.D.Run.emits E rho y (ofHead p ⟨.seat (.head s) q, K.root⟩)
      (SA.voteTime p.toParams s) := by
    refine ⟨k, hk, ?_⟩
    rw [(V2.D.Run.step_tick_eq E rho hk).2]
    exact (fgsa_emits_head E rho _ y _ s q K.root).mpr
      ⟨hawake, rfl, rfl, fgsa_joinedNow_noRestart E rho hsch hN hk, rfl⟩
  have hTarget : HeadTargetAtEmission p c E rho y
      (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K := by
    refine ⟨k, s, q, hk, ?_, rfl, rfl⟩
    rw [(V2.D.Run.step_tick_eq E rho hk).2]
    exact (fgsa_emits_head E rho _ y _ s q K.root).mpr
      ⟨hawake, rfl, rfl, fgsa_joinedNow_noRestart E rho hsch hN hk, rfl⟩
  have hF := hgeom.target_floor q hy hawake K hTarget
  have hFpre : Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) K := by
    simpa only [clockPre_fg] using hF
  have hFearly := Gen.Pure.block_preceq_trans
    (gateReceipt_floor_mono E rho hN hji x) hFpre
  have hdeadline : ∀ t, t ≤ SA.voteTime p.toParams s → dl t ≤ SA.earlyTime p.toParams s := by
    intro t ht
    have hb := hbound t
    rw [max_eq_right ht, hDelta, htimes] at hb
    exact hb
  have hKearly : K ∈ (storeAt p c E rho j x).base.blocks := by
    by_cases hg : K = .genesis
    · rw [hg]
      exact ((cstoreInv_stateBefore E rho j x).baseTree _).mpr
        ⟨.genesis, (cstoreInv_stateBefore E rho j x).fg.gen, rfl⟩
    · have hm := hKsource
      change K ∈ (V2.D.Run.stateBefore E rho k y).st.base.blocks at hm
      rw [fgsa_preTick_eq_timeRead E rho hsch hN hk,
        ← Gen.V2.Duty.stateBefore_idxBefore E rho (SA.voteTime p.toParams s) hsch] at hm
      rw [← (metaInv_stateBefore E rho (V2.D.Run.idxBefore rho
        (SA.voteTime p.toParams s)) y).stampKeys] at hm
      obtain ⟨⟨b, stamp⟩, hm, he⟩ := List.mem_map.mp hm
      dsimp only at he
      subst b
      rcases fgsa_block_stamp_source E rho hN _ y K stamp hm with hgen |
        ⟨l, hl, t, o, ho, ha, _⟩
      · exact (hg hgen.1).elim
      · obtain ⟨parent, hdel, _⟩ := ha.1
        have htv := (Gen.V2.Duty.index_lt_idxBefore_iff hsch hdel _).mp hl
        have hdl := hdeadline t htv.le
        exact fgsa_gateReceipt_block_to_tick (hroots := hroots)
          E rho hE hN hDelta dl cut hD t o K ho
          (Or.inr ⟨y, hy, l, ha⟩) (hlt t) (hdl.trans (hearly.le.trans hcut))
          hx hj hdl hFearly
  have hdl := hdeadline (SA.voteTime p.toParams s) le_rfl
  have hwindow : (V2.D.Run.stateBeforeTime E rho (dl (SA.voteTime p.toParams s)) x).st.slot p ≤
      s + 1 := by
    have hn := V2.D.Engine.stateBefore_now_mono_noRestart (fgsaClock p c) E rho hsch hN
      (gateReceipt_idx_mono rho hdl) x
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho _ x),
      fgsa_clock_now p c (V2.D.Run.stateBefore E rho _ x),
      Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch,
      Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch,
      ← fgsa_preTick_eq_timeRead E rho hsch hN hj] at hn
    have hb := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c)
      E rho hsch hj x
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho j x)] at hb
    exact ((Internal.slotOf_mono (p := p) (hn.trans hb)).trans_eq
      (slotOf_offset p s (2 * p.Δ) (by omega) (by omega))).trans (Nat.le_succ _)
  have hr := fgsa_honest_head_receipt E rho hDelta hE hN hC dl cut s q K.root
    (SA.voteTime p.toParams s) y x hD hy hem hx (hdl.trans (hearly.le.trans hcut))
    (hlt _) hwindow
    (hdl.trans (hsch.in_horizon _ (List.mem_of_getElem? hj)).2)
    (fgsa_awakeOn_before_tick_noRestart E rho hE hN hj hx
      (by change 0 ≤ 4 * p.Δ * (s : Int) + p.Δ; positivity) hdl)
  have hid : V2.D.Run.idxBefore rho (dl (SA.voteTime p.toParams s)) ≤ j := by
    by_contra hn
    exact (not_lt.mpr hdl)
      ((Gen.V2.Duty.index_lt_idxBefore_iff hsch hj _).mp (Nat.lt_of_not_ge hn))
  have hvoteMem := hr.1
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch] at hvoteMem
  have hvkeep := fgsa_gateReceipt_stamps E rho hN (hid.trans hji) x s
    (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) .genesis hvoteMem
    (((cstoreInv_stateBefore E rho _ x).baseTree _).mpr
      ⟨.genesis, (cstoreInv_stateBefore E rho _ x).fg.gen, rfl⟩)
  have hKg : K ∈ (actView (clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s))).blocks := by
    apply (actView_blocks _ K).mpr
    rw [(clockPre_fields p _ _).2.1, clockPre_fg]
    exact ⟨(fgsa_store_cumulative p c E rho hN hji x).2.1.subset hKearly,
      Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K) hFpre⟩
  have hslot : K.slot ≤ s := by
    have hm := (fgsa_stateBefore_bounds E rho hsch k y).1 K hKsource
    have hn := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c)
      E rho hsch hk y
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho k y)] at hn
    exact hm.trans ((Internal.slotOf_mono (p := p) hn).trans_eq
      (slotOf_offset p s p.Δ hd.le (by omega)))
  refine ⟨K, SA.voteTime p.toParams s, hy, hem, hvkeep.1, hKg, hslot, ?_, ?_, hF,
    hgeom.covered_prefix q hy hawake K hTarget⟩
  · rw [hvkeep.2.1]
    change GridCO.stampVote (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho (dl (SA.voteTime p.toParams s))) x).st.base _ < _
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch]
    exact hr.2.trans_le hdl
  · have hvj := (fgsa_gateReceipt_stamps E rho hN hid x s _ .genesis hvoteMem
      (((cstoreInv_stateBefore E rho _ x).baseTree _).mpr
        ⟨.genesis, (cstoreInv_stateBefore E rho _ x).fg.gen, rfl⟩)).1
    rw [(fgsa_gateReceipt_stamps E rho hN hji x s _ K hvj hKearly).2.2]
    apply fgsa_gateReceipt_block_stamp_lt E rho hsch hN hj _ K hKearly
    change 0 < 4 * p.Δ * (s : Int) + 2 * p.Δ
    positivity

/-- The enabled actor, exact receiver epoch and fresh/retained object services at one gate. -/
structure GateReceiptScope (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) (s : Slot) : Prop where
  enabled : enabledGateAt p c E rho i x s
  receiverJoined : joinedAt p E rho x (s + 1) (SA.gateTime p.toParams s)
  readEpoch : V2.D.restartFree rho x (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) i
  services : ∀ q K, rho.seatOf (.base (.head s)) q ∈ rho.honest →
    HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
      (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
    Nonempty (FreshHeadService E rho s q K.root (SA.earlyTime p.toParams s) x) ∧
    TargetReceiptService E rho K (SA.earlyTime p.toParams s) x

/-- Joined selected voters and exact receiver service give local gate receipts. -/
theorem fgsa_gateReceipt_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    (_hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (s : Slot) (_hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams s) (SA.gateTime p.toParams s))
    {i : Nat} {x : V} (ht : IsGateTick p c rho i x s) (B : Block)
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B)
    (hScope : GateReceiptScope E rho i x s)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    E.awake x (SA.earlyTime p.toParams s) = true ∧
    joinedAtTime p (storeAt p c E rho i x).restartTime
      (SA.gateTime p.toParams s) = true ∧
    ∀ q : Fin p.n, rho.seatOf (.base (.head s)) q ∈ rho.honest →
      joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s) →
      ∃ K t,
        rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
          (ofHead p ⟨.seat (.head s) q, K.root⟩) t ∧
        baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n) ∈
          (storeAt p c E rho i x).base.votes ∧
        K ∈ (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))).blocks ∧
        K.slot ≤ s ∧
        GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)))
          (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) <
            GridCO.earlyTime p.toParams.engine s ∧
        GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))) K < GridCO.earlyTime p.toParams.engine s ∧
        Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)).fg.F) K ∧ Block.Preceq B K := by
  have hsch := hE.toScheduleWellFormed
  have hx := hsch.honest_only _ (List.mem_of_getElem? ht)
  have hd := p.deltaPos
  have hawakeEarly := fgsa_awake_of_joinedAt E rho x (s + 1)
    (SA.gateTime p.toParams s) (SA.earlyTime p.toParams s) hScope.receiverJoined
    (by change 0 ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ; positivity)
    (by unfold slotStartZ; push_cast; change _ ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ; linarith)
    (by change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ; linarith)
  refine ⟨hawakeEarly, fgsa_gate_joined_of_enabled E rho hScope.enabled, ?_⟩
  intro q hy hJoined
  let y := rho.seatOf (.base (.head s)) q
  have hvt : ((4 * s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams s := by
    change ((4 * s + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int) + p.Δ
    push_cast
    ring
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hsch hDelta y hy (4 * s + 1)
    (hvt ▸ ((fgsa_vote_lt_gate p s).le.trans (hsch.in_horizon _ (List.mem_of_getElem? ht)).2))
    (by simpa only [hvt] using hJoined.1)
  rw [hvt] at hk
  let K := headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y)
    (SA.voteTime p.toParams s)).st s
  have hem : ofHead p ⟨.seat (.head s) q, K.root⟩ ∈ V2.D.Run.emitsAt E rho k := by
    rw [(V2.D.Run.step_tick_eq E rho hk).2]
    exact (fgsa_emits_head E rho _ y _ s q K.root).mpr
      ⟨hJoined.1, rfl, rfl, fgsa_head_joined_of_joinedAt E rho hsch hk hJoined, rfl⟩
  have hTarget : HeadTargetAtEmission p c E rho y
      (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K :=
    ⟨k, s, q, hk, hem, rfl, rfl⟩
  obtain ⟨⟨hHeadService⟩, hBlockService⟩ := hScope.services q K hy hTarget
  have hrec := hHeadService.receipt hE hx hk hem
  have hblock := fgsa_target_receipt_on E rho hsch hroots K (SA.earlyTime p.toParams s)
    x hx hBlockService
  have hstamp := fgsa_block_stamp_before_read E rho hsch x (SA.earlyTime p.toParams s)
    (by change 0 < 4 * p.Δ * (s : Int) + 2 * p.Δ; positivity) K hblock
  have htime : SA.earlyTime p.toParams s < SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hid : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ i := by
    by_contra hn
    exact (not_lt.mpr htime.le)
      ((Gen.V2.Duty.index_lt_idxBefore_iff hsch ht _).mp (Nat.lt_of_not_ge hn))
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (SA.earlyTime p.toParams s) hsch]
    at hrec hblock hstamp
  have hkeep := fgsa_gateReceipt_stamps_on E rho hid x hScope.readEpoch s
    (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) K hrec.1 hblock
  have hF := hgeom.target_floor q hy hJoined.1 K hTarget
  have hKg : K ∈ (actView (clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s))).blocks := by
    apply (actView_blocks _ K).mpr
    rw [(clockPre_fields p _ _).2.1, clockPre_fg]
    have hFpre := hF
    rw [clockPre_fg] at hFpre
    exact ⟨(fgsa_store_durable p c E rho hid x).2.1.subset hblock,
      Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K) hFpre⟩
  have hKsource : K ∈ (storeAt p c E rho k y).base.blocks := by
    have hm := headVote_stored p _ (storeBundle_postClock E rho k y
      (SA.voteTime p.toParams s)).cstore s
    change K ∈ (clock p (storeAt p c E rho k y) _).base.blocks at hm
    rwa [(clock_cumulative p _ _).2.1] at hm
  have hslot : K.slot ≤ s := by
    have hm := (fgsa_stateBefore_bounds E rho hsch k y).1 K hKsource
    exact hm.trans ((Internal.slotOf_mono (p := p) (fgsa_preTick_now_le E rho hsch hk)).trans_eq
      (slotOf_offset p s p.Δ hd.le (by dsimp [Time] at *; omega)))
  exact ⟨K, SA.voteTime p.toParams s, hy, ⟨k, hk, hem⟩, hkeep.1, hKg, hslot,
    hkeep.2.1.trans_lt hrec.2, hkeep.2.2.trans_lt hstamp, hF,
    hgeom.covered_prefix q hy hJoined.1 K hTarget⟩

/-- Ready block service gives exact membership at an actual receiver tick.
The named body persists in durable storage after the service freeze. -/
theorem fgsa_gateReceipt_block_to_tick_on (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hS : V2.D.ScheduleWellFormed E rho)
    (hRoots : NamedReceiptRootCollisionFree p c E rho)
    (o : Obj p) (send freeze : Time) (K : Block) (ho : blockOf? p o = some K)
    {j : Nat} {x : V} {t : Time} (hx : x ∈ rho.honest)
    (hj : rho.events[j]? = some (.tick x t)) (hfreeze : freeze ≤ t)
    (hService : ReceiverService E rho o send freeze x) :
    K ∈ (storeAt p c E rho j x).base.blocks := by
  obtain ⟨s, N, rfl, rfl⟩ := gateReceipt_block_decode ho
  obtain ⟨Y, hY, he⟩ := hService.proposal hS hx hRoots
  have hid : V2.D.Run.idxBefore rho freeze ≤ j := by
    by_contra hn
    exact (not_lt.mpr hfreeze)
      ((Gen.V2.Duty.index_lt_idxBefore_iff hS hj _).mp (Nat.lt_of_not_ge hn))
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho freeze hS] at hY
  exact ((cstoreInv_stateBefore E rho j x).baseTree _).mpr
    ⟨Y, (fgsa_store_durable p c E rho hid x).1 hY, he⟩

end AvailableChain.FGSA.Run
end
