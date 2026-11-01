module
public import AvailableChainFGSAProofs.Proofs.Shared.GateReceipt
public import AvailableChainFGSAProofs.Proofs.Shared.Count
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSAClaims.Statements.ComposeStmt

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem iexact_find_kept {α : Type} [BEq α] [LawfulBEq α]
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
Blueprint 03:293–312; spec 1283–1294; plan I-EXACT, G1 step 4.
Class (iii). DC: INTENTIONAL; a kept first-receipt row keeps its vote stamp
in every later stamp list, whatever the later store clock is. -/
theorem inclusion_stampVote_of_prefix {n : Nat} {st st' : GridCO.State n .root}
    (h : st.voteStamp <+: st'.voteStamp) {o : GridCO.Wire n .root}
    (hm : o ∈ st.voteStamp.map Prod.fst) :
    GridCO.stampVote st' o = GridCO.stampVote st o := by
  unfold GridCO.stampVote
  rw [iexact_find_kept h o hm]
  cases he : st.voteStamp.find? (fun row => row.1 == o) with
  | none =>
    obtain ⟨row, hr, ho⟩ := List.mem_map.mp hm
    have hn := List.find?_eq_none.mp he row hr
    rw [ho, beq_self_eq_true] at hn
    contradiction
  | some row => rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:293–312; spec 1283–1294; plan I-EXACT, G1 step 4.
Class (iii). DC: INTENTIONAL; a kept first-receipt row keeps its block stamp
in every later stamp list, whatever the later store clock is. -/
theorem inclusion_stampBlock_of_prefix {n : Nat} {st st' : GridCO.State n .root}
    (h : st.blockStamp <+: st'.blockStamp) {K : Block}
    (hm : K ∈ st.blockStamp.map Prod.fst) :
    GridCO.stampBlock st' K = GridCO.stampBlock st K := by
  unfold GridCO.stampBlock
  rw [iexact_find_kept h K hm]
  cases he : st.blockStamp.find? (fun row => row.1 == K) with
  | none =>
    obtain ⟨row, hr, ho⟩ := List.mem_map.mp hm
    have hn := List.find?_eq_none.mp he row hr
    rw [ho, beq_self_eq_true] at hn
    contradiction
  | some row => rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:293–312; spec 1283–1294; plan I-EXACT, G1 step 4.
Class (iii). DC: INTENTIONAL; without restarts a received vote and block stay
stored with their original stamps at every later index. -/
theorem inclusion_stamps_kept (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hN : V2.D.NoRestart rho) {j i : Nat} (hji : j ≤ i) (x : V)
    (o : GridCO.Wire p.n .root) (K : Block)
    (ho : o ∈ (storeAt p c E rho j x).base.votes)
    (hK : K ∈ (storeAt p c E rho j x).base.blocks) :
    o ∈ (storeAt p c E rho i x).base.votes ∧ K ∈ (storeAt p c E rho i x).base.blocks ∧
      GridCO.stampVote (storeAt p c E rho i x).base o =
        GridCO.stampVote (storeAt p c E rho j x).base o ∧
      GridCO.stampBlock (storeAt p c E rho i x).base K =
        GridCO.stampBlock (storeAt p c E rho j x).base K := by
  have hc := fgsa_store_cumulative p c E rho hN hji x
  have hv : o ∈ (storeAt p c E rho j x).base.voteStamp.map Prod.fst := by
    change o ∈ (V2.D.Run.stateBefore E rho j x).st.base.voteStamp.map Prod.fst
    rw [fgsa_vote_stamp_keys E rho j x]
    exact ho
  have hb : K ∈ (storeAt p c E rho j x).base.blockStamp.map Prod.fst := by
    change K ∈ (V2.D.Run.stateBefore E rho j x).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho j x).«meta».stampKeys]
    exact hK
  refine ⟨?_, hc.2.1.subset hK, inclusion_stampVote_of_prefix hc.2.2.2.1 hv,
    inclusion_stampBlock_of_prefix hc.2.2.1 hb⟩
  change o ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes
  rw [← fgsa_vote_stamp_keys E rho i x]
  obtain ⟨row, hr, he⟩ := List.mem_map.mp hv
  exact List.mem_map.mpr ⟨row, hc.2.2.2.1.subset hr, he⟩

theorem inclusion_stamps_kept_on (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
     {j i : Nat} (hji : j ≤ i) (x : V) (hRF : V2.D.restartFree rho x j i)
    (o : GridCO.Wire p.n .root) (K : Block)
    (ho : o ∈ (storeAt p c E rho j x).base.votes)
    (hK : K ∈ (storeAt p c E rho j x).base.blocks) :
    o ∈ (storeAt p c E rho i x).base.votes ∧ K ∈ (storeAt p c E rho i x).base.blocks ∧
      GridCO.stampVote (storeAt p c E rho i x).base o =
        GridCO.stampVote (storeAt p c E rho j x).base o ∧
      GridCO.stampBlock (storeAt p c E rho i x).base K =
        GridCO.stampBlock (storeAt p c E rho j x).base K := by
  have hc := fgsa_store_cumulative_on p c E rho hji x hRF
  have hv : o ∈ (storeAt p c E rho j x).base.voteStamp.map Prod.fst := by
    change o ∈ (V2.D.Run.stateBefore E rho j x).st.base.voteStamp.map Prod.fst
    rw [fgsa_vote_stamp_keys E rho j x]
    exact ho
  have hb : K ∈ (storeAt p c E rho j x).base.blockStamp.map Prod.fst := by
    change K ∈ (V2.D.Run.stateBefore E rho j x).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho j x).«meta».stampKeys]
    exact hK
  refine ⟨?_, hc.2.1.subset hK, inclusion_stampVote_of_prefix hc.2.2.2.1 hv,
    inclusion_stampBlock_of_prefix hc.2.2.1 hb⟩
  change o ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes
  rw [← fgsa_vote_stamp_keys E rho i x]
  obtain ⟨row, hr, he⟩ := List.mem_map.mp hv
  exact List.mem_map.mpr ⟨row, hc.2.2.2.1.subset hr, he⟩

omit [DecidableEq V] in
private theorem iexact_idx_mono (rho : V2.D.Run V (fgsa p c)) :
    Monotone (V2.D.Run.idxBefore rho) := by
  intro a b hab
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true
    (lt_of_lt_of_le (of_decide_eq_true he) hab))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03:293–312, 21 H.22:3100–3120; spec 1240–1243, 1283–1294;
plan I-EXACT, G1 step 4. Class (iii). DC: INTENTIONAL; the gate-receipt
argument of fgsa_gateReceipt, read at the early tick e_r of any honest
reader instead of at the gate d_r. The emitted HEAD is the scheduled read.
The reader floor bound is an explicit input. The receiver has the scheduled early tick. -/
theorem inclusion_head_receipt_early_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (r : Slot)
    {j : Nat} {x : V} (hj : rho.events[j]? = some (.tick x (SA.earlyTime p.toParams r)))
    (q : Fin p.n) (_hy : rho.seatOf (.base (.head r)) q ∈ rho.honest)
    (hJoined : joinedAt p E rho (rho.seatOf (.base (.head r)) q) r
      (SA.voteTime p.toParams r))
    {k : Nat} (hk : rho.events[k]? =
      some (.tick (rho.seatOf (.base (.head r)) q) (SA.voteTime p.toParams r)))
    (K : Block) (hK : headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k
      (rho.seatOf (.base (.head r)) q)) (SA.voteTime p.toParams r)).st r = K)
    (hHeadService : FreshHeadService E rho r q K.root (SA.earlyTime p.toParams r) x)
    (hBlockService : TargetReceiptService E rho K (SA.earlyTime p.toParams r) x)
    (hReadEpoch : V2.D.restartFree rho x
      (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams r)) j)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    V2.D.Run.emits E rho (rho.seatOf (.base (.head r)) q) (ofHead p ⟨.seat (.head r) q, K.root⟩)
      (SA.voteTime p.toParams r) ∧
    baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) ∈ (storeAt p c E rho j x).base.votes ∧
    GridCO.stampVote (storeAt p c E rho j x).base
      (baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n)) < SA.earlyTime p.toParams r ∧
    K ∈ (storeAt p c E rho j x).base.blocks ∧
    GridCO.stampBlock (storeAt p c E rho j x).base K < SA.earlyTime p.toParams r ∧
    K.slot ≤ r := by
  let y := rho.seatOf (.base (.head r)) q
  have hsch := hE.toScheduleWellFormed
  have hx := hsch.honest_only _ (List.mem_of_getElem? hj)
  have hem : ofHead p ⟨.seat (.head r) q, K.root⟩ ∈ V2.D.Run.emitsAt E rho k := by
    rw [(V2.D.Run.step_tick_eq E rho hk).2]
    exact (fgsa_emits_head E rho _ y _ r q K.root).mpr
      ⟨hJoined.1, rfl, rfl, fgsa_head_joined_of_joinedAt E rho hsch hk hJoined,
        congrArg Block.root hK.symm⟩
  have hrec := hHeadService.receipt hE hx hk hem
  have hblock := fgsa_target_receipt_on E rho hsch hroots K (SA.earlyTime p.toParams r)
    x hx hBlockService
  have hstamp := fgsa_block_stamp_before_read E rho hsch x (SA.earlyTime p.toParams r)
    (by change 0 < 4 * p.Δ * (r : Int) + 2 * p.Δ; have hd := p.deltaPos; positivity) K hblock
  have hid : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams r) ≤ j := by
    by_contra hn
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hsch hj _).mp (Nat.lt_of_not_ge hn)
    exact (lt_irrefl _ ht).elim
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (SA.earlyTime p.toParams r) hsch]
    at hrec hblock hstamp
  have hkeep := inclusion_stamps_kept_on E rho hid x hReadEpoch
    (baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n)) K hrec.1 hblock
  have hKsource : K ∈ (storeAt p c E rho k y).base.blocks := by
    have hm := headVote_stored p _ (storeBundle_postClock E rho k y
      (SA.voteTime p.toParams r)).cstore r
    rw [hK] at hm
    change K ∈ (clock p (storeAt p c E rho k y) _).base.blocks at hm
    rwa [(clock_cumulative p _ _).2.1] at hm
  have hslot : K.slot ≤ r := by
    have hm := (fgsa_stateBefore_bounds E rho hsch k y).1 K hKsource
    have hn := fgsa_preTick_now_le E rho hsch hk
    exact hm.trans ((Internal.slotOf_mono (p := p) hn).trans_eq
      (slotOf_offset p r p.Δ p.deltaPos.le (by have hd := p.deltaPos; dsimp [Time] at *; omega)))
  exact ⟨⟨k, hk, hem⟩, hkeep.1, hkeep.2.2.1.trans_lt hrec.2,
    hkeep.2.1, hkeep.2.2.2.trans_lt hstamp, hslot⟩

theorem inclusion_head_receipt_early
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (r : Slot)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams r) (SA.earlyTime p.toParams r))
    {j : Nat} {x : V} (hj : rho.events[j]? = some (.tick x (SA.earlyTime p.toParams r)))
    (q : Fin p.n) (hy : rho.seatOf (.base (.head r)) q ∈ rho.honest)
    (hawake : E.awake (rho.seatOf (.base (.head r)) q) (SA.voteTime p.toParams r) = true)
    {k : Nat} (hk : rho.events[k]? =
      some (.tick (rho.seatOf (.base (.head r)) q) (SA.voteTime p.toParams r)))
    (K : Block) (hK : headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k
      (rho.seatOf (.base (.head r)) q)) (SA.voteTime p.toParams r)).st r = K)
    (hF : Block.Preceq (eraseFG (storeAt p c E rho j x).fg.F) K)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    V2.D.Run.emits E rho (rho.seatOf (.base (.head r)) q) (ofHead p ⟨.seat (.head r) q, K.root⟩)
      (SA.voteTime p.toParams r) ∧
    baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) ∈ (storeAt p c E rho j x).base.votes ∧
    GridCO.stampVote (storeAt p c E rho j x).base
      (baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n)) < SA.earlyTime p.toParams r ∧
    K ∈ (storeAt p c E rho j x).base.blocks ∧
    GridCO.stampBlock (storeAt p c E rho j x).base K < SA.earlyTime p.toParams r ∧
    K.slot ≤ r := by
  let y := rho.seatOf (.base (.head r)) q
  have hsch := hE.toScheduleWellFormed
  have hx := hsch.honest_only _ (List.mem_of_getElem? hj)
  have hd : (0 : Int) < p.Δ := p.deltaPos
  have htimes : SA.voteTime p.toParams r + p.Δ = SA.earlyTime p.toParams r := by
    change 4 * p.Δ * (r : Int) + p.Δ + p.Δ = 4 * p.Δ * (r : Int) + 2 * p.Δ
    ring
  rw [Gen.V2.Duty.LabelSyncOn_def] at hSync
  obtain ⟨dl, cut, hD, _, hlt, hbound, _, hcut, _⟩ := hSync
  have hKsource : K ∈ (storeAt p c E rho k y).base.blocks := by
    have hm := headVote_stored p _ (storeBundle_postClock E rho k y
      (SA.voteTime p.toParams r)).cstore r
    rw [hK] at hm
    change K ∈ (clock p (storeAt p c E rho k y) _).base.blocks at hm
    rwa [(clock_cumulative p _ _).2.1] at hm
  have hem : V2.D.Run.emits E rho y (ofHead p ⟨.seat (.head r) q, K.root⟩)
      (SA.voteTime p.toParams r) := by
    refine ⟨k, hk, ?_⟩
    rw [(V2.D.Run.step_tick_eq E rho hk).2]
    exact (fgsa_emits_head E rho _ y _ r q K.root).mpr
      ⟨hawake, rfl, rfl, fgsa_joinedNow_noRestart E rho hsch hN hk,
        congrArg Block.root hK.symm⟩
  have hdeadline : ∀ t, t ≤ SA.voteTime p.toParams r → dl t ≤ SA.earlyTime p.toParams r := by
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
        ← Gen.V2.Duty.stateBefore_idxBefore E rho (SA.voteTime p.toParams r) hsch] at hm
      rw [← (metaInv_stateBefore E rho (V2.D.Run.idxBefore rho
        (SA.voteTime p.toParams r)) y).stampKeys] at hm
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
          (Or.inr ⟨y, hy, l, ha⟩) (hlt t) (hdl.trans hcut) hx hj hdl hF
  have hdl := hdeadline (SA.voteTime p.toParams r) le_rfl
  have hwindow : (V2.D.Run.stateBeforeTime E rho (dl (SA.voteTime p.toParams r)) x).st.slot p ≤
      r + 1 := by
    have hn := V2.D.Engine.stateBefore_now_mono_noRestart (fgsaClock p c) E rho hsch hN
      (iexact_idx_mono rho hdl) x
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
      (slotOf_offset p r (2 * p.Δ) (by omega) (by omega))).trans (Nat.le_succ _)
  have hr := fgsa_honest_head_receipt E rho hDelta hE hN hC dl cut r q K.root
    (SA.voteTime p.toParams r) y x hD hy hem hx (hdl.trans hcut) (hlt _) hwindow
    (hdl.trans (hsch.in_horizon _ (List.mem_of_getElem? hj)).2)
    (fgsa_awakeOn_before_tick_noRestart E rho hE hN hj hx
      (by change 0 ≤ 4 * p.Δ * (r : Int) + p.Δ; positivity) hdl)
  have hid : V2.D.Run.idxBefore rho (dl (SA.voteTime p.toParams r)) ≤ j := by
    by_contra hn
    exact (not_lt.mpr hdl)
      ((Gen.V2.Duty.index_lt_idxBefore_iff hsch hj _).mp (Nat.lt_of_not_ge hn))
  have hvoteMem := hr.1
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch] at hvoteMem
  have hkeep := inclusion_stamps_kept E rho hN hid x
    (baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n)) .genesis hvoteMem
    (((cstoreInv_stateBefore E rho _ x).baseTree _).mpr
      ⟨.genesis, (cstoreInv_stateBefore E rho _ x).fg.gen, rfl⟩)
  have hslot : K.slot ≤ r := by
    have hm := (fgsa_stateBefore_bounds E rho hsch k y).1 K hKsource
    have hn := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c)
      E rho hsch hk y
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho k y)] at hn
    exact hm.trans ((Internal.slotOf_mono (p := p) hn).trans_eq
      (slotOf_offset p r p.Δ hd.le (by omega)))
  refine ⟨hem, hkeep.1, ?_, hKearly, ?_, hslot⟩
  · rw [hkeep.2.2.1]
    change GridCO.stampVote (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho (dl (SA.voteTime p.toParams r))) x).st.base _ < _
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch]
    exact hr.2.trans_le hdl
  · apply fgsa_gateReceipt_block_stamp_lt E rho hsch hN hj _ K hKearly
    change 0 < 4 * p.Δ * (r : Int) + 2 * p.Δ
    positivity

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:293–312; spec 1240–1243; plan I-EXACT, G1 step 4.
Class (iii). DC: INTENTIONAL; one stored vote per seat excludes a cap. -/
theorem inclusion_no_equivocation {n : Nat} (L : List (GridCO.Wire n .root)) (k : Fin n)
    (a : GridCO.Wire n .root) (h : ∀ o ∈ L, GridCO.headSeat? o = some k → o = a) :
    GridCO.equivocates L k = false := by
  cases he : GridCO.equivocates L k with
  | false => rfl
  | true =>
    obtain ⟨u, hu, w, hw, hn, hku, hkw⟩ := (Gen.AC.Root.cap_pair L k).mp he
    exact (hn ((h u hu hku).trans (h w hw hkw).symm)).elim

omit [DecidableEq V] in
open scoped Classical in
private theorem hygiene_joinedHonest_unfold (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (t : Time) :
    joinedHonest p E rho t = rho.honest.filter (fun v => joinedAt p E rho v (slotAt p t) t) := rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 02:531–541, 03:293–312; spec 1240–1243; plan I-EXACT, G1 step 4.
Class (iii). DC: INTENTIONAL; exactService_participation_of_card without the
fast threshold. The fresh HEAD seat map is a bijection. -/
theorem inclusion_joined_head_seats [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (r : Slot)
    (hbatch : Gen.Pure.Batch (joinedHonest p E rho (SA.voteTime p.toParams r)).card
      (Gen.V2.Duty.faulty rho).card) :
    ∃ H : Finset (Fin p.n),
      (∀ q, q ∈ H ↔ rho.seatOf (.base (.head r)) q ∈ rho.honest ∧
        joinedAt p E rho (rho.seatOf (.base (.head r)) q) r (SA.voteTime p.toParams r)) ∧
      Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card := by
  classical
  let H := Finset.univ.filter (fun q : Fin p.n =>
    rho.seatOf (.base (.head r)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head r)) q) r (SA.voteTime p.toParams r))
  have hH (q : Fin p.n) : q ∈ H ↔ rho.seatOf (.base (.head r)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head r)) q) r (SA.voteTime p.toParams r) := by
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
  have hbij : Function.Bijective (fun q : Fin p.n => rho.seatOf (.base (.head r)) q) :=
    hC (.base (.head r)) trivial
  have himage : H.image (rho.seatOf (.base (.head r))) =
      joinedHonest p E rho (SA.voteTime p.toParams r) := by
    ext y
    have hs : slotAt p (SA.voteTime p.toParams r) = r :=
      slotOf_offset p r p.Δ p.deltaPos.le (by have hd := p.deltaPos; dsimp [Time] at *; omega)
    simp only [hygiene_joinedHonest_unfold E rho, hs, Finset.mem_filter]
    constructor
    · intro hy
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
      exact (hH q).mp hq
    · intro hy
      obtain ⟨q, rfl⟩ := hbij.2 y
      exact Finset.mem_image.mpr ⟨q, (hH q).mpr hy, rfl⟩
  have hc : H.card = (joinedHonest p E rho (SA.voteTime p.toParams r)).card :=
    (Finset.card_image_of_injective H hbij.1).symm.trans (congrArg Finset.card himage)
  exact ⟨H, hH, hc ▸ hbatch⟩

theorem inclusion_head_seats [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (r : Slot)
    (hbatch : Gen.Pure.Batch (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams r)).card
      (Gen.V2.Duty.faulty rho).card) :
    ∃ H : Finset (Fin p.n),
      (∀ q, q ∈ H ↔ rho.seatOf (.base (.head r)) q ∈ rho.honest ∧
        E.awake (rho.seatOf (.base (.head r)) q) (SA.voteTime p.toParams r) = true) ∧
      Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card := by
  classical
  let H := Finset.univ.filter (fun q : Fin p.n =>
    rho.seatOf (.base (.head r)) q ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head r)) q) (SA.voteTime p.toParams r) = true)
  have hH (q : Fin p.n) : q ∈ H ↔ rho.seatOf (.base (.head r)) q ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head r)) q) (SA.voteTime p.toParams r) = true := by
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
  have hbij : Function.Bijective (fun q : Fin p.n => rho.seatOf (.base (.head r)) q) :=
    hC (.base (.head r)) trivial
  have himage : H.image (rho.seatOf (.base (.head r))) =
      Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams r) := by
    ext y
    rw [Gen.V2.Duty.awakeHonest_def, Finset.mem_filter]
    constructor
    · intro hy
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
      exact (hH q).mp hq
    · intro hy
      obtain ⟨q, rfl⟩ := hbij.2 y
      exact Finset.mem_image.mpr ⟨q, (hH q).mpr hy, rfl⟩
  have hc : H.card = (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams r)).card :=
    (Finset.card_image_of_injective H hbij.1).symm.trans (congrArg Finset.card himage)
  exact ⟨H, hH, hc ▸ hbatch⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 02:531–541; spec 1240–1243, 1283–1294; plan I-EXACT, G1 step 4.
Class (iii). DC: Goldfish/Confirmation:494,508; fgsa_late_rest_bound for any
pool whose seats have stored label-r witnesses. Honest stored seats were awake. -/
theorem inclusion_rest_bound [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (hE : V2.D.ExecutionValid E rho)
    (r : Slot) (H : Finset (Fin p.n))
    (hH : ∀ k, rho.seatOf (.base (.head r)) k ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head r)) k) (SA.voteTime p.toParams r) = true → k ∈ H)
    (L : List (GridCO.Wire p.n .root))
    (hL : ∀ o ∈ L, ∀ k, GridCO.headSeat? o = some k →
      ∃ i x, ∃ o' ∈ (storeAt p c E rho i x).base.votes,
        GridCO.headLabel? o' = some r ∧ GridCO.headSeat? o' = some k) :
    ((GridCO.seats p.n L).toFinset \ H).card ≤ (Gen.V2.Duty.faulty rho).card := by
  apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head r)))
  · intro k hk
    obtain ⟨hl, hn⟩ := Finset.mem_sdiff.mp hk
    rw [Gen.V2.Duty.faulty_def]
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hh
    apply hn (hH k hh ?_)
    obtain ⟨o, ho, hs⟩ := (Gen.AC.Root.vote_pool_mem_seats _ k).mp hl
    obtain ⟨i, x, o', ho', hl', hs'⟩ := hL o ho k hs
    exact fgsa_stored_honest_head_awake E rho hE i x r k o' ho' hl' hs' hh
  · intro k _ j _ he
    exact (hC (.base (.head r)) trivial).injective he

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Paper 22:1228–1234,1251–1253,1719–1722: the full action pool at label qR+1 is a
walk
batch for every Q below all honest label HEADs and above the reader's F; the action head
is the walk on these pools.
DC: Goldfish/Confirmation.lean:494,508, honest/rest partition with unique honest votes.
INTENTIONAL: FG-SA reads the post-clock action store; every honest HEAD seat is awake.
The admission is inclusion_head_receipt_early at earlyTime (qR+1) = actionTime q. -/
theorem fgsa_action_walk_batch [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hb : Base₂ p c E rho) (q : Nat)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams (q * p.R + 1)) (SA.earlyTime p.toParams (q * p.R + 1)))
    (hJoined : ∀ y ∈ rho.honest,
      joinedAt p E rho y (q * p.R + 1) (SA.voteTime p.toParams (q * p.R + 1)))
    (hbatch : Gen.Pure.Batch
      (joinedHonest p E rho (SA.voteTime p.toParams (q * p.R + 1))).card
      (Gen.V2.Duty.faulty rho).card)
    (Q : Block) (x : V) (nd : Node p)
    (hnd : postClock E rho x (p.actionTime q) = some nd)
    (hcover : ∀ y H, y ∈ rho.honest → headAtLabel p c E rho y (q * p.R + 1) = some H →
      Block.Preceq Q H)
    (hFQ : Block.Preceq (eraseFG nd.st.fg.F) Q)
    (hReadEpoch : ∀ j, rho.events[j]? = some (.tick x (p.actionTime q)) →
      V2.D.restartFree rho x (V2.D.Run.idxBefore rho (p.actionTime q)) j)
    (hServices : ∀ a K, rho.seatOf (.base (.head (q * p.R + 1))) a ∈ rho.honest →
      headAtLabel p c E rho (rho.seatOf (.base (.head (q * p.R + 1))) a)
        (q * p.R + 1) = some K →
      Nonempty (FreshHeadService E rho (q * p.R + 1) a K.root (p.actionTime q) x) ∧
      TargetReceiptService E rho K (p.actionTime q) x) :
    let s := q * p.R + 1
    let raw := GridCO.votesAt nd.st.base s
    let support := raw.filter (fun o => match GridCO.resolvedHead? (FGSA.actView nd.st) o with
      | some H => decide (H.slot ≤ s)
      | none => false)
    let seats : Finset (Fin p.n) := by
      classical
      exact Finset.univ.filter (fun k : Fin p.n => rho.seatOf (.base (.head s)) k ∈ rho.honest)
    Gen.Pure.Batch seats.card (Gen.V2.Duty.faulty rho).card ∧
    WalkBatch p c rho nd.st s raw support Q seats (Gen.V2.Duty.faulty rho).card ∧
    FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support := by
  intro s raw support seats
  have hseat : ∀ a, a ∈ seats ↔ rho.seatOf (.base (.head s)) a ∈ rho.honest := by
    intro a
    simp only [seats, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsch := hb.valid.toScheduleWellFormed
  have hd : (0 : Int) < p.Δ := p.deltaPos
  have hearly : SA.earlyTime p.toParams s = p.actionTime q := by
    change 4 * p.Δ * ((q * p.R + 1 : Nat) : Int) + 2 * p.Δ =
      4 * p.Δ * ((q * p.R : Nat) : Int) + 6 * p.Δ
    push_cast
    ring
  have hvthor : SA.voteTime p.toParams s ≤ rho.horizon := by
    obtain ⟨_, _, _, _, _, _, hvd, _, hdt⟩ := hSync
    have := hb.delta
    linarith
  obtain ⟨j, hj, hclock⟩ : ∃ j, rho.events[j]? = some (.tick x (p.actionTime q)) ∧
      (fgsa p c).clock (V2.D.Run.stateBefore E rho j x) (p.actionTime q) = nd := by
    rw [postClock_def, preTick_def] at hnd
    cases hi : V2.D.Run.tickIdx? rho x (p.actionTime q) with
    | none => rw [hi] at hnd; cases hnd
    | some j =>
      rw [hi] at hnd
      exact ⟨j, V2.D.Run.tickIdx?_spec hi, Option.some.inj hnd⟩
  have hjE : rho.events[j]? = some (.tick x (SA.earlyTime p.toParams s)) := by
    rw [hearly]
    exact hj
  have hvotes : nd.st.base.votes = (storeAt p c E rho j x).base.votes := by
    rw [← hclock]
    exact (clock_vn _ _).1
  have hblocks : nd.st.base.blocks = (storeAt p c E rho j x).base.blocks := by
    rw [← hclock]
    exact clock_base_blocks p _ _
  have hrec : ∀ a ∈ seats, ∃ K, V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) a)
        (ofHead p ⟨.seat (.head s) a, K.root⟩) (SA.voteTime p.toParams s) ∧
      baseVote (⟨.seat (.head s) a, K.root⟩ : HeadWire p.n) ∈ raw ∧
      K ∈ nd.st.base.blocks ∧ K ∈ (FGSA.actView nd.st).blocks ∧ K.slot ≤ s ∧
      Block.Preceq Q K := by
    intro a ha
    have hy := (hseat a).mp ha
    have hJoin := hJoined _ hy
    have hawake := hJoin.1
    have hvt : ((4 * s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams s := by
      change ((4 * s + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int) + p.Δ
      push_cast
      ring
    obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hsch hb.delta _ hy (4 * s + 1) (hvt ▸ hvthor)
      (by simpa only [hvt] using hawake)
    rw [hvt] at hk
    let K := FGSA.headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k
      (rho.seatOf (.base (.head s)) a)) (SA.voteTime p.toParams s)).st s
    have hHL : headAtLabel p c E rho (rho.seatOf (.base (.head s)) a) s = some K := by
      change (postClock E rho _ (SA.voteTime p.toParams s)).map
        (fun nd => FGSA.headVote p nd.st s) = some K
      rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hsch hk]
      rfl
    have hQK := hcover _ K hy hHL
    have hFK := Gen.Pure.block_preceq_trans hFQ hQK
    obtain ⟨⟨hHeadService⟩, hBlockService⟩ := hServices a K hy hHL
    rw [← hearly] at hHeadService hBlockService
    have hEpoch := hReadEpoch j hj
    rw [← hearly] at hEpoch
    obtain ⟨hem, hv, _, hKb, _, hslot⟩ :=
      inclusion_head_receipt_early_on (hroots := hb.receiptIdealization)
        E rho hb.valid s hjE a hy hJoin hk K rfl hHeadService hBlockService hEpoch
    have hKn : K ∈ nd.st.base.blocks := hblocks ▸ hKb
    have hKact : K ∈ (FGSA.actView nd.st).blocks := (actView_blocks _ K).mpr
      ⟨hKn, Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K) hFK⟩
    refine ⟨K, hem, List.mem_filter.mpr ⟨hvotes ▸ hv, by exact beq_self_eq_true _⟩,
      hKn, hKact, hslot, hQK⟩
  have hslot : nd.st.slot p = s := by
    rw [← hclock]
    exact (fgsa_action_slot_round (c := c) (V2.D.Run.stateBefore E rho j x) q).1
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨H, hH, hBH⟩ := inclusion_joined_head_seats E rho hb.cstar s hbatch
    have hsub : H ⊆ seats := fun a ha => (hseat a).mpr ((hH a).mp ha).1
    exact ⟨lt_of_lt_of_le hBH.lt (Finset.card_le_card hsub)⟩
  · intro o ho
    exact (List.mem_filter.mp ho).1
  · intro o ho
    exact beq_iff_eq.mp (List.mem_filter.mp ho).2
  · intro a ha
    obtain ⟨K, _, hraw, hKn, hKact, hslot, hQK⟩ := hrec a ha
    have hInv : CStoreInv p nd.st := by
      rw [← hclock]
      exact cstoreInv_clock p _ (cstoreInv_stateBefore E rho j x) _
    have hdomain : nd.st.base.headDomain = none := by
      rw [← hclock]
      exact base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho j x))
    have hres := actView_resolve_target p nd.st hInv hdomain
      (baseVote ⟨.seat (.head s) a, K.root⟩) hKact rfl
    refine ⟨(hseat a).mp ha, _, List.mem_filter.mpr ⟨hraw, ?_⟩, hraw, rfl, K,
      base_resolve_target p nd.st hInv hdomain _ hKn rfl, hslot, hQK⟩
    change (match GridCO.resolvedHead? (actView nd.st) _ with
      | some H => decide (H.slot ≤ s) | none => false) = true
    rw [hres]
    exact decide_eq_true hslot
  · exact inclusion_rest_bound E rho hb.cstar hb.valid s seats
      (fun k hh _ => (hseat k).mpr hh) raw
      (fun o ho k hk => ⟨j, x, o, hvotes ▸ (List.mem_filter.mp ho).1,
        beq_iff_eq.mp (List.mem_filter.mp ho).2, hk⟩)
  · intro a ha
    obtain ⟨K, hem, _, _, _, _, _⟩ := hrec a ha
    refine inclusion_no_equivocation raw a (baseVote ⟨.seat (.head s) a, K.root⟩) ?_
    intro o ho hk
    exact fgsa_honest_head_eq_of_stored E rho hb.valid j x s a K.root _ ((hseat a).mp ha) hem o
      (hvotes ▸ (List.mem_filter.mp ho).1) (beq_iff_eq.mp (List.mem_filter.mp ho).2) hk
  · dsimp only [FGSA.fgHead]
    rw [hslot]
    rfl

/-- Explicit legacy action-batch form. Awake voters need NoRestart for their duty guard. -/
theorem fgsa_action_walk_batch_legacy [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hb : Base₂ p c E rho) (hN : V2.D.NoRestart rho) (q : Nat)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams (q * p.R + 1)) (SA.earlyTime p.toParams (q * p.R + 1)))
    (hawake : ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams (q * p.R + 1)) = true)
    (hbatch : Gen.Pure.Batch
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams (q * p.R + 1))).card
      (Gen.V2.Duty.faulty rho).card)
    (Q : Block) (x : V) (nd : Node p)
    (hnd : postClock E rho x (p.actionTime q) = some nd)
    (hcover : ∀ y H, y ∈ rho.honest → headAtLabel p c E rho y (q * p.R + 1) = some H →
      Block.Preceq Q H)
    (hFQ : Block.Preceq (eraseFG nd.st.fg.F) Q) :
    let s := q * p.R + 1
    let raw := GridCO.votesAt nd.st.base s
    let support := raw.filter (fun o => match GridCO.resolvedHead? (FGSA.actView nd.st) o with
      | some H => decide (H.slot ≤ s)
      | none => false)
    let seats : Finset (Fin p.n) := by
      classical
      exact Finset.univ.filter (fun k : Fin p.n => rho.seatOf (.base (.head s)) k ∈ rho.honest)
    Gen.Pure.Batch seats.card (Gen.V2.Duty.faulty rho).card ∧
    WalkBatch p c rho nd.st s raw support Q seats (Gen.V2.Duty.faulty rho).card ∧
    FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support := by
  intro s raw support seats
  have hseat : ∀ a, a ∈ seats ↔ rho.seatOf (.base (.head s)) a ∈ rho.honest := by
    intro a
    simp only [seats, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsch := hb.valid.toScheduleWellFormed
  have hd : (0 : Int) < p.Δ := p.deltaPos
  have hearly : SA.earlyTime p.toParams s = p.actionTime q := by
    change 4 * p.Δ * ((q * p.R + 1 : Nat) : Int) + 2 * p.Δ =
      4 * p.Δ * ((q * p.R : Nat) : Int) + 6 * p.Δ
    push_cast
    ring
  have hvthor : SA.voteTime p.toParams s ≤ rho.horizon := by
    obtain ⟨_, _, _, _, _, _, hvd, _, hdt⟩ := hSync
    have := hb.delta
    linarith
  obtain ⟨j, hj, hclock⟩ : ∃ j, rho.events[j]? = some (.tick x (p.actionTime q)) ∧
      (fgsa p c).clock (V2.D.Run.stateBefore E rho j x) (p.actionTime q) = nd := by
    rw [postClock_def, preTick_def] at hnd
    cases hi : V2.D.Run.tickIdx? rho x (p.actionTime q) with
    | none => rw [hi] at hnd; cases hnd
    | some j =>
      rw [hi] at hnd
      exact ⟨j, V2.D.Run.tickIdx?_spec hi, Option.some.inj hnd⟩
  have hjE : rho.events[j]? = some (.tick x (SA.earlyTime p.toParams s)) := by
    rw [hearly]
    exact hj
  have hvotes : nd.st.base.votes = (storeAt p c E rho j x).base.votes := by
    rw [← hclock]
    exact (clock_vn _ _).1
  have hblocks : nd.st.base.blocks = (storeAt p c E rho j x).base.blocks := by
    rw [← hclock]
    exact clock_base_blocks p _ _
  have hfg : nd.st.fg = (storeAt p c E rho j x).fg := by
    rw [← hclock]
    exact clock_fg p _ _
  have hrec : ∀ a ∈ seats, ∃ K, V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) a)
        (ofHead p ⟨.seat (.head s) a, K.root⟩) (SA.voteTime p.toParams s) ∧
      baseVote (⟨.seat (.head s) a, K.root⟩ : HeadWire p.n) ∈ raw ∧
      K ∈ nd.st.base.blocks ∧ K ∈ (FGSA.actView nd.st).blocks ∧ K.slot ≤ s ∧
      Block.Preceq Q K := by
    intro a ha
    have hy := (hseat a).mp ha
    have hawake := hawake _ hy
    have hvt : ((4 * s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams s := by
      change ((4 * s + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int) + p.Δ
      push_cast
      ring
    obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hsch hb.delta _ hy (4 * s + 1) (hvt ▸ hvthor)
      (by simpa only [hvt] using hawake)
    rw [hvt] at hk
    let K := FGSA.headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k
      (rho.seatOf (.base (.head s)) a)) (SA.voteTime p.toParams s)).st s
    have hHL : headAtLabel p c E rho (rho.seatOf (.base (.head s)) a) s = some K := by
      change (postClock E rho _ (SA.voteTime p.toParams s)).map
        (fun nd => FGSA.headVote p nd.st s) = some K
      rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hsch hk]
      rfl
    have hQK := hcover _ K hy hHL
    have hFK : Block.Preceq (eraseFG nd.st.fg.F) K := Gen.Pure.block_preceq_trans hFQ hQK
    obtain ⟨hem, hv, _, hKb, _, hslot⟩ :=
      inclusion_head_receipt_early (hroots := hb.receiptIdealization)
      E rho hb.valid
      hN hb.delta hb.cstar s hSync hjE a hy hawake hk K rfl (by rwa [← hfg])
    have hKn : K ∈ nd.st.base.blocks := hblocks ▸ hKb
    have hKact : K ∈ (FGSA.actView nd.st).blocks := (actView_blocks _ K).mpr
      ⟨hKn, Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K) hFK⟩
    refine ⟨K, hem, List.mem_filter.mpr ⟨hvotes ▸ hv, by exact beq_self_eq_true _⟩,
      hKn, hKact, hslot, hQK⟩
  have hslot : nd.st.slot p = s := by
    rw [← hclock]
    exact (fgsa_action_slot_round (c := c) (V2.D.Run.stateBefore E rho j x) q).1
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨H, hH, hBH⟩ := inclusion_head_seats E rho hb.cstar s hbatch
    have hsub : H ⊆ seats := fun a ha => (hseat a).mpr ((hH a).mp ha).1
    exact ⟨lt_of_lt_of_le hBH.lt (Finset.card_le_card hsub)⟩
  · intro o ho
    exact (List.mem_filter.mp ho).1
  · intro o ho
    exact beq_iff_eq.mp (List.mem_filter.mp ho).2
  · intro a ha
    obtain ⟨K, _, hraw, hKn, hKact, hslot, hQK⟩ := hrec a ha
    have hInv : CStoreInv p nd.st := by
      rw [← hclock]
      exact cstoreInv_clock p _ (cstoreInv_stateBefore E rho j x) _
    have hdomain : nd.st.base.headDomain = none := by
      rw [← hclock]
      exact base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho j x))
    have hres := actView_resolve_target p nd.st hInv hdomain
      (baseVote ⟨.seat (.head s) a, K.root⟩) hKact rfl
    refine ⟨(hseat a).mp ha, _, List.mem_filter.mpr ⟨hraw, ?_⟩, hraw, rfl, K,
      base_resolve_target p nd.st hInv hdomain _ hKn rfl, hslot, hQK⟩
    change (match GridCO.resolvedHead? (actView nd.st) _ with
      | some H => decide (H.slot ≤ s) | none => false) = true
    rw [hres]
    exact decide_eq_true hslot
  · exact inclusion_rest_bound E rho hb.cstar hb.valid s seats
      (fun k hh _ => (hseat k).mpr hh) raw
      (fun o ho k hk => ⟨j, x, o, hvotes ▸ (List.mem_filter.mp ho).1,
        beq_iff_eq.mp (List.mem_filter.mp ho).2, hk⟩)
  · intro a ha
    obtain ⟨K, hem, _, _, _, _, _⟩ := hrec a ha
    refine inclusion_no_equivocation raw a (baseVote ⟨.seat (.head s) a, K.root⟩) ?_
    intro o ho hk
    exact fgsa_honest_head_eq_of_stored E rho hb.valid j x s a K.root _ ((hseat a).mp ha) hem o
      (hvotes ▸ (List.mem_filter.mp ho).1) (beq_iff_eq.mp (List.mem_filter.mp ho).2) hk
  · dsimp only [FGSA.fgHead]
    rw [hslot]
    rfl

end AvailableChain.FGSA.Run
end
