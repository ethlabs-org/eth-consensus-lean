module
public import AvailableChainFGSAProofs.Proofs.Clean.StateGate
public import AvailableChainFGSAProofs.Proofs.Clean.Transfer
public import AvailableChainFGSAProofs.Proofs.Shared.SameLabel
public import AvailableChainFGSAProofs.Proofs.Shared.Count
public import AvailableChainFGSAProofs.Proofs.Shared.AnchorService
public import AvailableChainFGSAProofs.Proofs.Clean.Service

public section

/-! P3 §8.7 F2.5a–b; bp02 §§5.4–5.5. Gate history and independent guard.
Old history supplies the active honest batch; receipt coverage retains its paths.
Ordered, Same, and nonempty are proved first; transfer then supplies Continues. -/

namespace AvailableChain.FGSA.Run

variable {ΔF : Time}
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- The store confirmation fact is called directly. The private batch boundary
-- is discharged by gate_batch_of_history at the public OSN consumer.
omit [Fintype V] in
private theorem ordered_of_confirmation
    {i : Nat} (hsch : V2.D.ScheduleWellFormed E rho)
    (hh : CleanHist p c E rho i) (hs : CleanState p c E rho i)
    (hbatch : ∀ x s, enabledGateAt p c E rho i x s →
      ∀ r B, (r, B) ∈ cleanResults p c E rho i → r < s →
      let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
      let v := actView pre
      let a := eraseFG pre.fg.F
      GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
        2 * SA.Root.prefixSupport p.toParams v s a ∧
      GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
        2 * SA.Root.prefixSupport p.toParams v s B ∧
      (∀ X, Block.Preceq a X → Block.Preceq X B → X ≠ a → X ∈ v.blocks)) :
    ∀ s r B C, (s, B) ∈ cleanResults p c E rho (i + 1) →
      (r, C) ∈ cleanResults p c E rho (i + 1) → s < r → Block.Preceq B C := by
  have hlabels : ∀ {j x y s r}, j ≤ i → IsGateTick p c rho j x s →
      IsGateTick p c rho i y r → s ≤ r := by
    intro j x y s r hji hj hi
    have ht : SA.gateTime p.toParams s ≤ SA.gateTime p.toParams r := by
      rcases hji.eq_or_lt with rfl | hlt
      · exact le_of_eq (V2.Event.tick.inj (Option.some.inj (hj.symm.trans hi))).2
      · obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
        obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
        have hk := (List.pairwise_iff_getElem.mp hsch.sorted) j i hjl hil hlt
        rw [hje, hie] at hk
        exact V2.D.Engine.time_le_of_key_le _ _ hk
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤
      4 * p.Δ * (r : Int) + 6 * p.Δ at ht
    have hd : (0 : Int) < p.Δ := p.deltaPos
    exact_mod_cast (show (s : Int) ≤ (r : Int) by nlinarith)
  intro s r B C hB hC hsr
  rcases cleanResults_mem_succ_iff.mp hC with hCold | ⟨x, ht, hCnew⟩
  · rcases cleanResults_mem_succ_iff.mp hB with hBold | ⟨y, hu, _⟩
    · exact hh.ordered s r B C hBold hCold hsr
    · obtain ⟨j, hj, x, hx, _⟩ := hCold
      exact (Nat.not_lt_of_ge (hlabels (Nat.le_of_lt hj) hx hu.1) hsr).elim
  · rcases cleanResults_mem_succ_iff.mp hB with hBold | ⟨y, hu, _⟩
    · let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams r)
      have hac : Block.Compatible (eraseFG pre.fg.F) B := by
        change Block.Compatible (eraseFG (clockPre p _ _).fg.F) B
        rw [clockPre_fg]
        rcases (hs.gateInputs x r ht.1).1 with hg | ⟨t, D, hD, _, haD⟩
        · change Block.Compatible (F_at p c E rho i x) B
          rw [hg]
          exact block_compatible_of_common (block_genesis_preceq B) (block_preceq_refl B)
        · exact block_compatible_of_preceq_compatible haD (cleanHist_results_compatible hh hD hBold)
      obtain ⟨ha, hb, hpath⟩ := hbatch x r ht s B hBold hsr
      obtain ⟨D, hD, hBD⟩ := fgsa_confirmationFrom_covers_majority p (actView pre)
        (eraseFG pre.fg.F) B r B.root hac ha hb hpath
      have hraw := (clean_gate_nonempty_raw hsch ht.1 hCnew).2
      have he : D = C := Option.some.inj (hD.symm.trans hraw)
      exact he ▸ hBD
    · exact (Nat.not_lt_of_ge (hlabels le_rfl ht.1 hu.1) hsr).elim



/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F2.5a:4900–4945; bp02 §5.4. Class B, label-seat count instance.
DC: Goldfish/Confirmation.lean:494; same honest participation count.
The label-seat bijection converts the Clean participation bound to Batch.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_gate_batch (b₀ : Time) (h : CleanCutSet p c E rho b₀ ΔF)
    {i : Nat} {x : V} {s : Slot} (hi : i < timeIdx rho b₀)
    (ht : IsGateTick p c rho i x s) :
    ∃ H : Finset (Fin p.n),
      (∀ k, k ∈ H ↔ rho.seatOf (.base (.head s)) k ∈ rho.honest ∧
        joinedAt p E rho (rho.seatOf (.base (.head s)) k) s (SA.voteTime p.toParams s)) ∧
      Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card :=
  clean_gate_batch_joined h hi ht

private theorem stamp_find_kept {α : Type} [BEq α] [LawfulBEq α]
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

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F2.5a:4921–4945; bp02 §5.4 (original early stamps). Class B.
DC: Schedule/AdoptionTransport.lean:157; receipt retention analogue.
INTENTIONAL: clockPre and actView retain the original FG-SA stamps
(spec/fgsa-protocol.tex:2506–2513), including stamps of inactive blocks. -/
theorem clean_gate_stamps (_hf : FGFoundation p c E rho)
    {j i : Nat} {x : V} {s : Slot} (hRF : V2.D.restartFree rho x j i) (_hx : x ∈ rho.honest)
    (hji : j ≤ i) (_hi : i ≤ rho.events.length)
    (o : GridCO.Wire p.n .root) (B : Block)
    (ho : o ∈ (storeAt p c E rho j x).base.votes)
    (hB : B ∈ (storeAt p c E rho j x).base.blocks) :
    let v := actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    o ∈ (storeAt p c E rho i x).base.votes ∧
      GridCO.stampVote v o = GridCO.stampVote (storeAt p c E rho j x).base o ∧
      GridCO.stampBlock v B = GridCO.stampBlock (storeAt p c E rho j x).base B := by
  intro v
  have hc := fgsa_store_cumulative_on p c E rho hji x hRF
  have hv : o ∈ (storeAt p c E rho j x).base.voteStamp.map Prod.fst := by
    change o ∈ (V2.D.Run.stateBefore E rho j x).st.base.voteStamp.map Prod.fst
    rw [fgsa_vote_stamp_keys E rho j x]
    exact ho
  have hb : B ∈ (storeAt p c E rho j x).base.blockStamp.map Prod.fst := by
    change B ∈ (V2.D.Run.stateBefore E rho j x).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho j x).«meta».stampKeys]
    exact hB
  have hev := stamp_find_kept hc.2.2.2.1 o hv
  have heb := stamp_find_kept hc.2.2.1 B hb
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
    cases he : (storeAt p c E rho j x).base.blockStamp.find? (fun row => row.1 == B) with
    | none =>
      obtain ⟨row, hr, ho⟩ := List.mem_map.mp hb
      have hn := List.find?_eq_none.mp he row hr
      rw [ho, beq_self_eq_true] at hn
      contradiction
    | some row => rfl

private theorem clean_gate_zero_of_receipts (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (i : Nat) (x : V) (H : Finset (Fin p.n))
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card)
    (hH : ∀ k, rho.seatOf (.base (.head 0)) k ∈ rho.honest →
      joinedAt p E rho (rho.seatOf (.base (.head 0)) k) 0 (SA.voteTime p.toParams 0) → k ∈ H)
    (hF : eraseFG (storeAt p c E rho i x).fg.F = .genesis)
    (hreceipts : ∀ k ∈ H, ∃ t,
      rho.seatOf (.base (.head 0)) k ∈ rho.honest ∧
      V2.D.Run.emits E rho (rho.seatOf (.base (.head 0)) k)
        (ofHead p ⟨.seat (.head 0) k, genesisRoot⟩) t ∧
      baseVote (⟨.seat (.head 0) k, genesisRoot⟩ : HeadWire p.n) ∈
        (storeAt p c E rho i x).base.votes ∧
      GridCO.stampVote
        (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams 0)))
        (baseVote (⟨.seat (.head 0) k, genesisRoot⟩ : HeadWire p.n)) <
          GridCO.earlyTime p.toParams.engine 0)
    (hgen : GridCO.stampBlock
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams 0))) .genesis <
        GridCO.earlyTime p.toParams.engine 0) :
    let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams 0)
    let v := actView pre
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine v 0) <
      2 * SA.Root.prefixSupport p.toParams v 0 .genesis ∧
    SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) v 0 = some .genesis := by
  intro pre v
  have hstore := cstoreInv_clockPre p (storeAt p c E rho i x)
    (storeBundle_stateBefore E rho i x).cstore (SA.gateTime p.toParams 0)
  have hg : Block.genesis ∈ v.blocks := (actView_genesis_F p pre hstore).1
  have hsupp : ∀ k ∈ H,
      Gen.AC.Root.poolSupports v.blocks
        (GridCO.cleanSupport p.toParams.engine v 0) k .genesis = true := by
    intro k hk
    obtain ⟨t, hh, he, hv, hvs⟩ := hreceipts k hk
    exact fgsa_active_support_of_receipt E rho hE i x 0 k .genesis .genesis t hh he hv
      hg (Nat.le_refl 0) hvs hgen (Gen.Pure.block_preceq_refl _)
  have hc := Gen.AC.Root.batch_counts v.blocks (GridCO.lateVotes p.toParams.engine v 0)
    (GridCO.cleanSupport p.toParams.engine v 0) (GridCO.cleanSupport p.toParams.engine v 0)
    H H.card (Gen.V2.Duty.faulty rho).card .genesis
    (fun _ ho => fgsa_early_subset_late p v 0 (List.mem_filter.mp ho).1)
    (fun _ ho => ho) rfl (fun k _ => fgsa_cleanSupport_no_equivocation p v 0 k)
    hsupp (fgsa_late_rest_bound_joined E rho hC hE i x 0 H hH) hbatch
  have hscore (B : Block) : SA.Root.prefixSupport p.toParams v 0 B =
      GridCO.goldfishScore v.blocks (GridCO.cleanSupport p.toParams.engine v 0)
        (GridCO.cleanSupport p.toParams.engine v 0) B :=
    actView_score p pre hstore
      (by rw [clockPre_headDomain]; exact base_headDomain_none p (reachable_stateBefore E rho i x))
      _ _ B
  have hmajor := (hc.2.2.1 .genesis (Gen.Pure.block_preceq_refl _)).2
  let score := GridCO.goldfishScore v.blocks (GridCO.cleanSupport p.toParams.engine v 0)
    (GridCO.cleanSupport p.toParams.engine v 0)
  let elig := fun X => decide (GridCO.voterCount (GridCO.lateVotes p.toParams.engine v 0) <
    2 * score X)
  have hno (C : Block) (hne : C ≠ .genesis) (k : Fin p.n) (hk : k ∈ H) :
      Gen.AC.Root.poolSupports v.blocks (GridCO.cleanSupport p.toParams.engine v 0) k C = false
          := by
    apply Bool.eq_false_iff.mpr
    intro hs
    obtain ⟨o, ho, hseat, hvote⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ k C).mp hs
    have hearly := (List.mem_filter.mp ho).1
    have hlabel : GridCO.headLabel? o = some 0 :=
      beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp hearly).1).2
    have hm : o ∈ (storeAt p c E rho i x).base.votes := by
      have hm := (List.mem_filter.mp (List.mem_filter.mp hearly).1).1
      change o ∈ (clockPre p (storeAt p c E rho i x) _).base.votes at hm
      rw [(Internal.clockPre_vn _ _).1] at hm
      exact hm
    obtain ⟨t, hh, he, _, _⟩ := hreceipts k hk
    have heq := fgsa_honest_head_eq_of_stored E rho hE i x 0 k genesisRoot t hh he
      o hm hlabel hseat
    rw [heq] at hvote
    have hlookup : Block.findByRoot? v.blocks genesisRoot = some .genesis :=
      Block.findByRoot?_of_unique hg (fun A hA B hB =>
        baseBlocks_rootInj p pre hstore A (List.mem_filter.mp hA).1 B (List.mem_filter.mp hB).1)
    change (match Block.findByRoot? v.blocks genesisRoot with
      | none => false
      | some B => decide (B ∈ v.blocks) && decide (B.slot ≤ 0) && Block.preceq C B) = true
      at hvote
    rw [hlookup] at hvote
    change (_ && _ && decide (C = Block.genesis)) = true at hvote
    exact hne (of_decide_eq_true (Bool.and_eq_true_iff.mp hvote).2)
  have hdom : Gen.Pure.DominatedSuffix .genesis .genesis v.blocks score elig := by
    rw [Gen.Pure.DominatedSuffix_def]
    intro C hstrict hC
    have heq : C = .genesis := of_decide_eq_true hC
    subst C
    change (false && _) = true at hstrict
    cases hstrict
  have hstop : Gen.Pure.NoEligibleChild v.blocks elig .genesis := by
    rw [Gen.Pure.NoEligibleChild_def]
    intro C _ hp
    have hne : C ≠ .genesis := by intro h; subst C; cases hp
    have hbound := hc.2.2.2.2 C (hno C hne)
    exact decide_eq_false (Nat.not_lt_of_ge hbound)
  have hw := Gen.Pure.walk_exact_of_dominated_suffix .genesis .genesis
    v.blocks score elig (Gen.Pure.block_preceq_refl _) hdom hstop
  refine ⟨by rw [hscore]; exact hmajor, ?_⟩
  have ha : eraseFG pre.fg.F = .genesis := by
    change eraseFG (clockPre p _ _).fg.F = _
    rw [clockPre_fg]
    exact hF
  rw [ha]
  have hscoreFn : GridCO.goldfishScoreOn (GridCO.resolutionTree v) v.blocks
      (GridCO.cleanSupport p.toParams.engine v 0)
      (GridCO.cleanSupport p.toParams.engine v 0) = score := funext hscore
  unfold SA.Root.confirmationFrom GridCO.confirmationFrom
  dsimp only
  rw [hscoreFn]
  change (if GridCO.voterCount (GridCO.lateVotes p.toParams.engine v 0) <
      2 * score (GridCO.ghost .genesis v.blocks score elig) then
        some (GridCO.ghost .genesis v.blocks score elig) else none) = _
  rw [hw]
  exact ite_eq_left hmajor

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F2.5a; bp02 §5.4, label zero. Class B, run nonemptiness.
DC: Goldfish/Confirmation.lean:494,567; genesis majority analogue.
INTENTIONAL: the F-anchored optional raw result is exactly genesis
(spec/fgsa-protocol.tex:2506–2513). No successor history is used.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_gate_zero (b₀ : Time) (h : CleanCutSet p c E rho b₀ ΔF)
    (hf : FGFoundation p c E rho) {i : Nat} {x : V}
    (hi : i < timeIdx rho b₀) (hG : enabledGateAt p c E rho i x 0)
    (hs : CleanState p c E rho i) :
    gateResultAt p c E rho i = some (some .genesis) := by
  have ht := hG.1
  have hsch := h.base.valid.toScheduleWellFormed
  have hx : x ∈ rho.honest := hsch.honest_only _ (List.mem_of_getElem? ht)
  have hil : i ≤ rho.events.length := Nat.le_of_lt (List.getElem?_eq_some_iff.mp ht).1
  have htime : 6 * p.Δ ≤ b₀ := by
    have hh := (V2.D.Engine.index_lt_read_length_iff hsch b₀ ht).mp hi
    change 4 * p.Δ * (0 : Int) + 6 * p.Δ ≤ b₀ at hh
    simpa only [mul_zero, zero_add] using hh
  have hd : (0 : Int) < p.Δ := p.deltaPos
  obtain ⟨H, hH, hbatch⟩ := clean_gate_batch p c E rho b₀ h hi ht
  have hF : eraseFG (storeAt p c E rho i x).fg.F = .genesis := by
    rcases (hs.gateInputs x 0 ht).1 with hg | ⟨r, B, _, hr, _⟩
    · exact hg
    · exact (Nat.not_lt_zero r hr).elim
  have hgen : GridCO.stampBlock
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams 0)))
      .genesis < GridCO.earlyTime p.toParams.engine 0 := by
    have hRF : V2.D.restartFree rho x 0 i := by
      intro j w _ hji he
      have hb := clean_gate_restart_bound hsch hG j w hji he
      have hpos := (h.base.restartsAtWakes x w (List.mem_of_getElem? he)).1
      change w ≤ 4 * p.Δ * (0 : Int) at hb
      nlinarith
    have hp := (hf.cumul.2 0 i x hx (Nat.zero_le i) hil hRF).1
    change [(Block.genesis, (0 : Time))] <+: (storeAt p c E rho i x).base.blockStamp at hp
    obtain ⟨tail, he⟩ := hp
    change (((clockPre p _ _).base.blockStamp.find? _).map Prod.snd).getD _ < _
    rw [(clockPre_stamps p _ _).1, ← he]
    change (0 : Time) < 4 * p.Δ * (0 : Int) + 2 * p.Δ
    nlinarith
  have hreceipts : ∀ k ∈ H, ∃ t,
      rho.seatOf (.base (.head 0)) k ∈ rho.honest ∧
      V2.D.Run.emits E rho (rho.seatOf (.base (.head 0)) k)
        (ofHead p ⟨.seat (.head 0) k, genesisRoot⟩) t ∧
      baseVote (⟨.seat (.head 0) k, genesisRoot⟩ : HeadWire p.n) ∈
        (storeAt p c E rho i x).base.votes ∧
      GridCO.stampVote
        (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams 0)))
        (baseVote (⟨.seat (.head 0) k, genesisRoot⟩ : HeadWire p.n)) <
          GridCO.earlyTime p.toParams.engine 0 := by
    intro k hk
    obtain ⟨hkh, hkJ⟩ := (hH k).mp hk
    have hka := hkJ.1
    change E.awake _ (4 * p.Δ * (0 : Int) + p.Δ) = true at hka
    have h1 : (1 : Time) * p.Δ ≤ rho.horizon := by linarith [h.cut.2]
    obtain ⟨l, hl, _⟩ := fgsa_tick_total E rho hsch h.base.delta _ hkh 1 h1
      (by simpa only [mul_zero, zero_add, Nat.cast_one, one_mul] using hka)
    have hem : V2.D.Run.emits E rho (rho.seatOf (.base (.head 0)) k)
        (ofHead p ⟨.seat (.head 0) k, genesisRoot⟩) p.Δ := by
      have hl' : rho.events[l]? = some (.tick (rho.seatOf (.base (.head 0)) k) p.Δ) := by
        simpa only [Nat.cast_one, one_mul] using hl
      refine ⟨l, hl', ?_⟩
      rw [(V2.D.Run.step_tick_eq E rho hl').2]
      have hv : SA.voteTime p.toParams 0 = p.Δ := by
        change 4 * p.Δ * (0 : Int) + p.Δ = p.Δ
        ring
      have hl0 : rho.events[l]? = some
          (.tick (rho.seatOf (.base (.head 0)) k) (SA.voteTime p.toParams 0)) := by
        rw [hv]
        exact hl'
      have hj := clean_joinedNow_of_joined_vote hsch hl0 hkJ
      rw [hv] at hj
      apply (fgsa_emits_head E rho _ _ _ 0 k genesisRoot).mpr
      refine ⟨?_, hv, rfl, hj, congrArg Block.root (headVote_zero p _).symm⟩
      change E.awake _ (4 * p.Δ * (0 : Int) + p.Δ) = true at hka
      simpa only [mul_zero, zero_add] using hka
    have hv : SA.voteTime p.toParams 0 = p.Δ := by
      change 4 * p.Δ * (0 : Int) + p.Δ = p.Δ
      ring
    have hem0 := hem
    rw [← hv] at hem0
    have hr := clean_gate_head_receipt h hx hG (by
      change 4 * p.Δ * (0 : Int) + 6 * p.Δ ≤ b₀
      simpa only [mul_zero, zero_add] using htime) k genesisRoot hkh hem0
    have hD : SA.earlyTime p.toParams 0 = 2 * p.Δ := by
      change 4 * p.Δ * (0 : Int) + 2 * p.Δ = 2 * p.Δ
      ring
    let j := V2.D.Run.idxBefore rho (SA.earlyTime p.toParams 0)
    have hji : j ≤ i := by
      by_contra hn
      have ht' := (Gen.V2.Duty.index_lt_idxBefore_iff hsch ht _).mp (Nat.lt_of_not_ge hn)
      change 4 * p.Δ * (0 : Int) + 6 * p.Δ <
        4 * p.Δ * (0 : Int) + 2 * p.Δ at ht'
      linarith
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch] at hr
    have hb : Block.genesis ∈ (storeAt p c E rho j x).base.blocks :=
      ((storeBundle_stateBefore E rho j x).cstore.baseTree _).mpr
        ⟨.genesis, (storeBundle_stateBefore E rho j x).cstore.fg.gen, rfl⟩
    have hRF := clean_gate_read_epoch h.base.valid hG
      (D := SA.earlyTime p.toParams 0) (by
        change 4 * p.Δ * (0 : Int) < 4 * p.Δ * (0 : Int) + 2 * p.Δ
        linarith)
    have htrans := clean_gate_stamps p c E rho hf hRF (s := 0) hx hji hil _ .genesis hr.1 hb
    refine ⟨p.Δ, hkh, hem, htrans.1, ?_⟩
    rw [htrans.2.1]
    exact hr.2
  have hraw := (clean_gate_zero_of_receipts p c E rho h.base.valid h.base.cstar i x H hbatch
    (fun k hk ha => (hH k).mpr ⟨hk, ha⟩) hF hreceipts hgen).2
  exact (clean_gate_raw hsch hG).trans (congrArg some hraw)

omit [Fintype V] in
private theorem gate_source_path (hsch : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {y : V} {s : Slot} {K : Block}
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)))
    (hK : K ∈ (storeAt p c E rho k y).base.blocks) :
    ∀ b, Block.Preceq b K → b ≠ .genesis →
      ∃ l < k, ∃ t o, blockOf? p o = some b ∧
        V2.D.Run.acceptsAt E rho l y o t ∧ 0 ≤ t ∧ t < SA.voteTime p.toParams s := by
  intro b hb hne
  have hc := (storeBundle_stateBefore E rho k y).cstore
  obtain ⟨Kfg, hKfg, he⟩ := (hc.baseTree K).mp hK
  rw [← he] at hb
  obtain ⟨Bfg, hBfg, heB⟩ := eraseFG_ancestor_mem hc.fg.closed hKfg hb
  have hbm := (hc.baseTree b).mpr ⟨Bfg, hBfg, heB⟩
  obtain ⟨l, hl, t, o, ho, ha⟩ := fgsa_block_accepted_origin E rho k y b hne hbm
  refine ⟨l, hl, t, o, ho, ha, ?_, ?_⟩
  · obtain ⟨parent, hd, _⟩ := ha.1
    exact (hsch.in_horizon _ (List.mem_of_getElem? hd)).1
  · obtain ⟨parent, hd, _⟩ := ha.1
    obtain ⟨hll, hle⟩ := List.getElem?_eq_some_iff.mp hd
    obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
    have hkey := (List.pairwise_iff_getElem.mp hsch.sorted) l k hll hkl hl
    rw [hle, hke] at hkey
    change toLex (t, (2 : Nat)) ≤ toLex (SA.voteTime p.toParams s, 1) at hkey
    rcases Prod.Lex.toLex_le_toLex.mp hkey with hlt | ⟨_, hphase⟩
    · exact hlt
    · omega

omit [Fintype V] in
private theorem gate_path_coverage (hE : V2.D.ExecutionValid E rho)
    (hR : V2.D.RestartsAtWakes E rho) (hDelta : E.Δ = p.Δ)
    (b₀ : Time) (hhealthy : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (fgsaDelay E.Δ ΔF) b₀)
    (hb₀ : b₀ ≤ rho.horizon) {i k : Nat} {x y : V} {s : Slot} {K : Block}
    (hG : enabledGateAt p c E rho i x s) (hcut : SA.gateTime p.toParams s ≤ b₀)
    (hy : y ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)))
    (hK : K ∈ (storeAt p c E rho k y).base.blocks)
    (hF : ∀ j, j ≤ i → Block.Preceq (F_at p c E rho j x) K) :
    ∃ required paths,
      ReceiptCoverageAnchorPremises E rho (fun t => t + p.Δ) b₀
        (SA.earlyTime p.toParams s) 0 x K required paths
        (fun _ _ => SA.voteTime p.toParams s) ∧
      paths K (SA.earlyTime p.toParams s) := by
  have ht := hG.1
  have hx : x ∈ rho.honest := hE.honest_only _ (List.mem_of_getElem? ht)
  let required := fun o t => ∃ l < k, V2.D.Run.acceptsAt E rho l y o t ∧
    ∃ b, blockOf? p o = some b ∧ Block.Preceq b K
  let paths := fun B d => B = K ∧ d = SA.earlyTime p.toParams s
  have hsch := hE.toScheduleWellFormed
  have hD : SA.earlyTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hd : (0 : Int) < p.Δ := p.deltaPos
    linarith
  have hidx : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ i := by
    by_contra hh
    have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hsch ht (SA.earlyTime p.toParams s)).mp
      (Nat.lt_of_not_ge hh)
    exact (not_lt.mpr hD) hlt
  have htime : ∀ o t, required o t → 0 ≤ t ∧ t < SA.voteTime p.toParams s := by
    rintro o t ⟨l, hl, ha, _⟩
    obtain ⟨parent, hd, _⟩ := ha.1
    refine ⟨(hsch.in_horizon _ (List.mem_of_getElem? hd)).1, ?_⟩
    obtain ⟨hll, hle⟩ := List.getElem?_eq_some_iff.mp hd
    obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
    have hkey := (List.pairwise_iff_getElem.mp hsch.sorted) l k hll hkl hl
    rw [hle, hke] at hkey
    change toLex (t, (2 : Nat)) ≤ toLex (SA.voteTime p.toParams s, 1) at hkey
    rcases Prod.Lex.toLex_le_toLex.mp hkey with hh | ⟨_, hh⟩
    · exact hh
    · omega
  have hve : SA.voteTime p.toParams s + p.Δ = SA.earlyTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 2 * p.Δ
    ring
  have decode {o : Obj p} {b : Block} (hb : blockOf? p o = some b) :
      ∃ r N, (toWire p o).decode = some (.block r N) := by
    change (match (toWire p o).decode with
      | some (.block _ N) => some N.erase | _ => none) = _ at hb
    cases hd : (toWire p o).decode with
    | none => rw [hd] at hb; contradiction
    | some m => cases m <;> simp_all
  refine ⟨required, paths, ?_, rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hDelta] using Gen.V2.Duty.deliveryWithinOn_of_healthyPrefixBy E rho b₀ hhealthy
          (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ _)
  · intro o t hr
    have htt := htime o t hr
    obtain ⟨l, _, ha, b, hb, _⟩ := hr
    obtain ⟨r, N, hd⟩ := decode hb
    obtain ⟨hT, hH, hRF, _⟩ := fgsa_gate_path_anchor_service hE hDelta hR hx hy hG hd ha
      htt.2
    have h0 : 0 ≤ SA.voteTime p.toParams s := by
      change 0 ≤ 4 * p.Δ * (s : Int) + p.Δ
      have := p.deltaPos
      positivity
    refine ⟨htt.1, htt.2.le, h0,
      lt_add_of_pos_right _ p.deltaPos, ?_, Nat.zero_le _, ?_, hH, hRF,
      (fgsa_proposal_acceptance_facts hE hd ha).2⟩
    · exact hve.le
    · simpa only [hve] using hT
  · rintro o t ⟨l, _, ha, b, hb, _⟩ r signer B hv
    obtain ⟨u, N, hd⟩ := decode hb
    rw [hd] at hv
    cases hv
  · intro o t hr
    have htt := htime o t hr
    obtain ⟨l, _, ha, b, hb, _⟩ := hr
    obtain ⟨r, N, hd⟩ := decode hb
    have hh := (fgsa_gate_path_anchor_service hE hDelta hR hx hy hG hd ha
      htt.2).2.2.2
    simpa only [hve] using hh
  · intro j _ hj
    exact block_compatible_of_common (block_preceq_refl K) (hF j (hj.trans hidx))
  · exact ⟨fun _ _ hab => add_le_add hab le_rfl, hD.trans hcut, hb₀, Nat.zero_le _⟩
  · rintro B d ⟨hBK, hdD⟩
    subst B
    subst d
    refine ⟨block_preceq_refl K, le_rfl, ?_⟩
    intro b hb hne
    obtain ⟨l, hl, t, o, ho, ha, _, ht'⟩ := gate_source_path p c E rho hsch hk hK b hb hne
    have hdecode : ∃ r N, N.erase = b ∧ (toWire p o).decode = some (.block r N) := by
      change (match (toWire p o).decode with
        | some (.block _ N) => some N.erase | _ => none) = _ at ho
      cases he : (toWire p o).decode with
      | none => rw [he] at ho; contradiction
      | some m =>
        cases m <;> simp only [he, reduceCtorEq, Option.some.injEq] at ho
        exact ⟨_, _, ho, rfl⟩
    obtain ⟨r, N, heN, hdec⟩ := hdecode
    refine ⟨o, t, r, N, heN, ⟨l, hl, ha, b, ho, hb⟩, hdec, ?_⟩
    exact hve.le
  · intro o t r N hr hdec
    obtain ⟨l, hl, ha, b', hb', hBK⟩ := hr
    have hb : blockOf? p o = some N.erase := by
      change (match (toWire p o).decode with | some (.block _ N) => some N.erase | _ => none) = _
      rw [hdec]
    have heq := Option.some.inj (hb'.symm.trans hb)
    subst b'
    exact ⟨K, SA.earlyTime p.toParams s, ⟨rfl, rfl⟩, hBK⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F2.5a:4921–4945; bp02 §5.4. Class B, old-history head prefixes.
DC: SafetyRegimes.lean:69–75; successive selection/HEAD order analogue.
INTENTIONAL: retrospective event reads and every intervening F are explicit
(spec/fgsa-protocol.tex:2506–2513). Only old Continues is used. -/
theorem clean_gate_head_prefixes {b₀ : Time}
    (h : CleanCutSet p c E rho b₀ ΔF) (hf : FGFoundation p c E rho)
    {i k : Nat} {x y : V} {s : Slot} (hi : i < timeIdx rho b₀)
    (ht : IsGateTick p c rho i x (s + 1))
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)))
    (hh : CleanHist p c E rho i) (hs : CleanState p c E rho i) :
    (∀ r B, (r, B) ∈ cleanResults p c E rho i → r < s + 1 →
      Block.Preceq B (headAtIdx p c E rho k (s + 1))) ∧
    (∀ j, j ≤ i → Block.Preceq (F_at p c E rho j x) (headAtIdx p c E rho k (s + 1))) :=
  clean_gate_head_prefixes_joined h hf hi ht hk hJ hh hs

private theorem gate_active_heads (b₀ : Time) (h : CleanCutSet p c E rho b₀ ΔF)
    (hf : FGFoundation p c E rho) {i : Nat} {x : V} {s : Slot}
    (hi : i < timeIdx rho b₀) (hG : enabledGateAt p c E rho i x (s + 1))
    (hh : CleanHist p c E rho i) (hs : CleanState p c E rho i)
    (B : Block)
    (hB : ∀ k y, rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      Block.Preceq B (headAtIdx p c E rho k (s + 1))) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head (s + 1))) q ∈ rho.honest →
      joinedAt p E rho (rho.seatOf (.base (.head (s + 1))) q) (s + 1)
        (SA.voteTime p.toParams (s + 1)) →
      ∃ K t,
        rho.seatOf (.base (.head (s + 1))) q ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.head (s + 1))) q)
          (ofHead p ⟨.seat (.head (s + 1)) q, K.root⟩) t ∧
        baseVote (⟨.seat (.head (s + 1)) q, K.root⟩ : HeadWire p.n) ∈
          (storeAt p c E rho i x).base.votes ∧
        K ∈ (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams (s + 1)))).blocks ∧
        K.slot ≤ s + 1 ∧
        GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams (s + 1))))
          (baseVote (⟨.seat (.head (s + 1)) q, K.root⟩ : HeadWire p.n)) <
            GridCO.earlyTime p.toParams.engine (s + 1) ∧
        GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams (s + 1)))) K < GridCO.earlyTime p.toParams.engine (s + 1) ∧
        Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams (s + 1))).fg.F) K ∧ Block.Preceq B K := by
  have ht := hG.1
  intro q hy hJ
  have hawake := hJ.1
  let y := rho.seatOf (.base (.head (s + 1))) q
  have hsch := h.base.valid.toScheduleWellFormed
  have hd : (0 : Int) < p.Δ := p.deltaPos
  have hx : x ∈ rho.honest := hsch.honest_only _ (List.mem_of_getElem? ht)
  have hil := Nat.le_of_lt (List.getElem?_eq_some_iff.mp ht).1
  have hcut : SA.gateTime p.toParams (s + 1) ≤ b₀ :=
    (V2.D.Engine.index_lt_read_length_iff hsch b₀ ht).mp hi
  have htimes : SA.voteTime p.toParams (s + 1) + p.Δ = SA.earlyTime p.toParams (s + 1) := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ + p.Δ =
      4 * p.Δ * ((s + 1 : Nat) : Int) + 2 * p.Δ
    ring
  have hearly : SA.earlyTime p.toParams (s + 1) < SA.gateTime p.toParams (s + 1) := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + 2 * p.Δ <
      4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    linarith
  have hvote : SA.voteTime p.toParams (s + 1) < SA.earlyTime p.toParams (s + 1) := by
    rw [← htimes]
    exact lt_add_of_pos_right _ hd
  have hvt : ((4 * (s + 1) + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams (s + 1) := by
    change ((4 * (s + 1) + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    ring
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hsch h.base.delta y hy (4 * (s + 1) + 1)
    (hvt ▸ (hvote.le.trans (hearly.le.trans (hcut.trans h.cut.2)))) (hvt ▸ hawake)
  rw [hvt] at hk
  let K := headAtIdx p c E rho k (s + 1)
  have hKeq : K = headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y)
      (SA.voteTime p.toParams (s + 1))).st (s + 1) := by
    have htick : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams (s + 1)) = some k := by
      have hkl := (List.getElem?_eq_some_iff.mp hk).1
      obtain ⟨l, hl⟩ : ∃ l, V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams (s + 1)) = some l := by
        rw [V2.D.Run.tickIdx?, ← Option.isSome_iff_exists, List.findIdx?_isSome, List.any_eq_true]
        refine ⟨rho.events[k], List.getElem_mem hkl, ?_⟩
        rw [(List.getElem?_eq_some_iff.mp hk).2]
        exact decide_eq_true ⟨rfl, rfl⟩
      exact (fgsa_tick_unique E rho hsch (V2.D.Run.tickIdx?_spec hl) hk) ▸ hl
    have heK := vHead_eq_headAtIdx p c E rho hsch hk
    rw [vHead_def, postClock_def, preTick_def, htick] at heK
    exact (Option.some.inj heK).symm
  have hKsource : K ∈ (storeAt p c E rho k y).base.blocks := by
    have hm := headVote_stored p _ (storeBundle_postClock E rho k y
      (SA.voteTime p.toParams (s + 1))).cstore (s + 1)
    rw [← hKeq] at hm
    change K ∈ (clock p (storeAt p c E rho k y) _).base.blocks at hm
    rwa [(clock_cumulative p _ _).2.1] at hm
  have hem : V2.D.Run.emits E rho y (ofHead p ⟨.seat (.head (s + 1)) q, K.root⟩)
      (SA.voteTime p.toParams (s + 1)) := by
    refine ⟨k, hk, ?_⟩
    rw [(V2.D.Run.step_tick_eq E rho hk).2]
    exact (fgsa_emits_head E rho _ y _ (s + 1) q K.root).mpr
      ⟨hawake, rfl, rfl, clean_joinedNow_of_joined_vote hsch hk hJ, congrArg Block.root hKeq⟩
  have hprefix := clean_gate_head_prefixes p c E rho h hf hi ht hk hJ hh hs
  obtain ⟨required, paths, hcov, hp⟩ := gate_path_coverage p c E rho h.base.valid
    h.base.restartsAtWakes h.base.delta b₀ h.healthy h.cut.2 hG hcut hy hk hKsource hprefix.2
  have hidx : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams (s + 1)) ≤ i := by
    by_contra hn
    exact (not_lt.mpr hearly.le)
      ((Gen.V2.Duty.index_lt_idxBefore_iff hsch ht _).mp (Nat.lt_of_not_ge hn))
  have hFearly : Block.Preceq (eraseFG (V2.D.Run.stateBeforeTime E rho
      (SA.earlyTime p.toParams (s + 1)) x).st.fg.F) K := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch]
    exact hprefix.2 _ hidx
  have hpath := fgsa_active_path_of_coverage_anchor (hroots := h.base.receiptIdealization)
    E rho h.base.valid h.base.delta
    (fun t => t + p.Δ) b₀ (SA.earlyTime p.toParams (s + 1)) 0 x K required paths
    (fun _ _ => SA.voteTime p.toParams (s + 1)) hx hcov hp hFearly
  let j := V2.D.Run.idxBefore rho (SA.earlyTime p.toParams (s + 1))
  have hKearly : K ∈ (storeAt p c E rho j x).base.blocks := by
    have hm := (actView_blocks _ K).mp (hpath K (block_preceq_refl K))
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch] at hm
    exact hm.1
  have hr := clean_gate_head_receipt h hx hG hcut q K.root hy hem
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch] at hr
  have hRF := clean_gate_read_epoch h.base.valid hG
    (D := SA.earlyTime p.toParams (s + 1)) (by
      change 4 * p.Δ * ((s + 1 : Nat) : Int) <
        4 * p.Δ * ((s + 1 : Nat) : Int) + 2 * p.Δ
      linarith)
  have htrans := clean_gate_stamps p c E rho hf hRF (s := s + 1) hx hidx hil _ K hr.1 hKearly
  have hKg : K ∈ (actView (clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams (s + 1)))).blocks := by
    apply (actView_blocks _ K).mpr
    rw [(clockPre_fields p _ _).2.1, clockPre_fg]
    exact ⟨(hf.cumul.1 j i x hx hidx hil).2.1.subset hKearly,
      block_compatible_of_common (block_preceq_refl K) (hprefix.2 i le_rfl)⟩
  have hslot : K.slot ≤ s + 1 := by
    have hm := (fgsa_stateBefore_bounds E rho hsch k y).1 K hKsource
    have hn := fgsa_preTick_now_le E rho hsch hk
    exact hm.trans ((Internal.slotOf_mono (p := p) hn).trans_eq
      (slotOf_offset p (s + 1) p.Δ hd.le (by omega)))
  have hpos : 0 < SA.earlyTime p.toParams (s + 1) := by
    change 0 < 4 * p.Δ * ((s + 1 : Nat) : Int) + 2 * p.Δ
    positivity
  refine ⟨K, SA.voteTime p.toParams (s + 1), hy, hem, htrans.1, hKg, hslot,
    ?_, ?_, ?_, hB k y hk hJ⟩
  · rw [htrans.2.1]
    exact hr.2
  · rw [htrans.2.2]
    have hm : K ∈ (rho.stateBeforeTime E (SA.earlyTime p.toParams (s + 1)) x).st.base.blocks := by
      rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch]
      exact hKearly
    have hb := fgsa_block_stamp_before_read E rho hsch x _ hpos K hm
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch] at hb
    exact hb
  · rw [clockPre_fg]
    exact hprefix.2 i le_rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F2.5a; bp02 §5.4. Class B, same-label history extension.
DC: Goldfish/Confirmation.lean:405, eligible_compatible; same compatibility.
INTENTIONAL: actual optional F-anchored reads (spec/fgsa-protocol.tex:2496–2513).
This covers old/new and new/new pairs without a successor Continues premise.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_gate_same (b₀ : Time) (h : CleanCutSet p c E rho b₀ ΔF)
    {i : Nat} (hi : i < timeIdx rho b₀) :
    ∀ s B C, (s, B) ∈ cleanResults p c E rho (i + 1) →
      (s, C) ∈ cleanResults p c E rho (i + 1) → Block.Compatible B C := by
  intro s B C ⟨j, hj, x, hx, hGx, hB⟩ ⟨k, hk, y, hy, hGy, hC⟩
  have hsch := h.base.valid.toScheduleWellFormed
  have hd : SA.gateTime p.toParams s ≤ b₀ :=
    (V2.D.Engine.index_lt_read_length_iff hsch b₀ hx).mp (show j < timeIdx rho b₀ by omega)
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [h.base.delta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    linarith
  exact fgsa_sameLabel_on (hroots := h.base.idealization) p c E rho h.base.valid s
    (fgsa_sameLabel_serviceScope E rho h.base.valid h.base.restartsAtWakes h.base.delta s
      (Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _) hvd hd h.cut.2))
    x y B C (hsch.honest_only _ (List.mem_of_getElem? hx))
    (hsch.honest_only _ (List.mem_of_getElem? hy))
    ((gateResultAt_eq_gateResult p c E rho hsch hx).symm.trans hB)
    ((gateResultAt_eq_gateResult p c E rho hsch hy).symm.trans hC)

private theorem gate_batch_of_history (b₀ : Time) (h : CleanCutSet p c E rho b₀ ΔF)
    (hf : FGFoundation p c E rho) {i : Nat} {x : V} {s : Slot}
    (hi : i < timeIdx rho b₀) (hG : enabledGateAt p c E rho i x (s + 1))
    (hh : CleanHist p c E rho i) (hs : CleanState p c E rho i)
    (B : Block)
    (hB : ∀ k y, rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      Block.Preceq B (headAtIdx p c E rho k (s + 1))) :
    let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams (s + 1))
    let v := actView pre
    let a := eraseFG pre.fg.F
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine v (s + 1)) <
      2 * SA.Root.prefixSupport p.toParams v (s + 1) a ∧
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine v (s + 1)) <
      2 * SA.Root.prefixSupport p.toParams v (s + 1) B ∧
    (∀ X, Block.Preceq a X → Block.Preceq X B → X ≠ a → X ∈ v.blocks) := by
  have ht := hG.1
  obtain ⟨H, hH, hb⟩ := clean_gate_batch p c E rho b₀ h hi ht
  apply fgsa_gate_batch_premises_joined E rho h.base.valid h.base.cstar i x (s + 1) B H hb
    (fun k hk ha => (hH k).mpr ⟨hk, ha⟩)
  intro k hk
  exact gate_active_heads p c E rho b₀ h hf hi hG hh hs B hB k
    ((hH k).mp hk).1 ((hH k).mp hk).2

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 F2.5a; bp02 §5.4. Class B, new-gate nonemptiness.
DC: NamedConfirmationWalk.lean:38 and Goldfish/Confirmation.lean:494,567.
INTENTIONAL: the optional F-anchored raw result must pass the anchor test
(spec/fgsa-protocol.tex:2506–2513). Label zero returns genesis exactly.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_gate_nonempty (b₀ : Time) :
    CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
    FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
    ∀ i x s, i < timeIdx rho b₀ → enabledGateAt p c E rho i x s →
      CleanHist p c E rho i → (∀ k, k ≤ i → CleanState p c E rho k) →
      ∃ B, gateResultAt p c E rho i = some (some B) ∧ (s = 0 → B = .genesis) := by
  intro h _ hf _ i x s hi hG hh hall
  have ht := hG.1
  cases s with
  | zero => exact ⟨.genesis, clean_gate_zero p c E rho b₀ h hf hi hG (hall i le_rfl), fun _ => rfl⟩
  | succ s =>
    have hb := gate_batch_of_history p c E rho b₀ h hf hi hG hh (hall i le_rfl)
      .genesis (fun _ _ _ _ => block_genesis_preceq _)
    let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams (s + 1))
    obtain ⟨B, hB, _⟩ := fgsa_confirmationFrom_covers_majority p (actView pre)
      (eraseFG pre.fg.F) .genesis (s + 1) genesisRoot
      (block_compatible_of_common (block_preceq_refl _) (block_genesis_preceq _))
      hb.1 hb.2.1 hb.2.2
    refine ⟨B, (clean_gate_raw h.base.valid.toScheduleWellFormed hG).trans (congrArg some hB), ?_⟩
    intro hn
    exact (Nat.succ_ne_zero s hn).elim

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F2.5a; bp02 §§5.4–5.5. Class B, add-only history extension.
DC: SafetyRegimes.lean:56–75 and NamedConfirmationWalk.lean:38.
INTENTIONAL: three event-prefix fields for actual F-anchored optional reads
(spec/fgsa-protocol.tex:2496–2525; lead Q2). The result adds no Continues field.
The first conjunct supplies the Ordered premise of clean_transfer_frame.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_gate_history_osn (b₀ : Time) :
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i, i < timeIdx rho b₀ → CleanGateTick p c rho i → CleanHist p c E rho i →
    (∀ k, k ≤ i → CleanState p c E rho k) →
    (∀ s r B C, (s, B) ∈ cleanResults p c E rho (i + 1) →
      (r, C) ∈ cleanResults p c E rho (i + 1) → s < r → Block.Preceq B C) ∧
    (∀ s B C, (s, B) ∈ cleanResults p c E rho (i + 1) →
      (s, C) ∈ cleanResults p c E rho (i + 1) → Block.Compatible B C) ∧
    (∀ j x s, j < i + 1 → enabledGateAt p c E rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis)) := by
  intro h hq hf hsrc i hi _ hh hall
  refine ⟨?_, clean_gate_same p c E rho b₀ h hi, ?_⟩
  · apply ordered_of_confirmation p c E rho h.base.valid.toScheduleWellFormed hh (hall i le_rfl)
    intro x s hG r B hB hrs
    have ht := hG.1
    cases s with
    | zero => exact (Nat.not_lt_zero r hrs).elim
    | succ s =>
      apply gate_batch_of_history p c E rho b₀ h hf hi hG hh (hall i le_rfl) B
      intro k y hk hJ
      exact (clean_gate_head_prefixes p c E rho h hf hi ht hk hJ hh
        (hall i le_rfl)).1 r B hB hrs
  · intro j x s hj ht
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hji | he
    · exact hh.nonempty j x s hji ht
    · subst j
      exact clean_gate_nonempty p c E rho b₀ h hq hf hsrc i x s hi ht hh hall


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 §§8.2–8.7 F2.5b; bp02 §§5.4–5.6. Class B, frozen history step.
DC: GSTZeroPreparedWalk.lean:546, SafetyRegimes.lean:53–80, and
JointHistoryGapsIdx.lean:26,141. INTENTIONAL divergence: FG-SA has an
F-anchored optional raw result, leases, and gate-before-action in one tick.
The event-prefix step proves Ordered before retrospective Continues
(bp02:553–613); it uses no closed safety theorem or successor state.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_gateHistStep (b₀ : Time) : CleanGateHistStep (ΔF := ΔF) p c E rho b₀ := by
  rw [CleanGateHistStep_def (ΔF := ΔF), CleanHistStep_def (ΔF := ΔF)]
  intro h hq hf hsrc i hi hgate hh hall
  have hOSN := clean_gate_history_osn p c E rho b₀ h hq hf hsrc i hi hgate hh hall
  refine ⟨hOSN.1, hOSN.2.1, hOSN.2.2, ?_⟩
  intro j k x y s B hj hkj ht hk hJ hB
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hji | he
  · exact hh.continues j k x y s B hji hkj ht hk hJ hB
  · subst j
    apply cleanTransfer p c E rho b₀ h hq hf hsrc i k x y s B hi hkj ht hk hJ hh hall hB
    intro r C hC hrs
    exact hOSN.1 r s C B
      (cleanResults_mono (Nat.le_succ i) hC)
      (cleanResults_mem_succ_iff.mpr (Or.inr ⟨x,
        clean_gate_enabled_of_result h.base.valid.toScheduleWellFormed ht hB, hB⟩)) hrs

end AvailableChain.FGSA.Run
end
