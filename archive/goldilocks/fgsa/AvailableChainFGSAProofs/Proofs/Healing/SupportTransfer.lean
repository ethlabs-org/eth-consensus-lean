module
public import AvailableChainFGSAProofs.Proofs.Healing.FramePaths
public import AvailableChainFGSAProofs.Proofs.Healing.SupportFrame
public import AvailableChainFGSAProofs.Proofs.Healing.SupportRelay
public import AvailableChainFGSAProofs.Proofs.Healing.SupportWrite
public import AvailableChainFGSAProofs.Proofs.Healing.SupportRelease

public section

/-! H-SUPPORT H.1 adapters (plan §4 steps 2–5; G3, G5). The private helpers restate
private helpers of Shared/Relay.lean, Shared/Release.lean and Clean/TransferFrame.lean,
which this lane may not edit. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.AC.Root

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Local service inputs for the first transfer. Retained HEAD history is explicit.
These fields describe object service and read epochs, rather than transfer conclusions. -/
structure FirstTransferScope (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c))
    (ix iy : Nat) (x y : V) (s : Slot) : Prop where
  sourceGuard : enabledGateAt p c E rho ix x s
  receiverGuard : joinedAtTime p (storeAt p c E rho iy y).restartTime
    (SA.releaseTime p.toParams s) = true
  epoch : V2.D.restartFree rho y
    (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) iy
  forward : ∀ q b,
    (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∈
      GridCO.cleanSupport p.toParams.engine
        (actView (clockPre p (storeAt p c E rho ix x)
          (SA.gateTime p.toParams s))) s →
    HeadRelayLocalServiceScope E rho s q b (SA.freezeTime p.toParams s) iy y
  backward : ∀ q b,
    ((⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∈
        GridCO.votesAt (storeAt p c E rho iy y).base s ∨
      (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∈
        headVotes p (clock p (storeAt p c E rho iy y)
          (SA.voteTime p.toParams (s + 1))) (s + 1)) →
    HeadRelayLocalServiceScope E rho s q b (SA.gateTime p.toParams s) ix x
  targets : ∀ K, K ∈ (storeAt p c E rho ix x).base.blocks →
    GridCO.stampBlock (storeAt p c E rho ix x).base K <
      SA.earlyTime p.toParams s →
    Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) K →
    TargetReceiptService E rho K (SA.freezeTime p.toParams s) y
  carriers : HealingCarriersAt E rho s iy y
    (SA.voteTime p.toParams (s + 1))

/-- The first carrier uses the stored release guard at this same receiver tick. -/
theorem FirstTransferScope.carriersOn {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {ix iy : Nat} {x y : V} {s : Slot}
    (h : FirstTransferScope E rho ix iy x y s) (hE : V2.D.ExecutionValid E rho)
    (hy : y ∈ rho.honest)
    (hi : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hSync : E.t_GST ≤ SA.voteTime p.toParams s) :
    ∀ j z, z ∈ rho.honest →
      rho.events[j]? = some (.tick z (SA.voteTime p.toParams s)) →
      joinedAt p E rho z s (SA.voteTime p.toParams s) →
      HeadCarrierServices E rho j z s y := by
  have hread : HealingJoinedTick E rho iy y (SA.voteTime p.toParams (s + 1)) := by
    apply healing_joined_tick_of_guard p c E rho hE hy hi
    convert h.receiverGuard using 1
    congr 1
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ = 4 * p.Δ * (s : Int) + 5 * p.Δ
    push_cast
    ring
  apply h.carriers hSync hread _ (hE.in_horizon _ (List.mem_of_getElem? hi)).2
  change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤
    4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
  push_cast
  linarith [p.deltaPos]

private theorem transfer_freeze_epoch (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {ix iy : Nat} {x y : V} {s : Slot}
    (hScope : FirstTransferScope E rho ix iy x y s) :
    V2.D.restartFree rho y (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) iy := by
  apply hScope.epoch.mono (fgsa_idxBefore_mono rho ?_) le_rfl
  change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
  linarith [p.deltaPos]

private theorem transfer_raw_backward (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    {ix iy : Nat} {x y : V} {s : Slot} (hx : x ∈ rho.honest)
    (hScope : FirstTransferScope E rho ix iy x y s)
    (o : GridCO.Wire p.n .root)
    (ho : o ∈ GridCO.votesAt (storeAt p c E rho iy y).base s)
    (q : Fin p.n) (hq : GridCO.headSeat? o = some q) :
    let late := GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s
    o ∈ late ∨ GridCO.equivocates late q = true := by
  obtain ⟨hm, hl⟩ := List.mem_filter.mp ho
  have hl' : GridCO.headLabel? o = some s := by simpa only [beq_iff_eq] using hl
  obtain ⟨auth, payload⟩ := o
  cases auth <;> cases payload <;> try contradiction
  rename_i r k b
  have hr := Option.some.inj hl'
  have hk := Option.some.inj hq
  subst r; subst k
  exact healing_support_raw_backward_on E rho hE hx q b (hScope.backward q b (Or.inl ho))

private theorem transfer_vote_shape {n : Nat} (o : GridCO.Wire n .root) (s : Slot) (k : Fin n)
    (hl : GridCO.headLabel? o = some s) (hk : GridCO.headSeat? o = some k) :
    ∃ B, o = ⟨.seat s k, .head B⟩ := by
  obtain ⟨auth, payload⟩ := o
  cases auth <;> cases payload <;> try contradiction
  rename_i r j B
  have hr : r = s := Option.some.inj hl
  have hj : j = k := Option.some.inj hk
  subst r; subst j
  exact ⟨B, rfl⟩

private theorem transfer_lift' {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

private theorem transfer_vote_release (s : Slot) :
    SA.voteTime p.toParams (s + 1) = SA.releaseTime p.toParams s := by
  change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ = 4 * p.Δ * (s : Int) + 5 * p.Δ
  push_cast
  ring

private theorem transfer_vote_clock' (st : State p.n) (s : Slot) :
    FGSA.clock p st (SA.voteTime p.toParams (s + 1)) =
      clockPre p st (SA.voteTime p.toParams (s + 1)) := by
  have hn : isGateTime p (SA.voteTime p.toParams (s + 1)) ≠ true := by
    intro hh
    obtain ⟨r, hr⟩ := (isGateTime_iff p _).mp hh
    symm at hr
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ =
      4 * p.Δ * (r : Int) + 6 * p.Δ at hr
    push_cast at hr
    have hd := p.deltaPos
    rcases Nat.lt_or_ge r s with hrs | hsr
    · have hi : (r : Int) + 1 ≤ (s : Int) := by exact_mod_cast hrs
      nlinarith
    · have hi : (s : Int) ≤ (r : Int) := by exact_mod_cast hsr
      nlinarith
  change (if isGateTime p _ then _ else _) = _
  rw [ite_eq_right hn]

private def transferReleaseSeats {n : Nat} (q : GridCO.Params) (v : GridCO.State n .root)
    (s : Slot) (B : Block) : Finset (Fin n) :=
  ((GridCO.seats n ((GridCO.votesAt v s).filter (fun o =>
    GridCO.resolvedBefore v o (GridCO.releaseTime q s)))).filter (fun k =>
      !GridCO.equivocates (GridCO.votesAt v s) k &&
      (GridCO.seatVotes ((GridCO.votesAt v s).filter (fun o =>
        GridCO.resolvedBefore v o (GridCO.releaseTime q s))) k).any (fun o =>
          (GridCO.resolvedHead? v o).any (fun C => !Block.compatible C B)))).toFinset

private theorem transfer_release_card {n : Nat} (q : GridCO.Params) (v : GridCO.State n .root)
    (s : Slot) (B : Block) :
    GridCO.releaseCount q v s B = (transferReleaseSeats q v s B).card := by
  have hp : (fun o : GridCO.Wire n .root => match GridCO.resolvedHead? v o with
      | some C => !Block.compatible C B
      | none => false) = (fun o => (GridCO.resolvedHead? v o).any
        (fun C => !Block.compatible C B)) := by
    funext o
    cases GridCO.resolvedHead? v o <;> rfl
  unfold GridCO.releaseCount transferReleaseSeats
  dsimp only
  refine Eq.trans ?_ (List.toFinset_card_of_nodup
    (List.Nodup.filter _ (List.nodup_dedup (α := Fin n) _))).symm
  congr 1
  apply congrArg (fun f => List.filter f _)
  funext k
  congr 1
  apply congrArg (fun f => (GridCO.seatVotes _ k).any f)
  exact hp

private theorem transfer_release_mem {n : Nat} (q : GridCO.Params) (v : GridCO.State n .root)
    (s : Slot) (B : Block) (k : Fin n)
    (he : GridCO.equivocates (GridCO.votesAt v s) k = false)
    (o : GridCO.Wire n .root) (ho : o ∈ GridCO.votesAt v s)
    (hr : GridCO.resolvedBefore v o (GridCO.releaseTime q s) = true)
    (hk : GridCO.headSeat? o = some k)
    (hc : (GridCO.resolvedHead? v o).any (fun C => !Block.compatible C B) = true) :
    k ∈ transferReleaseSeats q v s B := by
  dsimp only [transferReleaseSeats]
  simp only [List.mem_toFinset, List.mem_filter, Bool.and_eq_true,
    Bool.not_eq_true', List.any_eq_true, GridCO.seatVotes, beq_iff_eq]
  refine ⟨?_, he, o, ⟨⟨ho, hr⟩, hk⟩, hc⟩
  exact List.mem_dedup.mpr (List.mem_filterMap.mpr
    ⟨o, List.mem_filter.mpr ⟨ho, hr⟩, hk⟩)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:673–699 (H.1 reverse relay); plan H-SUPPORT §4 step 4.
DC: SAME a pool whose members relay to the late pool, as themselves or as cap
evidence, can show an equivocation only when the late pool shows it. -/
theorem healing_support_equiv_back {n : Nat} (U L : List (GridCO.Wire n .root)) (k : Fin n)
    (hback : ∀ o ∈ U, ∀ seat, GridCO.headSeat? o = some seat →
      o ∈ L ∨ GridCO.equivocates L seat = true)
    (he : GridCO.equivocates U k = true) : GridCO.equivocates L k = true := by
  obtain ⟨u, hu, v, hv, hne, hku, hkv⟩ := (cap_pair U k).mp he
  rcases hback u hu k hku with hu' | h
  · rcases hback v hv k hkv with hv' | h
    · exact (cap_pair L k).mpr ⟨u, hu', v, hv', hne, hku, hkv⟩
    · exact h
  · exact h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:620–631 (IF.6, honest support), 673–676; plan H-SUPPORT §4 step 2 (G3).
DC: INTENTIONAL a clean early support of at least the release threshold has a seat with
an honest holder, because the faulty holders are fewer than the threshold. CStar maps
the label-s seats injectively to nodes. -/
private theorem transfer_support_card (v : GridCO.State p.n .root) (s : Slot) (B : Block) :
    SA.Root.prefixSupport p.toParams v s B =
      ((GridCO.seats p.n (GridCO.cleanSupport p.toParams.engine v s)).toFinset.filter
        (fun i => Gen.AC.Root.poolSupports (GridCO.resolutionTree v)
          (GridCO.cleanSupport p.toParams.engine v s) i B = true)).card := by
  rw [cleanSupport_domain_score]
  rw [Gen.AC.Root.vote_pool_score_card]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  rw [show GridCO.equivocates (GridCO.cleanSupport p.toParams.engine v s) i = false from
    fgsa_cleanSupport_no_equivocation p v s i, Bool.false_or]

theorem healing_support_honest_seat [Fintype V] (rho : V2.D.Run V (fgsa p c))
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hfault : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
    (v : GridCO.State p.n .root) (s : Slot) (B : Block)
    (hτ : SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams v s B) :
    ∃ k o, rho.seatOf (.base (.head s)) k ∈ rho.honest ∧
      o ∈ GridCO.cleanSupport p.toParams.engine v s ∧ GridCO.headSeat? o = some k ∧
      Gen.AC.Root.voteSupports (GridCO.resolutionTree v) B o = true := by
  classical
  let P := GridCO.cleanSupport p.toParams.engine v s
  let T := (GridCO.seats p.n P).toFinset.filter
    (fun i => Gen.AC.Root.poolSupports (GridCO.resolutionTree v) P i B = true)
  have hcard : SA.Root.prefixSupport p.toParams v s B = T.card := transfer_support_card v s B
  by_contra hn
  have hle : T.card ≤ (Gen.V2.Duty.faulty rho).card := by
    apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head s)))
    · intro k hk
      rw [Finset.mem_coe, Gen.V2.Duty.faulty_def]
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hh
      obtain ⟨_, hs⟩ := Finset.mem_filter.mp hk
      obtain ⟨o, ho, hk', hsup⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ k B).mp hs
      exact hn ⟨k, o, hh, ho, hk', hsup⟩
    · intro k _ j _ he
      exact (hC (.base (.head s)) trivial).injective he
  have ht : SA.releaseThreshold p.toParams = (p.n + 1) / 2 := rfl
  have hpos := p.nPos
  omega

private theorem transfer_stamp_read (st : State p.n) (t : Time) (K : Block)
    (hK : K ∈ st.base.blockStamp.map Prod.fst) :
    GridCO.stampBlock (actView (clockPre p st t)) K = GridCO.stampBlock st.base K := by
  change (((clockPre p _ _).base.blockStamp.find? _).map Prod.snd).getD _ = _
  rw [(clockPre_stamps p _ _).1]
  unfold GridCO.stampBlock
  cases he : st.base.blockStamp.find? (fun row => row.1 == K) with
  | none =>
    obtain ⟨row, hr, hh⟩ := List.mem_map.mp hK
    have hn := List.find?_eq_none.mp he row hr
    rw [hh, beq_self_eq_true] at hn
    contradiction
  | some row => rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:673–689 (H.1); plan H-SUPPORT §4 step 4.
DC: SAME a clean early vote at the honest source gate is a stored label-s vote. Its
target is a stored block of slot at most s, stamped strictly before e_s. -/
theorem healing_support_clean_target (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {i : Nat} {x : V} {s : Slot} (o : GridCO.Wire p.n .root)
    (ho : o ∈ GridCO.cleanSupport p.toParams.engine
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s) :
    ∃ K, GridCO.resolvedHead?
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) o = some K ∧
      K ∈ (storeAt p c E rho i x).base.blocks ∧
      GridCO.stampBlock (storeAt p c E rho i x).base K < SA.earlyTime p.toParams s ∧
      K.slot ≤ s ∧ o ∈ (storeAt p c E rho i x).base.votes ∧
      GridCO.headLabel? o = some s := by
  let v := actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
  change o ∈ (GridCO.earlyVotes p.toParams.engine v s).filter _ at ho
  obtain ⟨he, _⟩ := List.mem_filter.mp ho
  obtain ⟨hv, hr⟩ := List.mem_filter.mp he
  obtain ⟨hm, hl⟩ := List.mem_filter.mp hv
  have hl' : GridCO.headLabel? o = some s := by simpa only [beq_iff_eq] using hl
  have hm' : o ∈ (storeAt p c E rho i x).base.votes := by
    change o ∈ (clockPre p (storeAt p c E rho i x) _).base.votes at hm
    rwa [(Internal.clockPre_vn _ _).1] at hm
  unfold GridCO.resolvedBefore at hr
  cases ht : GridCO.resolvedHead? v o with
  | none => simp only [ht, Bool.false_eq_true] at hr
  | some K =>
    rw [ht] at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    obtain ⟨⟨hslot, _⟩, hstamp⟩ := hr
    have hK := resolvedHead_mem v o ht
    have hKb : K ∈ (storeAt p c E rho i x).base.blocks := by
      have h := ((actView_blocks _ K).mp hK).1
      rwa [(clockPre_fields p _ _).2.1] at h
    have hkeys : K ∈ (storeAt p c E rho i x).base.blockStamp.map Prod.fst := by
      change K ∈ (V2.D.Run.stateBefore E rho i x).st.base.blockStamp.map Prod.fst
      rw [(storeBundle_stateBefore E rho i x).«meta».stampKeys]
      exact hKb
    rw [transfer_stamp_read _ _ K hkeys] at hstamp
    refine ⟨K, rfl, hKb, hstamp, ?_, hm', hl'⟩
    simpa only [hl', Option.getD_some] using hslot

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:620–631 (IF.6), 673–676; plan H-SUPPORT §4 step 2 (G3).
DC: SAME a stored label-s vote of an honest holder is its own HEAD: the holder ticks at
v_s and the target is the HEAD of its post-clock state. -/
theorem healing_support_honest_head_joined (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) {i : Nat} {x : V} {s : Slot} {k : Fin p.n}
    {o : GridCO.Wire p.n .root} (ho : o ∈ (storeAt p c E rho i x).base.votes)
    (hl : GridCO.headLabel? o = some s) (hk : GridCO.headSeat? o = some k)
    (hh : rho.seatOf (.base (.head s)) k ∈ rho.honest) :
    ∃ j, rho.events[j]? = some (.tick (rho.seatOf (.base (.head s)) k)
        (SA.voteTime p.toParams s)) ∧
      GridCO.headTarget? o = some (headVote p (FGSA.clock p
        (V2.D.Run.stateBefore E rho j (rho.seatOf (.base (.head s)) k)).st
        (SA.voteTime p.toParams s)) s).root ∧
      joinedAt p E rho (rho.seatOf (.base (.head s)) k) s (SA.voteTime p.toParams s) := by
  obtain ⟨K, rfl⟩ := transfer_vote_shape o s k hl hk
  change _ ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes at ho
  rw [← fgsa_vote_stamp_keys E rho i x] at ho
  obtain ⟨⟨w, stamp⟩, hv, hvEq⟩ := List.mem_map.mp ho
  dsimp only at hvEq
  subst w
  have hdelivery : ∃ (j : Nat) (parent : Obj p) (u : Time),
      rho.events[j]? = some (.deliver x parent u) ∧
      (parent = ofHead p ⟨.seat (.head s) k, K⟩ ∨
        (fgsa p c).carries parent (ofHead p ⟨.seat (.head s) k, K⟩)) := by
    rcases fgsa_vote_stamp_source_or_restart E rho i x s k K stamp hv with
      ⟨j, _, u, ha, _⟩ | ⟨j, _, wake, _, _, hr⟩
    · obtain ⟨parent, hd, hh⟩ := ha.1
      exact ⟨j, parent, u, hd, (fgsaHooks p c).handles_carries _ parent _ hh⟩
    · obtain ⟨q, _, parent, u, hd, hc⟩ :=
        fgsa_replayed_head_delivery_origin E rho j x wake s k K hr
      exact ⟨q, parent, u, hd, Or.inr hc⟩
  obtain ⟨j, parent, u, hd, hhandles⟩ := hdelivery
  have horigin : ∃ t, t ≤ u ∧ V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) k)
      (ofHead p ⟨.seat (.head s) k, K⟩) t := by
    rcases hhandles with hp | hc
    · subst parent
      exact hE.unforgeable x _ u ⟨j, hd⟩ _ hh rfl
    · exact hE.carried x parent u ⟨j, hd⟩ _ hc _ hh rfl
  obtain ⟨t, _, j', ht, he⟩ := horigin
  have he0 := he
  rw [(V2.D.Run.step_tick_eq E rho ht).2] at he
  obtain ⟨_, htime, _, _, hK⟩ := (fgsa_emits_head E rho _ _ t s k K).mp he
  subst htime
  exact ⟨j', ht, by rw [hK]; rfl, fgsa_joinedAt_of_emitted_head E rho hE ht he0⟩

theorem healing_support_honest_head (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) {i : Nat} {x : V} {s : Slot} {k : Fin p.n}
    {o : GridCO.Wire p.n .root} (ho : o ∈ (storeAt p c E rho i x).base.votes)
    (hl : GridCO.headLabel? o = some s) (hk : GridCO.headSeat? o = some k)
    (hh : rho.seatOf (.base (.head s)) k ∈ rho.honest) :
    ∃ j, rho.events[j]? = some (.tick (rho.seatOf (.base (.head s)) k)
        (SA.voteTime p.toParams s)) ∧
      GridCO.headTarget? o = some (headVote p (FGSA.clock p
        (V2.D.Run.stateBefore E rho j (rho.seatOf (.base (.head s)) k)).st
        (SA.voteTime p.toParams s)) s).root  := by
  obtain ⟨j, hj, he, _⟩ := healing_support_honest_head_joined E rho hE ho hl hk hh
  exact ⟨j, hj, he⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:689–692 (H.1 release), 620–631 (IF.6); plan H-SUPPORT §4 step 5
(G5).
DC: INTENTIONAL release LOWER bound. The clean early supporters of B at the honest source
gate are resolved and clean at the receiver's q_s release read, by forward and reverse
relay. Each one opposes a target that conflicts with B, so the count reaches the lease
level τ and the lease is released. `fgsa_release_bound` is the upper bound instead. -/
theorem healing_support_release_compat (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (_hDelta : E.Δ = p.Δ)
    (s : Slot) (_hSync : Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s)
      (SA.gateTime p.toParams s))
    {ix iy : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (_hix : rho.events[ix]? = some (.tick x (SA.gateTime p.toParams s)))
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hScope : FirstTransferScope E rho ix iy x y s)
    {B : Block}
    (hτ : SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s B)
    (hFB : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))).base.obligations, Block.Compatible row.1 B := by
  intro row hrow
  by_contra hrc
  let src := actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))
  let st0 := storeAt p c E rho iy y
  let st1 : State p.n := { st0 with
    base := GridCO.expire { st0.base with now := SA.releaseTime p.toParams s }
      (SA.releaseTime p.toParams s) }
  have hdst : FGSA.clock p st0 (SA.voteTime p.toParams (s + 1)) =
      onView (fun view => SA.Root.release p.toParams view s) st1 := by
    rw [transfer_vote_clock', transfer_vote_release,
      fgsa_release_clockPre st0 s hScope.receiverGuard]
  obtain ⟨_, hcount⟩ := healing_support_release_rows st0 s hScope.receiverGuard row hrow
  have hinv : CStoreInv p (FGSA.clock p st0 (SA.voteTime p.toParams (s + 1))) :=
    cstoreInv_clock p _ (cstoreInv_stateBefore E rho iy y) _
  have hlevel : row.2.1 = SA.releaseThreshold p.toParams := by
    obtain ⟨b, g, d⟩ := row
    exact hinv.leaseKeys.2 _ hrow
  have hsub : (GridCO.seats p.n (GridCO.cleanSupport p.toParams.engine src s)).toFinset.filter
      (fun i => Gen.AC.Root.poolSupports (GridCO.resolutionTree src)
        (GridCO.cleanSupport p.toParams.engine src s) i B = true) ⊆
      transferReleaseSeats p.toParams.engine (actView st1) s row.1 := by
    intro k hk
    obtain ⟨_, hs⟩ := Finset.mem_filter.mp hk
    obtain ⟨o, ho, hko, hsup⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ k B).mp hs
    obtain ⟨K, hK, hKm, hKst, hslot, _, hol⟩ := healing_support_clean_target E rho o ho
    have hBK : Block.Preceq B K := by
      rw [Gen.AC.Root.voteSupports_def, resolvedHead_target _ o hK] at hsup
      exact (Bool.and_eq_true_iff.mp hsup).2
    have hFK : Block.Preceq (eraseFG st0.fg.F) K := Gen.Pure.block_preceq_trans hFB hBK
    have hFK' : Block.Preceq (eraseFG (((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
        (SA.voteTime p.toParams (s + 1))).st).fg.F) K := by
      change Block.Preceq (eraseFG (FGSA.clock p st0 _).fg.F) K
      rw [clock_fg]
      exact hFK
    obtain ⟨Kfg, hKe, hpath⟩ := healing_support_target_path_on (hroots := hroots)
      E rho hE.toScheduleWellFormed hy hiy (transfer_freeze_epoch E rho hScope) K
      (hScope.targets K hKm hKst hFK)
    have hcl := fgsa_cleanSupport_seat_clean_late p src s o ho k hko
    rcases fgsa_cleanSupport_vote_forward_on_receipt E rho hE s ix iy x y hy o ho k hko
      (fun b he => hScope.forward k b (he ▸ ho))
      with ⟨hod, hst⟩ | heq
    · have hod' : o ∈ st0.base.votes := by
        change o ∈ (FGSA.clock p st0 _).base.votes at hod
        rwa [(clock_vn st0 _).1] at hod
      have hKfg := hpath Kfg (KitFG.preceq_refl Kfg)
      have hKb : K ∈ (actView st1).blocks := by
        apply (actView_blocks st1 K).mpr
        refine ⟨?_, Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K) hFK⟩
        have hb := (hinv.baseTree (eraseFG Kfg)).mpr ⟨Kfg, hKfg.1, rfl⟩
        rw [clock_base_blocks, hKe] at hb
        exact hb
      have hdomain : GridCO.resolutionTree (actView st1) = st0.base.blocks := by
        rw [actView_resolutionTree]
        change st0.base.headDomain.getD st0.base.blocks = st0.base.blocks
        rw [show st0.base.headDomain = none from
          base_headDomain_none p (reachable_stateBefore E rho iy y)]
        rfl
      have hlookup : Gen.AC.Root.resolvedTarget? (GridCO.resolutionTree (actView st1)) o =
          some K := by
        rw [hdomain]
        exact resolvedTarget_of_mem _ (baseBlocks_rootInj p st0
          (cstoreInv_stateBefore E rho iy y)) o (List.mem_filter.mp hKb).1
          (resolvedHead_root _ o hK)
      have hresolve := resolvedHead_of_lookup (actView st1) o hlookup hKb
      apply transfer_release_mem
      · cases he : GridCO.equivocates (GridCO.votesAt (actView st1) s) k with
        | false => rfl
        | true =>
          exfalso
          have hL := healing_support_equiv_back (GridCO.votesAt st0.base s) _ k
            (fun o' ho' seat hs' => transfer_raw_backward E rho hE hx hScope o' ho' seat hs') he
          change GridCO.equivocates (GridCO.lateVotes p.toParams.engine src s) k = true at hL
          rw [hcl] at hL
          contradiction
      · exact List.mem_filter.mpr ⟨hod', by simpa only [beq_iff_eq] using hol⟩
      · unfold GridCO.resolvedBefore
        rw [hresolve]
        have hsv : GridCO.stampVote (actView st1) o =
            GridCO.stampVote (FGSA.clock p st0 (SA.voteTime p.toParams (s + 1))).base o := by
          rw [hdst]
          rfl
        have hsb : GridCO.stampBlock (actView st1) K =
            GridCO.stampBlock (FGSA.clock p st0 (SA.voteTime p.toParams (s + 1))).base K := by
          rw [hdst]
          rfl
        have hfr : SA.freezeTime p.toParams s < GridCO.releaseTime p.toParams.engine s := by
          change 4 * p.Δ * (s : Int) + 3 * p.Δ < 4 * p.Δ * (s : Int) + 5 * p.Δ
          have hd := p.deltaPos
          linarith
        have hb2 := hKfg.2
        rw [hKe] at hb2
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨by simpa only [hol, Option.getD_some] using hslot, ?_⟩, ?_⟩
        · rw [hsv]
          exact lt_trans hst hfr
        · rw [hsb]
          exact lt_trans hb2 hfr
      · exact hko
      · rw [hresolve]
        change (!Block.compatible K row.1) = true
        cases hc : Block.compatible K row.1 with
        | false => rfl
        | true =>
          exfalso
          apply hrc
          change Block.compatible row.1 B = true
          unfold Block.compatible at hc ⊢
          rcases Bool.or_eq_true_iff.mp hc with h | h
          · exact Bool.or_eq_true_iff.mpr
              (Or.inr (Gen.Pure.block_preceq_trans hBK h))
          · exact Bool.or_eq_true_iff.mpr
              (Gen.Pure.block_preceq_total_of_common h hBK)
    · exfalso
      have hL := healing_support_equiv_back _ _ k
        (fgsa_headVotes_backward_relay_on_receipt E rho hE s ix iy x y hx
          (fun q b hb => hScope.backward q b (Or.inr hb))) heq
      change GridCO.equivocates (GridCO.lateVotes p.toParams.engine src s) k = true at hL
      rw [hcl] at hL
      contradiction
  have hle := Finset.card_le_card hsub
  rw [← transfer_release_card, ← transfer_support_card] at hle
  have hcount' : GridCO.releaseCount p.toParams.engine (actView st1) s row.1 < row.2.1 := hcount
  have hτ' : SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams src s B := hτ
  omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:673–699 (H.1), 748–783 (H.3 kept path); plan H-SUPPORT §4 steps
2–5.
DC: INTENTIONAL first transfer at q_s = v_(s+1) in a settled phase. One honest clean
supporter gives the HEAD witness W (F1+F2, via S0), so W and its ancestors are in the
receiver's frozen q_s domain; RXing (F-root) or the common J (top-J) puts Z and F below
W. If F covers B the HEAD covers B. Else F ⪯ B, each clean supporter relays (G4) and
the transfer counts hold. `hlease` is the lease premise of H.1: the fast arm discharges
it by release (G5), the slow arm by its window. -/
theorem healing_first_transfer_core (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (_mono : RMono p c E rho) (crossing : RXing p c E rho)
    (hE : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    {ΔF : Time} (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} (hhead : u ≤ SA.voteTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v)
    {ix : Nat} {x : V} (hx : x ∈ rho.honest)
    (hix : rho.events[ix]? = some (.tick x (SA.gateTime p.toParams s)))
    {B : Block} {k : Fin p.n} {o : GridCO.Wire p.n .root}
    (hkh : rho.seatOf (.base (.head s)) k ∈ rho.honest)
    (ho : o ∈ GridCO.cleanSupport p.toParams.engine
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s)
    (hko : GridCO.headSeat? o = some k)
    (hsup : Gen.AC.Root.voteSupports
      (GridCO.resolutionTree (actView (clockPre p (storeAt p c E rho ix x)
        (SA.gateTime p.toParams s)))) B o = true)
    (hmaj : GridCO.voterCount (GridCO.lateVotes p.toParams.engine
        (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s) <
      2 * GridCO.goldfishScore
        (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))).blocks
        (GridCO.cleanSupport p.toParams.engine
          (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s)
        (GridCO.cleanSupport p.toParams.engine
          (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s) B)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hScope : FirstTransferScope E rho ix iy x y s)
    (hv : SA.voteTime p.toParams (s + 1) ≤ v)
    (hlease : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B →
      ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
        (SA.voteTime p.toParams (s + 1))).base.obligations, Block.Compatible row.1 B)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    Block.Preceq B (headVote p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))) (s + 1)) := by
  have hS := hE.toScheduleWellFormed
  have hd := p.deltaPos
  let src := actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))
  let dst := FGSA.clock p (storeAt p c E rho iy y) (SA.voteTime p.toParams (s + 1))
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hsync (fgsaDelay_nonrow E.Δ _) (hgst.trans hhead) hvd (hgate.trans hphase.2.1)
  -- The honest supporter and its HEAD witness (G3; F1 + F2 through S0).
  obtain ⟨K, hK, hKm, _, _, hom, hol⟩ := healing_support_clean_target E rho o ho
  have hBK : Block.Preceq B K := by
    rw [Gen.AC.Root.voteSupports_def, resolvedHead_target _ o hK] at hsup
    exact (Bool.and_eq_true_iff.mp hsup).2
  obtain ⟨jz, hjz, hKz, hSourceJoin⟩ := healing_support_honest_head_joined E rho hE hom hol hko hkh
  have hRoot := Option.some.inj ((resolvedHead_root _ o hK).symm.trans hKz)
  have hKheld := headVote_stored p _
    (cstoreInv_clock p _ (cstoreInv_stateBefore E rho jz (rho.seatOf (.base (.head s)) k))
      (SA.voteTime p.toParams s)) s
  rw [clock_base_blocks] at hKheld
  have hKeq := stored_block_eq_of_root_eq E rho (hroots.toNamedRootCollisionFree E rho) ix jz x
    (rho.seatOf (.base (.head s)) k) hKm hKheld hRoot
  have hvs : SA.voteTime p.toParams s + p.Δ ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  obtain ⟨Kfg, hKfull, hKe, W, hW, hKW, hloW, hrelay⟩ :=
    healing_head_witness_relay_on (hroots := hroots)
      p c E rho crossing hE hkh hjz hy ((hScope.carriersOn hE hy hiy (hgst.trans hhead)
        jz _ hkh hjz hSourceJoin).relay
        (healing_head_carrier_demand_phase p c E rho crossing hE hphase
          hkh hjz hhead (hvs.trans hgate) hy))
  have hKe2 : eraseFG Kfg = K := hKe.trans hKeq.symm
  have hBW : Block.Preceq B (eraseFG W) := by
    refine Gen.Pure.block_preceq_trans hBK ?_
    rw [← hKe2]
    exact eraseFG_preceq hKW
  have hZK : FGBlock.Preceq (FGSA.controls p ((fgsa p c).clock (rho.stateBefore E jz
      (rho.seatOf (.base (.head s)) k)) (SA.voteTime p.toParams s)).st).Z Kfg :=
    ((KitFG.mem_filteredFromView _ _ _ _).mp hKfull).2.2.1
  have hRz : FGSA.controls p ((fgsa p c).clock (rho.stateBefore E jz
      (rho.seatOf (.base (.head s)) k)) (SA.voteTime p.toParams s)).st =
      R_at p c E rho jz (rho.seatOf (.base (.head s)) k) := by
    change KitFG.treeStoreControlsView (heightView p) (FGSA.clock p _ _).fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho jz _).fg
    rw [clock_fg]
    rfl
  rw [hRz] at hZK hloW
  -- The settled frames at the source HEAD and at the receiver HEAD.
  have hvsv : SA.voteTime p.toParams s ≤ SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hfz := healing_settled_frame_strict p c E rho crossing u v m J contested hphase jz _
    (healing_support_idxBefore_le p c E rho hS hjz hhead)
    (healing_phase_lt_timeIdx p c E rho hS hjz (hvsv.trans hv)).le hkh
  have hfy := healing_settled_frame_strict p c E rho crossing u v m J contested hphase iy y
    (healing_support_idxBefore_le p c E rho hS hiy (hhead.trans hvsv))
    (healing_phase_lt_timeIdx p c E rho hS hiy hv).le hy
  have hes : SA.voteTime p.toParams s + p.Δ ≤ SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hWd : W ∈ (storeAt p c E rho
      (V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + p.Δ)) y).fg.TF := by
    have h := hrelay W (KitFG.preceq_refl W)
    change W ∈ (V2.D.Run.stateBefore E rho _ y).st.fg.TF
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    exact h
  have hWy : W ∈ (storeAt p c E rho iy y).fg.TF :=
    (fgsa_store_durable p c E rho
      (healing_support_idxBefore_le p c E rho hS hiy hes) y).1 hWd
  have hloy : (R_at p c E rho iy y).lo ≤ (heightView p W).h := by
    have e1 : (R_at p c E rho iy y).lo = (R_at p c E rho jz _).lo :=
      hfy.2.2.1.trans hfz.2.2.1.symm
    rw [e1]
    exact hloW
  have hZFy : FGBlock.Preceq (R_at p c E rho iy y).Z W ∧
      FGBlock.Preceq (storeAt p c E rho iy y).fg.F W := by
    cases J with
    | some J0 =>
      obtain ⟨_, _, hZy, _, _, hFJ⟩ := hfy.2.2.2.1
      obtain ⟨_, _, hZz, _, _, _⟩ := hfz.2.2.2.1
      have hZW : FGBlock.Preceq J0 W := by
        rw [← hZz]
        exact KitFG.preceq_trans hZK hKW
      refine ⟨?_, KitFG.preceq_trans hFJ hZW⟩
      change FGBlock.Preceq (FGSA.controls p (storeAt p c E rho iy y)).Z W
      rw [hZy]
      exact hZW
    | none =>
      obtain ⟨_, hZy, ⟨Kc, hKc, hKcF, hKclt⟩, _⟩ := hfy.2.2.2.1
      have hFW := crossing iy iy y y Kc W hy le_rfl hKc hKcF ⟨hy, hWy⟩
        (lt_of_lt_of_le hKclt hloy)
      refine ⟨?_, hFW⟩
      change FGBlock.Preceq (FGSA.controls p (storeAt p c E rho iy y)).Z W
      rw [hZy]
      exact hFW
  -- The receiver HEAD.
  have hinv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho iy y) _
  have hdfg : dst.fg = (storeAt p c E rho iy y).fg := clock_fg p _ _
  have hRd : FGSA.controls p dst = R_at p c E rho iy y := by
    change KitFG.treeStoreControlsView (heightView p) dst.fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho iy y).fg
    rw [hdfg]
  have hWdst : W ∈ dst.fg.TF := hdfg ▸ hWy
  have hFW' : Block.Preceq (eraseFG dst.fg.F) (eraseFG W) := by
    rw [hdfg]
    exact eraseFG_preceq hZFy.2
  by_cases hBF : Block.Preceq B (eraseFG dst.fg.F)
  · exact preceq_headVote_of_preceq_F p dst hinv hBF (Nat.succ_pos s)
  have hFB : Block.Preceq (eraseFG dst.fg.F) B := by
    rcases Gen.Pure.block_preceq_total_of_common hFW' hBW with h | h
    · exact h
    · exact absurd h hBF
  have hFB0 : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B := hdfg ▸ hFB
  -- The kept path: W and its ancestors are in the frozen q_s domain (F4).
  have hread : postClock E rho y (SA.voteTime p.toParams (s + 1)) =
      some ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
        (SA.voteTime p.toParams (s + 1))) := by
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hiy]
    rfl
  have hdpos : 0 < SA.voteTime p.toParams s + p.Δ := by
    change 0 < 4 * p.Δ * (s : Int) + p.Δ + p.Δ
    positivity
  have hdfreeze : SA.voteTime p.toParams s + p.Δ ≤ SA.freezeTime p.toParams (s + 1 - 1) := by
    rw [Nat.add_sub_cancel]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    linarith
  have hfrozen := healing_frozen_path_on p c E rho hS hdpos hes hdfreeze hWd hread (by
    intro i hi
    have he : i = iy := by
      have h1 := fgsa_tickIdx_of_event p c E rho hS hi
      have h2 := fgsa_tickIdx_of_event p c E rho hS hiy
      exact Option.some.inj (h1.symm.trans h2)
    have hed : SA.voteTime p.toParams s + p.Δ = SA.earlyTime p.toParams s := by
      change 4 * p.Δ * (s : Int) + p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 2 * p.Δ
      ring
    simpa only [he, hed] using hScope.epoch)
  have hpath : ∀ C, Block.Prec (liveRoot p dst) C → Block.Preceq C B →
      C ∈ erasedList dst (filteredFrom p.E p.cfg (FGSA.controls p dst)
        (voterBlocks p dst (s + 1))) := by
    intro C hr hCB
    have hr' : liveRoot p dst ≠ C ∧ Block.Preceq (liveRoot p dst) C := by
      change ((!decide (liveRoot p dst = C)) && Block.preceq (liveRoot p dst) C) = true at hr
      simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Block.Preceq] using hr
    obtain ⟨A, hA, heA, hAW⟩ :=
      eraseFG_ancestor_preceq hinv.fg.closed hWdst (Gen.Pure.block_preceq_trans hCB hBW)
    have hFA : FGBlock.Preceq dst.fg.F A := transfer_lift'
      (Gen.Pure.block_preceq_trans (F_preceq_liveRoot p dst hinv) (heA ▸ hr'.2))
    have hZA : FGBlock.Preceq (FGSA.controls p dst).Z A := transfer_lift'
      (Gen.Pure.block_preceq_trans (fgsa_Z_preceq_liveRoot p dst) (heA ▸ hr'.2))
    apply List.mem_filter.mpr
    refine ⟨(hinv.baseTree C).mpr ⟨A, hA, heA⟩, decide_eq_true ⟨A, ?_, heA⟩⟩
    rw [KitFG.filteredFrom_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
    exact (KitFG.mem_filteredFromView (heightView p) (FGSA.controls p dst) _ A).mpr
      ⟨hfrozen A hFA hAW, hFA, hZA, W,
        hfrozen W (hdfg ▸ hZFy.2) (KitFG.preceq_refl W), hAW, hRd ▸ hloy⟩
  -- The live root is compatible with B (lease premise of H.1).
  have hrows := hlease hFB0
  have hanchor : Block.Compatible (liveRoot p dst) B := by
    have hselect := Gen.Pure.foldl_select_mem (fun (best b : Block) =>
      best.depth < b.depth || (best.depth == b.depth && best.root < b.root))
      (dst.base.obligations.filterMap (fun row =>
        if dst.base.now < row.2.2 && decide (∃ X ∈ FGSA.fullTree p dst, eraseFG X = row.1)
        then some row.1 else none)) (eraseFG (FGSA.controls p dst).Z)
    change FGSA.liveRoot p dst = _ ∨ FGSA.liveRoot p dst ∈ _ at hselect
    rcases hselect with he | hm
    · rw [he]
      exact Gen.Pure.block_compatible_of_common (eraseFG_preceq (hRd ▸ hZFy.1)) hBW
    · obtain ⟨row, hr, hrow⟩ := List.mem_filterMap.mp hm
      split at hrow
      · rw [← Option.some.inj hrow]
        exact hrows row hr
      · contradiction
  -- Majority and rival dominance at the receiver (C5 forward, C6 reverse relay; G4).
  have hforward : ∀ o ∈ GridCO.cleanSupport p.toParams.engine src s, ∀ seat,
      GridCO.headSeat? o = some seat → Gen.AC.Root.voteSupports src.blocks B o = true →
      (o ∈ FGSA.headSupport p dst (s + 1) ∧ Gen.AC.Root.voteSupports dst.base.blocks B o = true) ∨
        GridCO.equivocates (FGSA.headVotes p dst (s + 1)) seat = true := by
    intro o' ho' seat hs' hsup'
    obtain ⟨K', hK', hKm', hKst', _, _, _⟩ := healing_support_clean_target E rho o' ho'
    have hBK' : Block.Preceq B K' := by
      have hlookup := resolvedTarget_of_mem src.blocks
        (fun A hA C hC => baseBlocks_rootInj p _
          (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho ix x) _) A
          (List.mem_filter.mp hA).1 C (List.mem_filter.mp hC).1)
        o' (resolvedHead_mem _ o' hK') (resolvedHead_root _ o' hK')
      rw [Gen.AC.Root.voteSupports_def, hlookup] at hsup'
      exact (Bool.and_eq_true_iff.mp hsup').2
    obtain ⟨Kfg', hKe', hpath'⟩ := healing_support_target_path_on (hroots := hroots)
      E rho hS hy hiy (transfer_freeze_epoch E rho hScope) K'
      (hScope.targets K' hKm' hKst' (Gen.Pure.block_preceq_trans hFB0 hBK'))
    exact fgsa_cleanSupport_forward_relay_on_receipt E rho hE s hx hy hix hiy o' ho'
      seat hs' (fun b he => hScope.forward seat b (he ▸ ho')) Kfg' (hKe' ▸ hK') B
      (hKe' ▸ hBK') hpath' hFB
  have hc := Gen.AC.Root.transfer src.blocks dst.base.blocks
    (GridCO.cleanSupport p.toParams.engine src s) (GridCO.lateVotes p.toParams.engine src s)
    (FGSA.headVotes p dst (s + 1)) (FGSA.headSupport p dst (s + 1)) B
    (fun _ ho' => fgsa_early_subset_late p src s (List.mem_filter.mp ho').1)
    (fgsa_cleanSupport_seat_clean_late p src s) hforward
    (fgsa_headVotes_backward_relay_on_receipt E rho hE s ix iy x y hx
          (fun q b hb => hScope.backward q b (Or.inr hb)))
    (fgsa_headSupport_subset_headVotes E rho hE iy y s) hmaj
  rw [Gen.AC.Root.TransferBounds_def] at hc
  rw [fgsa_headVote_eq_filtered, ite_eq_right (Nat.succ_ne_zero s)]
  exact fgsa_headInTree_covers_of_transfer p dst _ _ _ B
    hanchor hpath hc.2.2.2.2.2.1 hc.2.2.2.2.2.2

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:673–699 (H.1, fast case p ≥ τ); plan H-SUPPORT §4 (S1 first HEAD
clause).
DC: INTENTIONAL the fast arm of PhaseBody gives the first transfer: every honest HEAD at
label s+1 inside the phase covers B. The fast test gives the honest supporter (G3) and the
release lower bound (G5); the genuine result gives the majority. This is only the s+1
clause of `Transfers`; see the H-SUPPORT report for the later clauses. -/
theorem healing_first_transfer_fast [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v)
    {x : V} (hx : x ∈ rho.honest) {nd : Node p}
    (hnd : postClock E rho x (SA.gateTime p.toParams s) = some nd)
    (hB : B ∈ (fastWriteAt nd.st s).getD [])
    {y : V} (hy : y ∈ rho.honest) (hv : SA.voteTime p.toParams (s + 1) ≤ v)
    (hScopes : ∀ ix iy,
      rho.events[ix]? = some (.tick x (SA.gateTime p.toParams s)) →
      rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
      FirstTransferScope E rho ix iy x y s)
    {H : Block} (hH : headAtLabel p c E rho y (s + 1) = some H) :
    Block.Preceq B H := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  -- The source gate tick.
  rw [postClock_def, preTick_def] at hnd
  cases hix' : V2.D.Run.tickIdx? rho x (SA.gateTime p.toParams s) with
  | none => rw [hix'] at hnd; cases hnd
  | some ix =>
  rw [hix'] at hnd
  have hix := V2.D.Run.tickIdx?_spec hix'
  have hnd' := Option.some.inj hnd
  subst hnd'
  have hGuard := fgsa_gate_joined_of_enabled E rho (by
    have hh := hH
    unfold headAtLabel at hh
    rw [postClock_def, preTick_def] at hh
    cases hi : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams (s + 1)) with
    | none => rw [hi] at hh; cases hh
    | some iy =>
      exact (hScopes ix iy hix (V2.D.Run.tickIdx?_spec hi)).sourceGuard)
  rw [healing_support_fastWrite p c E rho hS hix hGuard] at hB
  let src := actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))
  -- The fast set: a genuine result h ⪰ B and the fast test at B.
  unfold fastSet at hB
  cases hconf : SA.Root.confirmationFrom p.toParams (eraseFG (storeAt p c E rho ix x).fg.F) src
      s with
  | none => rw [hconf] at hB; exact absurd hB List.not_mem_nil
  | some h =>
  rw [hconf] at hB
  dsimp only at hB
  split at hB
  · exact absurd hB List.not_mem_nil
  obtain ⟨_, hb⟩ := List.mem_filter.mp hB
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hb
  obtain ⟨⟨_, hBh⟩, hτ⟩ := hb
  have hmaj : GridCO.voterCount (GridCO.lateVotes p.toParams.engine src s) <
      2 * GridCO.goldfishScore src.blocks (GridCO.cleanSupport p.toParams.engine src s)
        (GridCO.cleanSupport p.toParams.engine src s) B := by
    have hh : GridCO.voterCount (GridCO.lateVotes p.toParams.engine src s) <
        2 * GridCO.goldfishScore src.blocks (GridCO.cleanSupport p.toParams.engine src s)
          (GridCO.cleanSupport p.toParams.engine src s) h := by
      change (if _ then some _ else none) = some h at hconf
      split at hconf
      · have he := Option.some.inj hconf
        subst h
        have heq (C : Block) :
            GridCO.goldfishScoreOn (GridCO.resolutionTree src) src.blocks
              (GridCO.cleanSupport p.toParams.engine src s)
              (GridCO.cleanSupport p.toParams.engine src s) C =
            GridCO.goldfishScore src.blocks (GridCO.cleanSupport p.toParams.engine src s)
              (GridCO.cleanSupport p.toParams.engine src s) C :=
          actView_score p (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))
            (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho ix x) _)
            (by rw [clockPre_headDomain];
                exact base_headDomain_none p (reachable_stateBefore E rho ix x)) _ _ C
        rw [← heq _]
        assumption
      · contradiction
    have ha := Gen.AC.Root.goldfishScore_antitone src.blocks
      (GridCO.cleanSupport p.toParams.engine src s)
      (GridCO.cleanSupport p.toParams.engine src s) B h hBh
    omega
  -- The honest supporter (G3).
  obtain ⟨k, o, hkh, ho, hko, hsup⟩ :=
    healing_support_honest_seat rho hrec.base.cstar hrec.fault src s B hτ
  -- The receiver HEAD tick.
  unfold headAtLabel at hH
  rw [postClock_def, preTick_def] at hH
  cases hiy' : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams (s + 1)) with
  | none => rw [hiy'] at hH; cases hH
  | some iy =>
  rw [hiy'] at hH
  have hiy := V2.D.Run.tickIdx?_spec hiy'
  have hHeq := Option.some.inj hH
  subst hHeq
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) (hgst.trans hhead) hvd (hgate.trans hphase.2.1)
  exact healing_first_transfer_core (hroots := hrec.base.receiptIdealization)
    E rho mono crossing hE hDelta hrec.sync hgst hphase
    hhead hgate hx hix hkh ho hko hsup hmaj hy hiy
    (hScopes ix iy hix hiy) hv
    (fun hFB => healing_support_release_compat (hroots := hrec.base.receiptIdealization)
      E rho hE hDelta s hSync hx hy hix hiy
      (hScopes ix iy hix hiy) hτ hFB)

end AvailableChain.FGSA.Run
end
