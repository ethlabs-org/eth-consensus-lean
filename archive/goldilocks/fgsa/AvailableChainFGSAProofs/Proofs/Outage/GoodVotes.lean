module
public import AvailableChainFGSAProofs.Proofs.Shared.Release
public import AvailableChainFGSAProofs.Proofs.Outage.GateCount
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceSleep
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingReceipt

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

omit [DecidableEq V] in
open scoped Classical in
private theorem outage_joinedHonest_unfold (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (t : Time) :
    joinedHonest p E rho t = rho.honest.filter
      (fun v => joinedAt p E rho v (slotAt p t) t) := rfl

/-- The good seats are exactly the joined honest voters outside W at this
label. The linked duty gives their exact cardinality. -/
theorem outage_good_seats (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (fast : Bool) (b₀ : Time) (r s : Slot) :
    ∃ H : Finset (Fin p.n),
      (∀ k, k ∈ H ↔ rho.seatOf (.base (.head s)) k ∈
        outageH p E rho s \ outageW p E rho fast b₀ r) ∧
      H.card = (outageH p E rho s \ outageW p E rho fast b₀ r).card := by
  classical
  let good := outageH p E rho s \ outageW p E rho fast b₀ r
  let seat : Fin p.n → V := rho.seatOf (.base (.head s))
  let H : Finset (Fin p.n) := Finset.univ.filter (fun k => seat k ∈ good)
  have hH : ∀ k, k ∈ H ↔ seat k ∈ good := by
    intro k
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
  have hbij : Function.Bijective seat := hC (.base (.head s)) trivial
  have himage : H.image seat = good := by
    ext y
    constructor
    · intro hy
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
      exact (hH k).mp hk
    · intro hy
      obtain ⟨k, rfl⟩ := hbij.surjective y
      exact Finset.mem_image.mpr ⟨k, (hH k).mpr hy, rfl⟩
  refine ⟨H, hH, ?_⟩
  change H.card = good.card
  rw [← himage, Finset.card_image_of_injective _ hbij.injective]

/-- Every stored honest HEAD was emitted by a joined voter. Thus a late
seat outside the good set maps into A union W, even at a restarted receiver.
No awake-all-receivers or global monotonicity premise is used. -/
theorem outage_late_opponent_bound [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (i : Nat) (x : V) (s : Slot) (fast : Bool) (b₀ : Time) (r : Slot)
    (H : Finset (Fin p.n))
    (hH : ∀ k, k ∈ H ↔ rho.seatOf (.base (.head s)) k ∈
      outageH p E rho s \ outageW p E rho fast b₀ r) :
    let v := actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    ((GridCO.seats p.n (GridCO.lateVotes p.toParams.engine v s)).toFinset \ H).card ≤
      (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card := by
  classical
  intro v
  apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head s)))
  · intro k hk
    obtain ⟨hl, hn⟩ := Finset.mem_sdiff.mp hk
    by_cases hh : rho.seatOf (.base (.head s)) k ∈ rho.honest
    · apply Finset.mem_union_right
      by_contra hw
      apply hn ((hH k).mpr (Finset.mem_sdiff.mpr ⟨?_, hw⟩))
      obtain ⟨o, ho, hs⟩ := (Gen.AC.Root.vote_pool_mem_seats _ k).mp hl
      have hlabel : GridCO.headLabel? o = some s :=
        beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp ho).1).2
      have hm : o ∈ (storeAt p c E rho i x).base.votes := by
        have hm := (List.mem_filter.mp (List.mem_filter.mp ho).1).1
        change o ∈ (clockPre p (storeAt p c E rho i x) _).base.votes at hm
        rw [(Internal.clockPre_vn _ _).1] at hm
        exact hm
      have hJ := fgsa_stored_honest_head_joined E rho hE i x s k o hm hlabel hs hh
      have hslot : slotAt p (SA.voteTime p.toParams s) = s :=
        slotOf_offset p s p.Δ p.deltaPos.le
          (by have hd := p.deltaPos; dsimp [Time] at *; omega)
      change rho.seatOf (.base (.head s)) k ∈ joinedHonest p E rho _
      simp only [outage_joinedHonest_unfold E rho, hslot, Finset.mem_filter]
      exact ⟨hh, hJ⟩
    · apply Finset.mem_union_left
      rw [Gen.V2.Duty.faulty_def]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hh⟩
  · intro k _ j _ he
    exact (hC (.base (.head s)) trivial).injective he

/-- E gives the exact good-seat majority and opponent bound for each
protected label. It applies to every receiver store, including W. Receipt
membership and compatible targets are separate joint-invariant obligations. -/
theorem outage_good_batch_of_e [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hBase : Base₂ p c E rho)
    {fast : Bool} {b₀ b₁ : Time} (hE : OutageE p E rho fast b₀ b₁) :
    ∃ r, FirstRestored p b₁ r ∧ ∀ s, r ≤ s → s ≤ r + p.k + 1 →
      ∃ H : Finset (Fin p.n),
        (∀ k, k ∈ H ↔ rho.seatOf (.base (.head s)) k ∈
          outageH p E rho s \ outageW p E rho fast b₀ r) ∧
        (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card < H.card ∧
        ∀ i x, let v := actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))
          ((GridCO.seats p.n (GridCO.lateVotes p.toParams.engine v s)).toFinset \ H).card ≤
            (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card := by
  obtain ⟨r, hr, hCount⟩ := hE
  refine ⟨r, hr, ?_⟩
  intro s hrs hsr
  obtain ⟨H, hH, hCard⟩ := outage_good_seats E rho hBase.cstar fast b₀ r s
  refine ⟨H, hH, hCard.symm ▸ hCount s hrs hsr, ?_⟩
  intro i x
  exact outage_late_opponent_bound E rho hBase.valid hBase.cstar i x s fast b₀ r H hH

/-- Before the first restored label, a good joined voter is covered by G.
This step uses membership in W, not a continuous-awake premise for all honest nodes. -/
theorem outage_good_covered (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {fast : Bool} {b₀ : Time} {r s : Slot} {y : V}
    (hy : y ∈ outageH p E rho s \ outageW p E rho fast b₀ r)
    (hb : b₀ ≤ SA.voteTime p.toParams s) (hsr : s ≤ r) :
    y ∈ coveredNodes p E rho fast b₀ := by
  classical
  obtain ⟨hH, hW⟩ := Finset.mem_sdiff.mp hy
  change y ∈ joinedHonest p E rho (SA.voteTime p.toParams s) at hH
  rw [outage_joinedHonest_unfold] at hH
  obtain ⟨hHonest, hJ⟩ := Finset.mem_filter.mp hH
  by_contra hn
  apply hW
  change y ∈ rho.honest.filter _
  exact Finset.mem_filter.mpr ⟨hHonest, hn, s, hb, hsr, hJ.1⟩

/-- The last Clean transfer supplies both target bounds at the pending gate.
The actual emission gives sender joinedness. The receiver may be in W. -/
theorem outage_pending_head_targets (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hvalid : V2.D.ExecutionValid E rho) {fast : Bool} {T b₀ : Time} {B : Block}
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hG : enabledGateAt p c E rho i x (l + 1)) (q : Fin p.n) (K : Block)
    (hy : rho.seatOf (.base (.head (l + 1))) q ∈ rho.honest)
    (hTarget : HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head (l + 1))) q)
      (ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩) (SA.voteTime p.toParams (l + 1)) K) :
    Block.Preceq B K ∧ Block.Preceq (F_at p c E rho i x) K := by
  have hs := hvalid.toScheduleWellFormed
  obtain ⟨k, hk, hem⟩ : V2.D.Run.emits E rho
      (rho.seatOf (.base (.head (l + 1))) q)
      (ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩)
      (SA.voteTime p.toParams (l + 1)) := by
    obtain ⟨k, _, _, hk, hem, _, _⟩ := hTarget
    exact ⟨k, hk, hem⟩
  have hK := headTargetAtEmission_at_tick E rho hs hTarget hk rfl
  have hDK := arming_head_ge_on hs htransfer hc.max_mem hy
    (fgsa_joinedAt_of_emitted_head E rho hvalid hk hem) hk
  change Block.Preceq D (headVote p (clock p (rho.stateBefore E k
    (rho.seatOf (.base (.head (l + 1))) q)).st (SA.voteTime p.toParams (l + 1)))
      (l + 1)) at hDK
  rw [← hK] at hDK
  exact ⟨block_preceq_trans hc.max_read hDK,
    block_preceq_trans (outage_pending_frame_below hs hc hx hG) hDK⟩

/-- Receipt services are requested only for the selected honest HEADs at this enabled gate.
The joint proof supplies their receiver floor; arbitrary HEADs in W are not requested. -/
structure OutageGateReceiptScope (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) (s : Slot) (H : Finset (Fin p.n)) : Prop where
  enabled : enabledGateAt p c E rho i x s
  receiverJoined : joinedAt p E rho x (s + 1) (SA.gateTime p.toParams s)
  readEpoch : V2.D.restartFree rho x (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) i
  services : ∀ q ∈ H, ∀ K, rho.seatOf (.base (.head s)) q ∈ rho.honest →
    HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
      (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
    Nonempty (FreshHeadService E rho s q K.root (SA.earlyTime p.toParams s) x) ∧
      TargetReceiptService E rho K (SA.earlyTime p.toParams s) x

/-- Restrict a produced full pending batch to the selected seats. This is a scope adapter. -/
theorem outage_gate_scope_of_shared {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {i : Nat} {x : V} {s : Slot} (h : GateReceiptScope E rho i x s)
    (H : Finset (Fin p.n)) : OutageGateReceiptScope E rho i x s H :=
  ⟨h.enabled, h.receiverJoined, h.readEpoch, fun q _ K hy hK => h.services q K hy hK⟩

/-- Selected good voters supply authentic targets and strict receipt stamps
at the actual gate. The receiver can be in W. The joint invariant must
supply the target and finality bounds; local receipt service supplies membership. -/
theorem outage_good_heads_at_gate (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hBase : Base₂ p c E rho) (i : Nat) (x : V) (s : Slot) (B : Block)
    (hx : x ∈ rho.honest) (H : Finset (Fin p.n))
    (hScope : OutageGateReceiptScope E rho i x s H)
    (hSelected : ∀ q ∈ H, rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s))
    (hTargets : ∀ q ∈ H, ∀ K, HeadTargetAtEmission p c E rho
      (rho.seatOf (.base (.head s)) q) (ofHead p ⟨.seat (.head s) q, K.root⟩)
        (SA.voteTime p.toParams s) K →
      Block.Preceq B K ∧ Block.Preceq (F_at p c E rho i x) K) :
    ∀ q ∈ H, ∃ K t,
      rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
      V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n) ∈
        (storeAt p c E rho i x).base.votes ∧
      K ∈ (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))).blocks ∧
      K.slot ≤ s ∧
      GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x)
        (SA.gateTime p.toParams s))) (baseVote ⟨.seat (.head s) q, K.root⟩) <
          GridCO.earlyTime p.toParams.engine s ∧
      GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x)
        (SA.gateTime p.toParams s))) K < GridCO.earlyTime p.toParams.engine s ∧
      Block.Compatible K B := by
  have hs := hBase.valid.toScheduleWellFormed
  have ht := hScope.enabled.1
  intro q hq
  obtain ⟨hy, hJ⟩ := hSelected q hq
  let y := rho.seatOf (.base (.head s)) q
  have hvh : SA.voteTime p.toParams s ≤ rho.horizon :=
    (fgsa_vote_lt_gate p s).le.trans (hs.in_horizon _ (List.mem_of_getElem? ht)).2
  have he : ((4 * s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams s := by
    change ((4 * s + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int) + p.Δ
    push_cast
    ring
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hs hBase.delta y hy (4 * s + 1)
    (he ▸ hvh) (he ▸ hJ.1)
  rw [he] at hk
  let K := headVote p (clock p (rho.stateBefore E k y).st (SA.voteTime p.toParams s)) s
  have hem : ofHead p ⟨.seat (.head s) q, K.root⟩ ∈ rho.emitsAt E k := by
    rw [(V2.D.Run.step_tick_eq E rho hk).2]
    exact (fgsa_emits_head E rho _ y _ s q K.root).mpr
      ⟨hJ.1, rfl, rfl, fgsa_head_joined_of_joinedAt E rho hs hk hJ, rfl⟩
  have hTarget : HeadTargetAtEmission p c E rho y
      (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K :=
    ⟨k, s, q, hk, hem, rfl, rfl⟩
  obtain ⟨hBK, hFK⟩ := hTargets q hq K hTarget
  obtain ⟨⟨hHead⟩, hBody⟩ := hScope.services q hq K hy hTarget
  have hrec := hHead.receipt hBase.valid hx hk hem
  have hblock := fgsa_target_receipt_on E rho hs hBase.receiptIdealization K
    (SA.earlyTime p.toParams s) x hx hBody
  have hstamp := fgsa_block_stamp_before_read E rho hs x (SA.earlyTime p.toParams s)
    (by change 0 < 4 * p.Δ * (s : Int) + 2 * p.Δ; have hd := p.deltaPos; positivity) K hblock
  have heg : SA.earlyTime p.toParams s < SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hid : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ i := by
    by_contra hn
    exact (not_lt_of_ge heg.le)
      ((Gen.V2.Duty.index_lt_idxBefore_iff hs ht _).mp (Nat.lt_of_not_ge hn))
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (SA.earlyTime p.toParams s) hs]
    at hrec hblock hstamp
  have hkeep := fgsa_gateReceipt_stamps_on E rho hid x hScope.readEpoch s
    (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) K hrec.1 hblock
  have hKg : K ∈ (actView (clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s))).blocks := by
    apply (actView_blocks _ K).mpr
    rw [(clockPre_fields p _ _).2.1, clockPre_fg]
    exact ⟨(fgsa_store_durable p c E rho hid x).2.1.subset hblock,
      Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K) hFK⟩
  refine ⟨K, SA.voteTime p.toParams s, hy, ⟨k, hk, hem⟩, hkeep.1, hKg,
    (arming_emitted_head_fields hs hTarget (by rw [toWire_ofHead]; rfl)).2,
    hkeep.2.1.trans_lt hrec.2, hkeep.2.2.trans_lt hstamp, ?_⟩
  exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K) hBK

/-- OUTPUT-DIRECT §7. DC: INTENTIONAL; instantiate the compatible-batch
count at the actual pre-gate active view. The sleep caller bounds the
complement by A union W. Authenticity gives resolved targets. Receipts stay explicit. -/
theorem outageV_gate_of_receipts {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (i : Nat) (x : V) (s : Slot) (B C : Block) (H : Finset (Fin p.n))
    (a : Nat) (hpart : a < H.card)
    (hrest : ((GridCO.seats p.n (GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s)).toFinset
        \ H).card ≤ a)
    (hheads : ∀ k ∈ H, ∃ K t,
      rho.seatOf (.base (.head s)) k ∈ rho.honest ∧
      V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) k)
        (ofHead p ⟨.seat (.head s) k, K.root⟩) t ∧
      baseVote (⟨.seat (.head s) k, K.root⟩ : HeadWire p.n) ∈
        (storeAt p c E rho i x).base.votes ∧
      K ∈ (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))).blocks ∧
      K.slot ≤ s ∧
      GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)))
        (baseVote (⟨.seat (.head s) k, K.root⟩ : HeadWire p.n)) <
          GridCO.earlyTime p.toParams.engine s ∧
      GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)))
        K < GridCO.earlyTime p.toParams.engine s ∧ Block.Compatible K B)
    (hresult : SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s = some C) :
    Block.Compatible C B := by
  let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
  let v := actView pre
  have hstore : CStoreInv p pre := cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x) _
  have hd : pre.base.headDomain = none := by
    rw [clockPre_headDomain]
    exact base_headDomain_none p (reachable_stateBefore E rho i x)
  have hraw : GridCO.cleanSupport p.toParams.engine v s ⊆ GridCO.lateVotes p.toParams.engine v s :=
    fun _ ho => fgsa_early_subset_late p v s (List.mem_filter.mp ho).1
  apply outageV_gate_of_compatible_batch p.toParams.engine v (eraseFG pre.fg.F) B C s H
    a ?_ hraw hrest hpart
    (fun k _ => fgsa_cleanSupport_no_equivocation p v s k) ?_ hresult
  · intro k hk
    obtain ⟨K, t, hh, he, hv, hK, hslot, hvs, hbs, _⟩ := hheads k hk
    have hsupp := fgsa_active_support_of_receipt E rho hE i x s k K K t
      hh he hv hK hslot hvs hbs (Gen.Pure.block_preceq_refl K)
    obtain ⟨o, ho, hseat, _⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ k K).mp hsupp
    exact (Gen.AC.Root.vote_pool_mem_seats _ k).mpr ⟨o, hraw ho, hseat⟩
  · intro o ho k hk hseat X hX
    obtain ⟨K, t, hh, he, _, hK, _, _, _, hKB⟩ := hheads k hk
    have hl : GridCO.headLabel? o = some s :=
      beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp (List.mem_filter.mp ho).1).1).2
    have hm : o ∈ (storeAt p c E rho i x).base.votes := by
      have hm := (List.mem_filter.mp (List.mem_filter.mp (List.mem_filter.mp ho).1).1).1
      change o ∈ pre.base.votes at hm
      rw [(Internal.clockPre_vn _ _).1] at hm
      exact hm
    have heq := fgsa_honest_head_eq_of_stored E rho hE i x s k K.root t hh he o hm hl hseat
    rw [heq] at hX
    have hresolve : Gen.AC.Root.resolvedTarget? (GridCO.resolutionTree v)
        (baseVote (⟨.seat (.head s) k, K.root⟩ : HeadWire p.n)) = some K := by
      rw [actView_resolutionTree]
      change Gen.AC.Root.resolvedTarget? (pre.base.headDomain.getD pre.base.blocks) _ = _
      rw [hd]
      exact resolvedTarget_of_mem _ (baseBlocks_rootInj p pre hstore) _
        (List.mem_filter.mp hK).1 rfl
    have hXK : X = K := Option.some.inj (hX.symm.trans hresolve)
    exact hXK.symm ▸ hKB

/-- Compatible good targets and exact local service instantiate the actual
gate count. The opponent bound is supplied by outage_late_opponent_bound. -/
theorem outageV_gate_of_good_service (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hBase : Base₂ p c E rho) (i : Nat) (x : V) (s : Slot) (B C : Block)
    (hx : x ∈ rho.honest) (H : Finset (Fin p.n))
    (hScope : OutageGateReceiptScope E rho i x s H) (a : Nat) (hpart : a < H.card)
    (hrest : ((GridCO.seats p.n (GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s)).toFinset
        \ H).card ≤ a)
    (hSelected : ∀ q ∈ H, rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s))
    (hTargets : ∀ q ∈ H, ∀ K, HeadTargetAtEmission p c E rho
      (rho.seatOf (.base (.head s)) q) (ofHead p ⟨.seat (.head s) q, K.root⟩)
        (SA.voteTime p.toParams s) K →
      Block.Preceq B K ∧ Block.Preceq (F_at p c E rho i x) K)
    (hresult : SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s = some C) :
    Block.Compatible C B :=
  outageV_gate_of_receipts E rho hBase.valid i x s B C H a hpart hrest
    (outage_good_heads_at_gate E rho hBase i x s B hx H hScope hSelected hTargets) hresult

/-- A write can only add one of its supplied targets. Old rows can remain
incompatible; this lemma promises compatibility only for new rows. -/
theorem outage_writeKeys_new_compatible {n : Nat} (keys : List (Block × Nat))
    (lim : Time) (st : GridCO.State n .root) (B : Block)
    (hkeys : ∀ key ∈ keys, Block.Compatible key.1 B) :
    ∀ row ∈ (GridCO.writeKeys st keys lim).obligations,
      row ∈ st.obligations ∨ Block.Compatible row.1 B := by
  induction keys generalizing st with
  | nil => exact fun row hr => Or.inl hr
  | cons key keys ih =>
    intro row hr
    rw [@GridCO.writeKeys_def GridCO.slowLeasePolicy, List.foldl_cons,
      ← @GridCO.writeKeys_def GridCO.slowLeasePolicy] at hr
    rcases ih (GridCO.writeObligation st key.1 key.2 lim)
      (fun k hk => hkeys k (List.mem_cons_of_mem _ hk)) row hr with hrow | hc
    · change row ∈ st.obligations.filter _ ++ [_] at hrow
      rcases List.mem_append.mp hrow with hold | hnew
      · exact Or.inl (List.mem_filter.mp hold).1
      · have he := List.mem_singleton.mp hnew
        rw [he]
        exact Or.inr (hkeys key (List.mem_cons_self ..))
    · exact Or.inr hc

/-- Every new gate lock is compatible when the passed result is compatible.
This local late-write step applies to every receiver store, including W;
the joint proof must still supply result compatibility at every actual gate. -/
theorem outage_gate_writeKeys_compatible {n : Nat} (params : GridCO.Params)
    (st : GridCO.State n .root) (s : Slot) (C B : Block) (lim : Time)
    (hCB : Block.Compatible C B) :
    ∀ row ∈ (GridCO.writeKeys st
      (@GridCO.gateWriteKeys GridCO.slowLeasePolicy .root params n st s C) lim).obligations,
      row ∈ st.obligations ∨ Block.Compatible row.1 B := by
  apply outage_writeKeys_new_compatible
  intro key hk
  rw [@GridCO.gateWriteKeys_def GridCO.slowLeasePolicy] at hk
  obtain ⟨X, hX, hk⟩ := List.mem_flatMap.mp hk
  obtain ⟨g, _, he⟩ := List.mem_map.mp hk
  subst key
  have hXC := (Bool.and_eq_true_iff.mp (List.mem_filter.mp hX).2).2
  exact Gen.Pure.block_compatible_of_preceq_compatible hXC hCB

/-- The late-write exclusion quantifies over every honest writer, including W.
Its remaining joint input is compatibility of each enabled late result. Old
rows can remain; this statement excludes conflicting targets in new write keys. -/
theorem outage_all_honest_late_gate_keys (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (r : Slot) (B : Block)
    (hResults : ∀ i x s C, x ∈ rho.honest → r < s →
      enabledGateAt p c E rho i x s → gateResultAt p c E rho i = some (some C) →
      Block.Compatible C B) :
    ∀ i x s C, x ∈ rho.honest → r < s → enabledGateAt p c E rho i x s →
      gateResultAt p c E rho i = some (some C) →
      ∀ key ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
        (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s C,
        Block.Compatible key.1 B := by
  intro i x s C hx hrs hG hC key hk
  rw [@GridCO.gateWriteKeys_def GridCO.slowLeasePolicy] at hk
  obtain ⟨X, hX, hk⟩ := List.mem_flatMap.mp hk
  obtain ⟨g, _, he⟩ := List.mem_map.mp hk
  subst key
  have hXC := (Bool.and_eq_true_iff.mp (List.mem_filter.mp hX).2).2
  exact Gen.Pure.block_compatible_of_preceq_compatible hXC (hResults i x s C hx hrs hG hC)

/-- Release opponents are in A union W. Every stored honest HEAD has an
actual joined emission, including replayed votes after a receiver restart.
Only the good senders need target compatibility. -/
theorem outage_good_release_bound [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hroots : NamedRootCollisionFree p c E rho)
    (fast : Bool) (b₀ : Time) (r s : Slot) (B : Block) (i : Nat) (x : V)
    (hheads : ∀ y ∈ outageH p E rho s \ outageW p E rho fast b₀ r,
      ∀ o t, V2.D.Run.emits E rho y o t →
      ∀ q K, o.auth = .seat (.base (.head s)) q →
        HeadTargetAtEmission p c E rho y o t K → Block.Compatible K B) :
    GridCO.releaseCount p.toParams.engine (actView (storeAt p c E rho i x)) s B ≤
      (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card := by
  apply fgsa_releaseCount_le_senders p.toParams.engine (actView (storeAt p c E rho i x))
    s B (rho.seatOf (.base (.head s)))
    (hC (.base (.head s)) trivial).injective
  intro k o ho _ hseat hconf
  by_cases hW : rho.seatOf (.base (.head s)) k ∈ outageW p E rho fast b₀ r
  · exact Finset.mem_union_right _ hW
  apply Finset.mem_union_left
  rw [Gen.V2.Duty.faulty_def]
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hhonest
  have hl : GridCO.headLabel? o = some s := by
    simpa only [beq_iff_eq] using (List.mem_filter.mp ho).2
  have hstored : o ∈ (storeAt p c E rho i x).base.votes :=
    (List.mem_filter.mp ho).1
  have hJ := fgsa_stored_honest_head_joined E rho hE i x s k o hstored hl hseat hhonest
  have hslot : slotAt p (SA.voteTime p.toParams s) = s :=
    slotOf_offset p s p.Δ p.deltaPos.le
      (by have := p.deltaPos; dsimp [Time] at *; omega)
  have hGood : rho.seatOf (.base (.head s)) k ∈
      outageH p E rho s \ outageW p E rho fast b₀ r := by
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hW⟩
    change rho.seatOf (.base (.head s)) k ∈ joinedHonest p E rho _
    simp only [outage_joinedHonest_unfold E rho, hslot, Finset.mem_filter]
    exact ⟨hhonest, hJ⟩
  obtain ⟨D, hresolve, hConflict⟩ : ∃ D,
      GridCO.resolvedHead? (actView (storeAt p c E rho i x)) o = some D ∧
      (!Block.compatible D B) = true := by
    cases hR : GridCO.resolvedHead? (actView (storeAt p c E rho i x)) o with
    | none => simp only [hR, Option.any_none, Bool.false_eq_true] at hconf
    | some D => exact ⟨D, rfl, by simpa only [hR, Option.any_some] using hconf⟩
  obtain ⟨auth, payload⟩ := o
  cases auth with
  | none => cases payload <;> change (none : Option Slot) = some s at hl <;> contradiction
  | proposer r => cases payload <;> change (none : Option Slot) = some s at hl <;> contradiction
  | seat r j =>
    cases payload with
    | proposal C raw support =>
        change (none : Option Slot) = some s at hl
        contradiction
    | head C =>
      have hrs : r = s := Option.some.inj hl
      have hjk : j = k := Option.some.inj hseat
      subst r; subst j
      have hv := hstored
      change _ ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes at hv
      rw [← fgsa_vote_stamp_keys E rho i x] at hv
      obtain ⟨⟨wire, stamp⟩, hv, he⟩ := List.mem_map.mp hv
      dsimp only at he
      subst wire
      have horigin : ∃ (j : Nat) (parent : Obj p) (u : Time),
          rho.events[j]? = some (.deliver x parent u) ∧
          (parent = ofHead p ⟨.seat (.head s) k, C⟩ ∨
            (fgsa p c).carries parent (ofHead p ⟨.seat (.head s) k, C⟩)) := by
        rcases fgsa_vote_stamp_source_or_restart E rho i x s k C stamp hv with
          ⟨j, _, u, ha, _⟩ | ⟨j, _, wake, _, _, hr⟩
        · obtain ⟨parent, hd, hh⟩ := ha.1
          exact ⟨j, parent, u, hd, (fgsaHooks p c).handles_carries _ parent _ hh⟩
        · obtain ⟨j', _, parent, u, hd, hc⟩ :=
            fgsa_replayed_head_delivery_origin E rho j x wake s k C hr
          exact ⟨j', parent, u, hd, Or.inr hc⟩
      obtain ⟨j, parent, u, hd, hc⟩ := horigin
      have hem : ∃ t, t ≤ u ∧ V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) k)
          (ofHead p ⟨.seat (.head s) k, C⟩) t := by
        rcases hc with rfl | hc
        · exact hE.unforgeable x _ u ⟨j, hd⟩ _ hhonest rfl
        · exact hE.carried x parent u ⟨j, hd⟩ _ hc _ hhonest rfl
      obtain ⟨u, _, hem⟩ := hem
      obtain ⟨H, hH⟩ := headTargetAtEmission_exists E rho hem rfl
      have hcompat := hheads _ hGood _ u hem k H rfl hH
      have hCH : C = H.root := by
        obtain ⟨_, _, _, _, _, ho, _⟩ := hH
        exact Msg.head.inj (congrArg (fun o : Obj p => o.payload) ho)
      have hTarget : GridCO.headTarget? (⟨.seat s k, .head C⟩ : GridCO.Wire p.n .root) =
          some H.root := congrArg some hCH
      have hDH := headTargetAtEmission_receiver_eq E rho hroots hH i x
        (actView (storeAt p c E rho i x)) ⟨.seat s k, .head C⟩
        (fun _ h => (List.mem_filter.mp h).1) hTarget hresolve
      rw [hDH, show Block.compatible H B = true from hcompat] at hConflict
      contradiction

/-- Finality coverage suffices at an enabled gate, with no receipt or count input. -/
theorem outage_finalized_gate_result (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {s : Slot} {B C : Block}
    (hG : enabledGateAt p c E rho i x s) (hBF : Block.Preceq B (F_at p c E rho i x))
    (hresult : gateResultAt p c E rho i = some (some C)) : Block.Preceq B C := by
  have hraw := inclusion_gate_raw_at_tick E rho hs hG
  have hC := Option.some.inj (hraw.symm.trans hresult)
  rw [clockPre_fg] at hC
  change GridCO.confirmationFrom p.toParams.engine (F_at p c E rho i x)
    (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s = some C at hC
  have hext := outageV_result_extends_anchor p.toParams.engine
    (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)))
    (F_at p c E rho i x) C s hC
  exact Gen.Pure.block_preceq_trans hBF hext

/-- A finalized receiver uses the walk anchor. Otherwise good targets must cover B.
The count is used only in the F below B branch, at the actual enabled receiver. -/
theorem outageV_gate_of_good_service_scoped (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hBase : Base₂ p c E rho)
    (i : Nat) (x : V) (s : Slot) (B C : Block) (hx : x ∈ rho.honest)
    (hG : enabledGateAt p c E rho i x s)
    (hFB : Block.Compatible (F_at p c E rho i x) B)
    (H : Finset (Fin p.n)) (a : Nat) (hpart : a < H.card)
    (hrest : ((GridCO.seats p.n (GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s)).toFinset
        \ H).card ≤ a)
    (hSelected : ∀ q ∈ H, rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s))
    (hScope : Block.Preceq (F_at p c E rho i x) B → OutageGateReceiptScope E rho i x s H)
    (hTargets : Block.Preceq (F_at p c E rho i x) B → ∀ q ∈ H, ∀ K,
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
      Block.Preceq B K)
    (hresult : gateResultAt p c E rho i = some (some C)) : Block.Compatible C B := by
  have hraw := inclusion_gate_raw_at_tick E rho hBase.valid.toScheduleWellFormed hG
  have hC := Option.some.inj (hraw.symm.trans hresult)
  by_cases hBF : Block.Preceq B (F_at p c E rho i x)
  · exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl C)
      (outage_finalized_gate_result E rho hBase.valid.toScheduleWellFormed hG hBF hresult)
  have hlow : Block.Preceq (F_at p c E rho i x) B := by
    rcases Bool.or_eq_true_iff.mp hFB with h | h
    · exact h
    · exact (hBF h).elim
  exact outageV_gate_of_good_service E rho hBase i x s B C hx H (hScope hlow)
    a hpart hrest hSelected (fun q hq K hK =>
      ⟨hTargets hlow q hq K hK, Gen.Pure.block_preceq_trans hlow (hTargets hlow q hq K hK)⟩)
    hC

/-- Fresh HEAD receipts supply the late denominator even when the target body is
below the receiver floor. Only resolved good targets need compatibility. -/
theorem outageV_gate_of_emitted_heads (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hBase : Base₂ p c E rho)
    (i : Nat) (x : V) (s : Slot) (B C : Block) (H : Finset (Fin p.n))
    (a : Nat) (hpart : a < H.card)
    (hrest : ((GridCO.seats p.n (GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s)).toFinset
        \ H).card ≤ a)
    (hheads : ∀ q ∈ H, ∃ K,
      rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K ∧
      baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n) ∈
        (storeAt p c E rho i x).base.votes ∧
      GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x)
        (SA.gateTime p.toParams s))) (baseVote ⟨.seat (.head s) q, K.root⟩) <
          GridCO.gateTime p.toParams.engine s ∧ Block.Compatible K B)
    (hresult : gateResultAt p c E rho i = some (some C))
    (hG : enabledGateAt p c E rho i x s) : Block.Compatible C B := by
  let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
  let v := actView pre
  have hraw : GridCO.cleanSupport p.toParams.engine v s ⊆
      GridCO.lateVotes p.toParams.engine v s := fun _ ho =>
    fgsa_early_subset_late p v s (List.mem_filter.mp ho).1
  have hC := Option.some.inj
    ((inclusion_gate_raw_at_tick E rho hBase.valid.toScheduleWellFormed hG).symm.trans hresult)
  apply outageV_gate_of_compatible_batch p.toParams.engine v (eraseFG pre.fg.F) B C s H
    a ?_ hraw hrest hpart
    (fun q _ => fgsa_cleanSupport_no_equivocation p v s q) ?_ hC
  · intro q hq
    obtain ⟨K, _, _, hv, ht, _⟩ := hheads q hq
    apply (Gen.AC.Root.vote_pool_mem_seats _ q).mpr
    refine ⟨baseVote ⟨.seat (.head s) q, K.root⟩, ?_, rfl⟩
    apply List.mem_filter.mpr
    refine ⟨List.mem_filter.mpr ⟨?_, beq_self_eq_true _⟩, decide_eq_true ht⟩
    change _ ∈ pre.base.votes
    rw [(Internal.clockPre_vn _ _).1]
    exact hv
  · intro o ho q hq hseat X hX
    obtain ⟨K, hh, hK, _, _, hKB⟩ := hheads q hq
    obtain ⟨k, hk, hm⟩ : V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) := by
      obtain ⟨k, _, _, hk, hm, _, _⟩ := hK
      exact ⟨k, hk, hm⟩
    have hl : GridCO.headLabel? o = some s :=
      beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp (List.mem_filter.mp ho).1).1).2
    have hv : o ∈ (storeAt p c E rho i x).base.votes := by
      have hv := (List.mem_filter.mp (List.mem_filter.mp (List.mem_filter.mp ho).1).1).1
      change o ∈ pre.base.votes at hv
      rwa [(Internal.clockPre_vn _ _).1] at hv
    have heq := fgsa_honest_head_eq_of_stored E rho hBase.valid i x s q K.root
      (SA.voteTime p.toParams s) hh ⟨k, hk, hm⟩ o hv hl hseat
    rw [heq, actView_resolutionTree] at hX
    have hd : pre.base.headDomain = none := by
      rw [clockPre_headDomain]
      exact base_headDomain_none p (reachable_stateBefore E rho i x)
    change Block.findByRoot? (pre.base.headDomain.getD pre.base.blocks) K.root = some X at hX
    rw [hd] at hX
    have hXm := Block.findByRoot?_mem hX
    change X ∈ pre.base.blocks at hXm
    rw [(clockPre_fields p _ _).2.1] at hXm
    obtain ⟨j, hKm⟩ := headTargetAtEmission_stored E rho hK
    have hXK := stored_block_eq_of_root_eq E rho hBase.idealization i j x
      (rho.seatOf (.base (.head s)) q) hXm hKm (Block.findByRoot?_root hX)
    exact hXK.symm ▸ hKB

end AvailableChain.FGSA.Run
end
