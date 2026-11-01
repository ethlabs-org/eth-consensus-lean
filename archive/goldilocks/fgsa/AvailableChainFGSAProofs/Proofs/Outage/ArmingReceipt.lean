module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingArith
public import AvailableChainFGSAProofs.Proofs.Shared.HeadAdmit -- shake: keep (source declarations)
public import AvailableChainFGSAClaims.Statements.OutageSleep -- shake: keep (source declarations)

public section

/-! Local full-batch receipt kernel. This module does not import ArmingPending.
The public prefix theorem can consume it from ArmingPending at closure. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Authentic emitted HEAD targets have the signed root and a current-slot bound. -/
theorem arming_emitted_head_fields {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {y : V} {o : Obj p} {s : Slot} {a : Fin p.n}
    {b : BlockId} {H : Block}
    (hTarget : HeadTargetAtEmission p c E rho y o (SA.voteTime p.toParams s) H)
    (hd : (toWire p o).decode = some (.vote s a b)) : H.root = b ∧ H.slot ≤ s := by
  have ho : o = ofHead p ⟨.seat (.head s) a, b⟩ := by
    apply toWire_injective
    rw [toWire_ofHead]
    exact decode_eq_vote.mp hd
  subst o
  obtain ⟨i, hi, hem⟩ := show V2.D.Run.emits E rho y
      (ofHead p ⟨.seat (.head s) a, b⟩) (SA.voteTime p.toParams s) from by
    obtain ⟨i, _, _, hi, hem, _, _⟩ := hTarget
    exact ⟨i, hi, hem⟩
  have hH := headTargetAtEmission_at_tick E rho hs hTarget hi rfl
  have he := hem
  rw [(V2.D.Run.step_tick_eq E rho hi).2] at he
  have hfields := (fgsa_emits_head E rho _ y _ s a b).mp he
  have hroot : H.root = b := by rw [hH]; exact hfields.2.2.2.2.symm
  have hstored : H ∈ (storeAt p c E rho i y).base.blocks := by
    rw [hH]
    have hm := headVote_stored p _
      (storeBundle_postClock E rho i y (SA.voteTime p.toParams s)).cstore s
    change headVote p (clock p (storeAt p c E rho i y) _) s ∈
      (clock p (storeAt p c E rho i y) _).base.blocks at hm
    rwa [clock_base_blocks] at hm
  have hbound := (fgsa_stateBefore_bounds E rho hs i y).1 H hstored
  have hnow := fgsa_preTick_now_le E rho hs hi
  have hslot := slotOf_offset p s p.Δ p.deltaPos.le
    (by have hδ := p.deltaPos; dsimp [Time] at *; omega)
  exact ⟨hroot, hbound.trans ((Internal.slotOf_mono (p := p) hnow).trans_eq hslot)⟩

/-- The local receipt inputs for one batch. These are proof data, not outage fields. -/
structure ArmingBatchReceiptService (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (s : Slot) (C : Time) : Prop where
  heads : ∀ y o a b, y ∈ rho.honest →
    V2.D.Run.emits E rho y o (SA.voteTime p.toParams s) →
    (toWire p o).decode = some (.vote s a b) →
    ∃ H, HeadTargetAtEmission p c E rho y o (SA.voteTime p.toParams s) H ∧
      (¬ Block.Compatible H (eraseFG (V2.D.Run.stateBeforeTime E rho C x).st.fg.F) ∨
        (Nonempty (FreshHeadService E rho s a b C x) ∧
          TargetReceiptService E rho H C x))
  proposals : ∀ y o m q N, y ∈ rho.honest →
    V2.D.Run.emits E rho y o (V2.D.proposalTime (fgsaInterface p c) m) →
    V2.D.proposalTime (fgsaInterface p c) m ≤ SA.voteTime p.toParams s →
    (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho C x) o = false →
    (toWire p o).decode = some (.block q N) →
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer q, .proposal N⟩)
      (V2.D.proposalTime (fgsaInterface p c) m) C x)

/-- Processed proposals give all stored ancestors with strict receipt stamps. -/
theorem arming_proposal_receipt_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) (hroots : NamedReceiptRootCollisionFree p c E rho)
    {x : V} (hx : x ∈ rho.honest) {q : Slot} {N : NamedProposal p.n} {send C : Time}
    (hC : 0 < C)
    (h : ReceiverService E rho (ofWire p ⟨.proposer q, .proposal N⟩) send C x) :
    ReceiptObjectAt p c E rho x (ofWire p ⟨.proposer q, .proposal N⟩) C := by
  refine ⟨h.processed hs hx (by simp [isRowObject, ofWire]), ?_, ?_⟩
  · intro s a b hd
    rw [toWire_ofWire] at hd
    cases hd
  · intro s M hd B hBM
    rw [toWire_ofWire] at hd
    cases hd
    obtain ⟨Y, hY, hYN⟩ := h.proposal hs hx hroots
    have hBY : Block.Preceq B (eraseFG Y) := hYN ▸ hBM
    obtain ⟨Z, hZ, hZB⟩ := eraseFG_ancestor_mem
      (storeBundle_stateBeforeTime E rho C x).cstore.fg.closed hY hBY
    refine ⟨Z, hZ, hZB, fgsa_block_stamp_before_read E rho hs x C hC B ?_⟩
    exact ((storeBundle_stateBeforeTime E rho C x).cstore.baseTree B).mpr ⟨Z, hZ, hZB⟩

/-- A ready fresh HEAD with a compatible target is fully resolved at the read. -/
theorem arming_head_receipt_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hE : V2.D.ExecutionValid E rho) (hroots : NamedReceiptRootCollisionFree p c E rho)
    {x y : V} (hx : x ∈ rho.honest) {s : Slot} {a : Fin p.n} {K : Block} {C : Time}
    (hC : 0 < C) (hslot : K.slot ≤ s)
    (hcompat : Block.Compatible K (eraseFG (V2.D.Run.stateBeforeTime E rho C x).st.fg.F))
    (hHead : FreshHeadService E rho s a K.root C x)
    (hTarget : TargetReceiptService E rho K C x) {k : Nat}
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)))
    (hem : ofHead p ⟨.seat (.head s) a, K.root⟩ ∈ V2.D.Run.emitsAt E rho k) :
    ReceiptObjectAt p c E rho x (ofHead p ⟨.seat (.head s) a, K.root⟩) C := by
  let st := (V2.D.Run.stateBeforeTime E rho C x).st
  have hs := hE.toScheduleWellFormed
  obtain ⟨hvote, hvs⟩ := hHead.receipt hE hx hk hem
  have hblock := fgsa_target_receipt_on E rho hs hroots K C x hx hTarget
  have hbs := fgsa_block_stamp_before_read E rho hs x C hC K hblock
  have hactive : K ∈ (actView st).blocks := (actView_blocks st K).mpr ⟨hblock, hcompat⟩
  have hlookup : Block.findByRoot? (GridCO.resolutionTree (actView st)) K.root = some K := by
    have hdomain : st.base.headDomain = none := by
      dsimp only [st]
      rw [← Gen.V2.Duty.stateBefore_idxBefore E rho C hs]
      exact base_headDomain_none p (reachable_stateBefore E rho _ x)
    rw [actView_resolutionTree, GridCO.resolutionTree, hdomain]
    exact Block.findByRoot?_of_unique hblock
      (baseBlocks_rootInj p st (storeBundle_stateBeforeTime E rho C x).cstore)
  have hresolved : GridCO.resolvedHead? (actView st)
      (baseVote (⟨.seat (.head s) a, K.root⟩ : HeadWire p.n)) = some K := by
    change ((Block.findByRoot? (GridCO.resolutionTree (actView st)) K.root).bind
      fun B => if B ∈ (actView st).blocks then some B else none) = some K
    simp only [hlookup, Option.bind_some, hactive, ite_true]
  refine ⟨?_, ?_, ?_⟩
  · change decide (_ ∈ st.base.votes) = true
    exact decide_eq_true hvote
  · intro r b root hd
    rw [toWire_ofHead] at hd
    cases hd
    change GridCO.resolvedBefore (actView st) _ C = true
    unfold GridCO.resolvedBefore
    rw [hresolved]
    change (decide (K.slot ≤ s) && decide (GridCO.stampVote st.base _ < C) &&
      decide (GridCO.stampBlock st.base K < C)) = true
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true hslot, decide_eq_true hvs⟩,
        decide_eq_true hbs⟩
  · intro r N hd
    rw [toWire_ofHead] at hd
    cases hd

/-- Local service yields the batch receipt, including the approved finality alternative. -/
theorem arming_batch_receipt_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hE : V2.D.ExecutionValid E rho) (hroots : NamedReceiptRootCollisionFree p c E rho)
    {x : V} (hx : x ∈ rho.honest) {s : Slot} {C : Time} (hC : 0 < C)
    (h : ArmingBatchReceiptService E rho x s C) : BatchReceiptAt p c E rho x s C := by
  classical
  constructor
  · intro y o hy hem a b hd
    obtain ⟨K, hK, hcases⟩ := h.heads y o a b hy hem hd
    rcases hcases with hbad | ⟨⟨hHead⟩, hTarget⟩
    · exact Or.inl ⟨K, hK, hbad⟩
    obtain ⟨hroot, hslot⟩ := arming_emitted_head_fields hE.toScheduleWellFormed hK hd
    have ho : o = ofHead p ⟨.seat (.head s) a, b⟩ := by
      apply toWire_injective
      rw [toWire_ofHead]
      exact decode_eq_vote.mp hd
    subst o
    rw [← hroot] at hem ⊢
    by_cases hbad : ¬ Block.Compatible K (eraseFG (V2.D.Run.stateBeforeTime E rho C x).st.fg.F)
    · exact Or.inl ⟨K, by simpa [hroot] using hK, hbad⟩
    · obtain ⟨k, hk, he⟩ := hem
      rw [← hroot] at hHead
      exact Or.inr (arming_head_receipt_on hE hroots hx hC hslot (not_not.mp hbad)
        hHead hTarget hk he)
  · intro y o m hy hem htime hnot q N hd
    obtain ⟨hProp⟩ := h.proposals y o m q N hy hem htime hnot hd
    have ho : o = ofWire p ⟨.proposer q, .proposal N⟩ := by
      apply toWire_injective
      rw [toWire_ofWire]
      exact decode_eq_block.mp hd
    subst o
    exact arming_proposal_receipt_on hE.toScheduleWellFormed hroots hx hC hProp

/-- The prefix receipt proof composes local batches. Regime-derived service
remains a closure input. -/
theorem arming_prefix_batch_receipt_on {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} (hE : V2.D.ExecutionValid E rho)
    (hroots : NamedReceiptRootCollisionFree p c E rho) {fast : Bool} {T b₀ : Time}
    (hService : ∀ x ∈ coveredNodes p E rho fast b₀, ∀ q,
      (if fast then q = coverLabel p b₀
       else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (q : Int) ∧ q ≤ coverLabel p b₀) →
      T ≤ SA.gateTime p.toParams q →
      SA.earlyTime p.toParams q ≤ b₀ →
      ArmingBatchReceiptService E rho x q (SA.earlyTime p.toParams q)) :
    OutagePrefixReceipt p c E rho fast T b₀ := by
  intro x hx q hq hT hCut
  have hxH : x ∈ rho.honest := by
    classical
    change x ∈ rho.honest.filter _ at hx
    exact (Finset.mem_filter.mp hx).1
  apply arming_batch_receipt_on hE hroots hxH
    (show 0 < SA.earlyTime p.toParams q from by
      rw [arming_early_eq]
      have hd := p.deltaPos
      positivity)
  exact hService x hx q hq hT hCut

end AvailableChain.FGSA.Run
end
