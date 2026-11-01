module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.StepGateBatch -- shake: keep
-- shake keep reason: Inclusion uses exactService_emitted_head_joined.
public import AvailableChainFGSAProofs.Proofs.Shared.ExactService -- shake: keep

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- Exact joined HEAD receipts force the enabled raw gate result. -/
theorem wc_exact_gate_raw (hE : V2.D.ExecutionValid E rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    {i : Nat} {x : V} {s : Slot} {Q : Block}
    (H : Finset (Fin p.n))
    (hH : ∀ q, q ∈ H ↔ rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s))
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card)
    (hrec : ∀ q ∈ H, ∃ t,
      rho.emits E (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, Q.root⟩) t ∧
      baseVote (⟨.seat (.head s) q, Q.root⟩ : HeadWire p.n) ∈
        (storeAt p c E rho i x).base.votes ∧
      Q ∈ (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))).blocks ∧
      Q.slot ≤ s ∧
      GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x)
        (SA.gateTime p.toParams s))) (baseVote ⟨.seat (.head s) q, Q.root⟩) <
        GridCO.earlyTime p.toParams.engine s ∧
      GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x)
        (SA.gateTime p.toParams s))) Q < GridCO.earlyTime p.toParams.engine s ∧
      Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i x)
        (SA.gateTime p.toParams s)).fg.F) Q) :
    let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
    let v := actView pre
    SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) v s = some Q ∧
      H.card ≤ SA.Root.prefixSupport p.toParams v s Q ∧
      Q ∈ v.blocks ∧ Block.Preceq (eraseFG pre.fg.F) Q := by
  intro pre v
  have hheads (q : Fin p.n) (hq : q ∈ H) := hrec q hq
  have hcover := fgsa_gate_batch_premises_joined E rho hE hC i x s Q H hbatch
    (fun q hy haw => (hH q).mpr ⟨hy, haw⟩) (by
      intro q hq
      obtain ⟨t, he, hv, hQ, hslot, hvs, hbs, hF⟩ := hheads q hq
      exact ⟨Q, t, ((hH q).mp hq).1, he, hv, hQ, hslot, hvs, hbs, hF,
        block_preceq_refl Q⟩)
  have hsupp (q : Fin p.n) (hq : q ∈ H) :
      Gen.AC.Root.poolSupports v.blocks (GridCO.cleanSupport p.toParams.engine v s) q Q = true := by
    obtain ⟨t, he, hv, hQ, hslot, hvs, hbs, _⟩ := hrec q hq
    exact fgsa_active_support_of_receipt E rho hE i x s q Q Q t
      ((hH q).mp hq).1 he hv hQ hslot hvs hbs (block_preceq_refl Q)
  have hc := Gen.AC.Root.batch_counts v.blocks (GridCO.lateVotes p.toParams.engine v s)
    (GridCO.cleanSupport p.toParams.engine v s) (GridCO.cleanSupport p.toParams.engine v s)
    H H.card (Gen.V2.Duty.faulty rho).card Q
    (fun _ ho => fgsa_early_subset_late p v s (List.mem_filter.mp ho).1)
    (fun _ ho => ho) rfl (fun q _ => fgsa_cleanSupport_no_equivocation p v s q)
    hsupp (fgsa_late_rest_bound_joined E rho hC hE i x s H
      (fun q hy haw => (hH q).mpr ⟨hy, haw⟩)) hbatch
  have hpos : 0 < H.card := lt_of_le_of_lt (Nat.zero_le _) hbatch.lt
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos
  obtain ⟨_, _, _, hQ, _, _, _, hF⟩ := hrec q hq
  obtain ⟨C, hraw, hQC⟩ := fgsa_confirmationFrom_covers_majority p v (eraseFG pre.fg.F)
    Q s Q.root (Bool.or_eq_true_iff.mpr (Or.inl hF)) hcover.1 hcover.2.1 hcover.2.2
  have hno (D : Block) (hD : ¬ Block.Preceq D Q) (k : Fin p.n) (hk : k ∈ H) :
      Gen.AC.Root.poolSupports v.blocks (GridCO.cleanSupport p.toParams.engine v s) k D = false
          := by
    apply Bool.eq_false_iff.mpr
    intro hs
    obtain ⟨o, ho, hseat, hvote⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ k D).mp hs
    have hearly := (List.mem_filter.mp ho).1
    have hlabel : GridCO.headLabel? o = some s :=
      beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp hearly).1).2
    have hm : o ∈ (storeAt p c E rho i x).base.votes := by
      have hm := (List.mem_filter.mp (List.mem_filter.mp hearly).1).1
      change o ∈ (clockPre p (storeAt p c E rho i x) _).base.votes at hm
      rwa [(Internal.clockPre_vn _ _).1] at hm
    obtain ⟨t, he, _, _, _, _, _, _⟩ := hrec k hk
    have heq := fgsa_honest_head_eq_of_stored E rho hE i x s k Q.root t
      ((hH k).mp hk).1 he o hm hlabel hseat
    rw [heq] at hvote
    have hlookup := Block.findByRoot?_of_unique hQ (fun A hA B hB =>
      baseBlocks_rootInj p pre
        (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x) _) A
        (List.mem_filter.mp hA).1 B (List.mem_filter.mp hB).1)
    change (match Block.findByRoot? v.blocks Q.root with
      | none => false
      | some C => decide (C ∈ v.blocks) && decide (C.slot ≤ s) && Block.preceq D C) = true
      at hvote
    rw [hlookup] at hvote
    change (_ && _ && Block.preceq D Q) = true at hvote
    exact hD (Bool.and_eq_true_iff.mp hvote).2
  have helig : GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s C := by
    let W := GridCO.ghost (eraseFG pre.fg.F) v.blocks (SA.Root.prefixSupport p.toParams v s)
      (fun D => decide (GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
        2 * SA.Root.prefixSupport p.toParams v s D))
    change (if GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s W then some W else none) = some C at hraw
    by_cases hw : GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
        2 * SA.Root.prefixSupport p.toParams v s W
    · rw [ite_eq_left hw] at hraw
      exact (Option.some.inj hraw) ▸ hw
    · rw [ite_eq_right hw] at hraw
      cases hraw
  have hscore (D : Block) : SA.Root.prefixSupport p.toParams v s D =
      GridCO.goldfishScore v.blocks (GridCO.cleanSupport p.toParams.engine v s)
        (GridCO.cleanSupport p.toParams.engine v s) D :=
    actView_score p pre (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x) _)
      (by rw [clockPre_headDomain]; exact base_headDomain_none p (reachable_stateBefore E rho i x))
      _ _ D
  have hCQ : Block.Preceq C Q := by
    by_contra hn
    have hb := hc.2.2.2.2 C (hno C hn)
    rw [hscore] at helig
    omega
  have heq := block_preceq_antisymm hQC hCQ
  subst C
  refine ⟨hraw, ?_, hQ, hF⟩
  rw [hscore]
  exact (hc.2.2.1 Q (block_preceq_refl Q)).1


end AvailableChain.FGSA.Run
end
