module
public import AvailableChainFGSAProofs.Proofs.Shared.CatchUp
public import AvailableChainFGSARun.Proofs.ReceiptCoverageReady
public import AvailableChainFGSARun.Proofs.RootResolution
public import AvailableChainFGSARun.Proofs.HeadHistory

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem count_head_keys (o : GridCO.Wire p.n .root) (s : Slot) (k : Fin p.n)
    (hl : GridCO.headLabel? o = some s) (hk : GridCO.headSeat? o = some k) :
    ∃ K, o = ⟨.seat s k, .head K⟩ := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> cases hl
  | proposer r => cases payload <;> cases hl
  | seat r j =>
    cases payload with
    | proposal B raw sup => cases hl
    | head K =>
      have hr : r = s := Option.some.inj hl
      have hj : j = k := Option.some.inj hk
      subst r; subst j
      exact ⟨K, rfl⟩

private theorem count_head_signed_origin (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (idx : Nat) (x : V) (s : Slot) (k : Fin p.n) (K : BlockId) (stamp : Time)
    (hv : ((⟨.seat s k, .head K⟩ : GridCO.Wire p.n .root), stamp) ∈
      (V2.D.Run.stateBefore E rho idx x).st.base.voteStamp)
    (hh : rho.seatOf (.base (.head s)) k ∈ rho.honest) :
    ∃ t, V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) k)
      (ofHead p ⟨.seat (.head s) k, K⟩) t := by
  have horigin : ∃ (j : Nat) (parent : Obj p) (u : Time),
      rho.events[j]? = some (.deliver x parent u) ∧
      (parent = ofHead p ⟨.seat (.head s) k, K⟩ ∨
        (fgsa p c).carries parent (ofHead p ⟨.seat (.head s) k, K⟩)) := by
    rcases fgsa_vote_stamp_source_or_restart E rho idx x s k K stamp hv with
      ⟨j, _, u, ha, _⟩ | ⟨j, _, wake, _, _, hr⟩
    · obtain ⟨parent, he, hhandles⟩ := ha.1
      exact ⟨j, parent, u, he, (fgsaHooks p c).handles_carries _ _ _ hhandles⟩
    · obtain ⟨q, _, parent, u, he, hc⟩ :=
        fgsa_replayed_head_delivery_origin E rho j x wake s k K hr
      exact ⟨q, parent, u, he, Or.inr hc⟩
  obtain ⟨j, parent, u, he, hc⟩ := horigin
  have hem : ∃ t, t ≤ u ∧ V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) k)
      (ofHead p ⟨.seat (.head s) k, K⟩) t := by
    rcases hc with rfl | hc
    · exact hE.unforgeable x _ u ⟨j, he⟩ _ hh rfl
    · exact hE.carried x parent u ⟨j, he⟩ _ hc _ hh rfl
  obtain ⟨t, _, ht⟩ := hem
  exact ⟨t, ht⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.1, blueprint 02 §2.1. Class (ii), receipt/authenticity instance.
DC: Protocol/Handlers/GoldfishVotePool.lean:320 (unique honest vote per label).
Same uniqueness conclusion; FG-SA also permits carried HEAD receipts. -/
theorem fgsa_honest_head_eq_of_stored (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (i : Nat) (x : V) (s : Slot) (k : Fin p.n)
    (K : BlockId) (t : Time) (hh : rho.seatOf (.base (.head s)) k ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) k)
      (ofHead p ⟨.seat (.head s) k, K⟩) t)
    (o : GridCO.Wire p.n .root) (ho : o ∈ (storeAt p c E rho i x).base.votes)
    (hl : GridCO.headLabel? o = some s) (hk : GridCO.headSeat? o = some k) :
    o = baseVote (⟨.seat (.head s) k, K⟩ : HeadWire p.n) := by
  obtain ⟨C, rfl⟩ := count_head_keys o s k hl hk
  change _ ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes at ho
  rw [← fgsa_vote_stamp_keys E rho i x] at ho
  obtain ⟨⟨v, stamp⟩, hv, hvEq⟩ := List.mem_map.mp ho
  dsimp only at hvEq
  subst v
  obtain ⟨u, hu⟩ := count_head_signed_origin E rho hE i x s k C stamp hv hh
  have heq := Gen.V2.Duty.honest_unique_singleDuty_statement (P := fgsa p c) E rho
    hE.nodup hE.toUnforgeableSignatures (fgsaHooks p c).handles_carries
    (.base (.head s)) (fgsa_head_singleDuty s) k hh (ofHead p ⟨.seat (.head s) k, C⟩)
    (ofHead p ⟨.seat (.head s) k, K⟩) rfl rfl
    (Or.inl ⟨u, hu⟩) (Or.inl ⟨t, he⟩)
  have hCK : C = K := congrArg (fun o : Obj p => o.payload) heq |> Msg.head.inj
  subst C
  rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.1, blueprint 02 §2.1 and §5.4. Class (ii), active receipt instance.
DC: Goldfish/Confirmation:494,508. INTENTIONAL: resolved support is restricted
by the current F; the receipt must retain its target (P3:4921–4929).
The read is the actual pre-gate store, including clockPre. -/
theorem fgsa_active_support_of_receipt (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (i : Nat) (x : V) (s : Slot) (k : Fin p.n) (K B : Block) (t : Time)
    (hh : rho.seatOf (.base (.head s)) k ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) k)
      (ofHead p ⟨.seat (.head s) k, K.root⟩) t)
    (hv : baseVote (⟨.seat (.head s) k, K.root⟩ : HeadWire p.n) ∈
      (storeAt p c E rho i x).base.votes)
    (hK : K ∈ (actView (clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s))).blocks)
    (hslot : K.slot ≤ s)
    (hvote : GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s))) (baseVote (⟨.seat (.head s) k, K.root⟩ : HeadWire p.n)) <
      GridCO.earlyTime p.toParams.engine s)
    (hblock : GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s))) K < GridCO.earlyTime p.toParams.engine s)
    (hBK : Block.Preceq B K) :
    let v := actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    Gen.AC.Root.poolSupports v.blocks (GridCO.cleanSupport p.toParams.engine v s) k B = true := by
  intro v
  let o : GridCO.Wire p.n .root := ⟨.seat s k, .head K.root⟩
  have hvotes : v.votes = (storeAt p c E rho i x).base.votes :=
    (Internal.clockPre_vn (storeAt p c E rho i x) _).1
  change K ∈ v.blocks at hK
  change GridCO.stampVote v o < _ at hvote
  change GridCO.stampBlock v K < _ at hblock
  let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
  have hstore := cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x)
    (SA.gateTime p.toParams s)
  have hdomain : pre.base.headDomain = none := by
    rw [clockPre_headDomain]
    exact base_headDomain_none p (reachable_stateBefore E rho i x)
  have hresolve : GridCO.resolvedHead? v o = some K :=
    actView_resolve_of_mem p pre hstore hdomain hK s k
  have hlookup : Block.findByRoot? v.blocks K.root = some K :=
    Block.findByRoot?_of_unique hK (fun A hA C hC =>
      baseBlocks_rootInj p pre hstore A (List.mem_filter.mp hA).1 C (List.mem_filter.mp hC).1)
  have hmem : o ∈ GridCO.earlyVotes p.toParams.engine v s := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_filter.mpr ⟨?_, by exact beq_self_eq_true _⟩, ?_⟩
    · rw [hvotes]; exact hv
    · unfold GridCO.resolvedBefore
      rw [hresolve]
      change ((decide (K.slot ≤ s) &&
        decide (GridCO.stampVote v o < GridCO.earlyTime p.toParams.engine s)) &&
        decide (GridCO.stampBlock v K < GridCO.earlyTime p.toParams.engine s)) = true
      simp only [hslot, hvote, hblock, decide_true, Bool.true_and]
  have hclean : o ∈ GridCO.cleanSupport p.toParams.engine v s := by
    apply List.mem_filter.mpr
    refine ⟨hmem, ?_⟩
    rw [Bool.not_eq_true']
    apply List.any_eq_false.mpr
    intro u hu
    by_cases hs : GridCO.sameSeat u o = true
    · have hl : GridCO.headLabel? u = some s := by
        exact beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp hu).1).2
      have hk : GridCO.headSeat? u = some k := by
        rcases u with ⟨ua, up⟩
        cases ua with
        | none => cases up <;> cases hl
        | proposer r => cases up <;> cases hl
        | seat r j =>
          cases up with
          | proposal C raw sup => cases hl
          | head C =>
            change (r == s && j == k) = true at hs
            have hj := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hs).2
            subst j
            rfl
      have hum : u ∈ (storeAt p c E rho i x).base.votes := by
        rw [← hvotes]
        exact (List.mem_filter.mp (List.mem_filter.mp hu).1).1
      have hue := fgsa_honest_head_eq_of_stored E rho hE i x s k K.root t hh he u hum
        hl hk
      change u = o at hue
      rw [hue]
      simp only [bne_self_eq_false, Bool.and_false, Bool.false_eq_true, not_false_eq_true]
    · simp only [Bool.eq_false_iff.mpr hs, Bool.false_and, Bool.false_eq_true, not_false_eq_true]
  apply (Gen.AC.Root.vote_pool_support_witness _ _ k B).mpr
  refine ⟨o, hclean, rfl, ?_⟩
  unfold Gen.AC.Root.voteSupports Gen.AC.Root.resolvedTarget?
  change (match Block.findByRoot? v.blocks K.root with
    | none => false
    | some C => decide (C ∈ v.blocks) && decide (C.slot ≤ s) && Block.preceq B C) = true
  rw [hlookup]
  change (decide (K ∈ v.blocks) && decide (K.slot ≤ s) && Block.preceq B K) = true
  simp only [hK, hslot, decide_true, Bool.true_and]
  exact hBK

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 F1b.1, K8 and blueprint 02 §5.4:531–541. Class (ii), active path
instance. DC: no exact counterpart for active F filtering. INTENTIONAL: compatibility
through every intervening F (the K8 `compat` field, P3:4921–4929).
A received path whose head extends the final F stays in the active view. -/
theorem fgsa_active_path_of_coverage (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (K : Block)
    (required : Obj p → Time → Prop) (paths : Block → Time → Prop)
    (hx : x ∈ rho.honest)
    (hcov : ReceiptCoveragePremises E rho dl cut D first x K required paths)
    (hpath : paths K D)
    (hFK : Block.Preceq (eraseFG (V2.D.Run.stateBeforeTime E rho D x).st.fg.F) K)
    (hroots : NamedReceiptRootCollisionFree p c E rho)
    (hAwake : ∀ o t, required o t → V2.D.AwakeOn E x t (dl t)) :
    ∀ X, Block.Preceq X K → X ∈ (actView (V2.D.Run.stateBeforeTime E rho D x).st).blocks := by
  let st := (V2.D.Run.stateBeforeTime E rho D x).st
  have hc := (fgsa_receiptCoverage_ready E rho dl cut D first x K required paths
    hroots hDelta hE hN hx hAwake hcov).1
  have hb := (storeBundle_stateBeforeTime E rho D x).cstore
  have hK : K ∈ (actView st).blocks := by
    rcases hc with ⟨hKF, _⟩ | ⟨_, _, hpaths⟩
    · have heq : K = eraseFG st.fg.F := Gen.Pure.block_preceq_antisymm hKF hFK
      rw [heq]
      exact (actView_genesis_F p st hb).2
    · obtain ⟨Y, hY, hYK⟩ := hpaths K D hpath K (Gen.Pure.block_preceq_refl K)
      apply (actView_blocks st K).mpr
      refine ⟨(hb.baseTree K).mpr ⟨Y, hY, hYK⟩, ?_⟩
      exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K) hFK
  intro X hX
  exact actView_ancestor_closed p st hb hK hX

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.1, blueprint 02 §2.1. Class (ii), late-participant instance.
DC: Goldfish/Confirmation:494,508; same honest participation bound.
Authenticity retains the HEAD label and exact vote duty time. -/
theorem fgsa_stored_honest_head_awake (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (i : Nat) (x : V) (s : Slot) (k : Fin p.n) (o : GridCO.Wire p.n .root)
    (ho : o ∈ (storeAt p c E rho i x).base.votes)
    (hl : GridCO.headLabel? o = some s) (hk : GridCO.headSeat? o = some k)
    (hh : rho.seatOf (.base (.head s)) k ∈ rho.honest) :
    E.awake (rho.seatOf (.base (.head s)) k) (SA.voteTime p.toParams s) = true := by
  obtain ⟨K, rfl⟩ := count_head_keys o s k hl hk
  change _ ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes at ho
  rw [← fgsa_vote_stamp_keys E rho i x] at ho
  obtain ⟨⟨v, stamp⟩, hv, hvEq⟩ := List.mem_map.mp ho
  dsimp only at hvEq
  subst v
  obtain ⟨t, j', ht, he⟩ := count_head_signed_origin E rho hE i x s k K stamp hv hh
  rw [(V2.D.Run.step_tick_eq E rho ht).2] at he
  have hem := (fgsa_emits_head E rho _ _ t s k K).mp he
  rw [hem.2.1]
  exact hem.1

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.1, blueprint 02 §2.1. Class (ii), label-seat count instance.
DC: Goldfish/Confirmation:494,508; same honest/rest partition. The selected
batch contains all honest holders awake at the vote duty.
Stored-vote authenticity supplies this timing fact with the original label. -/
theorem fgsa_late_rest_bound [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c))
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hE : V2.D.ExecutionValid E rho) (i : Nat) (x : V) (s : Slot) (H : Finset (Fin p.n))
    (hH : ∀ k, rho.seatOf (.base (.head s)) k ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head s)) k) (SA.voteTime p.toParams s) = true → k ∈ H) :
    let v := actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    ((GridCO.seats p.n (GridCO.lateVotes p.toParams.engine v s)).toFinset \ H).card ≤
      (Gen.V2.Duty.faulty rho).card := by
  intro v
  apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head s)))
  · intro k hk
    obtain ⟨hl, hn⟩ := Finset.mem_sdiff.mp hk
    rw [Gen.V2.Duty.faulty_def]
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hh
    apply hn (hH k hh ?_)
    obtain ⟨o, ho, hs⟩ := (Gen.AC.Root.vote_pool_mem_seats _ k).mp hl
    have hlabel : GridCO.headLabel? o = some s :=
      beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp ho).1).2
    have hm : o ∈ (storeAt p c E rho i x).base.votes := by
      have h := (List.mem_filter.mp (List.mem_filter.mp ho).1).1
      change o ∈ (clockPre p (storeAt p c E rho i x) _).base.votes at h
      rw [(Internal.clockPre_vn _ _).1] at h
      exact h
    exact fgsa_stored_honest_head_awake E rho hE i x s k o hm hlabel hs hh
  · intro k _ j _ he
    exact (hC (.base (.head s)) trivial).injective he

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.1, blueprint 02 §5.4:531–541. Class (ii), Gen batch instance.
DC: Goldfish/Confirmation:494,508,567. INTENTIONAL: two supported prefixes,
including the F anchor, and only the stored suffix (P3:4900–4945).
This is the count boundary over the actual pre-gate store. Receipt resolution
and head-history facts are explicit; they are not assumed count conclusions. -/
theorem fgsa_gate_batch_premises [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (i : Nat) (x : V) (s : Slot) (B : Block) (H : Finset (Fin p.n))
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card)
    (hH : ∀ k, rho.seatOf (.base (.head s)) k ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head s)) k) (SA.voteTime p.toParams s) = true → k ∈ H)
    (hheads : ∀ k ∈ H, ∃ K t,
      rho.seatOf (.base (.head s)) k ∈ rho.honest ∧
      V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) k)
        (ofHead p ⟨.seat (.head s) k, K.root⟩) t ∧
      baseVote (⟨.seat (.head s) k, K.root⟩ : HeadWire p.n) ∈
        (storeAt p c E rho i x).base.votes ∧
      K ∈ (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))).blocks ∧
      K.slot ≤ s ∧
      GridCO.stampVote
        (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)))
        (baseVote (⟨.seat (.head s) k, K.root⟩ : HeadWire p.n)) < GridCO.earlyTime
            p.toParams.engine s ∧
      GridCO.stampBlock
        (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) K <
        GridCO.earlyTime p.toParams.engine s ∧
      Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i x)
        (SA.gateTime p.toParams s)).fg.F) K ∧ Block.Preceq B K) :
    let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
    let v := actView pre
    let a := eraseFG pre.fg.F
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s a ∧
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s B ∧
    (∀ X, Block.Preceq a X → Block.Preceq X B → X ≠ a → X ∈ v.blocks) := by
  intro pre v a
  have hsupp (X : Block) (hX : X = a ∨ X = B) :
      ∀ k ∈ H, Gen.AC.Root.poolSupports v.blocks
        (GridCO.cleanSupport p.toParams.engine v s) k X = true := by
    intro k hk
    obtain ⟨K, t, hh, he, hv, hK, hslot, hvs, hbs, haK, hBK⟩ := hheads k hk
    apply fgsa_active_support_of_receipt E rho hE i x s k K X t hh he hv hK hslot hvs hbs
    rcases hX with rfl | rfl
    · exact haK
    · exact hBK
  have hrest := fgsa_late_rest_bound E rho hC hE i x s H hH
  have hcount (X : Block) (hX : X = a ∨ X = B) :
      GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
        2 * SA.Root.prefixSupport p.toParams v s X := by
    have hc := Gen.AC.Root.batch_counts v.blocks (GridCO.lateVotes p.toParams.engine v s)
      (GridCO.cleanSupport p.toParams.engine v s) (GridCO.cleanSupport p.toParams.engine v s)
      H H.card (Gen.V2.Duty.faulty rho).card X
      (fun _ ho => fgsa_early_subset_late p v s (List.mem_filter.mp ho).1)
      (fun _ ho => ho) rfl (fun k _ => fgsa_cleanSupport_no_equivocation p v s k)
      (hsupp X hX) hrest hbatch
    have he := actView_score p pre
      (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x) _)
      (by rw [clockPre_headDomain]; exact base_headDomain_none p (reachable_stateBefore E rho i x))
      (GridCO.cleanSupport p.toParams.engine v s) (GridCO.cleanSupport p.toParams.engine v s) X
    change _ < 2 * GridCO.goldfishScoreOn (GridCO.resolutionTree v) v.blocks _ _ X
    rw [he]
    exact (hc.2.2.1 X (Gen.Pure.block_preceq_refl X)).2
  refine ⟨hcount a (Or.inl rfl), hcount B (Or.inr rfl), ?_⟩
  intro X _ hXB _
  have hpos : 0 < H.card := lt_of_le_of_lt (Nat.zero_le _) hbatch.lt
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  obtain ⟨K, _, _, _, _, hK, _, _, _, _, hBK⟩ := hheads k hk
  have hstore := cstoreInv_clockPre p (storeAt p c E rho i x)
    (storeBundle_stateBefore E rho i x).cstore (SA.gateTime p.toParams s)
  exact actView_ancestor_closed p pre hstore hK (Gen.Pure.block_preceq_trans hXB hBK)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.1; blueprint 02 §5.4, genesis case (f2-5a1 finding (a)).
Class (ii), active honest batch instance. DC: Goldfish/Confirmation:494,508,567;
INTENTIONAL: the optional F-anchored result must pass the anchor test.
Honest genesis receipts give a strict majority and exclude every non-genesis
result at this actual pre-gate store. Receipt stamps remain explicit inputs. -/
theorem fgsa_gate_zero_of_receipts [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (i : Nat) (x : V) (H : Finset (Fin p.n))
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card)
    (hH : ∀ k, rho.seatOf (.base (.head 0)) k ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head 0)) k) (SA.voteTime p.toParams 0) = true → k ∈ H)
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
    hsupp (fgsa_late_rest_bound E rho hC hE i x 0 H hH) hbatch
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

private theorem count_stamp_kept (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (i j : Nat) (v : GridCO.Wire p.n .root)
    (hm : v ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes)
    (hp : (V2.D.Run.stateBefore E rho i x).st.base.voteStamp <+:
      (V2.D.Run.stateBefore E rho j x).st.base.voteStamp) :
    GridCO.stampVote (V2.D.Run.stateBefore E rho j x).st.base v =
      GridCO.stampVote (V2.D.Run.stateBefore E rho i x).st.base v := by
  rw [← fgsa_vote_stamp_keys E rho i x] at hm
  obtain ⟨⟨v', t⟩, ht, he⟩ := List.mem_map.mp hm
  dsimp only at he
  subst v'
  obtain ⟨tail, htail⟩ := hp
  unfold GridCO.stampVote
  rw [← htail, List.find?_append]
  cases hf : (V2.D.Run.stateBefore E rho i x).st.base.voteStamp.find?
      (fun row => row.1 == v) with
  | none =>
      have hn := List.find?_eq_none.mp hf (v, t) ht
      simp only [beq_self_eq_true] at hn
      contradiction
  | some row => rfl

/-- Receipt coverage needs handler readiness only on [a, dl(a)).
The supplied window witness is the same anchor for ReadyTrigger,
HistorySafeAt, restartFree, and handler readiness. -/
theorem fgsa_receiptCoverage_anchor_on :
  ∀ {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (B : Block)
    (required : Obj p → Time → Prop) (paths : Block → Time → Prop),
    NamedReceiptRootCollisionFree p c E rho → E.Δ = p.Δ → V2.D.ExecutionValid E rho
      → x ∈ rho.honest →
    ReceiptCoverageSleepPremises E rho dl cut D first x B required paths →
    (∀ o t, required o t → ∃ a, t ≤ a ∧ 0 ≤ a ∧ a < dl a ∧
      Gen.V2.Duty.ReadyTrigger E rho o t x a (dl a) ∧
      Gen.V2.Duty.HistorySafeAt E rho x o a ∧
      V2.D.restartFree rho x (V2.D.Run.actionCut rho a) (V2.D.Run.idxBefore rho D) ∧
      first ≤ V2.D.Run.actionCut rho a ∧ dl a ≤ dl t ∧
      (fgsa p c).wellFormed o = true ∧
      (∀ s signer K, (toWire p o).decode = some (.vote s signer K) →
        (V2.D.Run.stateBeforeTime E rho (dl t) x).st.slot p ≤ s + 1 ∧
        ∀ i t', V2.D.Run.actionCut rho a ≤ i → i < V2.D.Run.idxBefore rho (dl a) →
          a ≤ t' → V2.D.Run.handlesAt E rho i x o t' →
          s ≤ (V2.D.Run.stateBefore E rho i x).st.slot p ∧
            (V2.D.Run.stateBefore E rho i x).st.slot p ≤ s + 1) ∧
      ∀ j u, a ≤ u → u < dl a → V2.D.Run.handlesAt E rho j x o u →
        (fgsa p c).wellFormed o = true ∧
        (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x) o = true ∧
        fgsaTimely p (V2.D.Run.stateBefore E rho j x) o) →
    let st := (V2.D.Run.stateBeforeTime E rho D x).st
    ((Block.Preceq B (eraseFG st.fg.F) ∧
      Block.Preceq B st.base.stableRecord ∧
      (∀ s, 0 < s → Block.Preceq B (headVote p st s)) ∧
      (∀ raw sup, Block.Preceq B (getHead p st raw sup)) ∧
      Block.Preceq B (fgHead p st) ∧
      (∀ lease ∈ st.base.obligations, Block.Compatible B lease.1)) ∨
     (Block.Preceq (eraseFG st.fg.F) B ∧
      (∀ o t s N, required o t →
        (toWire p o).decode = some (.block s N) →
        ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho (dl t) x).st.fg.TF, eraseFG Y = N.erase) ∧
      (∀ K d, paths K d → ∀ b, Block.Preceq b K →
        ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho d x).st.fg.TF, eraseFG Y = b))) ∧
    (∀ o t s a K, required o t → (toWire p o).decode = some (.vote s a K) →
      let v := baseVote (⟨.seat (.head s) a, K⟩ : HeadWire p.n)
      (v ∈ st.base.votes ∧ GridCO.stampVote st.base v < dl t) ∨
      ∃ v₁ ∈ st.base.votes, ∃ v₂ ∈ st.base.votes,
        v₁ ≠ v₂ ∧ GridCO.headLabel? v₁ = some s ∧ GridCO.headLabel? v₂ = some s ∧
        GridCO.headSeat? v₁ = some a ∧ GridCO.headSeat? v₂ = some a ∧
        GridCO.stampVote st.base v₁ < dl t ∧ GridCO.stampVote st.base v₂ < dl t) := by
  intro p In V inst c E rho dl cut D first x B required paths hRoots hDelta hExecution
    hx h hReady
  have hS := hExecution.toScheduleWellFormed
  have hidx := fgsa_idxBefore_mono rho
  have hf (a : Time) (ha : a ≤ D) :
      Block.Preceq (eraseFG (V2.D.Run.stateBeforeTime E rho a x).st.fg.F)
        (eraseFG (V2.D.Run.stateBeforeTime E rho D x).st.fg.F) := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho a hS,
      ← Gen.V2.Duty.stateBefore_idxBefore E rho D hS]
    have hm := fgsa_monoAlong_preceq_F p c (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho a) x).st.fg.F
    rw [Gen.V2.Duty.MonoAlong_def] at hm
    apply eraseFG_preceq
    apply V2.D.Engine.stateBefore_stable_restore _ hm.1 hm.2.1 hm.2.2
      E rho (hidx ha) x
    · intro nd w hh
      change FGBlock.Preceq (V2.D.Run.stateBefore E rho
        (V2.D.Run.idxBefore rho a) x).st.fg.F (acRestart p nd.st w).fg.F
      rwa [acRestart_fg]
    · exact KitFG.preceq_refl _
  have hstore := storeBundle_stateBeforeTime E rho D x
  constructor
  · have hcompat := h.compat _ h.deadline.2.2.2.1 (le_refl _)
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho D hS] at hcompat
    change (Block.preceq B (eraseFG (V2.D.Run.stateBeforeTime E rho D x).st.fg.F) ||
      Block.preceq (eraseFG (V2.D.Run.stateBeforeTime E rho D x).st.fg.F) B) = true at hcompat
    simp only [Bool.or_eq_true] at hcompat
    rcases hcompat with hBF | hFB
    · left
      refine ⟨hBF, Gen.Pure.block_preceq_trans hBF hstore.nest,
        (fun s hs => preceq_headVote_of_preceq_F p _ hstore.cstore hBF hs),
        preceq_getHead_of_preceq_F p _ hstore.cstore hBF,
        preceq_fgHead_of_preceq_F p _ hstore.cstore hBF, ?_⟩
      intro lease hl
      have hlc := hstore.cstore.saCompat.1 lease hl
      change Block.compatible lease.1 _ = true at hlc
      rw [Gen.Pure.block_compatible_comm] at hlc
      exact Gen.Pure.block_compatible_of_preceq_compatible hBF hlc
    · right
      have hproposal : ∀ o t s N, required o t →
          (toWire p o).decode = some (.block s N) →
          ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho (dl t) x).st.fg.TF, eraseFG Y = N.erase := by
        intro o t s N hr hd
        obtain ⟨K, d, hk, hbK⟩ := h.deadline.2.2.2.2.2.2 o t s N hr hd
        have hBK := (h.deadline.2.2.2.2.2.1 K d hk).1
        have ht := h.deadline.2.2.2.2.1 o t hr
        obtain ⟨a, hta, ha, had, hT, hHistory, hRF, _, hdl, _, _, hReadyAt⟩ :=
          hReady o t hr
        have ho : o = ofWire p ⟨.proposer s, .proposal N⟩ := by
          apply toWire_injective
          rw [toWire_ofWire]
          exact decode_eq_block.mp hd
        have hFK := Gen.Pure.block_preceq_trans
          (Gen.Pure.block_preceq_trans (hf (dl a) (hdl.trans ht.2.2.2)) hFB) hBK
        have hbF := Gen.Pure.block_compatible_of_common hbK hFK
        have hTrigger : Gen.V2.Duty.Trigger E rho o t := by
          obtain ⟨v, hv, htr, _⟩ := hT
          rcases htr with he | ⟨i, hi⟩
          · exact Or.inl ⟨v, hv, he⟩
          · exact Or.inr ⟨v, hv, i, hi⟩
        change Block.compatible N.erase
          (eraseFG (V2.D.Run.stateBeforeTime E rho (dl a) x).st.fg.F) = true at hbF
        have hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl a) x) o = false := by
          change excludesS p _ o = false
          dsimp only [excludesS]
          rw [hd]
          simp only [blockExcluded, activeCompatible, hbF, Bool.not_true, Bool.false_or]
          exact fgsa_trigger_invalid_false E rho o t s N hTrigger hd _
        rw [ho] at hT hHistory hNX
        exact fgsa_proposal_receipt_on E rho hS hRoots dl cut s N t a (dl t) x h.within
          hT hx hta ha had (hdl.trans (ht.2.2.2.trans h.deadline.2.1))
          (hdl.trans (ht.2.2.2.trans (h.deadline.2.1.trans h.deadline.2.2.1))) hdl
          hHistory (hRF.mono le_rfl (hidx ht.2.2.2)) (by
            intro j u hau hud hh
            rw [← ho] at hh ⊢
            exact hReadyAt j u hau hud hh) hNX
      refine ⟨hFB, hproposal, ?_⟩
      intro K d hk b hb
      by_cases hg : b = .genesis
      · subst b
        exact ⟨.genesis, (storeBundle_stateBeforeTime E rho d x).cstore.fg.gen, rfl⟩
      · obtain ⟨o, t, s, N, heN, hr, hd, htd⟩ :=
          (h.deadline.2.2.2.2.2.1 K d hk).2.2 b hb hg
        obtain ⟨Y, hY, he⟩ := hproposal o t s N hr hd
        rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hS] at hY
        rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hS]
        exact ⟨Y, (fgsa_store_durable p c E rho (hidx htd) x).1 hY, he.trans heN⟩
  · intro o t s signer K hr hd
    have ht := h.deadline.2.2.2.2.1 o t hr
    obtain ⟨a, hta, ha, had, hT, hHistory, hRF, _, hdl, _, hw, hReadyAt⟩ :=
      hReady o t hr
    have ho : o = ofHead p ⟨.seat (.head s) signer, K⟩ := by
      apply toWire_injective
      rw [toWire_ofHead]
      exact decode_eq_vote.mp hd
    have hcum := fgsa_store_cumulative_on p c E rho (hidx (hdl.trans ht.2.2.2)) x
      (hRF.mono (Gen.V2.Duty.actionCut_le_idxBefore hS had) le_rfl)
    have keep (v : GridCO.Wire p.n .root)
        (hm : v ∈ (V2.D.Run.stateBeforeTime E rho (dl a) x).st.base.votes) :
        v ∈ (V2.D.Run.stateBeforeTime E rho D x).st.base.votes ∧
        GridCO.stampVote (V2.D.Run.stateBeforeTime E rho D x).st.base v =
          GridCO.stampVote (V2.D.Run.stateBeforeTime E rho (dl a) x).st.base v := by
      rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (dl a) hS] at hm ⊢
      rw [← Gen.V2.Duty.stateBefore_idxBefore E rho D hS]
      refine ⟨?_, count_stamp_kept E rho x _ _ v hm hcum.2.2.2.1⟩
      rw [← fgsa_vote_stamp_keys E rho _ x] at hm ⊢
      exact List.mem_map.mpr (by
        obtain ⟨row, hrow, he⟩ := List.mem_map.mp hm
        exact ⟨row, hcum.2.2.2.1.subset hrow, he⟩)
    by_cases hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl a) x) o = false
    · rw [ho] at hT hHistory hNX
      have hp := (fgsa_head_receipt_on E rho hS dl cut s signer K t a (dl a) x h.within
        hT hx hta ha had (hdl.trans (ht.2.2.2.trans h.deadline.2.1))
        (hdl.trans (ht.2.2.2.trans (h.deadline.2.1.trans h.deadline.2.2.1))) le_rfl hHistory
        (hRF.mono le_rfl (hidx (hdl.trans ht.2.2.2))) (by
          intro j u hau hud hh
          rw [← ho] at hh ⊢
          exact hReadyAt j u hau hud hh) hNX).1
      have hk := keep _ hp
      exact Or.inl ⟨hk.1, hk.2.trans_lt
        ((fgsa_head_stamp_before_read E rho hS x (dl a) s signer K hp).trans_le hdl)⟩
    · have hn : excludesS p (V2.D.Run.stateBeforeTime E rho (dl a) x).st o = true :=
        Bool.eq_true_of_ne_false hNX
      rw [ho] at hn
      have hwindow : (V2.D.Run.stateBeforeTime E rho (dl a) x).st.slot p ≤ s + 1 := by
        have hm := V2.D.Engine.stateBefore_now_mono_atRestart (fgsaClock p c)
          (fgsaRestoreTimeLaw p c) E rho hS (hidx hdl) x
        rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho _ x),
          fgsa_clock_now p c (V2.D.Run.stateBefore E rho _ x),
          Gen.V2.Duty.stateBefore_idxBefore E rho (dl a) hS,
          Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hS] at hm
        exact (Internal.slotOf_mono (p := p) hm).trans (hw s signer K hd).1
      obtain ⟨v₁, h₁, v₂, h₂, hn, hl₁, hl₂, ha₁, ha₂, hs₁, hs₂⟩ :=
        fgsa_head_excluded_before E rho hS x (dl a) s signer K hwindow hn
      have hk₁ := keep _ h₁
      have hk₂ := keep _ h₂
      exact Or.inr ⟨v₁, hk₁.1, v₂, hk₂.1, hn, hl₁, hl₂, ha₁, ha₂,
        hk₁.2.trans_lt (hs₁.trans_le hdl), hk₂.2.trans_lt (hs₂.trans_le hdl)⟩

/-- Ready receipt coverage uses each object's receiver anchor and epoch.
Handler readiness is required only inside the named service windows. -/
theorem fgsa_receiptCoverage_on :
  ∀ {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (B : Block)
    (required : Obj p → Time → Prop) (paths : Block → Time → Prop),
    NamedReceiptRootCollisionFree p c E rho → E.Δ = p.Δ → V2.D.ExecutionValid E rho
      → x ∈ rho.honest →
    ReceiptCoverageSleepPremises E rho dl cut D first x B required paths →
    (∀ o t, required o t → ∀ j u, t ≤ u → u < dl t →
      V2.D.Run.handlesAt E rho j x o u →
      (fgsa p c).wellFormed o = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x) o = true ∧
      fgsaTimely p (V2.D.Run.stateBefore E rho j x) o) →
    let st := (V2.D.Run.stateBeforeTime E rho D x).st
    ((Block.Preceq B (eraseFG st.fg.F) ∧
      Block.Preceq B st.base.stableRecord ∧
      (∀ s, 0 < s → Block.Preceq B (headVote p st s)) ∧
      (∀ raw sup, Block.Preceq B (getHead p st raw sup)) ∧
      Block.Preceq B (fgHead p st) ∧
      (∀ lease ∈ st.base.obligations, Block.Compatible B lease.1)) ∨
     (Block.Preceq (eraseFG st.fg.F) B ∧
      (∀ o t s N, required o t →
        (toWire p o).decode = some (.block s N) →
        ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho (dl t) x).st.fg.TF, eraseFG Y = N.erase) ∧
      (∀ K d, paths K d → ∀ b, Block.Preceq b K →
        ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho d x).st.fg.TF, eraseFG Y = b))) ∧
    (∀ o t s a K, required o t → (toWire p o).decode = some (.vote s a K) →
      let v := baseVote (⟨.seat (.head s) a, K⟩ : HeadWire p.n)
      (v ∈ st.base.votes ∧ GridCO.stampVote st.base v < dl t) ∨
      ∃ v₁ ∈ st.base.votes, ∃ v₂ ∈ st.base.votes,
        v₁ ≠ v₂ ∧ GridCO.headLabel? v₁ = some s ∧ GridCO.headLabel? v₂ = some s ∧
        GridCO.headSeat? v₁ = some a ∧ GridCO.headSeat? v₂ = some a ∧
        GridCO.stampVote st.base v₁ < dl t ∧ GridCO.stampVote st.base v₂ < dl t) := by
  intro p In V inst c E rho dl cut D first x B required paths hRoots hDelta hExecution
    hx h hReady
  apply fgsa_receiptCoverage_anchor_on E rho dl cut D first x B required paths
    hRoots hDelta hExecution hx h
  intro o t hr
  obtain ⟨a, hta, ha, had, hT, hHistory, hRF, hfirst, hdl, hWF, hw⟩ := h.slotWindow o t hr
  refine ⟨a, hta, ha, had, hT, hHistory, hRF, hfirst, hdl, hWF, hw, ?_⟩
  intro j u hau hud hh
  exact hReady o t hr j u (hta.trans hau) (hud.trans_le hdl) hh

/-- Active paths from receiver-local sleep receipt coverage. -/
theorem fgsa_active_path_of_coverage_on (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hDelta : E.Δ = p.Δ)
    (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (K : Block)
    (required : Obj p → Time → Prop) (paths : Block → Time → Prop)
    (hx : x ∈ rho.honest)
    (hcov : ReceiptCoverageSleepPremises E rho dl cut D first x K required paths)
    (hpath : paths K D)
    (hFK : Block.Preceq (eraseFG (V2.D.Run.stateBeforeTime E rho D x).st.fg.F) K)
    (hroots : NamedReceiptRootCollisionFree p c E rho)
    (hReady : ∀ o t, required o t → ∀ j u, t ≤ u → u < dl t →
      V2.D.Run.handlesAt E rho j x o u →
      (fgsa p c).wellFormed o = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x) o = true ∧
      fgsaTimely p (V2.D.Run.stateBefore E rho j x) o) :
    ∀ X, Block.Preceq X K → X ∈ (actView (V2.D.Run.stateBeforeTime E rho D x).st).blocks := by
  let st := (V2.D.Run.stateBeforeTime E rho D x).st
  have hc := (fgsa_receiptCoverage_on E rho dl cut D first x K required paths
    hroots hDelta hE hx hcov hReady).1
  have hb := (storeBundle_stateBeforeTime E rho D x).cstore
  have hK : K ∈ (actView st).blocks := by
    rcases hc with ⟨hKF, _⟩ | ⟨_, _, hpaths⟩
    · have heq : K = eraseFG st.fg.F := Gen.Pure.block_preceq_antisymm hKF hFK
      rw [heq]
      exact (actView_genesis_F p st hb).2
    · obtain ⟨Y, hY, hYK⟩ := hpaths K D hpath K (Gen.Pure.block_preceq_refl K)
      apply (actView_blocks st K).mpr
      refine ⟨(hb.baseTree K).mpr ⟨Y, hY, hYK⟩, ?_⟩
      exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K) hFK
  intro X hX
  exact actView_ancestor_closed p st hb hK hX


/-- Active paths use handler readiness at the same supplied receiver anchor. -/
theorem fgsa_active_path_of_coverage_anchor_on (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hDelta : E.Δ = p.Δ)
    (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (K : Block)
    (required : Obj p → Time → Prop) (paths : Block → Time → Prop)
    (hx : x ∈ rho.honest)
    (hcov : ReceiptCoverageSleepPremises E rho dl cut D first x K required paths)
    (hpath : paths K D)
    (hFK : Block.Preceq (eraseFG (V2.D.Run.stateBeforeTime E rho D x).st.fg.F) K)
    (hroots : NamedReceiptRootCollisionFree p c E rho)
    (hReady : ∀ o t, required o t → ∃ a, t ≤ a ∧ 0 ≤ a ∧ a < dl a ∧
      Gen.V2.Duty.ReadyTrigger E rho o t x a (dl a) ∧
      Gen.V2.Duty.HistorySafeAt E rho x o a ∧
      V2.D.restartFree rho x (V2.D.Run.actionCut rho a) (V2.D.Run.idxBefore rho D) ∧
      first ≤ V2.D.Run.actionCut rho a ∧ dl a ≤ dl t ∧
      (fgsa p c).wellFormed o = true ∧
      (∀ s signer K, (toWire p o).decode = some (.vote s signer K) →
        (V2.D.Run.stateBeforeTime E rho (dl t) x).st.slot p ≤ s + 1 ∧
        ∀ i t', V2.D.Run.actionCut rho a ≤ i → i < V2.D.Run.idxBefore rho (dl a) →
          a ≤ t' → V2.D.Run.handlesAt E rho i x o t' →
          s ≤ (V2.D.Run.stateBefore E rho i x).st.slot p ∧
            (V2.D.Run.stateBefore E rho i x).st.slot p ≤ s + 1) ∧
      ∀ j u, a ≤ u → u < dl a → V2.D.Run.handlesAt E rho j x o u →
        (fgsa p c).wellFormed o = true ∧
        (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x) o = true ∧
        fgsaTimely p (V2.D.Run.stateBefore E rho j x) o) :
    ∀ X, Block.Preceq X K → X ∈ (actView (V2.D.Run.stateBeforeTime E rho D x).st).blocks := by
  let st := (V2.D.Run.stateBeforeTime E rho D x).st
  have hc := (fgsa_receiptCoverage_anchor_on E rho dl cut D first x K required paths
    hroots hDelta hE hx hcov hReady).1
  have hb := (storeBundle_stateBeforeTime E rho D x).cstore
  have hK : K ∈ (actView st).blocks := by
    rcases hc with ⟨hKF, _⟩ | ⟨_, _, hpaths⟩
    · have heq : K = eraseFG st.fg.F := Gen.Pure.block_preceq_antisymm hKF hFK
      rw [heq]
      exact (actView_genesis_F p st hb).2
    · obtain ⟨Y, hY, hYK⟩ := hpaths K D hpath K (Gen.Pure.block_preceq_refl K)
      apply (actView_blocks st K).mpr
      refine ⟨(hb.baseTree K).mpr ⟨Y, hY, hYK⟩, ?_⟩
      exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K) hFK
  intro X hX
  exact actView_ancestor_closed p st hb hK hX


/-- Internal coverage binds all receiver obligations to one explicit anchor. -/
structure ReceiptCoverageAnchorPremises
    {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (B : Block)
    (required : Obj p → Time → Prop) (paths : Block → Time → Prop)
    (anchor : Obj p → Time → Time) : Prop where
  within : Gen.V2.Duty.DeliveryWithinOn E rho
    (fun o => ¬ isRowObject o) dl cut
  service : ∀ o t, required o t →
    let a := anchor o t
    0 ≤ t ∧ t ≤ a ∧ 0 ≤ a ∧ a < dl a ∧ dl a ≤ D ∧
    first ≤ V2.D.Run.actionCut rho a ∧
    Gen.V2.Duty.ReadyTrigger E rho o t x a (dl a) ∧
    Gen.V2.Duty.HistorySafeAt E rho x o a ∧
    V2.D.restartFree rho x
      (V2.D.Run.actionCut rho a) (V2.D.Run.idxBefore rho D) ∧
    (fgsa p c).wellFormed o = true
  slotWindow : ∀ o t, required o t →
    ∀ s signer K, (toWire p o).decode = some (.vote s signer K) →
    let a := anchor o t
    (V2.D.Run.stateBeforeTime E rho (dl a) x).st.slot p ≤ s + 1 ∧
    (∀ j u, a ≤ u → u < dl a →
      V2.D.Run.handlesAt E rho j x o u →
      s ≤ (V2.D.Run.stateBefore E rho j x).st.slot p ∧
      (V2.D.Run.stateBefore E rho j x).st.slot p ≤ s + 1)
  handlers : ∀ o t, required o t →
    ∀ j u, anchor o t ≤ u → u < dl (anchor o t) →
      V2.D.Run.handlesAt E rho j x o u →
      (fgsa p c).wellFormed o = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x) o = true ∧
      fgsaTimely p (V2.D.Run.stateBefore E rho j x) o
  compat : ∀ i, first ≤ i → i ≤ V2.D.Run.idxBefore rho D →
    Block.Compatible B (eraseFG (V2.D.Run.stateBefore E rho i x).st.fg.F)
  deadline : Monotone dl ∧ D ≤ cut ∧ cut ≤ rho.horizon ∧
    first ≤ V2.D.Run.idxBefore rho D
  pathCoverage : ∀ K d, paths K d → Block.Preceq B K ∧ d ≤ D ∧
    ∀ b, Block.Preceq b K → b ≠ .genesis →
      ∃ o t s N, N.erase = b ∧ required o t ∧
        (toWire p o).decode = some (.block s N) ∧
        dl (anchor o t) ≤ d
  proposalPaths : ∀ o t s N, required o t →
    (toWire p o).decode = some (.block s N) →
    ∃ K d, paths K d ∧ Block.Preceq N.erase K

def ReceiptCoverageAnchorStatement : Prop :=
  ∀ {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (B : Block)
    (required : Obj p → Time → Prop) (paths : Block → Time → Prop)
    (anchor : Obj p → Time → Time),
    NamedReceiptRootCollisionFree p c E rho → E.Δ = p.Δ →
    V2.D.ExecutionValid E rho → x ∈ rho.honest →
    ReceiptCoverageAnchorPremises E rho dl cut D first x B
      required paths anchor →
    let st := (V2.D.Run.stateBeforeTime E rho D x).st
    ((Block.Preceq B (eraseFG st.fg.F) ∧
      Block.Preceq B st.base.stableRecord ∧
      (∀ s, 0 < s → Block.Preceq B (headVote p st s)) ∧
      (∀ raw sup, Block.Preceq B (getHead p st raw sup)) ∧
      Block.Preceq B (fgHead p st) ∧
      (∀ lease ∈ st.base.obligations, Block.Compatible B lease.1)) ∨
     (Block.Preceq (eraseFG st.fg.F) B ∧
      (∀ o t s N, required o t →
        (toWire p o).decode = some (.block s N) →
        ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho
          (dl (anchor o t)) x).st.fg.TF, eraseFG Y = N.erase) ∧
      (∀ K d, paths K d → ∀ b, Block.Preceq b K →
        ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho d x).st.fg.TF,
          eraseFG Y = b))) ∧
    (∀ o t s signer K, required o t →
      (toWire p o).decode = some (.vote s signer K) →
      let v := baseVote (⟨.seat (.head s) signer, K⟩ : HeadWire p.n)
      (v ∈ st.base.votes ∧
        GridCO.stampVote st.base v < dl (anchor o t)) ∨
      ∃ v₁ ∈ st.base.votes, ∃ v₂ ∈ st.base.votes,
        v₁ ≠ v₂ ∧
        GridCO.headLabel? v₁ = some s ∧ GridCO.headLabel? v₂ = some s ∧
        GridCO.headSeat? v₁ = some signer ∧ GridCO.headSeat? v₂ = some signer ∧
        GridCO.stampVote st.base v₁ < dl (anchor o t) ∧
        GridCO.stampVote st.base v₂ < dl (anchor o t))

/-- Anchor-relative receipt coverage follows from receiver-local N4 service. -/
theorem fgsa_receiptCoverage_anchor : ReceiptCoverageAnchorStatement := by
  intro p In V inst c E rho dl cut D first x B required paths anchor hRoots hDelta hExecution
    hx h
  have hS := hExecution.toScheduleWellFormed
  have hidx := fgsa_idxBefore_mono rho
  have hf (a : Time) (ha : a ≤ D) :
      Block.Preceq (eraseFG (V2.D.Run.stateBeforeTime E rho a x).st.fg.F)
        (eraseFG (V2.D.Run.stateBeforeTime E rho D x).st.fg.F) := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho a hS,
      ← Gen.V2.Duty.stateBefore_idxBefore E rho D hS]
    have hm := fgsa_monoAlong_preceq_F p c (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho a) x).st.fg.F
    rw [Gen.V2.Duty.MonoAlong_def] at hm
    apply eraseFG_preceq
    apply V2.D.Engine.stateBefore_stable_restore _ hm.1 hm.2.1 hm.2.2
      E rho (hidx ha) x
    · intro nd w hh
      change FGBlock.Preceq (V2.D.Run.stateBefore E rho
        (V2.D.Run.idxBefore rho a) x).st.fg.F (acRestart p nd.st w).fg.F
      rwa [acRestart_fg]
    · exact KitFG.preceq_refl _
  have hstore := storeBundle_stateBeforeTime E rho D x
  constructor
  · have hcompat := h.compat _ h.deadline.2.2.2 (le_refl _)
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho D hS] at hcompat
    change (Block.preceq B (eraseFG (V2.D.Run.stateBeforeTime E rho D x).st.fg.F) ||
      Block.preceq (eraseFG (V2.D.Run.stateBeforeTime E rho D x).st.fg.F) B) = true at hcompat
    simp only [Bool.or_eq_true] at hcompat
    rcases hcompat with hBF | hFB
    · left
      refine ⟨hBF, Gen.Pure.block_preceq_trans hBF hstore.nest,
        (fun s hs => preceq_headVote_of_preceq_F p _ hstore.cstore hBF hs),
        preceq_getHead_of_preceq_F p _ hstore.cstore hBF,
        preceq_fgHead_of_preceq_F p _ hstore.cstore hBF, ?_⟩
      intro lease hl
      have hlc := hstore.cstore.saCompat.1 lease hl
      change Block.compatible lease.1 _ = true at hlc
      rw [Gen.Pure.block_compatible_comm] at hlc
      exact Gen.Pure.block_compatible_of_preceq_compatible hBF hlc
    · right
      have hproposal : ∀ o t s N, required o t →
          (toWire p o).decode = some (.block s N) →
          ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho (dl (anchor o t)) x).st.fg.TF,
            eraseFG Y = N.erase := by
        intro o t s N hr hd
        obtain ⟨K, d, hk, hbK⟩ := h.proposalPaths o t s N hr hd
        have hBK := (h.pathCoverage K d hk).1
        let a := anchor o t
        obtain ⟨_, hta, ha, had, hdl, _, hT, hHistory, hRF, _⟩ := h.service o t hr
        have hReadyAt := h.handlers o t hr
        have ho : o = ofWire p ⟨.proposer s, .proposal N⟩ := by
          apply toWire_injective
          rw [toWire_ofWire]
          exact decode_eq_block.mp hd
        have hFK := Gen.Pure.block_preceq_trans
          (Gen.Pure.block_preceq_trans (hf (dl a) hdl) hFB) hBK
        have hbF := Gen.Pure.block_compatible_of_common hbK hFK
        have hTrigger : Gen.V2.Duty.Trigger E rho o t := by
          obtain ⟨v, hv, htr, _⟩ := hT
          rcases htr with he | ⟨i, hi⟩
          · exact Or.inl ⟨v, hv, he⟩
          · exact Or.inr ⟨v, hv, i, hi⟩
        change Block.compatible N.erase
          (eraseFG (V2.D.Run.stateBeforeTime E rho (dl a) x).st.fg.F) = true at hbF
        have hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl a) x) o = false := by
          change excludesS p _ o = false
          dsimp only [excludesS]
          rw [hd]
          simp only [blockExcluded, activeCompatible, hbF, Bool.not_true, Bool.false_or]
          exact fgsa_trigger_invalid_false E rho o t s N hTrigger hd _
        change Gen.V2.Duty.ReadyTrigger E rho o t x a (dl a) at hT
        change Gen.V2.Duty.HistorySafeAt E rho x o a at hHistory
        rw [ho] at hT hHistory hNX
        let service : ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
            t (dl a) x := {
          dl := dl, cut := cut, anchor := a, within := h.within, ready := hT
          send_le := hta, nonneg := ha, later := had
          cut_le := hdl.trans h.deadline.2.1
          horizon := hdl.trans (h.deadline.2.1.trans h.deadline.2.2.1)
          freeze_le := le_rfl, history := hHistory
          epoch := hRF.mono le_rfl (hidx hdl)
          handlers := by
            intro j u hau hud hh
            rw [← ho] at hh ⊢
            exact hReadyAt j u hau hud hh
          not_excluded := hNX }
        exact service.proposal hS hx hRoots
      refine ⟨hFB, hproposal, ?_⟩
      intro K d hk b hb
      by_cases hg : b = .genesis
      · subst b
        exact ⟨.genesis, (storeBundle_stateBeforeTime E rho d x).cstore.fg.gen, rfl⟩
      · obtain ⟨o, t, s, N, heN, hr, hd, htd⟩ :=
          (h.pathCoverage K d hk).2.2 b hb hg
        obtain ⟨Y, hY, he⟩ := hproposal o t s N hr hd
        rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (dl (anchor o t)) hS] at hY
        rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hS]
        exact ⟨Y, (fgsa_store_durable p c E rho (hidx htd) x).1 hY, he.trans heN⟩
  · intro o t s signer K hr hd
    let a := anchor o t
    obtain ⟨_, hta, ha, had, hdl, _, hT, hHistory, hRF, _⟩ := h.service o t hr
    have hw := h.slotWindow o t hr
    have hReadyAt := h.handlers o t hr
    have ho : o = ofHead p ⟨.seat (.head s) signer, K⟩ := by
      apply toWire_injective
      rw [toWire_ofHead]
      exact decode_eq_vote.mp hd
    have hcum := fgsa_store_cumulative_on p c E rho (hidx hdl) x
      (hRF.mono (Gen.V2.Duty.actionCut_le_idxBefore hS had) le_rfl)
    have keep (v : GridCO.Wire p.n .root)
        (hm : v ∈ (V2.D.Run.stateBeforeTime E rho (dl a) x).st.base.votes) :
        v ∈ (V2.D.Run.stateBeforeTime E rho D x).st.base.votes ∧
        GridCO.stampVote (V2.D.Run.stateBeforeTime E rho D x).st.base v =
          GridCO.stampVote (V2.D.Run.stateBeforeTime E rho (dl a) x).st.base v := by
      rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (dl a) hS] at hm ⊢
      rw [← Gen.V2.Duty.stateBefore_idxBefore E rho D hS]
      refine ⟨?_, count_stamp_kept E rho x _ _ v hm hcum.2.2.2.1⟩
      rw [← fgsa_vote_stamp_keys E rho _ x] at hm ⊢
      exact List.mem_map.mpr (by
        obtain ⟨row, hrow, he⟩ := List.mem_map.mp hm
        exact ⟨row, hcum.2.2.2.1.subset hrow, he⟩)
    by_cases hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl a) x) o = false
    · change Gen.V2.Duty.ReadyTrigger E rho o t x a (dl a) at hT
      change Gen.V2.Duty.HistorySafeAt E rho x o a at hHistory
      rw [ho] at hT hHistory hNX
      have hp := (fgsa_head_receipt_on E rho hS dl cut s signer K t a (dl a) x h.within
        hT hx hta ha had (hdl.trans h.deadline.2.1)
        (hdl.trans (h.deadline.2.1.trans h.deadline.2.2.1)) le_rfl hHistory
        (hRF.mono le_rfl (hidx hdl)) (by
          intro j u hau hud hh
          rw [← ho] at hh ⊢
          exact hReadyAt j u hau hud hh) hNX).1
      have hk := keep _ hp
      exact Or.inl ⟨hk.1, hk.2.trans_lt
        (fgsa_head_stamp_before_read E rho hS x (dl a) s signer K hp)⟩
    · have hn : excludesS p (V2.D.Run.stateBeforeTime E rho (dl a) x).st o = true :=
        Bool.eq_true_of_ne_false hNX
      rw [ho] at hn
      have hwindow := (hw s signer K hd).1
      obtain ⟨v₁, h₁, v₂, h₂, hn, hl₁, hl₂, ha₁, ha₂, hs₁, hs₂⟩ :=
        fgsa_head_excluded_before E rho hS x (dl a) s signer K hwindow hn
      have hk₁ := keep _ h₁
      have hk₂ := keep _ h₂
      exact Or.inr ⟨v₁, hk₁.1, v₂, hk₂.1, hn, hl₁, hl₂, ha₁, ha₂,
        hk₁.2.trans_lt hs₁, hk₂.2.trans_lt hs₂⟩


/-- Active paths use the same anchor deadlines as receipt coverage. -/
theorem fgsa_active_path_of_coverage_anchor
    {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (K : Block)
    (required : Obj p → Time → Prop) (paths : Block → Time → Prop)
    (anchor : Obj p → Time → Time)
    (hx : x ∈ rho.honest)
    (hcov : ReceiptCoverageAnchorPremises E rho dl cut D first x K
      required paths anchor)
    (hpath : paths K D)
    (hFK : Block.Preceq
      (eraseFG (V2.D.Run.stateBeforeTime E rho D x).st.fg.F) K)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ X, Block.Preceq X K →
      X ∈ (actView (V2.D.Run.stateBeforeTime E rho D x).st).blocks := by
  let st := (V2.D.Run.stateBeforeTime E rho D x).st
  have hc := (fgsa_receiptCoverage_anchor E rho dl cut D first x K required paths anchor
    hroots hDelta hE hx hcov).1
  have hb := (storeBundle_stateBeforeTime E rho D x).cstore
  have hK : K ∈ (actView st).blocks := by
    rcases hc with ⟨hKF, _⟩ | ⟨_, _, hpaths⟩
    · have heq : K = eraseFG st.fg.F := Gen.Pure.block_preceq_antisymm hKF hFK
      rw [heq]
      exact (actView_genesis_F p st hb).2
    · obtain ⟨Y, hY, hYK⟩ := hpaths K D hpath K (Gen.Pure.block_preceq_refl K)
      apply (actView_blocks st K).mpr
      refine ⟨(hb.baseTree K).mpr ⟨Y, hY, hYK⟩, ?_⟩
      exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K) hFK
  intro X hX
  exact actView_ancestor_closed p st hb hK hX

/-- Stored honest HEADs have joined duty origin, including replayed votes. -/
theorem fgsa_stored_honest_head_joined (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (i : Nat) (x : V) (s : Slot) (k : Fin p.n) (o : GridCO.Wire p.n .root)
    (ho : o ∈ (storeAt p c E rho i x).base.votes)
    (hl : GridCO.headLabel? o = some s) (hk : GridCO.headSeat? o = some k)
    (hh : rho.seatOf (.base (.head s)) k ∈ rho.honest) :
    joinedAt p E rho (rho.seatOf (.base (.head s)) k) s (SA.voteTime p.toParams s) := by
  obtain ⟨K, rfl⟩ := count_head_keys o s k hl hk
  change _ ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes at ho
  rw [← fgsa_vote_stamp_keys E rho i x] at ho
  obtain ⟨⟨v, stamp⟩, hv, hvEq⟩ := List.mem_map.mp ho
  dsimp only at hvEq
  subst v
  obtain ⟨t, j', ht, he⟩ := count_head_signed_origin E rho hE i x s k K stamp hv hh
  have hoemit := he
  rw [(V2.D.Run.step_tick_eq E rho ht).2] at he
  have hem := (fgsa_emits_head E rho _ _ t s k K).mp he
  have htime := hem.2.1
  subst t
  exact fgsa_joinedAt_of_emitted_head E rho hE ht hoemit

/-- The batch denominator counts joined honest voters at the exact duty tick. -/
theorem fgsa_late_rest_bound_joined [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c))
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hE : V2.D.ExecutionValid E rho) (i : Nat) (x : V) (s : Slot) (H : Finset (Fin p.n))
    (hH : ∀ k, rho.seatOf (.base (.head s)) k ∈ rho.honest →
      joinedAt p E rho (rho.seatOf (.base (.head s)) k) s (SA.voteTime p.toParams s) → k ∈ H) :
    let v := actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    ((GridCO.seats p.n (GridCO.lateVotes p.toParams.engine v s)).toFinset \ H).card ≤
      (Gen.V2.Duty.faulty rho).card := by
  intro v
  apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head s)))
  · intro k hk
    obtain ⟨hl, hn⟩ := Finset.mem_sdiff.mp hk
    rw [Gen.V2.Duty.faulty_def]
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hh
    apply hn (hH k hh ?_)
    obtain ⟨o, ho, hs⟩ := (Gen.AC.Root.vote_pool_mem_seats _ k).mp hl
    have hlabel : GridCO.headLabel? o = some s :=
      beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp ho).1).2
    have hm : o ∈ (storeAt p c E rho i x).base.votes := by
      have h := (List.mem_filter.mp (List.mem_filter.mp ho).1).1
      change o ∈ (clockPre p (storeAt p c E rho i x) _).base.votes at h
      rw [(Internal.clockPre_vn _ _).1] at h
      exact h
    exact fgsa_stored_honest_head_joined E rho hE i x s k o hm hlabel hs hh
  · intro k _ j _ he
    exact (hC (.base (.head s)) trivial).injective he

/-- The batch denominator counts joined honest voters at the exact duty tick. -/
theorem fgsa_gate_batch_premises_joined [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (i : Nat) (x : V) (s : Slot) (B : Block) (H : Finset (Fin p.n))
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card)
    (hH : ∀ k, rho.seatOf (.base (.head s)) k ∈ rho.honest →
      joinedAt p E rho (rho.seatOf (.base (.head s)) k) s (SA.voteTime p.toParams s) → k ∈ H)
    (hheads : ∀ k ∈ H, ∃ K t,
      rho.seatOf (.base (.head s)) k ∈ rho.honest ∧
      V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) k)
        (ofHead p ⟨.seat (.head s) k, K.root⟩) t ∧
      baseVote (⟨.seat (.head s) k, K.root⟩ : HeadWire p.n) ∈
        (storeAt p c E rho i x).base.votes ∧
      K ∈ (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))).blocks ∧
      K.slot ≤ s ∧
      GridCO.stampVote
        (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)))
        (baseVote (⟨.seat (.head s) k, K.root⟩ : HeadWire p.n)) < GridCO.earlyTime
            p.toParams.engine s ∧
      GridCO.stampBlock
        (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) K <
        GridCO.earlyTime p.toParams.engine s ∧
      Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i x)
        (SA.gateTime p.toParams s)).fg.F) K ∧ Block.Preceq B K) :
    let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
    let v := actView pre
    let a := eraseFG pre.fg.F
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s a ∧
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s B ∧
    (∀ X, Block.Preceq a X → Block.Preceq X B → X ≠ a → X ∈ v.blocks) := by
  intro pre v a
  have hsupp (X : Block) (hX : X = a ∨ X = B) :
      ∀ k ∈ H, Gen.AC.Root.poolSupports v.blocks
        (GridCO.cleanSupport p.toParams.engine v s) k X = true := by
    intro k hk
    obtain ⟨K, t, hh, he, hv, hK, hslot, hvs, hbs, haK, hBK⟩ := hheads k hk
    apply fgsa_active_support_of_receipt E rho hE i x s k K X t hh he hv hK hslot hvs hbs
    rcases hX with rfl | rfl
    · exact haK
    · exact hBK
  have hrest := fgsa_late_rest_bound_joined E rho hC hE i x s H hH
  have hcount (X : Block) (hX : X = a ∨ X = B) :
      GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
        2 * SA.Root.prefixSupport p.toParams v s X := by
    have hc := Gen.AC.Root.batch_counts v.blocks (GridCO.lateVotes p.toParams.engine v s)
      (GridCO.cleanSupport p.toParams.engine v s) (GridCO.cleanSupport p.toParams.engine v s)
      H H.card (Gen.V2.Duty.faulty rho).card X
      (fun _ ho => fgsa_early_subset_late p v s (List.mem_filter.mp ho).1)
      (fun _ ho => ho) rfl (fun k _ => fgsa_cleanSupport_no_equivocation p v s k)
      (hsupp X hX) hrest hbatch
    have he := actView_score p pre
      (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x) _)
      (by rw [clockPre_headDomain]; exact base_headDomain_none p (reachable_stateBefore E rho i x))
      (GridCO.cleanSupport p.toParams.engine v s) (GridCO.cleanSupport p.toParams.engine v s) X
    change _ < 2 * GridCO.goldfishScoreOn (GridCO.resolutionTree v) v.blocks _ _ X
    rw [he]
    exact (hc.2.2.1 X (Gen.Pure.block_preceq_refl X)).2
  refine ⟨hcount a (Or.inl rfl), hcount B (Or.inr rfl), ?_⟩
  intro X _ hXB _
  have hpos : 0 < H.card := lt_of_le_of_lt (Nat.zero_le _) hbatch.lt
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  obtain ⟨K, _, _, _, _, hK, _, _, _, _, hBK⟩ := hheads k hk
  have hstore := cstoreInv_clockPre p (storeAt p c E rho i x)
    (storeBundle_stateBefore E rho i x).cstore (SA.gateTime p.toParams s)
  exact actView_ancestor_closed p pre hstore hK (Gen.Pure.block_preceq_trans hXB hBK)

/-- An actual honest emitted HEAD cannot be excluded in its label window.
Stored or replayed copies have the same signed target. -/
theorem fgsa_honest_head_not_excluded (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    {s : Slot} {q : Fin p.n} {b : BlockId} {send d : Time} {x : V}
    (hh : rho.seatOf (.base (.head s)) q ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
      (ofHead p ⟨.seat (.head s) q, b⟩) send)
    (hWindow : (rho.stateBeforeTime E d x).st.slot p ≤ s + 1) :
    (fgsa p c).excludes (rho.stateBeforeTime E d x)
      (ofHead p ⟨.seat (.head s) q, b⟩) = false := by
  by_contra hn
  obtain ⟨u, hu, v, hv, hne, hlu, hlv, hqu, hqv, _, _⟩ :=
    fgsa_head_excluded_before E rho hE.toScheduleWellFormed x d s q b hWindow
      (Bool.eq_true_of_ne_false hn)
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hE.toScheduleWellFormed] at hu hv
  have hU := fgsa_honest_head_eq_of_stored E rho hE _ x s q b send hh he u hu hlu hqu
  have hV := fgsa_honest_head_eq_of_stored E rho hE _ x s q b send hh he v hv hlv hqv
  exact hne (hU.trans hV.symm)

end AvailableChain.FGSA.Run
end
