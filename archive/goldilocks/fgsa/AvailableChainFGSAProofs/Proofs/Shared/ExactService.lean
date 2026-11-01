module
public import AvailableChainFGSAProofs.Proofs.Shared.GateReceipt
public import AvailableChainFGSAProofs.Proofs.Shared.Count
public import AvailableChainFGSAProofs.Proofs.Shared.OpeningSource
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.22, H3: the emitted HEAD is the scheduled HEAD read.
DC: Handlers/GoldfishVotePool.lean:320, unique honest vote at a label.
INTENTIONAL: FG-SA identifies its post-clock read with the actual signed
HEAD. This uses the SA HEAD label and does not use an FG row round. -/
theorem exactService_emitted_head (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (s : Slot) (Q : Block)
    (hhead : ∀ y ∈ rho.honest, headAtLabel p c E rho y s = some Q)
    (q : Fin p.n) (hy : rho.seatOf (.base (.head s)) q ∈ rho.honest)
    (K : Block) (t : Time)
    (he : HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
      (ofHead p ⟨.seat (.head s) q, K.root⟩) t K) : K = Q := by
  have hObserver := he
  obtain ⟨j, _, _, hj, hem, _, _⟩ := he
  have hK := headTargetAtEmission_at_tick E rho hs hObserver hj rfl
  rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem
  obtain ⟨_, ht, _, _, _⟩ := (fgsa_emits_head E rho _ _ _ s q K.root).mp hem
  subst t
  have hr := hhead _ hy
  change (postClock E rho _ (SA.voteTime p.toParams s)).map
    (fun nd => headVote p nd.st s) = some Q at hr
  rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hj] at hr
  exact hK.trans (Option.some.inj hr)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 erratum 13 and blueprint 02:531–541, 21 H.22 H3.
DC: Goldfish/Confirmation.lean:434–441, HonestSupport.vote.
INTENTIONAL: exact HEAD reads specialize the Shared active receipts to Q;
the consumer supplies GateReceiptGeometry at the actual gate read.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem exactService_gate_receipts_of_head
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (s : Slot) (Q : Block)
    (hhead : ∀ y ∈ rho.honest, headAtLabel p c E rho y s = some Q)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s) (SA.gateTime p.toParams s))
    {i : Nat} {x : V} (ht : IsGateTick p c rho i x s)
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s Q)
    (q : Fin p.n) (hy : rho.seatOf (.base (.head s)) q ∈ rho.honest)
    (hawake : E.awake (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s) = true)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∃ t, V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
      (ofHead p ⟨.seat (.head s) q, Q.root⟩) t ∧
      baseVote (⟨.seat (.head s) q, Q.root⟩ : HeadWire p.n) ∈
        (storeAt p c E rho i x).base.votes ∧
      Q ∈ (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))).blocks ∧
      Q.slot ≤ s ∧
      GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x)
        (SA.gateTime p.toParams s))) (baseVote (⟨.seat (.head s) q, Q.root⟩ : HeadWire p.n)) <
          GridCO.earlyTime p.toParams.engine s ∧
      GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x)
        (SA.gateTime p.toParams s))) Q < GridCO.earlyTime p.toParams.engine s ∧
      Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i x)
        (SA.gateTime p.toParams s)).fg.F) Q := by
  obtain ⟨K, t, hh, he, hv, hK, hslot, hvs, hbs, hF, _⟩ :=
    fgsa_gateReceipt (hroots := hroots) E rho hE hN hDelta hC s hSync ht Q hgeom q hy hawake
  have hKm : K ∈ (rho.stateBefore E i x).st.base.blocks := by
    have hm := (List.mem_filter.mp hK).1
    change K ∈ (clockPre p _ _).base.blocks at hm
    rwa [(clockPre_fields p _ _).2.1] at hm
  have hObserver := headTargetAtEmission_of_stored E rho
    (hroots.toNamedRootCollisionFree E rho) he rfl i x hKm
  have heq := exactService_emitted_head E rho hE.toScheduleWellFormed s Q hhead q hh K t hObserver
  subst K
  exact ⟨t, he, hv, hK, hslot, hvs, hbs, hF⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 02:531–541 and 21 H.22 H3, exact raw result from honest HEADs.
DC: Goldfish/Confirmation.lean:494,508,567, honest support and exclusion.
INTENTIONAL: FG-SA uses the active F anchor and a late-vote denominator.
The SA participation count and GateReceiptGeometry are explicit inputs.
No slot equality for Q or FG row premise is needed.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem exactService_gate_raw_of_head [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (s : Slot) (Q : Block)
    (hhead : ∀ y ∈ rho.honest, headAtLabel p c E rho y s = some Q)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s) (SA.gateTime p.toParams s))
    {i : Nat} {x : V} (ht : IsGateTick p c rho i x s)
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s Q)
    (H : Finset (Fin p.n))
    (hH : ∀ q, q ∈ H ↔ rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s) = true)
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
    let v := actView pre
    SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) v s = some Q ∧
      H.card ≤ SA.Root.prefixSupport p.toParams v s Q ∧
      Q ∈ v.blocks ∧ Block.Preceq (eraseFG pre.fg.F) Q := by
  intro pre v
  have hrec (q : Fin p.n) (hq : q ∈ H) :=
    exactService_gate_receipts_of_head (hroots := hroots)
      E rho hE hN hDelta hC s Q hhead hSync ht hgeom
      q ((hH q).mp hq).1 ((hH q).mp hq).2
  have hheads (q : Fin p.n) (hq : q ∈ H) := hrec q hq
  have hcover := fgsa_gate_batch_premises E rho hE hC i x s Q H hbatch
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
    hsupp (fgsa_late_rest_bound E rho hC hE i x s H
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

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.22 H3 and spec 297–298, 457–461: read the saved fast write.
DC: Grades/RecoveryCapturedActionCarrier.lean:30, the action store after confirmation.
INTENTIONAL: FG-SA saves a fast-write list at each SA gate label. This
adapter exposes that saved list, including at labels with no action. -/
theorem exactService_fastWrite_of_gateService
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (i : Nat) (x : V) (s : Slot) (Q : Block)
    (ht : IsGateTick p c rho i x s)
    (hEnabled : enabledGateAt p c E rho i x s)
    (hservice : Gen.AC.Duty.GateService (fgsaAC E rho) i s x Q) :
    Q ∈ (fastWriteAt (((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
      (SA.gateTime p.toParams s)).st) s).getD [] := by
  let nd := V2.D.Run.stateBefore E rho i x
  let st := ((fgsa p c).clock nd (SA.gateTime p.toParams s)).st
  have hf := fgsa_gate_fresh E rho hs ht
  have hinv := (storeBundle_postClock E rho i x (SA.gateTime p.toParams s)).cstore
  obtain ⟨_, _, _, _, hfast, _⟩ := hservice
  have hfastEq : st.fastWrite = nd.st.fastWrite ++ [(s, (fgsaAC E rho).fast i s x)] := by
    have hb := congrArg State.fastWrite (fgsa_gate_clock_bridge E rho hs ht
      (fgsa_gate_joined_of_enabled E rho hEnabled))
    rw [normalizeS_fields] at hb
    change st.fastWrite = nd.st.fastWrite ++ [(s, fastSet p (eraseFG nd.st.fg.F)
      (actView (clockPre p nd.st (SA.gateTime p.toParams s))) s)] at hb
    have hf' : GridCO.savedGenuine (clockPre p nd.st (SA.gateTime p.toParams s)).base s = none := by
      unfold GridCO.savedGenuine
      rw [clockPre_genuine]
      exact hf
    have hr : (fgsaAC E rho).fast i s x = fastSet p (eraseFG nd.st.fg.F)
        (actView (clockPre p nd.st (SA.gateTime p.toParams s))) s := by
      change (if (GridCO.savedGenuine (clockPre p nd.st (SA.gateTime p.toParams s)).base
        s).isSome then [] else _) = _
      rw [hf']
      simp only [Option.isSome_none, Bool.false_eq_true, ite_false, clockPre_fg]
      rfl
    rw [hr]
    exact hb
  have hrow : (s, (fgsaAC E rho).fast i s x) ∈ st.fastWrite := by
    rw [hfastEq]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  have hfind : st.fastWrite.find? (fun row => row.1 == s) =
      some (s, (fgsaAC E rho).fast i s x) := by
    cases he : st.fastWrite.find? (fun row => row.1 == s) with
    | none => have hn := List.find?_eq_none.mp he _ hrow; simp at hn
    | some row =>
      have hk : row.1 = s := by simpa using List.find?_some he
      exact congrArg some (List.inj_on_of_nodup_map hinv.fastDom.1
        (List.mem_of_find?_eq_some he) hrow hk)
  change Q ∈ (((st.fastWrite.find? (fun row => row.1 == s)).map Prod.snd).getD [])
  simpa only [hfind, Option.map_some, Option.getD_some] using hfast

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 A.9 / F1b.7 and blueprint 21 H.17 / H.22 H3.
DC: UserConfirmationRecovery.lean:235 and Goldfish/Confirmation.lean:434.
INTENTIONAL: the FG-SA consumer supplies the active receipt floor, lease
compatibility, the old-output bound, and a retained opening representative.
The selector maximum follows from the exact post-gate output and live leases;
it is not an extra premise. No FG row or lane theorem supplies these fields. -/
structure ExactServiceGateGeometry (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) (s : Slot) (Q : Block) : Prop
    extends GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s Q where
  guard : ∀ lease ∈ ((fgsaAC E rho).gateView i x s).obligations,
    Block.Compatible (Gen.AC.Lease.target lease) Q
  old_output : Block.Preceq Q ((fgsaAC E rho).output i x) → (fgsaAC E rho).output i x = Q
  opening_domain : ∀ r, s = r * p.R →
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)).st
    ∃ D, eraseFG D = Q ∧ D ∈ domainR p st (treeT p st)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17, H.22 H3: exact output bounds every live candidate.
DC: Grades/RecoveryCapturedActionCarrier.lean:30, the shared action/gate store.
INTENTIONAL: FG-SA selects the deepest retained fresh candidate. A retained
representative and exact output suffice for its erased value; no separate
selector maximum or FG row premise is required. -/
theorem exactService_opening_of_gateService
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (i : Nat) (x : V) (r : Nat) (Q : Block)
    (ht : rho.events[i]? = some (.tick x (p.actionTime r)))
    (hEnabled : enabledGateAt p c E rho i x (r * p.R))
    (hservice : Gen.AC.Duty.GateService (fgsaAC E rho) i (r * p.R) x Q)
    (hout : (fgsaAC E rho).output (i + 1) x = Q)
    (hdom : ∃ D, eraseFG D = Q ∧
      D ∈ domainR p (((fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)).st)
        (treeT p (((fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)).st))) :
    actionSource p c E rho x r = some (some Q) := by
  let nd := V2.D.Run.stateBefore E rho i x
  let st := ((fgsa p c).clock nd (p.actionTime r)).st
  have hpost : (V2.D.Run.stateBefore E rho (i + 1) x).st = st := by
    rw [V2.D.Run.stateBefore_succ E rho ht]
    simp only [V2.D.World.step, Function.update_self]
    exact tick_st (c := c) E rho nd x (p.actionTime r)
  have hS : st.base.stableRecord = Q := by
    change (V2.D.Run.stateBefore E rho (i + 1) x).st.base.stableRecord = Q at hout
    rwa [hpost] at hout
  obtain ⟨D, hD, hkept⟩ := hdom
  have hserved : eraseFG D ∈ sourceCandidates p st := by
    rw [hD]
    exact openingSource_candidate_of_gateService E rho hs i x r Q ht hEnabled hservice
  obtain ⟨C, hC, hDC⟩ := openingSource_extends_served E rho i x r D hkept hserved
  have hm := hC
  rw [fgSource_eq_jointSource] at hm
  have hcand : eraseFG C ∈ sourceCandidates p st :=
    of_decide_eq_true (Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ hm).1).2
  rw [sourceCandidates_def] at hcand
  have hlive := (Finset.mem_filter.mp hcand).2
  change ((st.base.obligations.find? (fun row => row.1 == eraseFG C)).map
    (fun row => row.2.2)).any (fun d => decide (st.base.now < d)) = true at hlive
  have hbelow : Block.Preceq (eraseFG C) Q := by
    cases hf : st.base.obligations.find? (fun row => row.1 == eraseFG C) with
    | none => simp only [hf, Option.map_none, Option.any_none, Bool.false_eq_true] at hlive
    | some lease =>
      have htime : st.base.now < lease.2.2 := by
        simpa only [hf, Option.map_some, Option.any_some, decide_eq_true_eq] using hlive
      have he : lease.1 = eraseFG C := by simpa using List.find?_some hf
      have hb := (storeBundle_postClock E rho i x (p.actionTime r)).lease lease
        (List.mem_of_find?_eq_some hf) htime
      change Block.Preceq lease.1 st.base.stableRecord at hb
      rwa [he, hS] at hb
  have habove : Block.Preceq Q (eraseFG C) := hD ▸ eraseFG_preceq hDC
  have heq := block_preceq_antisymm hbelow habove
  change ((postClock E rho x (p.actionTime r)).map (fun nd => FGSA.fgSource p nd.st)).map
    (Option.map eraseFG) = some (some Q)
  rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs ht]
  change some ((FGSA.fgSource p st).map eraseFG) = some (some Q)
  rw [hC]
  exact congrArg (fun B => some (some B)) heq

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 A.9 / F1b.7; blueprint 21 H.22 H3, all gate clauses at one tick.
DC: Goldfish/Confirmation.lean:494,508,567; UserConfirmationRecovery.lean:235;
RecoveryCapturedActionCarrier.lean:30. INTENTIONAL: FG-SA combines the
optional raw result, whole-result guard, saved fast write, stable output,
and erased opening read. Geometry and the fast participation count remain
consumer premises; the proof does not obtain them from a lane.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem exactService_gate_at_of_head [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (s : Slot) (Q : Block) (hne : Q ≠ .genesis)
    (hhead : ∀ y ∈ rho.honest, headAtLabel p c E rho y s = some Q)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s) (SA.gateTime p.toParams s))
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho i x s)
    (hgeom : ExactServiceGateGeometry E rho i x s Q)
    (H : Finset (Fin p.n))
    (hH : ∀ q, q ∈ H ↔ rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s) = true)
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card)
    (hfast : SA.releaseThreshold p.toParams ≤ H.card)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    gateResult p c E rho x s = some (some Q) ∧
    (∃ j, enabledGateAt p c E rho j x s ∧ gatePassedAt p c E rho j) ∧
    (∃ nd, postClock E rho x (SA.gateTime p.toParams s) = some nd ∧
      Q ∈ (fastWriteAt nd.st s).getD []) ∧
    (fgsaInterface p c).stable (afterTicks E rho (SA.gateTime p.toParams s) x) = Q ∧
    (∀ r, s = r * p.R → actionSource p c E rho x r = some (some Q)) := by
  let st := storeAt p c E rho i x
  let pre := clockPre p st (SA.gateTime p.toParams s)
  let v := actView pre
  let w := (fgsaAC E rho).gateView i x s
  have hs := hE.toScheduleWellFormed
  have hEnabled := fgsa_enabledGate_noRestart E rho hN ht
  obtain ⟨hr, hcount, hmem, hanchor⟩ := exactService_gate_raw_of_head (hroots := hroots)
    E rho hE hN hDelta hC
    s Q hhead hSync ht hgeom.toGateReceiptGeometry H hH hbatch
  have hv : { v with early := st.base.early } = w := fgsa_clockPre_gateView p st s
  have hrawEq : SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) v s =
      (fgsaAC E rho).raw i s x := by
    rw [clockPre_fg]
    have he := congrArg (fun u => SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) u s) hv
    exact he
  have hraw : (fgsaAC E rho).raw i s x = some Q := hrawEq.symm.trans hr
  have hsupport : SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams w s Q := by
    have he := congrArg (fun u => SA.Root.prefixSupport p.toParams u s Q) hv
    exact he ▸ hfast.trans hcount
  have hmemw : Q ∈ w.blocks := (congrArg GridCO.State.blocks hv) ▸ hmem
  have hlevel : SA.releaseThreshold p.toParams ∈ (fgsaAC E rho).gateLevels i x s Q := by
    change SA.releaseThreshold p.toParams ∈
      @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine p.n .root w s Q
    change SA.releaseThreshold p.toParams ∈
      (if decide (SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams w s Q) ||
        GridCO.slowEligible p.toParams.engine w s Q then [SA.releaseThreshold p.toParams] else [])
    simp only [hsupport, decide_true, Bool.true_or, ite_true, List.mem_singleton]
  have hservice := fgsa_gate_of_coveringBatch E rho hs i s x Q ht hEnabled
    ⟨Q, hraw, block_preceq_refl Q⟩ (by
      intro C hC
      have he := Option.some.inj (hraw.symm.trans hC)
      subst C
      exact hgeom.guard) hne hmemw hsupport hlevel
  have hanchor' : Block.Preceq ((fgsaAC E rho).anchor i x) Q := by
    change Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) Q
    simpa only [clockPre_fg] using hanchor
  have hout := (fgsa_S_eq_of_exact E rho hs i s x Q hx ht hEnabled hraw
    hgeom.guard hgeom.old_output hanchor').1
  have hidx := fgsa_tickIdx_of_event p c E rho hs ht
  refine ⟨?_, ⟨i, hEnabled, ?_⟩, ?_, ?_, ?_⟩
  · rw [gateResult_eq_saved p c E rho hs ht]
    have hg := fgsa_gate_saved_result E rho hs ht
      (fgsa_gate_joined_of_enabled E rho hEnabled)
    change SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (V2.D.Run.stateBefore E rho i x).st
        (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (V2.D.Run.stateBefore E rho i x).st
        (SA.gateTime p.toParams s))) s = some Q at hr
    rw [clockPre_fg] at hr
    exact hg.trans (congrArg some hr)
  · refine ⟨x, s, hEnabled, ?_, Q, hr, ?_⟩
    · unfold GridCO.savedGenuine
      rw [clockPre_genuine]
      exact fgsa_gate_fresh E rho hs ht
    · apply List.any_eq_false.mpr
      intro lease hl
      have hlw : lease ∈ w.obligations := (congrArg GridCO.State.obligations hv) ▸ hl
      have hg : Block.compatible lease.1 Q = true := hgeom.guard lease hlw
      simp only [hg, Bool.not_true, Bool.false_eq_true, not_false_eq_true]
  · refine ⟨(fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (SA.gateTime p.toParams s), ?_,
      exactService_fastWrite_of_gateService E rho hs i x s Q ht hEnabled hservice⟩
    rw [postClock_def, preTick_def, hidx]
    rfl
  · rw [afterTicks_node E rho hs ht]
    change (V2.D.tick E rho (V2.D.Run.stateBefore E rho i x) x
      (SA.gateTime p.toParams s)).1.st.base.stableRecord = Q
    change (V2.D.Run.stateBefore E rho (i + 1) x).st.base.stableRecord = Q at hout
    rwa [(V2.D.Run.step_tick_eq E rho ht).1] at hout
  · intro r he
    subst s
    exact exactService_opening_of_gateService E rho hs i x r Q ht hEnabled hservice hout
      (hgeom.opening_domain r rfl)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 A.9; blueprint 21 H.22 H3: the gate clauses conditional on the HEAD clause.
DC: UserConfirmationRecovery.lean:235 and Goldfish/Confirmation.lean:494,508,567.
INTENTIONAL: J2 has separate finite HEAD and gate horizons. The caller supplies
SA participation, gate geometry, and vote-to-gate synchrony only when the gate
is in the horizon. Q is non-genesis because the fast set excludes genesis.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem exactService_gate_of_head [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (v : Slot) (Q : Block) (hne : Q ≠ .genesis)
    (hhead : SA.voteTime p.toParams v ≤ rho.horizon →
      ∀ x ∈ rho.honest, headAtLabel p c E rho x v = some Q)
    (hSync : SA.gateTime p.toParams v ≤ rho.horizon →
      Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams v) (SA.gateTime p.toParams v))
    (hparticipation : SA.gateTime p.toParams v ≤ rho.horizon →
      ∃ H : Finset (Fin p.n),
        (∀ q, q ∈ H ↔ rho.seatOf (.base (.head v)) q ∈ rho.honest ∧
          E.awake (rho.seatOf (.base (.head v)) q) (SA.voteTime p.toParams v) = true) ∧
        Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card ∧
        SA.releaseThreshold p.toParams ≤ H.card)
    (hgeometry : ∀ i x, x ∈ rho.honest → IsGateTick p c rho i x v →
      ExactServiceGateGeometry E rho i x v Q)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    SA.gateTime p.toParams v ≤ rho.horizon → ∀ x ∈ rho.honest,
      confirmedReaderAtIdx p c E rho x
        (afterTicksIdx rho (SA.gateTime p.toParams v)) (SA.gateTime p.toParams v) →
      gateResult p c E rho x v = some (some Q) ∧
      (∃ j, enabledGateAt p c E rho j x v ∧ gatePassedAt p c E rho j) ∧
      (∃ nd, postClock E rho x (SA.gateTime p.toParams v) = some nd ∧
        Q ∈ (fastWriteAt nd.st v).getD []) ∧
      (fgsaInterface p c).stable (afterTicks E rho (SA.gateTime p.toParams v) x) = Q ∧
      (∀ r, v = r * p.R → actionSource p c E rho x r = some (some Q)) := by
  intro hh x hx hreader
  have hvg : SA.voteTime p.toParams v ≤ SA.gateTime p.toParams v := by
    change 4 * p.Δ * (v : Int) + p.Δ ≤ 4 * p.Δ * (v : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have htime : ((4 * v + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams v := by
    change ((4 * v + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (v : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨i, hi, _⟩ := fgsa_tick_total E rho hE.toScheduleWellFormed hDelta x hx
    (4 * v + 6) (htime ▸ hh)
    (by simpa only [htime] using hreader.2.1)
  rw [htime] at hi
  obtain ⟨H, hH, hbatch, hfast⟩ := hparticipation hh
  exact exactService_gate_at_of_head (hroots := hroots) E rho hE hN hDelta hC v Q hne
    (hhead (hvg.trans hh)) (hSync hh) hx hi (hgeometry i x hx hi) H hH hbatch hfast

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 A.9; blueprint 21 H.22 H3, composition with the supplied HEAD clause.
DC: UserConfirmationRecovery.lean:235 and Goldfish/Confirmation.lean:434–441.
INTENTIONAL: this is the complete J2 conjunction with its two horizons;
the HEAD producer remains a separate input. The gate premises are unchanged.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem exactService_of_head_and_gate [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (v : Slot) (Q : Block) (hne : Q ≠ .genesis)
    (hhead : SA.voteTime p.toParams v ≤ rho.horizon →
      ∀ x ∈ rho.honest, headAtLabel p c E rho x v = some Q)
    (hSync : SA.gateTime p.toParams v ≤ rho.horizon →
      Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams v) (SA.gateTime p.toParams v))
    (hparticipation : SA.gateTime p.toParams v ≤ rho.horizon →
      ∃ H : Finset (Fin p.n),
        (∀ q, q ∈ H ↔ rho.seatOf (.base (.head v)) q ∈ rho.honest ∧
          E.awake (rho.seatOf (.base (.head v)) q) (SA.voteTime p.toParams v) = true) ∧
        Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card ∧
        SA.releaseThreshold p.toParams ≤ H.card)
    (hgeometry : ∀ i x, x ∈ rho.honest → IsGateTick p c rho i x v →
      ExactServiceGateGeometry E rho i x v Q)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ExactService p c E rho v Q :=
  ⟨(fun hh x hx _ => hhead hh x hx), exactService_gate_of_head (hroots := hroots)
    E rho hE hN hDelta hC v Q hne hhead hSync
    hparticipation hgeometry⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 02:531–541: express SA participation with the actual HEAD seats.
DC: Goldfish/Confirmation.lean:434–441, honest committee membership.
INTENTIONAL: the FG-SA fresh HEAD seat map is a bijection. This transfers
awake-honest cardinality without any linked FG seat or FG round. -/
theorem exactService_participation_of_card [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (v : Slot)
    (hbatch : Gen.Pure.Batch (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams v)).card
      (Gen.V2.Duty.faulty rho).card)
    (hfast : SA.releaseThreshold p.toParams ≤
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams v)).card) :
    ∃ H : Finset (Fin p.n),
      (∀ q, q ∈ H ↔ rho.seatOf (.base (.head v)) q ∈ rho.honest ∧
        E.awake (rho.seatOf (.base (.head v)) q) (SA.voteTime p.toParams v) = true) ∧
      Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card ∧
      SA.releaseThreshold p.toParams ≤ H.card := by
  classical
  let H := Finset.univ.filter (fun q : Fin p.n =>
    rho.seatOf (.base (.head v)) q ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head v)) q) (SA.voteTime p.toParams v) = true)
  have hH (q : Fin p.n) : q ∈ H ↔ rho.seatOf (.base (.head v)) q ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head v)) q) (SA.voteTime p.toParams v) = true := by
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
  have hbij : Function.Bijective (fun q : Fin p.n => rho.seatOf (.base (.head v)) q) :=
    hC (.base (.head v)) trivial
  have himage : H.image (rho.seatOf (.base (.head v))) =
      Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams v) := by
    ext y
    rw [Gen.V2.Duty.awakeHonest_def, Finset.mem_filter]
    constructor
    · intro hy
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
      exact (hH q).mp hq
    · intro hy
      obtain ⟨q, rfl⟩ := hbij.2 y
      exact Finset.mem_image.mpr ⟨q, (hH q).mpr hy, rfl⟩
  have hc : H.card = (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams v)).card := by
    exact (Finset.card_image_of_injective H hbij.1).symm.trans (congrArg Finset.card himage)
  exact ⟨H, hH, hc ▸ hbatch, hc ▸ hfast⟩

/-- Receiver-local exact service with joined HEAD readers and selected voters. -/
theorem exactService_emitted_head_joined (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (s : Slot) (Q : Block)
    (hhead : ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
      headAtLabel p c E rho y s = some Q)
    (q : Fin p.n) (hy : rho.seatOf (.base (.head s)) q ∈ rho.honest)
    (K : Block) (t : Time)
    (he : HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
      (ofHead p ⟨.seat (.head s) q, K.root⟩) t K) : K = Q := by
  have hObserver := he
  obtain ⟨j, _, _, hj, hem, _, _⟩ := he
  have hK := headTargetAtEmission_at_tick E rho hE.toScheduleWellFormed hObserver hj rfl
  have ho := hem
  rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem
  obtain ⟨_, ht, _, _, _⟩ := (fgsa_emits_head E rho _ _ _ s q K.root).mp hem
  subst t
  have hr := hhead _ hy (fgsa_joinedAt_of_emitted_head E rho hE hj ho)
  change (postClock E rho _ (SA.voteTime p.toParams s)).map
    (fun nd => headVote p nd.st s) = some Q at hr
  rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hE.toScheduleWellFormed hj] at hr
  exact hK.trans (Option.some.inj hr)

/-- Receiver-local exact service with joined HEAD readers and selected voters. -/
theorem exactService_gate_receipts_of_head_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (s : Slot) (Q : Block)
    (hhead : ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
      headAtLabel p c E rho y s = some Q)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s) (SA.gateTime p.toParams s))
    {i : Nat} {x : V} (ht : IsGateTick p c rho i x s)
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s Q)
    (hScope : GateReceiptScope E rho i x s)
    (q : Fin p.n) (hy : rho.seatOf (.base (.head s)) q ∈ rho.honest)
    (hawake : joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s))
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∃ t, V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
      (ofHead p ⟨.seat (.head s) q, Q.root⟩) t ∧
      baseVote (⟨.seat (.head s) q, Q.root⟩ : HeadWire p.n) ∈
        (storeAt p c E rho i x).base.votes ∧
      Q ∈ (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))).blocks ∧
      Q.slot ≤ s ∧
      GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x)
        (SA.gateTime p.toParams s))) (baseVote (⟨.seat (.head s) q, Q.root⟩ : HeadWire p.n)) <
          GridCO.earlyTime p.toParams.engine s ∧
      GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x)
        (SA.gateTime p.toParams s))) Q < GridCO.earlyTime p.toParams.engine s ∧
      Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i x)
        (SA.gateTime p.toParams s)).fg.F) Q := by
  obtain ⟨K, t, hh, he, hv, hK, hslot, hvs, hbs, hF, _⟩ :=
    (fgsa_gateReceipt_on (hroots := hroots) E rho hE hDelta hC s hSync ht Q hgeom
      hScope).2.2 q hy hawake
  have hKm : K ∈ (rho.stateBefore E i x).st.base.blocks := by
    have hm := (List.mem_filter.mp hK).1
    change K ∈ (clockPre p _ _).base.blocks at hm
    rwa [(clockPre_fields p _ _).2.1] at hm
  have hObserver := headTargetAtEmission_of_stored E rho
    (hroots.toNamedRootCollisionFree E rho) he rfl i x hKm
  have heq := exactService_emitted_head_joined E rho hE s Q hhead q hh K t hObserver
  subst K
  exact ⟨t, he, hv, hK, hslot, hvs, hbs, hF⟩

/-- Receiver-local exact service with joined HEAD readers and selected voters. -/
theorem exactService_gate_raw_of_head_on [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (s : Slot) (Q : Block)
    (hhead : ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
      headAtLabel p c E rho y s = some Q)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s) (SA.gateTime p.toParams s))
    {i : Nat} {x : V} (ht : IsGateTick p c rho i x s)
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s Q)
    (hScope : GateReceiptScope E rho i x s)
    (H : Finset (Fin p.n))
    (hH : ∀ q, q ∈ H ↔ rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s))
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
    let v := actView pre
    SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) v s = some Q ∧
      H.card ≤ SA.Root.prefixSupport p.toParams v s Q ∧
      Q ∈ v.blocks ∧ Block.Preceq (eraseFG pre.fg.F) Q := by
  intro pre v
  have hrec (q : Fin p.n) (hq : q ∈ H) :=
    exactService_gate_receipts_of_head_on (hroots := hroots)
      E rho hE hDelta hC s Q hhead hSync ht hgeom hScope
      q ((hH q).mp hq).1 ((hH q).mp hq).2
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

/-- Receiver-local exact service with joined HEAD readers and selected voters. -/
theorem exactService_gate_at_of_head_on [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (s : Slot) (Q : Block) (hne : Q ≠ .genesis)
    (hhead : ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
      headAtLabel p c E rho y s = some Q)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s) (SA.gateTime p.toParams s))
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho i x s)
    (hgeom : ExactServiceGateGeometry E rho i x s Q)
    (hScope : GateReceiptScope E rho i x s)
    (H : Finset (Fin p.n))
    (hH : ∀ q, q ∈ H ↔ rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s))
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card)
    (hfast : SA.releaseThreshold p.toParams ≤ H.card)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    gateResult p c E rho x s = some (some Q) ∧
    (∃ j, enabledGateAt p c E rho j x s ∧ gatePassedAt p c E rho j) ∧
    (∃ nd, postClock E rho x (SA.gateTime p.toParams s) = some nd ∧
      Q ∈ (fastWriteAt nd.st s).getD []) ∧
    (fgsaInterface p c).stable (afterTicks E rho (SA.gateTime p.toParams s) x) = Q ∧
    (∀ r, s = r * p.R → actionSource p c E rho x r = some (some Q)) := by
  let st := storeAt p c E rho i x
  let pre := clockPre p st (SA.gateTime p.toParams s)
  let v := actView pre
  let w := (fgsaAC E rho).gateView i x s
  have hs := hE.toScheduleWellFormed
  have hEnabled := hScope.enabled
  obtain ⟨hr, hcount, hmem, hanchor⟩ := exactService_gate_raw_of_head_on (hroots := hroots)
    E rho hE hDelta hC
    s Q hhead hSync ht hgeom.toGateReceiptGeometry hScope H hH hbatch
  have hv : { v with early := st.base.early } = w := fgsa_clockPre_gateView p st s
  have hrawEq : SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) v s =
      (fgsaAC E rho).raw i s x := by
    rw [clockPre_fg]
    have he := congrArg (fun u => SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) u s) hv
    exact he
  have hraw : (fgsaAC E rho).raw i s x = some Q := hrawEq.symm.trans hr
  have hsupport : SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams w s Q := by
    have he := congrArg (fun u => SA.Root.prefixSupport p.toParams u s Q) hv
    exact he ▸ hfast.trans hcount
  have hmemw : Q ∈ w.blocks := (congrArg GridCO.State.blocks hv) ▸ hmem
  have hlevel : SA.releaseThreshold p.toParams ∈ (fgsaAC E rho).gateLevels i x s Q := by
    change SA.releaseThreshold p.toParams ∈
      @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine p.n .root w s Q
    change SA.releaseThreshold p.toParams ∈
      (if decide (SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams w s Q) ||
        GridCO.slowEligible p.toParams.engine w s Q then [SA.releaseThreshold p.toParams] else [])
    simp only [hsupport, decide_true, Bool.true_or, ite_true, List.mem_singleton]
  have hservice := fgsa_gate_of_coveringBatch E rho hs i s x Q ht hEnabled
    ⟨Q, hraw, block_preceq_refl Q⟩ (by
      intro C hC
      have he := Option.some.inj (hraw.symm.trans hC)
      subst C
      exact hgeom.guard) hne hmemw hsupport hlevel
  have hanchor' : Block.Preceq ((fgsaAC E rho).anchor i x) Q := by
    change Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) Q
    simpa only [clockPre_fg] using hanchor
  have hout := (fgsa_S_eq_of_exact E rho hs i s x Q hx ht hEnabled hraw
    hgeom.guard hgeom.old_output hanchor').1
  have hidx := fgsa_tickIdx_of_event p c E rho hs ht
  refine ⟨?_, ⟨i, hEnabled, ?_⟩, ?_, ?_, ?_⟩
  · rw [gateResult_eq_saved p c E rho hs ht]
    have hg := fgsa_gate_saved_result E rho hs ht
      (fgsa_gate_joined_of_enabled E rho hEnabled)
    change SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (V2.D.Run.stateBefore E rho i x).st
        (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (V2.D.Run.stateBefore E rho i x).st
        (SA.gateTime p.toParams s))) s = some Q at hr
    rw [clockPre_fg] at hr
    exact hg.trans (congrArg some hr)
  · refine ⟨x, s, hEnabled, ?_, Q, hr, ?_⟩
    · unfold GridCO.savedGenuine
      rw [clockPre_genuine]
      exact fgsa_gate_fresh E rho hs ht
    · apply List.any_eq_false.mpr
      intro lease hl
      have hlw : lease ∈ w.obligations := (congrArg GridCO.State.obligations hv) ▸ hl
      have hg : Block.compatible lease.1 Q = true := hgeom.guard lease hlw
      simp only [hg, Bool.not_true, Bool.false_eq_true, not_false_eq_true]
  · refine ⟨(fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (SA.gateTime p.toParams s), ?_,
      exactService_fastWrite_of_gateService E rho hs i x s Q ht hEnabled hservice⟩
    rw [postClock_def, preTick_def, hidx]
    rfl
  · rw [afterTicks_node E rho hs ht]
    change (V2.D.tick E rho (V2.D.Run.stateBefore E rho i x) x
      (SA.gateTime p.toParams s)).1.st.base.stableRecord = Q
    change (V2.D.Run.stateBefore E rho (i + 1) x).st.base.stableRecord = Q at hout
    rwa [(V2.D.Run.step_tick_eq E rho ht).1] at hout
  · intro r he
    subst s
    exact exactService_opening_of_gateService E rho hs i x r Q ht hEnabled hservice hout
      (hgeom.opening_domain r rfl)

/-- Joined HEAD service and the exact confirmed receiver scope compose at the gate. -/
theorem exactService_gate_of_head_on [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (v : Slot) (Q : Block) (hne : Q ≠ .genesis)
    (hhead : SA.voteTime p.toParams v ≤ rho.horizon →
      ∀ x ∈ rho.honest, joinedAt p E rho x v (SA.voteTime p.toParams v) →
        headAtLabel p c E rho x v = some Q)
    (hSync : SA.gateTime p.toParams v ≤ rho.horizon →
      Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams v) (SA.gateTime p.toParams v))
    (hparticipation : SA.gateTime p.toParams v ≤ rho.horizon →
      ∃ H : Finset (Fin p.n),
        (∀ q, q ∈ H ↔ rho.seatOf (.base (.head v)) q ∈ rho.honest ∧
          joinedAt p E rho (rho.seatOf (.base (.head v)) q) v (SA.voteTime p.toParams v)) ∧
        Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card ∧
        SA.releaseThreshold p.toParams ≤ H.card)
    (hgeometry : ∀ i x, x ∈ rho.honest → IsGateTick p c rho i x v →
      ExactServiceGateGeometry E rho i x v Q)
    (hScopes : ∀ i x,
      confirmedReaderAtIdx p c E rho x (afterTicksIdx rho (SA.gateTime p.toParams v))
        (SA.gateTime p.toParams v) → IsGateTick p c rho i x v →
      GateReceiptScope E rho i x v)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    SA.gateTime p.toParams v ≤ rho.horizon → ∀ x ∈ rho.honest,
      confirmedReaderAtIdx p c E rho x
        (afterTicksIdx rho (SA.gateTime p.toParams v)) (SA.gateTime p.toParams v) →
      gateResult p c E rho x v = some (some Q) ∧
      (∃ j, enabledGateAt p c E rho j x v ∧ gatePassedAt p c E rho j) ∧
      (∃ nd, postClock E rho x (SA.gateTime p.toParams v) = some nd ∧
        Q ∈ (fastWriteAt nd.st v).getD []) ∧
      (fgsaInterface p c).stable (afterTicks E rho (SA.gateTime p.toParams v) x) = Q ∧
      (∀ r, v = r * p.R → actionSource p c E rho x r = some (some Q)) := by
  intro hh x hx hreader
  have hvg : SA.voteTime p.toParams v ≤ SA.gateTime p.toParams v := by
    change 4 * p.Δ * (v : Int) + p.Δ ≤ 4 * p.Δ * (v : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have htime : ((4 * v + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams v := by
    change ((4 * v + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (v : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨i, hi, _⟩ := fgsa_tick_total E rho hE.toScheduleWellFormed hDelta x hx
    (4 * v + 6) (htime ▸ hh)
    (by simpa only [htime] using hreader.2.1)
  rw [htime] at hi
  obtain ⟨H, hH, hbatch, hfast⟩ := hparticipation hh
  exact exactService_gate_at_of_head_on (hroots := hroots) E rho hE hDelta hC v Q hne
    (hhead (hvg.trans hh)) (hSync hh) hx hi (hgeometry i x hx hi)
    (hScopes i x hreader hi) H hH hbatch hfast

/-- Joined HEAD service and the exact confirmed receiver scope compose at the gate. -/
theorem exactService_of_head_and_gate_on [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (v : Slot) (Q : Block) (hne : Q ≠ .genesis)
    (hhead : SA.voteTime p.toParams v ≤ rho.horizon →
      ∀ x ∈ rho.honest, joinedAt p E rho x v (SA.voteTime p.toParams v) →
        headAtLabel p c E rho x v = some Q)
    (hSync : SA.gateTime p.toParams v ≤ rho.horizon →
      Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams v) (SA.gateTime p.toParams v))
    (hparticipation : SA.gateTime p.toParams v ≤ rho.horizon →
      ∃ H : Finset (Fin p.n),
        (∀ q, q ∈ H ↔ rho.seatOf (.base (.head v)) q ∈ rho.honest ∧
          joinedAt p E rho (rho.seatOf (.base (.head v)) q) v (SA.voteTime p.toParams v)) ∧
        Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card ∧
        SA.releaseThreshold p.toParams ≤ H.card)
    (hgeometry : ∀ i x, x ∈ rho.honest → IsGateTick p c rho i x v →
      ExactServiceGateGeometry E rho i x v Q)
    (hScopes : ∀ i x,
      confirmedReaderAtIdx p c E rho x (afterTicksIdx rho (SA.gateTime p.toParams v))
        (SA.gateTime p.toParams v) → IsGateTick p c rho i x v →
      GateReceiptScope E rho i x v)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ExactService p c E rho v Q :=
  ⟨hhead, exactService_gate_of_head_on (hroots := hroots)
    E rho hE hDelta hC v Q hne hhead hSync
    hparticipation hgeometry hScopes⟩

omit [DecidableEq V] in
open scoped Classical in
private theorem hygiene_joinedHonest_unfold (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (t : Time) :
    joinedHonest p E rho t = rho.honest.filter (fun v => joinedAt p E rho v (slotAt p t) t) := rfl

/-- Joined HEAD service and the exact confirmed receiver scope compose at the gate. -/
theorem exactService_participation_of_card_joined [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (v : Slot)
    (hbatch : Gen.Pure.Batch (joinedHonest p E rho (SA.voteTime p.toParams v)).card
      (Gen.V2.Duty.faulty rho).card)
    (hfast : SA.releaseThreshold p.toParams ≤
      (joinedHonest p E rho (SA.voteTime p.toParams v)).card) :
    ∃ H : Finset (Fin p.n),
      (∀ q, q ∈ H ↔ rho.seatOf (.base (.head v)) q ∈ rho.honest ∧
        joinedAt p E rho (rho.seatOf (.base (.head v)) q) v (SA.voteTime p.toParams v)) ∧
      Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card ∧
      SA.releaseThreshold p.toParams ≤ H.card := by
  classical
  let H := Finset.univ.filter (fun q : Fin p.n =>
    rho.seatOf (.base (.head v)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head v)) q) v (SA.voteTime p.toParams v))
  have hH (q : Fin p.n) : q ∈ H ↔ rho.seatOf (.base (.head v)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head v)) q) v (SA.voteTime p.toParams v) := by
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
  have hbij : Function.Bijective (fun q : Fin p.n => rho.seatOf (.base (.head v)) q) :=
    hC (.base (.head v)) trivial
  have himage : H.image (rho.seatOf (.base (.head v))) =
      joinedHonest p E rho (SA.voteTime p.toParams v) := by
    ext y
    have hs : slotAt p (SA.voteTime p.toParams v) = v :=
      slotOf_offset p v p.Δ p.deltaPos.le (by have hd := p.deltaPos; dsimp [Time] at *; omega)
    simp only [hygiene_joinedHonest_unfold E rho, hs, Finset.mem_filter]
    constructor
    · intro hy
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
      exact (hH q).mp hq
    · intro hy
      obtain ⟨q, rfl⟩ := hbij.2 y
      exact Finset.mem_image.mpr ⟨q, (hH q).mpr hy, rfl⟩
  have hc : H.card = (joinedHonest p E rho (SA.voteTime p.toParams v)).card := by
    exact (Finset.card_image_of_injective H hbij.1).symm.trans (congrArg Finset.card himage)
  exact ⟨H, hH, hc ▸ hbatch, hc ▸ hfast⟩

end AvailableChain.FGSA.Run
end
