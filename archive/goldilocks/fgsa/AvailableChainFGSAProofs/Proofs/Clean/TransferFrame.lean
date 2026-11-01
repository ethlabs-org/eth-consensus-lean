module
public import AvailableChainFGSAProofs.Proofs.Clean.StateGate -- shake: keep (source declarations)
public import AvailableChainFGSAProofs.Proofs.Shared.Count
public import AvailableChainFGSAProofs.Proofs.Shared.AnchorService
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

public import AvailableChainFGSAProofs.Proofs.Shared.Roots

public section

/-! P3 §8.7 F2.2; bp02 §3.5 steps 5–6 and §4.2. Proposal paths for the
retrospective next-slot read. Each vertex uses its own acceptance trigger. -/

namespace AvailableChain.FGSA.Run

variable {ΔF : Time}
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem transfer_decode {o : Obj p} {b : Block} (h : blockOf? p o = some b) :
    ∃ u N, N.erase = b ∧ (toWire p o).decode = some (.block u N) := by
  unfold blockOf? at h
  cases hd : (toWire p o).decode with
  | none => simp only [hd, reduceCtorEq] at h
  | some m =>
    cases m <;> simp only [hd, reduceCtorEq, Option.some.injEq] at h
    exact ⟨_, _, h, rfl⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 F2.2, T7.8; bp02 §3.5 step 5 and §4.2. Class B.
DC: Protocol/Schedule/AdoptionTransport.lean:509, acceptance-window boundary.
INTENTIONAL: FG-SA uses each proposal's stored stamp and acceptance, not
an honest supporting seat (spec/fgsa-protocol.tex:2506–2513).
Ancestor closure is applied just after K's early acceptance. -/
theorem clean_transfer_source_acceptances
    (hroots : NamedRootCollisionFree p c E rho)
    (hV : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    {i : Nat} {x : V} {s : Slot} {K B : Block}
    (hK : K ∈ (storeAt p c E rho i x).base.blocks)
    (hstamp : GridCO.stampBlock (storeAt p c E rho i x).base K <
      SA.earlyTime p.toParams s)
    (hBK : Block.Preceq B K) :
    ∀ b, Block.Preceq b B → b ≠ .genesis →
      ∃ l < i, ∃ t o u N, N.erase = b ∧
        (toWire p o).decode = some (.block u N) ∧
        V2.D.Run.acceptsAt E rho l x o t ∧ 0 ≤ t ∧ t < SA.earlyTime p.toParams s := by
  have hsch := hV.toScheduleWellFormed
  intro b hb hne
  have hbK := block_preceq_trans hb hBK
  have hKg : K ≠ .genesis := by
    intro he
    rw [he] at hbK
    exact hne (Gen.Pure.block_preceq_antisymm hbK (block_genesis_preceq b))
  have hpub : V2.PublicTime E (SA.earlyTime p.toParams s) := by
    refine ⟨4 * s + 2, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + 2 * p.Δ = _
    push_cast
    ring
  have hz : 0 ≤ SA.earlyTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    have hd := p.deltaPos
    positivity
  obtain ⟨j, hji, t, o, ho, ha, ht⟩ :=
    fgsa_block_accepted_before E rho hV i x K _ hKg hpub hz hK hstamp
  obtain ⟨u, N, heN, hdec⟩ := transfer_decode p ho
  have hpost := ha.2.2
  change processedS p (V2.D.Run.stateBefore E rho (j + 1) x).st o = true at hpost
  dsimp only [processedS] at hpost
  rw [hdec] at hpost
  obtain ⟨Kfg, hKfg, hroot⟩ := of_decide_eq_true hpost
  obtain ⟨envelope, hdelivery, _⟩ := ha.1
  have hx := hsch.honest_only _ (List.mem_of_getElem? hdelivery)
  have heK : eraseFG Kfg = K := rootBlockInRun_eq E rho hroots
    (rootScope_store hx hKfg) (rootBlockInRun_held E rho hx i hK)
    (by simpa only [← named_erase_root, heN] using (eraseFG_root Kfg).trans hroot)
  have hc := (storeBundle_stateBefore E rho (j + 1) x).cstore
  obtain ⟨A, hA, heA⟩ := eraseFG_ancestor_mem hc.fg.closed hKfg (heK ▸ hbK)
  have hbm := (hc.baseTree b).mpr ⟨A, hA, heA⟩
  obtain ⟨l, hl, t', o', ho', ha'⟩ := fgsa_block_accepted_origin E rho (j + 1) x b hne hbm
  obtain ⟨u', M, heM, hd'⟩ := transfer_decode p ho'
  obtain ⟨parent, hd, _⟩ := ha.1
  obtain ⟨parent', hd'', _⟩ := ha'.1
  refine ⟨l, by omega, t', o', u', M, heM, hd', ha',
    (hsch.in_horizon _ (List.mem_of_getElem? hd'')).1, ?_⟩
  have htime : t' ≤ t := by
    by_cases heq : l = j
    · subst l
      rw [hd] at hd''
      cases hd''
      exact le_rfl
    · obtain ⟨hll, hle⟩ := List.getElem?_eq_some_iff.mp hd''
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hd
      have hkey := (List.pairwise_iff_getElem.mp hsch.sorted) l j hll hjl (by omega)
      rw [hle, hje] at hkey
      change toLex (t', (2 : Nat)) ≤ toLex (t, 2) at hkey
      rcases Prod.Lex.toLex_le_toLex.mp hkey with hlt | ⟨heq, _⟩
      · exact le_of_lt hlt
      · exact le_of_eq heq
  exact htime.trans_lt ht

private theorem transfer_early_support (v : GridCO.State p.n .root) (s : Slot) (a B : Block)
    (h : SA.Root.confirmationFrom p.toParams a v s = some B) :
    ∃ o K, o ∈ GridCO.cleanSupport p.toParams.engine v s ∧
      GridCO.resolvedHead? v o = some K ∧ K ∈ v.blocks ∧ Block.Preceq B K ∧
      GridCO.stampBlock v K < SA.earlyTime p.toParams s := by
  obtain ⟨o, K, ho, hr, hm, _, hp, ht⟩ := confirmation_support_body p v s a B h
  exact ⟨o, K, ho, hr, hm, hp, ht⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 F2.2, T7.8; bp02 §3.5 step 5 and §4.2. Class B.
DC: Protocol/Schedule/AdoptionTransport.lean:509, confirmation acceptance window.
INTENTIONAL: the F-anchored raw result supplies an early resolved supporter;
its seat and proposer need not be honest (spec/fgsa-protocol.tex:2506–2513). -/
theorem clean_transfer_gate_acceptances
    (hV : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    {i : Nat} {x : V} {s : Slot} {B : Block}
    (ht : IsGateTick p c rho i x s)
    (hB : gateResultAt p c E rho i = some (some B))
    (hroots : NamedRootCollisionFree p c E rho) :
    ∀ b, Block.Preceq b B → b ≠ .genesis →
      ∃ l < i, ∃ t o u N, N.erase = b ∧
        (toWire p o).decode = some (.block u N) ∧
        V2.D.Run.acceptsAt E rho l x o t ∧ 0 ≤ t ∧ t < SA.earlyTime p.toParams s := by
  have hsch := hV.toScheduleWellFormed
  have hraw := (clean_gate_nonempty_raw hsch ht hB).2
  obtain ⟨o, K, _, _, hK, hBK, hstamp⟩ := transfer_early_support p _ s _ B hraw
  have hmem := ((actView_blocks _ K).mp hK).1
  rw [(clockPre_fields p _ _).2.1] at hmem
  have hkeys : K ∈ (storeAt p c E rho i x).base.blockStamp.map Prod.fst := by
    change K ∈ (V2.D.Run.stateBefore E rho i x).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho i x).«meta».stampKeys]
    exact hmem
  have heq : GridCO.stampBlock
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) K =
      GridCO.stampBlock (storeAt p c E rho i x).base K := by
    change (((clockPre p _ _).base.blockStamp.find? _).map Prod.snd).getD _ = _
    rw [(clockPre_stamps p _ _).1]
    unfold GridCO.stampBlock
    cases he : (storeAt p c E rho i x).base.blockStamp.find? (fun row => row.1 == K) with
    | none =>
      obtain ⟨row, hr, hh⟩ := List.mem_map.mp hkeys
      have hn := List.find?_eq_none.mp he row hr
      rw [hh, beq_self_eq_true] at hn
      contradiction
    | some row => rfl
  rw [heq] at hstamp
  exact clean_transfer_source_acceptances (hroots := hroots) p c E rho hV hDelta hmem hstamp hBK

private theorem transfer_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

private theorem transfer_row_tick {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j x r a) :
    rho.events[j]? = some (.tick x (p.actionTime r)) := ha.2.1

private theorem transfer_frame_at_vote
    (hroots : NamedRootCollisionFree p c E rho)
    (hsch : V2.D.ScheduleWellFormed E rho)
    (hf : FGFoundation p c E rho) (_hsrc : SrcFrameAboveStmt p c E rho)
    {i k : Nat} {y : V} {s : Slot} {Bfg : FGBlock (Fin p.n)}
    (hki : k < i)
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hs : CleanState p c E rho i)
    (hord : ∀ r C, (r, C) ∈ cleanResults p c E rho i → r < s →
      Block.Preceq C (eraseFG Bfg)) :
    FGBlock.Preceq (storeAt p c E rho k y).fg.F Bfg ∧
      FGBlock.Preceq (FGSA.controls p (storeAt p c E rho k y)).Z Bfg ∧
      (FGSA.controls p (storeAt p c E rho k y)).contest = false ∧
      (FGSA.controls p (storeAt p c E rho k y)).lo ≤ hOf p.E p.cfg Bfg := by
  have hy := hsch.honest_only _ (List.mem_of_getElem? hk)
  have hrows := hs.sources.1
  rw [CleanRowSources_def] at hrows
  have hsrc' := srcFrameAbove_scoped p c E rho hf.store hf.strat
    (fun e => FGBlock.Preceq e Bfg) 0
    ⟨fun _ _ hXY hY => KitFG.preceq_trans hXY hY⟩
    (fun _ => KitFG.genesis_preceq Bfg) k y hy ?_
  · have hc : ∀ W ∈ (storeAt p c E rho k y).fg.TF, ∀ e ∈ certified p W,
        FGBlock.Preceq e Bfg := fun W hW e he => hsrc'.1 W hW e he (Nat.zero_le _)
    have hF := hsrc'.2.1 (Nat.zero_le _)
    have hJ := hsrc'.2.2.1 (Nat.zero_le _)
    have hZ := hsrc'.2.2.2 (Nat.zero_le _)
    let st := storeAt p c E rho k y
    have hinv := (hf.store k y hy).1.fg
    have hcross : ∀ W ∈ st.fg.TF, ∀ U, FGBlock.Preceq U W →
        hOf p.E p.cfg U < hOf p.E p.cfg W →
        FGBlock.Preceq (derive p.E p.cfg U).T_h Bfg := by
      intro W hW U hU hlt
      apply hc W hW
      simp only [certified_def, heightView_eq_simplex p,
        KitFG.simplexHeightView_def, KitFG.heightOf_def]
      exact ⟨U, hU, Or.inr (Or.inr ⟨rfl, hlt⟩)⟩
    have hcrossH : ∀ W ∈ st.fg.TF, ∀ U, FGBlock.Preceq U W →
        (heightView p U).h < (heightView p W).h →
        FGBlock.Preceq (heightView p U).T_h Bfg := by
      simpa only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def, hOf]
        using hcross
    have hn := KitFG.storeFrameView_noContest_of_crossed_of_inv
      p.E (heightView p) (fgCertificateLaws p).height (finalityView p) st.fg hinv
        (fgJustificationLaws p) (by
      intro W hW U hU hlt
      exact KitFG.preceq_total_of_common hJ (hcrossH W hW U hU hlt))
    have hlo := KitFG.storeFrameView_height_of_crossed_prefix_of_inv
      p.E (heightView p) (fgCertificateLaws p).height (finalityView p) st.fg hinv Bfg hn hcrossH
    have hnTree : (controls p st).contest = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have ho := KitFG.treeStoreControlsView_contest_imp (heightView p) st.fg ht
      rw [hn] at ho
      cases ho
    refine ⟨hF, hZ, hnTree, ?_⟩
    change (controls p st).lo ≤ hOf p.E p.cfg Bfg
    rw [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
    have hle := fgsa_controls_lo_le_store p st
    rw [KitFG.storeControls_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)] at hle
    exact hle.trans hlo
  · intro z r a e ha he heScope _
    obtain ⟨j, hj, hrow⟩ := ha
    obtain ⟨C, hcSource, heq, hpre, hC⟩ := hrows j z r a _ (hj.trans hki) hrow he
    have heC : e = (derive p.E p.cfg C).T_h :=
      rootScope_eq hroots heScope
        (rootScope_ancestor (rootScope_source hrow.1 hcSource) (KitFG.entry_preceq p.E p.cfg C))
        (congrArg Prod.snd heq)
    have hrowtick := transfer_row_tick p c E rho hrow
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hrowtick
    obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
    have hkey := (List.pairwise_iff_getElem.mp hsch.sorted) j k hjl hkl hj
    rw [hje, hke] at hkey
    have ht := V2.D.Engine.time_le_of_key_le _ _ hkey
    have hrs : r * p.R < s := by
      change 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ ≤
        4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ at ht
      push_cast at ht
      have hd := p.deltaPos
      exact_mod_cast (show ((r * p.R : Nat) : Int) < (s : Int) by
        push_cast
        nlinarith)
    have hCB : Block.Preceq (eraseFG C) (eraseFG Bfg) := by
      rcases hC with hg | ⟨r', C', hC', hr', hCC'⟩
      · rw [hg]; exact block_genesis_preceq _
      · exact block_preceq_trans hCC' (hord r' C' hC' (hr'.trans_lt hrs))
    exact KitFG.preceq_trans (heC ▸ hpre) (transfer_lift p hCB)

private theorem transfer_coverage
    (hE : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    (b₀ : Time) (hhealthy : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (fgsaDelay E.Δ ΔF) b₀)
    (hb₀ : b₀ ≤ rho.horizon) {i : Nat} {x y : V} {s : Slot} {B : Block}
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hJ : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)))
    (hhor : SA.voteTime p.toParams (s + 1) ≤ rho.horizon)
    (hcut : SA.freezeTime p.toParams s ≤ b₀)
    (hpath : ∀ b, Block.Preceq b B → b ≠ .genesis →
      ∃ l < i, ∃ t o u N, N.erase = b ∧
        (toWire p o).decode = some (.block u N) ∧
        V2.D.Run.acceptsAt E rho l x o t ∧ 0 ≤ t ∧ t < SA.earlyTime p.toParams s)
    (hF : ∀ j, j ≤ V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) →
      Block.Preceq (F_at p c E rho j y) B) :
    ∃ required,
      ReceiptCoverageAnchorPremises E rho (fun t => t + p.Δ) b₀
        (SA.freezeTime p.toParams s) 0 y B required
        (fun L d => L = B ∧ d = SA.freezeTime p.toParams s)
        (fun _ _ => SA.earlyTime p.toParams s) := by
  let required := fun o t => 0 ≤ t ∧ t < SA.earlyTime p.toParams s ∧
    ∃ l < i, V2.D.Run.acceptsAt E rho l x o t ∧
      ∃ b, blockOf? p o = some b ∧ Block.Preceq b B
  have hef : SA.earlyTime p.toParams s + p.Δ = SA.freezeTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 3 * p.Δ
    ring
  have hfv : SA.freezeTime p.toParams s ≤ SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have decode {o : Obj p} {b : Block} (hb : blockOf? p o = some b) :
      ∃ r N, (toWire p o).decode = some (.block r N) := by
    change (match (toWire p o).decode with
      | some (.block _ N) => some N.erase | _ => none) = _ at hb
    cases hd : (toWire p o).decode with
    | none => rw [hd] at hb; contradiction
    | some m => cases m <;> simp_all
  refine ⟨required, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hDelta] using Gen.V2.Duty.deliveryWithinOn_of_healthyPrefixBy E rho b₀ hhealthy
          (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ _)
  · rintro o t ⟨h0, ht, l, _, ha, b, hb, _⟩
    obtain ⟨r, N, hd⟩ := decode hb
    obtain ⟨hT, hH, hRF, _⟩ := fgsa_transfer_path_anchor_service hE hDelta hy hx hJ hhor hd ha ht
    have hA : 0 ≤ SA.earlyTime p.toParams s := by
      change 0 ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
      have := p.deltaPos
      positivity
    refine ⟨h0, ht.le, hA, lt_add_of_pos_right _ p.deltaPos, ?_, Nat.zero_le _, ?_, hH,
      hRF.mono le_rfl (fgsa_idxBefore_mono rho hfv), (fgsa_proposal_acceptance_facts hE hd ha).2⟩
    · rw [hef]
    · simpa only [hef] using hT
  · rintro o t ⟨_, _, l, _, ha, b, hb, _⟩ r signer K hv
    obtain ⟨u, N, hd⟩ := decode hb
    rw [hd] at hv
    cases hv
  · rintro o t ⟨_, ht, l, _, ha, b, hb, _⟩
    obtain ⟨r, N, hd⟩ := decode hb
    have hH := (fgsa_transfer_path_anchor_service hE hDelta hy hx hJ hhor hd ha ht).2.2.2
    simpa only [hef] using hH
  · intro j _ hj
    exact block_compatible_of_common (block_preceq_refl B) (hF j hj)
  · exact ⟨fun _ _ hab => add_le_add hab le_rfl, hcut, hb₀, Nat.zero_le _⟩
  · rintro K d ⟨hKB, hdD⟩
    subst K d
    refine ⟨block_preceq_refl B, le_rfl, ?_⟩
    intro b hb hne
    obtain ⟨l, hl, t, o, u, N, heN, hd, ha, hz, ht⟩ := hpath b hb hne
    have ho : blockOf? p o = some b := by
      change (match (toWire p o).decode with | some (.block _ N) => some N.erase | _ => none) = _
      rw [hd]
      exact congrArg some heN
    refine ⟨o, t, u, N, heN, ⟨hz, ht, l, hl, ha, b, ho, hb⟩, hd, ?_⟩
    exact hef.le
  · intro o t u N hr hd
    obtain ⟨_, _, l, hl, ha, b', hb', hBK⟩ := hr
    have hb : blockOf? p o = some N.erase := by
      change (match (toWire p o).decode with | some (.block _ N) => some N.erase | _ => none) = _
      rw [hd]
    have heq := Option.some.inj (hb'.symm.trans hb)
    subst b'
    exact ⟨B, SA.freezeTime p.toParams s, ⟨rfl, rfl⟩, hBK⟩

private theorem transfer_raw_lift (hsch : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot} {B : Block}
    (ht : IsGateTick p c rho i x s)
    (hB : gateResultAt p c E rho i = some (some B)) :
    ∃ Bfg : FGBlock (Fin p.n), eraseFG Bfg = B := by
  have hraw := (clean_gate_nonempty_raw hsch ht hB).2
  have hc := cstoreInv_clockPre p _ (storeBundle_stateBefore E rho i x).cstore
    (SA.gateTime p.toParams s)
  obtain ⟨_, hm⟩ := compat_of_confirmation p _ hc hraw
  obtain ⟨Bfg, _, he⟩ := (hc.baseTree B).mp hm
  exact ⟨Bfg, he⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 F2.2, T7.12a/K8; bp02 §3.5 step 5 and §4.2. Class B.
DC: GSTZeroPreparedWalk.lean:546; AdoptionTransport.lean:442, receipt transport.
INTENTIONAL: FG-SA uses the strict freeze read, per-proposal accepted relay,
and the old-source F prefix (spec/fgsa-protocol.tex:2506–2513). The F-covered
K8 branch is handled by `fgsa_active_path_of_coverage`.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_transfer_receipt_path [Fintype V] (b₀ : Time)
    (h : CleanCutSet p c E rho b₀ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    {i k : Nat} {x y : V} {s : Slot} {B : Block}
    (hi : i < timeIdx rho b₀) (hki : k < i)
    (ht : IsGateTick p c rho i x s)
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)))
    (hs : CleanState p c E rho i)
    (hB : gateResultAt p c E rho i = some (some B))
    (hord : ∀ r C, (r, C) ∈ cleanResults p c E rho i → r < s → Block.Preceq C B) :
    ∀ b, Block.Preceq b B →
      b ∈ (actView (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st).blocks := by
  have hsch := h.base.valid.toScheduleWellFormed
  have hx := hsch.honest_only _ (List.mem_of_getElem? ht)
  have hy := hsch.honest_only _ (List.mem_of_getElem? hk)
  obtain ⟨Bfg, he⟩ := transfer_raw_lift p c E rho hsch ht hB
  have hframe := transfer_frame_at_vote (hroots := h.base.idealization) p c E rho hsch hf hsrc
    (Bfg := Bfg) hki hk hs
    (by simpa only [he] using hord)
  have hidx : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ k := by
    by_contra hn
    have htime := (Gen.V2.Duty.index_lt_idxBefore_iff hsch hk (SA.freezeTime p.toParams s)).mp
      (Nat.lt_of_not_ge hn)
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ <
      4 * p.Δ * (s : Int) + 3 * p.Δ at htime
    push_cast at htime
    have hd := p.deltaPos
    nlinarith
  have hF : ∀ j, j ≤ V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) →
      Block.Preceq (F_at p c E rho j y) B := by
    intro j hj
    rw [← he]
    exact eraseFG_preceq (KitFG.preceq_trans
      (hf.mono j k y hy (hj.trans hidx)).1 hframe.1)
  have hcut : SA.freezeTime p.toParams s ≤ b₀ := by
    have htime := (V2.D.Engine.index_lt_read_length_iff hsch b₀ ht).mp hi
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ b₀ at htime
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ b₀
    have hd := p.deltaPos
    linarith
  obtain ⟨required, hcov⟩ := transfer_coverage p c E rho h.base.valid h.base.delta
    b₀ h.healthy h.cut.2 hx hy hJ
    (hsch.in_horizon _ (List.mem_of_getElem? hk)).2 hcut
    (clean_transfer_gate_acceptances (hroots := h.base.idealization)
      p c E rho h.base.valid h.base.delta
      ht hB) hF
  apply fgsa_active_path_of_coverage_anchor (hroots := h.base.receiptIdealization)
    E rho h.base.valid h.base.delta
    (fun t => t + p.Δ) b₀ (SA.freezeTime p.toParams s) 0 y B required
    (fun L d => L = B ∧ d = SA.freezeTime p.toParams s)
    (fun _ _ => SA.earlyTime p.toParams s) hy hcov ⟨rfl, rfl⟩
  have hh := hF _ le_rfl
  change Block.Preceq (eraseFG (V2.D.Run.stateBefore E rho
    (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) y).st.fg.F) B at hh
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch] at hh
  exact hh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 F2.2, T7.8/T7.12a/K8; bp02 §3.5 step 5 and §4.2. Class B.
DC: GSTZeroPreparedWalk.lean:546; AdoptionTransport.lean:442, receipt transport.
INTENTIONAL: FG-SA transports the clean supporter's head K, not just B,
using each proposal's acceptance and strict freeze read
(spec/fgsa-protocol.tex:2506–2513). The old-source frame gives F ⪯ B ⪯ K.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_transfer_receipt_path_of_head [Fintype V] (b₀ : Time)
    (h : CleanCutSet p c E rho b₀ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    {i k : Nat} {x y : V} {s : Slot} {B K : Block} {o : GridCO.Wire p.n .root}
    (hi : i < timeIdx rho b₀) (hki : k < i)
    (ht : IsGateTick p c rho i x s)
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)))
    (hs : CleanState p c E rho i)
    (hB : gateResultAt p c E rho i = some (some B))
    (hord : ∀ r C, (r, C) ∈ cleanResults p c E rho i → r < s → Block.Preceq C B)
    (ho : o ∈ GridCO.cleanSupport p.toParams.engine
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s)
    (hK : GridCO.resolvedHead?
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) o = some K) (hBK
          : Block.Preceq B K) :
    ∀ b, Block.Preceq b K →
      b ∈ (actView (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st).blocks := by
  have hsch := h.base.valid.toScheduleWellFormed
  have hx := hsch.honest_only _ (List.mem_of_getElem? ht)
  have hy := hsch.honest_only _ (List.mem_of_getElem? hk)
  obtain ⟨Bfg, he⟩ := transfer_raw_lift p c E rho hsch ht hB
  have hframe := transfer_frame_at_vote (hroots := h.base.idealization) p c E rho hsch hf hsrc
    (Bfg := Bfg) hki hk hs
    (by simpa only [he] using hord)
  have hidx : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ k := by
    by_contra hn
    have htime := (Gen.V2.Duty.index_lt_idxBefore_iff hsch hk (SA.freezeTime p.toParams s)).mp
      (Nat.lt_of_not_ge hn)
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ <
      4 * p.Δ * (s : Int) + 3 * p.Δ at htime
    push_cast at htime
    have hd := p.deltaPos
    nlinarith
  have hF : ∀ j, j ≤ V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) →
      Block.Preceq (F_at p c E rho j y) B := by
    intro j hj
    rw [← he]
    exact eraseFG_preceq (KitFG.preceq_trans
      (hf.mono j k y hy (hj.trans hidx)).1 hframe.1)
  have hcut : SA.freezeTime p.toParams s ≤ b₀ := by
    have htime := (V2.D.Engine.index_lt_read_length_iff hsch b₀ ht).mp hi
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ b₀ at htime
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ b₀
    have hd := p.deltaPos
    linarith
  have hres := (List.mem_filter.mp (List.mem_filter.mp ho).1).2
  change GridCO.resolvedBefore _ o _ = true at hres
  dsimp only [GridCO.resolvedBefore] at hres
  rw [hK] at hres
  have hKm := resolvedHead_mem _ o hK
  have hstamp := of_decide_eq_true (Bool.and_eq_true_iff.mp hres).2
  have hmem := ((actView_blocks _ K).mp hKm).1
  rw [(clockPre_fields p _ _).2.1] at hmem
  have hkeys : K ∈ (storeAt p c E rho i x).base.blockStamp.map Prod.fst := by
    change K ∈ (V2.D.Run.stateBefore E rho i x).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho i x).«meta».stampKeys]
    exact hmem
  have heq : GridCO.stampBlock
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) K =
      GridCO.stampBlock (storeAt p c E rho i x).base K := by
    change (((clockPre p _ _).base.blockStamp.find? _).map Prod.snd).getD _ = _
    rw [(clockPre_stamps p _ _).1]
    unfold GridCO.stampBlock
    cases he : (storeAt p c E rho i x).base.blockStamp.find? (fun row => row.1 == K) with
    | none =>
      obtain ⟨row, hr, hh⟩ := List.mem_map.mp hkeys
      have hn := List.find?_eq_none.mp he row hr
      rw [hh, beq_self_eq_true] at hn
      contradiction
    | some row => rfl
  rw [heq] at hstamp
  have haccept := clean_transfer_source_acceptances (hroots := h.base.idealization)
    p c E rho h.base.valid
    h.base.delta
    hmem hstamp (block_preceq_refl K)
  obtain ⟨required, hcov⟩ := transfer_coverage p c E rho h.base.valid h.base.delta
    b₀ h.healthy h.cut.2 hx hy hJ
    (hsch.in_horizon _ (List.mem_of_getElem? hk)).2 hcut
    haccept (fun j hj => block_preceq_trans (hF j hj) hBK)
  apply fgsa_active_path_of_coverage_anchor (hroots := h.base.receiptIdealization)
    E rho h.base.valid h.base.delta
    (fun t => t + p.Δ) b₀ (SA.freezeTime p.toParams s) 0 y K required
    (fun L d => L = K ∧ d = SA.freezeTime p.toParams s)
    (fun _ _ => SA.earlyTime p.toParams s) hy hcov ⟨rfl, rfl⟩
  have hh := block_preceq_trans (hF _ le_rfl) hBK
  change Block.Preceq (eraseFG (V2.D.Run.stateBefore E rho
    (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) y).st.fg.F) K at hh
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch] at hh
  exact hh

private theorem transfer_read_stamp (hsch : V2.D.ScheduleWellFormed E rho)
    (y : V) (D : Time) (hD : 0 < D) (b : Block)
    (hb : b ∈ (V2.D.Run.stateBeforeTime E rho D y).st.base.blocks) :
    GridCO.stampBlock (V2.D.Run.stateBeforeTime E rho D y).st.base b < D := by
  exact fgsa_block_stamp_before_read E rho hsch y D hD b hb

omit [DecidableEq V] in
private theorem transfer_vote_epoch (hS : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {y : V} {s : Slot}
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1))) :
    V2.D.restartFree rho y (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) k := by
  intro j w hj hjk he
  have hw : w ≤ SA.voteTime p.toParams (s + 1) := by
    by_contra hn
    have hkj := V2.D.Engine.eventIndex_lt_of_time_lt hS hk he (lt_of_not_ge hn)
    omega
  have h0 := (hS.in_horizon _ (List.mem_of_getElem? he)).1
  have hb := hJ.2.2 w h0 hw (List.mem_of_getElem? he)
  have hf : SA.freezeTime p.toParams s ≤ w := by
    by_contra hn
    exact (not_lt_of_ge hj) ((Gen.V2.Duty.index_lt_idxBefore_iff hS he _).mpr
      (lt_of_not_ge hn))
  change w ≤ 4 * p.Δ * (((s + 1 : Nat) : Int) - 1) at hb
  change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ w at hf
  push_cast at hb
  linarith [p.deltaPos]

private theorem transfer_stamp_kept {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List (α × Time)} (hp : xs <+: ys) (a : α)
    (hm : a ∈ xs.map Prod.fst) :
    ys.find? (fun row => row.1 == a) = xs.find? (fun row => row.1 == a) := by
  obtain ⟨tail, he⟩ := hp
  rw [← he, List.find?_append]
  cases hf : xs.find? (fun row => row.1 == a) with
  | none =>
    obtain ⟨row, hr, hh⟩ := List.mem_map.mp hm
    have hn := List.find?_eq_none.mp hf row hr
    rw [hh, beq_self_eq_true] at hn
    contradiction
  | some row => rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F2.2, T7.8/T7.12a; bp02 §3.5 step 5 and §4.2. Class B.
DC: GSTZeroPreparedWalk.lean:546; WeakGenesisGSTZeroActionSources.lean:25.
INTENTIONAL: this is the FG-SA stamped path at the actual next-slot clocked
read, not a prepared SG walk (spec/fgsa-protocol.tex:2496–2525; design R4/R5).
The original freeze stamps survive both cumulative storage and the full clock.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_transfer_prefreeze_path [Fintype V] (b₀ : Time) :
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i k x y s B, i < timeIdx rho b₀ → k < i →
    IsGateTick p c rho i x s →
    rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
    joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
    CleanHist p c E rho i → (∀ j, j ≤ i → CleanState p c E rho j) →
    gateResultAt p c E rho i = some (some B) →
    (∀ r C, (r, C) ∈ cleanResults p c E rho i → r < s → Block.Preceq C B) →
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y)
      (SA.voteTime p.toParams (s + 1))).st
    ∃ Bfg : FGBlock (Fin p.n), eraseFG Bfg = B ∧
      ∀ A : FGBlock (Fin p.n), FGBlock.Preceq A Bfg →
        A ∈ st.fg.TF ∧
        GridCO.stampBlock st.base (eraseFG A) < SA.freezeTime p.toParams s := by
  intro h _ hf hsrc i k x y s B hi hki ht hk hJ _ hall hB hord st
  have hsch := h.base.valid.toScheduleWellFormed
  have hy := hsch.honest_only _ (List.mem_of_getElem? hk)
  have hpath := clean_transfer_receipt_path p c E rho b₀ h hf hsrc hi hki ht hk hJ
    (hall i le_rfl) hB hord
  let D := SA.freezeTime p.toParams s
  let j := V2.D.Run.idxBefore rho D
  have hjk : j ≤ k := by
    by_contra hn
    have htime := (Gen.V2.Duty.index_lt_idxBefore_iff hsch hk D).mp (Nat.lt_of_not_ge hn)
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ <
      4 * p.Δ * (s : Int) + 3 * p.Δ at htime
    push_cast at htime
    have hd := p.deltaPos
    nlinarith
  have hklen : k ≤ rho.events.length := Nat.le_of_lt (List.getElem?_eq_some_iff.mp hk).1
  have hd := hf.cumul.1 j k y hy hjk hklen
  have hc := hf.cumul.2 j k y hy hjk hklen (transfer_vote_epoch p c E rho hsch hk hJ)
  have hread : storeAt p c E rho j y = (V2.D.Run.stateBeforeTime E rho D y).st := by
    change (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D) y).st = _
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho D hsch]
  have hBmem := ((actView_blocks _ B).mp (hpath B (block_preceq_refl B))).1
  obtain ⟨Bfg, hBfg, he⟩ := ((storeBundle_stateBeforeTime E rho D y).cstore.baseTree B).mp hBmem
  refine ⟨Bfg, he, ?_⟩
  intro A hA
  have hAm := KitFG.ancestor_closed_of_parent_closed _
    (storeBundle_stateBeforeTime E rho D y).cstore.fg.closed Bfg hBfg A hA
  have hAb := ((storeBundle_stateBeforeTime E rho D y).cstore.baseTree (eraseFG A)).mpr
    ⟨A, hAm, rfl⟩
  have hAstamp := transfer_read_stamp p c E rho hsch y D (by
    change 0 < 4 * p.Δ * (s : Int) + 3 * p.Δ
    have hd := p.deltaPos
    positivity) (eraseFG A) hAb
  rw [← hread] at hAm hAb hAstamp
  have hkeys : eraseFG A ∈ (storeAt p c E rho j y).base.blockStamp.map Prod.fst := by
    change eraseFG A ∈ (V2.D.Run.stateBefore E rho j y).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho j y).«meta».stampKeys]
    exact hAb
  constructor
  · change A ∈ (FGSA.clock p (storeAt p c E rho k y) _).fg.TF
    rw [(clock_cumulative p _ _).1]
    exact hd.1 hAm
  · have heq := transfer_stamp_kept hc.1 (eraseFG A) hkeys
    change (((FGSA.clock p (storeAt p c E rho k y) _).base.blockStamp.find? _).map
      Prod.snd).getD _ < D
    rw [(clock_cumulative p _ _).2.2.1, heq]
    unfold GridCO.stampBlock at hAstamp
    cases hfind : (storeAt p c E rho j y).base.blockStamp.find? (fun row => row.1 == eraseFG A) with
    | none =>
      obtain ⟨row, hr, hh⟩ := List.mem_map.mp hkeys
      have hn := List.find?_eq_none.mp hfind row hr
      rw [hh, beq_self_eq_true] at hn
      contradiction
    | some row => simpa only [hfind, Option.map_some, Option.getD_some] using hAstamp

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F2.2, T7.8/T7.12a and C5; bp02 §3.5 step 5 and §4.2. Class B.
DC: GSTZeroPreparedWalk.lean:546; WeakGenesisGSTZeroActionSources.lean:25.
INTENTIONAL: FG-SA needs the supporter's whole stamped FG path at the
actual next-slot clocked read, as the C5 relay hpath premise requires
(spec/fgsa-protocol.tex:2496–2525,2506–2513). The lift is existential so
that the consumer can select it; eraseFG injectivity identifies any other lift.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_transfer_prefreeze_path_of_head [Fintype V] (b₀ : Time) :
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i k x y s B K (o : GridCO.Wire p.n .root), i < timeIdx rho b₀ → k < i →
    IsGateTick p c rho i x s →
    rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
    joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
    CleanHist p c E rho i → (∀ j, j ≤ i → CleanState p c E rho j) →
    gateResultAt p c E rho i = some (some B) →
    (∀ r C, (r, C) ∈ cleanResults p c E rho i → r < s → Block.Preceq C B) →
    o ∈ GridCO.cleanSupport p.toParams.engine
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s →
    GridCO.resolvedHead?
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) o = some K →
      Block.Preceq B K →
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y)
      (SA.voteTime p.toParams (s + 1))).st
    ∃ Kfg : FGBlock (Fin p.n), eraseFG Kfg = K ∧
      ∀ A : FGBlock (Fin p.n), FGBlock.Preceq A Kfg →
        A ∈ st.fg.TF ∧
        GridCO.stampBlock st.base (eraseFG A) < SA.freezeTime p.toParams s := by
  intro h _ hf hsrc i k x y s B K o hi hki ht hk hJ _ hall hB hord ho hK hBK st
  have hsch := h.base.valid.toScheduleWellFormed
  have hy := hsch.honest_only _ (List.mem_of_getElem? hk)
  have hpath := clean_transfer_receipt_path_of_head p c E rho b₀ h hf hsrc hi hki ht hk hJ
    (hall i le_rfl) hB hord ho hK hBK
  let D := SA.freezeTime p.toParams s
  let j := V2.D.Run.idxBefore rho D
  have hjk : j ≤ k := by
    by_contra hn
    have htime := (Gen.V2.Duty.index_lt_idxBefore_iff hsch hk D).mp (Nat.lt_of_not_ge hn)
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ <
      4 * p.Δ * (s : Int) + 3 * p.Δ at htime
    push_cast at htime
    have hd := p.deltaPos
    nlinarith
  have hklen : k ≤ rho.events.length := Nat.le_of_lt (List.getElem?_eq_some_iff.mp hk).1
  have hd := hf.cumul.1 j k y hy hjk hklen
  have hc := hf.cumul.2 j k y hy hjk hklen (transfer_vote_epoch p c E rho hsch hk hJ)
  have hread : storeAt p c E rho j y = (V2.D.Run.stateBeforeTime E rho D y).st := by
    change (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D) y).st = _
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho D hsch]
  have hKmem := ((actView_blocks _ K).mp (hpath K (block_preceq_refl K))).1
  obtain ⟨Kfg, hKfg, he⟩ := ((storeBundle_stateBeforeTime E rho D y).cstore.baseTree K).mp hKmem
  refine ⟨Kfg, he, ?_⟩
  intro A hA
  have hAm := KitFG.ancestor_closed_of_parent_closed _
    (storeBundle_stateBeforeTime E rho D y).cstore.fg.closed Kfg hKfg A hA
  have hAb := ((storeBundle_stateBeforeTime E rho D y).cstore.baseTree (eraseFG A)).mpr
    ⟨A, hAm, rfl⟩
  have hAstamp := transfer_read_stamp p c E rho hsch y D (by
    change 0 < 4 * p.Δ * (s : Int) + 3 * p.Δ
    have hd := p.deltaPos
    positivity) (eraseFG A) hAb
  rw [← hread] at hAm hAb hAstamp
  have hkeys : eraseFG A ∈ (storeAt p c E rho j y).base.blockStamp.map Prod.fst := by
    change eraseFG A ∈ (V2.D.Run.stateBefore E rho j y).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho j y).«meta».stampKeys]
    exact hAb
  constructor
  · change A ∈ (FGSA.clock p (storeAt p c E rho k y) _).fg.TF
    rw [(clock_cumulative p _ _).1]
    exact hd.1 hAm
  · have heq := transfer_stamp_kept hc.1 (eraseFG A) hkeys
    change (((FGSA.clock p (storeAt p c E rho k y) _).base.blockStamp.find? _).map
      Prod.snd).getD _ < D
    rw [(clock_cumulative p _ _).2.2.1, heq]
    unfold GridCO.stampBlock at hAstamp
    cases hfind : (storeAt p c E rho j y).base.blockStamp.find? (fun row => row.1 == eraseFG A) with
    | none =>
      obtain ⟨row, hr, hh⟩ := List.mem_map.mp hkeys
      have hn := List.find?_eq_none.mp hfind row hr
      rw [hh, beq_self_eq_true] at hn
      contradiction
    | some row => simpa only [hfind, Option.map_some, Option.getD_some] using hAstamp

private theorem transfer_vote_clock (st : State p.n) (s : Slot) :
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

private theorem transfer_live_bounds (st : State p.n) (B : Block)
    (hZ : Block.Preceq (eraseFG (FGSA.controls p st).Z) B)
    (hlease : ∀ row ∈ st.base.obligations, Block.Preceq row.1 B) :
    Block.Preceq (eraseFG (FGSA.controls p st).Z) (FGSA.liveRoot p st) ∧
      Block.Preceq (FGSA.liveRoot p st) B := by
  have hselect := Gen.Pure.foldl_select_mem (fun (best b : Block) =>
    best.depth < b.depth || (best.depth == b.depth && best.root < b.root))
    (st.base.obligations.filterMap (fun row =>
      if st.base.now < row.2.2 && decide (∃ X ∈ FGSA.fullTree p st, eraseFG X = row.1)
      then some row.1 else none)) (eraseFG (FGSA.controls p st).Z)
  change FGSA.liveRoot p st = _ ∨ FGSA.liveRoot p st ∈ _ at hselect
  rcases hselect with he | hm
  · rw [he]; exact ⟨block_preceq_refl _, hZ⟩
  · obtain ⟨row, hr, hrow⟩ := List.mem_filterMap.mp hm
    split at hrow
    · rename_i hguard
      have he := Option.some.inj hrow
      obtain ⟨X, hX, heX⟩ := of_decide_eq_true (Bool.and_eq_true_iff.mp hguard).2
      have hXZ := ((KitFG.mem_filteredFromView
        (heightView p) (FGSA.controls p st) st.fg.TF X).mp hX).2.2.1
      refine ⟨?_, he ▸ hlease row hr⟩
      rw [← he, ← heX]
      exact eraseFG_preceq hXZ
    · contradiction

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 F2.2; bp02 §3.5 steps 5–6 and §4.2. Class B.
DC: GSTZeroPreparedWalk.lean:513,546; WeakGenesisGSTZeroActionSources.lean:106.
INTENTIONAL: the exact Q6 retrospective FG-SA frame includes the FJ band,
contest, live lease root, and a witness in the actual voter set
(spec/fgsa-protocol.tex:2496–2525,2557–2571; design Appendix A and R4/R5).
The local height witness is Bfg itself. Ordered is an explicit input.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_transfer_frame [Fintype V] (b₀ : Time) :
  CleanCutSet p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i k x y s B, i < timeIdx rho b₀ → k < i →
    IsGateTick p c rho i x s →
    rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
    joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
    CleanHist p c E rho i → (∀ j, j ≤ i → CleanState p c E rho j) →
    gateResultAt p c E rho i = some (some B) →
    (∀ r C, (r, C) ∈ cleanResults p c E rho i → r < s → Block.Preceq C B) →
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y)
      (SA.voteTime p.toParams (s + 1))).st
    ∃ Bfg : FGBlock (Fin p.n), eraseFG Bfg = B ∧
      FGBlock.Preceq st.fg.F Bfg ∧ FGBlock.Preceq (FGSA.controls p st).Z Bfg ∧
      (FGSA.controls p st).contest = false ∧
      (FGSA.controls p st).lo ≤ hOf p.E p.cfg Bfg ∧
      Block.Preceq (eraseFG (FGSA.controls p st).Z) (FGSA.liveRoot p st) ∧
      Block.Preceq (FGSA.liveRoot p st) B ∧
      Bfg ∈ FGSA.voterBlocks p st (s + 1) ∧
      (∀ A : FGBlock (Fin p.n),
        Block.Preceq (FGSA.liveRoot p st) (eraseFG A) → FGBlock.Preceq A Bfg →
        eraseFG A ≠ FGSA.liveRoot p st →
        A ∈ domainR p st (FGSA.voterBlocks p st (s + 1))) := by
  intro h hq hf hsrc i k x y s B hi hki ht hk hJ hh hall hB hord st
  obtain ⟨Bfg, he, hpath⟩ := clean_transfer_prefreeze_path p c E rho b₀ h hq hf hsrc
    i k x y s B hi hki ht hk hJ hh hall hB hord
  have hsch := h.base.valid.toScheduleWellFormed
  have hframe := transfer_frame_at_vote (hroots := h.base.idealization) p c E rho hsch hf hsrc
    (Bfg := Bfg) hki hk
    (hall i le_rfl) (by simpa only [he] using hord)
  have hfg : st.fg = (storeAt p c E rho k y).fg := clock_fg p _ _
  have hcontrols : FGSA.controls p st = FGSA.controls p (storeAt p c E rho k y) :=
    congrArg (KitFG.treeStoreControlsView (heightView p)) hfg
  have hF : FGBlock.Preceq st.fg.F Bfg := by rw [hfg]; exact hframe.1
  have hZ : FGBlock.Preceq (FGSA.controls p st).Z Bfg := by rw [hcontrols]; exact hframe.2.1
  have hn : (FGSA.controls p st).contest = false := by rw [hcontrols]; exact hframe.2.2.1
  have hlo : (FGSA.controls p st).lo ≤ hOf p.E p.cfg Bfg := by rw [hcontrols]; exact hframe.2.2.2
  have hlease : ∀ row ∈ st.base.obligations, Block.Preceq row.1 B := by
    intro row hr
    change row ∈ (FGSA.clock p (storeAt p c E rho k y) _).base.obligations at hr
    rw [transfer_vote_clock p _ s] at hr
    have hmem := (clockPre_obligations_sublist p _ _).subset hr
    obtain ⟨j, hj, r, C, hjt, _, hC, hrow⟩ := (hall k (Nat.le_of_lt hki)).leases y row hmem
    have htime := fgsa_tick_time_strict E rho hsch hjt hk hj
    have hrs : r < s := by
      change 4 * p.Δ * (r : Int) + 6 * p.Δ <
        4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ at htime
      push_cast at htime
      have hd := p.deltaPos
      exact_mod_cast (show (r : Int) < (s : Int) by nlinarith)
    exact block_preceq_trans hrow (hord r C ⟨j, hj.trans hki, y, hjt,
      (clean_gate_enabled_of_result hsch hjt hC).2, hC⟩ hrs)
  have hlive := transfer_live_bounds p st B (by rw [← he]; exact eraseFG_preceq hZ) hlease
  have hv : ∀ A, FGBlock.Preceq st.fg.F A → FGBlock.Preceq A Bfg →
      A ∈ FGSA.voterBlocks p st (s + 1) := by
    intro A hFA hA
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨(hpath A hA).1, hFA⟩, ?_⟩
    rw [Bool.or_eq_true]
    left
    apply decide_eq_true
    simpa only [Nat.add_sub_cancel] using (hpath A hA).2
  refine ⟨Bfg, he, hF, hZ, hn, hlo, hlive.1, hlive.2,
    hv Bfg hF (KitFG.preceq_refl _), ?_⟩
  intro A hroot hA _
  have hZA := transfer_lift p (block_preceq_trans hlive.1 hroot)
  have hcstore := cstoreInv_clock p _ (storeBundle_stateBefore E rho k y).cstore
    (SA.voteTime p.toParams (s + 1))
  have hFA := transfer_lift p (block_preceq_trans (F_preceq_liveRoot p st hcstore) hroot)
  rw [domainR_def, frameR_def]
  rw [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)] at hlo
  exact (KitFG.mem_filteredFromView (heightView p) (FGSA.controls p st) _ A).mpr
    ⟨hv A hFA hA, hFA, hZA, Bfg, hv Bfg hF (KitFG.preceq_refl Bfg), hA, hlo⟩

end AvailableChain.FGSA.Run
end
