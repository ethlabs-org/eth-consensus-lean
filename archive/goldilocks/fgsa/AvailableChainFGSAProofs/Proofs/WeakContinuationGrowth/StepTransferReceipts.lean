module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Epoch
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.AnchorCoverage
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.StepTransferFrame

public section

/-! WC plan §6.5; DC retrospective paths retain the original per-body receipt times. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time}

/-- WC plan §6.5; DC preserve named receipt provenance and the strict freeze cutoff. -/
private theorem transfer_decode {o : Obj p} {b : Block} (h : blockOf? p o = some b) :
    ∃ u N, N.erase = b ∧ (toWire p o).decode = some (.block u N) := by
  unfold blockOf? at h
  cases hd : (toWire p o).decode with
  | none => simp only [hd, reduceCtorEq] at h
  | some m =>
    cases m <;> simp only [hd, reduceCtorEq, Option.some.injEq] at h
    exact ⟨_, _, h, rfl⟩

/-- WC plan §6.5; DC preserve named receipt provenance and the strict freeze cutoff. -/
private theorem transfer_source_acceptances
    (hroots : NamedReceiptRootCollisionFree p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    {i : Nat} {x : V} {s : Slot} {K B : Block}
    (hK : K ∈ (storeAt p c E rho i x).base.blocks)
    (hstamp : GridCO.stampBlock (storeAt p c E rho i x).base K <
      SA.earlyTime p.toParams s)
    (hBK : Block.Preceq B K) :
    ∀ b, Block.Preceq b B → b ≠ .genesis →
      ∃ l < i, ∃ t o u N, N.erase = b ∧
        (toWire p o).decode = some (.block u N) ∧
        V2.D.Run.acceptsAt E rho l x o t ∧ 0 ≤ t ∧ t < SA.earlyTime p.toParams s := by
  intro b hb hne
  have hsch := hvalid.toScheduleWellFormed
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
    fgsa_block_accepted_before E rho hvalid i x K _ hKg hpub hz hK hstamp
  obtain ⟨u, N, heN, hdec⟩ := transfer_decode p ho
  have hpost := ha.2.2
  change processedS p (V2.D.Run.stateBefore E rho (j + 1) x).st o = true at hpost
  dsimp only [processedS] at hpost
  rw [hdec] at hpost
  obtain ⟨Kfg, hKfg, hroot⟩ := of_decide_eq_true hpost
  obtain ⟨envelope, hdelivery, _⟩ := ha.1
  have hx := hsch.honest_only _ (List.mem_of_getElem? hdelivery)
  have heK : eraseFG Kfg = K := rootBlockInRun_eq E rho (hroots.toNamedRootCollisionFree E rho)
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

/-- WC plan §6.5; DC preserve named receipt provenance and the strict freeze cutoff. -/
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

/-- WC plan §6.5; DC each support path is retained at the next HEAD with its freeze stamps. -/
private theorem prefreeze_path
    (hvalid : V2.D.ExecutionValid E rho) (_hR : V2.D.RestartsAtWakes E rho) (hdelta : E.Δ = p.Δ)
    (hroots : NamedReceiptRootCollisionFree p c E rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hcumul : RStoreDurable p c E rho ∧ RStoreEpoch p c E rho)
    (hmono : RMonoAll p c E rho)
    {i k : Nat} {x y : V} {s : Slot} {K : Block} (hx : x ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)))
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hcut : SA.freezeTime p.toParams s ≤ rho.horizon)
    (hK : K ∈ (storeAt p c E rho i x).base.blocks)
    (hstamp : GridCO.stampBlock (storeAt p c E rho i x).base K < SA.earlyTime p.toParams s)
    (hFK : Block.Preceq (F_at p c E rho k y) K) :
    let st := FGSA.clock p (storeAt p c E rho k y) (SA.voteTime p.toParams (s + 1))
    ∃ Kfg : FGBlock (Fin p.n), eraseFG Kfg = K ∧
      ∀ A : FGBlock (Fin p.n), FGBlock.Preceq A Kfg → A ∈ st.fg.TF ∧
        GridCO.stampBlock st.base (eraseFG A) < SA.freezeTime p.toParams s := by
  intro st
  have hsch := hvalid.toScheduleWellFormed
  have hy := hvalid.honest_only _ (List.mem_of_getElem? hk)
  let D := SA.freezeTime p.toParams s
  let j := V2.D.Run.idxBefore rho D
  have hjk : j ≤ k := by
    by_contra hn
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hsch hk D).mp (Nat.lt_of_not_ge hn)
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ <
      4 * p.Δ * (s : Int) + 3 * p.Δ at ht
    push_cast at ht
    nlinarith [p.deltaPos]
  have hF : ∀ l, l ≤ j → Block.Preceq (F_at p c E rho l y) K := by
    intro l hl
    exact block_preceq_trans (eraseFG_preceq (hmono l k y hy (hl.trans hjk)).1) hFK
  have haccept := transfer_source_acceptances p c E rho hroots hvalid hdelta hK hstamp
    (block_preceq_refl K)
  obtain ⟨required, hcov⟩ := wcg_transfer_path_coverage hvalid hdelta hsync hx hy hJ
    (hvalid.in_horizon _ (List.mem_of_getElem? hk)).2 hGST hcut haccept hF
  have hpath : ∀ b, Block.Preceq b K →
      b ∈ (actView (V2.D.Run.stateBeforeTime E rho D y).st).blocks := by
    apply fgsa_active_path_of_coverage_anchor (hroots := hroots) E rho hvalid hdelta
      (fun t => max t E.t_GST + p.Δ) rho.horizon D 0 y K required
      (fun L d => L = K ∧ d = D) (fun _ _ => SA.earlyTime p.toParams s) hy hcov ⟨rfl, rfl⟩
    have hh := hF j le_rfl
    change Block.Preceq (eraseFG (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D)
      y).st.fg.F) K at hh
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho D hsch] at hh
    exact hh
  have hklen : k ≤ rho.events.length := Nat.le_of_lt (List.getElem?_eq_some_iff.mp hk).1
  have hRF := wcg_vote_read_epoch hsch hk hJ (D := D) (by
    change 4 * p.Δ * (s : Int) < 4 * p.Δ * (s : Int) + 3 * p.Δ
    linarith [p.deltaPos])
  have hc := hcumul.1 j k y hy hjk hklen
  have hstamps := hcumul.2 j k y hy hjk hklen hRF
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
  have hAstamp := fgsa_block_stamp_before_read E rho hsch y D (by
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
    exact hc.1 hAm
  · have heq := transfer_stamp_kept hstamps.1 (eraseFG A) hkeys
    change (((FGSA.clock p (storeAt p c E rho k y) _).base.blockStamp.find? _).map
      Prod.snd).getD _ < D
    rw [(clock_cumulative p _ _).2.2.1, heq]
    unfold GridCO.stampBlock at hAstamp
    cases hfind : (storeAt p c E rho j y).base.blockStamp.find?
        (fun row => row.1 == eraseFG A) with
    | none =>
      obtain ⟨row, hr, hh⟩ := List.mem_map.mp hkeys
      have hn := List.find?_eq_none.mp hfind row hr
      rw [hh, beq_self_eq_true] at hn
      contradiction
    | some row => simpa only [hfind, Option.map_some, Option.getD_some] using hAstamp

/-- WC plan §6.5; DC every support path keeps its actual frozen receipt evidence. -/
theorem wcg_retrospectivePaths [Fintype V] (ΔF : Time) (w : HealingWitness) (iStar : Nat) :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hwakes : V2.D.RestartsAtWakes E rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedReceiptRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_haccountable : FinalitySlashableBound p c E rho)
  (_hpart : ∀ t, SA.voteTime p.toParams (w.u + 1) ≤ t → t ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho t).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreDurable p c E rho ∧ RStoreEpoch p c E rho)
  (_hmono : RMonoAll p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExactNext p c E rho)
  (_hmeta : RFrameNextEpoch p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → enabledGateAt p c E rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, V2.D.restartFree rho x j i ∧
        enabledGateAt p c E rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar → ∀ i k x y s B, iStar ≤ i → i < rho.events.length →
    WCInv p c E rho w iStar i → IsGateTick p c rho i x s → w.u < s → k < i →
    rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
    joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
    gateResultAt p c E rho i = some (some B) → Block.Preceq w.QStar B →
    (∀ j z r C, WCResult p c E rho w iStar i j z r C → r < s → Block.Preceq C B) →
    let st := FGSA.clock p (storeAt p c E rho k y) (SA.voteTime p.toParams (s + 1))
    let src := actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    ∃ Bfg, eraseFG Bfg = B ∧ WCFrameLiveBelow p st (.head (s + 1)) Bfg
      (voterBlocks p st (s + 1)) ∧
      (∀ A, FGBlock.Preceq A Bfg → A ∈ st.fg.TF ∧
        GridCO.stampBlock st.base (eraseFG A) < SA.freezeTime p.toParams s) ∧
      ∀ o ∈ GridCO.cleanSupport p.toParams.engine src s, ∀ K,
        GridCO.resolvedHead? src o = some K → Block.Preceq B K →
        ∃ Kfg, eraseFG Kfg = K ∧ ∀ A, FGBlock.Preceq A Kfg → A ∈ st.fg.TF ∧
          GridCO.stampBlock st.base (eraseFG A) < SA.freezeTime p.toParams s := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i k x y s B hi hilen inv ht hslabel hki hk hJ hB hQB hord st src
  have hsch := hvalid.toScheduleWellFormed
  have hx := hvalid.honest_only _ (List.mem_of_getElem? ht)
  have hrawAt : gateResultAt p c E rho i = some (SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)).fg.F) src s) := by
    rw [gateResultAt_eq_gateResult p c E rho hsch ht,
      gateResult_eq_saved p c E rho hsch ht, clockPre_fg]
    exact fgsa_gate_saved_result E rho hsch ht
      (fgsa_gate_joined_of_enabled E rho (wcg_gate_enabled_of_result hsch ht hB))
  have hraw := Option.some.inj (hrawAt.symm.trans hB)
  have hc := cstoreInv_clockPre p _ (storeBundle_stateBefore E rho i x).cstore
    (SA.gateTime p.toParams s)
  obtain ⟨_, hm⟩ := compat_of_confirmation p _ hc hraw
  obtain ⟨Bfg, _, he⟩ := (hc.baseTree B).mp hm
  have hframe := wcg_retrospectiveFrame ΔF w iStar hvalid hlinked hcstar hnr hdelta hroots
    hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead
    hs i k x y s Bfg hi hilen inv ht hslabel hki hk hJ (he ▸ hQB)
    (fun j z r C hr hrs => he ▸ hord j z r C hr hrs)
  have hFB : Block.Preceq (F_at p c E rho k y) B := by
    have hF := block_preceq_trans hframe.frame.finalRoot hframe.frame.rootBelow
    change Block.Preceq (eraseFG (FGSA.clock p _ _).fg.F) _ at hF
    rw [clock_fg, he] at hF
    exact hF
  have hcut : SA.freezeTime p.toParams s ≤ rho.horizon := by
    have ht := (hvalid.in_horizon _ (List.mem_of_getElem? ht)).2
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ rho.horizon at ht
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ rho.horizon
    linarith [p.deltaPos]
  have hGST : E.t_GST ≤ SA.voteTime p.toParams s := by
    apply hs.firstVoteAfterGST.trans
    have hh : ((w.u + 1 : Nat) : Int) ≤ s := Int.ofNat_le.mpr (Nat.succ_le_of_lt hslabel)
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith [p.deltaPos]
  have paths : ∀ o ∈ GridCO.cleanSupport p.toParams.engine src s, ∀ K,
      GridCO.resolvedHead? src o = some K → Block.Preceq B K →
      ∃ Kfg, eraseFG Kfg = K ∧ ∀ A, FGBlock.Preceq A Kfg → A ∈ st.fg.TF ∧
        GridCO.stampBlock st.base (eraseFG A) < SA.freezeTime p.toParams s := by
    intro o ho K hK hBK
    have hres := (List.mem_filter.mp (List.mem_filter.mp ho).1).2
    change GridCO.resolvedBefore _ o _ = true at hres
    dsimp only [GridCO.resolvedBefore] at hres
    rw [hK] at hres
    have hKm := resolvedHead_mem _ o hK
    have hstamp := of_decide_eq_true (Bool.and_eq_true_iff.mp hres).2
    have hmem := ((actView_blocks _ K).mp hKm).1
    rw [(clockPre_fields p _ _).2.1] at hmem
    have heq : GridCO.stampBlock src K = GridCO.stampBlock
        (storeAt p c E rho i x).base K := by
      change (((clockPre p _ _).base.blockStamp.find? _).map Prod.snd).getD _ = _
      rw [(clockPre_stamps p _ _).1]
      have hkeys : K ∈ (storeAt p c E rho i x).base.blockStamp.map Prod.fst := by
        change K ∈ (V2.D.Run.stateBefore E rho i x).st.base.blockStamp.map Prod.fst
        rw [(metaInv_stateBefore E rho i x).stampKeys]
        exact hmem
      unfold GridCO.stampBlock
      cases he : (storeAt p c E rho i x).base.blockStamp.find? (fun row => row.1 == K) with
      | none =>
        obtain ⟨row, hr, hh⟩ := List.mem_map.mp hkeys
        have hn := List.find?_eq_none.mp he row hr
        rw [hh, beq_self_eq_true] at hn
        contradiction
      | some row => rfl
    rw [heq] at hstamp
    exact prefreeze_path p c E rho hvalid hnr hdelta hroots hsync hcumul hmono
      hx hk hJ hGST hcut hmem hstamp (block_preceq_trans hFB hBK)
  obtain ⟨o, K, ho, hK, _, _, hBK, _⟩ := confirmation_support_body p src s _ B hraw
  obtain ⟨Kfg, hKeq, hpath⟩ := paths o ho K hK hBK
  have hBpre : FGBlock.Preceq Bfg Kfg := eraseFG_preceq_iff.mp (by rwa [he, hKeq])
  exact ⟨Bfg, he, hframe, (fun A hA => hpath A (preceq_trans hA hBpre)), paths⟩

end AvailableChain.FGSA.Run
end
