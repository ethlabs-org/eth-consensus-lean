module
public import AvailableChainFGSAProofs.Proofs.Finality.Export -- shake: keep (source declarations)
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Export -- shake: keep
public import AvailableChainFGSAProofs.Statements.WeakContinuation -- shake: keep (WC interface)
public import AvailableChainFGSAProofs.Proofs.Foundations.Export -- shake: keep (P10 producers)
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Export -- shake: keep (P10 WC Export)
public import AvailableChainFGSAProofs.Proofs.Shared.Claims -- shake: keep (P10 claim adapter)

-- WC J1; DC handler order. B3 private matcher copy, with a checked equality.
namespace AvailableChain.FGSA
open AvailableChain.SimplexFG
/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private def wc_admitBlock (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) : State p.n :=
  if !namedParentHeld st N then st else
  match parentFG st N.erase with
  | none => st
  | some P =>
      if blockAccepted p st s N P then
        let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
          fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
        let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
        N.rows.foldl (admitRow p) st2
      else st

/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_admitBlock_eq : @admitBlock = @wc_admitBlock := rfl

end AvailableChain.FGSA


public section

/-! WC J1; DC bounded weak continuation: source seed and foundation discharge.
This module joins producers. The WC lane receives separate result premises. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC J1; DC named scope: every honest-holder row has its original action index.
Rejected delivered proposals count. Emitted-only proposals do not supply scope. -/
theorem wc_scopedRowOrigins (hv : V2.D.ExecutionValid E rho)
    (D : FGBlock (Fin p.n)) (hD : RootBlockInRun p c E rho (eraseFG D))
    (a : Row (Fin p.n)) (ha : a ∈ chainRows D)
    (hh : rho.seatOf (.base .fg) a.signer ∈ rho.honest) :
    ∃ j r wire, HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer := by
  obtain ⟨N, ⟨M, hM, hNM⟩, hN⟩ := hD
  have hDM : Block.Preceq (eraseFG D) M.erase := by
    rw [← hN]
    exact named_preceq_erase hNM
  have carriage : FinalityCarriage p c E rho (chainRows D) := by
    rcases hM with ⟨x, o, t, hd, ho⟩ | ⟨x, hx, i, hm⟩
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hd
      exact delivered_runBlock_carriage p c E rho hv j x o t hj M ho D hDM
    · have hr := namedOrigin_reachable E rho i x
      have hb := ((reachable_named_store p hr).2.1 M.erase).mpr ⟨M, hm, rfl⟩
      obtain ⟨W, hW, he⟩ := (cstoreInv_stateBefore E rho i x).baseTree M.erase |>.mp hb
      have hDW : FGBlock.Preceq D W := eraseFG_preceq_iff.mp (he ▸ hDM)
      have hstored := KitFG.ancestor_closed_of_parent_closed _
        (cstoreInv_stateBefore E rho i x).fg.closed W hW D hDW
      rw [FinalityCarriage_def]
      exact held_chain_row_origin p c E rho hv.toUnforgeableSignatures i x D ⟨hx, hstored⟩
  rw [FinalityCarriage_def] at carriage
  obtain ⟨wire, _, hd, auth, origin⟩ := carriage a ha
  have signer : RowSigner p c rho wire (rho.seatOf (.base .fg) a.signer) :=
    ⟨a.signer, auth, rfl⟩
  obtain ⟨j, t, hj, hem⟩ := origin _ signer hh
  obtain ⟨au, body⟩ := wire
  dsimp only at auth
  subst au
  obtain ⟨_, _, r, ht, _⟩ := (fgsa_emitsAt_row E rho j _ t hj a.signer body).mp hem
  exact ⟨j, r, ⟨.seat .fg a.signer, body⟩, ⟨hh, ht ▸ hj, hem⟩, hd, rfl⟩

/-- The selected saved value retains the family's enabled origin. -/
theorem wc_savedOrigin (i : Nat) (x : V) (hx : x ∈ rho.honest)
    (hf : WCFiniteFacts p c E rho i) (s : Slot) (B : Block)
    (hb : GridCO.savedGenuine (storeAt p c E rho i x).base s = some (some B)) :
    ∃ j < i, V2.D.restartFree rho x j i ∧ enabledGateAt p c E rho j x s ∧
      gateResultAt p c E rho j = some (some B) :=
  hf.saved x hx s B hb

variable [Fintype V]

/-- WC J1; DC premise discharge: supply every separate lane input to its consumer.
The consumer telescope is the literal [L] expansion; no foundation bundle is passed. -/
theorem wc_dischargeL {ΔF : Time} {w : HealingWitness} {Result : Prop}
    (hb : Base₂ p c E rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hdeltaF : E.Δ ≤ ΔF)
    (hfault : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
    (hpart : ∀ t, SA.voteTime p.toParams (w.u + 1) ≤ t → t ≤ rho.horizon →
      (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho t).card)
    (consume : ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.RestartsAtWakes E rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedReceiptRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfault : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_hfaultX : Gen.Pure.FaultX p.n (Gen.V2.Duty.faulty rho).card)
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
      TargetQCAt p.E B fp.height (heightView p B).J), Result) : Result := by
  have hq := fgsa_faultQ_of_count p hfault
  have hs := hb.valid.toScheduleWellFormed
  have hstore := fgsa_rStore p c E rho
  apply consume hb.valid hb.linked hb.cstar hb.restartsAtWakes hb.delta hb.receiptIdealization
    hsync hdeltaF hfault hq (fgsa_faultX_count_rec p hfault) hpart
    hstore ⟨fgsa_rStoreDurable p c E rho, fgsa_rStoreEpoch p c E rho⟩
    (fgsa_rMonoAll p c E rho)
    (fgsa_rActive p c E rho) (fgsa_rFrameExactNext p c E rho) (fgsa_rFrameNextEpoch p c E rho)
    (fgsa_rRec p c E rho) (fgsa_rGeo p c E rho) (fgsa_rCert p c E rho)
    (sourceDiscipline_tSrc p c E rho hs) (sourceDiscipline_labelBound p c E rho hs)
    (sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hb, hq⟩ hstore)
    (sourceDiscipline_strat p c E rho (pt := ()) ⟨hb, hq⟩ hstore)
    (fgsa_clientSafeAll p c E rho hb.linked)
  · intro j x r a e ha he
    exact sourceDiscipline_emittedName p c E rho hs ha he
  · intro i x row hr
    exact storedTargetsBelowOutput_target p _ (fgsa_storedTargetsBelowOutput p c E rho i x)
      row hr
  · intro i x row hr
    obtain ⟨j, hj, r, B, hG, hpass, hB, hp, hkeys, hd, he, hlast⟩ :=
      fgsa_leaseOrigins_lastWrite p c E rho hs i x row hr
    refine ⟨j, hj, r, B, hG, hpass, hB, hp, hkeys, hd, he, ?_⟩
    intro k w C hjk hki hEnabled
    exact hlast k w C hjk hki hEnabled.1
      (by rw [clockPre_joined]; exact fgsa_gate_joined_of_enabled E rho hEnabled)
  · exact fgsa_leaseOrigins_fastWrites_epoch p c E rho hs
  · exact fgsa_leaseOrigins_ancestorDeadlines p c E rho
  · exact held_chain_row_origin_before p c E rho hb.valid.toUnforgeableSignatures hs
  · exact wc_scopedRowOrigins hb.valid
  · intro j z r a u ha hsign hd fp hf
    exact cap_finality_head p c E rho ha hsign hd fp hf

/-- WC J1; DC fixed corruption: agreement transfers the source fault bound. -/
theorem wc_faultTransfer {E' : Generic.Env V} {source : V2.D.Run V (fgsa p c)}
    {G ΔF : Time} (hS : StrongRecoverySearchPrefix₂ p c E source G ΔF)
    (hc : CleanContinuation₂ p c E source E' rho ΔF) :
    (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3 := by
  simpa only [Gen.V2.Duty.faulty_def, hc.agrees.honest] using hS.fault

theorem wc_sourceParticipation {G ΔF : Time} {w : HealingWitness}
    (hS : StrongRecoverySearchPrefix₂ p c E rho G ΔF)
    (hjoin : E.t_GST ≤ slotStartZ p (w.u : Int)) :
    ∀ t, SA.voteTime p.toParams (w.u + 1) ≤ t → t ≤ rho.horizon →
      (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho t).card := by
  classical
  intro t hfirst hhor
  have hd := p.deltaPos
  have hden : 0 < 4 * p.Δ := by linarith
  have hnonneg : 0 ≤ t := by
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ t at hfirst
    nlinarith [Nat.cast_nonneg (α := Int) (w.u + 1)]
  have hslot : (w.u : Int) + 1 ≤ (slotAt p t : Int) := by
    change (w.u : Int) + 1 ≤ ((t / (4 * p.Δ)).toNat : Int)
    rw [Int.toNat_of_nonneg (Int.ediv_nonneg hnonneg hden.le)]
    have he := Int.mul_ediv_add_emod t (4 * p.Δ)
    have hr := Int.emod_lt_of_pos t hden
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ t at hfirst
    push_cast at hfirst
    nlinarith
  have hcut : E.t_GST ≤ slotStartZ p ((slotAt p t : Int) - 1) := by
    apply hjoin.trans
    change 4 * p.Δ * (w.u : Int) ≤ 4 * p.Δ * ((slotAt p t : Int) - 1)
    nlinarith
  have hgst : E.t_GST ≤ t := by
    apply hjoin.trans
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ t at hfirst
    change 4 * p.Δ * (w.u : Int) ≤ t
    push_cast at hfirst
    nlinarith
  have hall : joinedHonest p E rho t = rho.honest :=
    Finset.filter_eq_self.mpr (fun x hx =>
      finality_recovery_joined p c E rho hS.toRecovery₂ hx hcut hgst hhor)
  rw [hall]
  have hn := card_eq_n_of_linked hS.base.linked
  have hcard : (Gen.V2.Duty.faulty rho).card + rho.honest.card = p.n := by
    rw [Gen.V2.Duty.faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ]
    have hh := Finset.card_le_univ rho.honest
    omega
  have hf := hS.fault
  have hp := p.nPos
  omega

/-- WC J1; DC weak duty: the split includes the endpoint and the first suffix batch. -/
theorem wc_participation {E' : Generic.Env V} {source : V2.D.Run V (fgsa p c)}
    {G ΔF : Time} {w : HealingWitness}
    (hS : StrongRecoverySearchPrefix₂ p c E source G ΔF)
    (hc : CleanContinuationSleep₂ p c E source E' rho ΔF)
    (hjoin : E.t_GST ≤ slotStartZ p (w.u : Int)) :
    ∀ t, SA.voteTime p.toParams (w.u + 1) ≤ t → t ≤ rho.horizon →
      (Gen.V2.Duty.faulty rho).card < (joinedHonest p E' rho t).card := by
  classical
  intro t hfirst hhor
  by_cases hend : source.horizon < t
  · exact hc.joinedParticipation t hend hhor
  have ht := le_of_not_gt hend
  have hsource := wc_sourceParticipation hS hjoin t hfirst ht
  have hden : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have hnonneg : 0 ≤ t := by
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ t at hfirst
    nlinarith [p.deltaPos, Nat.cast_nonneg (α := Int) (w.u + 1)]
  have hslot : (w.u : Int) + 1 ≤ (slotAt p t : Int) := by
    change (w.u : Int) + 1 ≤ ((t / (4 * p.Δ)).toNat : Int)
    rw [Int.toNat_of_nonneg (Int.ediv_nonneg hnonneg hden.le)]
    have he := Int.mul_ediv_add_emod t (4 * p.Δ)
    have hr := Int.emod_lt_of_pos t hden
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ t at hfirst
    push_cast at hfirst
    nlinarith [p.deltaPos]
  have hcut : E.t_GST ≤ slotStartZ p ((slotAt p t : Int) - 1) := by
    apply hjoin.trans
    change 4 * p.Δ * (w.u : Int) ≤ 4 * p.Δ * ((slotAt p t : Int) - 1)
    nlinarith [p.deltaPos]
  have hgst : E.t_GST ≤ t := by
    apply hjoin.trans
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ t at hfirst
    change 4 * p.Δ * (w.u : Int) ≤ t
    push_cast at hfirst
    nlinarith [p.deltaPos]
  have hall : joinedHonest p E' rho t = rho.honest := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    have hj := finality_recovery_joined p c E source hS.toRecovery₂
      (hc.agrees.honest ▸ hx) hcut hgst ht
    refine ⟨(hc.agrees.awake x t ht).trans hj.1, ?_, ?_⟩
    · intro u hu hut hw
      apply hj.2.1 u hu hut
      change E.awake x u = true ∧ E.awake x (u - 1) = false
      change E'.awake x u = true ∧ E'.awake x (u - 1) = false at hw
      rw [← hc.agrees.awake x u (hut.trans ht),
        ← hc.agrees.awake x (u - 1) ((sub_le_self _ (by decide)).trans (hut.trans ht))]
      exact hw
    · intro u hu hut he
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
      have hklen : k < source.events.length := by
        by_contra hn
        have hm : V2.Event.restart x u ∈ rho.events.drop source.events.length := by
          have hd : (rho.events.drop source.events.length)[k - source.events.length]? =
              some (.restart x u) := by
            rw [List.getElem?_drop, Nat.add_sub_of_le (Nat.le_of_not_gt hn)]
            exact hk
          exact List.mem_of_getElem? hd
        exact (not_lt_of_ge (hut.trans ht)) (hc.agrees.suffixTime _ hm)
      apply hj.2.2 u hu hut
      exact List.mem_of_getElem? ((wc_eventReplay hc.agrees hklen).symm.trans hk)
  have hsourceAll : joinedHonest p E source t = source.honest :=
    Finset.filter_eq_self.mpr (fun x hx =>
      finality_recovery_joined p c E source hS.toRecovery₂ hx hcut hgst ht)
  rw [hall, Gen.V2.Duty.faulty_def, hc.agrees.honest]
  simpa only [hsourceAll, Gen.V2.Duty.faulty_def] using hsource

omit [Fintype V] in
/-- Keep the source join cutoff with the selected witness. -/
theorem wc_sourceJoinCut {w : HealingWitness} (h : H0 p c E rho w) :
    E.t_GST ≤ slotStartZ p (w.u : Int) := by
  have hs := h.synchronous
  have hu : (w.sStar : Int) + 2 ≤ w.u := by exact_mod_cast h.proposal_lower
  change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hs
  change E.t_GST ≤ 4 * p.Δ * (w.u : Int)
  nlinarith [p.deltaPos]


theorem wc_finiteFacts (hb : Base₂ p c E rho)
    (hfault : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
    (i : Nat) :
    WCFiniteFacts p c E rho i := by
  have hsch := hb.valid.toScheduleWellFormed
  exact wcg_finiteFacts hb.valid hb.receiptIdealization
    (sourceDiscipline_strat p c E rho (pt := ()) ⟨hb, fgsa_faultQ_of_count p hfault⟩
      (fgsa_rStore p c E rho))
    (fun x hx => fgsa_clientSafeAll p c E rho hb.linked x hx)
    (fun _ _ _ _ _ ha he => sourceDiscipline_emittedName p c E rho hsch ha he)
    (fun i x row hr => by
      obtain ⟨j, hj, r, B, hG, hpass, hB, hp, hkeys, hd, he, hlast⟩ :=
        fgsa_leaseOrigins_lastWrite p c E rho hsch i x row hr
      refine ⟨j, hj, r, B, hG, hpass, hB, hp, hkeys, hd, he, ?_⟩
      intro k w C hjk hki hEnabled
      exact hlast k w C hjk hki hEnabled.1
        (by rw [clockPre_joined]; exact fgsa_gate_joined_of_enabled E rho hEnabled))
    (fgsa_leaseOrigins_fastWrites_epoch p c E rho hsch)
    (fgsa_leaseOrigins_ancestorDeadlines p c E rho) i

private def wc_seedHeadAtIdx (p : Params) {In : Type} (c : AppCodec In)
    {V : Type} [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (k : Nat) (s : Slot) : Block :=
  match rho.events[k]? with
  | some (.tick y t) =>
      headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y) t).st s
  | _ => .genesis
private theorem wc_seedHeadAtIdx_eq : @headAtIdx = @wc_seedHeadAtIdx := rfl

theorem wc_heightSeed_of_finite {G ΔF : Time} {w : HealingWitness}
    (hS : StrongRecoverySearchPrefix₂ p c E rho G ΔF)
    (hinput : HealingInput p c E rho w ΔF) (hend : tstar p w < rho.horizon)
    (hfinite : ∀ i, WCFiniteFacts p c E rho i) :
    let i := afterTicksIdx rho (tstar p w)
    BoundedHealingCut₂ p c E rho w.u w.QStar i ΔF ∧ WCSeed p c E rho w i := by
  let i := afterTicksIdx rho (tstar p w)
  have hs := hS.base.valid.toScheduleWellFormed
  have hservice := hinput.ac.h3 w.u w.QStar hinput.wit.proposal hinput.wit.proposal_lower
  have hgate : SA.gateTime p.toParams w.u ≤ rho.horizon := le_of_lt hend
  have hGateReader (x : V) (hx : x ∈ rho.honest) :=
    fgsa_recovery_gate_readers hS.toRecoverySleep₂ hinput.wit hgate x hx
  have hcut : E.t_GST ≤ slotStartZ p ((w.u : Int) - 1) := by
    have ht := hinput.wit.synchronous
    have hu : (w.sStar : Int) + 2 ≤ w.u := by exact_mod_cast hinput.wit.proposal_lower
    change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at ht
    change E.t_GST ≤ 4 * p.Δ * ((w.u : Int) - 1)
    nlinarith [p.deltaPos]
  have hheadReader (x : V) (hx : x ∈ rho.honest) :
      headReader p E rho x w.u (SA.voteTime p.toParams w.u) := by
    refine ⟨hx, finality_recovery_joined p c E rho hS.toRecovery₂ hx hcut ?_ ?_⟩
    · apply hcut.trans
      change 4 * p.Δ * ((w.u : Int) - 1) ≤ 4 * p.Δ * (w.u : Int) + p.Δ
      linarith [p.deltaPos]
    · apply le_trans ?_ hgate
      change 4 * p.Δ * (w.u : Int) + p.Δ ≤ 4 * p.Δ * (w.u : Int) + 6 * p.Δ
      linarith [p.deltaPos]
  have href : ∀ x ∈ rho.honest, S_at p c E rho i x = w.QStar := by
    intro x hx
    have h := hinput.ac.h4.1 x hx
    rw [afterTicks_eq_stateBefore E rho hs] at h
    exact h
  have hnext : SA.voteTime p.toParams (w.u + 1) ≤ SA.gateTime p.toParams w.u := by
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (w.u : Int) + 6 * p.Δ
    push_cast
    have hd := p.deltaPos
    nlinarith
  have hfirst : E.t_GST ≤ SA.voteTime p.toParams (w.u + 1) := by
    have hstart := hinput.wit.synchronous
    have hslot : w.sStar + 2 ≤ w.u := hinput.wit.proposal_lower
    have hslot' : (w.sStar : Int) ≤ (w.u : Int) + 1 := by
      exact_mod_cast (Nat.le_trans (Nat.le_add_right w.sStar 2)
        (hslot.trans (Nat.le_succ w.u)))
    change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hstart
    change E.t_GST ≤ 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ
    push_cast
    have hd := p.deltaPos
    nlinarith
  obtain ⟨j₀, y₀, a₀, WStar, hrow₀, _, hsrc₀, herase, hheight⟩ := hinput.wit.fresh
  have hstored : ∀ x ∈ rho.honest, WStar ∈ (storeAt p c E rho i x).fg.TF := by
    intro x hx
    have hc := cstoreInv_stateBefore E rho i x
    have hQ : w.QStar ∈ (storeAt p c E rho i x).base.blocks := by
      rw [← href x hx]
      exact hc.Smem
    obtain ⟨Qfg, hQfg, heQ⟩ := hc.baseTree w.QStar |>.mp hQ
    apply KitFG.ancestor_closed_of_parent_closed _ hc.fg.closed Qfg hQfg
    apply eraseFG_preceq_iff.mp
    rw [herase, heQ]
    exact hinput.wit.source_prefix
  have hscope := rootScope_source hrow₀.1 hsrc₀
  refine ⟨⟨hinput.wit.after_gst, hend, rfl, hinput.wit.proposal, href⟩,
    ⟨rfl, List.length_filter_le _ _, hinput.wit.after_gst, hfirst,
      ⟨WStar, herase, hheight, hscope, hstored⟩, hinput.wit.source_prefix,
      ?_, href, ?_, ?_, ?_, ?_, ?_, hfinite i⟩⟩
  · intro x hx
    obtain ⟨hraw, ⟨j, hj, hpass⟩, _⟩ := hservice.2 hgate x hx (hGateReader x hx)
    refine ⟨j, wcg_tick_before_cut hs hj.1 le_rfl, hj.1, ?_, hpass⟩
    rw [gateResultAt_eq_gateResult p c E rho hs hj.1]
    exact hraw
  · intro x hx
    have heq : ((4 * (w.u + 1) + 1 : Nat) : Time) * p.Δ =
        SA.voteTime p.toParams (w.u + 1) := by
      change _ = 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ
      push_cast
      ring
    obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hs hS.base.delta x hx
      (4 * (w.u + 1) + 1) (heq ▸ hnext.trans hgate)
      (heq ▸ hS.awake x hx _ hfirst (hnext.trans hgate))
    rw [heq] at hk
    let st := FGSA.clock p (storeAt p c E rho k x) (SA.voteTime p.toParams (w.u + 1))
    have hread : headAtLabel p c E rho x (w.u + 1) = some (headVote p st (w.u + 1)) := by
      change (postClock E rho x (SA.voteTime p.toParams (w.u + 1))).map
        (fun nd => headVote p nd.st (w.u + 1)) = _
      rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hk]
      rfl
    have hraw := (hservice.2 hgate x hx (hGateReader x hx)).1
    have hsu : w.sStar ≤ w.u := le_trans (Nat.le_add_right _ _) hinput.wit.proposal_lower
    have hle := (hinput.ac.h5 x w.u w.QStar hx hsu hraw).2.1
      x (w.u + 1) (headVote p st (w.u + 1))
        ⟨hx, finality_recovery_joined p c E rho hS.toRecovery₂ hx
          (by simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using
            wc_sourceJoinCut hinput.wit) hfirst (hnext.trans hgate)⟩ le_rfl hread
    have hinv := cstoreInv_clock p _ (cstoreInv_stateBefore E rho k x)
      (SA.voteTime p.toParams (w.u + 1))
    refine ⟨k, wcg_tick_before_cut hs hk hnext, ⟨hk, ?_, ?_, ?_⟩⟩
    · rw [wc_seedHeadAtIdx_eq]
      unfold wc_seedHeadAtIdx
      rw [hk]
      exact hle
    · intro A hA
      obtain ⟨H, hH, hHread⟩ := hinv.baseTree _ |>.mp (headVote_stored p st hinv (w.u + 1))
      obtain ⟨Afg, hAfg, heA⟩ := eraseFG_ancestor_mem hinv.fg.closed hH
        (hHread ▸ Gen.Pure.block_preceq_trans hA hle)
      exact hinv.baseTree A |>.mpr ⟨Afg, hAfg, heA⟩
    · have hr := (hfinite k).receipts x hx
      constructor
      · simpa only [(clock_cumulative p _ _).2.2.1] using hr.blocks
      · simpa only [(clock_cumulative p _ _).2.2.2.1] using hr.votes
  · intro j x r a e hj ha he hhigh
    obtain ⟨K, B, hK, hpair, hentry, hB, hKB, _⟩ :=
      sourceDiscipline_emittedName p c E rho hs ha he
    refine ⟨K, B, hK, hpair, hentry, hB, hKB, ?_⟩
    have ht := wcg_time_before_cut hs ha.2.1 hj
    have hlabel : r * p.R ≤ w.u := by
      change 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ ≤
        4 * p.Δ * (w.u : Int) + 6 * p.Δ at ht
      have hd := p.deltaPos
      have hcast : ((r * p.R : Nat) : Int) ≤ (w.u : Int) := by nlinarith
      exact_mod_cast hcast
    rcases hlabel.lt_or_eq with hlt | heq
    · have hh : high p w K := by
        rw [high_def, heightView_eq_simplex]
        change w.M + 1 ≤ hOf p.E p.cfg K
        simpa only [hpair] using hhigh
      have hhead := hservice.1 (by
        change 4 * p.Δ * (w.u : Int) + p.Δ ≤ rho.horizon
        change 4 * p.Δ * (w.u : Int) + 6 * p.Δ ≤ rho.horizon at hgate
        have hd := p.deltaPos
        nlinarith) x ha.1 (hheadReader x ha.1).2
      exact (hinput.ac.h2A x r K ha.1 hK hh).1 x w.u w.QStar (hheadReader x ha.1)
        (Nat.succ_le_of_lt hlt) hhead
    · rw [heq] at hB
      have heB := Option.some.inj (Option.some.inj
        (hB.symm.trans (hservice.2 hgate x ha.1 (hGateReader x ha.1)).1))
      exact heB ▸ hKB
  · intro x hx
    have hc := (cstoreInv_stateBefore E rho i x).fg
    change w.M + 1 ≤ (rho.stateBefore E i x).st.fg.h_max
    rw [hc.hmax]
    rw [← hheight]
    have hw : WStar ∈ (rho.stateBefore E i x).st.fg.TF := hstored x hx
    exact le_sup_of_le_left (Finset.le_sup (f := fun B => (heightView p B).h) hw)
  · intro x hx
    have hn := nestOK_stateBefore E rho i x
    change Block.Preceq (F_at p c E rho i x) (S_at p c E rho i x) at hn
    rwa [href x hx] at hn
  · intro x hx row hr _
    have ht := storedTargetsBelowOutput_target p _ (fgsa_storedTargetsBelowOutput p c E rho i x)
      row hr
    change Block.Preceq row.1 (S_at p c E rho i x) at ht
    rwa [href x hx] at ht

/-- The source seed consumes the family's finite-facts producer. -/
theorem wc_heightSeed {G ΔF : Time} {w : HealingWitness}
    (hS : StrongRecoverySearchPrefix₂ p c E rho G ΔF)
    (hinput : HealingInput p c E rho w ΔF) (hend : tstar p w < rho.horizon) :
    let i := afterTicksIdx rho (tstar p w)
    BoundedHealingCut₂ p c E rho w.u w.QStar i ΔF ∧ WCSeed p c E rho w i :=
  wc_heightSeed_of_finite hS hinput hend
    (wc_finiteFacts hS.base hS.fault)

/-- WC J1; DC continuation assembly: all [L] inputs, including the first suffix batch.
The finite source seed is sufficient for the split at the inclusive source endpoint. -/
theorem wc_dischargeContinuation {E' : Generic.Env V} {source : V2.D.Run V (fgsa p c)}
    {G ΔF : Time} {w : HealingWitness} {iStar : Nat} {Result : Prop}
    (hS : StrongRecoverySearchPrefix₂ p c E source G ΔF)
    (hc : CleanContinuationSleep₂ p c E source E' rho ΔF)
    (_hs : WCSeed p c E source w iStar)
    (hjoin : E.t_GST ≤ slotStartZ p (w.u : Int))
    (consume : ∀
  (_hvalid : V2.D.ExecutionValid E' rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.RestartsAtWakes E' rho)
  (_hdelta : E'.Δ = p.Δ)
  (_hroots : NamedReceiptRootCollisionFree p c E' rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E' rho (fgsaDelay E'.Δ ΔF))
  (_hdeltaF : E'.Δ ≤ ΔF)
  (_hfault : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_hfaultX : Gen.Pure.FaultX p.n (Gen.V2.Duty.faulty rho).card)
  (_hpart : ∀ t, SA.voteTime p.toParams (w.u + 1) ≤ t → t ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card < (joinedHonest p E' rho t).card)
  (_hstore : RStore p c E' rho)
  (_hcumul : RStoreDurable p c E' rho ∧ RStoreEpoch p c E' rho)
  (_hmono : RMonoAll p c E' rho)
  (_hactive : RActive p c E' rho)
  (_hframe : RFrameExactNext p c E' rho)
  (_hmeta : RFrameNextEpoch p c E' rho)
  (_hrec : RRec p c E' rho)
  (_hgeo : RGeo p c E' rho)
  (_hcert : RCert p c E' rho)
  (_hsrc : TSrc p c E' rho)
  (_hlabel : LabelBound p c E' rho)
  (_hqc : RQCOrigin p c E' rho)
  (_hstrat : RStrat p c E' rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E' rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E' rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E' rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E' rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E' rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E' rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E' rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E' rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E' rho j ∧
      gateResultAt p c E' rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E' rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → enabledGateAt p c E' rho k x w →
        let pre := clockPre p (storeAt p c E' rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E' rho i x) s).getD [] →
      ∃ j < i, V2.D.restartFree rho x j i ∧ enabledGateAt p c E' rho j x s ∧
        gatePassedAt p c E' rho j ∧
        ∃ B, gateResultAt p c E' rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E' rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E' rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E' rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E' rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E' rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E' rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E' rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E' rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E' rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J), Result) : Result :=
  wc_dischargeL hc.base hc.sync hc.deltaF (wc_faultTransfer hS hc.toCleanContinuation₂)
    (wc_participation hS hc hjoin) consume

/-- WC plan §8 Job 4 and r2.1; DC source witness before every continuation.
Select H-time once, build the source seed once, then replay and discharge [L]. -/
theorem fgsa_weakContinuationLiveClaim_of_hTime (hH : HTimeClaim p) (G : Time) :
    WeakContinuationLiveClaim p G := by
  intro V _ _ In c ΔF hδ E source hS
  obtain ⟨w, input, start, bound⟩ := hH G ΔF hδ c E source ()
    ⟨⟨hS.toRecoverySleep₂, hS.liveness⟩, hS.endpoint.ge⟩
  have hend : tstar p w < source.horizon := by
    rw [hS.endpoint]
    exact start.trans_lt bound
  obtain ⟨cut, hs⟩ := wc_heightSeed hS input hend
  refine ⟨w.u, w.QStar, afterTicksIdx source (tstar p w), cut, ?_⟩
  intro E' rho hc
  have hs' := wc_seedReplay hc.agrees hS.base.valid hs cut.beforeEnd
  apply wc_dischargeContinuation hS hc hs (wc_sourceJoinCut input.wit)
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead
  exact wc_seededLiveAt ΔF w (afterTicksIdx source (tstar p w))
    hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs'

end AvailableChain.FGSA.Run
end
