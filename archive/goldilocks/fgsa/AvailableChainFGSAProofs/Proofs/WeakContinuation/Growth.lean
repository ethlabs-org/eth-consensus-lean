module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Inclusion
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthProposal
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthCausal
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

public section

/-! WC J3, plan §§6.12–7; DC AvailableChainGrowth.afterGST.
Blueprint 23 §17: the selected cut remains fixed before the continuation gap.
The deadline is exactly t + G' + 6Δ. Safety and inclusion are explicit inputs. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

omit [DecidableEq V] in
/-- WC J3, plan §6.12; DC named public reads: include deliveries after the gate cut. -/
theorem wc_cut_publicRead {u : Slot} {iStar : Nat}
    (hschedule : V2.D.ScheduleWellFormed E rho)
    (hcut : iStar = afterTicksIdx rho (SA.gateTime p.toParams u))
    (t : Time) (ht : SA.gateTime p.toParams u ≤ t) :
    iStar ≤ timeIdx rho t ∧ timeIdx rho t ≤ rho.events.length := by
  refine ⟨?_, List.length_filter_le _ _⟩
  rw [hcut]
  exact (preIdx_le_afterTicksIdx E rho hschedule _).2.trans
    (V2.D.Engine.read_length_mono _ _ ht)

/-- WC J3, plan §7; DC AvailableChainGrowth.afterGST: one actual proposal grows
both getters at the exact deadline. Blueprint 23 §17.2 supplies the eight steps. -/
theorem wc_growth_of_safety_inclusion (ΔF : Time) (u : Slot)
    (Q : Block) (iStar : Nat)
    (hcache : WCCachedSafety p c E rho iStar Q)
    (hcover : ∀ pt : PtSP, u + 2 ≤ pt.s →
      HonestProposal E rho (fgsaInterface p c) pt.s pt.P →
      SA.gateTime p.toParams pt.s ≤ rho.horizon →
      ∃ x ∈ rho.honest, Block.Preceq pt.P (S_at p c E rho rho.events.length x)) :
    WCGrowthStatement p c E rho ΔF u Q iStar := by
  intro hbase hcut hsafe hincl _ G' hG' hrecurrence t ht hdeadline
  have hd := p.deltaPos
  have h6 : 0 ≤ 6 * p.Δ := mul_nonneg (by decide) hd.le
  have hgap : 0 ≤ G' := (mul_nonneg (by decide : (0 : Time) ≤ 4) hd.le).trans hG'
  have hwindow : t + G' ≤ rho.horizon :=
    (le_add_of_nonneg_right h6).trans hdeadline
  have htD : t ≤ t + G' + 6 * p.Δ :=
    (le_add_of_nonneg_right hgap).trans (le_add_of_nonneg_right h6)
  obtain ⟨s, hfuture, hupper, hh, ha⟩ := hrecurrence t ht hwindow
  have hs := hbase.valid.toScheduleWellFormed
  obtain ⟨B, hprop, hslot⟩ := fgsa_honestProposal_exists_of_awake_slot E rho hs
    hbase.delta hh ha.1 ha.2.2 (hupper.trans hwindow)
  have hstart : u + 2 ≤ s := by
    by_contra h
    have hsu : s ≤ u + 1 := by
      simp only [Slot] at h ⊢
      omega
    have hcast : (s : Time) ≤ (u : Time) + 1 := by exact_mod_cast hsu
    have hscaled := mul_le_mul_of_nonneg_left hcast
      (mul_nonneg (by decide : (0 : Time) ≤ 4) hd.le)
    change 4 * p.Δ * (u : Time) + 6 * p.Δ ≤ t at ht
    change t < 4 * p.Δ * (s : Time) at hfuture
    nlinarith
  have hgate : SA.gateTime p.toParams s ≤ t + G' + 6 * p.Δ := by
    change 4 * p.Δ * (s : Time) + 6 * p.Δ ≤ t + G' + 6 * p.Δ
    change 4 * p.Δ * (s : Time) ≤ t + G' at hupper
    simpa only [add_comm] using add_le_add_left hupper (6 * p.Δ)
  have htzero : 0 ≤ t := by
    change 4 * p.Δ * (u : Time) + 6 * p.Δ ≤ t at ht
    exact (add_nonneg
      (mul_nonneg (mul_nonneg (by decide) hd.le) (Nat.cast_nonneg u)) h6).trans ht
  have hreadT := wc_cut_publicRead hs hcut t ht
  have hreadD := wc_cut_publicRead hs hcut (t + G' + 6 * p.Δ) (ht.trans htD)
  have hserved := hincl ⟨s, B⟩ hstart hprop (hgate.trans hdeadline)
  obtain ⟨y, hy, hBy⟩ := hcover ⟨s, B⟩ hstart hprop (hgate.trans hdeadline)
  refine ⟨s, B, hfuture, hprop, ?_⟩
  intro g hg
  refine ⟨?_, fun x hx => hserved g hg _ x ⟨hgate, hdeadline⟩ hx⟩
  intro x hx
  have hcompat := hcache.compatible (timeIdx rho t) rho.events.length x y hreadT
    ⟨hreadD.1.trans (List.length_filter_le _ _), le_rfl⟩ hx.1 hy
  have hc : Block.Compatible (V2.D.outputAt E rho g x t) B := by
    rw [fgsa_outputAt_eq_S_at E rho hs g hg x t]
    change Block.compatible _ B = true
    rw [Gen.Pure.block_compatible_comm]
    exact Gen.Pure.block_compatible_of_preceq_compatible hBy
      (by
        simpa only [Block.Compatible,
          Gen.Pure.block_compatible_comm (S_at p c E rho rho.events.length y)] using hcompat)
  have hn := fgsa_output_noFuture_of_slot E rho hs htzero hfuture hslot.ge g hg x
  have hb : Block.Preceq (V2.D.outputAt E rho g x t) B :=
    (Bool.or_eq_true_iff.mp hc).resolve_right hn
  have hne : V2.D.outputAt E rho g x t ≠ B := by
    intro he; exact hn (he ▸ Gen.Pure.block_preceq_refl B)
  change (!decide (_ = B) && Block.preceq _ B) = true
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  exact ⟨hne, hb⟩

/-- WC J3, plan §§6.11–7; DC persistent inclusion and joint growth at the fixed deadline.
Only four reviewed Job 1 Statements remain as producer premises. The complete [L]
telescope is unchanged. The continuation gap is quantified after the seed. -/
theorem wc_checkpoint [Fintype V] (ΔF : Time) (w : HealingWitness) (iStar : Nat)
    (hinduction : WCSeededInductionStatement p c E rho ΔF w iStar)
    (hframeLive : WCSeededFrameLiveStatement p c E rho ΔF w iStar)
    (hsafety : WCSeededSafetyStatement p c E rho w iStar)
    (hfinalBelow : WCFinalBelowStatement p c E rho ΔF w iStar) :
  ∀
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
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar → SA.gateTime p.toParams w.u ≤ rho.horizon →
    SSafeFromCut₂ p c E rho iStar w.QStar ΔF ∧
    (∀ pt : PtSP, w.u + 2 ≤ pt.s →
      HonestProposal E rho (fgsaInterface p c) pt.s pt.P →
      SA.gateTime p.toParams pt.s ≤ rho.horizon → ServedFromGateAt p c E rho pt) ∧
    ∀ G' : Time, 4 * p.Δ ≤ G' →
      AwakeProposerRecurrenceFrom p c E rho (SA.gateTime p.toParams w.u) G' →
      ∀ t : Time, SA.gateTime p.toParams w.u ≤ t →
        t + G' + 6 * p.Δ ≤ rho.horizon → JointGrowthAt p c E rho t (t + G' + 6 * p.Δ) := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfault hfaultQ hfaultX
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed hgate
  have hinv := hinduction hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfault
    hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc
    hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hseed
  obtain ⟨hcompat, hmonoS, hserved, houtputs⟩ :=
    hsafety hvalid.toScheduleWellFormed hseed hinv
  have hfinal := hfinalBelow hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfault
    hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc
    hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hseed hinv
  have hsafe : SSafeFromCut₂ p c E rho iStar w.QStar ΔF :=
    ⟨hcompat, hmonoS, hserved, fun i x y hcut hi => hfinal i x y ⟨hcut, hi⟩, houtputs⟩
  have hresult := wc_inclusion6_result ΔF w iStar hframeLive
    hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfault hfaultQ hfaultX
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead hseed hinv
  have hincl := fun pt hstart hprop hgate => (hresult pt hstart hprop hgate).2
  have hcache := wc_cachedSafety hvalid.toScheduleWellFormed hseed hinv
  have hcover (pt : PtSP) (hstart : w.u + 2 ≤ pt.s)
      (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
      (hgate : SA.gateTime p.toParams pt.s ≤ rho.horizon) :
      ∃ x ∈ rho.honest, Block.Preceq pt.P (S_at p c E rho rho.events.length x) := by
    obtain ⟨j, x, hr⟩ := (hresult pt hstart hprop hgate).1
    have hb := wc_gate_result_served hvalid.toScheduleWellFormed
      (hinv rho.events.length ⟨hseed.within, le_rfl⟩) hr
    exact ⟨x, hr.honest, Gen.Pure.block_preceq_trans hb
      (hcache.monotone (j + 1) rho.events.length x
        ⟨hr.afterCut.trans (Nat.le_succ j), Nat.succ_le_of_lt hr.completed⟩
        ⟨hseed.within, le_rfl⟩ (Nat.succ_le_of_lt hr.completed) hr.honest)⟩
  exact ⟨hsafe, hincl, wc_growth_of_safety_inclusion ΔF w.u w.QStar iStar hcache hcover
    ⟨hvalid, hlinked, hcstar, hnr, hdelta, hroots⟩ hseed.cut hsafe hincl hgate⟩

end AvailableChain.FGSA.Run
end
