module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Epoch
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.StepInit -- shake: keep
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Safety
public import AvailableChainFGSARun.Proofs.AC

public section

/-! WC plan §6.6; DC finite service follows the proved joint history. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {w : HealingWitness} {iStar : Nat}

/-- WC plan §6.6; DC a completed guard writes its result into the local output. -/
theorem wcg_gate_result_served {i j : Nat} {x : V} {s : Slot} {B : Block}
    (hsch : V2.D.ScheduleWellFormed E rho) (hi : WCInv p c E rho w iStar i)
    (hr : WCResult p c E rho w iStar i j x s B) :
    Block.Preceq B (S_at p c E rho (j + 1) x) := by
  obtain ⟨C, hC, _, hpass⟩ := hi.nonempty j x s hr.afterCut hr.completed
    hr.honest (wcg_result_enabled hr hsch) hr.label
  have hrawAt : gateResultAt p c E rho j = some (SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s) := by
    rw [gateResultAt_eq_gateResult p c E rho hsch hr.event,
      gateResult_eq_saved p c E rho hsch hr.event, clockPre_fg]
    exact fgsa_gate_saved_result E rho hsch hr.event
      (fgsa_gate_joined_of_enabled E rho (wcg_result_enabled hr hsch))
  have hraw := Option.some.inj (hrawAt.symm.trans hr.value)
  obtain ⟨y, r, he, _, G, hG, hguard⟩ := hpass
  have hevent := V2.Event.tick.inj (Option.some.inj (he.1.symm.trans hr.event))
  have hlabel : r = s := by
    have ht := hevent.2
    change 4 * p.Δ * (r : Int) + 6 * p.Δ = 4 * p.Δ * (s : Int) + 6 * p.Δ at ht
    have hcast : (r : Int) = s := by nlinarith [p.deltaPos]
    exact Int.ofNat_inj.mp hcast
  have hxy := hevent.1
  subst y
  subst r
  have heq : G = B := Option.some.inj (hG.symm.trans hraw)
  subst G
  have hview := fgsa_clockPre_gateView p (storeAt p c E rho j x) s
  have hraw' : (fgsaAC E rho).raw j s x = some B := by
    rw [clockPre_fg] at hraw
    have he := congrArg (fun v => SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho j x).fg.F) v s) hview
    exact he.symm.trans hraw
  have hguard' : ∀ lease ∈ ((fgsaAC E rho).gateView j x s).obligations,
      Block.Compatible (Gen.AC.Lease.target lease) B := by
    intro lease hm
    have he : (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)).base.obligations =
        ((fgsaAC E rho).gateView j x s).obligations := by
      have he' := congrArg GridCO.State.obligations hview
      exact he'
    rw [← he] at hm
    have hg := List.any_eq_false.mp hguard lease hm
    simpa only [Gen.AC.Lease.target, Block.Compatible, Bool.not_eq_true',
      Bool.not_eq_false] using hg
  have hc := wcg_result_output_compatible hsch hi hr hr.afterCut (Nat.le_of_lt hr.completed)
    hr.honest
  have hadv : Block.Preceq (S_at p c E rho j x) (GridCO.advance (S_at p c E rho j x) B) := by
    unfold GridCO.advance
    split
    · exact block_preceq_refl _
    · next hn =>
      rcases Bool.or_eq_true_iff.mp hc with h | h
      · exact h
      · exact (hn h).elim
  have hb : Block.Preceq B (GridCO.advance (S_at p c E rho j x) B) := by
    unfold GridCO.advance
    split
    · assumption
    · exact block_preceq_refl _
  rcases (fgsaAC_gate_write E rho j s x
    (wcg_gate_pre_joined (wcg_result_enabled hr hsch)) hr.event).effects with hskip | hrun
  · obtain ⟨result, hsaved⟩ := hskip.1
    have hfresh := fgsa_gate_fresh E rho hsch hr.event
    change GridCO.savedGenuine (storeAt p c E rho j x).base s = some result at hsaved
    change GridCO.savedGenuine (storeAt p c E rho j x).base s = none at hfresh
    rw [hfresh] at hsaved
    cases hsaved
  · have hw := (hrun.accept B hraw' hguard').1
    change S_at p c E rho (j + 1) x = Gen.AC.normalizeOutput (F_at p c E rho j x)
      (GridCO.advance (S_at p c E rho j x) B) at hw
    have hn : Block.preceq (F_at p c E rho j x)
        (GridCO.advance (S_at p c E rho j x) B) = true :=
      block_preceq_trans (nestOK_stateBefore E rho j x) hadv
    rwa [hw, Gen.AC.normalizeOutput_def, ite_eq_left hn]

/-- An enabled original gate result persists to both inclusive output getters. -/
theorem wcg_gate_result_outputs {n j : Nat} {x : V} {s : Slot} {B : Block} {t : Time}
    (hS : V2.D.ScheduleWellFormed E rho) (hs : WCSeed p c E rho w iStar)
    (inv : WCInv p c E rho w iStar n) (hr : WCResult p c E rho w iStar n j x s B)
    (ht : SA.gateTime p.toParams s ≤ t) (hin : timeIdx rho t ≤ n)
    (g : V2.D.Output (fgsa p c))
    (hg : g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed]) :
    Block.Preceq B (V2.D.outputAt E rho g x t) := by
  have hji := (V2.D.Engine.index_lt_read_length_iff hS t hr.event).mpr ht
  have hm := wcg_output_mono_of_inv hS hs inv (j + 1) (timeIdx rho t) x
    ⟨hr.afterCut.trans (Nat.le_succ j), (Nat.succ_le_of_lt hji).trans hin⟩
    ⟨hr.afterCut.trans hji.le, hin⟩ (Nat.succ_le_of_lt hji) hr.honest
  rw [fgsa_outputAt_eq_S_at E rho hS g hg x t]
  exact block_preceq_trans (wcg_gate_result_served hS inv hr) hm

/-- A later-reader service inclusion carries to both output getters. -/
theorem wcg_service_result_outputs {d t : Time} {B : Block} {y : V}
    (hS : V2.D.ScheduleWellFormed E rho)
    (hservice : ∀ i x, afterTicksIdx rho d ≤ i → i ≤ rho.events.length →
      confirmedReaderIdx p c E rho x i → Block.Preceq B (S_at p c E rho i x))
    (hcut : afterTicksIdx rho d ≤ timeIdx rho t)
    (hy : confirmedReaderIdx p c E rho y (timeIdx rho t))
    (g : V2.D.Output (fgsa p c))
    (hg : g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed]) :
    Block.Preceq B (V2.D.outputAt E rho g y t) := by
  rw [fgsa_outputAt_eq_S_at E rho hS g hg y t]
  exact hservice _ y hcut (List.length_filter_le _ _) hy

variable [Fintype V] {ΔF : Time}

/-- WC plan §6.6; DC finite service needs only history through the requested read. -/
theorem wcg_service4_prefix :
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
  WCSeed p c E rho w iStar → ∀ n, WCInv p c E rho w iStar n →
    ∀ j x s B, WCResult p c E rho w iStar n j x s B →
    SA.gateTime p.toParams s + 4 * p.Δ ≤ rho.horizon →
    ∀ i y, afterTicksIdx rho (SA.gateTime p.toParams s + 4 * p.Δ) ≤ i → i ≤ n →
      confirmedReaderIdx p c E rho y i → Block.Preceq B (S_at p c E rho i y) := by
  intro hvalid _hlinked _hcstar _hwakes hdelta _hroots _hsync _hdeltaF _hfaultQ
    _haccountable hpart _hstore _hcumul _hmono _hactive _hframe _hmeta _hrec _hgeo _hcert
    _hsrc _hlabel _hqc _hstrat _hnoslash _hemitted _htargets _hlease _hfast _hdeadlines
    _hheldRows _hscopeRows _hfinalHead hs n inv j x s B hr hhor i y hcut hin hy
  have hS := hvalid.toScheduleWellFormed
  have hnext : SA.gateTime p.toParams (s + 1) = SA.gateTime p.toParams s + 4 * p.Δ := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ =
      (4 * p.Δ * (s : Int) + 6 * p.Δ) + 4 * p.Δ
    push_cast
    ring
  have hcut' : afterTicksIdx rho (SA.gateTime p.toParams (s + 1)) ≤ i := hnext ▸ hcut
  have hhor' : SA.gateTime p.toParams (s + 1) ≤ rho.horizon := hnext ▸ hhor
  have hcTime : SA.voteTime p.toParams (w.u + 1) ≤
      SA.gateTime p.toParams (s + 1) := by
    have hh : ((w.u + 1 : Nat) : Int) ≤ (s + 1 : Nat) := Int.ofNat_le.mpr
      (Nat.succ_le_succ hr.label.le)
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤
      4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    nlinarith [p.deltaPos]
  have hilen := hin.trans inv.interval.2
  obtain ⟨z, q, _hz, hGq, _⟩ := wcg_joined_gate_witness hvalid hdelta (s + 1)
    (hpart _ hcTime hhor') hhor'
  have hqc : q < afterTicksIdx rho (SA.gateTime p.toParams (s + 1)) := by
    by_contra hn
    have hf := V2.D.Engine.filter_false_of_index_ge hS
      (cutPred (SA.gateTime p.toParams (s + 1))) (by
        intro e f hk hf
        exact decide_eq_true (hk.trans (of_decide_eq_true hf)))
      (Nat.le_of_not_gt hn) hGq.1
    have htrue : cutPred (SA.gateTime p.toParams (s + 1))
        (.tick z (SA.gateTime p.toParams (s + 1)) : V2.Event V (fgsa p c).Object) = true :=
      decide_eq_true le_rfl
    rw [htrue] at hf
    cases hf
  have hTime := wcg_event_before_prefixTime hS hilen (hqc.trans_le hcut') hGq.1
  have finish (k r : Nat) (C : Block)
      (hrC : WCResult p c E rho w iStar n k y r C) (hki : k < i)
      (hBC : Block.Preceq B C) : Block.Preceq B (S_at p c E rho i y) := by
    have hCout := wcg_gate_result_served hS inv hrC
    have hm := wcg_output_mono_of_inv hS hs inv (k + 1) i y
      ⟨hrC.afterCut.trans (Nat.le_succ k), (Nat.succ_le_of_lt hki).trans hin⟩
      ⟨hrC.afterCut.trans hki.le, hin⟩ (Nat.succ_le_of_lt hki) hy.1.1
    exact block_preceq_trans hBC (block_preceq_trans hCout hm)
  by_cases hmarker : ∀ wake, (storeAt p c E rho i y).restartTime = some wake →
      wake ≤ slotStartZ p ((s + 1 : Nat) : Int)
  · obtain ⟨k, hki, hG⟩ := wcg_confirmedReader_early_gate hvalid hdelta hy hhor'
      hTime hcut' hmarker
    have hk := (wcg_gate_cut_iff hS hs hG.1).mpr (hr.label.trans (Nat.lt_succ_self s))
    obtain ⟨C, hC, _, _⟩ := inv.nonempty k y (s + 1) hk (hki.trans_le hin) hy.1.1 hG
      (hr.label.trans (Nat.lt_succ_self s))
    have hrC : WCResult p c E rho w iStar n k y (s + 1) C :=
      ⟨hy.1.1, hk, hki.trans_le hin, hr.label.trans (Nat.lt_succ_self s), hG.1, hC⟩
    exact finish k (s + 1) C hrC hki
      (inv.ordered j k x y s (s + 1) B C hr hrC (Nat.lt_succ_self s))
  · push Not at hmarker
    obtain ⟨wake, hw', hlate'⟩ := hmarker
    have hc := hy.1.2.2
    rw [hw'] at hc
    obtain ⟨r, k, hwr, _hrt, hki, hG, _hA, _hR⟩ := hc
    have hsr : s < r := by
      have hh := hlate'.trans_le hwr
      change 4 * p.Δ * ((s + 1 : Nat) : Int) < 4 * p.Δ * (r : Int) at hh
      have hcast : (s : Int) + 1 < r := by push_cast at hh; nlinarith [p.deltaPos]
      exact Nat.lt_of_succ_lt (Int.ofNat_lt.mp (by exact_mod_cast hcast))
    have hk := (wcg_gate_cut_iff hS hs hG.1).mpr (hr.label.trans hsr)
    obtain ⟨C, hC, _, _⟩ := inv.nonempty k y r hk (hki.trans_le hin) hy.1.1 hG
      (hr.label.trans hsr)
    have hrC : WCResult p c E rho w iStar n k y r C :=
      ⟨hy.1.1, hk, hki.trans_le hin, hr.label.trans hsr, hG.1, hC⟩
    exact finish k r C hrC hki (inv.ordered j k x y s r B C hr hrC hsr)

/-- WC plan §6.6; DC the next covered gate serves the result at every honest reader. -/
theorem wcg_service4 : WCGService4Statement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs hinv j x s B hx hj ht hlabel' hB hhor i y hcut hilen hy
  exact wcg_service4_prefix hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs rho.events.length (hinv rho.events.length ⟨hs.within, le_rfl⟩)
    j x s B ⟨hx, hj, (List.getElem?_eq_some_iff.mp ht).1, hlabel', ht, hB⟩
    hhor i y hcut hilen hy

end AvailableChain.FGSA.Run
end
