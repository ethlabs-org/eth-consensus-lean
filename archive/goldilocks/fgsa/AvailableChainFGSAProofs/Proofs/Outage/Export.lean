module
public import AvailableChainFGSAProofs.Proofs.Outage.Suppliers
public import AvailableChainFGSAProofs.Proofs.Outage.ExactProposalRetained
public import AvailableChainFGSAProofs.Proofs.Outage.InclusionGateBody
public import AvailableChainFGSAProofs.Proofs.Outage.GrowthConsumer
-- shake keep reason: facade coverage
public import AvailableChainFGSAProofs.Proofs.Outage.GrowthSuppliers -- shake: keep
public import AvailableChainFGSAProofs.Proofs.Outage.Close
public import AvailableChainFGSAProofs.Proofs.Shared.Claims
-- shake: keep (Clean cut statement boundary)


public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable (p : Params)

section CleanClaims

-- Each supplier has the same binders and conclusion as its reviewed projection.
variable
    (hstore : ∀ {In V : Type} [DecidableEq V] (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)), RStore p c E rho)
    (hframe : ∀ {In V : Type} [DecidableEq V] (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)), RFrameExactNext p c E rho)
    (hstrat : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
      SourceDisciplinePrem p c E rho pt → RStrat p c E rho)
    (hsrc : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
      SourceDisciplinePrem p c E rho pt → SrcFrameAboveStmt p c E rho)
    (hordered : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
        SA.gateTime p.toParams r ≤ pt.b₀ → SA.gateTime p.toParams s ≤ pt.b₀ →
        confirmedReader p c E rho x (SA.gateTime p.toParams r) →
        confirmedReader p c E rho y (SA.gateTime p.toParams s) →
        gateResult p c E rho x r = some (some B) →
        gateResult p c E rho y s = some (some C) →
        (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ j x s, j < timeIdx rho pt.b₀ → x ∈ rho.honest → enabledGateAt p c E rho j x s →
        ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
        SA.gateTime p.toParams s ≤ pt.b₀ → gateResult p c E rho x s = some (some B) →
        joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
        vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ i v, i ≤ timeIdx rho pt.b₀ → v ∈ rho.honest →
        let st := storeAt p c E rho i v
        let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
        below (F_at p c E rho i v) ∧ below (J_at p c E rho i v) ∧
        below (S_at p c E rho i v) ∧
        (∀ row ∈ st.base.obligations, below row.1 ∧
          ∃ j < i, ∃ s B, enabledGateAt p c E rho j v s ∧ gatePassedAt p c E rho j ∧
            gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B) ∧
        (∀ s C, GridCO.savedGenuine st.base s = some (some C) → below C ∧
          ∃ j < i, V2.D.restartFree rho v j i ∧
          enabledGateAt p c E rho j v s ∧ gateResultAt p c E rho j = some (some C)) ∧
        (∀ j s C, j < i → enabledGateAt p c E rho j v s →
          V2.D.restartFree rho v j i → FGSA.activeCompatible st C = true →
          gateResultAt p c E rho j = some (some C) →
          GridCO.savedGenuine st.base s = some (some C)) ∧
        (∀ s X, X ∈ (FGSA.fastWriteAt st s).getD [] → below X ∧
          ∃ j < i, V2.D.restartFree rho v j i ∧
          enabledGateAt p c E rho j v s ∧ gatePassedAt p c E rho j ∧
            ∃ C, gateResultAt p c E rho j = some (some C) ∧
              Block.Preceq X C ∧ fastAt p c E rho v s X) ∧
        (S_at p c E rho i v = .genesis ∨
          (∃ j < i, ∃ s, enabledGateAt p c E rho j v s ∧
            gateResultAt p c E rho j = some (some (S_at p c E rho i v))) ∨
          (∃ j ≤ i, S_at p c E rho i v = F_at p c E rho j v)))
    (hrows : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ i j x r a e, i ≤ timeIdx rho pt.b₀ → j < i → HonestRowAt p c E rho j x r a →
        namedEntry a.payload.height_pair = some e →
        ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
          BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))

include hstore hframe hstrat hsrc hordered hnonempty htransfer hleases hrows

/-- ROOT-DIGEST W2b. Blueprint 03 §4; DC available/stableIncludedFast: INTENTIONAL exact HEAD.
The supplier projections restore the frozen claim, including sleep silence. -/
theorem outage_exactProposalClaim_of : ExactProposalClaim p := by
  intro V _ _ In c E rho pt ΔF h
  have hv : 0 < SA.voteTime p.toParams pt.s := by
    change 0 < 4 * p.Δ * (pt.s : Time) + p.Δ
    have hd := p.deltaPos
    positivity
  have hq := h.set.pre.toCleanCut.faultQ_of_pos (hv.trans_le h.hhor)
  obtain ⟨hs, ho, hn, ht, hl, hr⟩ :=
    outage_supplier_history p hsrc hordered hnonempty htransfer hleases hrows
      c E rho h.set (hv.trans_le h.hhor)
  have hbelow : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1 :=
    fun i v hi hv row hrow => ((hl i v hi hv).2.2.2.1 row hrow).1
  exact ⟨fun x hx hJ => inclusion_exact_receipt (_hstrat := hstrat c E rho () ⟨h.set.pre.base, hq⟩)
    E rho ΔF h.set (outage_supplier_inclusion_inputs (pt := ()) ⟨h.set⟩)
    (hstore c E rho) (hframe c E rho)
      hs ho hn ht hbelow hr pt h.prop h.hhor x ⟨hx, hJ⟩,
    inclusion_exact_head (hstrat := hstrat c E rho () ⟨h.set.pre.base, hq⟩)
      E rho ΔF h.set (outage_supplier_inclusion_inputs (pt := ()) ⟨h.set⟩)
    (hstore c E rho) (hframe c E rho)
      hs ho hn ht hbelow hr pt h.prop h.hhor,
    inclusion_sleep_silence E rho pt.s⟩

variable
    (hmono : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : Unit),
      CleanPrem p c E rho pt ΔF →
      ScopedMono (confirmedReaderIdx p c E rho) (S_at p c E rho) (· ≤ rho.events.length))

include hmono

/-- ROOT-DIGEST W2b. Blueprint 03 §5; DC available/stableIncludedFast: INTENTIONAL post-gate event
read.
The supplier projections restore the frozen claim at the finite Clean horizon. -/
theorem outage_cleanInclusionPostGateClaim_of : CleanInclusionPostGateClaim p := by
  intro V _ _ In c E rho pt ΔF h
  have hg : 0 < SA.gateTime p.toParams pt.s := by
    change 0 < 4 * p.Δ * (pt.s : Time) + 6 * p.Δ
    have hd := p.deltaPos
    positivity
  have hq := h.set.pre.toCleanCut.faultQ_of_pos (hg.trans_le h.hhor)
  obtain ⟨hs, ho, hn, ht, hl, hr⟩ :=
    outage_supplier_history p hsrc hordered hnonempty htransfer hleases hrows
      c E rho h.set (hg.trans_le h.hhor)
  have hbelow : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1 :=
    fun i v hi hv row hrow => ((hl i v hi hv).2.2.2.1 row hrow).1
  have hHistory : InclusionHistoryBounds E rho := ⟨by
    intro i x hi hx
    have hb := hl i x hi hx
    exact ⟨hb.1, hb.2.1, hb.2.2.1,
      fun row hr => (hb.2.2.2.1 row hr).1,
      fun r C hC => (hb.2.2.2.2.1 r C hC).1⟩⟩
  exact clean_inclusion_post_gate_body (hstrat := hstrat c E rho () ⟨h.set.pre.base, hq⟩) E rho ΔF
    h.set (outage_supplier_inclusion_inputs (pt := ()) ⟨h.set⟩) hHistory
    (hstore c E rho) (hframe c E rho)
    hs ho hn ht hbelow hr pt h.prop h.hhor (hmono c E rho () ⟨h.set⟩)

variable
    (hReaderGate : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : Unit),
      CleanPrem p c E rho pt ΔF →
      ∀ q i x, x ∈ rho.honest → SA.gateTime p.toParams q ≤ rho.horizon →
        enabledGateAt p c E rho i x q →
        ∃ C, gateResultAt p c E rho i = some (some C) ∧
          Block.Preceq C (S_at p c E rho (timeIdx rho (SA.gateTime p.toParams q)) x))
    (hReaderMono : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : Unit),
      CleanPrem p c E rho pt ΔF →
      ScopedMono (confirmedReader p c E rho)
        (fun t x => S_at p c E rho (timeIdx rho t) x)
        (fun t => 0 ≤ t ∧ t ≤ rho.horizon))

include hReaderGate hReaderMono

omit hmono in
/-- ROOT-DIGEST W2b. Blueprint 03 §5; DC available/stableIncludedFast: INTENTIONAL inclusive public
reads.
The supplier projections restore the frozen claim at the finite Clean horizon. -/
theorem outage_cleanInclusionClaim_of : CleanInclusionClaim p := by
  intro V _ _ In c E rho pt ΔF h
  have hg : 0 < SA.gateTime p.toParams pt.s := by
    change 0 < 4 * p.Δ * (pt.s : Time) + 6 * p.Δ
    have hd := p.deltaPos
    positivity
  have hq := h.set.pre.toCleanCut.faultQ_of_pos (hg.trans_le h.hhor)
  obtain ⟨hs, ho, hn, ht, hl, hr⟩ :=
    outage_supplier_history p hsrc hordered hnonempty htransfer hleases hrows
      c E rho h.set (hg.trans_le h.hhor)
  have hbelow : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1 :=
    fun i v hi hv row hrow => ((hl i v hi hv).2.2.2.1 row hrow).1
  have hHistory : InclusionHistoryBounds E rho := ⟨by
    intro i x hi hx
    have hb := hl i x hi hx
    exact ⟨hb.1, hb.2.1, hb.2.2.1,
      fun row hr => (hb.2.2.2.1 row hr).1,
      fun r C hC => (hb.2.2.2.2.1 r C hC).1⟩⟩
  exact clean_inclusion_body (hstrat := hstrat c E rho () ⟨h.set.pre.base, hq⟩)
    E rho ΔF h.set (outage_supplier_inclusion_inputs (pt := ()) ⟨h.set⟩) hHistory
    (hstore c E rho) (hframe c E rho)
    hs ho hn ht hbelow hr pt h.prop h.hhor
    (outage_supplier_later_origins E rho h.set.pre.base
      (hReaderGate c E rho () ⟨h.set⟩) (hReaderMono c E rho () ⟨h.set⟩) pt.s)


end CleanClaims

/-- P20: only the two scoped growth suppliers are parameters. The preceding
CleanClaims include lists do not apply outside that section. -/
theorem outage_cleanGrowthClaim_of (p : Params)
    (hcompatible : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time),
      CleanSet p c E rho ΔF →
      ∀ s B, HonestProposal E rho (fgsaInterface p c) s B →
      SA.gateTime p.toParams s ≤ rho.horizon →
      ∀ u x g, 0 ≤ u → u < V2.D.proposalTime (fgsaInterface p c) s →
        confirmedReader p c E rho x u →
        g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
        Block.Compatible (V2.D.outputAt E rho g x u) B)
    (hinclusion : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time),
      CleanSet p c E rho ΔF →
      ∀ s B, HonestProposal E rho (fgsaInterface p c) s B →
      SA.gateTime p.toParams s ≤ rho.horizon →
      ∀ u x g, SA.gateTime p.toParams s ≤ u → u ≤ rho.horizon →
        confirmedReader p c E rho x u →
        g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
        Block.Preceq B (V2.D.outputAt E rho g x u)) :
    CleanGrowthClaim p := by
  exact clean_growth_claim_body p hcompatible hinclusion


/-- The named foundation and finite Clean producers close the scoped outage body. -/
theorem outage_outageCompatClaim_of
    (hfoundation : FGFoundationClaim p) (hsrc : SrcFrameAboveClaim p)
    (hdisc : SourceDisciplineClaim p)
    (hClean : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      {b₀ ΔF : Time}, HealthyPrefixSleep₂ p c E rho b₀ ΔF →
      FaultQ p.n (Gen.V2.Duty.faulty rho).card →
      FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
      OutageCleanCutInputs (p := p) (c := c) E rho b₀) : OutageCompatClaim p := by
  intro V _ _ In c E rho fast pt ΔF h
  have hq := h.set.pre.faultQ_of_pos (outage_cut_pos h.set.toOutage₂)
  have hp : SourceDisciplinePrem p c E rho () := ⟨h.set.pre.base, hq⟩
  have hf0 := hfoundation c E rho () hp
  have hf : FGFoundation p c E rho :=
    ⟨hf0.store, hf0.cumul, hf0.mono, hf0.frame, hf0.geo, hf0.strat, hf0.reconcile⟩
  have hs := hsrc c E rho () hp
  have hd := hdisc c E rho () hp
  have hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C) := by
    intro k x r a e ha he
    obtain ⟨e', C, G, he', hC, hn, hTC, hG, hCG, hfast⟩ := hd.1.2.2 k x r a ha
    exact ⟨C, G, hC, (Option.some.inj (he.symm.trans he')).trans hn, hTC, hG, hCG, hfast⟩
  exact outage_compat_body hf hs hd.1.1 hnamed
    (hClean c E rho h.set.sleepPre hq hf hs) h

/-- Fast P1 is the public scoped outage projection. -/
theorem outage_fastP1Claim_of
    (hfoundation : FGFoundationClaim p) (hsrc : SrcFrameAboveClaim p)
    (hdisc : SourceDisciplineClaim p)
    (hClean : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      {b₀ ΔF : Time}, HealthyPrefixSleep₂ p c E rho b₀ ΔF →
      FaultQ p.n (Gen.V2.Duty.faulty rho).card →
      FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
      OutageCleanCutInputs (p := p) (c := c) E rho b₀) : FastP1Claim p := by
  intro V _ _ In c E rho pt ΔF h
  exact (outage_outageCompatClaim_of p hfoundation hsrc hdisc hClean c E rho true pt ΔF h).1

/-- Slow P1 includes the unchanged covered-receiver lease guarantee. -/
theorem outage_slowP1Claim_of
    (hfoundation : FGFoundationClaim p) (hsrc : SrcFrameAboveClaim p)
    (hdisc : SourceDisciplineClaim p)
    (hClean : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      {b₀ ΔF : Time}, HealthyPrefixSleep₂ p c E rho b₀ ΔF →
      FaultQ p.n (Gen.V2.Duty.faulty rho).card →
      FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
      OutageCleanCutInputs (p := p) (c := c) E rho b₀) : SlowP1Claim p := by
  intro V _ _ In c E rho pt ΔF h
  exact outage_outageCompatClaim_of p hfoundation hsrc hdisc hClean c E rho false pt ΔF h

/-- The per-run public boundary uses the same named finite Clean input bundle. -/
theorem outage_compat_body_of_cut {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {fast : Bool} {pt : PtOut} {ΔF : Time}
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hClean : OutageCleanCutInputs (p := p) (c := c) E rho pt.b₀)
    (h : OutagePrem p c fast E rho pt ΔF) : OutageCompatAt p c E rho fast pt :=
  outage_compat_body hf hsrc htsrc hnamed hClean h

end AvailableChain.FGSA.Run
end
