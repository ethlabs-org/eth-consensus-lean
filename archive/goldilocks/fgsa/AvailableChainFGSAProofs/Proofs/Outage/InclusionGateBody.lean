module
public import AvailableChainFGSAProofs.Proofs.Outage.InclusionGateService
public import AvailableChainFGSAProofs.Proofs.Outage.GrowthConsumer

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- A caught-up read after the actual gate proves that gate was enabled. -/
theorem inclusion_enabled_gate_of_after_reader
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {s : Slot}
    (hi : IsGateTick p c rho i x s)
    (hx : confirmedReaderAtIdx p c E rho x
      (afterTicksIdx rho (SA.gateTime p.toParams s)) (SA.gateTime p.toParams s)) :
    enabledGateAt p c E rho i x s := by
  have hnode := (afterTicks_node E rho hs hi).trans (rho.step_tick_eq E hi).1.symm
  rw [afterTicks_eq_stateBefore E rho hs] at hnode
  have hMark : (storeAt p c E rho (afterTicksIdx rho (SA.gateTime p.toParams s)) x).restartTime =
      (storeAt p c E rho i x).restartTime := by
    change (rho.stateBefore E _ x).st.restartTime = (rho.stateBefore E i x).st.restartTime
    rw [hnode, (rho.step_tick_eq E hi).1]
    have ht := tick_st (c := c) E rho (rho.stateBefore E i x) x
      (SA.gateTime p.toParams s)
    exact (congrArg State.restartTime ht).trans (fgsa_clock_restartTime _ _)
  refine ⟨hi, ?_⟩
  have hc := hx.2.2
  rw [hMark] at hc
  cases hm : (storeAt p c E rho i x).restartTime with
  | none => trivial
  | some w =>
    rw [hm] at hc
    obtain ⟨q, _, hwq, hqt, _⟩ := hc
    have hqs := (arming_gate_le_iff p q s).mp hqt
    exact hwq.trans (by
      change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (s : Int)
      exact mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr hqs) (by linarith [p.deltaPos]))

/-- ROOT-DIGEST W2b. Blueprint 03:418–458; S3a Q12:3454; plan I-GATE, G6. Class (iii).
DC: INTENTIONAL; this is the unfolded InclusionPostGateAt body.
The event-prefix monotonicity conjunct has the approved confirmed-reader scope. -/
theorem clean_inclusion_post_gate_body [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hInputs : InclusionReceiverInputs E rho)
    (hHistory : InclusionHistoryBounds E rho)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      enabledGateAt p c E rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1)
    (hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    (pt : PtSP) (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hhor : SA.gateTime p.toParams pt.s ≤ rho.horizon)
    (hmono : ScopedMono (confirmedReaderIdx p c E rho) (S_at p c E rho)
      (· ≤ rho.events.length))
    (hstrat : RStrat p c E rho) :
    ScopedServed (fun x i => confirmedReaderAtIdx p c E rho x i
      (SA.gateTime p.toParams pt.s)) (S_at p c E rho) pt.P
      (fun i => i = afterTicksIdx rho (SA.gateTime p.toParams pt.s)) ∧
    ScopedMono (confirmedReaderIdx p c E rho) (S_at p c E rho)
      (· ≤ rho.events.length) := by
  refine ⟨?_, hmono⟩
  intro k x hk hx
  subst k
  have hs := hset.pre.base.valid.toScheduleWellFormed
  have he : ((4 * pt.s + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams pt.s := by
    change ((4 * pt.s + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (pt.s : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨i, hi, _⟩ := fgsa_tick_total E rho hs hset.pre.base.delta x hx.1
    (4 * pt.s + 6) (he ▸ hhor) (he ▸ hx.2.1)
  rw [he] at hi
  have hout := (inclusion_gate_exact (hstrat := hstrat) E rho ΔF hset hInputs hHistory
    hstore hframe hsrc hordered
    hnonempty
    htransfer hleases hrows pt hprop hhor hx.1
    (inclusion_enabled_gate_of_after_reader E rho hs hi hx)).2.2.2
  have hnode := (afterTicks_node E rho hs hi).trans (V2.D.Run.step_tick_eq E rho hi).1.symm
  rw [afterTicks_eq_stateBefore E rho hs] at hnode
  have hS := congrArg (fun nd : Node p => nd.st.base.stableRecord) hnode
  change Block.Preceq pt.P (S_at p c E rho (afterTicksIdx rho _) x)
  rw [show S_at p c E rho (afterTicksIdx rho _) x = S_at p c E rho (i + 1) x from
    by rw [S_at_def, S_at_def]; exact hS, hout]
  exact block_preceq_refl _

/-- ROOT-DIGEST W2b. Blueprint 03:418–458; S3a Q12:3454; plan I-READ, G7. Class (iii).
DC: INTENTIONAL; the later-read supplier gives an actual enabled gate origin
at or after the inclusion label. Ordering gives inclusion at the public read.
The origin supplier remains owned work; it is not a public claim premise. -/
theorem clean_inclusion_body [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hInputs : InclusionReceiverInputs E rho)
    (hHistory : InclusionHistoryBounds E rho)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      enabledGateAt p c E rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1)
    (hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    (pt : PtSP) (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hhor : SA.gateTime p.toParams pt.s ≤ rho.horizon)
    (hOrigins : ∀ t x, SA.gateTime p.toParams pt.s ≤ t → t ≤ rho.horizon →
      confirmedReader p c E rho x t →
      ∃ q i B, pt.s ≤ q ∧ SA.gateTime p.toParams q ≤ t ∧
        enabledGateAt p c E rho i x q ∧ gateResultAt p c E rho i = some (some B) ∧
        Block.Preceq B (S_at p c E rho (timeIdx rho t) x))
    (hstrat : RStrat p c E rho) :
    ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      ScopedServed (confirmedReader p c E rho) (fun t x => V2.D.outputAt E rho g x t) pt.P
        (fun t => SA.gateTime p.toParams pt.s ≤ t ∧ t ≤ rho.horizon) := by
  have hs := hset.pre.base.valid.toScheduleWellFormed
  obtain ⟨z, hz, _, _, j, hG⟩ := inclusion_joined_gate_witness E rho hset pt.s hhor
  have hExact := inclusion_gate_exact (hstrat := hstrat) E rho ΔF hset hInputs hHistory
    hstore hframe hsrc hordered hnonempty htransfer hleases hrows pt hprop hhor hz
    hG
  intro g hg t x ht hx
  obtain ⟨q, i, B, hsq, hqt, hGX, hB, hBS⟩ := hOrigins t x ht.1 ht.2 hx
  have hBR : gateResult p c E rho x q = some (some B) :=
    (gateResultAt_eq_gateResult p c E rho hs hGX.1) ▸ hB
  have hPB : Block.Preceq pt.P B := by
    rcases hsq.lt_or_eq with hlt | rfl
    · exact (hordered z x pt.s q pt.P B hz hx.1 hhor (hqt.trans ht.2)
        hExact.1 hBR).1 hlt
    · have hX := inclusion_gate_exact (hstrat := hstrat) E rho ΔF hset hInputs hHistory
        hstore hframe hsrc hordered hnonempty htransfer hleases hrows pt hprop hhor hx.1
        hGX
      have he := Option.some.inj (Option.some.inj (hBR.symm.trans hX.1))
      rw [he]
      exact block_preceq_refl _
  have hread : V2.D.outputAt E rho g x t = S_at p c E rho (timeIdx rho t) x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;>
      change (V2.D.Run.readAt E rho t x).st.base.stableRecord = _ <;>
      rw [S_at_def, V2.D.Engine.readAt_eq_stateBefore hs t] <;> rfl
  change Block.Preceq pt.P (V2.D.outputAt E rho g x t)
  rw [hread]
  exact block_preceq_trans hPB hBS

/-- One inclusive gate witness supplies growth compatibility for earlier readers.
Same-time deliveries preserve the exact proposal by the Clean finality bound.
This proof uses no global monotonicity and no later-reader origin supplier. -/
theorem clean_inclusion_gate_witness [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hInputs : InclusionReceiverInputs E rho)
    (hHistory : InclusionHistoryBounds E rho)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      enabledGateAt p c E rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1)
    (hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    (pt : PtSP) (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hhor : SA.gateTime p.toParams pt.s ≤ rho.horizon)
    (hstrat : RStrat p c E rho) :
    ∃ y, confirmedReader p c E rho y (SA.gateTime p.toParams pt.s) ∧
      Block.Preceq pt.P (S_at p c E rho (timeIdx rho (SA.gateTime p.toParams pt.s)) y) := by
  classical
  let d := SA.gateTime p.toParams pt.s
  let n := timeIdx rho d
  have hV := hset.pre.base.valid
  have hs := hV.toScheduleWellFormed
  obtain ⟨z, hz, _, _, i, hG⟩ := inclusion_joined_gate_witness E rho hset pt.s hhor
  have hExact := inclusion_gate_exact (hstrat := hstrat) E rho ΔF hset hInputs hHistory
    hstore hframe hsrc hordered hnonempty htransfer hleases hrows pt hprop hhor hz
    hG
  have hhead := inclusion_headAtLabel (hstrat := hstrat) E rho ΔF hset hInputs
    hstore hframe hsrc hordered hnonempty htransfer hleases hrows pt hprop hhor
  have hprior := inclusion_prior_results_below E rho hset hordered hnonempty htransfer
    pt.s pt.P hprop.1.1 hhor hhead hz
  have hResults : ∀ r C, (r, C) ∈ cleanResults p c E rho n → Block.Preceq C pt.P := by
    intro r C hC
    obtain ⟨j, hj, x, ht, hg, hr⟩ := hC
    have htime : SA.gateTime p.toParams r ≤ d :=
      (V2.D.Engine.index_lt_read_length_iff hs d ht).mp hj
    rcases htime.lt_or_eq with hlt | heq
    · exact hprior r C ⟨j, (Gen.V2.Duty.index_lt_idxBefore_iff hs ht d).mpr hlt,
        x, ht, hg, hr⟩
    · have hrs : r = pt.s := by
        change 4 * p.Δ * (r : Int) + 6 * p.Δ =
          4 * p.Δ * (pt.s : Int) + 6 * p.Δ at heq
        have hri : (r : Int) = pt.s := by nlinarith [p.deltaPos]
        exact_mod_cast hri
      subst r
      have hx := hs.honest_only _ (List.mem_of_getElem? ht)
      have hX := inclusion_gate_exact (hstrat := hstrat) E rho ΔF hset hInputs hHistory
        hstore hframe hsrc hordered hnonempty htransfer hleases hrows pt hprop hhor hx
        ⟨ht, hg⟩
      have hr' : gateResult p c E rho x pt.s = some (some C) :=
        (gateResultAt_eq_gateResult p c E rho hs ht) ▸ hr
      have he := Option.some.inj (Option.some.inj (hr'.symm.trans hX.1))
      rw [he]
      exact block_preceq_refl _
  have hN : n ≤ timeIdx rho rho.horizon :=
    V2.D.Engine.read_length_mono _ _ hhor
  have hF : ∀ k, k ≤ n → ∀ y ∈ rho.honest, Block.Preceq (F_at p c E rho k y) pt.P := by
    intro k hkn y hy
    have hb := (hHistory.below k y (hkn.trans hN) hy).1
    rcases hb with hgen | ⟨q, C, hC, _, hXC⟩
    · rw [hgen]
      exact block_genesis_preceq _
    · obtain ⟨j, hj, x, ht, hg, hr⟩ := hC
      exact block_preceq_trans hXC (hResults q C ⟨j, hj.trans_le hkn, x, ht, hg, hr⟩)
  have hiN : i + 1 ≤ n := Nat.succ_le_of_lt
    ((V2.D.Engine.index_lt_read_length_iff hs d hG.1).mpr le_rfl)
  have hState : ∀ k, i + 1 ≤ k → k ≤ n → S_at p c E rho k z = pt.P := by
    intro k hik
    induction k, hik using Nat.le_induction with
    | base => intro _; exact hExact.2.2.2
    | succ k hik ih =>
      intro hkN
      have hkN' : k ≤ n := (Nat.le_succ k).trans hkN
      have hOld := ih hkN'
      have hiK : i < k := by omega
      change (fgsaAC E rho).output k z = pt.P at hOld
      change (fgsaAC E rho).output (k + 1) z = pt.P
      rcases fgsaAC_output_step E rho k z with hkeep | ⟨q, ht⟩ |
        ⟨o, t, C, ht, hb, ha, hrec⟩ | ⟨t, ht, hreset⟩
      · exact hkeep.trans hOld
      · have htime : SA.gateTime p.toParams q = d := by
          have hle := (V2.D.Engine.index_lt_read_length_iff hs d ht).mp
            (lt_of_lt_of_le (Nat.lt_succ_self k) hkN)
          have hge : d ≤ SA.gateTime p.toParams q := by
            by_contra hn
            have hki := V2.D.Engine.eventIndex_lt_of_time_lt hs ht hG.1 (lt_of_not_ge hn)
            omega
          exact le_antisymm hle hge
        have ht' : rho.events[k]? = some (.tick z d) := htime ▸ ht
        have hEq := fgsa_tick_unique E rho hs ht' hG.1
        omega
      · have hFP : Block.Preceq ((fgsaAC E rho).anchor (k + 1) z) pt.P :=
          hF (k + 1) hkN z hz
        rw [hrec, hOld, Gen.AC.normalizeOutput_def]
        exact ite_eq_left hFP
      · have hle := (V2.D.Engine.index_lt_read_length_iff hs d ht).mp
          (lt_of_lt_of_le (Nat.lt_succ_self k) hkN)
        have hki := V2.D.Engine.restart_index_lt_event hs ht hG.1 hle
          (by change (0 : Nat) < 1; decide)
        omega
  refine ⟨z, inclusion_confirmedReader_of_enabledGate E rho hV hz hG, ?_⟩
  rw [hState n hiN le_rfl]
  exact block_preceq_refl _

/-- The first P20 growth supplier follows from the actual inclusive gate
witness and the scoped public-output compatibility projection. -/
theorem clean_growth_compatible_from_history [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hInputs : InclusionReceiverInputs E rho)
    (hHistory : InclusionHistoryBounds E rho)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      enabledGateAt p c E rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1)
    (hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    (pt : PtSP) (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hhor : SA.gateTime p.toParams pt.s ≤ rho.horizon)
    (hOutputs : ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      ScopedCompat (confirmedReader p c E rho) (fun t x => V2.D.outputAt E rho g x t)
        (fun t => 0 ≤ t ∧ t ≤ rho.horizon))
    (hstrat : RStrat p c E rho) :
    ∀ u x g, 0 ≤ u → u < V2.D.proposalTime (fgsaInterface p c) pt.s →
      confirmedReader p c E rho x u →
      g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
      Block.Compatible (V2.D.outputAt E rho g x u) pt.P := by
  have hWitness := clean_inclusion_gate_witness (hstrat := hstrat) E rho ΔF hset hInputs hHistory
    hstore hframe hsrc hordered hnonempty htransfer hleases hrows pt hprop hhor
  intro u x g hu hus hx hg
  exact clean_growth_compatible_of_outputs E rho hset hOutputs hhor hWitness hu hus hx hg

end AvailableChain.FGSA.Run
end
