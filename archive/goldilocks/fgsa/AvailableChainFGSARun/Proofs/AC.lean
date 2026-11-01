module
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainFGSA.Proofs.ActView
public import AvailableChainFGSARun.Statements.AC

public section

namespace AvailableChain.FGSA.Run

private theorem ac_gate_ne_offset (p : Params) (s r : Slot) (k : Int)
    (hk : k = 3 ∨ k = 5) :
    SA.gateTime p.toParams s ≠ 4 * p.Δ * r + k * p.Δ := by
  intro he
  have hm : (4 * (s : Int) + 6) * p.Δ = (4 * (r : Int) + k) * p.Δ := by
    change 4 * p.Δ * s + 6 * p.Δ = _ at he
    nlinarith
  have hn : 4 * (s : Int) + 6 = 4 * (r : Int) + k :=
    mul_right_cancel₀ (ne_of_gt p.deltaPos) hm
  rcases hk with rfl | rfl <;> omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
At a gate, expiry runs. Only the early cache can differ from the Gen view. -/
theorem fgsa_clockPre_gateView (p : Params) (st : State p.n) (s : Slot) :
    { actView (clockPre p st (SA.gateTime p.toParams s)) with early := st.base.early } =
      SA.Root.expire { actView st with now := SA.gateTime p.toParams s }
        (SA.gateTime p.toParams s) := by
  let t := SA.gateTime p.toParams s
  have hf : (decide (0 ≤ t - 3 * p.Δ) &&
      t == SA.freezeTime p.toParams ((t - 3 * p.Δ) / (4 * p.Δ)).toNat) = false := by
    apply Bool.and_eq_false_iff.mpr
    exact Or.inr (beq_eq_false_iff_ne.mpr (ac_gate_ne_offset p s _ 3 (Or.inl rfl)))
  have hq : (decide (0 ≤ t - 5 * p.Δ) &&
      t == SA.releaseTime p.toParams ((t - 5 * p.Δ) / (4 * p.Δ)).toNat) = false := by
    apply Bool.and_eq_false_iff.mpr
    exact Or.inr (beq_eq_false_iff_ne.mpr (ac_gate_ne_offset p s _ 5 (Or.inr rfl)))
  change { actView (clockPre p st t) with early := st.base.early } = _
  rw [clockPre_eq]
  simp only [hf, hq, Bool.false_and, Bool.false_eq_true, ite_false]
  by_cases he : (decide (0 ≤ t - 2 * p.Δ) &&
      t == SA.earlyTime p.toParams ((t - 2 * p.Δ) / (4 * p.Δ)).toNat) = true
  · simp only [he, ite_true]
    rfl
  · simp only [he]
    rfl



variable {p : Params} {In : Type} {c : AppCodec In} {V : Type} [DecidableEq V]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The anchor is below the output at every event index. -/
theorem fgsaAC_anchor_le_output (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) :
    Block.Preceq ((fgsaAC E rho).anchor i x) ((fgsaAC E rho).output i x) :=
  nestOK_stateBefore E rho i x

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Every live lease of an honest node targets a prefix of its output. -/
theorem fgsaAC_lease_le_output (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) :
    Gen.AC.Duty.LeaseBelowOutput (fgsaAC E rho) := by
  intro i x hx lease hl ht
  exact leaseBelowOutput_honest E rho i x hx lease hl ht

private theorem ac_fold_stable {n : Nat} (bs : List Block) (levels : Block → List Nat)
    (d : Time) (v : GridCO.State n .root) :
    (bs.foldl (fun acc b => (levels b).foldl
      (fun acc g => GridCO.writeObligation acc b g d) acc) v).stableRecord = v.stableRecord := by
  induction bs generalizing v with
  | nil => rfl
  | cons b bs ih =>
    rw [List.foldl_cons, ih]
    generalize levels b = gs
    induction gs generalizing v with
    | nil => rfl
    | cons g gs ihg => rw [List.foldl_cons, ihg]; rfl

private theorem ac_fold_leases {n : Nat} (bs : List Block) (levels : Block → List Nat)
    (d : Time) (v w : GridCO.State n .root) (hv : v.obligations = w.obligations) :
    (bs.foldl (fun acc b => (levels b).foldl
      (fun acc g => GridCO.writeObligation acc b g d) acc) v).obligations =
    (bs.foldl (fun acc b => (levels b).foldl
      (fun acc g => GridCO.writeObligation acc b g d) acc) w).obligations := by
  induction bs generalizing v w with
  | nil => exact hv
  | cons b bs ih =>
    simp only [List.foldl_cons]
    apply ih
    generalize levels b = gs
    induction gs generalizing v w with
    | nil => exact hv
    | cons g gs ihg =>
      simp only [List.foldl_cons]
      apply ihg
      change v.obligations.filter _ ++ [(_, _, max _ _)] =
        w.obligations.filter _ ++ [(_, _, max _ _)]
      have hd : GridCO.deadlineOf v b g = GridCO.deadlineOf w b g := by
        change ((v.obligations.find? _).map _) = ((w.obligations.find? _).map _)
        rw [hv]
      rw [hv, hd]



private theorem ac_clock_gate (p : Params) (st : State p.n) (s : Slot) :
    clock p st (SA.gateTime p.toParams s) =
      gateStep p (clockPre p st (SA.gateTime p.toParams s)) s := by
  have hd : SA.gateTime p.toParams s - 6 * p.Δ = 4 * p.Δ * (s : Int) := by
    change 4 * p.Δ * s + 6 * p.Δ - 6 * p.Δ = _
    ring
  have hi : ((SA.gateTime p.toParams s - 6 * p.Δ) / (4 * p.Δ)).toNat = s := by
    rw [hd, Int.mul_ediv_cancel_left _ (by have := p.deltaPos; positivity)]
    exact Int.toNat_natCast s
  change (if _ then _ else _) = _
  rw [hi]
  have hn : 0 ≤ SA.gateTime p.toParams s - 6 * p.Δ := by
    rw [hd]; have := p.deltaPos; positivity
  simp only [hn, decide_true, BEq.rfl, Bool.and_self, ite_true]

private theorem ac_gate_expand (p : SA.Params) {n : Nat} (a : Block)
    (v : GridCO.State n .root) (s : Slot) :
    SA.Root.gateFrom p a v s =
      match SA.Root.confirmationFrom p a v s with
      | none => { v with genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .root v s none }
      | some h =>
        if v.obligations.any (fun row => !Block.compatible row.1 h) then
          { v with
            goldfishRecord := GridCO.advance v.goldfishRecord h
            genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .root v s (some h) }
        else
          (v.blocks.filter (fun b => b != .genesis && Block.preceq b h)).foldl
            (fun acc b => (@GridCO.admissionLevels GridCO.slowLeasePolicy p.engine n .root v s
                b).foldl
              (fun acc g => GridCO.writeObligation acc b g (SA.gateTime p s + SA.lifetime p)) acc)
            { v with
              goldfishRecord := GridCO.advance v.goldfishRecord h
              genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .root v s (some h)
              stableRecord := GridCO.advance v.stableRecord h } := rfl

private theorem ac_fast_expand (p : Params) (a : Block) (v : GridCO.State p.n .root) (s : Slot) :
    fastSet p a v s = match SA.Root.confirmationFrom p.toParams a v s with
      | none => []
      | some h => if v.obligations.any (fun row => !Block.compatible row.1 h) then [] else
          v.blocks.filter (fun b => b != .genesis && Block.preceq b h &&
            decide (SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams v s b)) := rfl

private theorem ac_veto_false {n : Nat} (v : GridCO.State n .root) (h : Block)
    (hh : ∀ row ∈ v.obligations, Block.Compatible row.1 h) :
    v.obligations.any (fun row => !Block.compatible row.1 h) = false := by
  apply List.any_eq_false.mpr
  intro row hr
  have h := hh row hr
  change Block.compatible row.1 _ = true at h
  simp only [h, Bool.not_true, Bool.false_eq_true, not_false_eq_true]

private theorem ac_veto_true {n : Nat} (v : GridCO.State n .root) (h : Block)
    (hh : ∃ row ∈ v.obligations, ¬ Block.Compatible row.1 h) :
    v.obligations.any (fun row => !Block.compatible row.1 h) = true := by
  obtain ⟨row, hr, hh⟩ := hh
  apply List.any_eq_true.mpr
  exact ⟨row, hr, by simpa only [Bool.not_eq_true', Bool.eq_false_iff, Block.Compatible] using hh⟩



private theorem ac_normalize_onView_stable {n : Nat} (st : State n)
    (f : GridCO.State n .root → GridCO.State n .root) (rows : List (Slot × List Block)) :
    (normalizeS { onView f st with fastWrite := rows }).base.stableRecord =
      Gen.AC.normalizeOutput (eraseFG st.fg.F) (f (actView st)).stableRecord := by
  rw [normalizeS_fields, Gen.AC.normalizeOutput_def]
  rfl

set_option maxHeartbeats 1600000 in
-- The gate proof compares nested store updates and two lease folds.
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Every gate tick satisfies the event-indexed gate law, including repeated ticks. -/
theorem fgsaAC_gate_write (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i s : Nat) (x : V)
    (hj : joinedNow p (clockPre p (V2.D.Run.stateBefore E rho i x).st
      (SA.gateTime p.toParams s)) = true) :
    Gen.AC.Duty.GateWriteSpec (fgsaAC E rho) i s x := by
  intro ht
  let st := (V2.D.Run.stateBefore E rho i x).st
  let pre := clockPre p st (SA.gateTime p.toParams s)
  let v := actView pre
  let w := (fgsaAC E rho).gateView i x s
  have hn : (V2.D.Run.stateBefore E rho (i + 1) x).st = gateStep p pre s := by
    rw [V2.D.Run.stateBefore_succ E rho ht]
    simp only [V2.D.World.step, Function.update_self]
    change (V2.D.tick E rho (V2.D.Run.stateBefore E rho i x) x
      (SA.gateTime p.toParams s)).1.st = _
    exact (tick_st (c := c) E rho (V2.D.Run.stateBefore E rho i x) x
      (SA.gateTime p.toParams s)).trans (ac_clock_gate p st s)
  have hv : { v with early := st.base.early } = w := fgsa_clockPre_gateView p st s
  have hfg : pre.fg = st.fg := clockPre_fg p st _
  have hS : pre.base.stableRecord = st.base.stableRecord := clockPre_stable p st _
  have hO : pre.base.obligations = w.obligations := by
    have h := congrArg GridCO.State.obligations hv
    exact h
  have hraw : SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) v s =
      (fgsaAC E rho).raw i s x := by
    rw [hfg]
    have h := congrArg (fun v => SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) v s) hv
    exact h
  have hlevels : @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine p.n .root v s =
      (fgsaAC E rho).gateLevels i x s := by
    have h := congrArg (fun v =>
      @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine p.n .root v s) hv
    exact h
  have hblocks : v.blocks = w.blocks := by
    have h := congrArg GridCO.State.blocks hv
    exact h
  have hfast : ∀ h, v.blocks.filter (fun b => b != .genesis && Block.preceq b h &&
      decide (SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams v s b)) =
      (fgsaAC E rho).gateFast i x s h := by
    intro h
    exact congrArg (fun v => v.blocks.filter (fun b => b != .genesis && Block.preceq b h &&
      decide (SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams v s b))) hv
  have hsav (r : Slot) : GridCO.savedGenuine pre.base r = (fgsaAC E rho).saved i x r := by
    change (pre.base.genuine.find? _).map _ = _
    rw [clockPre_genuine]
    rfl
  have hpost (r : Slot) : (fgsaAC E rho).saved (i + 1) x r =
      GridCO.savedGenuine (gateStep p pre s).base r := by
    change GridCO.savedGenuine (V2.D.Run.stateBefore E rho (i + 1) x).st.base r = _
    rw [hn]
  have hout : (fgsaAC E rho).output (i + 1) x = (gateStep p pre s).base.stableRecord :=
    congrArg (fun st => st.base.stableRecord) hn
  have hlease : (fgsaAC E rho).leases (i + 1) x = (gateStep p pre s).base.obligations :=
    congrArg (fun st => st.base.obligations) hn
  have hnorm : normalizeS pre = pre := by
    have hnest : Block.preceq (eraseFG pre.fg.F) pre.base.stableRecord = true := by
      rw [hfg, hS]
      exact nestOK_stateBefore E rho i x
    exact ite_eq_left hnest
  refine ⟨rfl, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · change eraseFG (V2.D.Run.stateBefore E rho (i + 1) x).st.fg.F = _
    rw [hn, gateStep_fg, hfg]
    rfl
  · intro r hr
    rw [hpost]
    cases hs : GridCO.savedGenuine pre.base s with
    | none => exact (gateStep_other p pre s r hr).trans (hsav r)
    | some result =>
      rw [gateStep_saved p pre s (by rw [hs]; rfl), hnorm]
      exact hsav r
  · intro result hs
    rw [hpost, gateStep_saved p pre s (by rw [hsav, hs]; rfl), hnorm, hsav]
    exact hs
  · intro hs
    rw [hpost, (gateStep_fresh p pre s ((hsav s).trans hs) hj).1, hraw]
  · cases hs : GridCO.savedGenuine pre.base s with
    | some result =>
      left
      refine ⟨⟨result, (hsav s).symm.trans hs⟩, ?_, ?_, ?_⟩
      · rw [hout, gateStep_saved p pre s (by rw [hs]; rfl), hnorm, hS]
        rfl
      · rw [hlease, gateStep_saved p pre s (by rw [hs]; rfl), hnorm]
        exact hO
      · change (if (GridCO.savedGenuine pre.base s).isSome then _ else _) = _
        rw [hs]
        rfl
    | none =>
      right
      have hgate : gateStep p pre s = normalizeS
          { onView (fun v => SA.Root.gateFrom p.toParams (eraseFG pre.fg.F) v s) pre with
            fastWrite := pre.fastWrite ++ [(s, fastSet p (eraseFG pre.fg.F) v s)] } := by
        unfold gateStep
        simp only [hs, Option.isSome_none, Bool.false_eq_true, ite_false,
          show joinedNow p pre = true from hj, Bool.not_true]
        rfl
      have hfastread : (fgsaAC E rho).fast i s x = fastSet p (eraseFG pre.fg.F) v s := by
        change (if (GridCO.savedGenuine pre.base s).isSome then _ else _) = _
        rw [hs]
        rfl
      have houtput : (fgsaAC E rho).output (i + 1) x =
          Gen.AC.normalizeOutput (eraseFG st.fg.F)
            (SA.Root.gateFrom p.toParams (eraseFG pre.fg.F) v s).stableRecord := by
        rw [hout, hgate, ac_normalize_onView_stable, hfg]
      have hleases : (fgsaAC E rho).leases (i + 1) x =
          (SA.Root.gateFrom p.toParams (eraseFG pre.fg.F) v s).obligations := by
        rw [hlease, hgate, normalizeS_fields]
        rfl
      have hnormS : Gen.AC.normalizeOutput (eraseFG st.fg.F) v.stableRecord =
          (fgsaAC E rho).output i x := by
        change Gen.AC.normalizeOutput (eraseFG st.fg.F) pre.base.stableRecord = _
        rw [hS]
        exact ite_eq_left (show Block.preceq (eraseFG st.fg.F) st.base.stableRecord = true
          from nestOK_stateBefore E rho i x)
      constructor
      · intro hr
        have hr' := hraw.trans hr
        rw [houtput, hleases, hfastread, ac_gate_expand, ac_fast_expand, hr']
        exact ⟨hnormS, hO, rfl⟩
      · intro h hr hh
        have hr' := hraw.trans hr
        have hveto : v.obligations.any (fun row => !Block.compatible row.1 h) = true := by
          apply ac_veto_true
          change ∃ row ∈ pre.base.obligations, ¬ Block.Compatible row.1 h
          rw [hO]
          exact hh
        rw [houtput, hleases, hfastread, ac_gate_expand, ac_fast_expand, hr']
        simp only [hveto, ite_true]
        exact ⟨hnormS, hO, trivial⟩
      · intro h hr hh
        have hr' := hraw.trans hr
        have hveto : v.obligations.any (fun row => !Block.compatible row.1 h) = false := by
          apply ac_veto_false
          change ∀ row ∈ pre.base.obligations, Block.Compatible row.1 h
          rw [hO]
          exact hh
        rw [houtput, hleases, hfastread, ac_gate_expand, ac_fast_expand, hr']
        simp only [hveto, Bool.false_eq_true, ite_false]
        refine ⟨?_, ?_, hfast h⟩
        · rw [ac_fold_stable]
          change Gen.AC.normalizeOutput _ (GridCO.advance pre.base.stableRecord h) = _
          rw [hS]
          rfl
        · rw [hblocks, hlevels]
          exact ac_fold_leases _ _ _ _ w hO



private theorem ac_block_output (p : Params) (st : State p.n) (hst : NestOK st)
    (s : Slot) (N : NamedProposal p.n) :
    (admitBlock p st s N).base.stableRecord = st.base.stableRecord ∨
      (eraseFG (admitBlock p st s N).fg.F ≠ eraseFG st.fg.F ∧
        (admitBlock p st s N).base.stableRecord =
          Gen.AC.normalizeOutput (eraseFG (admitBlock p st s N).fg.F)
            st.base.stableRecord) := by
  cases hn : namedParentHeld st N with
  | false =>
    rw [admitBlock_refused p st s N (Or.inl hn)]
    exact Or.inl rfl
  | true =>
    cases hp : parentFG st N.erase with
    | none =>
      rw [admitBlock_refused p st s N (Or.inr (Or.inl hp))]
      exact Or.inl rfl
    | some P =>
      cases ha : blockAccepted p st s N P with
      | false =>
        rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hp, ha⟩))]
        exact Or.inl rfl
      | true =>
        obtain ⟨pool, he, -⟩ := admitBlock_accepted_eq p st s N P hn hp ha
        let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
          fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
        change admitBlock p st s N =
          { (if st1.fg.F = st.fg.F then st1 else reconcile st1) with rowPool := pool } at he
        have hs1 : st1.base.stableRecord = st.base.stableRecord :=
          admitProposal_stable p.toParams.engine st.base _ N.erase _
        rw [he]
        by_cases hf : st1.fg.F = st.fg.F
        · rw [ite_eq_left hf]
          exact Or.inl hs1
        · rw [ite_eq_right hf]
          have ho : (reconcile st1).base.stableRecord =
              Gen.AC.normalizeOutput (eraseFG st1.fg.F) st.base.stableRecord := by
            change (normalizeS _).base.stableRecord = _
            rw [normalizeS_fields]
            change (if Block.preceq (eraseFG st1.fg.F) st1.base.stableRecord then _ else _) = _
            rw [hs1]
            rfl
          change (reconcile st1).base.stableRecord = _ ∨
            (eraseFG (reconcile st1).fg.F ≠ _ ∧ (reconcile st1).base.stableRecord = _)
          rw [reconcile_fg]
          by_cases heq : eraseFG st1.fg.F = eraseFG st.fg.F
          · left
            rw [ho, heq]
            exact ite_eq_left hst
          · exact Or.inr ⟨heq, ho⟩

private theorem ac_process_output (p : Params) (st : State p.n) (hst : NestOK st)
    (o : Obj p) :
    (FGSA.process p st (toWire p o)).base.stableRecord = st.base.stableRecord ∨
      (∃ b, (fgsaInterface p c).block o.payload = some b ∧
        eraseFG (FGSA.process p st (toWire p o)).fg.F ≠ eraseFG st.fg.F ∧
        (FGSA.process p st (toWire p o)).base.stableRecord =
          Gen.AC.normalizeOutput (eraseFG (FGSA.process p st (toWire p o)).fg.F)
            st.base.stableRecord) := by
  obtain ⟨auth, msg⟩ := o
  cases auth with
  | none => cases msg <;> exact Or.inl rfl
  | seat label seat =>
    cases label with
    | prop s =>
      cases msg with
      | head b => exact Or.inl rfl
      | row body => exact Or.inl rfl
      | proposal N =>
        rcases ac_block_output p st hst s N with he | he
        · exact Or.inl he
        · exact Or.inr ⟨N.erase, rfl, he⟩
    | base label =>
      cases label with
      | head s =>
        cases msg with
        | head b => exact Or.inl (admitHead_base_stable p st s seat b)
        | proposal N => exact Or.inl rfl
        | row body => exact Or.inl rfl
      | fg =>
        cases msg with
        | head b => exact Or.inl rfl
        | proposal N => exact Or.inl rfl
        | row body =>
          change (admitRow p st _).base.stableRecord = _ ∨ _
          rcases admitRow_eq p st _ with he | he <;> rw [he] <;> exact Or.inl rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
An output change is a gate, reconciliation, or restart. No event order is needed. -/
theorem fgsaAC_output_step (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) :
    (fgsaAC E rho).output (i + 1) x = (fgsaAC E rho).output i x ∨
      Gen.AC.Duty.GateWrite (fgsaAC E rho) i x ∨ Gen.AC.Duty.Reconcile (fgsaAC E rho) i x ∨
      (∃ t, rho.events[i]? = some (.restart x t) ∧
        (fgsaAC E rho).output (i + 1) x = (fgsaAC E rho).output 0 x) := by
  cases he : rho.events[i]? with
  | none =>
    left
    change (V2.D.Run.stateBefore E rho (i + 1) x).st.base.stableRecord = _
    simp only [V2.D.Run.stateBefore, List.take_add_one, he, Option.toList_none, List.append_nil]
    rfl
  | some e =>
    by_cases hx : e.node = x
    · cases e with
      | restart y t =>
        change y = x at hx
        subst y
        left
        change (V2.D.Run.stateBefore E rho (i + 1) x).st.base.stableRecord = _
        rw [V2.D.Run.stateBefore_succ E rho he]
        simp only [V2.D.World.step, Function.update_self]
        exact acRestart_stableRecord p _ t
      | tick y t =>
        change y = x at hx
        subst y
        by_cases hg : ∃ s, t = SA.gateTime p.toParams s
        · obtain ⟨s, rfl⟩ := hg
          exact Or.inr (Or.inl ⟨s, he⟩)
        · left
          have hc : clock p (V2.D.Run.stateBefore E rho i x).st t =
              clockPre p (V2.D.Run.stateBefore E rho i x).st t := by
            change (if _ then _ else _) = _
            apply ite_eq_right
            intro hh
            have ht := (Bool.and_eq_true_iff.mp hh).2
            exact hg ⟨_, beq_iff_eq.mp ht⟩
          change (V2.D.Run.stateBefore E rho (i + 1) x).st.base.stableRecord = _
          rw [V2.D.Run.stateBefore_succ E rho he]
          simp only [V2.D.World.step, Function.update_self]
          have hn := tick_st (c := c) E rho (V2.D.Run.stateBefore E rho i x) x t
          have ho := congrArg (fun st => st.base.stableRecord) hn
          exact ho.trans (hc ▸ clockPre_stable p (V2.D.Run.stateBefore E rho i x).st t)
      | deliver y o t =>
        change y = x at hx
        subst y
        have hn : (V2.D.Run.stateBefore E rho (i + 1) x).st =
            FGSA.process p (V2.D.Run.stateBefore E rho i x).st (toWire p o) := by
          rw [V2.D.Run.stateBefore_succ E rho he]
          simp only [V2.D.World.step, Function.update_self]
          rfl
        rcases ac_process_output (c := c) p (V2.D.Run.stateBefore E rho i x).st
          (nestOK_stateBefore E rho i x) o with ho | ⟨b, hb, ha, ho⟩
        · left
          change (V2.D.Run.stateBefore E rho (i + 1) x).st.base.stableRecord = _
          rw [hn]
          exact ho
        · right; right; left
          refine ⟨o, t, b, he, hb, ?_, ?_⟩
          · change eraseFG (V2.D.Run.stateBefore E rho (i + 1) x).st.fg.F ≠ _
            rw [hn]
            exact ha
          · change (V2.D.Run.stateBefore E rho (i + 1) x).st.base.stableRecord =
              Gen.AC.normalizeOutput (eraseFG (V2.D.Run.stateBefore E rho (i + 1) x).st.fg.F) _
            rw [hn]
            exact ho
    · left
      change (V2.D.Run.stateBefore E rho (i + 1) x).st.base.stableRecord = _
      rw [V2.D.Run.stateBefore_succ E rho he, V2.D.World.step_apply_of_node_ne E rho _ hx]
      rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FG-SA satisfies all AC laws on every run, including restarts. -/
theorem fgsaAC_laws (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hjoin : ∀ i s x, rho.events[i]? = some (.tick x (SA.gateTime p.toParams s)) →
      joinedNow p (clockPre p (V2.D.Run.stateBefore E rho i x).st
        (SA.gateTime p.toParams s)) = true) :
    Gen.AC.Duty.ACLaws (fgsaAC E rho) where
  anchor_le_output := fgsaAC_anchor_le_output E rho
  lease_le_output := fgsaAC_lease_le_output E rho
  output_step := fgsaAC_output_step E rho
  gate_write := fun i s x ht => fgsaAC_gate_write E rho i s x (hjoin i s x ht) ht



private theorem ac_gate_reindex {In V : Type} {P : V2.ProtocolSpecD In}
    {E : Generic.Env V} {rho : V2.D.Run V P} (A : Gen.AC.Duty.ACReads E rho .root)
    (raw : Slot → V → Option Block) (fast : Slot → V → List Block)
    (i s : Nat) (x : V) (hr : A.raw i s x = raw s x) (hf : A.fast i s x = fast s x)
    (h : Gen.AC.Duty.GateWriteAtSpec A i s x) :
    Gen.AC.Duty.GateWriteAtSpec
      ({ A with raw := fun _ => raw, fast := fun _ => fast } : Gen.AC.Duty.ACReads E rho .root)
      i s x := by
  refine ⟨h.view_output, h.view_leases, h.view_now, h.anchor_eq, ?_, h.saved_other,
    h.saved, ?_, ?_⟩
  · exact hr.symm.trans h.raw_eq
  · intro hn
    exact (h.fresh hn).trans (congrArg some hr)
  · rcases h.effects with hskip | hrun
    · left
      exact ⟨hskip.1, hskip.2.1, hskip.2.2.1, hf.symm.trans hskip.2.2.2⟩
    · right
      constructor
      · intro hn
        obtain ⟨ho, hl, hh⟩ := hrun.empty (hr.trans hn)
        exact ⟨ho, hl, hf.symm.trans hh⟩
      · intro b hb hv
        obtain ⟨ho, hl, hh⟩ := hrun.veto b (hr.trans hb) hv
        exact ⟨ho, hl, hf.symm.trans hh⟩
      · intro b hb hv
        obtain ⟨ho, hl, hh⟩ := hrun.accept b (hr.trans hb) hv
        exact ⟨ho, hl, hf.symm.trans hh⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Under schedule uniqueness, the gate observations also have slot-only reads.
This separate statement adds no schedule premise to `fgsaAC_laws`. -/
theorem fgsaAC_slot_gate_reads (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    (hjoin : ∀ i s x, rho.events[i]? = some (.tick x (SA.gateTime p.toParams s)) →
      joinedNow p (clockPre p (V2.D.Run.stateBefore E rho i x).st
        (SA.gateTime p.toParams s)) = true) :
    ∃ (raw : Slot → V → Option Block) (fast : Slot → V → List Block),
      ∀ i s x, rho.events[i]? = some (.tick x (SA.gateTime p.toParams s)) →
        (fgsaAC E rho).raw i s x = raw s x ∧ (fgsaAC E rho).fast i s x = fast s x ∧
          Gen.AC.Duty.GateWriteAtSpec
            ({ fgsaAC E rho with raw := fun _ => raw, fast := fun _ => fast } :
              Gen.AC.Duty.ACReads E rho .root) i s x := by
  let index := fun s x => rho.events.idxOf (.tick x (SA.gateTime p.toParams s))
  let raw := fun s x => (fgsaAC E rho).raw (index s x) s x
  let fast := fun s x => (fgsaAC E rho).fast (index s x) s x
  refine ⟨raw, fast, ?_⟩
  intro i s x ht
  have hi : index s x = i := by
    obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp ht
    change rho.events.idxOf _ = i
    rw [← he]
    exact hs.nodup.idxOf_getElem i hlt
  have hr : (fgsaAC E rho).raw i s x = raw s x := by dsimp only [raw]; rw [hi]
  have hf : (fgsaAC E rho).fast i s x = fast s x := by dsimp only [fast]; rw [hi]
  refine ⟨hr, hf, ?_⟩
  have h := fgsaAC_gate_write E rho i s x (hjoin i s x ht) ht
  exact ac_gate_reindex (fgsaAC E rho) raw fast i s x hr hf h

end AvailableChain.FGSA.Run
end
