module
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceDefs
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingStep
public import AvailableChainFGSARun.Proofs.AncestorDeadlinesStore
public import AvailableChainFGSARun.Proofs.AC

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §8.2; O-INDUCT plan §5. Class (iii).
DC: INTENTIONAL; normalization retains B when its new finalized anchor
is compatible with B. It may discard a suffix strictly above B. -/
theorem outage_normalize_covers {F S B : Block} (hBS : Block.Preceq B S)
    (hFB : Block.Compatible F B) : Block.Preceq B (Gen.AC.normalizeOutput F S) := by
  rw [Gen.AC.normalizeOutput_def]
  split
  · exact hBS
  · next hn =>
    rcases Bool.or_eq_true_iff.mp hFB with h | h
    · exact (hn (block_preceq_trans h hBS)).elim
    · exact h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §8.2; O-INDUCT plan §5. Class (iii).
DC: INTENTIONAL; an accepted compatible gate result retains B in S. -/
theorem outage_advance_covers {S C B : Block} (hBS : Block.Preceq B S)
    (hCB : Block.Compatible C B) : Block.Preceq B (GridCO.advance S C) := by
  change Block.Preceq B (if Block.preceq C S then S else C)
  split
  · exact hBS
  · next hn =>
    rcases Bool.or_eq_true_iff.mp hCB with h | h
    · exact (hn (block_preceq_trans h hBS)).elim
    · exact h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §8.3; O-INDUCT plan §5 gate guard. Class (iii).
DC: INTENTIONAL; a passed gate result is compatible with B. The selected
B row is still present in the active view when F does not cover B. -/
theorem outage_passed_raw_compatible (p : Params) (st : State p.n) (hinv : CStoreInv p st)
    {B C : Block} {s : Slot}
    (hprotect : Block.Preceq B (eraseFG st.fg.F) ∨
      ∃ dl, (B, SA.releaseThreshold p.toParams, dl) ∈ st.base.obligations)
    (hraw : SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (FGSA.actView st) s = some C)
    (hguard : (FGSA.actView st).obligations.any (fun row => !Block.compatible row.1 C) = false) :
    Block.Compatible C B := by
  rcases hprotect with hBF | ⟨dl, hrow⟩
  · have hc := (compat_of_confirmation p st hinv hraw).1
    have hFC : Block.Compatible (eraseFG st.fg.F) C := by
      change Block.compatible (eraseFG st.fg.F) C = true
      rw [block_compatible_comm]
      exact hc
    have hBC := block_compatible_of_preceq_compatible hBF hFC
    change Block.compatible C B = true
    rw [block_compatible_comm]
    exact hBC
  · have hm : (B, SA.releaseThreshold p.toParams, dl) ∈ (FGSA.actView st).obligations := hrow
    have hn := List.any_eq_false.mp hguard _ hm
    have hBC : Block.compatible B C = true := by
      cases he : Block.compatible B C with
      | true => rfl
      | false => exact (hn (by rw [he]; rfl)).elim
    change Block.compatible C B = true
    rw [block_compatible_comm]
    exact hBC

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §8.2; O-INDUCT plan §5 max renewal. Class (iii).
DC: INTENTIONAL; every write retains the lower deadline bound, whether
the key is renewed or a different target is written. -/
theorem outage_writeKeys_keep {n : Nat} (keys : List (Block × Nat)) (lim lower : Time)
    (hlim : lower ≤ lim) (st : GridCO.State n .root) {B : Block} {g : Nat} {dl : Time}
    (hm : (B, g, dl) ∈ st.obligations) (hdl : lower ≤ dl) :
    ∃ dl', (B, g, dl') ∈ (GridCO.writeKeys st keys lim).obligations ∧ lower ≤ dl' := by
  induction keys generalizing st dl with
  | nil => exact ⟨dl, hm, hdl⟩
  | cons key keys ih =>
    have hstep : ∃ dl', (B, g, dl') ∈ (GridCO.writeObligation st key.1 key.2 lim).obligations ∧
        lower ≤ dl' := by
      by_cases hk : key.1 = B ∧ key.2 = g
      · obtain ⟨hB, hg⟩ := hk
        rw [hB, hg]
        obtain ⟨dl', hm', hd'⟩ := arming_write_row st B g lim
        exact ⟨dl', hm', hlim.trans hd'⟩
      · refine ⟨dl, List.mem_append_left _ (List.mem_filter.mpr ⟨hm, ?_⟩), hdl⟩
        change (!(B == key.1 && g == key.2)) = true
        cases he : (B == key.1 && g == key.2) with
        | false => rfl
        | true =>
          obtain ⟨hB, hg⟩ := Bool.and_eq_true_iff.mp he
          exact (hk ⟨(beq_iff_eq.mp hB).symm, (beq_iff_eq.mp hg).symm⟩).elim
    obtain ⟨dl', hm', hd'⟩ := hstep
    rw [@GridCO.writeKeys_def GridCO.slowLeasePolicy, List.foldl_cons,
      ← @GridCO.writeKeys_def GridCO.slowLeasePolicy]
    exact ih _ hm' hd'

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §8.2; O-INDUCT plan §5. Class (iii).
DC: INTENTIONAL; normalization changes neither F nor the selected row. -/
theorem outage_normalize_protection (p : Params) {B : Block} {j : Slot} (st : State p.n)
    (hp : OutageProtection p B j st) (hc : Block.Compatible (eraseFG st.fg.F) B) :
    OutageProtection p B j (FGSA.normalizeS st) := by
  rw [OutageProtection_def]
  rw [normalizeS_fields]
  refine ⟨?_, hp.2⟩
  exact outage_normalize_covers hp.1 hc

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §8.2–3; O-INDUCT plan §5 gate. Class (iii).
DC: INTENTIONAL; the whole-result guard prevents a conflicting write.
Max renewal retains the pending deadline, also on the slow arm. -/
theorem outage_gateStep_protection (p : Params) {B : Block} {j s : Slot} (st : State p.n)
    (hinv : CStoreInv p st) (hp : OutageProtection p B j st)
    (hc : Block.Compatible (eraseFG st.fg.F) B) (hjs : j ≤ s) :
    OutageProtection p B j (FGSA.gateStep p st s) := by
  let Q : State p.n := { FGSA.onView
    (fun v => SA.Root.gateFrom p.toParams (eraseFG st.fg.F) v s) st with
    fastWrite := st.fastWrite ++ [(s, FGSA.fastSet p (eraseFG st.fg.F) (FGSA.actView st) s)] }
  have hQ : OutageProtection p B j Q := by
    rw [OutageProtection_def]
    cases hraw : SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (FGSA.actView st) s with
    | none =>
      have he : SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (FGSA.actView st) s =
          { FGSA.actView st with
            genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy p.n .root (FGSA.actView st)
                s none } := by
        unfold SA.Root.gateFrom GridCO.gateFrom
        rw [show GridCO.confirmationFrom p.toParams.engine (eraseFG st.fg.F)
          (FGSA.actView st) s = none from hraw]
      change Block.Preceq B
        (SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (FGSA.actView st) s).stableRecord ∧
        (Block.Preceq B (eraseFG st.fg.F) ∨ ∃ dl,
          (B, SA.releaseThreshold p.toParams, dl) ∈
            (SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (FGSA.actView st) s).obligations ∧
          SA.gateTime p.toParams j + L p ≤ dl)
      rw [he]
      exact ⟨hp.1, hp.2⟩
    | some C =>
      cases hg : (FGSA.actView st).obligations.any (fun row => !Block.compatible row.1 C) with
      | true =>
        have he : SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (FGSA.actView st) s =
            { FGSA.actView st with
              goldfishRecord := GridCO.advance (FGSA.actView st).goldfishRecord C
              genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy p.n .root (FGSA.actView
                  st) s (some C) } := by
          unfold SA.Root.gateFrom GridCO.gateFrom
          rw [show GridCO.confirmationFrom p.toParams.engine (eraseFG st.fg.F)
            (FGSA.actView st) s = some C from hraw]
          change (if _ then _ else _) = _
          have hg' : (FGSA.actView st).obligations.any
              (fun (target, _, _) => !Block.compatible target C) = true := hg
          rw [hg']
          rfl
        change Block.Preceq B
          (SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (FGSA.actView st) s).stableRecord ∧
          (Block.Preceq B (eraseFG st.fg.F) ∨ ∃ dl,
            (B, SA.releaseThreshold p.toParams, dl) ∈
              (SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (FGSA.actView st) s).obligations ∧
            SA.gateTime p.toParams j + L p ≤ dl)
        rw [he]
        exact ⟨hp.1, hp.2⟩
      | false =>
        have hCB := outage_passed_raw_compatible p st hinv
          (hp.2.imp id (fun ⟨dl, hm, _⟩ => ⟨dl, hm⟩)) hraw hg
        have hw := gateFrom_eq_writeKeys_fgsa p.toParams
          (eraseFG st.fg.F) (FGSA.actView st) s C hraw hg
        constructor
        · change Block.Preceq B
            (SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (FGSA.actView st) s).stableRecord
          rw [hw, arming_writeKeys_stable]
          exact outage_advance_covers hp.1 hCB
        · change Block.Preceq B (eraseFG st.fg.F) ∨ ∃ dl,
            (B, SA.releaseThreshold p.toParams, dl) ∈
              (SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (FGSA.actView st) s).obligations ∧
            SA.gateTime p.toParams j + L p ≤ dl
          rcases hp.2 with hF | ⟨dl, hm, hd⟩
          · exact Or.inl hF
          · right
            rw [hw]
            refine outage_writeKeys_keep _ _ _ ?_ _ ?_ hd
            · change SA.gateTime p.toParams j + L p ≤ SA.gateTime p.toParams s + L p
              have hgate := (arming_gate_le_iff p j s).mpr hjs
              exact add_le_add hgate le_rfl
            · exact hm
  unfold FGSA.gateStep
  apply outage_normalize_protection
  · split
    · exact hp
    · split
      · exact ⟨hp.1, hp.2⟩
      · exact hQ
  · split
    · exact hc
    · split <;> exact hc

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

set_option maxHeartbeats 800000 in
-- Source and gate-read reductions need a larger elaboration limit.
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §8.3; O-INDUCT plan §5 FG action. Class (iii).
DC: INTENTIONAL; TSrc's passed gate is this action tick by tick uniqueness.
The source compatibility proof uses pre-gate protection, not successor
history. INLINE htsrc: sourceDiscipline_tSrc. -/
theorem outage_tick_source_compatible (hs : V2.D.ScheduleWellFormed E rho)
    (htsrc : TSrc p c E rho) {i : Nat} {x : V} {r : Nat} {C B : Block} {j : Slot}
    (hi : rho.events[i]? = some (.tick x (p.actionTime r))) (hx : x ∈ rho.honest)
    (hp : OutageProtection p B j
      (FGSA.clockPre p (storeAt p c E rho i x) (p.actionTime r)))
    (hC : actionSource p c E rho x r = some (some C)) : Block.Compatible C B := by
  obtain ⟨X, G, _, hXm, hG, hCG, _, k, hk, hpass⟩ := htsrc x r C hx hC
  have hki : k = i := fgsa_tick_unique E rho hs hk hi
  subst k
  obtain ⟨y, s, hEnabled, _, C', hraw, hguard⟩ := hpass
  have htick := hEnabled.1
  have hys := V2.Event.tick.inj (Option.some.inj (htick.symm.trans hi))
  have hyx : y = x := hys.1
  subst y
  have hsr : s = r * p.R := by
    exact Nat.le_antisymm ((arming_gate_le_iff p s (r * p.R)).mp hys.2.le)
      ((arming_gate_le_iff p (r * p.R) s).mp hys.2.symm.le)
  subst s
  have hGr := (arming_gateResult_tick hs hEnabled).trans (congrArg some hraw)
  have hGC : G = C' := Option.some.inj (Option.some.inj (hG.symm.trans hGr))
  have hCB := outage_passed_raw_compatible p _
    (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x) _)
    (hp.2.imp id (fun ⟨dl, hm, _⟩ => ⟨dl, hm⟩)) hraw hguard
  exact block_compatible_of_preceq_compatible (hGC ▸ hCG C hXm) hCB

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §8.2; O-INDUCT plan §5 duties. Class (iii).
DC: INTENTIONAL; every positive-slot HEAD extends its live root,
including an empty walked view. -/
theorem outage_head_of_root (p : Params) (st : State p.n) {B : Block} {s : Slot}
    (hroot : Block.Preceq B (FGSA.liveRoot p st)) (hs : s ≠ 0) :
    Block.Preceq B (FGSA.headVote p st s) := by
  unfold FGSA.headVote
  rw [ite_eq_right hs]
  exact block_preceq_trans hroot (liveRoot_preceq_headInTree p st _ _ _)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §8.2; O-INDUCT plan §6 step 7. Class (iii).
DC: INTENTIONAL; after the causal frame proof, reconciliation retains
the selected row or changes to the finalized-coverage branch. -/
theorem outage_delivery_protection {i : Nat} {x : V} {o : Obj p} {t : Time}
    (hi : rho.events[i]? = some (.deliver x o t)) {B : Block} {j : Slot}
    (hp : OutageProtection p B j (storeAt p c E rho i x))
    (hc : Block.Compatible (F_at p c E rho (i + 1) x) B) :
    OutageProtection p B j (storeAt p c E rho (i + 1) x) := by
  have hpost : storeAt p c E rho (i + 1) x =
      FGSA.process p (storeAt p c E rho i x) (toWire p o) := by
    change (V2.D.Run.stateBefore E rho (i + 1) x).st = _
    rw [V2.D.Run.stateBefore_succ E rho hi]
    simp only [V2.D.World.step, Function.update_self]
    rfl
  constructor
  · rcases fgsaAC_output_step E rho i x with he | ⟨s, hs⟩ |
        ⟨o', t', b, hd, _, _, hn⟩ | ⟨t', hr, _⟩
    · change S_at p c E rho (i + 1) x = S_at p c E rho i x at he
      change Block.Preceq B (S_at p c E rho (i + 1) x)
      rw [he]
      exact hp.1
    · rw [hi] at hs
      cases hs
    · change S_at p c E rho (i + 1) x =
        Gen.AC.normalizeOutput (F_at p c E rho (i + 1) x) (S_at p c E rho i x) at hn
      change Block.Preceq B (S_at p c E rho (i + 1) x)
      rw [hn]
      exact outage_normalize_covers hp.1 hc
    · rw [hi] at hr
      cases hr
  · rcases hp.2 with hF | ⟨dl, hm, hd⟩
    · left
      rw [hpost]
      exact block_preceq_trans hF (eraseFG_preceq (process_F_mono p _ _))
    · right
      refine ⟨dl, ?_, hd⟩
      rw [hpost]
      rcases arming_process_lease p (storeAt p c E rho i x) (toWire p o) with h | h
      · rw [h.1]
        exact hm
      · rw [h.1]
        apply List.mem_filter.mpr
        refine ⟨hm, ?_⟩
        change Block.compatible B
          (eraseFG (FGSA.process p (storeAt p c E rho i x) (toWire p o)).fg.F) = true
        rw [← hpost, block_compatible_comm]
        exact hc

end AvailableChain.FGSA.Run
end
