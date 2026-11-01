module
public import AvailableChainFGSAProofs.Proofs.Healing.SupportWrite
public import AvailableChainFGSAProofs.Proofs.Shared.Gate

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem opening_clock_gate_eq (st : State p.n) (s : Slot) :
    FGSA.clock p st (SA.gateTime p.toParams s) =
      gateStep p (clockPre p st (SA.gateTime p.toParams s)) s := by
  have hDelta : (0 : Int) < p.Δ := p.deltaPos
  have ht : SA.gateTime p.toParams s - 6 * p.Δ = 4 * p.Δ * (s : Int) := by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ - 6 * p.Δ = _
    ring
  have hslot : ((SA.gateTime p.toParams s - 6 * p.Δ) / (4 * p.Δ)).toNat = s := by
    rw [ht, Int.mul_ediv_cancel_left _ (by positivity), Int.toNat_natCast]
  have hg : 0 ≤ SA.gateTime p.toParams s - 6 * p.Δ := by rw [ht]; positivity
  unfold FGSA.clock
  dsimp only
  rw [hslot]
  simp only [hg, decide_true, beq_self_eq_true, Bool.true_and, ite_true]

/-- A nonempty fast write at a scheduled gate supplies its exact join guard. -/
theorem healing_fastWrite_joined (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {j : Nat} {y : V} {w : Slot} {B : Block}
    (ht : IsGateTick p c rho j y w)
    (hB : B ∈ (fastWriteAt ((fgsa p c).clock (V2.D.Run.stateBefore E rho j y)
      (SA.gateTime p.toParams w)).st w).getD []) :
    joinedAtTime p (storeAt p c E rho j y).restartTime
      (SA.gateTime p.toParams w) = true := by
  let st := (FGSA.clock p (storeAt p c E rho j y) (SA.gateTime p.toParams w))
  cases hj : joinedAtTime p (storeAt p c E rho j y).restartTime
      (SA.gateTime p.toParams w) with
  | true => rfl
  | false =>
    have hnew : GridCO.savedGenuine
        (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w)).base w = none := by
      unfold GridCO.savedGenuine
      rw [clockPre_genuine]
      exact fgsa_gate_fresh E rho hs ht
    have hfw : st.fastWrite = (storeAt p c E rho j y).fastWrite ++ [(w, [])] := by
      dsimp only [st]
      rw [opening_clock_gate_eq]
      rw [(gateStep_unjoined p _ w hnew (by rwa [clockPre_joined])).2.1]
      rw [clockPre_fastWrite]
    have hrow : (w, []) ∈ st.fastWrite := by
      rw [hfw]
      exact List.mem_append_right _ (List.mem_cons_self ..)
    have hinv := (storeBundle_postClock E rho j y (SA.gateTime p.toParams w)).cstore
    have hfind : st.fastWrite.find? (fun row => row.1 == w) = some (w, []) := by
      cases he : st.fastWrite.find? (fun row => row.1 == w) with
      | none => have hn := List.find?_eq_none.mp he _ hrow; simp at hn
      | some row =>
        have hk : row.1 = w := by simpa using List.find?_some he
        exact congrArg some (List.inj_on_of_nodup_map hinv.fastDom.1
          (List.mem_of_find?_eq_some he) hrow hk)
    change B ∈ ((st.fastWrite.find? (fun row => row.1 == w)).map Prod.snd).getD [] at hB
    rw [hfind] at hB
    exact absurd hB List.not_mem_nil

/-- A nonempty scheduled fast write enables the matching gate construction. -/
theorem healing_enabledGate_of_fastWrite (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hs : V2.D.ScheduleWellFormed E rho)
    {j : Nat} {y : V} {w : Slot} {B : Block} (ht : IsGateTick p c rho j y w)
    (hB : B ∈ (fastWriteAt ((fgsa p c).clock (V2.D.Run.stateBefore E rho j y)
      (SA.gateTime p.toParams w)).st w).getD []) :
    enabledGateAt p c E rho j y w := by
  have hj := healing_fastWrite_joined E rho hs ht hB
  have hslot : p.slotOf (SA.gateTime p.toParams w) = w + 1 :=
    (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho j y) _).2.symm.trans
      (fgsa_gate_slot (c := c) _ w)
  refine ⟨ht, ?_⟩
  unfold joinedAtTime at hj
  cases hr : (storeAt p c E rho j y).restartTime with
  | none => trivial
  | some t =>
    rw [hr, hslot] at hj
    change t ≤ 4 * p.Δ * (w : Int)
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using of_decide_eq_true hj

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 01 §6.6, §7; plan H-GATE §3C (lease origins before q).
DC: SAME the raw result of an honest gate of label w is a stored block of slot at most
w + 1 at that gate. -/
theorem opening_result_slot (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {j : Nat} {y : V} {w : Slot} {B : Block}
    (ht : IsGateTick p c rho j y w) (hres : gateResultAt p c E rho j = some (some B)) :
    B ∈ (storeAt p c E rho j y).base.blocks ∧ B.slot ≤ w + 1 := by
  have hgr : gateResult p c E rho y w = some (some B) :=
    (gateResultAt_eq_gateResult p c E rho hs ht).symm.trans hres
  have hconf := (fgsa_gate_raw_of_nonempty p c E rho hs ht hgr).2
  have hm : B ∈ (storeAt p c E rho j y).base.blocks := by
    have h := (compat_of_confirmation p _ (cstoreInv_clockPre p _
      (cstoreInv_stateBefore E rho j y) _) hconf).2
    rwa [(clockPre_fields p _ _).2.1] at h
  refine ⟨hm, ?_⟩
  have hb := (fgsa_stateBefore_bounds E rho hs j y).1 B hm
  have hn := fgsa_preTick_now_le E rho hs ht
  have hsl := Internal.slotOf_mono (p := p) hn
  have he : p.slotOf (SA.gateTime p.toParams w) = w + 1 :=
    (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho j y) _).2.symm.trans
      (fgsa_gate_slot (c := c) _ w)
  exact hb.trans (hsl.trans_eq he)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Spec 892–906 (fast-write set); plan H-GATE §3B (q = rR).
DC: SAME a member of the fast set saved at an honest gate tick is a non-genesis active
prefix of the passed raw result, with release-threshold support in the gate view. -/
theorem opening_fastWrite_spec (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {j : Nat} {y : V} {w : Slot}
    (ht : IsGateTick p c rho j y w) {B : Block}
    (hB : B ∈ (fastWriteAt ((fgsa p c).clock (V2.D.Run.stateBefore E rho j y)
      (SA.gateTime p.toParams w)).st w).getD []) :
    ∃ h, SA.Root.confirmationFrom p.toParams (eraseFG (storeAt p c E rho j y).fg.F)
        (actView (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w))) w = some h ∧
      (actView (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w))).obligations.any
        (fun row => !Block.compatible row.1 h) = false ∧
      B ∈ (actView (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w))).blocks ∧
      B ≠ .genesis ∧ Block.Preceq B h ∧
      SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams
        (actView (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w))) w B := by
  have hjoined := healing_fastWrite_joined E rho hs ht hB
  rw [healing_support_fastWrite p c E rho hs ht hjoined] at hB
  unfold fastSet at hB
  cases hconf : SA.Root.confirmationFrom p.toParams (eraseFG (storeAt p c E rho j y).fg.F)
      (actView (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w))) w with
  | none => rw [hconf] at hB; exact absurd hB List.not_mem_nil
  | some h =>
    rw [hconf] at hB
    dsimp only at hB
    split at hB
    · exact absurd hB List.not_mem_nil
    · rename_i hg
      obtain ⟨hmem, hb⟩ := List.mem_filter.mp hB
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hb
      obtain ⟨⟨hne, hBh⟩, hτ⟩ := hb
      exact ⟨h, rfl, Bool.eq_false_iff.mpr hg, hmem, hne, hBh, hτ⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Spec 899–921 (admission levels); plan H-GATE §3C.
DC: SAME release-threshold support in the gate view admits the single SA lease level. -/
theorem opening_gate_level (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) (s : Slot) (B : Block)
    (hsupport : SA.releaseThreshold p.toParams ≤
      SA.Root.prefixSupport p.toParams ((fgsaAC E rho).gateView i x s) s B) :
    SA.releaseThreshold p.toParams ∈ (fgsaAC E rho).gateLevels i x s B := by
  change SA.releaseThreshold p.toParams ∈
    @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine p.n .root ((fgsaAC E
        rho).gateView i x s) s B
  change SA.releaseThreshold p.toParams ∈
    (if decide (SA.releaseThreshold p.toParams ≤
        SA.Root.prefixSupport p.toParams ((fgsaAC E rho).gateView i x s) s B) ||
      GridCO.slowEligible p.toParams.engine ((fgsaAC E rho).gateView i x s) s B
      then [SA.releaseThreshold p.toParams] else [])
  simp only [hsupport, decide_true, Bool.true_or, ite_true, List.mem_singleton]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Spec 892–921; blueprint 21 H.22 H3; plan H-GATE §3B (q = rR adapter).
DC: INTENTIONAL the reverse of `exactService_fastWrite_of_gateService`: a member of the fast
set saved at an honest gate tick has GateService at that tick. The fast set is nonempty
only after a passed guard; its members carry the lease level. -/
theorem opening_gateService_of_fastWrite (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {s : Slot}
    (ht : IsGateTick p c rho i x s) {B : Block}
    (hB : B ∈ (fastWriteAt ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
      (SA.gateTime p.toParams s)).st s).getD []) :
    Gen.AC.Duty.GateService (fgsaAC E rho) i s x B := by
  obtain ⟨h, hconf, hguard, hmem, hne, hBh, hτ⟩ := opening_fastWrite_spec E rho hs ht hB
  have hv : { actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) with
      early := (storeAt p c E rho i x).base.early } = (fgsaAC E rho).gateView i x s :=
    fgsa_clockPre_gateView p (storeAt p c E rho i x) s
  have hraw : (fgsaAC E rho).raw i s x = some h := by
    have he := congrArg (fun u => SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho i x).fg.F) u s) hv
    have he' : (fgsaAC E rho).raw i s x = SA.Root.confirmationFrom p.toParams
        (eraseFG (storeAt p c E rho i x).fg.F)
        (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s := he.symm
    exact he'.trans hconf
  have hsupport : SA.releaseThreshold p.toParams ≤
      SA.Root.prefixSupport p.toParams ((fgsaAC E rho).gateView i x s) s B := by
    have he := congrArg (fun u => SA.Root.prefixSupport p.toParams u s B) hv
    exact he ▸ hτ
  have hmemw : B ∈ ((fgsaAC E rho).gateView i x s).blocks :=
    (congrArg GridCO.State.blocks hv) ▸ hmem
  refine fgsa_gate_of_coveringBatch E rho hs i s x B ht
    (healing_enabledGate_of_fastWrite E rho hs ht hB) ⟨h, hraw, hBh⟩ ?_ hne hmemw hsupport
    (opening_gate_level E rho i x s B hsupport)
  intro C hC lease hl
  have heq := Option.some.inj (hraw.symm.trans hC)
  subst heq
  rw [← hv] at hl
  have hno := List.any_eq_false.mp hguard lease hl
  change Block.compatible lease.1 h = true
  cases hcb : Block.compatible lease.1 h with
  | true => rfl
  | false => exact absurd (by rw [hcb]; rfl) hno

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:628–650 (H.4 fast body); plan H-GATE §3C (fast lease write).
DC: SAME the fast arm of `healing_support_phaseBody_of_write`. A fast write key needs no
synchronous window. -/
theorem opening_phaseBody_of_fast_key (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    {j : Nat} {x : V} {w : Slot} {C B : Block} {g : Nat} (hx : x ∈ rho.honest)
    (ht : IsGateTick p c rho j x w) (hpass : gatePassedAt p c E rho j)
    (hres : gateResultAt p c E rho j = some (some C))
    (hkey : (B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams w))) w C)
    (hfast : SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams
      (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams w))) w B) :
    PhaseBody p c E rho w B := by
  obtain ⟨hmem, hne, hBC, _, _⟩ := healing_support_key_cases p hkey
  obtain ⟨hin, hpost⟩ := healing_support_gate_reads p c E rho hs ht
  have hgr : gateResult p c E rho x w = some (some C) :=
    (gateResultAt_eq_gateResult p c E rho hs ht).symm.trans hres
  obtain ⟨hjoined, hconf⟩ := fgsa_gate_raw_of_nonempty p c E rho hs ht hgr
  change SA.Root.confirmationFrom p.toParams
    (eraseFG (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams w)).fg.F)
    (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams w))) w = some C at hconf
  refine ⟨x, hx, Or.inl ⟨_, hpost, ?_⟩⟩
  rw [healing_support_fastWrite p c E rho hs ht hjoined]
  have hF : eraseFG (storeAt p c E rho j x).fg.F =
      eraseFG (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams w)).fg.F := by
    rw [clockPre_fg]
  obtain ⟨x', w', ⟨ht', _⟩, _, h, hh, hguard⟩ := hpass
  obtain ⟨hxx, hw⟩ : x' = x ∧ SA.gateTime p.toParams w' = SA.gateTime p.toParams w := by
    have he := ht'.symm.trans ht
    simp only [Option.some.injEq, V2.Event.tick.injEq] at he
    exact he
  subst hxx
  have hww : w' = w := by
    change 4 * p.Δ * (w' : Int) + 6 * p.Δ = 4 * p.Δ * (w : Int) + 6 * p.Δ at hw
    have hd := p.deltaPos
    have he : (w' : Int) = w := by nlinarith
    exact_mod_cast he
  subst w'
  have hhC : h = C := Option.some.inj (hh.symm.trans hconf)
  subst h
  unfold fastSet
  rw [hF, hconf]
  dsimp only
  simp only [hguard, Bool.false_eq_true, ↓reduceIte]
  refine List.mem_filter.mpr ⟨hmem, ?_⟩
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
  exact ⟨⟨hne, hBC⟩, hfast⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.22:3109–3114 (exact service), 00:516–527 (store); plan H-GATE §3B, §3D.
DC: SAME the exact gate service of Q at q stores Q at every honest gate tick of q, and the
store is cumulative, so every later honest read holds Qfg. -/
theorem opening_exact_stored (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    {q : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)} (hQfg : eraseFG Qfg = Q)
    {jq : Nat} {x : V} (hjq : IsGateTick p c rho jq x q)
    (hQw : Q ∈ (fastWriteAt ((fgsa p c).clock (V2.D.Run.stateBefore E rho jq x)
      (SA.gateTime p.toParams q)).st q).getD [])
    {i : Nat} (hji : jq ≤ i) :
    Q ∈ (storeAt p c E rho i x).base.blocks ∧ Qfg ∈ (storeAt p c E rho i x).fg.TF ∧
      Q ≠ .genesis := by
  obtain ⟨_, _, _, hmem, hne, _, _⟩ := opening_fastWrite_spec E rho hs hjq hQw
  have hb0 : Q ∈ (storeAt p c E rho jq x).base.blocks := by
    have h := ((actView_blocks _ Q).mp hmem).1
    rwa [(clockPre_fields p _ _).2.1] at h
  have hb : Q ∈ (storeAt p c E rho i x).base.blocks :=
    (fgsa_store_durable p c E rho hji x).2.1.subset hb0
  obtain ⟨B, hB, heB⟩ := ((cstoreInv_stateBefore E rho i x).baseTree Q).mp hb
  have he : B = Qfg := eraseFG_injective (heB.trans hQfg.symm)
  subst he
  exact ⟨hb, hB, hne⟩

end AvailableChain.FGSA.Run
end
