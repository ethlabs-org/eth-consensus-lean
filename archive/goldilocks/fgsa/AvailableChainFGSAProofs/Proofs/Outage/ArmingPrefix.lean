module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingStep
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingHistory
public import AvailableChainFGSAProofs.Proofs.Shared.Channels

public section

/-! Plan O-ARM §4 fields 4, 5 and 7 (output and F clauses), §6.2 steps 3 and
5. Every actual action strictly before the pending gate reads a gate of label
at most `l`. Its source and named entry are below the comparison maximum `D`.
`cpPrefix_of_srcFrame` then bounds F, J, Z and the floor of every honest store
up to the strict pending read. Leases and S stay below `D` on that interval. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- ROOT-DIGEST W2b. Plan O-ARM §2. Class (iii). DC: INTENTIONAL; the FG lift of an erased
order, with a two-block view (root injectivity holds on every view). -/
theorem arming_lift {n : Nat} {A B : FGBlock (Fin n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

/-- Plan O-ARM §4 field 4, §6.2 step 3. Class (iii). DC: INTENTIONAL; an actual
honest source of an action strictly before the pending gate is below `D`. -/
theorem arming_source_below {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho)
    (htsrc : ∀ y r C, y ∈ rho.honest →
      actionSource p c E rho y r = some (some C) →
      ∃ X G, candidatesAt p c E rho y r = some X ∧ C ∈ X ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        (∀ A ∈ X, Block.Preceq A G) ∧
        (∀ A ∈ X, fastAt p c E rho y (r * p.R) A) ∧
        ∃ i, IsGateTick p c rho i y (r * p.R) ∧ gatePassedAt p c E rho i)
    {b₀ : Time} {l : Slot} {D : Block} (hl : SA.gateTime p.toParams l ≤ b₀)
    (hmax : ∀ r X, (r, X) ∈ cleanResults p c E rho (timeIdx rho b₀) → r ≤ l →
      Block.Preceq X D) :
    ∀ y r X, y ∈ rho.honest → p.actionTime r < SA.gateTime p.toParams (l + 1) →
      actionSource p c E rho y r = some (some X) → Block.Preceq X D := by
  intro y r X hy hr hX
  obtain ⟨Xs, G, _, hXm, hG, hle, _, i, hi, hpass⟩ := htsrc y r X hy hX
  have hrl := arming_action_label p l r hr
  have hgb : SA.gateTime p.toParams (r * p.R) ≤ b₀ :=
    ((arming_gate_le_iff p _ _).mpr hrl).trans hl
  exact block_preceq_trans (hle X hXm)
    (hmax _ G (arming_clean_of_tick hs (arming_enabled_of_pass hi hpass) hgb hG).2 hrl)

/-- Plan O-ARM §4 field 4, §6.2 step 3. Class (iii). DC: INTENTIONAL; the
named entry of an exact honest row strictly before the pending gate is an
ancestor of the FG lift of `D`, at its own height. -/
theorem arming_entry_below {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho)
    (hnamed : ∀ i y r a, HonestRowAt p c E rho i y r a →
      ∃ e C G, namedEntry a.payload.height_pair = some e ∧
        actionSourceFG p c E rho y r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧
        fastAt p c E rho y (r * p.R) (eraseFG C))
    {b₀ : Time}
    (hcleanGate : ∀ r y, SA.gateTime p.toParams r ≤ b₀ → y ∈ rho.honest →
      ∃ C, gateResult p c E rho y r = some (some C) ∧
        (∃ i, IsGateTick p c rho i y r ∧ gatePassedAt p c E rho i) ∧
        Block.Preceq C (S_at p c E rho (afterTicksIdx rho (SA.gateTime p.toParams r)) y) ∧
        ∀ r' < r, ∀ C', gateResult p c E rho y r' = some (some C') → Block.Preceq C' C)
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)} (hDh : eraseFG Dh = D)
    (hl : SA.gateTime p.toParams l ≤ b₀)
    (hmax : ∀ r X, (r, X) ∈ cleanResults p c E rho (timeIdx rho b₀) → r ≤ l →
      Block.Preceq X D) :
    ∀ i y r (a : RowWire p.n) e, HonestRowAt p c E rho i y r a →
      p.actionTime r < SA.gateTime p.toParams (l + 1) →
      namedEntry a.payload.height_pair = some e → EntryBelow p e Dh := by
  intro i y r a e ha hr he
  obtain ⟨e', C, G, he', _, hee, hTC, hG, hCG, _⟩ := hnamed i y r a ha
  have heq : e = e' := Option.some.inj (he.symm.trans he')
  have hrl := arming_action_label p l r hr
  have hgb : SA.gateTime p.toParams (r * p.R) ≤ b₀ :=
    ((arming_gate_le_iff p _ _).mpr hrl).trans hl
  obtain ⟨_, _, ⟨k, hk, hpass⟩, _⟩ := hcleanGate (r * p.R) y hgb ha.1
  have hGD := hmax _ G (arming_clean_of_tick hs (arming_enabled_of_pass hk hpass) hgb hG).2 hrl
  have hCD : FGBlock.Preceq C Dh := arming_lift (hDh ▸ block_preceq_trans hCG hGD)
  have hh : (heightView p (heightView p C).T_h).h = (heightView p C).h :=
    (Window.windowHeightLaws p p.K_W p.kWLarge).entry_same_height C
  refine ⟨(heightView p C).T_h, KitFG.preceq_trans hTC hCD, ?_⟩
  rw [heq, hee, hh]

/-- ROOT-DIGEST W2b. Plan O-ARM §4 field 5, §6.2 step 3. Class (iii). DC: INTENTIONAL;
`cpPrefix_of_srcFrame` at the FG lift of `D`, for every index up to the strict
pending read. The named entries are those of actions strictly before d(l + 1). -/
theorem arming_frame_below {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (_hsrc : SrcFrameAboveStmt p c E rho) {l : Slot} {D : Block}
    {Dh : FGBlock (Fin p.n)} (hDh : eraseFG Dh = D)
    (hentry : ∀ i y r (a : RowWire p.n) e, HonestRowAt p c E rho i y r a →
      p.actionTime r < SA.gateTime p.toParams (l + 1) →
      namedEntry a.payload.height_pair = some e → EntryBelow p e Dh)
    {i : Nat} (hi : i ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)))
    {y : V} (hy : y ∈ rho.honest) (hroots : NamedRootCollisionFree p c E rho)
    (hstrat : RStrat p c E rho) (hScope : RootBlockInRun p c E rho (eraseFG Dh)) :
    Block.Preceq (F_at p c E rho i y) D ∧ Block.Preceq (J_at p c E rho i y) D ∧
      Block.Preceq (eraseFG (FGSA.controls p (storeAt p c E rho i y)).Z) D ∧
      (FGSA.controls p (storeAt p c E rho i y)).contest = false ∧
      (FGSA.controls p (storeAt p c E rho i y)).lo ≤ (heightView p Dh).h := by
  have _hcanonicalFrame := hframe
  have hcp := fgsa_cpPrefix_of_srcFrame p c E rho hstore hroots hstrat
  rw [CPPrefix_def] at hcp
  obtain ⟨_, hF, hJ, hZ, hn, hlo⟩ := hcp i y Dh hy hScope (by
    intro z r a e ha he
    obtain ⟨k, hk, hrow⟩ := ha
    have htk : p.actionTime r < SA.gateTime p.toParams (l + 1) :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hs hrow.2.1 _).mp (lt_of_lt_of_le hk hi)
    exact hentry k z r a e hrow htk he)
  rw [← hDh]
  exact ⟨eraseFG_preceq hF, eraseFG_preceq hJ, eraseFG_preceq hZ, hn, hlo⟩

/-- Plan O-ARM §4 field 5. Class (iii). DC: INTENTIONAL; every lease target at
or before the cut is below an actual successful gate result of label at most
`l`, hence below `D`. -/
theorem arming_leases_cut {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {b₀ : Time} {l : Slot} {D : Block}
    (hcut : b₀ < SA.gateTime p.toParams (l + 1))
    (hleaseOrigin : ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i y).base.obligations,
      ∃ q < i, ∃ s C, IsGateTick p c rho q y s ∧
        gatePassedAt p c E rho q ∧
        gateResultAt p c E rho q = some (some C) ∧ Block.Preceq row.1 C)
    (hmax : ∀ r X, (r, X) ∈ cleanResults p c E rho (timeIdx rho b₀) → r ≤ l →
      Block.Preceq X D)
    {i : Nat} (hi : i ≤ timeIdx rho b₀) {y : V} (hy : y ∈ rho.honest) :
    ∀ row ∈ (storeAt p c E rho i y).base.obligations, Block.Preceq row.1 D := by
  intro row hrow
  obtain ⟨q, hq, s, C, hqt, hpass, hres, hrC⟩ := hleaseOrigin i y hi hy row hrow
  have hmem : (s, C) ∈ cleanResults p c E rho (timeIdx rho b₀) :=
    ⟨q, lt_of_lt_of_le hq hi, y, hqt, (arming_enabled_of_pass hqt hpass).2, hres⟩
  obtain ⟨_, _, _, _, _, hsb, _, _⟩ := arming_clean_mem hs le_rfl hmem
  exact block_preceq_trans hrC (hmax s C hmem (arming_lt_pending p l s (hsb.trans_lt hcut)))

/-- Plan O-ARM §4 field 5, §6.2 step 5. Class (iii). DC: INTENTIONAL; between
the cut and the pending gate no lease target is introduced: a tick keeps a
sublist and a delivery keeps or filters the leases. -/
theorem arming_leases_interval {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    {b₀ : Time} {l : Slot} {D : Block} (hl : SA.gateTime p.toParams l ≤ b₀)
    (y : V) {i : Nat} (hi₀ : timeIdx rho b₀ ≤ i)
    (hi : i ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)))
    (h₀ : ∀ row ∈ (storeAt p c E rho (timeIdx rho b₀) y).base.obligations,
      Block.Preceq row.1 D) :
    ∀ row ∈ (storeAt p c E rho i y).base.obligations, Block.Preceq row.1 D := by
  induction i, hi₀ using Nat.le_induction with
  | base => exact h₀
  | succ k hk ih =>
    have hkl : k < rho.events.length :=
      lt_of_lt_of_le (Nat.lt_succ_self k) (hi.trans (arming_idxBefore_le_length rho _))
    have he : rho.events[k]? = some rho.events[k] := List.getElem?_eq_getElem hkl
    have hprev := ih (le_trans (Nat.le_succ k) hi)
    rcases arming_store_succ (E := E) hnr he y with heq | ⟨t, het, heq⟩ | ⟨o, t, het, heq⟩
    · rw [heq]
      exact hprev
    · obtain ⟨hb, hd⟩ := arming_event_window hs he hk (lt_of_lt_of_le (Nat.lt_succ_self k) hi)
      rw [het] at hb hd
      have hoff := arming_clock_offGate_fields p (storeAt p c E rho k y) t
        (arming_offGate p l hl hb hd)
      intro row hrow
      rw [heq] at hrow
      exact hprev row (hoff.2.2.2.subset hrow)
    · intro row hrow
      rw [heq] at hrow
      rcases arming_process_lease p (storeAt p c E rho k y) (toWire p o) with h | h
      · rw [h.1] at hrow
        exact hprev row hrow
      · rw [h.1] at hrow
        exact hprev row (List.mem_filter.mp hrow).1

/-- Plan O-ARM §4 field 5, §6.2 step 5. Class (iii). DC: INTENTIONAL; between
the cut and the pending gate no lease target is introduced: a tick keeps a
sublist and a delivery keeps or filters the leases. -/
theorem arming_leases_interval_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho)
    {b₀ : Time} {l : Slot} {D : Block} (hl : SA.gateTime p.toParams l ≤ b₀)
    (y : V) {i : Nat} (hi₀ : timeIdx rho b₀ ≤ i)
    (hi : i ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)))
    (hEpoch : V2.D.restartFree rho y (timeIdx rho b₀) i)
    (h₀ : ∀ row ∈ (storeAt p c E rho (timeIdx rho b₀) y).base.obligations,
      Block.Preceq row.1 D) :
    ∀ row ∈ (storeAt p c E rho i y).base.obligations, Block.Preceq row.1 D := by
  induction i, hi₀ using Nat.le_induction with
  | base => exact h₀
  | succ k hk ih =>
    have hkl : k < rho.events.length :=
      lt_of_lt_of_le (Nat.lt_succ_self k) (hi.trans (arming_idxBefore_le_length rho _))
    have he : rho.events[k]? = some rho.events[k] := List.getElem?_eq_getElem hkl
    have hprev := ih (le_trans (Nat.le_succ k) hi)
      (hEpoch.mono le_rfl (Nat.le_succ k))
    rcases arming_store_succ_on (E := E) he y
      (hEpoch.mono hk le_rfl) with heq | ⟨t, het, heq⟩ | ⟨o, t, het, heq⟩
    · rw [heq]
      exact hprev
    · obtain ⟨hb, hd⟩ := arming_event_window hs he hk (lt_of_lt_of_le (Nat.lt_succ_self k) hi)
      rw [het] at hb hd
      have hoff := arming_clock_offGate_fields p (storeAt p c E rho k y) t
        (arming_offGate p l hl hb hd)
      intro row hrow
      rw [heq] at hrow
      exact hprev row (hoff.2.2.2.subset hrow)
    · intro row hrow
      rw [heq] at hrow
      rcases arming_process_lease p (storeAt p c E rho k y) (toWire p o) with h | h
      · rw [h.1] at hrow
        exact hprev row hrow
      · rw [h.1] at hrow
        exact hprev row (List.mem_filter.mp hrow).1

/-- ROOT-DIGEST W2b. Plan O-ARM §4 field 5. Class (iii). DC: INTENTIONAL; field 5 of the arming
certificate: every honest local state up to the strict pending read. -/
theorem arming_prefix_state {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho) {b₀ : Time} {l : Slot} {D : Block}
    {Dh : FGBlock (Fin p.n)} (hDh : eraseFG Dh = D)
    (hl : SA.gateTime p.toParams l ≤ b₀) (hcut : b₀ < SA.gateTime p.toParams (l + 1))
    (hentry : ∀ i y r (a : RowWire p.n) e, HonestRowAt p c E rho i y r a →
      p.actionTime r < SA.gateTime p.toParams (l + 1) →
      namedEntry a.payload.height_pair = some e → EntryBelow p e Dh)
    (hleaseOrigin : ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i y).base.obligations,
      ∃ q < i, ∃ s C, IsGateTick p c rho q y s ∧
        gatePassedAt p c E rho q ∧
        gateResultAt p c E rho q = some (some C) ∧ Block.Preceq row.1 C)
    (hmax : ∀ r X, (r, X) ∈ cleanResults p c E rho (timeIdx rho b₀) → r ≤ l →
      Block.Preceq X D) (hroots : NamedRootCollisionFree p c E rho)
    (hstrat : RStrat p c E rho) (hScope : RootBlockInRun p c E rho (eraseFG Dh)) :
    ∀ i y, i ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) →
      i ≤ rho.events.length → y ∈ rho.honest →
      Block.Preceq (F_at p c E rho i y) D ∧ Block.Preceq (J_at p c E rho i y) D ∧
      Block.Preceq (eraseFG (FGSA.controls p (storeAt p c E rho i y)).Z) D ∧
      (FGSA.controls p (storeAt p c E rho i y)).contest = false ∧
      (FGSA.controls p (storeAt p c E rho i y)).lo ≤ (heightView p Dh).h ∧
      ∀ row ∈ (storeAt p c E rho i y).base.obligations, Block.Preceq row.1 D := by
  intro i y hi _ hy
  obtain ⟨hF, hJ, hZ, hn, hlo⟩ := arming_frame_below (hroots := hroots) (hstrat := hstrat) (hScope
    := hScope)
    hs hstore hframe hsrc hDh hentry hi hy
  refine ⟨hF, hJ, hZ, hn, hlo, ?_⟩
  rcases le_or_gt i (timeIdx rho b₀) with hle | hgt
  · exact arming_leases_cut hs hcut hleaseOrigin hmax hle hy
  · exact arming_leases_interval hs hnr hl y hgt.le hi
      (arming_leases_cut hs hcut hleaseOrigin hmax le_rfl hy)

end AvailableChain.FGSA.Run
end
