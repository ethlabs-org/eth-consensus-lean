module
public import AvailableChainFGSAProofs.Proofs.Healing.ResetCut
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchDefs
public import AvailableChainFGCompose.Proofs.Healing.Reset

public section

/-! Blueprint 21 H.11:1744–1800, H.22:3229–3241; S5 J8 R1–R3.
DC: INTENTIONAL inclusive SA cut and the first honest height-(M+1) row.
R1 eliminates the named HG.5 input through frontierSearchStatement_iff and the
budget equations frontierSearchRiseBudget_eq / frontierSearchRowBudget_eq.
The named input is HG.5: producer HG2A-RECEIPT F3 (lf-hg2a). It supplies reset_row and
reset_first (the least honest row at exactly M+1), so HG.5 owns the IF.3(a) skip case,
global minimality and the ρ₁ arm. No frozen interface is changed.
The source input is INLINE. R2 (Assembly/ResetArrival.lean) discharges it from the
frozen SourceDisciplineBaseAt; it keeps the actual source and root.
No progress-attempt statement or full-H0 proposal service is used. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def p0d6b_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d6b_clock_laws (p : Params) :
    FGCompose.FGTimingLaws (p0d6b_timing p) where
  delta_pos := p.deltaPos
  rounds := p.RLarge
  proposal_eq s := by
    change 4 * p.Δ * (s : Time) = 4 * (s : Time) * p.Δ
    ring
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq _ := rfl

/-- Blueprint 21 H.11:1791–1797; S5 J8 R3.
DC: SAME the two HG.5 charges, with all subtraction in integer time. -/
theorem healing_reset_budget_sum (p : Params) (G ΔF ρbar : Time) :
    B_resetF p ΔF G ρbar = 3 * P p +
      (E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + B_cF p ΔF G ρbar) +
      (E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + D_cF p ρbar) := by
  exact FGCompose.healing_reset_budget_sum (p0d6b_timing p) G ΔF ρbar

/-- Blueprint 21 H.11:1791–1797; S5 J8 R3.
DC: SAME choose the allowance that attains the frozen minimum. -/
theorem healing_reset_budget_choice (p : Params) (G ΔF : Time) :
    ∃ ρbar, (ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) ∧
      B'_resetF p ΔF G = 3 * P p +
        (E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + B_cF p ΔF G ρbar) +
        (E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + D_cF p ρbar) := by
  by_cases hk : p.k ≤ 2 * p.R + 1
  · by_cases hle : B_resetF p ΔF G (ρΓ p G) ≤ B_resetF p ΔF G (ρ₁ p G)
    · refine ⟨ρΓ p G, Or.inl rfl, ?_⟩
      rw [B'_resetF_def, ite_eq_left hk, min_eq_left hle]
      exact healing_reset_budget_sum p G ΔF (ρΓ p G)
    · refine ⟨ρ₁ p G, Or.inr ⟨rfl, hk⟩, ?_⟩
      rw [B'_resetF_def, ite_eq_left hk, min_eq_right (le_of_not_ge hle)]
      exact healing_reset_budget_sum p G ΔF (ρ₁ p G)
  · refine ⟨ρΓ p G, Or.inl rfl, ?_⟩
    rw [B'_resetF_def, ite_eq_right hk]
    exact healing_reset_budget_sum p G ΔF (ρΓ p G)

/-- Blueprint 21 H.11:1791–1797; S5 J8 R3.
DC: SAME the strict cut bound gives the strict frozen minimum deadline. -/
theorem healing_reset_budget_lt (p : Params) (G ΔF GST u₀ : Time)
    (hcut : u₀ < GST + 3 * P p) :
    ∃ ρbar, (ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) ∧
      u₀ + (E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + B_cF p ΔF G ρbar) +
        (E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + D_cF p ρbar) <
        GST + B'_resetF p ΔF G := by
  obtain ⟨ρbar, hallow, hbudget⟩ := healing_reset_budget_choice p G ΔF
  exact ⟨ρbar, hallow, FGCompose.healing_reset_budget_lt (p0d6b_timing p) G ΔF GST u₀ ρbar _
    hbudget hcut⟩

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [DecidableEq V] in
private theorem p0d6b_start_nonneg : 0 ≤ recoveryStart p E := by
  have h := healing_recovery_start_lower (p := p) E
  linarith [E.t_GST_nonneg, p.deltaPos]

omit [DecidableEq V] in
private theorem p0d6b_first_eq :
    FGCompose.resetFirstRound (p0d6b_timing p) (p0d6b_clock_laws p) (recoveryStart p E) =
      resetFirstRound p E :=
  le_antisymm (FGCompose.reset_rG_first (p0d6b_timing p) (p0d6b_clock_laws p)
      (recoveryStart p E) _ (reset_rG_after p E))
    (reset_rG_first p E _ (FGCompose.reset_rG_after (p0d6b_timing p) (p0d6b_clock_laws p)
      (recoveryStart p E)))

omit [DecidableEq V] in
private theorem p0d6b_cut_eq :
    FGCompose.resetCutTime (p0d6b_timing p) (p0d6b_clock_laws p) (recoveryStart p E) =
      resetCutTime p E := by
  rw [FGCompose.reset_cut, reset_cut, p0d6b_first_eq]
  rfl

private def p0d6b_observations : FGCompose.FGObservationReads (fgsaCoreReads p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private theorem p0d6b_tree_keep : FGCompose.FGTreeKeepLaws (fgsaCoreReads p c) := by
  constructor
  intro nd t
  rw [fgsaCoreReads_def]
  change nd.st.fg.TF ⊆ (acRestart p nd.st t).fg.TF
  rw [acRestart_fg]

private theorem p0d6b_store_inv (i : Nat) (x : V) :
    KitFG.FGStoreInvariant (p0d6b_observations p c).height
      (p0d6b_observations p c).finality
      ((fgsaCoreReads p c).core (V2.D.Run.stateBefore E rho i x)).fg := by
  change KitFG.FGStoreInvariant (heightView p) (finalityView p) _
  rw [fgsaCoreReads_def]
  exact (storeBundle_stateBefore E rho i x).cstore.fg

private theorem p0d6b_row_eq (j : Nat) (y : V) (r : Nat) (a : RowWire p.n) :
    FGCompose.HonestRowAt (fgsaSafetyReads p c) E rho (p0d6b_timing p) j y r a =
      HonestRowAt p c E rho j y r a := by
  rw [fgsaSafetyReads_def]
  rfl

private theorem p0d6b_entry_eq (pair : NamedHeightPair) :
    FGCompose.namedEntry pair = namedEntry pair := by cases pair <;> rfl

private theorem p0d6b_source_eq (x : V) (r : Nat) :
    FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (p0d6b_timing p) x r =
      actionSourceFG p c E rho x r := by
  rw [fgsaCoreReads_def]
  rfl

private theorem p0d6b_old_heights_eq :
    FGCompose.oldRowHeights (fgsaSafetyReads p c) E rho (p0d6b_timing p)
      (fun a => FGCompose.namedEntry a.payload.height_pair) (recoveryStart p E) =
      oldRowHeights p c E rho := by
  unfold FGCompose.oldRowHeights oldRowHeights
  simp only [p0d6b_row_eq, p0d6b_entry_eq]
  rfl

private theorem p0d6b_mu_eq :
    FGCompose.muOf (fgsaSafetyReads p c) E rho (p0d6b_timing p)
      (fun a => FGCompose.namedEntry a.payload.height_pair) (recoveryStart p E) =
      muOf p c E rho := by
  unfold FGCompose.muOf muOf
  rw [p0d6b_old_heights_eq]

private theorem p0d6b_honest_frontier_eq (t : Time) :
    FGCompose.honestFrontier (fgsaCoreReads p c) E rho t = honestFrontier p c E rho t := by
  rw [fgsaCoreReads_def]
  rfl

private theorem p0d6b_frontier_eq :
    FGCompose.resetCutFrontier (fgsaCoreReads p c) E rho (p0d6b_timing p)
      (p0d6b_clock_laws p) (recoveryStart p E) = resetCutFrontier p c E rho := by
  unfold FGCompose.resetCutFrontier
  rw [p0d6b_cut_eq, p0d6b_honest_frontier_eq]
  exact (reset_frontier p c E rho).symm

private theorem p0d6b_heightRow_eq (r h : Nat) :
    FGCompose.HeightRow (fgsaSafetyReads p c) E rho (p0d6b_timing p)
      (fun a => FGCompose.namedEntry a.payload.height_pair) r h = HeightRow p c E rho r h := by
  unfold FGCompose.HeightRow HeightRow
  simp only [p0d6b_row_eq, p0d6b_entry_eq]

private theorem p0d6b_name
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
      {e : Height × BlockId}, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId}
    (ha : FGCompose.HonestRowAt (fgsaSafetyReads p c) E rho (p0d6b_timing p) j x r a)
    (he : FGCompose.namedEntry a.payload.height_pair = some e) :
    ∃ C, FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (p0d6b_timing p) x r =
        some (some C) ∧
      e = (((p0d6b_observations p c).height C).h,
        ((p0d6b_observations p c).height C).T_h.root) := by
  have ha' : HonestRowAt p c E rho j x r a := (p0d6b_row_eq p c E rho j x r a) ▸ ha
  have he' : namedEntry a.payload.height_pair = some e := by rwa [p0d6b_entry_eq] at he
  obtain ⟨C, G, hC, hh, _⟩ := emittedName ha' he'
  exact ⟨C, by rwa [p0d6b_source_eq], hh⟩


section Source

variable
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
      {e : Height × BlockId}, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))

include emittedName

/-- Blueprint 21 H.11:1755–1756; S5 J8 R1 rowCap.
DC: SAME the closed cap. INLINE producer: sourceDiscipline_emittedName. -/
theorem healing_reset_rowCap (hs : V2.D.ScheduleWellFormed E rho) :
    ∀ j y r a h e t, HonestRowAt p c E rho j y r a →
      rho.events[j]? = some (.tick y t) → t ≤ resetCutTime p E →
      namedEntry a.payload.height_pair = some (h, e) → h ≤ resetCutFrontier p c E rho := by
  intro j y r a h e t ha hj ht he
  have h := FGCompose.healing_reset_rowCap (T := p0d6b_timing p) (L := p0d6b_clock_laws p)
    (Jst := recoveryStart p E) (R := fgsaCoreReads p c) (S := fgsaSafetyReads p c) (E := E)
    (rho := rho) (O := p0d6b_observations p c) (pair := fun a => a.payload.height_pair)
    (CL := fgsaCoreLaws p c) (K := p0d6b_tree_keep p c)
    (storeInv := p0d6b_store_inv p c E rho)
    (emittedName := fun ha he => p0d6b_name p c E rho emittedName ha he) hs j y r a h e t
    ((p0d6b_row_eq p c E rho j y r a).symm ▸ ha) hj ((p0d6b_cut_eq p E).symm ▸ ht)
    (by rw [p0d6b_entry_eq]; exact he)
  rwa [p0d6b_frontier_eq] at h

/-- Blueprint 21 H.11:1754–1756,1772–1777; S5 J8 R1 mu_le.
DC: SAME an actual HG.5 row supplies a nonempty honest set. -/
theorem healing_reset_mu_le (hs : V2.D.ScheduleWellFormed E rho)
    {r h : Nat} (hrow : HeightRow p c E rho r h) :
    muOf p c E rho ≤ resetCutFrontier p c E rho := by
  have h := FGCompose.healing_reset_mu_le (T := p0d6b_timing p) (L := p0d6b_clock_laws p)
    (Jst := recoveryStart p E) (R := fgsaCoreReads p c) (S := fgsaSafetyReads p c) (E := E)
    (rho := rho) (O := p0d6b_observations p c) (pair := fun a => a.payload.height_pair)
    (Ef := p.E) (HL := (fgCertificateLaws p).height) (CL := fgsaCoreLaws p c)
    (K := p0d6b_tree_keep p c)
    (storeInv := p0d6b_store_inv p c E rho)
    (emittedName := fun ha he => p0d6b_name p c E rho emittedName ha he) hs
    ((p0d6b_heightRow_eq p c E rho r h).symm ▸ hrow)
  rwa [p0d6b_mu_eq, p0d6b_frontier_eq] at h

/-- Blueprint 21 H.11:1757–1759,1799–1800; S5 J8 R1 fresh.
DC: SAME select an erased actual fresh source, with the row's exact root.
INLINE producer: the frozen SourceDisciplineBaseAt (Assembly/ResetArrival.lean). -/
theorem healing_reset_fresh {r M : Nat} (hrow : HeightRow p c E rho r (M + 1)) :
    ∃ CStar, ∃ j y, ∃ (a : RowWire p.n) (C : FGBlock (Fin p.n)),
      HonestRowAt p c E rho j y r a ∧
      namedEntry a.payload.height_pair = some (M + 1, (heightView p C).T_h.root) ∧
      actionSourceFG p c E rho y r = some (some C) ∧
      eraseFG C = CStar ∧ (heightView p C).h = M + 1 := by
  obtain ⟨CStar, j, y, a, C, ha, he, hC, hE, hh⟩ := FGCompose.healing_reset_fresh
    (T := p0d6b_timing p) (R := fgsaCoreReads p c) (S := fgsaSafetyReads p c) (E := E)
    (rho := rho) (O := p0d6b_observations p c) (pair := fun a => a.payload.height_pair)
    (emittedName := fun ha he => p0d6b_name p c E rho emittedName ha he)
    ((p0d6b_heightRow_eq p c E rho r (M + 1)).symm ▸ hrow)
  refine ⟨CStar, j, y, a, C, (p0d6b_row_eq p c E rho j y r a) ▸ ha, ?_, ?_, ?_, hh⟩
  · rwa [p0d6b_entry_eq] at he
  · rwa [p0d6b_source_eq] at hC
  · rw [← hE, fgsaCoreReads_def]

end Source

/-- Blueprint 21 H.11:1778–1780; S5 J8 R1 synchronous.
DC: SAME a height-(M+1) row is strictly after the inclusive cut. -/
theorem healing_reset_synchronous {r : Nat}
    (rowCap : ∀ j y r a h e t, HonestRowAt p c E rho j y r a →
      rho.events[j]? = some (.tick y t) → t ≤ resetCutTime p E →
      namedEntry a.payload.height_pair = some (h, e) → h ≤ resetCutFrontier p c E rho)
    (hrow : HeightRow p c E rho r (resetCutFrontier p c E rho + 1)) :
    E.t_GST ≤ SA.voteTime p.toParams (r * p.R) := by
  have hstart := healing_recovery_start_lower (p := p) E
  refine FGCompose.healing_reset_synchronous (T := p0d6b_timing p) (L := p0d6b_clock_laws p)
    (Jst := recoveryStart p E) (R := fgsaCoreReads p c) (S := fgsaSafetyReads p c) (E := E)
    (rho := rho) (pair := fun a => a.payload.height_pair) (by linarith [p.deltaPos]) ?_
    ((p0d6b_frontier_eq p c E rho).symm ▸ (p0d6b_heightRow_eq p c E rho r _).symm ▸ hrow)
  intro j y r a h e t ha hj ht he
  rw [p0d6b_frontier_eq]
  exact rowCap j y r a h e t ((p0d6b_row_eq p c E rho j y r a) ▸ ha) hj
    ((p0d6b_cut_eq p E) ▸ ht)
    (by rwa [p0d6b_entry_eq] at he)

/-- Blueprint 21 H.11:1757–1758; S5 J8 R1 reset_first support.
DC: SAME the exported first-row contract supplies the exact minimality field.
healing_resetWitness obtains this contract from the named HG.5 input. -/
theorem healing_reset_reset_first {M : Nat} {deadline : Time}
    (firstRow : FirstHeightRowBy p c E rho (M + 1) deadline) :
    ∃ rStar, HeightRow p c E rho rStar (M + 1) ∧
      (∀ r, HeightRow p c E rho r (M + 1) → rStar ≤ r) ∧
      p.actionTime rStar ≤ deadline :=
  (firstHeightRowBy_iff p c E rho (M + 1) deadline).mp firstRow

section Source

variable
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
      {e : Height × BlockId}, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))

include emittedName

/-- Blueprint 21 H.11:1744–1800, H.22:3229–3241; S5 J8 R1 field support.
DC: INTENTIONAL reset-only fields, with no Q* service at this horizon.
The first-row contract is a frozen field input for this support lemma.
healing_resetWitness derives the first-row contract from healing_frontierSearch (HG2A-RECEIPT F3).
INLINE producer: the frozen SourceDisciplineBaseAt (Assembly/ResetArrival.lean). -/
theorem healing_reset_fields [Fintype V] {G ΔF deadline : Time}
    (hset : HealingSet p c E rho G ΔF)
    (firstRow : FirstHeightRowBy p c E rho (resetCutFrontier p c E rho + 1) deadline) :
    ∃ w, H0Reset p c E rho w ∧ p.actionTime w.rStar ≤ deadline := by
  have hs := hset.base.valid.toScheduleWellFormed
  have hstart := healing_recovery_start_lower (p := p) E
  obtain ⟨rS, hrowS, hfirstS, htimeS⟩ :=
    (firstHeightRowBy_iff p c E rho _ deadline).mp firstRow
  have firstRow' : FGCompose.FirstHeightRowBy (fgsaSafetyReads p c) E rho (p0d6b_timing p)
      (fun a => a.payload.height_pair)
      (FGCompose.resetCutFrontier (fgsaCoreReads p c) E rho (p0d6b_timing p)
        (p0d6b_clock_laws p) (recoveryStart p E) + 1) deadline := by
    rw [p0d6b_frontier_eq]
    exact (FGCompose.FirstHeightRowBy_def (fgsaSafetyReads p c) E rho (p0d6b_timing p)
      (fun a => a.payload.height_pair) _ deadline).mpr
      ⟨rS, (p0d6b_heightRow_eq p c E rho rS _).symm ▸ hrowS,
        fun r hr => hfirstS r ((p0d6b_heightRow_eq p c E rho r _) ▸ hr), htimeS⟩
  obtain ⟨w, hw, _, _, _, htime⟩ := FGCompose.healing_reset_fields
    (T := p0d6b_timing p) (L := p0d6b_clock_laws p)
    (Jst := recoveryStart p E) (R := fgsaCoreReads p c) (S := fgsaSafetyReads p c) (E := E)
    (rho := rho) (O := p0d6b_observations p c) (pair := fun a => a.payload.height_pair)
    (Ef := p.E) (HL := (fgCertificateLaws p).height) (CL := fgsaCoreLaws p c)
    (K := p0d6b_tree_keep p c)
    (storeInv := p0d6b_store_inv p c E rho)
    (emittedName := fun ha he => p0d6b_name p c E rho emittedName ha he) hs
    (p0d6b_start_nonneg p E) (by linarith [p.deltaPos]) firstRow'
  let W : HealingWitness :=
    { rG := w.rG, u₀ := w.u0, M := w.M, rStar := w.rStar, sStar := w.sStar,
      CStar := w.source, u := 0, QStar := .genesis }
  refine ⟨W, ?_, htime⟩
  obtain ⟨jF, yF, aF, CF, haF, heF, hCF, hEF, hhF⟩ := hw.fresh
  exact
    { rG_after := hw.rG_after
      rG_first := hw.rG_first
      cut := hw.cut
      frontier := (p0d6b_honest_frontier_eq p c E rho w.u0) ▸ hw.frontier
      rowCap := fun j y r a h e t ha hj ht he => hw.rowCap j y r a h e t
        ((p0d6b_row_eq p c E rho j y r a).symm ▸ ha) hj ht (by rw [p0d6b_entry_eq]; exact he)
      mu_le := (p0d6b_mu_eq p c E rho) ▸ hw.mu_le
      cut_lower := hw.cut_lower
      cut_upper := hw.cut_upper
      reset_row := (p0d6b_heightRow_eq p c E rho w.rStar (w.M + 1)) ▸ hw.reset_row
      reset_first := fun r hr => hw.reset_first r
        ((p0d6b_heightRow_eq p c E rho r (w.M + 1)).symm ▸ hr)
      label := hw.label
      fresh := ⟨jF, yF, aF, CF, (p0d6b_row_eq p c E rho jF yF w.rStar aF) ▸ haF,
        by rwa [p0d6b_entry_eq] at heF, by rwa [p0d6b_source_eq] at hCF,
        by rw [fgsaCoreReads_def] at hEF; exact hEF, hhF⟩
      synchronous := hw.synchronous }

/-- Blueprint 21 H.11:1744–1800, H.22:3229–3241; S5 J8 R1.
DC: INTENTIONAL reset-only witness, strict reset deadline recoveryStart + B'_reset^F.
Named HG.5 input `hsearch`: producer HG2A-RECEIPT F3 (lf-hg2a); it gives reset_row/first.
INLINE producer: the frozen SourceDisciplineBaseAt (Assembly/ResetArrival.lean). -/
theorem healing_resetWitness [Fintype V] {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF) (hδ : p.δt = 2 * p.R)
    (hbound : LivenessBoundW p ΔF) (hsearch : FrontierSearchStatement p c E rho G ΔF)
    (hhor : recoveryStart p E + B'_resetF p ΔF G ≤ rho.horizon) :
    ∃ w, H0Reset p c E rho w ∧
      p.actionTime w.rStar < recoveryStart p E + B'_resetF p ΔF G := by
  have hs := hset.base.valid.toScheduleWellFormed
  have hcap := healing_reset_rowCap p c E rho emittedName hs
  obtain ⟨ρbar, hallow, hlt⟩ :=
    healing_reset_budget_lt p G ΔF (recoveryStart p E) (resetCutTime p E) (reset_cut_upper p E)
  rw [← frontierSearchRiseBudget_eq, ← frontierSearchRowBudget_eq] at hlt
  have hguard : resetCutTime p E + frontierSearchRiseBudget p G ΔF ρbar +
      frontierSearchRowBudget p G ΔF ρbar ≤ rho.horizon := by linarith
  have hfs := (frontierSearchStatement_iff p c E rho G ΔF).mp hsearch hδ hbound
    (resetFirstRound p E) (resetCutTime p E) (resetCutFrontier p c E rho)
    (reset_rG_after p E) (reset_rG_first p E) (reset_cut p E) (reset_cut_lower p E)
    (reset_frontier p c E rho) hcap
  obtain ⟨rStar, hrow, hfirst, hall⟩ := hfs.2 ⟨ρbar, hallow, hguard⟩
  obtain ⟨j, ev, _, _, hevt, _, _, hrt⟩ := hall ρbar hallow hguard
  have firstRow : FirstHeightRowBy p c E rho (resetCutFrontier p c E rho + 1)
      (resetCutTime p E + frontierSearchRiseBudget p G ΔF ρbar +
        frontierSearchRowBudget p G ΔF ρbar) :=
    (firstHeightRowBy_iff p c E rho _ _).mpr ⟨rStar, hrow, hfirst, by linarith⟩
  obtain ⟨w, hw, htime⟩ := healing_reset_fields p c E rho emittedName hset firstRow
  exact ⟨w, hw, lt_of_le_of_lt htime hlt⟩

end Source

end AvailableChain.FGSA.Run
end
