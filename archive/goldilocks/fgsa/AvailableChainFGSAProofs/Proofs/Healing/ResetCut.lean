module
-- Preserve the old wrapper facade and its exported repair and bound suppliers.
public import AvailableChainFGSAProofs.Proofs.Healing.RepairGate -- shake: keep (facade coverage)
public import AvailableChainFGSAProofs.Proofs.Shared.BoundsW -- shake: keep (facade coverage)
public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope -- shake: keep (facade coverage)
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyClient
public import AvailableChainFGCompose.Proofs.Healing.ResetCut

public section

/-! S5 RS-0, plan Q4; blueprint 21 H.11:1744–1800.
The cut includes all events at its time. The frontier is the frozen
`honestFrontier`, with no replacement. Foundations supplies the INLINE
`emittedName` input through `emittedName_window` (Sources:217).

C1 STOP: the permitted inputs do not supply an event at the cut. A finite
run can end before the cut. C3 STOP: the permitted inputs allow an empty
honest set. Then the frontier is zero and `muOf` is one. The results below
prove the timing, row cap, old-row bound, and exact conditions for these gaps.
No premise is added to close either item. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private def p0d6a_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d6a_clock_laws (p : Params) :
    FGCompose.FGTimingLaws (p0d6a_timing p) where
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

private theorem p0d6a_start_nonneg : 0 ≤ recoveryStart p E := by
  have h := healing_recovery_start_lower (p := p) E
  linarith [E.t_GST_nonneg, p.deltaPos]

/-- H.11: the period is at least 8Δ. Params supplies R ≥ 2. -/
theorem reset_period_lower : 8 * p.Δ ≤ P p := by
  exact FGCompose.reset_period_lower (p0d6a_timing p) (p0d6a_clock_laws p)


/-- H.11: the action clock has a round at or after recoveryStart. -/
theorem reset_action_exists : ∃ r, recoveryStart p E ≤ p.actionTime r := by
  exact FGCompose.reset_action_exists (p0d6a_timing p) (p0d6a_clock_laws p) (recoveryStart p E)


/-- H.11: the first mathematical action round at or after recoveryStart. -/
noncomputable def resetFirstRound : Nat := Nat.find (reset_action_exists p E)

/-- H.11: the time of the inclusive cut. -/
noncomputable def resetCutTime : Time := p.actionTime (resetFirstRound p E + 2)

private theorem p0d6a_first_eq :
    FGCompose.resetFirstRound (p0d6a_timing p) (p0d6a_clock_laws p) (recoveryStart p E) =
      resetFirstRound p E := rfl

private theorem p0d6a_cut_eq :
    FGCompose.resetCutTime (p0d6a_timing p) (p0d6a_clock_laws p) (recoveryStart p E) =
      resetCutTime p E := rfl

theorem reset_rG_after : recoveryStart p E ≤ p.actionTime (resetFirstRound p E) := by
  exact FGCompose.reset_rG_after (p0d6a_timing p) (p0d6a_clock_laws p) (recoveryStart p E)


theorem reset_rG_first (r : Nat) (hr : recoveryStart p E ≤ p.actionTime r) :
    resetFirstRound p E ≤ r := by
  exact FGCompose.reset_rG_first (p0d6a_timing p) (p0d6a_clock_laws p) (recoveryStart p E) r hr


theorem reset_cut : resetCutTime p E = p.actionTime (resetFirstRound p E + 2) := by
  exact FGCompose.reset_cut (p0d6a_timing p) (p0d6a_clock_laws p) (recoveryStart p E)


/-- H.11: the first action lies in [recoveryStart, recoveryStart + P). -/
theorem reset_first_action_upper :
    p.actionTime (resetFirstRound p E) < recoveryStart p E + P p := by
  exact FGCompose.reset_first_action_upper (p0d6a_timing p) (p0d6a_clock_laws p)
    (recoveryStart p E) (p0d6a_start_nonneg p E)


theorem reset_cut_lower : recoveryStart p E + 2 * P p ≤ resetCutTime p E := by
  exact FGCompose.reset_cut_lower (p0d6a_timing p) (p0d6a_clock_laws p) (recoveryStart p E)


theorem reset_cut_upper : resetCutTime p E < recoveryStart p E + 3 * P p := by
  exact FGCompose.reset_cut_upper (p0d6a_timing p) (p0d6a_clock_laws p)
    (recoveryStart p E) (p0d6a_start_nonneg p E)


variable [DecidableEq V]

private def p0d6a_observations : FGCompose.FGObservationReads (fgsaCoreReads p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private theorem p0d6a_tree_keep : FGCompose.FGTreeKeepLaws (fgsaCoreReads p c) := by
  constructor
  intro nd t
  rw [fgsaCoreReads_def]
  change nd.st.fg.TF ⊆ (acRestart p nd.st t).fg.TF
  rw [acRestart_fg]

private theorem p0d6a_store_inv (i : Nat) (x : V) :
    KitFG.FGStoreInvariant (p0d6a_observations p c).height
      (p0d6a_observations p c).finality
      ((fgsaCoreReads p c).core (V2.D.Run.stateBefore E rho i x)).fg := by
  change KitFG.FGStoreInvariant (heightView p) (finalityView p) _
  rw [fgsaCoreReads_def]
  exact (storeBundle_stateBefore E rho i x).cstore.fg

private theorem p0d6a_row_eq (j : Nat) (y : V) (r : Nat) (a : RowWire p.n) :
    FGCompose.HonestRowAt (fgsaSafetyReads p c) E rho (p0d6a_timing p) j y r a =
      HonestRowAt p c E rho j y r a := by
  rw [fgsaSafetyReads_def]
  rfl

private theorem p0d6a_entry_eq (pair : NamedHeightPair) :
    FGCompose.namedEntry pair = namedEntry pair := by cases pair <;> rfl

private theorem p0d6a_source_eq (x : V) (r : Nat) :
    FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (p0d6a_timing p) x r =
      actionSourceFG p c E rho x r := by
  rw [fgsaCoreReads_def]
  rfl

private theorem p0d6a_old_heights_eq :
    FGCompose.oldRowHeights (fgsaSafetyReads p c) E rho (p0d6a_timing p)
      (fun a => FGCompose.namedEntry a.payload.height_pair) (recoveryStart p E) =
      oldRowHeights p c E rho := by
  unfold FGCompose.oldRowHeights oldRowHeights
  simp only [p0d6a_row_eq, p0d6a_entry_eq]
  rfl

private theorem p0d6a_mu_eq :
    FGCompose.muOf (fgsaSafetyReads p c) E rho (p0d6a_timing p)
      (fun a => FGCompose.namedEntry a.payload.height_pair) (recoveryStart p E) =
      muOf p c E rho := by
  unfold FGCompose.muOf muOf
  rw [p0d6a_old_heights_eq]

/-- H.11: the frozen honest frontier at the cut. -/
noncomputable def resetCutFrontier : Nat := honestFrontier p c E rho (resetCutTime p E)

private theorem p0d6a_honest_frontier_eq (t : Time) :
    FGCompose.honestFrontier (fgsaCoreReads p c) E rho t = honestFrontier p c E rho t := by
  rw [fgsaCoreReads_def]
  rfl

private theorem p0d6a_frontier_eq :
    FGCompose.resetCutFrontier (fgsaCoreReads p c) E rho (p0d6a_timing p)
      (p0d6a_clock_laws p) (recoveryStart p E) = resetCutFrontier p c E rho := by
  unfold FGCompose.resetCutFrontier
  rw [p0d6a_cut_eq, p0d6a_honest_frontier_eq]
  rfl

theorem reset_frontier :
    resetCutFrontier p c E rho = honestFrontier p c E rho (resetCutTime p E) := by
  have h := FGCompose.reset_frontier (p0d6a_timing p) (p0d6a_clock_laws p)
    (recoveryStart p E) (fgsaCoreReads p c) E rho
  rwa [p0d6a_frontier_eq, p0d6a_cut_eq, p0d6a_honest_frontier_eq] at h


/-- C4: the time read includes all simultaneous ticks and deliveries. -/
theorem reset_inclusive_frontier (hs : V2.D.ScheduleWellFormed E rho) (t : Time) :
    honestFrontier p c E rho t = frontierAtIdx p c E rho (timeIdx rho t) := by
  have h := FGCompose.reset_inclusive_frontier (fgsaCoreReads p c) E rho hs t
  change FGCompose.honestFrontier (fgsaCoreReads p c) E rho t =
    FGCompose.frontierAtIdx (fgsaCoreReads p c) E rho (FGCompose.timeIdx rho t) at h
  delta FGCompose.frontierAtIdx at h
  rw [p0d6a_honest_frontier_eq, fgsaCoreReads_def] at h
  exact h


omit [DecidableEq V] in
/-- C1 gap: a cut has a last event at its time exactly when that time occurs
in the finite run. The last index includes every event at that time. -/
theorem reset_inclusive_start_iff (hs : V2.D.ScheduleWellFormed E rho) (t : Time) :
    (∃ start ev, rho.events[start]? = some ev ∧ ev.time = t ∧
      timeIdx rho t = start + 1) ↔ ∃ ev ∈ rho.events, ev.time = t := by
  exact FGCompose.reset_inclusive_start_iff E rho hs t


/-- C2: the actual row source is stored before its action and remains in
the cumulative store at the inclusive cut. INLINE producer: emittedName_window. -/
theorem reset_row_cap (hs : V2.D.ScheduleWellFormed E rho)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    {j r h : Nat} {y : V} {a : RowWire p.n} {e : BlockId} {t u : Time}
    (ha : HonestRowAt p c E rho j y r a) (hj : rho.events[j]? = some (.tick y t))
    (htu : t ≤ u) (he : namedEntry a.payload.height_pair = some (h, e)) :
    h ≤ honestFrontier p c E rho u := by
  have hname : ∀ {j x r a h e},
      FGCompose.HonestRowAt (fgsaSafetyReads p c) E rho (p0d6a_timing p) j x r a →
      FGCompose.namedEntry a.payload.height_pair = some (h, e) → ∃ C,
        FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (p0d6a_timing p) x r =
          some (some C) ∧ h = (heightView p C).h := by
    intro j x r a h e ha he
    have ha' : HonestRowAt p c E rho j x r a := (p0d6a_row_eq p c E rho j x r a) ▸ ha
    have he' : namedEntry a.payload.height_pair = some (h, e) := by
      rwa [p0d6a_entry_eq] at he
    obtain ⟨C, G, hC, hh, _⟩ := emittedName ha' he'
    exact ⟨C, by rwa [p0d6a_source_eq], hh⟩
  have hcap := FGCompose.reset_row_cap (p0d6a_timing p) (fgsaCoreReads p c)
    (fgsaSafetyReads p c) E rho
    (p0d6a_observations p c) (fun a => FGCompose.namedEntry a.payload.height_pair)
    (fgsaCoreLaws p c) (p0d6a_tree_keep p c) (p0d6a_store_inv p c E rho) hs hname
    ((p0d6a_row_eq p c E rho j y r a).symm ▸ ha) hj htu
    (by rw [p0d6a_entry_eq]; exact he)
  rwa [p0d6a_honest_frontier_eq] at hcap


omit [DecidableEq V] in
/-- C3 timing: an old row acts 5Δ after its vote and strictly before u₀. -/
theorem reset_old_row_before_cut {r : Nat}
    (hold : SA.voteTime p.toParams (r * p.R) < recoveryStart p E) :
    p.actionTime r < resetCutTime p E := by
  exact FGCompose.reset_old_row_before_cut (p0d6a_timing p) (p0d6a_clock_laws p)
    (recoveryStart p E) hold


/-- C3 causal part: all old-row heights are bounded by the frozen M.
The result also holds for an empty honest set. -/
theorem reset_old_height_sup_le (hs : V2.D.ScheduleWellFormed E rho)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C)) :
    sSup (oldRowHeights p c E rho) ≤ resetCutFrontier p c E rho := by
  have hname : ∀ {j x r a h e},
      FGCompose.HonestRowAt (fgsaSafetyReads p c) E rho (p0d6a_timing p) j x r a →
      FGCompose.namedEntry a.payload.height_pair = some (h, e) → ∃ C,
        FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (p0d6a_timing p) x r =
          some (some C) ∧ h = (heightView p C).h := by
    intro j x r a h e ha he
    have ha' : HonestRowAt p c E rho j x r a := (p0d6a_row_eq p c E rho j x r a) ▸ ha
    have he' : namedEntry a.payload.height_pair = some (h, e) := by
      rwa [p0d6a_entry_eq] at he
    obtain ⟨C, G, hC, hh, _⟩ := emittedName ha' he'
    exact ⟨C, by rwa [p0d6a_source_eq], hh⟩
  have h := FGCompose.reset_old_height_sup_le (p0d6a_timing p) (p0d6a_clock_laws p)
    (recoveryStart p E)
    (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho (p0d6a_observations p c)
    (fun a => FGCompose.namedEntry a.payload.height_pair) (fgsaCoreLaws p c)
    (p0d6a_tree_keep p c) (p0d6a_store_inv p c E rho) hs hname
  rwa [p0d6a_old_heights_eq, p0d6a_frontier_eq] at h


/-- C3 gap: μ ≤ M holds exactly when the honest set is nonempty.
The permitted standing inputs do not imply this condition. -/
theorem reset_mu_le_iff (hs : V2.D.ScheduleWellFormed E rho)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C)) :
    muOf p c E rho ≤ resetCutFrontier p c E rho ↔ rho.honest.Nonempty := by
  have hname : ∀ {j x r a h e},
      FGCompose.HonestRowAt (fgsaSafetyReads p c) E rho (p0d6a_timing p) j x r a →
      FGCompose.namedEntry a.payload.height_pair = some (h, e) → ∃ C,
        FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (p0d6a_timing p) x r =
          some (some C) ∧ h = (heightView p C).h := by
    intro j x r a h e ha he
    have ha' : HonestRowAt p c E rho j x r a := (p0d6a_row_eq p c E rho j x r a) ▸ ha
    have he' : namedEntry a.payload.height_pair = some (h, e) := by
      rwa [p0d6a_entry_eq] at he
    obtain ⟨C, G, hC, hh, _⟩ := emittedName ha' he'
    exact ⟨C, by rwa [p0d6a_source_eq], hh⟩
  have h := FGCompose.reset_mu_le_iff (p0d6a_timing p) (p0d6a_clock_laws p) (recoveryStart p E)
    (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho (p0d6a_observations p c)
    (fun a => FGCompose.namedEntry a.payload.height_pair) p.E (fgCertificateLaws p).height
    (fgsaCoreLaws p c) (p0d6a_tree_keep p c) (p0d6a_store_inv p c E rho) hs hname
  rwa [p0d6a_mu_eq, p0d6a_frontier_eq] at h


end AvailableChain.FGSA.Run
end
