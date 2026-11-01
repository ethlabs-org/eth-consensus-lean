module
public import AvailableChainFGSAProofs.Proofs.Healing.ResetCut
public import AvailableChainFGSAProofs.Proofs.Foundations.Sources

set_option linter.privateModule false

public section

namespace AvailableChain.FGSA.Run.Tests.P0d6a
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private def d6f_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private def d6f_obs : FGCompose.FGObservationReads (fgsaCoreReads p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private theorem d6f_restore_keep : FGCompose.FGTreeKeepLaws (fgsaCoreReads p c) := by
  constructor
  intro nd t
  rw [fgsaCoreReads_def]
  change nd.st.fg.TF ⊆ (acRestart p nd.st t).fg.TF
  rw [acRestart_fg]

private theorem d6f_decoded_entry (a : RowWire p.n) {row : Row (Fin p.n)}
    (h : a.toRow? = some row) :
    FGCompose.namedEntry row.height_pair = namedEntry a.payload.height_pair := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => simp [RowWire.toRow?, RowWire.decode?] at h
  | proposer s => simp [RowWire.toRow?, RowWire.decode?] at h
  | seat label i =>
    cases label with
    | head s => simp [RowWire.toRow?, RowWire.decode?] at h
    | fg =>
      have hr : payload.toRow i = row := by
        simpa [RowWire.toRow?, RowWire.decode?] using h
      rw [← hr]
      cases payload with
      | vote body => cases body.height_pair <;> rfl

-- The real foundation producer supplies this leaf; its gate and fastAt fields are discarded.
private theorem d6f_source_only (hs : V2.D.ScheduleWellFormed E rho) :
    ∀ {j x r a h e},
      FGCompose.HonestRowAt (fgsaSafetyReads p c) E rho (d6f_timing p) j x r a →
      FGCompose.namedEntry a.payload.height_pair = some (h, e) → ∃ C,
        FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (d6f_timing p) x r =
          some (some C) ∧ h = (heightView p C).h := by
  intro j x r a h e ha he
  have ha' : HonestRowAt p c E rho j x r a := by
    rw [fgsaSafetyReads_def] at ha
    exact ha
  have he' : namedEntry a.payload.height_pair = some (h, e) := by
    cases pair : a.payload.height_pair with
    | empty => simp [FGCompose.namedEntry, pair] at he
    | vote h e b => simpa [FGCompose.namedEntry, namedEntry, pair] using he
  obtain ⟨C, G, hC, hh, _⟩ := emittedName_window p c E rho hs ha' he'
  refine ⟨C, ?_, hh⟩
  rw [fgsaCoreReads_def]
  exact hC

private theorem d6f_generic_cap (hs : V2.D.ScheduleWellFormed E rho)
    {j r h : Nat} {y : V} {a : RowWire p.n} {e : BlockId} {t : Time}
    (ha : HonestRowAt p c E rho j y r a) (hj : rho.events[j]? = some (.tick y t))
    (he : namedEntry a.payload.height_pair = some (h, e)) :
    h ≤ honestFrontier p c E rho t := by
  have hcap := FGCompose.reset_row_cap (d6f_timing p) (fgsaCoreReads p c) (fgsaSafetyReads p c)
    E rho (d6f_obs p c) (fun a => FGCompose.namedEntry a.payload.height_pair)
    (fgsaCoreLaws p c) (d6f_restore_keep p c)
    (fun i x => by
      change KitFG.FGStoreInvariant (heightView p) (finalityView p) _
      rw [fgsaCoreReads_def]
      exact (storeBundle_stateBefore E rho i x).cstore.fg) hs
    (d6f_source_only p c E rho hs)
    (by rw [fgsaSafetyReads_def]; exact ha) hj le_rfl
    (by cases pair : a.payload.height_pair with
        | empty => simp [namedEntry, pair] at he
        | vote h e b => simpa [FGCompose.namedEntry, namedEntry, pair] using he)
  rw [FGCompose.honestFrontier, fgsaCoreReads_def] at hcap
  exact hcap

private theorem d6f_mu_uses_real_source (hs : V2.D.ScheduleWellFormed E rho) :
    muOf p c E rho ≤ resetCutFrontier p c E rho ↔ rho.honest.Nonempty :=
  reset_mu_le_iff p c E rho hs (emittedName_window p c E rho hs)

#print axioms d6f_restore_keep
#print axioms d6f_decoded_entry
#print axioms d6f_source_only
#print axioms d6f_generic_cap
#print axioms d6f_mu_uses_real_source
#print axioms AvailableChain.FGSA.Run.reset_period_lower
#print axioms AvailableChain.FGSA.Run.reset_action_exists
#print axioms AvailableChain.FGSA.Run.reset_rG_after
#print axioms AvailableChain.FGSA.Run.reset_rG_first
#print axioms AvailableChain.FGSA.Run.reset_cut
#print axioms AvailableChain.FGSA.Run.reset_first_action_upper
#print axioms AvailableChain.FGSA.Run.reset_cut_lower
#print axioms AvailableChain.FGSA.Run.reset_cut_upper
#print axioms AvailableChain.FGSA.Run.reset_frontier
#print axioms AvailableChain.FGSA.Run.reset_inclusive_frontier
#print axioms AvailableChain.FGSA.Run.reset_inclusive_start_iff
#print axioms AvailableChain.FGSA.Run.reset_row_cap
#print axioms AvailableChain.FGSA.Run.reset_old_row_before_cut
#print axioms AvailableChain.FGSA.Run.reset_old_height_sup_le
#print axioms AvailableChain.FGSA.Run.reset_mu_le_iff

end AvailableChain.FGSA.Run.Tests.P0d6a
end
