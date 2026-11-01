module
public import AvailableChainFGSAProofs.Proofs.Clean.State
public import AvailableChainFGSAProofs.Proofs.Clean.Frame
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSAProofs.Proofs.Shared.Channels

public section

/-! P3 §§8.4, 8.7; bp02 §5.6. Independent action substep. -/
namespace AvailableChain.FGSA.Run

variable {ΔF : Time}
open AvailableChain.SimplexFG
variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem action_row_payload (hv : V2.D.ExecutionValid E rho)
    {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j x r a) :
    rho.events[j]? = some (.tick x (p.actionTime r)) ∧
      (attest p
        ((fgsa p c).clock (V2.D.Run.stateBefore E rho j x) (p.actionTime r)).st
        (V2.D.Run.stateBefore E rho j x).record ⟨0, p.nPos⟩).1 = some a.payload := by
  obtain ⟨seat, har⟩ := honestRow_auth p c rho E hv ha
  obtain ⟨_, hj, hem⟩ := ha
  rcases a with ⟨auth, body⟩
  dsimp only at har
  subst auth
  obtain ⟨_, _, _, _, hb⟩ := (fgsa_emitsAt_row E rho j x _ hj seat body).mp hem
  exact ⟨hj, hb⟩

/-- P3 §§8.4, 8.7; bp02 §5.6. Class B, local action preservation.
DC counterpart: none exact; Execution/WeakGenesisGSTZeroActionSources.lean
has action-source order facts. FG-SA emits a row after the gate in one tick.
The proof uses the given prior state and completed history directly.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_actionStep [Fintype V] {b₀ : Time} : CleanActionStep (ΔF := ΔF) p c E rho b₀ := by
  rw [CleanActionStep_def (ΔF := ΔF)]
  intro h _ _ _ i _ _ _ _ hh hstate
  rw [CleanRowSources_def]
  intro j x r a e hj ha he
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hji | hji
  · have hold := hstate.sources.1
    rw [CleanRowSources_def] at hold
    obtain ⟨C, hc, heq, hp, hb⟩ := hold j x r a e hji ha he
    exact ⟨C, hc, heq, hp, belowLabel_mono_index (Nat.le_succ i) hb⟩
  subst j
  have hs := h.base.valid.toScheduleWellFormed
  obtain ⟨hj, hb⟩ := action_row_payload p c E rho h.base.valid ha
  let nd := V2.D.Run.stateBefore E rho i x
  let st := ((fgsa p c).clock nd (p.actionTime r)).st
  obtain ⟨row, hrow, hbody⟩ := Option.map_eq_some_iff.mp hb
  obtain ⟨h, root, tm, hp, hroweq, _, _, _⟩ :=
    KitFG.createRowOnce_released p.E p.cfg nd.record ⟨0, p.nPos⟩
      (fgInputs p st).1 (fgInputs p st).2 hrow
  have hn : namedEntry (.vote h root tm) = some e := by
    rw [← hbody, hroweq] at he
    exact he
  have hfields := KitFG.height_pair_vote_fields hp
  change Option.map (fun C => ((derive p.E p.cfg C).h, (derive p.E p.cfg C).T_h.root))
    (fgSource p st) = some (h, root) at hfields
  cases hsrc : fgSource p st with
  | none => rw [hsrc] at hfields; cases hfields
  | some C =>
    have hpair : ((derive p.E p.cfg C).h, (derive p.E p.cfg C).T_h.root) = (h, root) := by
      exact Option.some.inj (by simpa only [hsrc, Option.map_some] using hfields)
    have heq : e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) := by
      exact (Option.some.inj hn).symm.trans hpair.symm
    have hread : actionSourceFG p c E rho x r = some (some C) := by
      rw [actionSourceFG_eq_round p c E rho hs hj]
      have hr := (fgsa_action_slot_round (p := p) (c := c) nd r).2
      change fgSource p st = some C at hsrc
      change some (deepest _) = some (some C)
      change deepest _ = some C at hsrc
      rw [hr] at hsrc
      exact congrArg some hsrc
    have hmem : eraseFG C ∈ sourceCandidates p st := by
      rw [fgSource_eq_jointSource] at hsrc
      exact of_decide_eq_true (Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ hsrc).1).2
    have hfw : eraseFG C ∈ (fastWriteAt st (r * p.R)).getD [] := by
      rw [sourceCandidates_def] at hmem
      have hm := (Finset.mem_filter.mp hmem).1
      rw [(fgsa_action_slot_round (c := c) nd r).2] at hm
      exact List.mem_toFinset.mp hm
    have hst : storeAt p c E rho (i + 1) x = st := by
      change (V2.D.Run.stateBefore E rho (i + 1) x).st = st
      rw [(V2.D.Run.step_tick_eq E rho hj).1]
      exact tick_st (p := p) (c := c) E rho _ _ _
    have ht : IsGateTick p c rho i x (r * p.R) := hj
    rw [← hst] at hfw
    obtain ⟨k, hk, hRF, hkt, _, G, hG, hCG, _⟩ :=
      clean_gate_fastWrite hs (Nat.lt_succ_self i) hh hstate ht _ _ hfw
    exact ⟨C, hread, heq, KitFG.entry_preceq p.E p.cfg C,
      belowLabel_of_preceq hCG (belowLabel_of_gateResultAt hs hk hkt.1 hG (Nat.le_refl _))⟩

/-- P3 §8.4; bp02 §§5.5–5.6. Class B, frozen gate state step.
DC counterpart: none; the FG-SA gate and action share one tick.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_gateStateStep [Fintype V] {b₀ : Time} :
    CleanGateStateStep (ΔF := ΔF) p c E rho b₀ :=
  clean_gateStateStep_of_action (clean_actionStep p c E rho)

/-- P3 §8.2, §8.7 and S2 (5142–5165); bp02 §5.5. Class B.
DC counterpart: Generic/Properties.lean:41, MonotoneFrom. This internal
form uses all nodes and event indices under a fixed completed history.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem sExtends_upTo [Fintype V] {b₀ : Time} {i : Nat}
    (h : CleanCutSet p c E rho b₀ ΔF) (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (hi : i ≤ timeIdx rho b₀) (hh : CleanHist p c E rho i) :
    ∀ v j k, j ≤ k → k ≤ i →
      Block.Preceq (S_at p c E rho j v) (S_at p c E rho k v) :=
  sExtends_upTo_of_action h hq hf hsrc (clean_actionStep p c E rho) hi hh

/-- P3 §8.7 F2.2/F2.6; bp02 §§3.3–3.4, §5.6. Class B, frozen frame.
DC counterparts: ChainState/FGRootWitness.lean:327,493 and
ChainState/Chain.lean:414,447,460,475. The FG-SA contest/domain bundle
has no exact DC counterpart; the given-state core documents its geometry.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanFrame [Fintype V] {b₀ : Time} : CleanFrameStmt (ΔF := ΔF) p c E rho b₀ := by
  rw [CleanFrameStmt_def (ΔF := ΔF)]
  intro h hq hf hsrc i hi hh
  exact cleanFrame_of_state p c E rho b₀ h hq hf hsrc i hi hh
    (cleanState_of_hist h hq hf hsrc (clean_actionStep p c E rho) hi hh)

end AvailableChain.FGSA.Run
end
