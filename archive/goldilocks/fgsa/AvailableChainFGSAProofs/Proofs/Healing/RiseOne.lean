module
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseBoot
public import AvailableChainFGSAProofs.Proofs.Healing.OpeningGateRead

public section

/-! S5 H-PHASE M5, plan A steps 1 and 3. The endpoint is inclusive. A rise
keeps its actual event, time and accepted carrier. The other branch supplies
the genesis phase only up to that endpoint. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Plan A step 1 and the horizon boundary. DC: INTENTIONAL an actual first
accepted rise, including its post-event prefix, at or before D. -/
def RiseOneBy (D : Time) : Prop :=
  ∃ i ev, rho.events[i]? = some ev ∧ ev.time ≤ D ∧ i + 1 ≤ timeIdx rho D ∧
    frontierAtIdx p c E rho i = 1 ∧ 2 ≤ frontierAtIdx p c E rho (i + 1) ∧
    EffectiveEvent p c E rho i ∧
    ∃ x W, HeldAt p c E rho (i + 1) x W ∧ 2 ≤ (heightView p W).h

omit [DecidableEq V] in
private theorem rise_one_time_le (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {ev : V2.Event V (Obj p)} (hi : rho.events[i]? = some ev)
    {D : Time} (hD : i < timeIdx rho D) : ev.time ≤ D := by
  have he : rho.events.filter (fun e => decide (e.time < D + 1)) =
      rho.events.filter (fun e => decide (e.time ≤ D)) :=
    List.filter_congr (fun e _ => by simp only [Int.lt_add_one_iff])
  have hiD : i < V2.D.Run.idxBefore rho (D + 1) := by
    rw [V2.D.Run.idxBefore_def, he]
    exact hD
  exact Int.lt_add_one_iff.mp ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi (D + 1)).mp hiD)

/-- Plan A step 6, used only after an accepted frontier witness exists.
DC: SAME PhaseBoot locates the first rise; the bounded adapter retains its
event and time. A carrier can jump above height two. -/
theorem healing_rise_one_of_frontier (hs : V2.D.ScheduleWellFormed E rho)
    (hne : rho.honest.Nonempty) {D : Time}
    (hfront : 2 ≤ frontierAtIdx p c E rho (timeIdx rho D)) :
    RiseOneBy p c E rho D := by
  obtain ⟨i, hi, hf, hf', heff⟩ := healing_phase_first_rise p c E rho hne hfront
  have hil : i < rho.events.length := hi.trans_le (List.length_filter_le _ _)
  obtain ⟨ev, hev⟩ : ∃ ev, rho.events[i]? = some ev :=
    ⟨rho.events[i], List.getElem?_eq_getElem hil⟩
  obtain ⟨x, hx, hmax⟩ := Finset.exists_mem_eq_sup rho.honest hne
    (fun x => (storeAt p c E rho (i + 1) x).fg.h_max)
  obtain ⟨W, hW, hh⟩ := healing_phase_frontier_witness p c E rho (i + 1) x
  have hhigh : 2 ≤ (heightView p W).h := by
    rw [hh, ← hmax]
    exact hf'
  exact ⟨i, ev, hev, rise_one_time_le p c E rho hs hev hi, hi, hf, hf', heff,
    x, W, ⟨hx, hW⟩, hhigh⟩

/-- Plan A step 1. DC: SAME monotonicity and positive store height give
frontier one at every prefix before the bounded endpoint with no rise. -/
theorem healing_rise_one_frontier (hs : V2.D.ScheduleWellFormed E rho)
    (mono : RMonoAll p c E rho) (hne : rho.honest.Nonempty) {D : Time}
    (hstop : ¬ RiseOneBy p c E rho D) {i : Nat} (hi : i ≤ timeIdx rho D) :
    frontierAtIdx p c E rho i = 1 := by
  have hcap : frontierAtIdx p c E rho (timeIdx rho D) < 2 := by
    by_contra hn
    exact hstop (healing_rise_one_of_frontier p c E rho hs hne (by omega))
  have hlo := (healing_phase_initial_frontier p c E rho hne).symm ▸
    healing_frontier_mono_all p c E rho mono (Nat.zero_le i)
  have hhi := (healing_frontier_mono_all p c E rho mono hi).trans_lt hcap
  omega

/-- Plan A step 1. DC: INTENTIONAL the no-rise branch uses the strict lower
cut and the inclusive endpoint; it never crosses a known rise. -/
theorem healing_rise_one_phase (hs : V2.D.ScheduleWellFormed E rho)
    (mono : RMonoAll p c E rho) (hne : rho.honest.Nonempty) {u D : Time}
    (huD : u ≤ D) (hD : D ≤ rho.horizon) (hstop : ¬ RiseOneBy p c E rho D) :
    PhaseInterval p c E rho u D 1 (some .genesis) false := by
  exact boot_phase_one p c E rho huD hD (fun i _ hi =>
    healing_rise_one_frontier p c E rho hs mono hne hstop hi)

/-- Plan A step 1. DC: INTENTIONAL the bounded split needs no honest
proposal, repair budget or settlement interval after D. -/
theorem healing_rise_one_split (hs : V2.D.ScheduleWellFormed E rho)
    (mono : RMonoAll p c E rho) (hne : rho.honest.Nonempty) {u D : Time}
    (huD : u ≤ D) (hD : D ≤ rho.horizon) :
    RiseOneBy p c E rho D ∨ PhaseInterval p c E rho u D 1 (some .genesis) false := by
  classical
  by_cases h : RiseOneBy p c E rho D
  · exact Or.inl h
  · exact Or.inr (healing_rise_one_phase p c E rho hs mono hne huD hD h)

/-- Plan A step 3. DC: SAME every height-one FG block has genesis entry.
The height-zero alternative is excluded by FGHeightLaws.one_le_h. -/
theorem healing_rise_one_entry (K : FGBlock (Fin p.n))
    (hK : (heightView p K).h = 1) : (heightView p K).T_h = .genesis := by
  have hlaws := (fgCertificateLaws p).height
  have hg := hlaws.h_mono (KitFG.genesis_preceq K)
  have hg1 : (heightView p .genesis).h = (heightView p K).h :=
    le_antisymm hg (hK ▸ hlaws.one_le_h _)
  have hplateau := hlaws.entry_plateau (KitFG.genesis_preceq K) hg1
  exact hplateau.symm

/-- Plan A step 3. DC: SAME the actual accepted gate copy recovers Qfg.
No supplied block identity is trusted without erasure injectivity. -/
theorem healing_rise_one_gate_copy (hs : V2.D.ScheduleWellFormed E rho)
    {q : Nat} {Q : Block} (hexact : ExactService p c E rho q Q)
    (hgate : SA.gateTime p.toParams q ≤ rho.horizon) {x : V} (hx : x ∈ rho.honest)
    (hReader : confirmedReaderAtIdx p c E rho x
      (afterTicksIdx rho (SA.gateTime p.toParams q)) (SA.gateTime p.toParams q)) :
    ∃ j Qfg, IsGateTick p c rho j x q ∧
      Qfg ∈ (storeAt p c E rho j x).fg.TF ∧ eraseFG Qfg = Q := by
  obtain ⟨j, ⟨hj, _⟩, _⟩ := (hexact.2 hgate x hx hReader).2.1
  obtain ⟨nd, hnd, hw⟩ := (hexact.2 hgate x hx hReader).2.2.1
  have hclock := (healing_support_gate_reads p c E rho hs hj).2
  have he := Option.some.inj (hnd.symm.trans hclock)
  subst nd
  obtain ⟨_, _, _, hm, _⟩ := opening_fastWrite_spec E rho hs hj hw
  have hb : Q ∈ (storeAt p c E rho j x).base.blocks := by
    have h := ((actView_blocks _ Q).mp hm).1
    rwa [(clockPre_fields p _ _).2.1] at h
  obtain ⟨Qfg, hQfg, heq⟩ := ((cstoreInv_stateBefore E rho j x).baseTree Q).mp hb
  exact ⟨j, Qfg, hj, hQfg, heq⟩

/-- Plan A step 3. DC: SAME identify an explicitly supplied Qfg with the
accepted copy, then use height positivity or the actual stopping rise. -/
theorem healing_rise_one_height (hs : V2.D.ScheduleWellFormed E rho)
    (mono : RMonoAll p c E rho) {q : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q) (hQfg : eraseFG Qfg = Q)
    (hexact : ExactService p c E rho q Q) {D : Time}
    (hgate : SA.gateTime p.toParams q ≤ D) (hD : D ≤ rho.horizon)
    (hReaders : ∀ x ∈ rho.honest, confirmedReaderAtIdx p c E rho x
      (afterTicksIdx rho (SA.gateTime p.toParams q)) (SA.gateTime p.toParams q)) :
    RiseOneBy p c E rho D ∨
      ((heightView p Qfg).h = 1 ∧ (heightView p Qfg).T_h = .genesis) := by
  obtain ⟨x, hx⟩ : rho.honest.Nonempty := ⟨_, hQ.1.2⟩
  obtain ⟨j, K, hj, hK, heK⟩ := healing_rise_one_gate_copy p c E rho hs hexact
    (hgate.trans hD) hx (hReaders x hx)
  have he : K = Qfg := eraseFG_injective (heK.trans hQfg.symm)
  subst K
  have hjD := (healing_phase_lt_timeIdx p c E rho hs hj hgate).le
  by_cases hh : 2 ≤ (heightView p Qfg).h
  · left
    exact healing_rise_one_of_frontier p c E rho hs ⟨x, hx⟩
      (hh.trans ((healing_phase_height_le p c E rho hK).trans
        ((healing_phase_local_le_frontier p c E rho hx).trans
          (healing_frontier_mono_all p c E rho mono hjD))))
  · have h1 : (heightView p Qfg).h = 1 := by
      exact Nat.le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_le hh))
        ((fgCertificateLaws p).height.one_le_h Qfg)
    exact Or.inr ⟨h1, healing_rise_one_entry p Qfg h1⟩

/-- Plan A step 5, receipt only. DC: SAME the exact covered row, including
an earlier suppressed send, reaches every honest receiver before a_r+DeltaF.
INLINE receipt: Assembly supplies fgsa_tRowsReceipt. Row receipt alone does
not establish a matching parent progress bit or height-two acceptance. -/
theorem healing_rise_one_rows_received (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) {ΔF : Time} (receipt : TRowsReceipt p c E rho ΔF)
    {r : Nat} {Q : Block} (hgst : E.t_GST ≤ p.actionTime r)
    (hhor : p.actionTime r + ΔF ≤ rho.horizon)
    (hcovered : OpeningCovered p c E rho r Q) (hentry : OpeningEntry p c E rho r 1) :
    ∀ x ∈ rho.honest, ∃ K j rSent a,
      actionSourceFG p c E rho x r = some (some K) ∧ rSent ≤ r ∧
      HonestRowAt p c E rho j x rSent a ∧
      namedEntry a.payload.height_pair = some (1, (FGBlock.genesis : FGBlock (Fin p.n)).root) ∧
      ∀ z ∈ rho.honest, HeldBefore p c E rho z a (p.actionTime r + ΔF) := by
  obtain ⟨e, he⟩ := hentry
  intro x hx
  obtain ⟨K, nd, j, rSent, a, _hnd, hK, _hfull, _hQK, hr, ha, hn⟩ := hcovered x hx
  have hK1 := (he x K hx hK).1
  have hT := healing_rise_one_entry p K hK1
  have hat : p.actionTime rSent ≤ p.actionTime r := by
    have hrR := Nat.mul_le_mul_right p.R hr
    have hrI : ((rSent * p.R : Nat) : Int) ≤ ((r * p.R : Nat) : Int) := by
      exact_mod_cast hrR
    change 4 * p.Δ * ((rSent * p.R : Nat) : Int) + 6 * p.Δ ≤
      4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    nlinarith [p.deltaPos]
  refine ⟨K, j, rSent, a, hK, hr, ha, ?_, ?_⟩
  · rwa [hK1, hT] at hn
  · intro z hz
    exact healing_phase_receipt p c E rho ΔF hs hnr receipt ha hat hgst hhor hz

end AvailableChain.FGSA.Run
end
