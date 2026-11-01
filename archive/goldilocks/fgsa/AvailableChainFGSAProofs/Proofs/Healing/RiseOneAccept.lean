module
public import AvailableChainFGSAProofs.Proofs.Healing.RiseOne
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionReceipt -- shake: keep
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionPhase

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1236–1237, 1467–1468; S5 M5b B2.
DC: SAME an effective event at or before D excludes the stopped genesis phase.
The result retains M1's actual first rise and accepted carrier. -/
theorem healing_rise_one_of_effective (hs : V2.D.ScheduleWellFormed E rho)
    (mono : RMonoAll p c E rho) (hne : rho.honest.Nonempty)
    {i : Nat} {ev : V2.Event V (Obj p)} {D : Time}
    (hi : rho.events[i]? = some ev) (ht : ev.time ≤ D)
    (heff : EffectiveEvent p c E rho i) : RiseOneBy p c E rho D := by
  by_contra hstop
  have hcut := healing_phase_lt_timeIdx p c E rho hs hi ht
  have hf : frontierAtIdx p c E rho (i + 1) = 1 :=
    healing_rise_one_frontier p c E rho hs mono hne hstop (Nat.succ_le_of_lt hcut)
  have hi1 : frontierAtIdx p c E rho i = 1 :=
    healing_rise_one_frontier p c E rho hs mono hne hstop hcut.le
  obtain ⟨x, hx⟩ := hne
  have htop : TopEvidence p c E rho i 1 :=
    ⟨x, hx, by
      have hJ := (boot_height_one p c E rho hx hi1).2.1
      change (storeAt p c E rho i x).fg.h_j = 0 at hJ
      rw [hJ]⟩
  rcases heff with hrise | heff
  · omega
  · rw [hf] at heff
    rcases heff with ⟨hnt, _⟩ | ⟨_, y, hy, _, hcy⟩
    · exact hnt htop
    · rw [(boot_height_one p c E rho hy hf).2.2.2.1] at hcy
      contradiction

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1236–1237, 1467–1468; S5 M5b step 6.
DC: SAME an actual accepted certificate supplies the frontier witness for M1.
The strict receipt cut can be the finite horizon. -/
theorem healing_rise_one_of_receipt (hs : V2.D.ScheduleWellFormed E rho)
    (mono : RMonoAll p c E rho) {x : V} {X : FGBlock (Fin p.n)} {d D : Time}
    (hx : x ∈ rho.honest) (hh : 2 ≤ (heightView p X).h)
    (hheld : Gen.V2.Duty.HoldsBefore E rho (fun nd => X ∈ nd.st.fg.TF) d x)
    (hd : d ≤ D) : RiseOneBy p c E rho D := by
  change X ∈ (V2.D.Run.stateBeforeTime E rho d x).st.fg.TF at hheld
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hs] at hheld
  exact healing_rise_one_of_frontier p c E rho hs ⟨x, hx⟩
    (hh.trans ((healing_phase_height_le p c E rho hheld).trans
      ((healing_phase_local_le_frontier p c E rho hx).trans
        (healing_frontier_mono_all p c E rho mono (healing_phase_idx_le_time p c rho hd)))))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:1410–1419, 1467–1468; S5 M5b B2.
DC: SAME r3 supplies the first honest receipt. In the genesis top-J phase,
each honest receiver has an F path to genesis, so the same signed proposal
is stored strictly before its deadline by every honest receiver. -/
theorem healing_rise_one_receipt_all [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (crossing : RXing p c E rho)
    {u : Time} {s : Slot} {X : FGBlock (Fin p.n)}
    (services : ∀ ip v (N : NamedProposal p.n) x, v ∈ rho.honest → x ∈ rho.honest →
      rho.events[ip]? = some (.tick v (SA.proposalTime p.toParams s)) →
      ofWire p ⟨.proposer s, .proposal N⟩ ∈ rho.emitsAt E ip →
      E.t_GST ≤ SA.proposalTime p.toParams s →
      SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon →
      Block.Compatible N.erase (eraseFG (rho.stateBeforeTime E
        (SA.proposalTime p.toParams s + p.Δ) x).st.fg.F) →
      Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
        (SA.proposalTime p.toParams s) (SA.proposalTime p.toParams s + p.Δ) x))
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X))
    (hu : u ≤ SA.proposalTime p.toParams s) (hready : recoveryStart p E ≤ u)
    (hp : PhaseInterval p c E rho u (SA.proposalTime p.toParams s + p.Δ) 1
      (some .genesis) false) :
    ∀ x ∈ rho.honest, Gen.V2.Duty.HoldsBefore E rho
      (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) x := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  classical
  intro x hx
  let t := SA.proposalTime p.toParams s
  let d := t + p.Δ
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨ip, N, heN, hip, hem, _⟩ :=
    healing_promotion_proposal_read p c E rho hs hnew
  let jd := V2.D.Run.idxBefore rho d
  have hujd : V2.D.Run.idxBefore rho u ≤ jd :=
    healing_phase_idxBefore_mono p c rho (by dsimp only [d, t]; linarith [p.deltaPos])
  obtain ⟨hH, _, _⟩ := hp.2.2.2 jd x hujd
    (healing_phase_idx_le_time p c rho le_rfl) hx
  have hFgen := (healing_phase_frontier_root p c E rho crossing hx
    (storeBundle_stateBefore E rho jd x).cstore.fg.gen
    (show (heightView p .genesis).h = (R_at p c E rho jd x).H from hH.symm)).1
  have hcompat : Block.Compatible (eraseFG X)
      (eraseFG (V2.D.Run.stateBeforeTime E rho d x).st.fg.F) := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hs]
    exact Bool.or_eq_true_iff.mpr (Or.inr (eraseFG_preceq
      (KitFG.preceq_trans hFgen (KitFG.genesis_preceq X))))
  obtain ⟨service⟩ := services ip _ N x hnew.1.2 hx hip hem (hGST.trans hu)
    hp.2.1 (by simpa only [heN] using hcompat)
  obtain ⟨Y, hY, he⟩ := service.proposal hs hx hrec.base.receiptIdealization
  have heq : Y = X := eraseFG_injective (he.trans heN)
  rw [heq] at hY
  exact hY

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1410–1419, 1467–1468; S5 M5b B2.
DC: SAME the inclusive r3 event split covers an event at the receipt deadline.
An earlier rise also ends this item. Only the no-rise arm uses the genesis
phase through the strict receipt cut; no phase is asserted after a rise. -/
theorem healing_rise_one_accept [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (crossing : RXing p c E rho)
    {u D : Time} {s : Slot} {X : FGBlock (Fin p.n)}
    (services : ∀ ip v (N : NamedProposal p.n) x, v ∈ rho.honest → x ∈ rho.honest →
      rho.events[ip]? = some (.tick v (SA.proposalTime p.toParams s)) →
      ofWire p ⟨.proposer s, .proposal N⟩ ∈ rho.emitsAt E ip →
      E.t_GST ≤ SA.proposalTime p.toParams s →
      SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon →
      Block.Compatible N.erase (eraseFG (rho.stateBeforeTime E
        (SA.proposalTime p.toParams s + p.Δ) x).st.fg.F) →
      Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
        (SA.proposalTime p.toParams s) (SA.proposalTime p.toParams s + p.Δ) x))
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X))
    (hu : u ≤ SA.proposalTime p.toParams s) (hready : recoveryStart p E ≤ u)
    (hd : SA.proposalTime p.toParams s + p.Δ ≤ D) (hD : D ≤ rho.horizon) :
    RiseOneBy p c E rho D ∨
      ∀ x ∈ rho.honest, Gen.V2.Duty.HoldsBefore E rho
        (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) x := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  classical
  have hs := hrec.base.valid.toScheduleWellFormed
  have hne : rho.honest.Nonempty := ⟨_, hnew.1.2⟩
  rcases healing_promotion_event_split p c E rho hs u D with
    ⟨i, ev, _, hi, heff, ht, _⟩ | _hquiet
  · exact Or.inl (healing_rise_one_of_effective p c E rho hs mono hne hi ht heff)
  by_cases hrise : RiseOneBy p c E rho D
  · exact Or.inl hrise
  have hcut : timeIdx rho (SA.proposalTime p.toParams s + p.Δ) ≤ timeIdx rho D := by
    change (rho.events.filter (fun e => decide (e.time ≤ _))).length ≤
      (rho.events.filter (fun e => decide (e.time ≤ D))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he => decide_eq_true
      ((of_decide_eq_true he).trans hd))
  have hp := boot_phase_one p c E rho
    (show u ≤ SA.proposalTime p.toParams s + p.Δ by linarith [p.deltaPos]) (hd.trans hD)
    (fun i _ hi => healing_rise_one_frontier p c E rho hs mono hne
      hrise (hi.trans hcut))
  exact Or.inr (healing_rise_one_receipt_all p c E rho hrec crossing services hnew hu hready hp)

end AvailableChain.FGSA.Run
end
