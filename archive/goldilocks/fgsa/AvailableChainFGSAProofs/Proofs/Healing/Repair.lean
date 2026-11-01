module
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthProposal
public import AvailableChainFGSAProofs.Proofs.Healing.RepairGate
public import AvailableChainFGSAProofs.Proofs.Healing.RepairH6S

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryService

public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryProducers

public section

/-! H-REPAIR (plan steps 1, 7, 10–13; blueprint 21 H.6:910–986, H.6-S:988–1052). The two
repair branches and `healing_tRepair : TRepair`. Recovery₂ is a standing hypothesis (plan
Gap 1); the other hypotheses are RMono, RXing, RQCOrigin and the inline last-write premise
(ruling B27). TRepair quantifies its own gap G; only its ProposalGap is used. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure RetainedWalk

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Bounded local services for repaired proposals and their enabled gates. -/
structure RepairServiceScopes (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Prop where
  permanence : ∀ u v m J contested, recoveryStart p E ≤ u →
    PhaseInterval p c E rho u v m J contested →
    SupportPermanenceServices E rho u v m J contested
  heads : ∀ (s : Slot) ip x N, E.t_GST ≤ slotStartZ p ((s : Int) - 2) → x ∈ rho.honest →
    rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
    (ofWire p ⟨.proposer s, .proposal N⟩) ∈ rho.emitsAt E ip →
    SA.voteTime p.toParams s ≤ rho.horizon → RepairHeadServices E rho s ip x N
  gates : ∀ (s : Slot), E.t_GST ≤ slotStartZ p ((s : Int) - 1) →
    SA.gateTime p.toParams s ≤ rho.horizon → RepairGateScope E rho s

/-- Recovery produces the bounded repair services at each actual read. -/
theorem healing_repair_service_scopes_recovery [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) : RepairServiceScopes E rho := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v m J contested hready hphase
    exact healing_support_permanence_recovery E rho hrec mono hready hphase
  · intro s ip x N hcut hx hip hem _
    exact healing_repair_head_services_recovery E rho hrec mono
      (healing_window_of_cut E hcut) hx hip hem
  · intro s hcut _
    exact healing_repair_gate_scope_recovery E rho hrec mono (healing_window_of_cut E hcut)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Plan H-REPAIR step 11 (HonestSlot → HonestProposal); Run/Emission.lean:72.
DC: INTENTIONAL the honest proposer of a post-GST slot inside the horizon ticks at t_s
(tick totality), is awake (Recovery₂) and emits its proposal (s ≠ 0). -/
theorem repair_honest_proposal [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot}
    (hs : Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s)
    (hgst : E.t_GST ≤ SA.proposalTime p.toParams s)
    (hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1))
    (hh : SA.proposalTime p.toParams s ≤ rho.horizon) :
    ∃ Q, HonestProposal E rho (fgsaInterface p c) s Q := by
  obtain ⟨Q, hQ, _⟩ := fgsa_honestProposal_exists_of_awake_slot E rho
    hrec.base.valid.toScheduleWellFormed hrec.base.delta hs
    (hrec.awake _ hs.2 _ hgst hh)
    (healing_recovery_restart_cutoff hrec hs.2 hh hcut) hh
  exact ⟨Q, hQ⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan H-REPAIR step 11. DC: INTENTIONAL GUP r2 uses the rounded-up gap. -/
theorem repair_grid_Γ {Gp : Time} {l s : Nat}
    (hs : SA.proposalTime p.toParams s ≤ SA.proposalTime p.toParams l + Gp) :
    SA.proposalTime p.toParams s ≤ SA.proposalTime p.toParams l + Γ p Gp := by
  linarith [(fgsa_gamma_bounds p Gp).1]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan H-REPAIR step 11. DC: INTENTIONAL GUP r2 has G ≤ Γ. -/
theorem repair_lt_Γ (Gp : Time) : Gp < Γ p Gp + 4 * p.Δ := by
  have := (fgsa_gamma_bounds p Gp).1
  linarith [p.deltaPos]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:965–986; plan H-REPAIR steps 9–10. DC: INTENTIONAL exact gate service of
an honest proposal of slot r + 1 inside the phase, from the lease cover of its preceding
HEAD batch (u ≤ v_r) and the gate geometry. -/
theorem repair_exact_service [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    (services : RepairServiceScopes E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {r : Nat} (hhead : u ≤ slotStartZ p (r : Int))
    (hPriorCut : E.t_GST ≤ slotStartZ p ((r : Int) - 1))
    (hlease : RepairLeaseCover E rho (r + 1))
    (hgate : SA.gateTime p.toParams (r + 1) ≤ v) {Q : Block}
    (hp : HonestProposal E rho (fgsaInterface p c) (r + 1) Q) :
    ExactService p c E rho (r + 1) Q := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hd := p.deltaPos
  have hvq : SA.voteTime p.toParams (r + 1) ≤ v := by
    refine le_trans ?_ hgate
    change 4 * p.Δ * ((r + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int) + 6 * p.Δ
    linarith
  have hus : u ≤ SA.voteTime p.toParams (r + 1) := by
    refine hhead.trans ?_
    change 4 * p.Δ * (r : Int) ≤ 4 * p.Δ * ((r + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hQs := repair_proposal_slot E rho hp
  have hheadVote : u ≤ SA.voteTime p.toParams r := by
    change u ≤ 4 * p.Δ * (r : Int) + p.Δ
    change u ≤ 4 * p.Δ * (r : Int) at hhead
    linarith
  have hcut : E.t_GST ≤ slotStartZ p (((r + 1 : Nat) : Int) - 1) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hGST.trans hhead
  have hhor : SA.voteTime p.toParams (r + 1) ≤ rho.horizon := hvq.trans hphase.2.1
  obtain ⟨ip, x, N, heN, hx, hip, hseat, hem⟩ := repair_proposal_emission E rho hp
  have hHeads := services.heads (r + 1) ip x N (by
    have he : ((r + 1 : Nat) : Int) - 2 = (r : Int) - 1 := by push_cast; omega
    simpa only [he] using hPriorCut) hx hip hem hhor
  have hPrior : ProposalSupportScope E rho ip x r (SA.proposalTime p.toParams (r + 1)) := by
    simpa only [Nat.add_sub_cancel] using hHeads.prior
  have hProposalSync : E.t_GST ≤ SA.proposalTime p.toParams (r + 1) - p.Δ := by
    refine hGST.trans (hheadVote.trans ?_)
    change 4 * p.Δ * (r : Int) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int) - p.Δ
    push_cast
    linarith
  have hCut : HealingWindow p E 1 r :=
    healing_window_of_cut E (healing_ready_vote_cutoff E (hready.trans hheadVote))
  have hFloors : ∀ y ∈ rho.honest, Block.Preceq
      (eraseFG (rho.stateBeforeTime E (SA.voteTime p.toParams (r + 1)) y).st.fg.F)
      N.erase := by
    intro y hy
    rw [heN]
    exact healing_proposal_phase_reader_floor hrec.base.valid crossing hphase hp
      (hhead.trans (by
        change 4 * p.Δ * (r : Int) ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
        push_cast; linarith [p.deltaPos])) hvq hy
  have hheadN := repair_head_exact E rho hrec.toRecovery₂ (r + 1) hProposalSync hx hip hseat N hem
    (fun y hy ih hih _ => repair_h6_input E rho hrec mono crossing hGST hphase hheadVote hvq
      hlease hx hip hPrior hCut hy hih)
    (fun y hy ih hi hj => hHeads.target hy hi hj (hFloors y hy))
    (fun y hy ih hi hj => hHeads.scopes y hy ih hi hj (hFloors y hy)) hhor
  have hheadQ : ∀ y ∈ rho.honest,
      joinedAt p E rho y (r + 1) (SA.voteTime p.toParams (r + 1)) →
      headAtLabel p c E rho y (r + 1) = some Q := by simpa only [heN] using hheadN
  have hne : Q ≠ .genesis := by
    rintro rfl
    exact Nat.succ_ne_zero r hQs.symm
  have hGates := services.gates (r + 1) hcut (hgate.trans hphase.2.1)
  exact repair_exact_service_on E rho hrec (r + 1) Q hne hcut (hGST.trans hus)
    (fun _ => hheadQ)
    (fun _ _ hx ht => repair_gate_geometry E rho hrec mono crossing qc
      writes hGST hphase hus hgate hQs hheadQ hx ht hGates)
    (fun i x hReader ht => (hGates.gates i x hReader.1 ht
      (healing_scope_enabled_gate hrec hReader.1 ht (by
        change E.t_GST ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
        have hb := hcut
        change E.t_GST ≤ 4 * p.Δ * (((r + 1 : Nat) : Int) - 1) at hb
        linarith [p.deltaPos]) (hgate.trans hphase.2.1)) Q
        (repair_gate_geometry E rho hrec mono crossing qc writes hGST hphase hus hgate
          hQs hheadQ hReader.1 ht hGates).toGateReceiptGeometry)) hhor

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:749–756 (RepairAfter); plan H-REPAIR step 10. DC: INTENTIONAL every
later honest proposal s with d_s ≤ v has exact service once the lease cover holds after
the threshold l and u ≤ v_l. -/
theorem repair_after_of_cover [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    (services : RepairServiceScopes E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {l : Nat} (hlu : u ≤ slotStartZ p (l : Int))
    (hPriorCut : E.t_GST ≤ slotStartZ p ((l : Int) - 1))
    (hcover : ∀ s, SA.proposalTime p.toParams l < SA.proposalTime p.toParams s →
      SA.voteTime p.toParams s ≤ v → RepairLeaseCover E rho s) :
    RepairAfter p c E rho l v := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  intro s Q hls hgate hp
  have hlt := repair_slot_lt_of_time hls
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.ne_zero_of_lt hlt)
  have hd := p.deltaPos
  have hlr : (l : Int) ≤ r := by omega
  have hhead : u ≤ slotStartZ p (r : Int) := by
    refine hlu.trans ?_
    change 4 * p.Δ * (l : Int) ≤ 4 * p.Δ * (r : Int)
    nlinarith
  have hvs : SA.voteTime p.toParams (r + 1) ≤ v := by
    refine le_trans ?_ hgate
    change 4 * p.Δ * ((r + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int) + 6 * p.Δ
    linarith
  have hPriorR : E.t_GST ≤ slotStartZ p ((r : Int) - 1) := by
    refine hPriorCut.trans ?_
    change 4 * p.Δ * ((l : Int) - 1) ≤ 4 * p.Δ * ((r : Int) - 1)
    nlinarith
  exact repair_exact_service E rho hrec mono crossing qc services writes hready hphase hhead
    hPriorR (hcover _ hls hvs) hgate hp

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:910–986 (two leases); plan H-REPAIR steps 3, 4, 10–12 (R4).
DC: INTENTIONAL with β the first proposal after u: RepairAfter (β + 2k − 1) v, and inside
u + ρΓ an honest proposal after t_(β+2k−1) with exact service. The gap window is G (not Γ);
Γ bounds the slot found. -/
theorem repair_two_lease [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    (services : RepairServiceScopes E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {Gp : Time} (hgap : ProposalGap p c E rho Gp)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {β : Nat} (hβ : u < SA.proposalTime p.toParams β)
    (hmin : ∀ b, u < SA.proposalTime p.toParams b → β ≤ b) :
    RepairAfter p c E rho (β + 2 * p.k - 1) v ∧
    (u + ρΓ p Gp ≤ v → ∃ s Q,
      SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams s ∧
      SA.gateTime p.toParams s ≤ u + ρΓ p Gp ∧
      HonestProposal E rho (fgsaInterface p c) s Q ∧ ExactService p c E rho s Q) := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hd := p.deltaPos
  have hk := p.kLarge
  have hu0 : 0 ≤ u := E.t_GST_nonneg.trans hGST
  have hβ1 : 1 ≤ β := by
    by_contra h0
    have hb0 : β = 0 := by omega
    subst hb0
    change u < 4 * p.Δ * ((0 : Nat) : Int) at hβ
    simp only [Nat.cast_zero, mul_zero] at hβ
    linarith
  have hβu : SA.proposalTime p.toParams β ≤ u + 4 * p.Δ := by
    by_contra hc
    have hc' : u < SA.proposalTime p.toParams (β - 1) := by
      change ¬ (4 * p.Δ * (β : Int) ≤ u + 4 * p.Δ) at hc
      change u < 4 * p.Δ * ((β - 1 : Nat) : Int)
      have e : ((β - 1 : Nat) : Int) = (β : Int) - 1 := by omega
      rw [e]
      linarith
    have := hmin (β - 1) hc'
    omega
  have hcl : ((β + 2 * p.k - 1 : Nat) : Int) = (β : Int) + 2 * p.k - 1 := by omega
  have htl : SA.proposalTime p.toParams (β + 2 * p.k - 1) ≤ u + 8 * p.k * p.Δ := by
    change 4 * p.Δ * (β : Int) ≤ u + 4 * p.Δ at hβu
    change 4 * p.Δ * ((β + 2 * p.k - 1 : Nat) : Int) ≤ u + 8 * p.k * p.Δ
    rw [hcl]
    linarith
  have hlu : u ≤ slotStartZ p ((β + 2 * p.k - 1 : Nat) : Int) := by
    refine hβ.le.trans ?_
    change 4 * p.Δ * (β : Int) ≤ 4 * p.Δ * ((β + 2 * p.k - 1 : Nat) : Int)
    rw [hcl]
    have hk' : (2 : Int) ≤ p.k := by exact_mod_cast hk
    nlinarith
  have hPriorCut : E.t_GST ≤ slotStartZ p (((β + 2 * p.k - 1 : Nat) : Int) - 1) := by
    refine (hGST.trans hβ.le).trans ?_
    change 4 * p.Δ * (β : Int) ≤ 4 * p.Δ * (((β + 2 * p.k - 1 : Nat) : Int) - 1)
    rw [hcl]
    have hk' : (2 : Int) ≤ p.k := by exact_mod_cast hk
    nlinarith
  have hafter : RepairAfter p c E rho (β + 2 * p.k - 1) v :=
    repair_after_of_cover E rho hrec mono crossing qc services writes hready hphase hlu hPriorCut
      (fun _ hls hvs => repair_lease_cover_two E rho hrec mono crossing writes
        (healing_tPerm E rho hrec mono crossing writes services.permanence) hready hphase hβ
        hls hvs)
  refine ⟨hafter, fun hbud => ?_⟩
  have hβl : SA.proposalTime p.toParams β ≤ SA.proposalTime p.toParams (β + 2 * p.k - 1) := by
    change 4 * p.Δ * (β : Int) ≤ 4 * p.Δ * ((β + 2 * p.k - 1 : Nat) : Int)
    rw [hcl]
    have hk' : (2 : Int) ≤ p.k := by exact_mod_cast hk
    nlinarith
  have hGl : E.t_GST ≤ SA.proposalTime p.toParams (β + 2 * p.k - 1) :=
    hGST.trans (hβ.le.trans hβl)
  have hlt := repair_lt_Γ (p := p) Gp
  have hhor : SA.proposalTime p.toParams (β + 2 * p.k - 1) + Gp ≤ rho.horizon := by
    refine le_trans ?_ (hbud.trans hphase.2.1)
    change _ ≤ u + (2 * ((4 * (p.k : Time) - 1) * p.Δ) + Γ p Gp + 8 * p.Δ)
    linarith
  have hReadyThreshold : recoveryStart p E ≤
      SA.proposalTime p.toParams (β + 2 * p.k - 1) := hready.trans (hβ.le.trans hβl)
  obtain ⟨s, hs1, hs2, hslot⟩ := hgap _ hReadyThreshold hhor
  rw [proposalTime_fgsa] at hs1 hs2
  have hsΓ := repair_grid_Γ (p := p) hs2
  have hds : SA.gateTime p.toParams s ≤ u + ρΓ p Gp := by
    change 4 * p.Δ * (s : Int) ≤ _ at hsΓ
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤
      u + (2 * ((4 * (p.k : Time) - 1) * p.Δ) + Γ p Gp + 8 * p.Δ)
    linarith
  have hts : SA.proposalTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hJoinCut : E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
    have hSlots := repair_slot_lt_of_time hs1
    have hSlotsI : ((β + 2 * p.k - 1 : Nat) : Int) + 1 ≤ (s : Int) := by
      exact_mod_cast (show β + 2 * p.k - 1 + 1 ≤ s from hSlots)
    change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
    change E.t_GST ≤ 4 * p.Δ * ((β + 2 * p.k - 1 : Nat) : Int) at hGl
    nlinarith [p.deltaPos]
  obtain ⟨Q, hp⟩ := repair_honest_proposal E rho hrec hslot (hGl.trans hs1.le) hJoinCut
    ((hts.trans (hds.trans hbud)).trans hphase.2.1)
  exact ⟨s, Q, hs1, hds, hp, hafter s Q hs1 (hds.trans hbud) hp⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6-S:988–1052 (one lease); plan H-REPAIR steps 3, 5, 10–12 (R4).
DC: INTENTIONAL with b the first HEAD label at or after u and the synchronous window
GST ≤ v_(b+1−k): RepairAfter (b + k) v, and strictly inside u + ρ₁ an honest proposal after
t_(b+k) with exact service. The budget keeps the strict bound for b. -/
theorem repair_synchronous [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    (services : RepairServiceScopes E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {Gp : Time} (hgap : ProposalGap p c E rho Gp)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {b : Nat} (hb : u ≤ SA.voteTime p.toParams b)
    (hmin : ∀ i, u ≤ SA.voteTime p.toParams i → b ≤ i)
    (hwindow : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k)) :
    RepairAfter p c E rho (b + p.k) v ∧
    (u + ρ₁ p Gp ≤ v → ∃ s Q,
      SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams s ∧
      SA.gateTime p.toParams s < u + ρ₁ p Gp ∧
      HonestProposal E rho (fgsaInterface p c) s Q ∧ ExactService p c E rho s Q) := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hd := p.deltaPos
  have hk := p.kLarge
  have hk' : (2 : Int) ≤ p.k := by exact_mod_cast hk
  have hu0 : 0 ≤ u := E.t_GST_nonneg.trans hGST
  have htb : SA.proposalTime p.toParams b < u + 3 * p.Δ := by
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · subst hb0
      change 4 * p.Δ * ((0 : Nat) : Int) < u + 3 * p.Δ
      simp only [Nat.cast_zero, mul_zero]
      linarith
    · by_contra hc
      have hc' : u ≤ SA.voteTime p.toParams (b - 1) := by
        change ¬ (4 * p.Δ * (b : Int) < u + 3 * p.Δ) at hc
        change u ≤ 4 * p.Δ * ((b - 1 : Nat) : Int) + p.Δ
        have e : ((b - 1 : Nat) : Int) = (b : Int) - 1 := by omega
        rw [e]
        linarith
      have := hmin (b - 1) hc'
      omega
  have hlu : u ≤ slotStartZ p ((b + p.k : Nat) : Int) := by
    refine hb.trans ?_
    change 4 * p.Δ * (b : Int) + p.Δ ≤ 4 * p.Δ * ((b + p.k : Nat) : Int)
    push_cast
    nlinarith
  have hPriorCut : E.t_GST ≤ slotStartZ p (((b + p.k : Nat) : Int) - 1) := by
    refine (hGST.trans hb).trans ?_
    change 4 * p.Δ * (b : Int) + p.Δ ≤ 4 * p.Δ * (((b + p.k : Nat) : Int) - 1)
    push_cast
    have hk' : (2 : Int) ≤ p.k := by exact_mod_cast p.kLarge
    nlinarith [p.deltaPos]
  have hafter : RepairAfter p c E rho (b + p.k) v :=
    repair_after_of_cover E rho hrec mono crossing qc services writes hready hphase hlu hPriorCut
      (fun _ hls hvs => repair_lease_cover_one E rho hrec mono crossing writes
        (healing_tPerm E rho hrec mono crossing writes services.permanence) hready hphase hb
        hwindow hls hvs)
  refine ⟨hafter, fun hbud => ?_⟩
  have htl : SA.proposalTime p.toParams (b + p.k) < u + 4 * p.k * p.Δ + 3 * p.Δ := by
    change 4 * p.Δ * (b : Int) < u + 3 * p.Δ at htb
    change 4 * p.Δ * ((b + p.k : Nat) : Int) < u + 4 * p.k * p.Δ + 3 * p.Δ
    push_cast
    linarith
  have hGl : E.t_GST ≤ SA.proposalTime p.toParams (b + p.k) := by
    refine hGST.trans (hb.trans ?_)
    change 4 * p.Δ * (b : Int) + p.Δ ≤ 4 * p.Δ * ((b + p.k : Nat) : Int)
    push_cast
    nlinarith
  have hlt := repair_lt_Γ (p := p) Gp
  have hhor : SA.proposalTime p.toParams (b + p.k) + Gp ≤ rho.horizon := by
    refine le_trans ?_ (hbud.trans hphase.2.1)
    change _ ≤ u + ((4 * (p.k : Time) - 1) * p.Δ + Γ p Gp + 10 * p.Δ)
    linarith
  have hReadyThreshold : recoveryStart p E ≤ SA.proposalTime p.toParams (b + p.k) := by
    refine hready.trans (hb.trans ?_)
    change 4 * p.Δ * (b : Int) + p.Δ ≤ 4 * p.Δ * ((b + p.k : Nat) : Int)
    push_cast
    nlinarith
  obtain ⟨s, hs1, hs2, hslot⟩ := hgap _ hReadyThreshold hhor
  rw [proposalTime_fgsa] at hs1 hs2
  have hsΓ := repair_grid_Γ (p := p) hs2
  have hds : SA.gateTime p.toParams s < u + ρ₁ p Gp := by
    change 4 * p.Δ * (s : Int) ≤ _ at hsΓ
    change 4 * p.Δ * (s : Int) + 6 * p.Δ < u + ((4 * (p.k : Time) - 1) * p.Δ + Γ p Gp + 10 * p.Δ)
    linarith
  have hts : SA.proposalTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hJoinCut : E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
    have hSlots := repair_slot_lt_of_time hs1
    have hSlotsI : ((b + p.k : Nat) : Int) + 1 ≤ (s : Int) := by
      exact_mod_cast (show b + p.k + 1 ≤ s from hSlots)
    change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
    change E.t_GST ≤ 4 * p.Δ * ((b + p.k : Nat) : Int) at hGl
    nlinarith [p.deltaPos]
  obtain ⟨Q, hp⟩ := repair_honest_proposal E rho hrec hslot (hGl.trans hs1.le) hJoinCut
    ((hts.trans (hds.le.trans hbud)).trans hphase.2.1)
  exact ⟨s, Q, hs1, hds, hp, hafter s Q hs1 (hds.le.trans hbud) hp⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
T-REPAIR (ChannelProps.lean:917; blueprint 21 H.6:749–756, 910–986, H.6-S:988–1052);
plan H-REPAIR steps 1, 13 (R5). DC: INTENTIONAL the exact frozen TRepair under the standing
Recovery₂ (plan Gap 1: unconditional TRepair is false on arbitrary runs). The other
hypotheses are RMono, RXing, RQCOrigin (FGFoundation fields with producers on main) and the
inline last-write premise (ruling B27), as in healing_tPerm. -/
theorem healing_tRepair [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    (services : RepairServiceScopes E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C) :
    TRepair p c E rho := by
  intro Gp u v m J contested hgap _ hgst hphase
  exact ⟨fun _ hβ hmin => repair_two_lease E rho hrec mono crossing qc services writes hgap hgst
      hphase hβ hmin,
    fun _ hb hmin _ hwindow => repair_synchronous E rho hrec mono crossing qc services writes hgap
      hgst hphase hb hmin hwindow⟩

end AvailableChain.FGSA.Run
end
