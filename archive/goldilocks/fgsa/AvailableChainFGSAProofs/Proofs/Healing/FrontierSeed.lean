module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSeedDefs
public import AvailableChainFGSAProofs.Proofs.Healing.RepairCover -- shake: keep (facade coverage)
public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryService

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

/-! HG.1 seed (blueprint 21:1333–1350, 1570–1574; TF-SEED Q4).
The qualification is the two-arm premise in the frozen `TFrontier`.
The initial phase includes the q+1 proposal and HEAD reads.
This module supplies their lease cover. It does not extend the phase to the q+1 gate.
The INLINE `writes` producer is `fgsa_leaseOrigins_lastWrite` (Foundations/Leases:392).
That producer is used at Assembly; this module imports only the Healing lane. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:915–986; TF-SEED Q1.
DC: SAME the unchanged H.6 repair output supplies the seed qualification. -/
theorem tfSeed_two_from_tRepair (h : TRepair p c E rho)
    {G u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgap : ProposalGap p c E rho G) (hG : 4 * p.Δ ≤ G)
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {β : Slot} (hβ : u < SA.proposalTime p.toParams β)
    (hmin : ∀ b, u < SA.proposalTime p.toParams b → β ≤ b)
    (hbudget : u + ρΓ p G ≤ v) :
    ∃ q Q, FrontierSeedQualification p E u q ∧
      SA.gateTime p.toParams q ≤ u + ρΓ p G ∧
      HonestProposal E rho (fgsaInterface p c) q Q ∧ ExactService p c E rho q Q := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  obtain ⟨q, Q, hlt, hgate, hp, hs⟩ :=
    (h G u v m J contested hgap hG hready hphase).1 β hβ hmin |>.2 hbudget
  exact ⟨q, Q, (frontierSeedQualification_iff p E u q).mpr
    (Or.inl ⟨β, hβ, hmin, hlt⟩), hgate, hp, hs⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6-S:988–1033; TF-SEED Q1.
DC: SAME the H.6-S repair output and its inputs supply the seed qualification. -/
theorem tfSeed_one_from_tRepair (h : TRepair p c E rho)
    {G u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgap : ProposalGap p c E rho G) (hG : 4 * p.Δ ≤ G)
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {b : Slot} (hb : u ≤ SA.voteTime p.toParams b)
    (hmin : ∀ i, u ≤ SA.voteTime p.toParams i → b ≤ i)
    (hkb : p.k ≤ b + 1) (hwindow : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k))
    (hbudget : u + ρ₁ p G ≤ v) :
    ∃ q Q, FrontierSeedQualification p E u q ∧
      SA.gateTime p.toParams q < u + ρ₁ p G ∧
      HonestProposal E rho (fgsaInterface p c) q Q ∧ ExactService p c E rho q Q := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  obtain ⟨q, Q, hlt, hgate, hp, hs⟩ :=
    (h G u v m J contested hgap hG hready hphase).2 b hb hmin hkb hwindow |>.2 hbudget
  exact ⟨q, Q, (frontierSeedQualification_iff p E u q).mpr
    (Or.inr ⟨b, hb, hmin, hkb, hwindow, hlt⟩), hgate, hp, hs⟩

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 HG.1:1333–1350; TF-SEED Q1.
DC: SAME later proposals keep the repair threshold and phase-start qualification. -/
theorem tfSeed_later {u : Time} {q s : Slot} (hseed : FrontierSeedQualification p E u q)
    (hlater : SA.proposalTime p.toParams q < SA.proposalTime p.toParams s) :
    FrontierSeedQualification p E u s := by
  rcases (frontierSeedQualification_iff p E u q).mp hseed with
    ⟨β, hβ, hmin, hlt⟩ | ⟨b, hb, hmin, hkb, hwindow, hlt⟩
  · exact (frontierSeedQualification_iff p E u s).mpr
      (Or.inl ⟨β, hβ, hmin, hlt.trans hlater⟩)
  · exact (frontierSeedQualification_iff p E u s).mpr
      (Or.inr ⟨b, hb, hmin, hkb, hwindow, hlt.trans hlater⟩)

omit [DecidableEq V] in
/-- Both repaired seed branches put GST before the seed voters' previous-slot cutoff. -/
theorem frontier_seed_vote_cutoff {u : Time} {q : Slot}
    (hseed : FrontierSeedQualification p E u q) (hready : recoveryStart p E ≤ u) :
    E.t_GST ≤ slotStartZ p ((q : Int) - 1) := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  change E.t_GST ≤ 4 * p.Δ * ((q : Int) - 1)
  rcases (frontierSeedQualification_iff p E u q).mp hseed with
    ⟨β, hβ, _, hlt⟩ | ⟨b, hb, _, _, _, hlt⟩
  · have hslots := repair_slot_lt_of_time hlt
    have key : ∀ b k z : Nat, 2 ≤ k → b + 2 * k - 1 < z → b + 1 ≤ z := by
      intro b k z hk hz
      omega
    have hβq : β + 1 ≤ q := key β p.k q p.kLarge hslots
    have hβqI : (β : Int) + 1 ≤ (q : Int) := by exact_mod_cast hβq
    change u < 4 * p.Δ * (β : Int) at hβ
    nlinarith [p.deltaPos]
  · have hslots := repair_slot_lt_of_time hlt
    have key : ∀ b k z : Nat, 2 ≤ k → b + k < z → b + 2 ≤ z := by
      intro b k z hk hz
      omega
    have hbq : b + 2 ≤ q := key b p.k q p.kLarge hslots
    have hbqI : (b : Int) + 2 ≤ (q : Int) := by exact_mod_cast hbq
    change u ≤ 4 * p.Δ * (b : Int) + p.Δ at hb
    nlinarith [p.deltaPos]

variable {p c}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:925–944, 1004–1025, 1570–1574; TF-SEED Q4 steps 1–2.
DC: INTENTIONAL the frozen seed premise gives the q+1 lease cover in the initial phase.
The q+1 gate needs a separate proof under the frontier cap. -/
theorem tfSeed_qSucc_lease_cover [Fintype V] {G ΔF : Time}
    (_hrec : RecoverySleep₂ p c E rho G ΔF) (_mono : RMonoAll p c E rho)
    (_crossing : RXing p c E rho)
    (_writes : ∀ i x (row : Block × Nat × Time),
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
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} {q : Slot}
    (_hready : recoveryStart p E ≤ u)
    (_hphase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (_hPerm : SupportPermanenceServices E rho u (SA.gateTime p.toParams q) m J contested)
    (hseed : FrontierSeedQualification p E u q)
    (twoCover : ∀ β, u < SA.proposalTime p.toParams β →
      SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams (q + 1) →
      SA.voteTime p.toParams (q + 1) ≤ SA.gateTime p.toParams q →
      RepairLeaseCover E rho (q + 1))
    (oneCover : ∀ b, u ≤ SA.voteTime p.toParams b →
      E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k) →
      SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams (q + 1) →
      SA.voteTime p.toParams (q + 1) ≤ SA.gateTime p.toParams q →
      RepairLeaseCover E rho (q + 1)) : RepairLeaseCover E rho (q + 1) := by
  have hd := p.deltaPos
  have hlater : SA.proposalTime p.toParams q < SA.proposalTime p.toParams (q + 1) := by
    change 4 * p.Δ * (q : Int) < 4 * p.Δ * ((q + 1 : Nat) : Int)
    push_cast
    linarith
  have hvs : SA.voteTime p.toParams (q + 1) ≤ SA.gateTime p.toParams q := by
    change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
    push_cast
    linarith
  rcases (frontierSeedQualification_iff p E u q).mp hseed with
    ⟨β, hβ, _, hlt⟩ | ⟨b, hb, _, _, hwindow, hlt⟩
  · exact twoCover β hβ (hlt.trans hlater) hvs
  · exact oneCover b hb hwindow (hlt.trans hlater) hvs

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:925–944, 1004–1025, 1570–1574; plan §3.1 step 7.
DC: INTENTIONAL the retained H.6 input at both actual q+1 reads in the initial phase.
Both seed arms use the checked lease cover. No phase through the q+1 gate is used. -/
theorem frontier_seed_qSucc_input [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (crossing : RXing p c E rho)
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
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} {q : Slot}
    (hready : recoveryStart p E ≤ u)
    (hphase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hPerm : SupportPermanenceServices E rho u (SA.gateTime p.toParams q) m J contested)
    (hseed : FrontierSeedQualification p E u q)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (q + 1))))
    (hPrior : ProposalSupportScope E rho ip x q (SA.proposalTime p.toParams (q + 1)))
    {ih : Nat} {y : V} (hy : y ∈ rho.honest)
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (q + 1)))) :
    RetainedH6Input p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (q + 1)))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (q + 1))) (q + 1) := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hd := p.deltaPos
  have hlater : SA.proposalTime p.toParams q < SA.proposalTime p.toParams (q + 1) := by
    change 4 * p.Δ * (q : Int) < 4 * p.Δ * ((q + 1 : Nat) : Int)
    push_cast
    linarith
  have hhead : u ≤ SA.voteTime p.toParams q := by
    rcases (frontierSeedQualification_iff p E u (q + 1)).mp
      (tfSeed_later p E hseed hlater) with ⟨β, hβ, _, hlt⟩ | ⟨b, hb, _, _, _, hlt⟩
    · exact repair_head_after_two hβ hlt
    · exact repair_head_after_one hb hlt
  have hvs : SA.voteTime p.toParams (q + 1) ≤ SA.gateTime p.toParams q := by
    change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
    push_cast
    linarith
  have hCut : HealingWindow p E 1 q :=
    healing_window_of_cut E (healing_ready_vote_cutoff E (hready.trans hhead))
  exact repair_h6_input E rho hrec mono crossing hGST hphase hhead hvs
    (tfSeed_qSucc_lease_cover E rho hrec mono crossing writes hready hphase hPerm hseed
      (fun β hβ hls hvs => repair_lease_cover_two_at E rho hrec mono crossing writes
        hready hphase hPerm hβ hls hvs)
      (fun b hb hSync hls hvs => repair_lease_cover_one_at E rho hrec mono crossing writes
        hready hphase hPerm hb hSync hls hvs))
    hx hip hPrior hCut hy hih

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:956–958, 1004–1025, 1570–1574; plan §3.1 step 7.
DC: INTENTIONAL every honest q+1 HEAD is the honest q+1 proposal.
The two arms consume `fgsa_retainedReads_H6` and `fgsa_retainedReads_H6S`, respectively. -/
theorem frontier_seed_qSucc_head [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (crossing : RXing p c E rho)
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
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} {q : Slot}
    (hready : recoveryStart p E ≤ u)
    (hphase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hPerm : SupportPermanenceServices E rho u (SA.gateTime p.toParams q) m J contested)
    (hseed : FrontierSeedQualification p E u q)
    (hServices : ∀ ip x N, x ∈ rho.honest →
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (q + 1))) →
      (ofWire p ⟨.proposer (q + 1), .proposal N⟩) ∈ rho.emitsAt E ip →
      RepairHeadServices E rho (q + 1) ip x N)
    {B : Block} (hp : HonestProposal E rho (fgsaInterface p c) (q + 1) B) :
    ∀ y ∈ rho.honest, joinedAt p E rho y (q + 1) (SA.voteTime p.toParams (q + 1)) →
      headAtLabel p c E rho y (q + 1) = some B := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hd := p.deltaPos
  have hlater : SA.proposalTime p.toParams q < SA.proposalTime p.toParams (q + 1) := by
    change 4 * p.Δ * (q : Int) < 4 * p.Δ * ((q + 1 : Nat) : Int)
    push_cast
    linarith
  have hhead : u ≤ SA.voteTime p.toParams q := by
    rcases (frontierSeedQualification_iff p E u (q + 1)).mp
      (tfSeed_later p E hseed hlater) with ⟨β, hβ, _, hlt⟩ | ⟨b, hb, _, _, _, hlt⟩
    · exact repair_head_after_two hβ hlt
    · exact repair_head_after_one hb hlt
  have hvs : SA.voteTime p.toParams (q + 1) ≤ SA.gateTime p.toParams q := by
    change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
    push_cast
    linarith
  have hE := hrec.base.valid
  have hDelta := hrec.base.delta
  obtain ⟨ip, x, N, heN, hx, hip, hseat, hem⟩ := repair_proposal_emission E rho hp
  subst B
  have hGST : E.t_GST ≤ SA.proposalTime p.toParams (q + 1) - p.Δ := by
    refine hGST.trans (hhead.trans ?_)
    change 4 * p.Δ * (q : Int) + p.Δ ≤ 4 * p.Δ * ((q + 1 : Nat) : Int) - p.Δ
    push_cast
    linarith
  have hhor : SA.voteTime p.toParams (q + 1) ≤ rho.horizon := hvs.trans hphase.2.1
  have hServices := hServices ip x N hx hip hem
  have hPrior : ProposalSupportScope E rho ip x q (SA.proposalTime p.toParams (q + 1)) := by
    simpa only [Nat.add_sub_cancel] using hServices.prior
  have hFloors : ∀ y ∈ rho.honest, Block.Preceq
      (eraseFG (rho.stateBeforeTime E (SA.voteTime p.toParams (q + 1)) y).st.fg.F)
      N.erase := by
    intro y hy
    exact healing_proposal_phase_reader_floor hrec.base.valid crossing hphase hp
      (hhead.trans (by
        change 4 * p.Δ * (q : Int) + p.Δ ≤ 4 * p.Δ * ((q + 1 : Nat) : Int)
        push_cast; linarith [p.deltaPos])) hvs hy
  exact repair_head_exact E rho hrec.toRecovery₂ (q + 1) hGST hx hip hseat N hem
    (fun y hy ih hih _ => frontier_seed_qSucc_input E rho hrec mono crossing writes
      hready hphase hPerm hseed hx hip hPrior hy hih)
    (fun y hy ih hi hj => hServices.target hy hi hj (hFloors y hy))
    (fun y hy ih hi hj => hServices.scopes y hy ih hi hj (hFloors y hy)) hhor

end AvailableChain.FGSA.Run
end
