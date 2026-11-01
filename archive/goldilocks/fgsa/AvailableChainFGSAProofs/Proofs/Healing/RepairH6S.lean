module
public import AvailableChainFGSAProofs.Proofs.Healing.RepairH6

public section

/-! H-REPAIR G-H6S (plan steps 3, 5–8; blueprint 21 H.6-S:988–1052). The retained H.6 input
under the b + k cut and the synchronous window GST ≤ v_(b+1−k). The window labels may be in
earlier phases; the last-write split supplies the lease cover. The H6-C lemma gives the
window from the start bound. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure RetainedWalk

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1034–1052 (H.6-C); plan H-REPAIR Outputs (H6-C arithmetic).
DC: INTENTIONAL with k ≤ 2R + 1 and the start bound g + 2P + 3Δ ≤ u, the first HEAD label b
at or after u has its synchronous window: g ≤ v_(b+1−k). The caller supplies the start
bound. -/
theorem repair_h6c_window {g u : Time} {b : Nat} (hk : p.k ≤ 2 * p.R + 1)
    (hu : g + 2 * P p + 3 * p.Δ ≤ u) (hb : u ≤ SA.voteTime p.toParams b)
    (hkb : p.k ≤ b + 1) : g ≤ SA.voteTime p.toParams (b + 1 - p.k) := by
  have hd := p.deltaPos
  have hc : ((b + 1 - p.k : Nat) : Int) = (b : Int) + 1 - p.k := by omega
  have hk' : (p.k : Int) ≤ 2 * p.R + 1 := by exact_mod_cast hk
  change g + 2 * (4 * (p.R : Int) * p.Δ) + 3 * p.Δ ≤ u at hu
  change u ≤ 4 * p.Δ * (b : Int) + p.Δ at hb
  change g ≤ 4 * p.Δ * ((b + 1 - p.k : Nat) : Int) + p.Δ
  rw [hc]
  nlinarith

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan H-REPAIR step 3. DC: SAME a slot after b + k, with u ≤ v_b, has its preceding HEAD
at or after u. -/
theorem repair_head_after_one {u : Time} {b r : Nat} (hb : u ≤ SA.voteTime p.toParams b)
    (hls : SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams (r + 1)) :
    u ≤ SA.voteTime p.toParams r := by
  have hd := p.deltaPos
  have hlt := repair_slot_lt_of_time hls
  have hr : (b : Int) ≤ r := by omega
  refine hb.trans ?_
  change 4 * p.Δ * (b : Int) + p.Δ ≤ 4 * p.Δ * (r : Int) + p.Δ
  nlinarith

/-- The repair adapter consumes the local lease cover at this actual label.
The joined-start TPerm input supplies both branches of the last-write split.
The phase-service producer of TPerm remains OPEN/P-H1. -/
theorem repair_lease_cover_one [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (_mono : RMonoAll p c E rho) (_crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
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
    (perm : TPerm p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {b : Slot} (hb : u ≤ SA.voteTime p.toParams b)
    (hwindow : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k)) {s : Slot}
    (hls : SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams s)
    (hvs : SA.voteTime p.toParams s ≤ v)
 : RepairLeaseCover E rho s := by
  exact repair_lease_cover_of_split E rho hrec.base.valid.toScheduleWellFormed
    (healing_last_write_one_lease p c E rho
      hrec.base.valid.toScheduleWellFormed perm writes hready hphase hb hwindow) hls hvs

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:988–1033 (H.6-S); plan H-REPAIR G-H6S (R2), steps 5–8. DC: INTENTIONAL the
retained H.6 input at every actual honest proposal/HEAD read pair of a slot s after b + k
with v_s ≤ v, under the synchronous window. -/
theorem retainedH6Input_on_synchronous_reads [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
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
    (perm : TPerm p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {b : Slot} (hb : u ≤ SA.voteTime p.toParams b)
    (hwindow : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k)) {s : Slot}
    (hls : SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams s)
    (hvs : SA.voteTime p.toParams s ≤ v)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hScope : ProposalSupportScope E rho ip x (s - 1) (SA.proposalTime p.toParams s))
    {ih : Nat} {y : V} (hy : y ∈ rho.honest)
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s))) :
    RetainedH6Input p (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s := by
  have hgst : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero
    (Nat.ne_zero_of_lt (repair_slot_lt_of_time hls))
  have hWindow : HealingWindow p E 2 (r + 1) :=
    healing_ready_proposal_window E ((hready.trans (repair_head_after_one hb hls)).trans (by
      change 4 * p.Δ * (r : Int) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
      push_cast
      linarith [p.deltaPos]))
  exact repair_h6_input E rho hrec mono crossing hgst hphase (repair_head_after_one hb hls) hvs
    (repair_lease_cover_one E rho hrec mono crossing writes perm hready hphase hb hwindow hls hvs)
    hx hip (by simpa only [Nat.add_sub_cancel] using hScope)
    (by simpa only [Nat.add_sub_cancel] using hWindow.prior) hy hih

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:988–1033 (H.6-S HEAD equality); plan H-REPAIR G-H6S (R2), step 8.
DC: INTENTIONAL every honest HEAD of a slot s after b + k with v_s ≤ v is its honest
proposal. -/
theorem repair_head_one [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
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
    (perm : TPerm p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {b : Slot} (hb : u ≤ SA.voteTime p.toParams b)
    (hwindow : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k)) {s : Slot}
    (hls : SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams s)
    (hvs : SA.voteTime p.toParams s ≤ v)
    (hServices : ∀ (ip : Nat) (x : V) (N : NamedProposal p.n), x ∈ rho.honest →
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
      (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈ rho.emitsAt E ip →
      RepairHeadServices E rho s ip x N)
    {Q : Block} (hp : HonestProposal E rho (fgsaInterface p c) s Q) :
    ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
      headAtLabel p c E rho y s = some Q := by
  have hgst : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero
    (Nat.ne_zero_of_lt (repair_slot_lt_of_time hls))
  have hWindow : HealingWindow p E 2 (r + 1) :=
    healing_ready_proposal_window E ((hready.trans (repair_head_after_one hb hls)).trans (by
      change 4 * p.Δ * (r : Int) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
      push_cast
      linarith [p.deltaPos]))
  exact repair_head_exact_legacy E rho hrec mono crossing hgst hphase
    (repair_head_after_one hb hls) hvs
    (repair_lease_cover_one E rho hrec mono crossing writes perm
      hready hphase hb hwindow hls hvs)
    (by simpa only [Nat.add_sub_cancel] using hWindow.prior) hServices hp

end AvailableChain.FGSA.Run
end
