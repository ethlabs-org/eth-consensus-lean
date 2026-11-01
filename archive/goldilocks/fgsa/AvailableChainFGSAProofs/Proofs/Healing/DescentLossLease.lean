module
public import AvailableChainFGSAProofs.Proofs.Healing.DescentLoss
public import AvailableChainFGSAProofs.Proofs.Healing.SupportLease

public section

/-! H-DESCENT D2 (H.13): the live leases at a loss read of label l ≥ sB + 2.
`healing_fast_lease_at` with the bound T bound to the current read v_l and its
HEAD coverage from `noLoss` at strictly earlier events. The last-write facts
are the inline hypothesis `writes` (B27). -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A vote time is not a gate time: the clock at v_l is the pre-gate clock. -/
private theorem lease_vote_clock (st : State p.n) (l : Slot) :
    FGSA.clock p st (SA.voteTime p.toParams l) = clockPre p st (SA.voteTime p.toParams l) := by
  have hn : isGateTime p (SA.voteTime p.toParams l) ≠ true := by
    intro hh
    obtain ⟨r, hr⟩ := (isGateTime_iff p _).mp hh
    symm at hr
    change 4 * p.Δ * (l : Int) + p.Δ = 4 * p.Δ * (r : Int) + 6 * p.Δ at hr
    have hd := p.deltaPos
    have h0 : (4 * ((l : Int) - r) - 5) * p.Δ = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h | h
    · omega
    · exact absurd h (ne_of_gt hd)
  change (if isGateTime p _ then _ else _) = _
  rw [ite_eq_right hn]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B `cause` (later live leases; bind T to the current
read); blueprint 21:689–715 (H.1 release, H.2 S1). DC: INTENTIONAL global
event-index measure. At a HEAD tick of label l ≥ sB + 2 of an honest node x,
with no earlier loss and F of x below the high source B, every live lease of
the post-clock state is compatible with B. Every HEAD that the lease bound
reads is an earlier tick, so `noLoss` gives its coverage. -/
theorem healing_loss_lease_late [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
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
    {k : Nat} (noLoss : ∀ k' < k, ∀ B sB, ¬ Lost p c E rho B sB k')
    {B : FGBlock (Fin p.n)} {sB : Slot} {x : V} {l : Slot}
    (hB : HighSrcN p c E rho B sB) (hx : x ∈ rho.honest) (hl : sB + 2 ≤ l)
    (hk : rho.events[k]? = some (.tick x (SA.voteTime p.toParams l)))
    (hScopes : ∀ y nd, y ∈ rho.honest →
      postClock E rho y (SA.gateTime p.toParams sB) = some nd →
      eraseFG B ∈ (fastWriteAt nd.st sB).getD [] →
      FastSupportScope E rho sB (SA.voteTime p.toParams l) y)
    (hFB : Block.Preceq (eraseFG (storeAt p c E rho k x).fg.F) (eraseFG B)) :
    ∀ row ∈ (FGSA.clock p (storeAt p c E rho k x) (SA.voteTime p.toParams l)).base.obligations,
      Block.Compatible row.1 (eraseFG B) := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  have hB' := hB
  rw [HighSrcN_def, SrcN_def] at hB'
  obtain ⟨hsrc, hc⟩ := hB'
  have hCut := healing_high_source_window p c E rho emittedNonempty emittedName hsrc hc
  have hgst := healing_high_source_sync p c E rho emittedNonempty emittedName hsrc hc
  obtain ⟨j, y, r, a, -, ha, hBs, rfl⟩ := hsrc
  have hy := ha.1
  have hj := ha.2.1
  have hgs : SA.gateTime p.toParams (r * p.R) ≤ rho.horizon :=
    (hS.in_horizon _ (List.mem_of_getElem? hj)).2
  have hvl : SA.voteTime p.toParams l ≤ rho.horizon :=
    (hS.in_horizon _ (List.mem_of_getElem? hk)).2
  -- The source B is fast-written at its own gate.
  have hnd : postClock E rho y (SA.gateTime p.toParams (r * p.R)) =
      some ((fgsa p c).clock (V2.D.Run.stateBefore E rho j y) (p.actionTime r)) := by
    change postClock E rho y (p.actionTime r) = _
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hj]
    rfl
  have hfw : eraseFG B ∈ (fastWriteAt ((fgsa p c).clock (V2.D.Run.stateBefore E rho j y)
      (p.actionTime r)).st (r * p.R)).getD [] := by
    have hr := actionSourceFG_eq_round p c E rho hS hj
    rw [hr] at hBs
    have hsel := FGSA.pickPair_some_spec _ _ (Option.some.inj hBs)
    have hp := (Finset.mem_filter.mp hsel.1).2
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp hp).1
  -- Every HEAD read by the lease bound is an earlier tick: `noLoss` covers B.
  have hcov : ∀ w, r * p.R + 1 ≤ w → SA.gateTime p.toParams w ≤ SA.voteTime p.toParams l →
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z w = some K →
        Block.Preceq (eraseFG B) K := by
    intro w hw hwl z hz K hK
    delta headAtLabel at hK
    rw [postClock_def, preTick_def] at hK
    cases hjz' : V2.D.Run.tickIdx? rho z (SA.voteTime p.toParams w) with
    | none => rw [hjz'] at hK; cases hK
    | some jz =>
    rw [hjz'] at hK
    have hjz := V2.D.Run.tickIdx?_spec hjz'
    have hKe : K = headAtIdx p c E rho jz w := by
      rw [healing_headAtIdx_tick p c E rho hjz]
      exact (Option.some.inj hK).symm
    have hlt : jz < k := healing_idx_lt_of_time_lt p c E rho hS hjz hk (by
      change 4 * p.Δ * (w : Int) + p.Δ < 4 * p.Δ * (l : Int) + p.Δ
      change 4 * p.Δ * (w : Int) + 6 * p.Δ ≤ 4 * p.Δ * (l : Int) + p.Δ at hwl
      linarith)
    by_contra hn
    rw [hKe] at hn
    exact noLoss jz hlt B (r * p.R) (by
      rw [Lost_def]
      exact ⟨hB, z, w, hz, hw, hjz, hn⟩)
  -- The loss node's tick at v_(sB+1) precedes the read.
  have hvq : SA.voteTime p.toParams (r * p.R + 1) < SA.voteTime p.toParams l := by
    have hl' : ((r * p.R : Nat) : Int) + 2 ≤ (l : Int) := by exact_mod_cast hl
    change 4 * p.Δ * ((r * p.R + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (l : Int) + p.Δ
    push_cast at hl' ⊢
    nlinarith
  obtain ⟨iq, hiq⟩ := healing_support_vote_tick E rho hS hDelta hx (r * p.R + 1)
    (hvq.le.trans hvl) (hrec.awake x hx _ (by
      refine hgst.trans ?_
      change 4 * p.Δ * ((r * p.R : Nat) : Int) + p.Δ ≤
        4 * p.Δ * ((r * p.R + 1 : Nat) : Int) + p.Δ
      push_cast
      nlinarith) (hvq.le.trans hvl))
  have hqa : iq < k := healing_idx_lt_of_time_lt p c E rho hS hiq hk hvq
  have hT : ∀ j' t, j' < k → rho.events[j']? = some (.tick x t) →
      t ≤ SA.voteTime p.toParams l := by
    intro j' t hjk hj'
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj'
    obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
    have hkey := (List.pairwise_iff_getElem.mp hS.sorted) j' k hjl hkl hjk
    rw [hje, hke] at hkey
    exact V2.D.Engine.time_le_of_key_le _ _ hkey
  have hrows := healing_fast_lease_at E rho hrec mono writes hgst hgs hy hnd hfw hvl
    (hScopes y _ hy hnd hfw)
    (healing_gate_cut_of_batch_cut E (r * p.R) hCut.2) hcov
    hx hiq hqa hT hFB
  intro row hrow
  rw [lease_vote_clock p] at hrow
  exact hrows row ((clockPre_obligations_sublist p _ _).subset hrow)

end AvailableChain.FGSA.Run
end
