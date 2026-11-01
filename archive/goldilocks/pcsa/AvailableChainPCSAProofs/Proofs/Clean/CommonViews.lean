module
public import AvailableChainPCSAProofs.Proofs.Clean.FrozenPCTransport
public import AvailableChainPCSAProofs.Proofs.Clean.CarriedView
public import AvailableChainPCSAProofs.Proofs.Clean.ViewRank
public import AvailableChainPCSAProofs.Proofs.Clean.CommonBodies
public import AvailableChainPCSAProofs.Proofs.Clean.NRoot

public section

/-! C6 CommonViews: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}
/-- In the delivery window: At an honest proposal, the actual proposer and voter PC views have the
same target. -/
theorem pcsa_common_view_targets_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (k : Nat) (y : V) (hy : y ∈ rho.honest) (s : Slot) (N : NamedProposal p.n)
    (hx : rho.seatOf (.prop (s + 1)) (0 : Fin 1) ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.prop (s + 1)) (0 : Fin 1))
      (⟨.seat (.prop (s + 1)) (0 : Fin 1), .proposal N⟩ : Obj p)
        (SA.proposalTime p.toParams (s + 1)))
    (hk : rho.events[k]? = some (.tick (rho.seatOf (.prop (s + 1)) (0 : Fin 1))
      (SA.proposalTime p.toParams (s + 1))))
    (hslot : N.slot = s + 1)
    (hT : T₀ ≤ SA.freezeTime p.toParams s) (hc : SA.voteTime p.toParams (s + 1) ≤ cut)
    (hmem : (⟨.proposer (s + 1), .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1)))
        y).st.proposals)
    (hpc : N.pc = proposerPC p (clock p (V2.D.Run.stateBefore E rho k
      (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st (SA.proposalTime p.toParams (s + 1)))) :
    (voterPC p (clock p (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1))) y).st
        (SA.voteTime p.toParams (s + 1))) (s + 1)).map PC.target =
      (proposerPC p (clock p (V2.D.Run.stateBefore E rho k
        (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
          (SA.proposalTime p.toParams (s + 1)))).map PC.target := by
  let x := rho.seatOf (.prop (s + 1)) (0 : Fin 1)
  let a := V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1))
  let src := clock p (V2.D.Run.stateBefore E rho k x).st (SA.proposalTime p.toParams (s + 1))
  let dst := clock p (V2.D.Run.stateBefore E rho a y).st (SA.voteTime p.toParams (s + 1))
  let sources := (pcSnapshotAt dst s ++ carriedPCs dst (s + 1)).filter (frameActive p dst)
  have hview : voterPC p dst (s + 1) = bestPC sources := by
    delta voterPC
    rw [Nat.add_sub_cancel]
  have hpropVote : SA.proposalTime p.toParams (s + 1) < SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) < 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    exact lt_add_of_pos_right _ p.deltaPos
  have hpropCut := hpropVote.le.trans hc
  have hkbefore : k ≤ V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1)) :=
    Nat.le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hk _).mpr
      hpropVote)
  have frozen (C : PC p.n) (hm : C ∈ pcSnapshotAt dst s) :
      ∃ D ∈ src.pcs.filter (frameActive p src), D.slot = C.slot ∧ D.target = C.target := by
    obtain ⟨D, hDmem, hDs, hDt, hDa⟩ := pcsa_frozen_pc_in_proposer_win E rho h hF hFault hD (hT :=
        hT)
      a k y x hy hx s C hk hpropCut hm
    exact ⟨D, List.mem_filter.mpr ⟨hDmem, hDa⟩, hDs, hDt⟩
  have carried (C : PC p.n) (hm : C ∈ carriedPCs dst (s + 1)) : N.pc = some C := by
    change C ∈ carriedPCs (clock p _ _) (s + 1) at hm
    rw [pcsa_clock_carriedPCs] at hm
    exact pcsa_carriedPC_eq_emitted E rho h.valid a y (s + 1) N hx he C hm
  change (voterPC p dst (s + 1)).map PC.target = (proposerPC p src).map PC.target
  cases hsv : proposerPC p src with
  | none =>
    have hNp : N.pc = none := hpc.trans hsv
    have hempty : sources = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro C hm
      rcases List.mem_append.mp (List.mem_filter.mp hm).1 with hf | hcar
      · obtain ⟨D, hDmem, _, _⟩ := frozen C hf
        have hsome := pcsa_bestPC_isSome_of_mem _ D hDmem
        change (proposerPC p src).isSome = true at hsome
        rw [hsv] at hsome
        cases hsome
      · have hh := (carried C hcar).symm.trans hNp
        cases hh
    rw [hview, hempty]
    rfl
  | some V =>
    have hNp : N.pc = some V := hpc.trans hsv
    have hVm := (List.mem_filter.mp (bestPC_mem _ V hsv)).1
    have hVpre : V ∈ (V2.D.Run.stateBefore E rho k x).st.pcs := by
      change V ∈ (clock p _ _).pcs at hVm
      rwa [pcsa_clock_pcs] at hVm
    obtain ⟨hw, z, hAck, _⟩ := pcsa_pc_honest_ack_before E rho h hFault k x hx _ hkbefore V hVpre
    have hVB : V.target ∈ src.base.blocks := by
      change V.target ∈ (clock p _ _).base.blocks
      rw [pcsa_clock_blocks]
      exact pcsa_pc_targets_held p _ (pcsa_reachable_stateBefore E rho k x) V hVpre
    have hrecv := pcsa_proposer_body_before_vote_win E rho h hF hD
      (hT := pcsa_floor_freeze_next hT) k a x y hx hy (s + 1)
      V.target hk (le_refl _) hc hVB
    have hVBdst : V.target ∈ dst.base.blocks := by
      change V.target ∈ (clock p _ _).base.blocks
      rwa [pcsa_clock_blocks]
    have hf : dst.fg.F = .genesis := by
      change (clock p _ _).fg.F = .genesis
      rw [pcsa_body_clock_fg]
      exact (hF y hy a).1
    have hvalid : pcValid dst V = true :=
      Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hw, decide_eq_true hVBdst⟩,
        CleanPCRelay.pcsa_activeCompatible_genesis dst hf V.target⟩
    have hVcar : V ∈ carriedPCs dst (s + 1) := pcsa_carriedPC_of_proposal dst (s + 1) N
      hslot (by change _ ∈ (clock p _ _).proposals; rwa [pcsa_clock_proposals]) V hNp hvalid
    have hVsource : V ∈ sources := List.mem_filter.mpr
      ⟨List.mem_append_right _ hVcar, pcsa_clock_target_active E rho hF a y hy _ V hVBdst⟩
    have upper (C : PC p.n) (hm : C ∈ sources) : C.slot ≤ V.slot := by
      rcases List.mem_append.mp (List.mem_filter.mp hm).1 with hfrozen | hcar
      · obtain ⟨D, hDmem, hDs, _⟩ := frozen C hfrozen
        rw [← hDs]
        exact pcsa_clean_bestPC_slot_ge _ D V hDmem hsv
      · have heq : C = V := Option.some.inj ((carried C hcar).symm.trans hNp)
        rw [heq]
    obtain ⟨D, hbest⟩ := Option.isSome_iff_exists.mp (pcsa_bestPC_isSome_of_mem sources V hVsource)
    have hd : voterPC p dst (s + 1) = some D := hview.trans hbest
    have hDs : D.slot = V.slot := Nat.le_antisymm (upper D (bestPC_mem sources D hbest))
      (pcsa_clean_bestPC_slot_ge sources V D hVsource hbest)
    obtain ⟨u, hDack, _⟩ := pcsa_voterPC_honest_ack_before E rho h hFault a y hy (s + 1)
      (le_refl _) D hd
    have hDt := pcsa_ack_targets_unique E rho h hF hFault u z V.slot D.target V.target
      (hDs ▸ hDack) hAck
    rw [hd]
    exact congrArg some hDt
/-- At an honest proposal, the actual proposer and voter PC views have the same target. -/
theorem pcsa_common_view_targets (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (k : Nat) (y : V) (hy : y ∈ rho.honest) (s : Slot) (N : NamedProposal p.n)
    (hx : rho.seatOf (.prop (s + 1)) (0 : Fin 1) ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.prop (s + 1)) (0 : Fin 1))
      (⟨.seat (.prop (s + 1)) (0 : Fin 1), .proposal N⟩ : Obj p)
        (SA.proposalTime p.toParams (s + 1)))
    (hk : rho.events[k]? = some (.tick (rho.seatOf (.prop (s + 1)) (0 : Fin 1))
      (SA.proposalTime p.toParams (s + 1))))
    (hslot : N.slot = s + 1)
    (hc : SA.voteTime p.toParams (s + 1) ≤ cut)
    (hmem : (⟨.proposer (s + 1), .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1)))
        y).st.proposals)
    (hpc : N.pc = proposerPC p (clock p (V2.D.Run.stateBefore E rho k
      (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st (SA.proposalTime p.toParams (s + 1)))) :
    (voterPC p (clock p (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1))) y).st
        (SA.voteTime p.toParams (s + 1))) (s + 1)).map PC.target =
      (proposerPC p (clock p (V2.D.Run.stateBefore E rho k
        (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
          (SA.proposalTime p.toParams (s + 1)))).map PC.target :=
  pcsa_common_view_targets_win E rho h hF hFault (pcsa_strictFrom_of_healthy E rho hD 0) k y hy s
    N hx he hk hslot (pcsa_floor_freeze (pcsa_zero_le_proposal s)) hc hmem hpc
end AvailableChain.PCSA.Run

end
