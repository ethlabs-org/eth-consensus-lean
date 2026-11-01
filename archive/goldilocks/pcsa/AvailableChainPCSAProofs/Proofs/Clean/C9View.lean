module
public import AvailableChainPCSAProofs.Proofs.Clean.C9Early
public import AvailableChainPCSAProofs.Proofs.Clean.CommonViews
public import AvailableChainPCSAProofs.Proofs.Clean.ProposerInputs
public import AvailableChainPCSAProofs.Proofs.Clean.ProposalDelivery
public import AvailableChainPCSAProofs.Proofs.Clean.PCScope
public import AvailableChainPCSAProofs.Proofs.Clean.HonestProposal

public section

/-! C9 early view (pcsa34-r4.3 §5.3, A2). At the early read of label `s + 1`,
every view target is below the honest proposal: a carried view PC is the
proposal's PC, and a frozen view PC has the slot and target of a proposer PC,
so the proposal's PC (also a view source) has the same slot and, by honest-ack
uniqueness, the same target. The proposal's PC target is below its parent. -/

namespace AvailableChain.PCSA

/-- An early time is never a freeze time. -/
theorem pcsa_c9_early_ne_freeze (p : Params) (s r : Slot) :
    SA.earlyTime p.toParams s ≠ SA.freezeTime p.toParams r := by
  intro he
  change 4 * p.Δ * (s : Int) + 2 * p.Δ = 4 * p.Δ * (r : Int) + 3 * p.Δ at he
  have hp := p.deltaPos
  rcases le_or_gt s r with h | h
  · have hh : (s : Int) ≤ (r : Int) := Int.ofNat_le.mpr h
    nlinarith
  · have hh : (r : Int) + 1 ≤ (s : Int) := by exact_mod_cast h
    nlinarith

/-- Early ticks leave the frozen PC source lists unchanged. -/
theorem pcsa_c9_early_snapshot (p : Params) (st : State p.n) (s : Slot) :
    (clock p st (SA.earlyTime p.toParams s)).pcSnapshot = st.pcSnapshot := by
  have he : (clock p st (SA.earlyTime p.toParams s)).pcSnapshot =
      (clockPre p st (SA.earlyTime p.toParams s)).pcSnapshot := by
    delta clock
    dsimp only
    split
    · exact gateStep_snapshot _ _ _
    · rfl
  rw [he, clockPre_snapshot]
  dsimp only
  split
  · rename_i hf
    exact (pcsa_c9_early_ne_freeze p s _
      (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hf).2)).elim
  · rfl

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- At the early read of an honest proposal's label, every view target is below the proposal. -/
theorem pcsa_c9_early_view_below_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (s : Slot) (N : NamedProposal p.n)
    (hx : rho.seatOf (.prop (s + 1)) (0 : Fin 1) ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.prop (s + 1)) (0 : Fin 1))
      (⟨.seat (.prop (s + 1)) (0 : Fin 1), .proposal N⟩ : Obj p)
        (SA.proposalTime p.toParams (s + 1)))
    (hT : T₀ ≤ SA.freezeTime p.toParams s)
    (hc : SA.voteTime p.toParams (s + 1) ≤ cut)
    (y : V) (hy : y ∈ rho.honest) (nd : Node p)
    (hnd : pcsa_postClock E rho y (SA.earlyTime p.toParams (s + 1)) = some nd) :
    ∀ C, voterPC p nd.st (s + 1) = some C → Block.Preceq C.target N.erase := by
  intro C hC
  let x := rho.seatOf (.prop (s + 1)) (0 : Fin 1)
  obtain ⟨kp, hkp, _, hslot, _, _, hpc, hparent⟩ := pcsa_emitted_proposal_inputs E rho x (s + 1)
    N he
  obtain ⟨a, ha, haidx, hst⟩ := pcsa_c9_postClock_index E rho h y _ nd hnd
  let src := clock p (V2.D.Run.stateBefore E rho kp x).st (SA.proposalTime p.toParams (s + 1))
  let dst := clock p (V2.D.Run.stateBefore E rho a y).st (SA.earlyTime p.toParams (s + 1))
  let sources := (pcSnapshotAt dst s ++ carriedPCs dst (s + 1)).filter (frameActive p dst)
  have hp : (0 : Int) < p.Δ := p.deltaPos
  have hview : voterPC p dst (s + 1) = bestPC sources := by
    delta voterPC
    rw [Nat.add_sub_cancel]
  rw [hst] at hC
  change voterPC p dst (s + 1) = some C at hC
  rw [hview] at hC
  have hbelow : ∀ W, N.pc = some W → Block.Preceq W.target N.erase := by
    intro W hW
    have hsv : proposerPC p src = some W := hpc.symm.trans hW
    have hact : frameActive p src W = true := (List.mem_filter.mp (bestPC_mem _ W hsv)).2
    have hwalk := pcsa_headInTree_extends_view p src W (erasedList src (fullTree p src))
      (proposerVotes src (s + 1)) (proposerSupport src (s + 1)) hact
    have hpar : Block.Preceq W.target N.parent.erase := by
      rw [hparent, hsv]
      exact hwalk
    exact Gen.Pure.block_preceq_trans hpar (pcsa_named_parent_prefix N)
  rcases List.mem_append.mp (List.mem_filter.mp (bestPC_mem sources C hC)).1 with hfrozen | hcar
  · have hsnap : pcSnapshotAt dst s = pcSnapshotAt (V2.D.Run.stateBefore E rho a y).st s := by
      delta pcSnapshotAt
      rw [pcsa_c9_early_snapshot]
    have hvsnap : pcSnapshotAt (clock p (V2.D.Run.stateBefore E rho a y).st
        (SA.voteTime p.toParams (s + 1))) s =
        pcSnapshotAt (V2.D.Run.stateBefore E rho a y).st s := by
      delta pcSnapshotAt
      rw [pcsa_vote_snapshot]
    rw [hsnap, ← hvsnap] at hfrozen
    have hpropVote : SA.proposalTime p.toParams (s + 1) < SA.voteTime p.toParams (s + 1) := by
      change 4 * p.Δ * ((s + 1 : Nat) : Int) < 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
      linarith
    obtain ⟨D, hDmem, hDs, hDt, hDa⟩ := pcsa_frozen_pc_in_proposer_win E rho h hF hFault hD a kp y x
      hy hx s C hkp hT (hpropVote.le.trans hc) hfrozen
    have hDf : D ∈ src.pcs.filter (frameActive p src) := List.mem_filter.mpr ⟨hDmem, hDa⟩
    obtain ⟨W, hsv⟩ := Option.isSome_iff_exists.mp (pcsa_bestPC_isSome_of_mem _ D hDf)
    have hNp : N.pc = some W := hpc.trans hsv
    have hDW : D.slot ≤ W.slot := pcsa_clean_bestPC_slot_ge _ D W hDf hsv
    have hkbefore : kp ≤ V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1)) :=
      Nat.le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hkp _).mpr
        hpropVote)
    have hva : V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1)) ≤ a := by
      apply Nat.le_of_not_gt
      intro hn
      have ht := (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed ha _).mp hn
      change 4 * p.Δ * ((s + 1 : Nat) : Int) + 2 * p.Δ <
        4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ at ht
      linarith
    have hWm := (List.mem_filter.mp (bestPC_mem _ W hsv)).1
    have hWpre : W ∈ (V2.D.Run.stateBefore E rho kp x).st.pcs := by
      change W ∈ (clock p _ _).pcs at hWm
      rwa [pcsa_clock_pcs] at hWm
    have hDpre : D ∈ (V2.D.Run.stateBefore E rho kp x).st.pcs := by
      change D ∈ (clock p _ _).pcs at hDmem
      rwa [pcsa_clock_pcs] at hDmem
    obtain ⟨hw, z, hAckW, _⟩ := pcsa_pc_honest_ack_before E rho h hFault kp x hx _ hkbefore W hWpre
    obtain ⟨_, z', hAckD, _⟩ := pcsa_pc_honest_ack_before E rho h hFault kp x hx _ hkbefore D hDpre
    have hWB : W.target ∈ src.base.blocks := by
      change W.target ∈ (clock p _ _).base.blocks
      rw [pcsa_clock_blocks]
      exact pcsa_pc_targets_held p _ (pcsa_reachable_stateBefore E rho kp x) W hWpre
    have hrecv := pcsa_proposer_body_before_vote_win E rho h hF hD kp a x y hx hy (s + 1)
      W.target hkp hva (pcsa_floor_freeze_next hT) hc hWB
    have hWBdst : W.target ∈ dst.base.blocks := by
      change W.target ∈ (clock p _ _).base.blocks
      rwa [pcsa_clock_blocks]
    have hf : dst.fg.F = .genesis := by
      change (clock p _ _).fg.F = .genesis
      rw [pcsa_body_clock_fg]
      exact (hF y hy a).1
    have hvalid : pcValid dst W = true :=
      Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hw, decide_eq_true hWBdst⟩,
        CleanPCRelay.pcsa_activeCompatible_genesis dst hf W.target⟩
    have hmem := (pcsa_honest_proposal_before_vote_win E rho h hF hD x y hx hy (s + 1) N he
      (pcsa_floor_freeze_next hT) hc a hva).1
    have hWcar : W ∈ carriedPCs dst (s + 1) := pcsa_carriedPC_of_proposal dst (s + 1) N
      hslot (by change _ ∈ (clock p _ _).proposals; rwa [pcsa_clock_proposals]) W hNp hvalid
    have hWsource : W ∈ sources := List.mem_filter.mpr
      ⟨List.mem_append_right _ hWcar, pcsa_clock_target_active E rho hF a y hy _ W hWBdst⟩
    have hWC : W.slot ≤ C.slot := pcsa_clean_bestPC_slot_ge sources W C hWsource hC
    have hDWs : D.slot = W.slot := Nat.le_antisymm hDW (hDs ▸ hWC)
    have hDtW := pcsa_ack_targets_unique E rho h hF hFault z' z W.slot D.target W.target
      (hDWs ▸ hAckD) hAckW
    rw [← hDt, hDtW]
    exact hbelow W hNp
  · change C ∈ carriedPCs (clock p _ _) (s + 1) at hcar
    rw [pcsa_clock_carriedPCs] at hcar
    exact hbelow C (pcsa_carriedPC_eq_emitted E rho h.valid a y (s + 1) N hx he C hcar)

/-- At the early read of an honest proposal's label, every view target is below the proposal. -/
theorem pcsa_c9_early_view_below (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (s : Slot) (N : NamedProposal p.n)
    (hx : rho.seatOf (.prop (s + 1)) (0 : Fin 1) ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.prop (s + 1)) (0 : Fin 1))
      (⟨.seat (.prop (s + 1)) (0 : Fin 1), .proposal N⟩ : Obj p)
        (SA.proposalTime p.toParams (s + 1)))
    (hc : SA.voteTime p.toParams (s + 1) ≤ cut)
    (y : V) (hy : y ∈ rho.honest) (nd : Node p)
    (hnd : pcsa_postClock E rho y (SA.earlyTime p.toParams (s + 1)) = some nd) :
    ∀ C, voterPC p nd.st (s + 1) = some C → Block.Preceq C.target N.erase :=
  pcsa_c9_early_view_below_win E rho h hF hFault
    (pcsa_strictFrom_of_healthy E rho hD (SA.freezeTime p.toParams s)) s N hx he (le_refl _)
    hc y hy nd hnd

end AvailableChain.PCSA.Run

end
