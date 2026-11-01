module
public import AvailableChainPCSAProofs.Proofs.Clean.VoterAuthenticity
public import AvailableChainPCSAProofs.Proofs.Clean.NReadTransport
public import AvailableChainPCSAProofs.Proofs.Clean.NWalkCounts
public import AvailableChainPCSAProofs.Proofs.Clean.VoteTransport
public import AvailableChainPCSAProofs.Proofs.Clean.StepAck
public import AvailableChainPCSAProofs.Proofs.Clean.PendingGates
public import AvailableChainPCSAProofs.Proofs.Clean.NRoot
public import AvailableChainPCSAProofs.Proofs.Clean.CutReads

public section

/-! C6 PendingNHead: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}
/-- Actual N receipt forces the next HEAD above the target once its root is compatible. -/
theorem pcsa_N_next_head_of_root_at_vote (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (hFault : FaultsBelowQA p c rho) (a : Nat) (x y : V) (hx : x ∈ rho.honest)
    (v : Time) (s : Slot) (B H : Block) (hc : SA.voteTime p.toParams (s + 1) ≤ cut)
    (hN : holdsN p (actView (clock p (V2.D.Run.stateBefore E rho a x).st v)) s B = true)
    (hH : HonestHeadAt p c E rho y (s + 1) H)
    (hroot : ∀ R, liveRootAt p c E rho y (s + 1) = some R → Block.Compatible R B) :
    Block.Preceq B H := by
  classical
  have hy := hH.1
  have hhead := hH.2.2
  rw [pcsa_voteHeadAt_def] at hhead
  obtain ⟨nd, hnd, hhead⟩ := Option.map_eq_some_iff.mp hhead
  obtain ⟨k, hk, hstore⟩ := pcsa_postClock_source E rho y _ nd hnd
  have hR : liveRootAt p c E rho y (s + 1) =
      some (liveRoot p nd.st (voterPC p nd.st (s + 1))) := by
    rw [pcsa_liveRootAt_def, hnd]
    rfl
  have hcompat := hroot _ hR
  rw [hstore] at hhead hcompat
  let dst := clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s + 1))
  let raw := headVotes p dst (s + 1)
  let sup := headSupport p dst (s + 1)
  have hfcut : SA.freezeTime p.toParams s ≤ cut := by
    apply le_trans _ hc
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤
      4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    have hp := p.deltaPos
    linarith
  have hfk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ k := by
    apply Nat.le_of_not_gt
    intro hlt
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff h.base.valid.toScheduleWellFormed hk _).mp hlt
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 3 * p.Δ at ht
    push_cast at ht
    have hp := p.deltaPos
    nlinarith
  have hread := pcsa_N_read_transport E rho h.base hF h.healthy a k x y hx hy v
    (SA.voteTime p.toParams (s + 1)) s B hfcut hfk hN
  let F := Finset.univ.filter (fun i : Fin p.n => rho.seatOf (.base (.head s)) i ∉ rho.honest)
  have hFcard : F.card < pcQuorum p.n := by
    apply lt_of_le_of_lt _ hFault
    apply Finset.card_le_card_of_injOn (fun i : Fin p.n => rho.seatOf (.base (.head s)) i)
    · intro i hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    · intro i _ j _ he
      exact (h.base.cstar (.base (.head s)) trivial).1 he
  have hcaps : ∀ i, GridCO.equivocates raw i = true → i ∈ F := by
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hh
    have hf := pcsa_voter_honest_not_capped_unconditional E rho h.base.valid k y
      (SA.voteTime p.toParams (s + 1)) s i hh
    change GridCO.equivocates raw i = false at hf
    rw [hi] at hf
    cases hf
  have hsub : sup ⊆ raw :=
    pcsa_headSupport_subset_at_read E rho h.base.valid.toDeliveryWellFormed k y _ (s + 1)
  obtain ⟨hmaj, hdom⟩ := pcsa_N_score_dominance dst.base.blocks raw sup B F hsub hFcard hcaps
    hread.1
  have hcover := pcsa_headInTree_covers_of_transfer p dst (voterPC p dst (s + 1))
    (erasedList dst (KitFG.storeFrameView (FGSA.heightView p) dst.fg (voterBlocks p dst (s + 1))))
    raw sup B hcompat (fun C _ hCB => (hread.2.2 C hCB).2) hmaj hdom
  delta headVote at hhead
  rw [ite_eq_right (Nat.succ_ne_zero s)] at hhead
  rw [← hhead]
  exact hcover
/-- An honest ack disseminates into the next HEAD under its separate N-root premise. -/
theorem pcsa_honestAck_next_head_of_root_at_vote (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (hFault : FaultsBelowQA p c rho) (x y : V) (s : Slot) (B H : Block)
    (hc : SA.voteTime p.toParams (s + 1) ≤ cut) (hAck : HonestAckAt p c E rho x s B)
    (hH : HonestHeadAt p c E rho y (s + 1) H)
    (hroot : ∀ R, liveRootAt p c E rho y (s + 1) = some R → Block.Compatible R B) :
    Block.Preceq B H := by
  obtain ⟨nd, hnd, _, _, hN, _⟩ := pcsa_honestAck_N_source E rho x s B hAck
  obtain ⟨a, _, hstore⟩ := pcsa_postClock_source E rho x _ nd hnd
  rw [hstore] at hN
  exact pcsa_N_next_head_of_root_at_vote E rho h hF hFault a x y hAck.1 _ s B H hc hN hH hroot
end AvailableChain.PCSA.Run

end
