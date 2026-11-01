module
public import AvailableChainPCSAProofs.Proofs.Clean.C9Stamp

public section

/-! C9 stamping in a strict delivery window, with equal honest HEADs as a premise. -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Equal honest HEADs and a quorum stamp the honest proposal before its freeze. -/
theorem pcsa_clean_honestProposal_stamped_from [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho)
    {T₀ cut : Time} (hD : StrictFrom E rho T₀ cut) (hcut : cut ≤ rho.horizon)
    (s : Slot) (hT : T₀ ≤ SA.freezeTime p.toParams s) (N : NamedProposal p.n)
    (hN : HonestNamedProposal p c E rho (s + 1) N)
    (hHeads : ∀ x H, HonestHeadAt p c E rho x (s + 1) H → H = N.erase)
    (hQ : nQuorum p.n ≤ (awakeHonestLabel p c E rho (s + 1)).card)
    (hz : SA.freezeTime p.toParams (s + 1) ≤ cut) :
    ∀ y ∈ rho.honest,
      PCStampedBefore p c E rho y (SA.freezeTime p.toParams (s + 1)) (s + 1) N.erase := by
  have hp : (0 : Int) < p.Δ := p.deltaPos
  have hez : SA.earlyTime p.toParams (s + 1) ≤ SA.freezeTime p.toParams (s + 1) := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + 2 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + 3 * p.Δ
    linarith
  have hve : SA.voteTime p.toParams (s + 1) ≤ SA.earlyTime p.toParams (s + 1) := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + 2 * p.Δ
    linarith
  have hec := hez.trans hz
  have hvc := hve.trans hec
  have hTp := pcsa_floor_freeze_next hT
  obtain ⟨hw, he⟩ := hN
  have hslot : N.erase.slot = s + 1 := pcsa_proposal_emitted_slot E rho _ (s + 1) N _ he
  have hNc := pcsa_c9_early_N_win E rho h hF hD (s + 1) N.erase (pcsa_floor_vote hTp) hec
    (hec.trans hcut) hQ hHeads
  have hAck : ∀ y ∈ rho.honest, E.awake y (SA.earlyTime p.toParams (s + 1)) = true →
      HonestAckAt p c E rho y (s + 1) N.erase := by
    intro y hy haw
    obtain ⟨nd, hnd, hn⟩ := hNc y hy
    exact pcsa_c9_honestAck E rho (s + 1) N.erase y nd hy haw hnd hslot hn
      (pcsa_c9_early_view_below_win E rho h hF hFault hD s N hw he hT hvc y hy nd hnd)
  have hBody : ∀ y ∈ rho.honest, N.erase ∈ (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams (s + 1))) y).st.base.blocks :=
    fun y hy => (pcsa_honest_proposal_before_vote_win E rho h hF hD _ y hw hy (s + 1)
      N he hTp hvc _ (pcsa_c9_idxBefore_mono rho (hve.trans hez))).2
  exact pcsa_c9_stamped_win E rho h hF hD (s + 1) N.erase (Nat.succ_pos s) hslot
    (pcsa_floor_early hTp) hz (hz.trans hcut) hBody
    (pcsa_c9_ack_quorum E rho h (s + 1) N.erase hQ hAck)

end AvailableChain.PCSA.Run

end
