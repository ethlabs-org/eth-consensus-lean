module
public import AvailableChainPCSAProofs.Proofs.Shared.VoterView
public import AvailableChainPCSAProofs.Proofs.Recovery.Exclusions

public section

/-! F3 under RECOVERY (pcsa34-r4.3b §5.6.1 step 1): the common view field of
the Formation premise at a slot whose proposal time is at least `t_GST + Δ`,
from the RECOVERY delivery premise and the Shared voter view; and block
admission (B1): the target of a PC held before `z_{s-1}` is stored at every
honest node before `t_s`. -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- [pcsa34-r4.3b §5.6.1 step 1 (F3)] Under RECOVERY, at a slot `s` with
`t_GST + Δ ≤ t_s`, every honest voter awake at `v_s` has the view target of the
honest slot-`s` proposal's PC. -/
theorem recovery_commonView (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho) (s : Slot) (hs : 0 < s)
    (ha : E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s)
    (hh : SA.gateTime p.toParams s ≤ rho.horizon)
    (N : NamedProposal p.n) (hN : HonestNamedProposal p c E rho s N) :
    ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams s) = true →
      (viewAt p c E rho y s).map (Option.map PC.target) = some (N.pc.map PC.target) := by
  have hd := p.deltaPos
  have hvg : SA.voteTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  exact pcsa_commonView_of_delivery E rho h.base hF s hs N hN
    (recovery_delivery_from_run E rho h s hs ha hh) hvg (hvg.trans hh)

/-- [pcsa34-r4.3b §5.6.1 (B1)] Under RECOVERY, at a slot `s > 0` with
`t_GST + Δ ≤ t_s` and `d_s` in the run, the target of a PC that an honest node
holds before `z_{s-1}` is a stored block of every honest node before `t_s`
(the deadline `max t z_{s-1} + Δ` is `t_s` at `z_{s-1}`). -/
theorem recovery_installed_target_body (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho) (s : Slot) (hs : 0 < s)
    (ha : E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s)
    (hh : SA.gateTime p.toParams s ≤ rho.horizon)
    (y : V) (hy : y ∈ rho.honest) (C : PC p.n)
    (hC : C ∈ (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams (s - 1)) y).st.pcs)
    (x : V) (hx : x ∈ rho.honest) :
    C.target ∈
      (V2.D.Run.stateBeforeTime E rho (SA.proposalTime p.toParams s) x).st.base.blocks := by
  have hS := h.base.valid.toScheduleWellFormed
  have hd := p.deltaPos
  have hΔ := E.Δ_pos
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hC
  have hT0 := (pcsa_outageStore_stateBefore E rho _ y hy).pcBlocks C hC
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hT0
  have hz : max (SA.freezeTime p.toParams (s - 1)) (SA.freezeTime p.toParams (s - 1)) + E.Δ =
      SA.proposalTime p.toParams s := by
    rw [max_self, h.base.delta]
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, (Nat.sub_add_cancel hs).symm⟩
    rw [Nat.add_sub_cancel]
    change 4 * p.Δ * (s' : Int) + 3 * p.Δ + p.Δ = 4 * p.Δ * ((s' + 1 : Nat) : Int)
    push_cast
    ring
  have hmono : Monotone (fun t => max t (SA.freezeTime p.toParams (s - 1)) + E.Δ) := by
    intro a b hab
    dsimp only
    exact Int.add_le_add_right (max_le_max hab (le_refl _)) E.Δ
  have hlt : ∀ t, t < max t (SA.freezeTime p.toParams (s - 1)) + E.Δ := fun t =>
    lt_of_le_of_lt (le_max_left t _) (lt_add_of_pos_right _ hΔ)
  have hcut : max (SA.freezeTime p.toParams (s - 1)) (SA.freezeTime p.toParams (s - 1)) +
      E.Δ ≤ SA.gateTime p.toParams s := by
    rw [hz]
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hB := pcsa_stored_body_within_on E rho h.base hF
    (recovery_delivery_from_run E rho h s hs ha hh)
    (fun o s N hdec => pcsa_block_isNonRow o s N hdec) hmono hlt y x hy hx _ hcut C.target hT0
  rwa [hz] at hB

end AvailableChain.PCSA.Run
end
