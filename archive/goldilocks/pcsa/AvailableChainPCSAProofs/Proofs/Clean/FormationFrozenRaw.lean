module
public import AvailableChainPCSAProofs.Proofs.Clean.FormationRetainedBack
public import AvailableChainPCSAProofs.Proofs.Clean.HeadRelay
public import AvailableChainPCSAProofs.Proofs.Clean.CommonInputs
public import AvailableChainPCSAProofs.Proofs.Shared.CleanWindow

public section

/-! The frozen raw relay at the Formation reads. Formation delivery is strict
from `z_{s-1}` (`pcsa_strictFrom_of_within`). A slot-`(s-1)` HEAD stamped
before `z_{s-1}` at an honest voter was accepted before `z_{s-1}`, so the
windowed HEAD relay gives it, or a cap of its seat, at the proposer by
`max t z_{s-1} + Δ = t_s`. -/

open AvailableChain AvailableChain.SimplexFG
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- Formation delivery is strict delivery from `z_{s-1}` to the freeze. -/
theorem pcsa_formation_strictFrom (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) :
    StrictFrom E rho (SA.freezeTime p.toParams (s - 1)) (SA.freezeTime p.toParams s) :=
  pcsa_strictFrom_of_within E rho h.delivery

/-- The frozen raw relay holds at the actual proposer and voter reads. -/
theorem pcsa_formation_frozen_raw (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (src dst : Node p) (y : V)
    (hSrc : pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src)
    (hy : y ∈ rho.honest)
    (hDst : pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst) :
    FormationFrozenRawOpen p src dst s := by
  have hS := h.base.valid.toScheduleWellFormed
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have hs1 : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by
    have hi : ((s - 1 : Nat) : Int) + 1 = (s : Int) := by
      exact_mod_cast Nat.sub_add_cancel h.slotPos
    omega
  have hpub : V2.PublicTime E (SA.freezeTime p.toParams (s - 1)) := by
    refine ⟨4 * (s - 1) + 3, ?_⟩
    rw [h.base.delta]
    change 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ = ((4 * (s - 1) + 3 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hzero : 0 ≤ SA.freezeTime p.toParams (s - 1) := by
    change 0 ≤ 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ
    positivity
  have hdl : SA.freezeTime p.toParams (s - 1) + E.Δ =
      GridCO.proposalTime p.toParams.engine s := by
    rw [h.base.delta]
    change 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ + p.Δ = 4 * p.Δ * (s : Int)
    rw [hs1]
    ring
  have hcut : GridCO.proposalTime p.toParams.engine s ≤ SA.freezeTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    linarith
  have hgate : GridCO.proposalTime p.toParams.engine s ≤ SA.gateTime p.toParams (s - 1) := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * ((s - 1 : Nat) : Int) + 6 * p.Δ
    rw [hs1]
    linarith
  have hss : s - 1 + 1 = s := Nat.sub_add_cancel h.slotPos
  rw [pcsa_postClock_def] at hSrc hDst
  obtain ⟨pre, hpre, hc⟩ := Option.map_eq_some_iff.mp hSrc
  rw [pcsa_preTick_def] at hpre
  obtain ⟨k, hidx, he⟩ := Option.map_eq_some_iff.mp hpre
  subst pre
  subst src
  obtain ⟨pre', hpre', hc'⟩ := Option.map_eq_some_iff.mp hDst
  rw [pcsa_preTick_def] at hpre'
  obtain ⟨a, _, he'⟩ := Option.map_eq_some_iff.mp hpre'
  subst pre'
  subst dst
  have htick := V2.D.Run.tickIdx?_spec hidx
  have hk' : rho.events[k]? = some (.tick
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (GridCO.proposalTime p.toParams.engine (s - 1 + 1))) := by
    rw [hss]
    exact htick
  have hle : V2.D.Run.idxBefore rho (GridCO.proposalTime p.toParams.engine s) ≤ k := by
    apply Nat.le_of_not_gt
    intro hn
    exact lt_irrefl _ ((Gen.V2.Duty.index_lt_idxBefore_iff hS htick _).mp hn)
  have hEq := pcsa_proposer_late_eq E rho h.base k _ (s - 1) hk'
  rw [hss] at hEq
  constructor
  intro i r hm hs
  have hm2 : (⟨.seat (s - 1) i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (clock p (V2.D.Run.stateBefore E rho a y).st (SA.voteTime p.toParams s)).base.votes := hm
  rw [pcsa_clock_heads] at hm2
  obtain ⟨row, hr⟩ := pcsa_head_stamp_lookup E rho a y ⟨.seat (s - 1) i, .head r⟩ hm2
  have hstamp : GridCO.stampVote (clock p (V2.D.Run.stateBefore E rho a y).st
      (SA.voteTime p.toParams s)).base ⟨.seat (s - 1) i, .head r⟩ =
      GridCO.stampVote (V2.D.Run.stateBefore E rho a y).st.base ⟨.seat (s - 1) i, .head r⟩ := by
    delta GridCO.stampVote
    rw [pcsa_clock_headStamps, hr]
    rfl
  have hs2 : GridCO.stampVote (V2.D.Run.stateBefore E rho a y).st.base
      ⟨.seat (s - 1) i, .head r⟩ < SA.freezeTime p.toParams (s - 1) := by
    rw [← hstamp]
    exact hs
  obtain ⟨j, _, t, ha, ht⟩ := pcsa_head_accepted_before E rho hS h.base.noRestart a y (s - 1)
    i r _ hpub hzero hm2 hs2
  have hmax : max t (SA.freezeTime p.toParams (s - 1)) + E.Δ =
      GridCO.proposalTime p.toParams.engine s := by
    rw [max_eq_right (le_of_lt ht), hdl]
  have hR := pcsa_head_relay_late_or_cap_win E rho h.base
    (pcsa_formation_strictFrom E rho s N ΔF h) j k y _ hy h.proposal.1 (s - 1) i r t
    (GridCO.proposalTime p.toParams.engine s) ha (hmax.trans_le hcut)
    (hmax.trans_le hgate) (hmax ▸ hle)
  change _ ∈ proposerVotes (clock p (V2.D.Run.stateBefore E rho k _).st
      (GridCO.proposalTime p.toParams.engine s)) s ∨
    GridCO.equivocates (proposerVotes (clock p (V2.D.Run.stateBefore E rho k _).st
      (GridCO.proposalTime p.toParams.engine s)) s) i = true
  rw [← hEq]
  exact hR

/-- The pre-freeze inputs from the premise alone. -/
theorem pcsa_formation_preFreeze_inputs_of_premise (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) :
    FormationPreFreezeInputs E rho s N :=
  pcsa_formation_preFreeze_inputs_of_frozen E rho s N ΔF h (fun src dst y hs hy _ hd =>
    pcsa_formation_frozen_raw E rho s N ΔF h src dst y hs hy hd)

end AvailableChain.PCSA.Run
end
