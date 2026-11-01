module
public import AvailableChainPCSAProofs.Proofs.Shared.FormationWindow
public import AvailableChainPCSAProofs.Proofs.Clean.FormationTime
public import AvailableChainPCSAProofs.Proofs.Shared.PCViews
public import AvailableChainPCSAProofs.Proofs.Shared.RelayRun

public section

/-! Formation relay (pcsa34-r4.3b §5.3).
Shared supplies PC rank, acceptance, collection closure and retention.
F1 handles an accepted old PC before the proposal at each honest receiver. -/

open AvailableChain AvailableChain.SimplexFG
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
variable [Fintype V]

/-- F1 handles an accepted pre-freeze PC before the next proposal read.
The receiver does not need to be awake. -/
theorem pcsa_formation_old_pc_relay (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (j : Nat) (x y : V) (t : Time) (C : PC p.n)
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (ht : t ≤ SA.freezeTime p.toParams (s - 1))
    (hAccept : V2.D.Run.acceptsAt E rho j x (⟨.none, .pc C⟩ : Obj p) t)
    (hNeed : (pcsaWith m p c).processed (V2.D.Run.stateBefore E rho (j + 1) y)
      (⟨.none, .pc C⟩ : Obj p) = false) :
    ∃ u, t ≤ u ∧ u < SA.proposalTime p.toParams s ∧
      ∃ k, V2.D.Run.handlesAt E rho k y (⟨.none, .pc C⟩ : Obj p) u := by
  have hs : ((s - 1 : Nat) : Int) + 1 = (s : Int) := by
    exact_mod_cast Nat.sub_add_cancel (Nat.one_le_of_lt h.slotPos)
  have hdl : max t (SA.freezeTime p.toParams (s - 1)) + E.Δ =
      SA.proposalTime p.toParams s := by
    rw [max_eq_right ht, h.base.delta]
    change (4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ) + p.Δ = 4 * p.Δ * (s : Int)
    have hs' : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by omega
    rw [hs']
    ring
  have hcut : SA.proposalTime p.toParams s ≤ SA.freezeTime p.toParams s := by
    have hd : (0 : Int) < p.Δ := p.deltaPos
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    nlinarith
  have hr := h.delivery.relay x hx j (⟨.none, .pc C⟩ : Obj p) True.intro t
    hAccept y hy hNeed (by rw [hdl]; exact hcut) (pcsa_pc_not_excluded _ C)
  simpa only [hdl] using hr
end AvailableChain.PCSA.Run

end
