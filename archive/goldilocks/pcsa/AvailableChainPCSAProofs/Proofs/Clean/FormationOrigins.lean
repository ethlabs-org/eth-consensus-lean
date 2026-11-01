module
public import AvailableChainPCSAProofs.Proofs.Shared.Certificates
public import AvailableChainPCSAProofs.Proofs.Shared.FormationWindow
public import AvailableChainPCSAProofs.Proofs.Clean.FormationView
public import AvailableChainPCSAProofs.Proofs.Shared.RelayRun

public section

/-! Frozen-PC origins for Formation. Shared stage-1 retention fixes each
frozen row. Its PCs have whole-PC acceptance origins no later than the
freeze. F1 gives the receiver either a held key or a strict earlier handler.
This closes hFrozenPCOrigin at the actual early read. The valid
certificate origins are the Shared/VoterView ones. Target-body receipt
and the resulting collection remain separate inputs. -/

open AvailableChain AvailableChain.SimplexFG
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- The original frozen-key origin follows from its valid certificate origin. -/
theorem pcsa_formation_frozen_pc_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hBase : Base₂ p c E rho)
    (hFrame : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest)
    (K : Nat) (s : Slot) (C : PC p.n)
    (hC : C ∈ pcSnapshotAt (V2.D.Run.stateBefore E rho K x).st s) :
    ∃ j t D, t ≤ SA.freezeTime p.toParams s ∧ D.slot = C.slot ∧ D.target = C.target ∧
      V2.D.Run.acceptsAt E rho j x (⟨.none, .pc D⟩ : Obj p) t := by
  obtain ⟨j, t, D, ht, hs, hb, _, ha⟩ := pcsa_frozen_pc_origin_valid
    E rho hBase hFrame x hx K s C hC
  exact ⟨j, t, D, ht, hs, hb, ha⟩

end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}
omit [Fintype V] in
/-- The original read interface follows from the valid certificate origin. -/
theorem pcsa_formation_frozen_pc_origin_read (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hBase : Base₂ p c E rho)
    (hFrame : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest)
    (s : Slot) (t : Time) (nd : Node p) (C : PC p.n)
    (hr : pcsa_postClock E rho x t = some nd) (ht : t ≠ SA.freezeTime p.toParams s)
    (hC : C ∈ pcSnapshotAt nd.st s) :
    ∃ j u D, u ≤ SA.freezeTime p.toParams s ∧ D.slot = C.slot ∧ D.target = C.target ∧
      V2.D.Run.acceptsAt E rho j x (⟨.none, .pc D⟩ : Obj p) u := by
  obtain ⟨j, u, D, hu, hs, hb, _, ha⟩ := pcsa_frozen_pc_origin_read_valid
    E rho hBase hFrame x hx s t nd C hr ht hC
  exact ⟨j, u, D, hu, hs, hb, ha⟩

/-- F1 supplies old-PC receipt from the run, without hFrozenPCOrigin. -/
theorem pcsa_formation_frozen_pc_receipt_of_run (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (x y : V) (nd : Node p) (C : PC p.n)
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hr : pcsa_postClock E rho x (SA.earlyTime p.toParams s) = some nd)
    (hFrozen : C ∈ pcSnapshotAt nd.st (s - 1)) :
    (∃ A ∈ (V2.D.Run.stateBeforeTime E rho (SA.proposalTime p.toParams s) y).st.pcs,
      A.slot = C.slot ∧ A.target = C.target) ∨
      ∃ D u k, D.slot = C.slot ∧ D.target = C.target ∧
        u < SA.proposalTime p.toParams s ∧
        V2.D.Run.handlesAt E rho k y (⟨.none, .pc D⟩ : Obj p) u := by
  have ht : SA.earlyTime p.toParams s ≠ SA.freezeTime p.toParams (s - 1) := by
    have hs : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by
      have hnat : s - 1 + 1 = s := Nat.sub_add_cancel h.slotPos
      have hi : ((s - 1 : Nat) : Int) + 1 = (s : Int) := by exact_mod_cast hnat
      omega
    have hd : (0 : Int) < p.Δ := p.deltaPos
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≠ 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ
    rw [hs]
    nlinarith
  exact pcsa_formation_frozen_pc_receipt E rho s N ΔF h x y nd C hx hy hFrozen
    (fun A hA => pcsa_formation_frozen_pc_origin_read E rho h.base h.frame x hx
      (s - 1) _ nd A hr ht hA)
end AvailableChain.PCSA.Run

end
