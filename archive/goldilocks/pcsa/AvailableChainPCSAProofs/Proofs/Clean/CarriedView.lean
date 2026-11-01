module
public import AvailableChainPCSAProofs.Proofs.Clean.CommonRaw

public section

/-! C6 CarriedView: concrete receipt and count support. -/
namespace AvailableChain.PCSA
/-- A stored proposal contributes its valid carried PC to its slot's source list. -/
theorem pcsa_carriedPC_of_proposal (st : State n) (s : Slot) (N : NamedProposal n)
    (hslot : N.slot = s) (hN : (⟨.proposer s, .proposal N⟩ : Wire n) ∈ st.proposals)
    (C : PC n) (hC : N.pc = some C) (hv : pcValid st C = true) : C ∈ carriedPCs st s := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_filterMap.mpr ⟨⟨.proposer s, .proposal N⟩, hN, ?_⟩, hv⟩
  change (if N.slot = s then N.pc else none) = some C
  rw [ite_eq_left hslot]
  exact hC
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Every carried PC at an honest proposer slot is the PC in its exact emitted metadata. -/
theorem pcsa_carriedPC_eq_emitted (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.ExecutionValid E rho)
    (k : Nat) (y : V) (s : Slot) (N : NamedProposal p.n)
    (hx : rho.seatOf (.prop s) (0 : Fin 1) ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.prop s) (0 : Fin 1))
      (⟨.seat (.prop s) (0 : Fin 1), .proposal N⟩ : Obj p) (SA.proposalTime p.toParams s))
    (C : PC p.n) (hC : C ∈ carriedPCs (V2.D.Run.stateBefore E rho k y).st s) :
    N.pc = some C := by
  obtain ⟨w, hw, hpc⟩ := List.mem_filterMap.mp (List.mem_filter.mp hC).1
  cases hd : w.decode with
  | none => rw [hd] at hpc; cases hpc
  | some msg => cases msg with
    | vote r i b => rw [hd] at hpc; cases hpc
    | row i body => rw [hd] at hpc; cases hpc
    | ack r i b => rw [hd] at hpc; cases hpc
    | pc D => rw [hd] at hpc; cases hpc
    | block r M =>
      rw [hd] at hpc
      change (if M.slot = s then M.pc else none) = some C at hpc
      split at hpc
      · rename_i hslot
        have hrs := (pcsa_proposal_pool_slot E rho hv.toDeliveryWellFormed k y w r M hw hd).trans
          hslot
        rw [hrs] at hd
        have hMN := pcsa_proposal_decoded_eq_emitted E rho hv k y s N hx he w hw M hd
        rwa [hMN] at hpc
      · cases hpc
end AvailableChain.PCSA.Run

end
