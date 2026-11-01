module
public import AvailableChainFGSAProofs.Proofs.Foundations.Export -- shake: keep (L42 export boundary)

public section

/-! F1.1 foundation claims, exposed through the L42 assembly boundary. -/

namespace AvailableChain.FGSA.Run

/-- The assembly boundary supplies durable data, local stamps, and all-run FG bounds. -/
theorem assembly_sleep_channels (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) :
    RStoreDurable p c E rho ∧ RStoreEpoch p c E rho ∧
      RMonoAll p c E rho ∧ RFrameNextEpoch p c E rho :=
  ⟨fgsa_rStoreDurable p c E rho, fgsa_rStoreEpoch p c E rho,
    fgsa_rMonoAll p c E rho, fgsa_rFrameNextEpoch p c E rho⟩

/-- Recovery supplies row service without a whole-run no-restart assumption. -/
theorem assembly_rows_of_healingSet (p : Params) {In V : Type}
    [DecidableEq V] [Fintype V] (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (h : HealingSet p c E rho G ΔF) : TRows p c E rho ΔF :=
  fgsa_tRows_recovery p c E rho h.toRecovery₂

end AvailableChain.FGSA.Run
end
