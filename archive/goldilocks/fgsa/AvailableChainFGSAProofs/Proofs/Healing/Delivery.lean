module
public import AvailableChainFGSAProofs.Proofs.Healing.SourceTiming
public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem delivery_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

/-- Blueprint 21:550–567 (IF.5), 2646–2652 (H.12); B13, B15, B17, B26.
DC: SAME admission or coverage at the exact strict-before freeze read.
Assembly supplies `sourceDiscipline_tSrc` as `source` and `fgsa_rMono` as `mono`.
The consumers prove compatibility; this producer keeps its frozen antecedent. -/
theorem healing_tDel [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (source : TSrc p c E rho) (mono : RMonoAll p c E rho)
    (hServices : ∀ y r K, y ∈ rho.honest →
      actionSourceFG p c E rho y r = some (some K) →
      recoveryStart p E ≤ SA.voteTime p.toParams (r * p.R) →
      SA.freezeTime p.toParams (r * p.R) ≤ rho.horizon →
      ∀ x ∈ rho.honest, FGBlock.Preceq
        (rho.stateBeforeTime E (SA.freezeTime p.toParams (r * p.R)) x).st.fg.F K →
      ∀ j z W, z ∈ rho.honest →
      rho.events[j]? = some (.tick z (SA.voteTime p.toParams (r * p.R))) →
      W ∈ (storeAt p c E rho j z).fg.TF →
      FGBlock.Preceq K W →
      FGBlock.Preceq
        (rho.stateBeforeTime E (SA.earlyTime p.toParams (r * p.R)) x).st.fg.F W →
      TargetReceiptService E rho (eraseFG W) (SA.earlyTime p.toParams (r * p.R)) x) :
    TDel p c E rho := by
  intro y r K hy hK hready hhor x hx
  have hgst : E.t_GST ≤ SA.voteTime p.toParams (r * p.R) := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  rw [Gen.V2.Duty.HoldsBefore_def]
  intro hcompat
  change (Block.preceq (eraseFG K) _ || Block.preceq _ (eraseFG K)) = true at hcompat
  rcases Bool.or_eq_true_iff.mp hcompat with hKF | hFK
  · exact Or.inr (delivery_lift hKF)
  · left
    have heD : SA.earlyTime p.toParams (r * p.R) ≤
        SA.freezeTime p.toParams (r * p.R) := by
      change 4 * p.Δ * ((r * p.R : Nat) : Int) + 2 * p.Δ ≤
        4 * p.Δ * ((r * p.R : Nat) : Int) + 3 * p.Δ
      linarith [p.deltaPos]
    exact healing_source_body_relay E rho hrec source mono hy hx hK hgst heD hhor
      (delivery_lift hFK) (hServices y r K hy hK hready hhor x hx (delivery_lift hFK))

/-- Ordinary source delivery from sleep recovery and the named source/mono producers.
The selected object service is constructed at the source's actual vote tick. -/
theorem healing_tDel_recovery [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (source : TSrc p c E rho) (mono : RMonoAll p c E rho) : TDel p c E rho := by
  apply healing_tDel E rho hrec.toRecovery₂ source mono
  intro y r K hy hK hready hhor x hx hFK j z W hz hj hW hKW hFloor
  apply healing_source_delivery_service E rho hrec hz hx hj hW
  · have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  · apply le_trans _ hhor
    change 4 * p.Δ * ((r * p.R : Nat) : Int) + 2 * p.Δ ≤
      4 * p.Δ * ((r * p.R : Nat) : Int) + 3 * p.Δ
    linarith [p.deltaPos]
  · exact hFloor

end AvailableChain.FGSA.Run
end
