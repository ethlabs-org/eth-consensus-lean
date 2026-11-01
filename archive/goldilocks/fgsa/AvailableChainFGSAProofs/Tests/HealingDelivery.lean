module
public import AvailableChainFGSAProofs.Proofs.Healing.Delivery -- shake: keep (TDel fixture)

set_option linter.privateModule false

public section

namespace AvailableChain.FGSA.Run.Tests.HealingDelivery
open AvailableChain.SimplexFG

-- Pure/model fixture: s = u−1 acts after both slot-u duty reads.
example (p : Params) (s : Slot) :
    SA.gateTime p.toParams s = SA.proposalTime p.toParams (s + 1) + 2 * p.Δ ∧
      SA.voteTime p.toParams (s + 1) < SA.gateTime p.toParams s := by
  change 4 * p.Δ * (s : Int) + 6 * p.Δ =
      4 * p.Δ * ((s + 1 : Nat) : Int) + 2 * p.Δ ∧
    4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
  push_cast
  constructor
  · ring
  · linarith [p.deltaPos]

-- Pure/model fixture: finality above K discharges the coverage arm.
example (p : Params) (st : State p.n) (K : FGBlock (Fin p.n))
    (hKF : FGBlock.Preceq K st.fg.F) :
    (∀ B, FGBlock.Preceq B K → B ∈ st.fg.TF) ∨ FGBlock.Preceq K st.fg.F :=
  Or.inr hKF

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private def DeliveryServices : Prop :=
  ∀ y r K, y ∈ rho.honest →
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
    TargetReceiptService E rho (eraseFG W) (SA.earlyTime p.toParams (r * p.R)) x

-- Conditional package fixture: the frozen antecedent, as the consumer supplies it.
example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (source : TSrc p c E rho) (mono : RMonoAll p c E rho)
    (hServices : DeliveryServices p c E rho)
    {x y : V} {r : Nat} {K : FGBlock (Fin p.n)}
    (hy : y ∈ rho.honest) (hx : x ∈ rho.honest)
    (hK : actionSourceFG p c E rho y r = some (some K))
    (hgst : recoveryStart p E ≤ SA.voteTime p.toParams (r * p.R))
    (hhor : SA.freezeTime p.toParams (r * p.R) ≤ rho.horizon)
    (hcompat : Block.Compatible (eraseFG K)
      (eraseFG (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams (r * p.R)) x).st.fg.F)) :
    (∀ B, FGBlock.Preceq B K →
      B ∈ (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams (r * p.R)) x).st.fg.TF) ∨
      FGBlock.Preceq K
        (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams (r * p.R)) x).st.fg.F :=
  healing_tDel E rho hrec source mono hServices y r K hy hK hgst hhor x hx hcompat

-- Conditional package fixture: hcompat from K ⪯ F at the freeze read.
example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (source : TSrc p c E rho) (mono : RMonoAll p c E rho)
    (hServices : DeliveryServices p c E rho)
    {x y : V} {r : Nat} {K : FGBlock (Fin p.n)}
    (hy : y ∈ rho.honest) (hx : x ∈ rho.honest)
    (hK : actionSourceFG p c E rho y r = some (some K))
    (hgst : recoveryStart p E ≤ SA.voteTime p.toParams (r * p.R))
    (hhor : SA.freezeTime p.toParams (r * p.R) ≤ rho.horizon)
    (hKF : FGBlock.Preceq K
      (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams (r * p.R)) x).st.fg.F) :
    (∀ B, FGBlock.Preceq B K →
      B ∈ (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams (r * p.R)) x).st.fg.TF) ∨
      FGBlock.Preceq K
        (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams (r * p.R)) x).st.fg.F :=
  healing_tDel E rho hrec source mono hServices y r K hy hK hgst hhor x hx
    (Gen.Pure.block_compatible_of_common (eraseFG_preceq hKF) (Gen.Pure.block_preceq_refl _))

-- Conditional package fixture: hcompat from F ⪯ K at the freeze read.
example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (source : TSrc p c E rho) (mono : RMonoAll p c E rho)
    (hServices : DeliveryServices p c E rho)
    {x y : V} {r : Nat} {K : FGBlock (Fin p.n)}
    (hy : y ∈ rho.honest) (hx : x ∈ rho.honest)
    (hK : actionSourceFG p c E rho y r = some (some K))
    (hgst : recoveryStart p E ≤ SA.voteTime p.toParams (r * p.R))
    (hhor : SA.freezeTime p.toParams (r * p.R) ≤ rho.horizon)
    (hFK : FGBlock.Preceq
      (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams (r * p.R)) x).st.fg.F K) :
    (∀ B, FGBlock.Preceq B K →
      B ∈ (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams (r * p.R)) x).st.fg.TF) ∨
      FGBlock.Preceq K
        (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams (r * p.R)) x).st.fg.F :=
  healing_tDel E rho hrec source mono hServices y r K hy hK hgst hhor x hx
    (Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl _) (eraseFG_preceq hFK))

-- Conditional package fixture: an actual honest pre-GST body acceptance.
example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    {j : Nat} {y x : V} {t D : Time} {s : Slot} {N : NamedProposal p.n}
    {K : FGBlock (Fin p.n)}
    (hy : y ∈ rho.honest) (hx : x ∈ rho.honest)
    (ha : V2.D.Run.acceptsAt E rho j y (ofWire p ⟨.proposer s, .proposal N⟩) t)
    (ht : t < E.t_GST) (hKb : eraseFG K = N.erase)
    (hd : E.t_GST + p.Δ ≤ D) (hhor : D ≤ rho.horizon)
    (hF : FGBlock.Preceq (V2.D.Run.stateBeforeTime E rho D x).st.fg.F K)
    (hService : Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
      t D x)) :
    Gen.V2.Duty.HoldsBefore E rho
      (fun nd => ∀ B, FGBlock.Preceq B K → B ∈ nd.st.fg.TF) D x :=
  healing_source_old_body E rho hrec mono hy hx ha ht hKb hd hhor hF hService

end AvailableChain.FGSA.Run.Tests.HealingDelivery
end
