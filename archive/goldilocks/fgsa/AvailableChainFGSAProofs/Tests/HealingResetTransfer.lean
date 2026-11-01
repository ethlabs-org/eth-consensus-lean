module
public import AvailableChainFGSAProofs.Proofs.Healing.ResetTransfer -- shake: keep (reset fixtures)

public section

namespace AvailableChain.FGSA.Run.Tests.HealingResetTransfer
open AvailableChain.SimplexFG

-- Pure/model fixture: s = u − 1 acts after both slot-u duty reads.
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

-- Pure/model fixture: q_(s*) is strictly before d_(s*).
example (p : Params) (s : Slot) :
    SA.releaseTime p.toParams s < SA.gateTime p.toParams s := by
  change 4 * p.Δ * (s : Int) + 5 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
  linarith [p.deltaPos]

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- Conditional package fixture: A supplies the actual reset-delivery premise.
example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (xing : RXing p c E rho) (cap : RCap p c E rho) (source : TSrc p c E rho)
    (mono : RMonoAll p c E rho) (w : HealingWitness)
    (hServices : H0Reset p c E rho w →
      SA.releaseTime p.toParams w.sStar ≤ rho.horizon →
      ∀ x ∈ rho.honest, ∀ j z W, z ∈ rho.honest →
      rho.events[j]? = some (.tick z (SA.voteTime p.toParams w.sStar)) →
      W ∈ (storeAt p c E rho j z).fg.TF →
      Block.Preceq w.CStar (eraseFG W) →
      FGBlock.Preceq
        (rho.stateBeforeTime E (SA.earlyTime p.toParams w.sStar) x).st.fg.F W →
      TargetReceiptService E rho (eraseFG W) (SA.earlyTime p.toParams w.sStar) x)
    (h0r : H0Reset p c E rho w)
    (hhor : SA.releaseTime p.toParams w.sStar ≤ rho.horizon) :
    ∀ x ∈ rho.honest, Gen.V2.Duty.HoldsBefore E rho
      (fun nd => ∃ C ∈ nd.st.fg.TF, eraseFG C = w.CStar)
      (SA.releaseTime p.toParams w.sStar) x :=
  healing_tDelReset_core E rho hrec source mono w h0r hhor
    (healing_low_finality_at_reset_reset E rho hrec xing cap source w h0r) (hServices h0r hhor)

-- Conditional package fixture: C closes the frozen contract without a floor premise.
example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (xing : RXing p c E rho) (cap : RCap p c E rho) (source : TSrc p c E rho)
    (mono : RMonoAll p c E rho) (w : HealingWitness)
    (hServices : H0Reset p c E rho w →
      SA.releaseTime p.toParams w.sStar ≤ rho.horizon →
      ∀ x ∈ rho.honest, ∀ j z W, z ∈ rho.honest →
      rho.events[j]? = some (.tick z (SA.voteTime p.toParams w.sStar)) →
      W ∈ (storeAt p c E rho j z).fg.TF →
      Block.Preceq w.CStar (eraseFG W) →
      FGBlock.Preceq
        (rho.stateBeforeTime E (SA.earlyTime p.toParams w.sStar) x).st.fg.F W →
      TargetReceiptService E rho (eraseFG W) (SA.earlyTime p.toParams w.sStar) x) :
    TDelReset p c E rho w :=
  healing_tDelReset_of_reset E rho hrec xing cap source mono w hServices

end AvailableChain.FGSA.Run.Tests.HealingResetTransfer
end
