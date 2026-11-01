module
public import AvailableChainPCSAProofs.Proofs.Shared.RestartSeed

public section

/-! The recovered-suffix output of the CI restart from label `s` (pcsa34-r5 §5.5).
It orders the recovered descendants of the seed block `P`: results, held PCs,
selected PCs and records from label `s` through the cut. -/
namespace AvailableChain.PCSA.Run
variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In) {m : FGMode}
    (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))

/-- The suffix invariant from the restart label `s` with seed `P` through `cut`. -/
structure RecoveredSuffixInvariant (s : Slot) (P : Block) (cut : Time) : Prop where
  resultsChain :
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ (i i' : Slot) (X Y : Block),
      s ≤ i → i ≤ i' → SA.gateTime p.toParams i' ≤ cut →
      gateResultAt p c E rho x i = some (some X) →
      gateResultAt p c E rho y i' = some (some Y) →
      (i < i' → Block.Preceq X Y) ∧ (i = i' → Block.Compatible X Y)
  pcChain :
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ (t t' : Time) (C D : PC p.n),
      t ≤ cut → t' ≤ cut → s ≤ C.slot → s ≤ D.slot →
      C ∈ (storeAt p c E rho x t).pcs → D ∈ (storeAt p c E rho y t').pcs →
      Block.Compatible C.target D.target ∧ (C.slot < D.slot → Block.Preceq C.target D.target)
  pcResults :
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ (t : Time) (C : PC p.n) (i : Slot) (X : Block),
      t ≤ cut → s ≤ C.slot → s ≤ i → SA.gateTime p.toParams i ≤ cut →
      C ∈ (storeAt p c E rho x t).pcs → gateResultAt p c E rho y i = some (some X) →
      Block.Compatible C.target X
  selected :
    ∀ x ∈ rho.honest, ∀ t : Time, SA.freezeTime p.toParams s ≤ t → t ≤ cut →
      ∃ C ∈ (storeAt p c E rho x t).pcs,
        latestPC (storeAt p c E rho x t) = some C ∧ s ≤ C.slot ∧ Block.Preceq P C.target
  recordOrigin :
    ∀ x ∈ rho.honest, ∀ t : Time, SA.gateTime p.toParams s ≤ t → t ≤ cut →
      ∃ (i : Slot) (X : Block), s ≤ i ∧ SA.gateTime p.toParams i ≤ t ∧
        gateResultAt p c E rho x i = some (some X) ∧
        (storeAt p c E rho x t).base.stableRecord = X
  recordMono :
    ∀ x ∈ rho.honest, ∀ t t' : Time, SA.gateTime p.toParams s ≤ t → t ≤ t' → t' ≤ cut →
      Block.Preceq (storeAt p c E rho x t).base.stableRecord
        (storeAt p c E rho x t').base.stableRecord
  gateAdvance :
    ∀ u : Slot, s ≤ u → SA.gateTime p.toParams u ≤ cut → ∀ x ∈ rho.honest, ∀ X : Block,
      gateResultAt p c E rho x u = some (some X) →
      Block.Preceq X (storeAt p c E rho x (SA.gateTime p.toParams u)).base.stableRecord
  honestGate :
    ∀ (u : Slot) (B : Block), s ≤ u →
      Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho u B →
      SA.gateTime p.toParams u ≤ cut → ∀ x ∈ rho.honest,
        gateResultAt p c E rho x u = some (some B)

end AvailableChain.PCSA.Run

end
