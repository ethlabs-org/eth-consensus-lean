module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.PrefixSteps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Core

public section

/-! # Uniqueness of a signing within one honest client prefix -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp}

/-- Signing uniqueness read on the signer's own honest observation prefix. -/
theorem sign_unique_at_core
    {u frameOf ini} {H : Time → Set (Fin sp.n)}
    (rc : GoldilocksRunCore u frameOf proposer dg H tr ini)
    {v : Fin sp.n} {d d' : Nat} {att : FG.Att sp.n}
    (hv : v ∈ H (tr.time d)) (hdd : d' ≤ d)
    (hs : tr.SignAt v d' att) (hs' : tr.SignAt v d att) : d' = d := by
  exact Healing.sign_unique_core (rc.upTo (rc.time_nonneg d)) hv
    ((RunTrace.upTo_signAt tr).mpr ⟨rc.time_mono hdd, hs⟩)
    ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs'⟩)

/-- A client executing honestly throughout a prefix signs an attestation at most once. -/
theorem sign_unique {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : GoldilocksRun proposer dg H tr ini)
    {v : Fin sp.n} (hv : v ∈ H)
    {d d' : Nat} {att : FG.Att sp.n} (hs : tr.SignAt v d att) (hs' : tr.SignAt v d' att) :
    d = d' :=
  Healing.sign_unique hrun hv hs hs'

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
