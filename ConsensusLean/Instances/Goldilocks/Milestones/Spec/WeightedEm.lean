module
public import ConsensusLean.Instances.Goldilocks.Spec.WeightedLocks.LateCertificate

@[expose] public section

/-! # Weighted emissions, forgotten

An emission of the weighted SA forgotten to the parent's state at its read point (`projEm`), and
an emission of the late-certificate SA forgotten to the weighted SA's (`projC`). They have their
own layer because the parent-mode lemmas (`Lemmas.AC`) and the candidate projections
(`Milestones.Spec.Candidates`) both read them, and only leaf layers may import the Candidates
layers. Definitions only; their characterising lemmas (`projEm_eq`, `map_projC_liftEm`) are in
`Lemmas/AC/Candidates`. -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable {sp : SAParams} {FGP : Type}

/-- The projection of an emission to the parent's state at its read point. -/
def projEm (e : EmW sp FGP) : Em sp FGP :=
  ⟨e.msg, e.readPoint.ac, e.head⟩

end Consensus.Goldilocks.EvidenceRelease

namespace Consensus.Goldilocks.LateCertificate

open SA EvidenceRelease

variable {sp : SAParams} {FGP : Type}

/-- An emission with its archive forgotten. -/
def projC (e : EmC sp FGP) : EmW sp FGP := ⟨e.msg, e.readPoint.er, e.head⟩

end Consensus.Goldilocks.LateCertificate

end
