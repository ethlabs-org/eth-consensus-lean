module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Candidates.LateCertificate

@[expose] public section

/-! # The late-certificate SA at a write mode: the parent link

`certModes_parent`: at the parent's mode the late-certificate SA at a mode is the late-certificate
SA (a propositional equality: a trace of one is a trace of the other up to rewriting along it). -/

namespace Consensus.Goldilocks.LateCertificate.Test.CertModes

open SA

variable {sp : SAParams} {FGP : Type}

/-- **At the parent's mode, the late-certificate SA at a mode is the late-certificate SA.** -/
theorem certModes_parent (ro : ReplayOrder sp FGP) :
    certRecoverySAM sp (WriteMode.parent sp) FGP ro = certRecoverySA sp FGP ro :=
  certRecoverySAM_parent ro

end Consensus.Goldilocks.LateCertificate.Test.CertModes

end
