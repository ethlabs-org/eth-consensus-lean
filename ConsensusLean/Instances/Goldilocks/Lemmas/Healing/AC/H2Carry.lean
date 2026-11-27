module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay

public section

/-! # Goldilocks Healing: `Carry` from the writer, with catch-up -/

namespace Consensus.Goldilocks.AC

open Compose

variable {FGP : Type} {sp : ACParams} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {T : GTrace sp FGP}

end Consensus.Goldilocks.AC

end
