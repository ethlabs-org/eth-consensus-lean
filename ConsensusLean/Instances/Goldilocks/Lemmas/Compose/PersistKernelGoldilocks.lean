module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.PersistKernel
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Induction
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks suppliers for the conditional persistence kernel -/

namespace Consensus.Goldilocks.Compose
open SA (SAParams ReplayOrder Vote Payload)
variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Set (Fin sp.n)} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {proposer : Nat → Fin sp.n} {ΔF : Time} {x : Fin sp.n} {i₀ s m : Nat}
  {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}

end Consensus.Goldilocks.Compose
