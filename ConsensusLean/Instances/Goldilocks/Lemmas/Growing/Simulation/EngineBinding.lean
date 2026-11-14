module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunTransport

public section

/-! # The Goldilocks engine binding

`goldilocksEngineBinding S pub hn` binds the compiled family `goldilocksWith S` at public
parameters `pub` to the shared Goldilocks run interface: each valid engine run with those public
parameters is represented by its run map (`goldilocksRunMap`), whose signer is the run
interface's (`goldilocksRunMap_signer`), and transports to a run of the interface
(`goldilocksRunMap_transport`). -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The Goldilocks engine binding** at public parameters `pub`. -/
noncomputable def goldilocksEngineBinding (S : BoundSetup) (pub : Model.Public)
    (hn : 1 ≤ pub.n) :
    Generic.EngineBinding (V := V) (F := goldilocksWith S)
      (A := goldilocksNode (S.params pub hn) (S.ro _)) pub (payloadOf S) (fun v => v.val)
      (Generic.goldilocksRunInterface (S.params pub hn) (S.ro _)) where
  map E hE rho hv := by
    subst hE
    exact goldilocksRunMap S rho hn hv
  signer_eq E hE rho hv := by
    subst hE
    exact (goldilocksRunMap_signer S rho hn hv).symm
  run_transport E hE rho hv := by
    subst hE
    exact goldilocksRunMap_transport S rho hn hv

end Consensus.Goldilocks.Simulation

end
