module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunTransport

public section

/-! # The Goldilocks engine binding

`goldilocksEngineBinding S A pub hn` binds the compiled family `goldilocks S` at public
parameters `pub` to the shared Goldilocks run interface: each valid engine run with those public
parameters is represented by its run map (`goldilocksRunMap`), whose signer is the run
interface's (`goldilocksRunMap_signer`), and transports to a run of the interface
(`goldilocksRunMap_transport`). -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The Goldilocks engine binding** at public parameters `pub`. -/
noncomputable def goldilocksEngineBinding (S : Setup) (A : ContractAssumptions S)
    (pub : Model.Public) (hn : 1 ≤ pub.n) :
    Generic.EngineBinding (V := V) (F := goldilocks S)
      (A := goldilocksNode (S.params pub hn) (S.ro _)) pub (payloadOf S) (fun v => v.val)
      (Generic.goldilocksRunInterface (S.params pub hn) (S.ro _) (S.sign pub) A.signGap) where
  map E hE rho hv := by
    subst hE
    exact goldilocksRunMap S rho hn hv
  signer_eq E hE rho hv := by
    subst hE
    exact (goldilocksRunMap_signer S rho hn hv).symm
  run_transport E hE rho hv := by
    subst hE
    exact goldilocksRunMap_transport S rho hn A hv

/-- At an environment's public parameters the binding uses its canonical run map. -/
theorem goldilocksEngineBinding_map (S : Setup) (A : ContractAssumptions S) (E : Env V)
    (hn : 1 ≤ (pubOf E).n) (rho : Model.Run (compiled (goldilocks S)) E)
    (hv : rho.ExecutionValid) :
    (goldilocksEngineBinding S A (pubOf E) hn).map E rfl rho hv =
      goldilocksRunMap S rho hn hv := by rfl

end Consensus.Goldilocks.Simulation

end
