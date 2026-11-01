module
public import AvailableChainFramework
public import AvailableChainLStar.Proofs.Hooks
public import AvailableChainLStar.Statements.Contract

@[expose] public section

namespace AvailableChain.Registry.LStar

open AvailableChain.Framework AvailableChain.LStar

/-- L* meets the E4 hook obligations with the third equivocation and the
stored-block wire as `excludes`. The facts are in
`AvailableChainLStar/Proofs/Hooks.lean`. -/
theorem lstarHooks (p : Params) (n : Nat) : HooksSound (lstar p n) :=
  ⟨LStar.excludes_inert p, LStar.excludes_stable p, LStar.processed_stable p,
    LStar.deps_stable p, LStar.handles_carries p⟩

/-- L* with `n` validators. An instance with hooks. It is not an eligible
candidate: eligibility and certificates are plan 1c. No `holdsAt` theorem: L*
has no contract proof (`Statements/Contract.lean:60-63` is a statement). -/
def lstarInst (p : Params) (n : Nat) : Instance :=
  ⟨n, lstar p n, p.Δ, p.deltaPos, lstarInterface p n, lstarHooks p n⟩

end AvailableChain.Registry.LStar

end
