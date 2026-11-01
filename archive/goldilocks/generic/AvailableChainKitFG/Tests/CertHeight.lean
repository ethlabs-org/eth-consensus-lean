module
public import AvailableChainKitFG.Correspondence -- shake: keep (examples)

-- Test values are private; production code must not import Tests.
set_option linter.privateModule false

/-! The finalized checkpoint does not fix the certificate height. Genesis is
finalized at height 0 in the genesis state and at height 1 in `certK`, after
`B1` justifies it at height 1. So R-XING takes the height of an explicit
accepted certificate (a carrier `K`), not a function of F (01:212).
Requested by fgsa-lean (DC ruling 2026-09-30). -/

namespace AvailableChain.KitFG.Tests.CertHeight

open AvailableChain.SimplexFG

/-- A finality row of seat `i` for genesis at height 1. -/
def finalRow (i : Fin 4) : Row (Fin 4) :=
  ⟨i, .vote 2 B1.root true, some ⟨1, genesisRoot⟩⟩

/-- `B1` and three finality rows: genesis becomes final at height 1. -/
def certK : FGBlock (Fin 4) :=
  .node B1 2 ⟨100⟩ 0 [finalRow 0, finalRow 1, finalRow 2]

example : (derive E4 cfg1 (.genesis : FGBlock (Fin 4))).F = .genesis ∧
    (derive E4 cfg1 certK).F = .genesis ∧
    (derive E4 cfg1 (.genesis : FGBlock (Fin 4))).h_F = 0 ∧
    (derive E4 cfg1 certK).h_F = 1 := by decide +kernel

end AvailableChain.KitFG.Tests.CertHeight
