module
public import AvailableChainKitFG.TwoChanges -- shake: keep (examples)

public section

set_option maxRecDepth 4096

namespace AvailableChain.KitFG.Tests.LowerFDomain

open AvailableChain.SimplexFG

def blocks : View (Fin 4) := {.genesis, B1a, B1b, childA}

def fControls : Controls (Fin 4) := ⟨.genesis, 4, 0, .genesis, false⟩

def jControls : Controls (Fin 4) := ⟨.genesis, 3, 2, B1a, false⟩

-- The F-root cut removes genesis and retains both F′ and its child.
example : filteredFrom E4 cfg1 { fControls with F := B1a } blocks = {B1a, childA} := by
  rw [(lowerF_domain_identity E4 cfg1 fControls B1a blocks
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).1]
  decide +kernel

-- The exact removal criterion applies to a strict ancestor in the old domain.
example :
    .genesis ∉ filteredFrom E4 cfg1 { fControls with F := B1a } blocks ↔
      FGBlock.Preceq .genesis B1a ∧ (.genesis : FGBlock (Fin 4)) ≠ B1a :=
  (lowerF_domain_identity E4 cfg1 fControls B1a blocks
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).2.1 .genesis (by decide +kernel)

-- F′ itself is an old member, so the strict inequality is necessary.
example :
    B1a ∉ filteredFrom E4 cfg1 { fControls with F := B1a } blocks ↔
      FGBlock.Preceq B1a B1a ∧ B1a ≠ B1a :=
  (lowerF_domain_identity E4 cfg1 fControls B1a blocks
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).2.1 B1a (by decide +kernel)

-- The top-J domain is unchanged by the same F move.
example : filteredFrom E4 cfg1 { jControls with F := B1a } blocks =
    filteredFrom E4 cfg1 jControls blocks :=
  (lowerF_domain_identity E4 cfg1 jControls B1a blocks
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).2.2 (by decide +kernel)

-- Both phases occur; the sibling is outside the old domain in both cases.
example : fControls.rootIsJ = false ∧ jControls.rootIsJ = true ∧
    filteredFrom E4 cfg1 fControls blocks = {.genesis, B1a, childA} ∧
    filteredFrom E4 cfg1 jControls blocks = {B1a, childA} ∧
    B1b ∉ filteredFrom E4 cfg1 fControls blocks ∧
    B1b ∉ filteredFrom E4 cfg1 jControls blocks := by
  decide +kernel

end AvailableChain.KitFG.Tests.LowerFDomain
end
