module
public import AvailableChainSimplexFG.Frame

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

/-- Under fixed controls, a lower F move removes exactly the strict ancestors
of F′ from the old domain and preserves the domain in a top-J phase.
DC: none; INTENTIONAL addition: FJ phase-dependent domain; record
blueprint/21-healing.md:691–694, 2579–2581. -/
def LowerFDomainIdentityStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig)
    (c : Controls V) (F' : FGBlock V)
    (blocks : Finset (FGBlock V)),
    FGBlock.Preceq c.F F' →
    (c.rootIsJ = false → hOf E cfg F' < c.lo) →
    (c.rootIsJ = true → FGBlock.Preceq F' c.J) →
    (∀ W ∈ blocks,
      hOf E cfg F' < hOf E cfg W → FGBlock.Preceq F' W) →
    let oldDomain := filteredFrom E cfg c blocks
    let newDomain := filteredFrom E cfg { c with F := F' } blocks
    newDomain =
      oldDomain.filter (fun B => FGBlock.preceq F' B) ∧
    (∀ B ∈ oldDomain,
      B ∉ newDomain ↔ FGBlock.Preceq B F' ∧ B ≠ F') ∧
    (c.rootIsJ = true → newDomain = oldDomain)

/-- The complete argument list of the exact strict-ancestor removal set.
DC: none; INTENTIONAL addition: FJ phase-dependent domain; record
blueprint/21-healing.md:691–694, 2579–2581. -/
theorem LowerFDomainIdentityStatement_def :
    LowerFDomainIdentityStatement =
      (∀ {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
        (E : Electorate V) (cfg : FGConfig)
        (c : Controls V) (F' : FGBlock V)
        (blocks : Finset (FGBlock V)),
        FGBlock.Preceq c.F F' →
        (c.rootIsJ = false → hOf E cfg F' < c.lo) →
        (c.rootIsJ = true → FGBlock.Preceq F' c.J) →
        (∀ W ∈ blocks,
          hOf E cfg F' < hOf E cfg W → FGBlock.Preceq F' W) →
        let oldDomain := filteredFrom E cfg c blocks
        let newDomain :=
          filteredFrom E cfg { c with F := F' } blocks
        newDomain =
          oldDomain.filter (fun B => FGBlock.preceq F' B) ∧
        (∀ B ∈ oldDomain,
          B ∉ newDomain ↔ FGBlock.Preceq B F' ∧ B ≠ F') ∧
        (c.rootIsJ = true → newDomain = oldDomain)) := by rfl

end AvailableChain.KitFG
end
