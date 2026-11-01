module
public import AvailableChainFGSARun.Statements.Roots -- shake: keep (axioms)

@[expose] public section

namespace AvailableChain.FGSA.Run.Tests.NVDigest

/-- ROOT-DIGEST W3: the NV digest uses the slot and keeps genesis root 0 separate. -/
def nvDigest (d : DigestInput 1) : BlockId := ⟨d.slot + 1⟩

/-- ROOT-DIGEST W3: a proposed body has the small slot root before any run premise. -/
theorem proposal_slot_root (p : Params)
    (hd : ∀ d : DigestInput p.n, p.digest d = ⟨d.slot + 1⟩)
    (H : Block) (s : Slot) (app : Nat)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) :
    (proposalBlock p H s app raw support rows).root = ⟨s + 1⟩ := by
  change p.digest ⟨H.root, s, app, rows, raw, support⟩ = _
  exact hd _

/-- ROOT-DIGEST W3: small roots can collide on content outside the actual NV run. -/
theorem same_slot_collision :
    nvDigest ⟨genesisRoot, 1, 0, [], [], []⟩ =
      nvDigest ⟨genesisRoot, 1, 1, [], [], []⟩ ∧
    (⟨genesisRoot, 1, 0, [], [], []⟩ : DigestInput 1) ≠
      ⟨genesisRoot, 1, 1, [], [], []⟩ := by decide +kernel

/-- ROOT-DIGEST W3: 405 keeps the same proposal-grid upper bound as 404. -/
theorem live_horizon_grid :
    (303 : Time) + (2 * 49 + 4) = 405 ∧
    405 / 4 = (404 / 4 : Nat) ∧ 405 + 1 = (406 : Nat) ∧
    (405 / 4 + 1 : Nat) < 128 := by decide +kernel

#print axioms proposal_slot_root
#print axioms same_slot_collision
#print axioms live_horizon_grid

end AvailableChain.FGSA.Run.Tests.NVDigest
end

-- ROOT-DIGEST: public fixture dependency audit.
#print axioms AvailableChain.FGSA.Run.Tests.NVDigest.nvDigest
