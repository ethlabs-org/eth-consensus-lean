module
public import AvailableChainKitFG.RecordHighOnce -- shake: keep (examples)

public section

set_option maxRecDepth 4096

namespace AvailableChain.KitFG.Tests.RecordHighOnce

open AvailableChain.SimplexFG

-- At the inclusive cut, same-height finality is removed. The theorem still
-- protects the returned record and every released height pair.
example :
    let step := createRowOnce E4 cfg1 RecordOnce.initial 0 (some .genesis) clientHdB1
    HighRecord 1 (fun _ => genesisRoot) step.2.toRecord ∧
      (∀ a, step.1 = some a →
        ∀ h T timeout, a.height_pair = .vote h T timeout →
        1 ≤ h → T = genesisRoot ∧ timeout = false) := by
  apply recordHighOnce E4 cfg1 1 (fun _ => genesisRoot) RecordOnce.initial 0
    (some .genesis) clientHdB1
    (fun _ _ => ⟨Or.inl rfl, rfl, Or.inl rfl⟩)
  · intro h T hf _
    change some (1, genesisRoot) = some (h, T) at hf
    cases hf
    rfl
  · intro fp hfp _
    exact congrArg FinalityPair.target (finality_pair_record_conditions hfp).1

example :
    (createRowOnce E4 cfg1 RecordOnce.initial 0 (some .genesis) clientHdB1).1 =
      some ⟨0, .vote 1 genesisRoot false, none⟩ ∧
    (createRowOnce E4 cfg1 RecordOnce.initial 0 (some .genesis) clientHdB1).2.lock 1 =
      none := by decide +kernel

-- Lower finality stays on the row. The high guard applies at height two.
example : HighRecord 2 (fun _ => B1.root)
    (createRowOnce E4 cfg1 RecordOnce.initial 0 (some B1) clientHdB1).2.toRecord := by
  apply (recordHighOnce E4 cfg1 2 (fun _ => B1.root) RecordOnce.initial 0
    (some B1) clientHdB1
    (fun _ _ => ⟨Or.inl rfl, rfl, Or.inl rfl⟩) ?_ ?_).1
  · intro h T hf _
    have hs : (some B1).map (fun C => ((derive E4 cfg1 C).h,
        (derive E4 cfg1 C).T_h.root)) = some (2, B1.root) := by decide +kernel
    rw [hs] at hf
    cases hf
    rfl
  · intro fp hfp hh
    have heq := congrArg FinalityPair.height (finality_pair_record_conditions hfp).1
    change fp.height = 1 at heq
    simp only [Height] at *
    omega

example :
    (createRowOnce E4 cfg1 RecordOnce.initial 0 (some B1) clientHdB1).1 =
      some ⟨0, .vote 2 B1.root false, some ⟨1, genesisRoot⟩⟩ := by decide +kernel

-- No source means no write, including no write of provisional finality.
example :
    (createRowOnce E4 cfg1 RecordOnce.initial 0 none clientHdB1).2 =
      RecordOnce.initial := by
  exact createRowOnce_none E4 cfg1 RecordOnce.initial 0 none clientHdB1 (by decide +kernel)

-- A same-height repeat is suppressed. Its new finality is not recorded.
example :
    let Λ := clientRecordOnce E4 cfg1 0 RecordOnce.initial [(some B1, clientHdNone)]
    (createRowOnce E4 cfg1 Λ 0 (some B1) clientHdB1).1 = none ∧
      (createRowOnce E4 cfg1 Λ 0 (some B1) clientHdB1).2 = Λ := by
  dsimp only
  refine ⟨by decide +kernel, ?_⟩
  apply createRowOnce_none
  decide +kernel

end AvailableChain.KitFG.Tests.RecordHighOnce
end
