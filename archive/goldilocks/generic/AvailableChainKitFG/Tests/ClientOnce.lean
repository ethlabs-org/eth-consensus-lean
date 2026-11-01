module
public import AvailableChainKitFG.ClientOnceSafety -- shake: keep (examples)

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

set_option maxRecDepth 4096

namespace AvailableChain.KitFG.Tests.ClientOnce

open AvailableChain.SimplexFG

-- No source means no row, even when the head supplies finality.
example : (createRowOnce E4 cfg1 RecordOnce.initial 0 none clientHdB1).1 = none := by
  decide +kernel

example : (createRowOnce E4 cfg1 RecordOnce.initial 0 none clientHdB1).2 =
    RecordOnce.initial := by rfl

-- A provisional lock on another entry blocks the height pair and is not stored.
example : (createRowOnce E4 cfg1 RecordOnce.initial 0 (some B1) ⟨2, ⟨5⟩, 0⟩).1 = none ∧
    (createRowOnce E4 cfg1 RecordOnce.initial 0 (some B1) ⟨2, ⟨5⟩, 0⟩).2.sent = [] ∧
    (createRowOnce E4 cfg1 RecordOnce.initial 0 (some B1) ⟨2, ⟨5⟩, 0⟩).2.lock 2 = none := by
  decide +kernel

-- A durable lock on another entry also blocks release.
example : (createRowOnce E4 cfg1 ⟨Record.initial.with_lock 2 ⟨5⟩, []⟩ 0
    (some B1) clientHdNone).1 = none := by decide +kernel

-- A new finality pair cannot cause a second target at the same height.
example : clientRunOnce E4 cfg1 0 RecordOnce.initial
    [(some B1, clientHdNone), (some B1, clientHdB1)] =
      [⟨0, .vote 2 B1.root false, none⟩] := by decide +kernel

example : (clientRecordOnce E4 cfg1 0 RecordOnce.initial
    [(some B1, clientHdNone), (some B1, clientHdB1)]).lock 1 = none := by decide +kernel

-- A timeout can name a different entry at the same height.
example : clientRunOnce E4 cfg1 0 RecordOnce.initial
    [(some B1, clientHdNone), (some clientB1alt, clientHdNone)] =
      [⟨0, .vote 2 B1.root false, none⟩,
       ⟨0, .vote 2 clientB1alt.root true, none⟩] := by decide +kernel

-- Once the timeout is recorded, another new entry can also be named.
example : clientRunOnce E4 cfg1 0 RecordOnce.initial
    [(some B1, clientHdNone), (some clientB1alt, clientHdNone),
     (some (.node .genesis 1 ⟨100⟩ 2 [rowT 0, rowT 1, rowT 2]), clientHdNone)] =
      [⟨0, .vote 2 B1.root false, none⟩,
       ⟨0, .vote 2 clientB1alt.root true, none⟩,
       ⟨0, .vote 2 (FGBlock.node .genesis 1 ⟨100⟩ 2 [rowT 0, rowT 1, rowT 2]).root true, none⟩] :=
           by
  decide +kernel

-- Full-content repeats are suppressed, including repeats of a timeout.
example : clientRunOnce E4 cfg1 0 RecordOnce.initial
    [(some B1, clientHdNone), (some clientB1alt, clientHdNone),
     (some clientB1alt, clientHdNone), (some B1, clientHdNone)] =
      [⟨0, .vote 2 B1.root false, none⟩,
       ⟨0, .vote 2 clientB1alt.root true, none⟩] := by decide +kernel

-- The key includes the finality pair and the timeout flag.
example : (⟨0, .vote 2 B1.root false, none⟩ : Row (Fin 4)).onceKey ≠
    (⟨0, .vote 2 B1.root false, some ⟨1, genesisRoot⟩⟩ : Row (Fin 4)).onceKey ∧
    (⟨0, .vote 2 B1.root false, none⟩ : Row (Fin 4)).onceKey ≠
    (⟨0, .vote 2 B1.root true, none⟩ : Row (Fin 4)).onceKey := by decide +kernel

-- Same-height finality is removed and does not write a lock.
example : clientRunOnce E4 cfg1 0 RecordOnce.initial [(some .genesis, clientHdB1)] =
    [⟨0, .vote 1 genesisRoot false, none⟩] ∧
    (clientRecordOnce E4 cfg1 0 RecordOnce.initial [(some .genesis, clientHdB1)]).lock 1 =
      none := by decide +kernel

-- A lower height also cannot carry the head's finality pair.
example : clientRunOnce E4 cfg1 0 RecordOnce.initial [(some B1, ⟨3, ⟨5⟩, 0⟩)] =
    [⟨0, .vote 2 B1.root false, none⟩] := by decide +kernel

-- The next higher-height row can carry freshly computed finality.
example : clientRunOnce E4 cfg1 0 RecordOnce.initial
    [(some .genesis, clientHdB1), (some B1, clientHdB1)] =
      [⟨0, .vote 1 genesisRoot false, none⟩,
       ⟨0, .vote 2 B1.root false, some ⟨1, genesisRoot⟩⟩] ∧
    (clientRecordOnce E4 cfg1 0 RecordOnce.initial
      [(some .genesis, clientHdB1), (some B1, clientHdB1)]).lock 1 = some genesisRoot := by
  decide +kernel

-- Suppressed finality is recomputed, not queued for the next action.
example : clientRunOnce E4 cfg1 0 RecordOnce.initial
    [(some .genesis, clientHdB1), (some B1, clientHdNone)] =
      [⟨0, .vote 1 genesisRoot false, none⟩, ⟨0, .vote 2 B1.root false, none⟩] := by
  decide +kernel

-- Resume from the durable record: the previous content stays suppressed.
example : clientRunOnce E4 cfg1 0
    (clientRecordOnce E4 cfg1 0 RecordOnce.initial [(some B1, clientHdNone)])
    [(some B1, clientHdB1)] = [] := by decide +kernel

end AvailableChain.KitFG.Tests.ClientOnce
end
