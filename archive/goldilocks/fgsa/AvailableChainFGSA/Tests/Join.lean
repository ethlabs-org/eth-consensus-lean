module
public import AvailableChainFGSA.Proofs.Join -- shake: keep (axioms)

@[expose] public section

namespace AvailableChain.FGSA.JoinTests

open AvailableChain.SimplexFG

abbrev p : Params :=
  { Δ := 1, n := 3, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun _ => ⟨99⟩ }

def storeAt (w t : Time) : State 3 :=
  { restartTime := some w, base := { GridCO.initial 3 .root with now := t } }

/-- Equality joins; one unit later waits for one more slot. -/
theorem join_boundary : joinedNow p (storeAt 4 8) = true ∧ joinedNow p (storeAt 5 8) = false ∧
    joinedNow p (storeAt 5 12) = true := by decide +kernel

/-- Integer subtraction at slot zero and the initial epoch. -/
theorem join_slot_zero : joinedNow p (storeAt 0 0) = false ∧ joinedNow p (storeAt (-4) 0) = true ∧
    joinedNow p (initial 3) = true := by decide +kernel

def lockedStore : State 3 :=
  { storeAt 5 4 with base := { (storeAt 5 4).base with
    obligations := [(.genesis, 2, 20), (.genesis, 2, 4)] } }

/-- The release-time tick keeps the live lock and expires the other lock. -/
theorem release_unjoined : (clockPre p lockedStore 5).base.obligations = [(.genesis, 2, 20)] ∧
    (clockPre p lockedStore 5).base.releaseSnapshots = [] := by decide +kernel

def candidate : FGBlock (Fin 3) := .node .genesis 1 ⟨1⟩ 0 []
def head (i : Fin 3) : GridCO.Wire 3 .root := ⟨.seat 1 i, .head candidate.root⟩

/-- Two seats support a non-genesis block before the early cutoff at time 6. -/
def gateStore : State 3 :=
  { fg := { Store.init with TF := {.genesis, candidate} }
    base := { GridCO.initial 3 .root with
      now := SA.gateTime p.toParams 1
      blocks := [.genesis, eraseFG candidate]
      blockStamp := [(.genesis, 0), (eraseFG candidate, 4)]
      votes := [head 0, head 1]
      voteStamp := [(head 0, 5), (head 1, 5)] } }

/-- Only the restart marker differs from the joined control. -/
def unjoinedGateStore : State 3 := { gateStore with restartTime := some 5 }

/-- Both stores satisfy nesting and use the scheduled gate time. -/
theorem gate_fixture : NestOK gateStore ∧ NestOK unjoinedGateStore ∧
    gateStore.base.now = 10 ∧ joinedNow p gateStore = true ∧
    joinedNow p unjoinedGateStore = false := by
  unfold NestOK
  decide +kernel

/-- The joined control confirms the candidate, writes a lock and advances the record. -/
theorem gate_joined :
    GridCO.savedGenuine (gateStep p gateStore 1).base 1 = some (some (eraseFG candidate)) ∧
    (gateStep p gateStore 1).fastWrite = [(1, [eraseFG candidate])] ∧
    (gateStep p gateStore 1).base.obligations = [(eraseFG candidate, 2, 17)] ∧
    (gateStep p gateStore 1).base.stableRecord = eraseFG candidate := by decide +kernel

/-- The same support is suppressed when unjoined; removing the guard fails this test. -/
theorem gate_unjoined :
    GridCO.savedGenuine (gateStep p unjoinedGateStore 1).base 1 = some none ∧
    (gateStep p unjoinedGateStore 1).fastWrite = [(1, [])] ∧
    (gateStep p unjoinedGateStore 1).base.obligations = unjoinedGateStore.base.obligations ∧
    (gateStep p unjoinedGateStore 1).base.stableRecord = unjoinedGateStore.base.stableRecord ∧
    (gateStep p unjoinedGateStore 1).fg = unjoinedGateStore.fg := by decide +kernel

end AvailableChain.FGSA.JoinTests
end

#print axioms AvailableChain.FGSA.JoinTests.join_boundary
#print axioms AvailableChain.FGSA.JoinTests.join_slot_zero
#print axioms AvailableChain.FGSA.JoinTests.release_unjoined
#print axioms AvailableChain.FGSA.JoinTests.gate_unjoined
