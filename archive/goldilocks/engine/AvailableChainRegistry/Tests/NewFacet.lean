module
public import AvailableChainFramework
public import AvailableChainRegistry.CounterRun

@[expose] public section

/-! The strong claim domain (Task 4; Review Focus 2). Only a `StrongInstance` can
hold a certificate of a `ClaimSpec ClaimDomain.strong`. An `Instance` without the
strong output has no such claim: the vacuity of `∀ I [HasStrong I], …`
(PHASE0-REPORT §6) cannot occur. A base claim pulls back to a strong instance
with its certificate, and a strong instance with a bad strong output is refuted.

The test claim `test.strongSafe.v1` has its own id. This module is not in the
catalog lock. -/

namespace AvailableChain.Registry.Tests

open AvailableChain AvailableChain.Generic AvailableChain.Framework
open AvailableChain.Framework.Catalog AvailableChain.Statements.Generic
open AvailableChain.Registry.Counter

/-- Counter with the stable output as its strong output. -/
def counterStrong : StrongInstance := { counterInst with strong := counterIface.stable }

/-- A base certificate, pulled back to the strong instance. -/
def certSafeStableStrong : Cert (safeStable.pull DomainMap.strongV1) counterStrong :=
  Cert.pull _ certSafeStable

/-- A test claim over the strong claim domain: the strong output is safe in the
Sleepy regime. -/
def testStrongSafe : ClaimSpec ClaimDomain.strong where
  id := `test.strongSafe.v1
  Const := Unit
  valid := fun _ => True
  le := fun _ _ => true
  le_refl := fun _ => rfl
  le_trans := fun _ _ _ _ _ => rfl
  Point := Time
  regime := fun I _ W x t₀ => sleepy I.toInstance W x.E x.rho t₀
  conclusion := fun I _ _ x t₀ => SafeFrom I.P x.rho I.strong t₀
  trigger := fun _ _ _ _ _ _ => True
  transport := by
    intro I k k' _ _ _ h
    cases k; cases k'; exact h
  refutable := .run

/-- Counter with a bad strong output: `chain 1` at height 1, genesis at every
other height. The output goes back to genesis after height 1. -/
def badStrong : StrongInstance :=
  { counterInst with strong := fun (st : Nat) => if st = 1 then chain 1 else .genesis }

/-- For Counter, a read at an integer time `t` is the state before time `t + 1`. -/
theorem readAt_eq_stateBeforeTime {V : Type} [DecidableEq V] (rho : Run V counter)
    (t : Time) : Run.readAt counter rho t = Run.stateBeforeTime counter rho (t + 1) := by
  unfold Run.stateBeforeTime Run.readAt
  congr 2
  funext e
  simp only [decide_eq_decide]
  exact Int.lt_add_one_iff.symm

/-- In the canonical run with one node and horizon 2, the strong read of
`badStrong` at node 0 is `chain 1` at time 0 and genesis at time 1, so it does
not only extend. -/
theorem badStrong_not_safe : ¬ SafeFrom badStrong.P (canonical 0 2) badStrong.strong 0 := by
  intro hs
  have hm := hs.monotone 0 (Finset.mem_univ _) 0 1 le_rfl (by decide) (by decide)
  have h0 : Run.readAt counter (canonical 0 2) 0 0 = (1 : Nat) := by
    rw [readAt_eq_stateBeforeTime]
    exact stateBeforeTime_eq 0 2 1 (by omega) 0
  have h1 : Run.readAt counter (canonical 0 2) 1 0 = (2 : Nat) := by
    rw [readAt_eq_stateBeforeTime]
    exact stateBeforeTime_eq 0 2 2 (by omega) 0
  change Block.Preceq (badStrong.strong (Run.readAt counter (canonical 0 2) 0 0))
    (badStrong.strong (Run.readAt counter (canonical 0 2) 1 0)) at hm
  rw [h0, h1] at hm
  exact absurd hm (by decide)

/-- The test claim refutes `badStrong`, with the run of `badStrong_not_safe`. -/
theorem refutedBadStrong : RefutationFamily testStrongSafe badStrong :=
  ⟨fun _ _ h => badStrong_not_safe (h ⟨Fin (Nat.succ 0), inferInstance, inferInstance⟩
    ⟨counterEnv 0, canonical 0 2⟩ rfl (0 : Time) (canonical_sleepy 0 2))⟩

/-- The canonical runs have no faulty validator. -/
theorem canonical_faultBound (k H f : Nat) : FaultBound counter f (canonical k H) := by
  simp [FaultBound, faulty, canonical]

/-- Task 8: the catalog claim `strongSafe` refutes `badStrong` at every fault
cap, with the run of `refutedBadStrong`. -/
theorem refutedBadStrongSafe : RefutationFamily strongSafe badStrong :=
  ⟨fun f _ h => badStrong_not_safe (h ⟨Fin (Nat.succ 0), inferInstance, inferInstance⟩
    ⟨counterEnv 0, canonical 0 2⟩ rfl (0 : Time)
    ⟨canonical_sleepy 0 2, canonical_faultBound 0 2 f⟩)⟩

/-- `strongSafe` can hold (Task 4 review, F1): Counter with its stable output
as the strong output, at fault cap 0. The proof is that of `certSafeStable`;
it does not read the fault bound. -/
def certStrongSafeCounter : Cert strongSafe counterStrong where
  const := (0 : Nat)
  valid := trivial
  inhabited := fun H =>
    ⟨⟨Fin (Nat.succ 0), inferInstance, inferInstance⟩, ⟨counterEnv 0, canonical 0 H.toNat⟩,
      (0 : Time), rfl, Int.self_le_toNat H,
      ⟨canonical_sleepy 0 H.toNat, canonical_faultBound 0 H.toNat 0⟩, trivial⟩
  proof := fun W x hx t₀ hr => certSafeStable.proof W x hx t₀ hr.1

end AvailableChain.Registry.Tests

end
