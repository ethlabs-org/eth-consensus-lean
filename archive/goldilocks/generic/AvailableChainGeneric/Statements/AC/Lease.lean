module
public import AvailableChainGeneric.Statements.AC.Reads

@[expose] public section

namespace AvailableChain.Gen.AC

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Each block and level has at most one stored deadline.
Source: step4b-plan.md, S4b-08, Q4 A; GridCO/Proofs/Map.lean:154–156. -/
def UniqueLeaseKeys {n : Nat} (st : GridCO.State n) : Prop :=
  ∀ x ∈ st.obligations, ∀ y ∈ st.obligations, (x.1, x.2.1) = (y.1, y.2.1) → x = y

theorem UniqueLeaseKeys_def {n : Nat} (st : GridCO.State n) : UniqueLeaseKeys st =
    (∀ x ∈ st.obligations, ∀ y ∈ st.obligations, (x.1, x.2.1) = (y.1, y.2.1) → x = y) := by
  rw [UniqueLeaseKeys]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
All stored lease targets are compatible, including expired targets.
Source: step4b-plan.md, S4b-08, Q4 A; GridCO/Proofs/Map.lean:818–821. -/
def LeaseMapChain {n : Nat} (st : GridCO.State n) : Prop :=
  ∀ K g d, (K, g, d) ∈ st.obligations → ∀ B level expiry,
    (B, level, expiry) ∈ st.obligations → Block.compatible K B = true

theorem LeaseMapChain_def {n : Nat} (st : GridCO.State n) : LeaseMapChain st =
    (∀ K g d, (K, g, d) ∈ st.obligations → ∀ B level expiry,
      (B, level, expiry) ∈ st.obligations → Block.compatible K B = true) := by
  rw [LeaseMapChain]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
A row for this block and level has a deadline at least `d`.
Source: step4b-plan.md, S4b-08, Q4 A; GridCO/Proofs/Protection.lean:17–18. -/
def ProtectsUntil {n : Nat} (st : GridCO.State n) (B : Block) (g : Nat) (d : Time) : Prop :=
  ∃ deadline, d ≤ deadline ∧ (B, g, deadline) ∈ st.obligations

theorem ProtectsUntil_def {n : Nat} (st : GridCO.State n) (B : Block) (g : Nat) (d : Time) :
    ProtectsUntil st B g d =
      (∃ deadline, d ≤ deadline ∧ (B, g, deadline) ∈ st.obligations) := by
  rw [ProtectsUntil]

-- Keep the adopted binder names, including unused proof binders (D01).
set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Live targets at an honest node are compatible.
Source: step4b-plan.md, S4b-01, Q1 A; GLY r3.14:716–719,1821–1825. -/
def LeaseChainStatement : Prop :=
  ∀ {V In : Type} {P : ProtocolSpec In} {E : Generic.Env V} {rho : Run V P}
    (A : ACReads E rho) (laws : ACLaws A) (i : Nat) (x : V)
    (hx : x ∈ rho.honest) (l k : Block × Nat × Time)
    (hl : l ∈ A.leases i x) (hk : k ∈ A.leases i x)
    (hll : A.now i x < Lease.deadline l) (hkl : A.now i x < Lease.deadline k),
    Block.Compatible (Lease.target l) (Lease.target k)

set_option linter.unusedVariables false in
theorem LeaseChainStatement_def : LeaseChainStatement =
    (∀ {V In : Type} {P : ProtocolSpec In} {E : Generic.Env V} {rho : Run V P}
      (A : ACReads E rho) (laws : ACLaws A) (i : Nat) (x : V)
      (hx : x ∈ rho.honest) (l k : Block × Nat × Time)
      (hl : l ∈ A.leases i x) (hk : k ∈ A.leases i x)
      (hll : A.now i x < Lease.deadline l) (hkl : A.now i x < Lease.deadline k),
      Block.Compatible (Lease.target l) (Lease.target k)) := by
  rw [LeaseChainStatement]

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
A gate retains a prefix protected by a lease that is live at the gate time.
Source: step4b-plan.md, S4b-01, Q1 A; GLY r3.14:716–719,1821–1825. -/
def PendingGateHarmlessStatement : Prop :=
  ∀ {V In : Type} {P : ProtocolSpec In} {E : Generic.Env V} {rho : Run V P}
    (A : ACReads E rho) (laws : ACLaws A) (i : Nat) (s : Slot) (x : V)
    (he : rho.events[i]? = some (.tick x (SA.gateTime A.prm s)))
    (B : Block) (g : Nat) (d : Time) (hr : (B, g, d) ∈ A.leases i x)
    (hd : SA.gateTime A.prm s < d) (hB : Block.Preceq B (A.output i x)),
    Block.Preceq B (A.output (i + 1) x)

set_option linter.unusedVariables false in
theorem PendingGateHarmlessStatement_def : PendingGateHarmlessStatement =
    (∀ {V In : Type} {P : ProtocolSpec In} {E : Generic.Env V} {rho : Run V P}
      (A : ACReads E rho) (laws : ACLaws A) (i : Nat) (s : Slot) (x : V)
      (he : rho.events[i]? = some (.tick x (SA.gateTime A.prm s)))
      (B : Block) (g : Nat) (d : Time) (hr : (B, g, d) ∈ A.leases i x)
      (hd : SA.gateTime A.prm s < d) (hB : Block.Preceq B (A.output i x)),
      Block.Preceq B (A.output (i + 1) x)) := by
  rw [PendingGateHarmlessStatement]

namespace Root

/-- [ROOT-DIGEST-2 W1; DC lease algebra]
Each block and level has at most one stored deadline.
Source: step4b-plan.md, S4b-08, Q4 A; GridCO/Proofs/Map.lean:154–156. -/
def UniqueLeaseKeys {n : Nat} (st : GridCO.State n .root) : Prop :=
  ∀ x ∈ st.obligations, ∀ y ∈ st.obligations, (x.1, x.2.1) = (y.1, y.2.1) → x = y

theorem UniqueLeaseKeys_def {n : Nat} (st : GridCO.State n .root) : UniqueLeaseKeys st =
    (∀ x ∈ st.obligations, ∀ y ∈ st.obligations, (x.1, x.2.1) = (y.1, y.2.1) → x = y) := by
  rw [UniqueLeaseKeys]

/-- [ROOT-DIGEST-2 W1; DC lease algebra]
All stored lease targets are compatible, including expired targets.
Source: step4b-plan.md, S4b-08, Q4 A; GridCO/Proofs/Map.lean:818–821. -/
def LeaseMapChain {n : Nat} (st : GridCO.State n .root) : Prop :=
  ∀ K g d, (K, g, d) ∈ st.obligations → ∀ B level expiry,
    (B, level, expiry) ∈ st.obligations → Block.compatible K B = true

theorem LeaseMapChain_def {n : Nat} (st : GridCO.State n .root) : LeaseMapChain st =
    (∀ K g d, (K, g, d) ∈ st.obligations → ∀ B level expiry,
      (B, level, expiry) ∈ st.obligations → Block.compatible K B = true) := by
  rw [LeaseMapChain]

/-- [ROOT-DIGEST-2 W1; DC lease algebra]
A row for this block and level has a deadline at least `d`.
Source: step4b-plan.md, S4b-08, Q4 A; GridCO/Proofs/Protection.lean:17–18. -/
def ProtectsUntil {n : Nat} (st : GridCO.State n .root) (B : Block) (g : Nat) (d : Time) : Prop :=
  ∃ deadline, d ≤ deadline ∧ (B, g, deadline) ∈ st.obligations

theorem ProtectsUntil_def {n : Nat} (st : GridCO.State n .root) (B : Block) (g : Nat) (d : Time) :
    ProtectsUntil st B g d =
      (∃ deadline, d ≤ deadline ∧ (B, g, deadline) ∈ st.obligations) := by
  rw [ProtectsUntil]

end Root

end AvailableChain.Gen.AC
